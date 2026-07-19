#!/usr/bin/env python3
"""Build the WSJ Chinese RSS archive used by GitHub Pages."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import time
import xml.etree.ElementTree as ET
from dataclasses import asdict, dataclass
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import urlparse

import requests
from bs4 import BeautifulSoup

RSS_URL = "https://cn.wsj.com/rss-news-and-feeds/zh-hans"
XPI_URL = "https://gitflic.ru/project/magnolia1234/bpc_uploads/blob/raw?file=bypass_paywalls_clean-latest.xpi"
MAX_ARCHIVE_ITEMS = 100
HELPER_XPI = "helper.xpi"

ARTICLES_DIR = "articles"
INDEX_FILE = "index.html"
FEED_FILE = "feed.xml"
MANIFEST_FILE = "manifest.json"

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64; rv:126.0) "
    "Gecko/20100101 Firefox/126.0"
)

ARCHIVE_CSS = """
html, body { max-width: 100% !important; overflow-x: hidden !important; }
img, picture img, figure img { max-width: 100% !important; height: auto !important; object-fit: contain !important; }
picture, figure, video, iframe, svg, canvas { max-width: 100% !important; }
figure, [role="img"] { height: auto !important; }
"""


@dataclass
class SitePaths:
    root: Path

    @property
    def articles(self) -> Path:
        return self.root / ARTICLES_DIR

    @property
    def index(self) -> Path:
        return self.root / INDEX_FILE

    @property
    def feed(self) -> Path:
        return self.root / FEED_FILE

    @property
    def manifest(self) -> Path:
        return self.root / MANIFEST_FILE

    @property
    def nojekyll(self) -> Path:
        return self.root / ".nojekyll"

    def article_path(self, filename: str) -> Path:
        return self.articles / filename

    def href_for(self, path: Path) -> str:
        return path.relative_to(self.root).as_posix()


@dataclass
class NewsItem:
    title: str
    summary: str
    link: str
    guid: str
    pub_date: str
    image_url: str
    snapshot: str = ""
    captured: bool = False
    capture_title: str = ""
    error: str = ""


@dataclass
class PageState:
    ready_state: str
    load_event_finished: bool
    height: int
    html_length: int
    text_length: int
    pending_images: int
    article_text_length: int = 0
    paragraph_count: int = 0


@dataclass
class CaptureCandidate:
    html_text: str
    title: str
    size_bytes: int
    text_length: int
    attempt: int
    height: int = 0
    article_text_length: int = 0
    paragraph_count: int = 0


PAGE_STATE_SCRIPT = """
const root = document.documentElement;
const body = document.body;
const nav = performance.getEntriesByType('navigation')[0];
const images = Array.from(document.images || []);
const textOf = (node) => ((node && (node.innerText || node.textContent)) || '').trim();
const articleSelectors = [
  'article',
  'main',
  '[role="main"]',
  '[data-testid*="article" i]',
  '[class*="article" i]',
  '[id*="article" i]'
];
const articleNodes = Array.from(document.querySelectorAll(articleSelectors.join(',')));
const articleTextLength = articleNodes.reduce((best, node) => Math.max(best, textOf(node).length), 0);
const paragraphs = Array.from(document.querySelectorAll('article p, main p, [role="main"] p, p'))
  .filter((node) => textOf(node).length >= 40);
return {
  readyState: document.readyState || '',
  loadEventFinished: Boolean(nav && nav.loadEventEnd > 0),
  height: Math.max(
    body ? body.scrollHeight : 0,
    root ? root.scrollHeight : 0,
    body ? body.offsetHeight : 0,
    root ? root.offsetHeight : 0
  ),
  htmlLength: root ? root.outerHTML.length : 0,
  textLength: body ? textOf(body).length : 0,
  articleTextLength,
  paragraphCount: paragraphs.length,
  pendingImages: images.filter((img) => !img.complete).length
};
"""

PREPARE_SNAPSHOT_SCRIPT = """
const sourceUrl = arguments[0];
const css = arguments[1];

let head = document.head;
if (!head) {
  head = document.createElement('head');
  document.documentElement.prepend(head);
}

document.querySelectorAll('base').forEach((node) => node.remove());
const base = document.createElement('base');
base.href = sourceUrl;
head.prepend(base);

let style = document.getElementById('__snapshot_display_css__');
if (!style) {
  style = document.createElement('style');
  style.id = '__snapshot_display_css__';
  head.appendChild(style);
}
style.textContent = css;

document.querySelectorAll('[data-src]:not([src])').forEach((node) => {
  node.setAttribute('src', node.getAttribute('data-src'));
});
document.querySelectorAll('[data-srcset]:not([srcset])').forEach((node) => {
  node.setAttribute('srcset', node.getAttribute('data-srcset'));
});
document.querySelectorAll('img').forEach((img) => {
  if (img.currentSrc) {
    img.setAttribute('src', img.currentSrc);
    img.removeAttribute('srcset');
    img.removeAttribute('sizes');
  }
  if (img.parentElement && img.parentElement.tagName.toLowerCase() === 'picture') {
    img.parentElement.querySelectorAll('source').forEach((source) => source.remove());
  }
  img.setAttribute('loading', 'eager');
  img.setAttribute('decoding', 'async');
  img.style.maxWidth = '100%';
  img.style.height = 'auto';
  img.style.objectFit = 'contain';
});
"""

ACTIVE_NUDGE_SCRIPT = """
const clickExpanders = Boolean(arguments[0]);
const textOf = (node) => ((node && (node.innerText || node.textContent)) || '').trim();
for (const img of Array.from(document.images || [])) {
  img.loading = 'eager';
  for (const [from, to] of [['data-src', 'src'], ['data-lazy-src', 'src'], ['data-original', 'src'], ['data-srcset', 'srcset']]) {
    const value = img.getAttribute(from);
    if (value && !img.getAttribute(to)) img.setAttribute(to, value);
  }
}
window.dispatchEvent(new Event('scroll'));
window.dispatchEvent(new Event('resize'));
let clicked = 0;
if (clickExpanders) {
  const pattern = /(继续阅读|阅读全文|展开|更多|show more|read more|continue reading)/i;
  const candidates = Array.from(document.querySelectorAll('button, a'))
    .filter((node) => pattern.test(textOf(node)) && !/subscribe|sign|login|订阅|登录|注册/i.test(textOf(node)));
  for (const node of candidates.slice(0, 3)) {
    try { node.click(); clicked += 1; } catch (error) {}
  }
}
return { clicked };
"""

CLEAR_STORAGE_SCRIPT = """
try { window.localStorage.clear(); } catch (error) {}
try { window.sessionStorage.clear(); } catch (error) {}
try {
  const past = 'Thu, 01 Jan 1970 00:00:00 GMT';
  const host = location.hostname || '';
  const domains = host ? [host, '.' + host.replace(/^www\\./, '')] : [''];
  const paths = ['/', location.pathname || '/'];
  document.cookie.split(';').forEach((cookie) => {
    const name = cookie.split('=')[0].trim();
    if (!name) return;
    paths.forEach((path) => {
      document.cookie = name + '=; expires=' + past + '; path=' + path;
      domains.forEach((domain) => {
        if (domain) document.cookie = name + '=; expires=' + past + '; path=' + path + '; domain=' + domain;
      });
    });
  });
} catch (error) {}
"""


class CaptureError(RuntimeError):
    pass


def env_bool(name: str, default: bool = False) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return value.strip().lower() in {"1", "true", "yes", "on"}


def log(scope: str, message: str) -> None:
    print(f"[{scope}] {message}", flush=True)


UTC_PLUS_8 = timezone(timedelta(hours=8))


def item_identity(item: NewsItem) -> str:
    return item.link or item.guid or item.title


def run_cmd(args: list[str], timeout: int = 30, label: str | None = None, check: bool = False, quiet: bool = False):
    proc = subprocess.run(args, text=True, capture_output=True, timeout=timeout)
    if proc.returncode != 0 and not quiet:
        name = label or " ".join(args)
        print(f"[命令] {name} 失败，返回码 {proc.returncode}")
        if proc.stdout.strip():
            print(proc.stdout.strip()[:1200])
        if proc.stderr.strip():
            print(proc.stderr.strip()[:1200])
    if check and proc.returncode != 0:
        raise RuntimeError(label or "命令执行失败")
    return proc


def port_open(host: str, port: int, timeout: int = 2) -> bool:
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


def proxy_url(port: int) -> str:
    return f"socks5h://127.0.0.1:{port}"


def request_proxies(port: int) -> dict[str, str] | None:
    if env_bool("SKIP_WARP"):
        return None
    proxy = proxy_url(port)
    return {"http": proxy, "https": proxy}


def proxy_ready(port: int) -> bool:
    if not port_open("127.0.0.1", port):
        return False
    proc = run_cmd(
        [
            "curl",
            "-fsS",
            "--max-time",
            "20",
            "--socks5-hostname",
            f"127.0.0.1:{port}",
            "https://www.cloudflare.com/cdn-cgi/trace",
        ],
        timeout=25,
        label="检查 WARP 代理",
        quiet=True,
    )
    if proc.returncode == 0:
        print("[WARP] 代理可用。")
        print("\n".join(proc.stdout.strip().splitlines()[:8]))
        return True
    return False


def warp_service_running() -> bool:
    return run_cmd(["pgrep", "-x", "warp-svc"], timeout=5, quiet=True).returncode == 0


def start_warp_service() -> bool:
    if warp_service_running():
        print("[WARP] warp-svc 已在运行。")
        return True
    service = Path("/usr/bin/warp-svc")
    if not service.exists():
        print("[WARP] 未找到 /usr/bin/warp-svc。")
        return False
    print("[WARP] 启动 warp-svc。")
    with Path("/tmp/warp-svc.log").open("ab") as log:
        subprocess.Popen([str(service)], stdout=log, stderr=log, start_new_session=True)
    time.sleep(5)
    return warp_service_running()


def configure_warp(port: int) -> None:
    registration = run_cmd(
        ["warp-cli", "--accept-tos", "registration", "new"],
        timeout=30,
        label="注册 WARP",
        quiet=True,
    )
    if registration.returncode != 0:
        print("[WARP] 注册步骤跳过。")

    mode = run_cmd(["warp-cli", "--accept-tos", "mode", "proxy"], timeout=20, label="设置 proxy 模式")
    if mode.returncode != 0:
        run_cmd(["warp-cli", "--accept-tos", "set-mode", "proxy"], timeout=20, label="设置 proxy 模式")

    run_cmd(["warp-cli", "--accept-tos", "proxy", "port", str(port)], timeout=20, label="设置 WARP 端口")
    run_cmd(["warp-cli", "--accept-tos", "connect"], timeout=30, label="连接 WARP")
    time.sleep(6)
    run_cmd(["warp-cli", "--accept-tos", "status"], timeout=20, label="查看 WARP 状态", quiet=True)


def ensure_warp_proxy(port: int) -> bool:
    if env_bool("SKIP_WARP"):
        print("[WARP] 已跳过。")
        return True
    print("[WARP] 检查代理。")
    if proxy_ready(port):
        return True
    if not start_warp_service():
        return False
    configure_warp(port)
    if proxy_ready(port):
        return True
    print("[WARP] 代理不可用。最近日志如下：")
    run_cmd(["bash", "-lc", "tail -n 80 /tmp/warp-svc.log || true"], timeout=10, label="读取 WARP 日志")
    return False


def fetch_rss(url: str, port: int) -> str:
    print(f"[RSS] 下载 {url}")
    response = requests.get(url, proxies=request_proxies(port), timeout=60, headers={"User-Agent": USER_AGENT})
    response.raise_for_status()
    response.encoding = response.encoding or "utf-8"
    return response.text


def item_text(elem: ET.Element, name: str) -> str:
    child = elem.find(name)
    return (child.text or "").strip() if child is not None else ""


def parse_description(description_html: str) -> tuple[str, str]:
    soup = BeautifulSoup(description_html or "", "html.parser")
    image_url = ""
    image = soup.find("img")
    if image is not None:
        image_url = (image.get("src") or "").strip()
    paragraph = soup.find("p")
    if paragraph is not None:
        return image_url, paragraph.get_text(" ", strip=True)
    if image is not None:
        image.decompose()
    return image_url, soup.get_text(" ", strip=True)


def parse_rss(xml_text: str, max_items: int) -> list[NewsItem]:
    root = ET.fromstring(xml_text.encode("utf-8"))
    channel = root.find("channel") or root
    items: list[NewsItem] = []
    for elem in channel.findall("item"):
        title = item_text(elem, "title")
        link = item_text(elem, "link")
        if not title or not link:
            continue
        image_url, summary = parse_description(item_text(elem, "description"))
        items.append(
            NewsItem(
                title=title,
                summary=summary,
                link=link,
                guid=item_text(elem, "guid"),
                pub_date=item_text(elem, "pubDate"),
                image_url=image_url,
            )
        )
        if len(items) >= max_items:
            break
    print(f"[RSS] 解析到 {len(items)} 条新闻。")
    return items


def article_filename(item: NewsItem) -> str:
    source = item.guid or item.link or item.title
    digest = hashlib.sha1(source.encode("utf-8")).hexdigest()[:12]
    parsed = urlparse(item.link)
    stem = Path(parsed.path).stem.lower()
    stem = re.sub(r"[^a-z0-9-]+", "-", stem).strip("-")
    if not stem:
        stem = "article"
    return f"{stem[:48]}-{digest}.html"


def addon_path_in_repo() -> Path:
    return Path(__file__).resolve().parent / HELPER_XPI


def download_addon(url: str, port: int) -> Path | None:
    helper_path = addon_path_in_repo()
    url = url.strip()

    if url:
        tmp = helper_path.with_suffix(".xpi.tmp")
        try:
            log("XPI", f"检查在线插件：{url}")
            response = requests.get(url, proxies=request_proxies(port), timeout=90, headers={"User-Agent": USER_AGENT})
            response.raise_for_status()
            if not response.content:
                raise RuntimeError("下载内容为空")
            tmp.write_bytes(response.content)
            tmp.replace(helper_path)
            log("XPI", f"在线插件已保存为 {helper_path.name}")
            return helper_path
        except Exception as exc:
            if tmp.exists():
                tmp.unlink()
            log("XPI", f"在线插件不可用，尝试使用本地 {helper_path.name}：{str(exc).replace(chr(10), ' ')[:160]}")

    if helper_path.exists():
        log("XPI", f"使用本地插件：{helper_path.name}")
        return helper_path

    log("XPI", "没有可用插件，将继续无插件抓取。")
    return None


def version_looks_like_firefox(path: Path) -> bool:
    try:
        proc = subprocess.run([str(path), "--version"], text=True, capture_output=True, timeout=15)
    except Exception:
        return False
    output = (proc.stdout or "") + (proc.stderr or "")
    return proc.returncode == 0 and "Firefox" in output


def is_elf(path: Path) -> bool:
    try:
        with path.open("rb") as file:
            return file.read(4) == b"\x7fELF"
    except OSError:
        return False


def nearby_firefox_bins(path: Path) -> list[Path]:
    roots = [path.parent, path.parent.parent]
    names = ["firefox-bin", "firefox/firefox", "firefox/firefox-bin"]
    return [root / name for root in roots for name in names]


def firefox_candidates() -> list[Path]:
    result: list[Path] = []
    env_path = os.environ.get("FIREFOX_BIN", "").strip()
    if env_path:
        path = Path(env_path)
        result.extend([path, *nearby_firefox_bins(path)])
    which_firefox = shutil.which("firefox")
    if which_firefox:
        path = Path(which_firefox)
        result.extend([path, *nearby_firefox_bins(path)])
    for root in (Path("/opt/hostedtoolcache"), Path("/opt"), Path("/usr/local"), Path("/usr/lib")):
        if root.exists():
            result.extend(root.glob("**/firefox/firefox"))
            result.extend(root.glob("**/firefox-bin"))
    result.extend([Path("/usr/bin/firefox"), Path("/usr/local/bin/firefox"), Path("/snap/bin/firefox")])
    return result


def find_firefox_binary() -> str | None:
    seen: set[str] = set()
    for candidate in firefox_candidates():
        try:
            path = candidate.resolve()
        except OSError:
            path = candidate
        key = str(path)
        if key in seen:
            continue
        seen.add(key)
        if not path.is_file() or not os.access(path, os.X_OK):
            continue
        if not version_looks_like_firefox(path):
            print(f"[Firefox] 跳过不可运行候选项：{path}")
            continue
        if not is_elf(path):
            print(f"[Firefox] 跳过 wrapper：{path}")
            continue
        print(f"[Firefox] 使用二进制：{path}")
        return str(path)
    print("[Firefox] 未找到可用的 Firefox 二进制。")
    return None


def create_driver(port: int, addon_path: Path | None, args: argparse.Namespace):
    from selenium import webdriver
    from selenium.webdriver.firefox.options import Options

    firefox_binary = find_firefox_binary()
    if not firefox_binary:
        raise RuntimeError("未找到 Firefox，请设置 FIREFOX_BIN 或使用 workflow 中的 setup-firefox。")

    options = Options()
    options.binary_location = firefox_binary
    options.add_argument("-headless")
    options.add_argument(f"--width={args.window_width}")
    options.add_argument(f"--height={args.window_height}")
    options.set_preference("general.useragent.override", USER_AGENT)
    options.set_preference("intl.accept_languages", "zh-CN,zh,en-US,en")
    options.set_preference("layout.css.devPixelsPerPx", "1.0")
    options.set_preference("browser.shell.checkDefaultBrowser", False)
    options.set_preference("browser.startup.homepage_override.mstone", "ignore")
    options.set_preference("startup.homepage_welcome_url", "about:blank")
    options.set_preference("startup.homepage_welcome_url.additional", "about:blank")
    options.set_preference("browser.cache.disk.enable", False)
    options.set_preference("browser.cache.memory.enable", False)
    options.set_preference("browser.cache.offline.enable", False)
    options.set_preference("network.http.use-cache", False)

    if not env_bool("SKIP_WARP"):
        options.set_preference("network.proxy.type", 1)
        options.set_preference("network.proxy.socks", "127.0.0.1")
        options.set_preference("network.proxy.socks_port", port)
        options.set_preference("network.proxy.socks_version", 5)
        options.set_preference("network.proxy.socks_remote_dns", True)
        options.set_preference("network.proxy.no_proxies_on", "")

    driver = webdriver.Firefox(options=options)
    driver.set_page_load_timeout(args.page_load_timeout)
    driver.set_script_timeout(30)
    driver.set_window_size(args.window_width, args.window_height)

    if addon_path is not None:
        addon_id = driver.install_addon(str(addon_path), temporary=True)
        print(f"[Firefox] 插件已安装：{addon_id}")
    return driver


def to_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def read_page_state(driver) -> PageState:
    data = driver.execute_script(PAGE_STATE_SCRIPT) or {}
    return PageState(
        ready_state=str(data.get("readyState") or ""),
        load_event_finished=bool(data.get("loadEventFinished")),
        height=to_int(data.get("height")),
        html_length=to_int(data.get("htmlLength")),
        text_length=to_int(data.get("textLength")),
        pending_images=to_int(data.get("pendingImages")),
        article_text_length=to_int(data.get("articleTextLength")),
        paragraph_count=to_int(data.get("paragraphCount")),
    )


def wait_for_ready_state(driver, timeout: float) -> PageState:
    deadline = time.monotonic() + timeout
    last_state = PageState("", False, 0, 0, 0, 0)
    while time.monotonic() < deadline:
        try:
            last_state = read_page_state(driver)
        except Exception:
            time.sleep(0.25)
            continue
        if last_state.ready_state == "complete" or last_state.load_event_finished:
            return last_state
        time.sleep(0.4)
    return last_state


def state_score(state: PageState) -> tuple[int, int, int]:
    return (state.paragraph_count, state.html_length, state.height)


def state_reaches_capture_floor(state: PageState, args: argparse.Namespace) -> bool:
    return state.paragraph_count >= args.min_capture_paragraphs


def candidate_reaches_capture_floor(candidate: CaptureCandidate, args: argparse.Namespace) -> bool:
    return state_reaches_capture_floor(
        PageState(
            ready_state="complete",
            load_event_finished=True,
            height=candidate.height,
            html_length=candidate.size_bytes,
            text_length=candidate.text_length,
            pending_images=0,
            article_text_length=candidate.article_text_length,
            paragraph_count=candidate.paragraph_count,
        ),
        args,
    )


def active_nudge_page(driver, click_expanders: bool = False) -> None:
    try:
        driver.execute_script(ACTIVE_NUDGE_SCRIPT, click_expanders)
    except Exception:
        pass


def wait_for_stable_page(driver, args: argparse.Namespace, timeout: float | None = None) -> PageState:
    deadline = time.monotonic() + (args.page_settle_timeout if timeout is None else timeout)
    stable_rounds = 0
    previous: PageState | None = None
    current = read_page_state(driver)
    best = current
    last_nudge = 0.0

    while time.monotonic() < deadline:
        time.sleep(args.page_settle_interval)
        current = read_page_state(driver)
        if state_score(current) > state_score(best):
            best = current
        if previous is None:
            previous = current
            continue

        html_delta = abs(current.html_length - previous.html_length)
        text_delta = abs(current.text_length - previous.text_length)
        height_delta = abs(current.height - previous.height)
        complete = current.ready_state == "complete" or current.load_event_finished
        quiet = current.pending_images == 0 and html_delta <= 1024 and text_delta <= 256 and height_delta <= 64
        good_enough = state_reaches_capture_floor(current, args)

        # 关键变化：短页面即使“稳定”也继续等一会儿，避免把插件尚未注入正文的页面当成成功。
        if complete and quiet and good_enough:
            stable_rounds += 1
            if stable_rounds >= args.page_stable_rounds:
                return current
        else:
            stable_rounds = 0

        if complete and not good_enough and time.monotonic() - last_nudge >= max(1.5, args.page_settle_interval * 2):
            active_nudge_page(driver, args.click_expanders)
            last_nudge = time.monotonic()
        previous = current

    return best if state_score(best) > state_score(current) else current


def clear_current_site_state(driver) -> None:
    try:
        driver.delete_all_cookies()
    except Exception:
        pass
    try:
        driver.execute_script(CLEAR_STORAGE_SCRIPT)
    except Exception:
        pass


def reset_browser_for_attempt(driver) -> None:
    clear_current_site_state(driver)
    try:
        driver.get("about:blank")
    except Exception:
        pass
    clear_current_site_state(driver)


def scroll_page(driver, steps: int, wait_seconds: float, click_expanders: bool = False) -> None:
    if steps <= 0:
        return
    previous_height = 0
    stable_rounds = 0
    for step in range(1, steps + 1):
        metrics = driver.execute_script(
            """
            const root = document.documentElement;
            const body = document.body;
            return {
              height: Math.max(body ? body.scrollHeight : 0, root ? root.scrollHeight : 0),
              viewport: window.innerHeight || (root ? root.clientHeight : 900) || 900
            };
            """
        ) or {}
        height = max(0, to_int(metrics.get("height")))
        viewport = max(1, to_int(metrics.get("viewport"), 900))
        max_y = max(0, height - viewport)
        position = int(max_y * step / max(1, steps))
        driver.execute_script("window.scrollTo(0, arguments[0]);", position)
        active_nudge_page(driver, click_expanders)
        time.sleep(wait_seconds)
        new_height = to_int(
            driver.execute_script(
                "return Math.max(document.body ? document.body.scrollHeight : 0, document.documentElement ? document.documentElement.scrollHeight : 0);"
            )
        )
        stable_rounds = stable_rounds + 1 if abs(new_height - previous_height) <= 64 else 0
        previous_height = new_height
        if stable_rounds >= 3 and step >= max(3, steps // 2):
            break
    driver.execute_script("window.scrollTo(0, document.body ? document.body.scrollHeight : 0);")
    time.sleep(min(1.0, max(0.2, wait_seconds)))
    driver.execute_script("window.scrollTo(0, 0);")
    time.sleep(min(1.0, max(0.2, wait_seconds)))


def prepare_snapshot_dom(driver, source_url: str) -> None:
    driver.execute_script(PREPARE_SNAPSHOT_SCRIPT, source_url, ARCHIVE_CSS)


def html_document_from_driver(driver) -> str:
    outer_html = driver.execute_script("return document.documentElement ? document.documentElement.outerHTML : '';") or ""
    outer_html = str(outer_html).lstrip()
    if re.match(r"(?is)^<!doctype\s+html", outer_html):
        return outer_html
    return "<!DOCTYPE html>\n" + outer_html


def capture_once(driver, item: NewsItem, attempt: int, args: argparse.Namespace) -> CaptureCandidate:
    from selenium.common.exceptions import TimeoutException

    reset_browser_for_attempt(driver)
    try:
        driver.get(item.link)
    except TimeoutException:
        log("CAPTURE", "页面加载超时，停止加载并保存当前 DOM。")
        driver.execute_script("window.stop();")

    ready = wait_for_ready_state(driver, args.ready_timeout)
    log("CAPTURE", f"attempt={attempt} loaded ready={ready.ready_state or '-'} paragraphs={ready.paragraph_count} html={ready.html_length} pending_images={ready.pending_images}")

    if args.initial_wait > 0:
        time.sleep(args.initial_wait)
    scroll_page(driver, args.scroll_steps, args.scroll_wait, args.click_expanders)
    stable = wait_for_stable_page(driver, args)
    log("CAPTURE", f"attempt={attempt} stable paragraphs={stable.paragraph_count} html={stable.html_length} pending_images={stable.pending_images}")

    if not state_reaches_capture_floor(stable, args):
        log("CAPTURE", f"attempt={attempt} paragraphs={stable.paragraph_count}/{args.min_capture_paragraphs}，追加触发滚动")
        scroll_page(driver, max(3, args.scroll_steps // 2), args.scroll_wait, args.click_expanders)
        stable = wait_for_stable_page(driver, args, args.low_capture_extra_timeout)

    prepare_snapshot_dom(driver, item.link)
    post = read_page_state(driver)
    snapshot_html = html_document_from_driver(driver)
    size_bytes = len(snapshot_html.encode("utf-8"))
    title = driver.title.strip() or item.title
    return CaptureCandidate(
        html_text=snapshot_html,
        title=title,
        size_bytes=size_bytes,
        text_length=max(stable.text_length, post.text_length),
        attempt=attempt,
        height=max(stable.height, post.height),
        article_text_length=max(stable.article_text_length, post.article_text_length),
        paragraph_count=max(stable.paragraph_count, post.paragraph_count),
    )


def save_article(driver, item: NewsItem, target: Path, href: str, args: argparse.Namespace) -> NewsItem:
    attempts = max(1, args.capture_attempts)
    candidates: list[CaptureCandidate] = []
    errors: list[str] = []

    for attempt in range(1, attempts + 1):
        try:
            candidate = capture_once(driver, item, attempt, args)
            candidates.append(candidate)
            log("CAPTURE", f"attempt={attempt} done paragraphs={candidate.paragraph_count} bytes={candidate.size_bytes}")
            if (
                args.stop_after_good_capture
                and attempt >= args.min_capture_attempts
                and candidate_reaches_capture_floor(candidate, args)
            ):
                log("CAPTURE", f"attempt={attempt} 已达到 paragraphs 阈值，跳过剩余重复访问。")
                break
        except Exception as exc:
            message = str(exc).replace("\n", " ")[:300]
            errors.append(f"第 {attempt} 次：{message}")
            log("CAPTURE", f"attempt={attempt} failed: {message}")

    if not candidates:
        raise CaptureError("；".join(errors) or "没有获得可保存的 HTML")

    best = max(candidates, key=lambda item: (item.paragraph_count, item.size_bytes))
    reached_floor = candidate_reaches_capture_floor(best, args)

    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(best.html_text, encoding="utf-8")

    item.snapshot = href
    item.captured = True
    item.capture_title = best.title
    item.error = "；".join(errors)
    if reached_floor:
        log("CAPTURE", f"saved {href} attempt={best.attempt} paragraphs={best.paragraph_count} bytes={best.size_bytes}")
    else:
        log(
            "CAPTURE",
            f"saved {href} attempt={best.attempt} paragraphs={best.paragraph_count}/{args.min_capture_paragraphs} bytes={best.size_bytes}，未达阈值但已保存",
        )
    return item


def count_article_paragraphs(html_text: str) -> int:
    soup = BeautifulSoup(html_text or "", "html.parser")
    paragraphs = soup.select('article p, main p, [role="main"] p, p')
    seen: set[int] = set()
    count = 0
    for node in paragraphs:
        marker = id(node)
        if marker in seen:
            continue
        seen.add(marker)
        if len(node.get_text(" ", strip=True)) >= 40:
            count += 1
    return count


def try_reuse_existing_snapshot(item: NewsItem, target: Path, href: str, args: argparse.Namespace) -> bool:
    if not target.exists():
        return False
    try:
        html_text = target.read_text(encoding="utf-8", errors="ignore")
    except OSError as exc:
        item.error = str(exc).replace("\n", " ")[:300]
        return False

    paragraphs = count_article_paragraphs(html_text)
    if paragraphs < args.min_capture_paragraphs:
        log("SKIP", f"existing snapshot too small paragraphs={paragraphs}/{args.min_capture_paragraphs}: {href}")
        return False

    item.snapshot = href
    item.captured = True
    item.capture_title = item.title
    item.error = ""
    log("SKIP", f"existing snapshot ok paragraphs={paragraphs}: {href}")
    return True


def capture_articles(items: list[NewsItem], paths: SitePaths, port: int, args: argparse.Namespace) -> list[NewsItem]:
    pending: list[tuple[int, NewsItem, Path, str]] = []
    for index, item in enumerate(items, start=1):
        filename = article_filename(item)
        target = paths.article_path(filename)
        href = paths.href_for(target)
        if not try_reuse_existing_snapshot(item, target, href, args):
            item.snapshot = ""
            item.captured = False
            pending.append((index, item, target, href))

    if args.skip_fetch_html:
        log("CAPTURE", f"跳过在线抓取，复用 {len(items) - len(pending)}/{len(items)} 条已有快照。")
        return items

    if not pending:
        log("CAPTURE", "所有 RSS 条目已有合格快照。")
        return items

    from selenium.common.exceptions import WebDriverException

    driver = None
    addon_path = download_addon(XPI_URL, port)
    try:
        driver = create_driver(port, addon_path, args)
        for index, item, target, href in pending:
            log("CAPTURE", f"{index}/{len(items)} {item.title}")
            try:
                save_article(driver, item, target, href, args)
            except (CaptureError, WebDriverException, RuntimeError, OSError) as exc:
                item.error = str(exc).replace("\n", " ")[:500]
                if target.exists() and target.stat().st_size > 0:
                    item.snapshot = href
                    item.captured = True
                    item.capture_title = item.capture_title or item.title
                    paragraphs = count_article_paragraphs(target.read_text(encoding="utf-8", errors="ignore"))
                    log("CAPTURE", f"failed; 使用已有本地 HTML：{href} paragraphs={paragraphs} error={item.error}")
                else:
                    item.snapshot = ""
                    item.captured = False
                    log("CAPTURE", f"failed; 没有可用 HTML，首页保留卡片但不加链接：{item.error}")
    finally:
        if driver is not None:
            driver.quit()
            log("FIREFOX", "已关闭。")
    return items


def load_previous_items(paths: SitePaths) -> list[NewsItem]:
    if not paths.manifest.exists():
        return []
    try:
        data = json.loads(paths.manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        log("SITE", f"旧 manifest 不可读，忽略：{exc}")
        return []

    result: list[NewsItem] = []
    for raw in data.get("items", []):
        if not isinstance(raw, dict):
            continue
        try:
            result.append(
                NewsItem(
                    title=str(raw.get("title") or ""),
                    summary=str(raw.get("summary") or ""),
                    link=str(raw.get("link") or ""),
                    guid=str(raw.get("guid") or ""),
                    pub_date=str(raw.get("pub_date") or ""),
                    image_url=str(raw.get("image_url") or ""),
                    snapshot=str(raw.get("snapshot") or ""),
                    captured=bool(raw.get("captured")),
                    capture_title=str(raw.get("capture_title") or ""),
                    error=str(raw.get("error") or ""),
                )
            )
        except TypeError:
            continue
    log("SITE", f"读取旧记录 {len(result)} 条。")
    return result


def prepare_output(paths: SitePaths) -> None:
    paths.root.mkdir(parents=True, exist_ok=True)
    for file in (paths.index, paths.feed, paths.manifest):
        if file.exists():
            file.unlink()
    paths.articles.mkdir(parents=True, exist_ok=True)
    paths.nojekyll.write_text("", encoding="utf-8")


def merge_archive_items(current_items: list[NewsItem], previous_items: list[NewsItem], max_items: int) -> list[NewsItem]:
    retained: list[NewsItem] = []
    seen: set[str] = set()
    for item in [*current_items, *previous_items]:
        key = item_identity(item)
        if not key or key in seen:
            continue
        seen.add(key)
        retained.append(item)
        if len(retained) >= max_items:
            break
    log("SITE", f"页面保留 {len(retained)} 条新闻，上限 {max_items} 条。")
    return retained


def retained_article_hrefs(items: Iterable[NewsItem]) -> set[str]:
    hrefs: set[str] = set()
    for item in items:
        if item.captured and item.snapshot.startswith(f"{ARTICLES_DIR}/"):
            hrefs.add(item.snapshot)
    return hrefs


def prune_articles(paths: SitePaths, items: Iterable[NewsItem]) -> None:
    keep = retained_article_hrefs(items)
    removed = 0
    for path in paths.articles.glob("*.html"):
        href = paths.href_for(path)
        if href not in keep:
            path.unlink()
            removed += 1
    if removed:
        log("SITE", f"清理旧快照 {removed} 个。")


def parse_rss_datetime(value: str) -> datetime | None:
    if not value:
        return None
    try:
        dt = parsedate_to_datetime(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except Exception:
        return None


def format_news_date(value: str) -> str:
    dt = parse_rss_datetime(value)
    if dt is None:
        return ""
    return dt.astimezone(UTC_PLUS_8).strftime("%m-%d %H:%M")


def format_update_time(dt: datetime | None = None) -> str:
    if dt is None:
        dt = datetime.now(timezone.utc)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(UTC_PLUS_8).strftime("%m-%d %H:%M")


def item_href(item: NewsItem) -> str:
    return item.snapshot if item.captured and item.snapshot else ""


def render_link_or_disabled(href: str, class_name: str, inner_html: str) -> str:
    if href:
        return f'<a class="{class_name}" href="{html.escape(href)}">{inner_html}</a>'
    return f'<div class="{class_name} disabled" aria-disabled="true">{inner_html}</div>'


def render_card(item: NewsItem, index: int = 0) -> str:
    href = item_href(item)
    image = item.image_url.strip()
    image_html = (
        f'<img src="{html.escape(image)}" alt="" loading="lazy" referrerpolicy="no-referrer">'
        if image
        else '<div class="placeholder">WSJ</div>'
    )
    thumb_html = render_link_or_disabled(href, "thumb", image_html)
    title_text = html.escape(item.title)
    title_inner = f'<span class="title-text">{title_text}</span>'
    title_html = (
        f'<a class="title" href="{html.escape(href)}">{title_inner}</a>'
        if href
        else f'<div class="title disabled" aria-disabled="true">{title_inner}</div>'
    )
    summary = html.escape(item.summary)
    date = html.escape(format_news_date(item.pub_date))
    meta_html = f'<div class="meta"><span>{date}</span></div>' if date else ''
    return f"""
      <article class="news-card" data-card-index="{index}">
        {thumb_html}
        <div class="content">
          {title_html}
          <p class="summary">{summary}</p>
          {meta_html}
        </div>
      </article>"""


def render_index(items: list[NewsItem], rss_url: str) -> str:
    cards = [render_card(item, index) for index, item in enumerate(items)]
    updated = format_update_time()
    return f"""<!doctype html>
<html lang="zh-Hans">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>新闻</title>
  <link rel="apple-touch-icon" href="https://s.wsj.net/media/wsj_apple-touch-icon-180x180.png">
  <style>
    :root {{
      color-scheme: light;
      --bg: #f5f5f7;
      --card: #ffffff;
      --text: #1d1d1f;
      --muted: #6e6e73;
      --line: rgba(0, 0, 0, 0.07);
      --shadow: rgba(0, 0, 0, 0.06);
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      background: var(--bg);
      color: var(--text);
      font-family: -apple-system, BlinkMacSystemFont, "SF Pro Text", "Segoe UI", "PingFang SC", "Hiragino Sans GB", "Microsoft YaHei", sans-serif;
      -webkit-font-smoothing: antialiased;
      text-rendering: optimizeLegibility;
    }}
    a {{ color: inherit; }}
    .page {{ width: min(1180px, 100%); margin: 0 auto; padding: 18px 14px 28px; }}
    .list {{ --columns: 1; display: grid; grid-template-columns: 1fr; gap: 14px; align-items: start; }}
    .masonry-column {{ display: flex; flex-direction: column; gap: 14px; min-width: 0; }}
    .news-card {{
      display: flex;
      flex-direction: column;
      overflow: hidden;
      background: var(--card);
      border: 1px solid var(--line);
      border-radius: 22px;
      box-shadow: 0 10px 30px var(--shadow);
    }}
    .thumb {{
      display: block;
      width: 100%;
      overflow: hidden;
      background: #e8e8ed;
      color: #8e8e93;
      text-decoration: none;
    }}
    .thumb img {{ width: 100%; height: auto; display: block; }}
    .placeholder {{ display: grid; place-items: center; width: 100%; aspect-ratio: 16 / 9; font-size: 24px; font-weight: 700; letter-spacing: 0.02em; }}
    .content {{ padding: 15px 15px 14px; display: flex; flex: 1; flex-direction: column; min-width: 0; }}
    .title {{ display: block; font-size: 17px; line-height: 1.38; font-weight: 700; letter-spacing: -0.01em; text-decoration: none; }}
    .title:hover {{ text-decoration: underline; text-underline-offset: 3px; }}
    .disabled {{ cursor: default; }}
    .summary {{
      margin: 9px 0 0;
      color: #3f3f46;
      font-size: 14px;
      line-height: 1.58;
    }}
    .meta {{ margin-top: auto; padding-top: 12px; color: var(--muted); font-size: 12px; line-height: 1.3; }}
    footer {{ margin-top: 20px; color: var(--muted); font-size: 12px; line-height: 1.4; text-align: center; }}
    @media (min-width: 720px) {{
      .page {{ padding: 22px 18px 30px; }}
      .list {{ --columns: 3; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 16px; }}
      .masonry-column {{ gap: 16px; }}
    }}
    @media (min-width: 1080px) {{
      .page {{ padding-top: 26px; }}
      .list {{ gap: 18px; }}
      .masonry-column {{ gap: 18px; }}
    }}
  </style>
</head>
<body>
  <main class="page">
    <section class="list" aria-label="新闻列表">
{''.join(cards)}
    </section>
    <footer>更新时间 {html.escape(updated)}</footer>
  </main>
  <script>
    (() => {{
      const list = document.querySelector('.list');
      if (!list) return;

      const columnCount = () => {{
        const value = getComputedStyle(list).getPropertyValue('--columns').trim();
        const count = Number.parseInt(value, 10);
        return Number.isFinite(count) && count > 0 ? count : 1;
      }};

      const orderedCards = () => Array.from(list.querySelectorAll('.news-card')).sort((a, b) => {{
        return Number(a.dataset.cardIndex || 0) - Number(b.dataset.cardIndex || 0);
      }});

      const restoreSingleColumn = (cards) => {{
        const directCards = Array.from(list.children).filter((node) => node.classList && node.classList.contains('news-card'));
        const alreadySingleColumn = directCards.length === cards.length && !list.querySelector('.masonry-column');

        if (!alreadySingleColumn) {{
          list.replaceChildren(...cards);
        }}
      }};

      let scheduled = false;

      const preserveViewport = () => {{
        const x = window.scrollX;
        const y = window.scrollY;
        const height = list.getBoundingClientRect().height;

        // Safari may clamp the page scroll position to zero while all cards
        // are temporarily detached by replaceChildren(). Keep the old list
        // height for that frame, then restore the exact viewport afterwards.
        if (height > 0) list.style.minHeight = `${{Math.ceil(height)}}px`;

        return () => requestAnimationFrame(() => {{
          list.style.minHeight = '';
          if (window.scrollX !== x || window.scrollY !== y) {{
            window.scrollTo(x, y);
          }}
        }});
      }};

      const arrange = () => {{
        scheduled = false;

        const restoreViewport = preserveViewport();

        const cards = orderedCards();
        const count = columnCount();

        if (count <= 1) {{
          restoreSingleColumn(cards);
          restoreViewport();
          return;
        }}

        const columns = Array.from({{ length: count }}, () => {{
          const column = document.createElement('div');
          column.className = 'masonry-column';
          return column;
        }});

        // The columns must be in the document before measuring their height.
        // Detached elements have height 0, which makes every card go into the first column.
        list.replaceChildren(...columns);

        const heights = columns.map(() => 0);

        for (const card of cards) {{
          let target = 0;

          for (let index = 1; index < heights.length; index += 1) {{
            if (heights[index] < heights[target]) target = index;
          }}

          columns[target].appendChild(card);
          heights[target] = columns[target].getBoundingClientRect().height;
        }}

        restoreViewport();
      }};

      const schedule = () => {{
        if (scheduled) return;
        scheduled = true;
        requestAnimationFrame(arrange);
      }};

      window.addEventListener('resize', schedule, {{ passive: true }});
      window.addEventListener('load', schedule, {{ once: true }});

      for (const image of Array.from(list.querySelectorAll('img'))) {{
        if (!image.complete) image.addEventListener('load', schedule, {{ once: true }});
      }}

      schedule();
    }})();
  </script>
</body>
</html>
"""


def write_index(items: list[NewsItem], paths: SitePaths, rss_url: str) -> None:
    paths.index.write_text(render_index(items, rss_url), encoding="utf-8")
    print(f"[站点] 首页：{paths.href_for(paths.index)}")


def write_manifest(items: Iterable[NewsItem], paths: SitePaths) -> None:
    data = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "site_root": str(paths.root),
        "index": INDEX_FILE,
        "articles_dir": ARTICLES_DIR,
        "items": [asdict(item) for item in items],
    }
    paths.manifest.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"[站点] 清单：{paths.href_for(paths.manifest)}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build the WSJ Chinese RSS site.")
    parser.add_argument("--rss-url", default=os.environ.get("RSS_URL", RSS_URL))
    parser.add_argument("--out-dir", type=Path, default=Path(os.environ.get("OUT_DIR", "site")))
    parser.add_argument("--max-items", type=int, default=int(os.environ.get("MAX_ITEMS", "25")))
    parser.add_argument("--max-archive-items", type=int, default=int(os.environ.get("MAX_ARCHIVE_ITEMS", str(MAX_ARCHIVE_ITEMS))))
    parser.add_argument("--warp-port", type=int, default=int(os.environ.get("WARP_PORT", "40000")))
    parser.add_argument("--skip-fetch-html", action="store_true", default=env_bool("SKIP_FETCH_HTML"))
    parser.add_argument("--capture-attempts", type=int, default=int(os.environ.get("CAPTURE_ATTEMPTS", "3")))
    parser.add_argument("--page-load-timeout", type=int, default=int(os.environ.get("PAGE_LOAD_TIMEOUT", "90")))
    parser.add_argument("--ready-timeout", type=float, default=float(os.environ.get("READY_TIMEOUT", "45")))
    parser.add_argument("--page-settle-timeout", type=float, default=float(os.environ.get("PAGE_SETTLE_TIMEOUT", "24")))
    parser.add_argument("--page-settle-interval", type=float, default=float(os.environ.get("PAGE_SETTLE_INTERVAL", "1.0")))
    parser.add_argument("--page-stable-rounds", type=int, default=int(os.environ.get("PAGE_STABLE_ROUNDS", "3")))
    parser.add_argument("--initial-wait", type=float, default=float(os.environ.get("INITIAL_WAIT", "2")))
    parser.add_argument("--scroll-steps", type=int, default=int(os.environ.get("SCROLL_STEPS", "8")))
    parser.add_argument("--scroll-wait", type=float, default=float(os.environ.get("SCROLL_WAIT", "1.0")))
    parser.add_argument("--min-capture-paragraphs", type=int, default=int(os.environ.get("MIN_CAPTURE_PARAGRAPHS", "10")))
    parser.add_argument("--min-capture-attempts", type=int, default=int(os.environ.get("MIN_CAPTURE_ATTEMPTS", "1")))
    parser.add_argument("--low-capture-extra-timeout", type=float, default=float(os.environ.get("LOW_CAPTURE_EXTRA_TIMEOUT", "8")))
    parser.add_argument("--stop-after-good-capture", dest="stop_after_good_capture", action="store_true", default=env_bool("STOP_AFTER_GOOD_CAPTURE", True))
    parser.add_argument("--keep-trying-after-good-capture", dest="stop_after_good_capture", action="store_false")
    parser.add_argument("--click-expanders", action="store_true", default=env_bool("CLICK_EXPANDERS"))
    parser.add_argument("--window-width", type=int, default=int(os.environ.get("WINDOW_WIDTH", "1366")))
    parser.add_argument("--window-height", type=int, default=int(os.environ.get("WINDOW_HEIGHT", "900")))
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    paths = SitePaths(args.out_dir)
    previous_items = load_previous_items(paths)
    prepare_output(paths)

    if not ensure_warp_proxy(args.warp_port):
        log("MAIN", "WARP 不可用，停止。")
        return 1

    xml_text = fetch_rss(args.rss_url, args.warp_port)
    paths.feed.write_text(xml_text, encoding="utf-8")

    current_items = parse_rss(xml_text, args.max_items)
    if not current_items:
        log("MAIN", "RSS 中没有可用新闻。")
        return 1

    current_items = capture_articles(current_items, paths, args.warp_port, args)
    items = merge_archive_items(current_items, previous_items, args.max_archive_items)
    prune_articles(paths, items)
    write_index(items, paths, args.rss_url)
    write_manifest(items, paths)
    log("DONE", f"Pages 入口目录：{paths.root.as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
