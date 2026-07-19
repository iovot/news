#!/usr/bin/env bash
set -euo pipefail

export DEBIAN_FRONTEND=noninteractive

echo "[install] apt update"
sudo apt-get update -y

echo "[install] base packages"
sudo apt-get install -y ca-certificates curl gnupg lsb-release procps

echo "[install] Cloudflare WARP repository"
sudo install -d -m 0755 /usr/share/keyrings
curl -fsSL https://pkg.cloudflareclient.com/pubkey.gpg \
  | sudo gpg --yes --dearmor -o /usr/share/keyrings/cloudflare-warp-archive-keyring.gpg

echo "deb [signed-by=/usr/share/keyrings/cloudflare-warp-archive-keyring.gpg] https://pkg.cloudflareclient.com/ $(lsb_release -cs) main" \
  | sudo tee /etc/apt/sources.list.d/cloudflare-client.list >/dev/null

sudo apt-get update -y
sudo apt-get install -y cloudflare-warp

echo "[install] done"
