#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 scripts/verify_G112_exact.py
python3 scripts/check_norm_mod.py
python3 scripts/check_P_root_interval.py
python3 scripts/circle_radius_root_interval_certificate.py
sha256sum -c SHA256SUMS
