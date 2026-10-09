#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
fast_root="${LEAN_FIFTEEN_STAGE0_FAST_ROOT:-/tmp/unequal-fifteen-stage0-lean-fast}"
lean_root="$fast_root/problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle/lean"
bundle_root="$fast_root/research/fifteen_equal_completion/candidate_bundle"
source_lean_root="$repo_root/problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle/lean"
source_bundle_root="$repo_root/research/fifteen_equal_completion/candidate_bundle"

mkdir -p "$lean_root/CirclePacking" "$bundle_root"
cp "$source_lean_root/lean-toolchain" "$lean_root/"
cp "$source_lean_root/CirclePacking/FifteenTickBounds.lean" "$lean_root/CirclePacking/"
cp "$source_lean_root/CirclePacking/FifteenStageZero.lean" "$lean_root/CirclePacking/"
cp "$source_bundle_root/stage0_cycles.txt" "$bundle_root/"
cp "$source_bundle_root/stage0_orbits.txt" "$bundle_root/"

cat > "$lean_root/lakefile.toml" <<'EOF'
name = "fifteenStageZeroFast"
defaultTargets = ["CirclePacking"]

[[lean_lib]]
name = "CirclePacking"
EOF

cd "$lean_root"
LEAN_NUM_THREADS=1 lake build CirclePacking.FifteenStageZero
