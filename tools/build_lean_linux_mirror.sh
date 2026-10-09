#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mirror_root="${UNEQUAL_LAKE_MIRROR:-${HOME}/unequal-circle-proof-linux}"
project_rel="problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle"
source_lean="$repo_root/$project_rel/lean"
mirror_repo="$mirror_root/unequal-circle-proof"
mirror_lean="$mirror_repo/$project_rel/lean"
cache_marker="$mirror_root/.lake-cache-seeded"

mkdir -p "$mirror_lean" "$mirror_repo/problems/packing-15-equal-disks-in-a-circle" \
  "$mirror_repo/$project_rel"

# Keep the persistent Lake cache on the Linux filesystem; sync only project
# sources and the two external files embedded by include_str.
rsync -ac --delete --exclude='/.lake/' "$source_lean/" "$mirror_lean/"
rsync -ac "$repo_root/$project_rel/certificates/" \
  "$mirror_repo/$project_rel/certificates/"
rsync -ac --delete "$repo_root/problems/packing-15-equal-disks-in-a-circle/candidate_bundle/" \
  "$mirror_repo/problems/packing-15-equal-disks-in-a-circle/candidate_bundle/"

if [[ ! -e "$cache_marker" ]]; then
  echo "Seeding the Linux mirror with the existing Lake cache (one-time copy)."
  mkdir -p "$mirror_lean/.lake"
  rsync -a --info=progress2 "$source_lean/.lake/" "$mirror_lean/.lake/"
  touch "$cache_marker"
fi

cd "$mirror_lean"
if (($# == 0)); then
  set -- CirclePacking
fi
exec lake build "$@"
