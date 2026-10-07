"""Create a manifest linking branch-tree frontier nodes to Farkas records."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("farkas", type=Path)
    parser.add_argument("--nodes", nargs="+", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    with gzip.open(args.farkas, "rt", encoding="utf-8") as stream:
        rows = [json.loads(line) for line in stream if line.strip()]
    records = {}
    for row in rows[1:]:
        records.setdefault(row["node"], 0)
        records[row["node"]] += 1
    expected = {node: 20160 for node in args.nodes}
    if {node: records.get(node, 0) for node in args.nodes} != expected:
        raise SystemExit({node: records.get(node, 0) for node in args.nodes})
    payload = {
        "kind": "frontier-farkas-manifest",
        "status": "partial-frontier-only",
        "farkas_artifact": str(args.farkas),
        "sha256": sha256(args.farkas),
        "nodes": {node: {"records": records[node], "status": "certified-local"}
                  for node in args.nodes},
        "unresolved_frontier_is_not_claimed_closed": True,
    }
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
