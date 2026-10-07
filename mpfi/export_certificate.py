"""Convert the JSON Farkas certificate to a simple C-reader format."""
from __future__ import annotations

import json
from pathlib import Path
import sys


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: export_certificate.py INPUT.json OUTPUT.dat")
    data = json.loads(Path(sys.argv[1]).read_text())
    out = [str(data["rho"])]
    for record in data["orders"]:
        out.append(" ".join(map(str, record["order"] + record["coefficients"])))
    Path(sys.argv[2]).write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
