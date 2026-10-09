#!/usr/bin/env python3
"""Translate the compact Stage 3 prefix certificate into a Lean value."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "research/fifteen_equal_completion/candidate_bundle"
CERT = BASE / "stage3_certificate_000000010101011.txt"
OUT = ROOT / "problems/packing-disks-radii-sqrt1-to-sqrt10-in-a-circle/lean/CirclePacking/FifteenStage3CertificateData.lean"


def main() -> None:
    line = CERT.read_text().strip()
    pattern, encoded = line.split("\t", 1)
    if pattern != "000000010101011":
        raise ValueError(f"unexpected pattern {pattern}")
    if not encoded or any(c not in "BSORMC0123456789ABCDEFOLU" for c in encoded):
        raise ValueError("certificate contains a character outside the compact alphabet")
    output = (
        "namespace CirclePacking\n\n"
        "def stage3Pattern000000010101011Text : String :=\n  \""
        + encoded
        + "\""
        + "\n\nend CirclePacking\n"
    )
    if not OUT.exists() or OUT.read_text() != output:
        OUT.write_text(output)
    print(f"{pattern}: encoded={len(encoded)} characters; Lean source={OUT.stat().st_size} bytes")


if __name__ == "__main__":
    main()
