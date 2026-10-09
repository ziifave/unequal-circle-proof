#!/usr/bin/env python3
"""Convert 113x16 monic K-coordinates into primitive integral coordinates.

All calculations use Python's unbounded integers and rational numbers.
The relative paths refer only to the unpacked package.
"""
from pathlib import Path
from fractions import Fraction
from math import gcd, lcm
import csv
import sys

sys.set_int_max_str_digits(0)
BASE = Path(__file__).resolve().parents[1]
SRC = BASE / 'data/G112_monic_components.tsv'
OUT = BASE / 'data/G112_primitive_components.tsv'
with SRC.open(newline='') as f:
    rows = list(csv.DictReader(f, delimiter='\t'))
assert len(rows) == 113
B = [[Fraction(row[f'basis_{m}']) for m in range(16)] for row in rows]
assert [int(row['power']) for row in rows] == list(range(113))
assert B[-1][0] == 1 and all(z == 0 for z in B[-1][1:])
common_den = 1
for row in B:
    for z in row:
        common_den = lcm(common_den, z.denominator)
V = [[z.numerator * (common_den // z.denominator) for z in row] for row in B]
content = 0
for row in V:
    for v in row:
        content = gcd(content, v)
assert content > 0
V = [[v // content for v in row] for row in V]
assert V[-1][0] > 0
with OUT.open('w', newline='') as f:
    w = csv.writer(f, delimiter='\t', lineterminator='\r\n')
    w.writerow(['power'] + [f'basis_{m}' for m in range(16)])
    for i, row in enumerate(V):
        w.writerow([i, *row])
print('WROTE', OUT.relative_to(BASE), '113 degrees, 16 components each')
