#!/usr/bin/env python3
"""Exact audit of the fixed coarse angular table in verify_integer_cycles.cpp."""
from fractions import Fraction as F
from math import factorial

SCALE = 2800
Q = (
    (1610, 0, 0, 840),
    (0, 0, 0, 0),
    (0, 0, 3360, 2408),
    (840, 0, 2408, 2408),
)

# Rational boxes enclosing the four classes O, small, medium, and high.
# O contains [L,b]; high contains [5/3,L]. The zero-containing class has no
# angular restriction in this deliberately coarse table.
R = (
    (F(2385, 1000), F(3522, 1000)),
    (F(0), F(1)),
    (F(1), F(5, 3)),
    (F(5, 3), F(2385432, 1000000)),
)


def cosine_lower(q):
    """Taylor P18 minus a rigorous Lagrange remainder bound."""
    x = F(q, SCALE)
    x2 = x * x
    term = F(1)
    p18 = term
    for j in range(1, 10):
        term *= -x2 / F((2 * j - 1) * (2 * j))
        p18 += term
    return p18 - x**19 / factorial(19)


def c(x, y):
    return (x*x + y*y - 4) / (2*x*y)


for i in range(4):
    for j in range(4):
        q = Q[i][j]
        if q == 0:
            continue
        assert R[i][0] > 0 and R[j][0] > 0
        assert R[i][0] + R[j][0] >= 2
        assert R[i][1] - R[j][0] < 2
        assert R[j][1] - R[i][0] < 2
        xmax = max(c(x, y) for x in R[i] for y in R[j])
        assert cosine_lower(q) >= xmax, (i, j, q, cosine_lower(q), xmax)

print("PASS: every positive entry of the fixed 4x4 table is a rigorous angular lower bound")
print("cosine lower bound = P18(x) - x^19/19!, with exact Fraction arithmetic")
