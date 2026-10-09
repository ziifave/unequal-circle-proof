"""Rational Machin-series bounds used by all angle tables and edge weights."""
from fractions import Fraction as F


def atan_partial(x, terms):
    return sum(((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1) for k in range(terms))


# Alternating-series bounds: even term count ends negative (lower), odd ends positive (upper).
a5_lower = atan_partial(F(1, 5), 6)
a5_upper = atan_partial(F(1, 5), 7)
a239_lower = atan_partial(F(1, 239), 2)
a239_upper = atan_partial(F(1, 239), 1)
# Machin's identity pi = 16 atan(1/5) - 4 atan(1/239).
pi_lower = 16 * a5_lower - 4 * a239_upper
pi_upper = 16 * a5_upper - 4 * a239_lower
assert pi_lower < pi_upper
assert pi_lower > F(8790, 2800)  # every q/2800 used by the bisection lies below pi
assert pi_upper < F(22, 7)      # hence 2*pi < 44/7 = 17600/2800
print("PASS: exact Machin-series rational bounds certify 8790/2800 < pi < 22/7")
