"""Small, auditable directed-rounding decimal interval implementation.

All endpoints are finite Decimal values.  Each operation evaluates its lower
endpoint with ROUND_FLOOR and its upper endpoint with ROUND_CEILING.  This is
deliberately small: the eventual independent certificate verifier uses the
same limited set of operations.
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from typing import Iterable


PRECISION = 90


def set_precision(digits: int) -> None:
    if digits < 30:
        raise ValueError("at least 30 decimal digits are required")
    global PRECISION
    PRECISION = digits


def _context(rounding: str) -> Context:
    return Context(prec=PRECISION, rounding=rounding)


def _binary(a: Decimal, b: Decimal, op: str, rounding: str) -> Decimal:
    with localcontext(_context(rounding)):
        if op == "+":
            return a + b
        if op == "-":
            return a - b
        if op == "*":
            return a * b
    raise ValueError(op)


def _sqrt(value: Decimal, rounding: str) -> Decimal:
    # Python's decimal sqrt is correctly rounded, but its implementation does
    # not honour directed rounding modes.  Certify direction afterwards using
    # exact-enough products of finite decimals and move by one ulp as needed.
    with localcontext(_context(ROUND_FLOOR)) as ctx:
        candidate = ctx.sqrt(value)
        if rounding == ROUND_FLOOR:
            while _exact_product(candidate, candidate) > value:
                candidate = candidate.next_minus(context=ctx)
        elif rounding == ROUND_CEILING:
            while _exact_product(candidate, candidate) < value:
                candidate = candidate.next_plus(context=ctx)
        else:
            raise ValueError(rounding)
        return candidate


def _exact_product(a: Decimal, b: Decimal) -> Decimal:
    # Each operand has at most PRECISION significant digits.  The product is
    # therefore exact in this much larger decimal context.
    with localcontext(Context(prec=2 * PRECISION + 20, rounding=ROUND_CEILING)) as ctx:
        return ctx.multiply(a, b)


def D(value: int | str | Decimal) -> Decimal:
    """Create an exact decimal input; floats are intentionally forbidden."""
    if isinstance(value, float):
        raise TypeError("float constants are forbidden in rigorous arithmetic")
    return Decimal(value)


@dataclass(frozen=True, slots=True)
class Interval:
    lo: Decimal
    hi: Decimal

    def __post_init__(self) -> None:
        if not self.lo.is_finite() or not self.hi.is_finite() or self.lo > self.hi:
            raise ValueError(f"invalid interval [{self.lo}, {self.hi}]")

    @classmethod
    def point(cls, value: int | str | Decimal) -> "Interval":
        d = D(value)
        return cls(d, d)

    @classmethod
    def sqrt_integer(cls, value: int) -> "Interval":
        if value < 0:
            raise ValueError("square root of a negative integer")
        x = D(value)
        return cls(_sqrt(x, ROUND_FLOOR), _sqrt(x, ROUND_CEILING))

    @classmethod
    def sqrt_nonnegative(cls, value: Decimal) -> "Interval":
        if value < 0:
            raise ValueError("square root of a negative value")
        return cls(_sqrt(value, ROUND_FLOOR), _sqrt(value, ROUND_CEILING))

    @property
    def width(self) -> Decimal:
        return _binary(self.hi, self.lo, "-", ROUND_CEILING)

    @property
    def midpoint(self) -> Decimal:
        with localcontext(_context(ROUND_FLOOR)):
            return (self.lo + self.hi) / D(2)

    def __add__(self, other: "Interval") -> "Interval":
        return Interval(
            _binary(self.lo, other.lo, "+", ROUND_FLOOR),
            _binary(self.hi, other.hi, "+", ROUND_CEILING),
        )

    def __sub__(self, other: "Interval") -> "Interval":
        return Interval(
            _binary(self.lo, other.hi, "-", ROUND_FLOOR),
            _binary(self.hi, other.lo, "-", ROUND_CEILING),
        )

    def __mul__(self, other: "Interval") -> "Interval":
        values_lo = [_binary(a, b, "*", ROUND_FLOOR) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        values_hi = [_binary(a, b, "*", ROUND_CEILING) for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(values_lo), max(values_hi))

    def square(self) -> "Interval":
        if self.lo <= 0 <= self.hi:
            lo = D(0)
        else:
            lo = min(_binary(self.lo, self.lo, "*", ROUND_FLOOR), _binary(self.hi, self.hi, "*", ROUND_FLOOR))
        hi = max(_binary(self.lo, self.lo, "*", ROUND_CEILING), _binary(self.hi, self.hi, "*", ROUND_CEILING))
        return Interval(lo, hi)

    def split(self) -> tuple["Interval", "Interval"]:
        if self.lo == self.hi:
            raise ValueError("cannot split a point interval")
        mid = self.midpoint
        if mid <= self.lo or mid >= self.hi:
            raise ValueError("precision exhausted while splitting interval")
        return Interval(self.lo, mid), Interval(mid, self.hi)

    def to_json(self) -> list[str]:
        return [str(self.lo), str(self.hi)]

    @classmethod
    def from_json(cls, raw: Iterable[str]) -> "Interval":
        lo, hi = raw
        return cls(D(lo), D(hi))
