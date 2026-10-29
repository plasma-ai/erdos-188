"""Integer enclosures at a dyadic scale, and exact bounds of Q over a box.

An enclosure bounds a rational by integers at scale ``2**bits``: the floor of
a center coordinate and the ceiling of a radius. A displacement box built
from enclosures contains the true displacement, and the exact minimum and
maximum of ``4Q`` over the box decide most distance comparisons without
rational arithmetic. The two screens here only exclude; a survivor is decided
exactly by its caller.
"""

from __future__ import annotations

from fractions import Fraction

__all__ = ['floor_scaled', 'ceil_scaled', 'extrema', 'within', 'beyond']

# lambda^2 = 441/10000; a screen compares 441 Q against 10000 times a squared bound
_NUMERATOR = 441
_DENOMINATOR = 10_000


def floor_scaled(value: Fraction, bits: int) -> int:
    """Return the floor of ``value * 2**bits``."""
    return (value.numerator << bits) // value.denominator


def ceil_scaled(value: Fraction, bits: int) -> int:
    """Return the ceiling of ``value * 2**bits``."""
    return -(((-value.numerator) << bits) // value.denominator)


def extrema(a: int, b: int, c: int, d: int) -> tuple[int, int]:
    """Return the minimum and maximum of 4Q over the integer box [a,b] x [c,d].

    Q is convex, so its maximum is at a corner and its minimum is at the
    origin when the box contains it, else at a corner or at the interior
    critical point of an edge, where 4Q(x, -x/2) = 3x^2.
    """
    corners = tuple(4 * (x * x + x * y + y * y) for x in (a, b) for y in (c, d))
    minimum, maximum = min(corners), max(corners)
    if a <= 0 <= b and c <= 0 <= d:
        return 0, maximum
    for x in (a, b):
        if 2 * c <= -x <= 2 * d:
            minimum = min(minimum, 3 * x * x)
    for y in (c, d):
        if 2 * a <= -y <= 2 * b:
            minimum = min(minimum, 3 * y * y)
    return minimum, maximum


def within(box: tuple[int, int, int, int], bound: int) -> bool:
    """Decide that every displacement in the box is nearer than the bound.

    The box bounds the scaled displacement and ``bound`` the scaled distance;
    nearer means ``lambda^2 Q < bound^2`` at that common scale. A nonpositive
    bound admits nothing.
    """
    if bound <= 0:
        return False
    _, maximum = extrema(*box)
    return _NUMERATOR * maximum < 4 * _DENOMINATOR * bound * bound


def beyond(box: tuple[int, int, int, int], bound: int) -> bool:
    """Decide that every displacement in the box is farther than the bound.

    Farther means ``lambda^2 Q > bound^2`` at the common scale, for a
    nonnegative bound.
    """
    minimum, _ = extrema(*box)
    return _NUMERATOR * minimum > 4 * _DENOMINATOR * bound * bound
