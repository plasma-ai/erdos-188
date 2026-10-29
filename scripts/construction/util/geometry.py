"""The fixed axial geometry of the construction and its covering cells.

Centers are axial coordinates modulo the period, the physical squared norm is
``lambda^2 Q`` with ``Q(s,t) = s^2 + st + t^2``, and the sixfold rotation is
``rho(s,t) = (-t, s+t)``. Direction cells, translation squares and the
preorder tree grammar follow the covering argument of the method.
"""

from __future__ import annotations

import dataclasses
import math
from fractions import Fraction

from .rationals import Site

__all__ = [
    'PERIOD',
    'SCALE',
    'SCALE_SQUARED',
    'HALF',
    'STEPS',
    'SQRT3_UPPER',
    'quadratic',
    'distance_squared',
    'rotate',
    'normalize',
    'nearest_lift',
    'admit_site',
    'Direction',
    'direction',
    'half_width',
    'midpoint',
    'Cell',
    'ROOT',
    'Preorder',
]

PERIOD = 59
SCALE = Fraction(21, 100)
SCALE_SQUARED = SCALE * SCALE
HALF = Fraction(1, 2)
# the centered progression indices of a 42-term target
STEPS = tuple(range(-21, 21))
# a rational upper bound for sqrt(3): 1733^2 = 3003289 > 3000000
SQRT3_UPPER = Fraction(1733, 1000)


def quadratic(s: Fraction, t: Fraction) -> Fraction:
    """Return the axial quadratic form Q(s,t) = s^2 + st + t^2."""
    return s * s + s * t + t * t


def distance_squared(s: Fraction, t: Fraction) -> Fraction:
    """Return the physical squared norm of an axial vector."""
    return SCALE_SQUARED * quadratic(s, t)


def rotate(s: Fraction, t: Fraction) -> tuple[Fraction, Fraction]:
    """Rotate an axial vector by pi/3 without normalizing the result."""
    return -t, s + t


def normalize(value: Fraction) -> tuple[Fraction, int]:
    """Reduce a coordinate into [0, 59) and return the period shift removed."""
    shift = math.floor(value / PERIOD)
    return value - PERIOD * shift, shift


def nearest_lift(value: Fraction) -> int:
    """Return the integer nearest to value/59, rounding a half-period tie up."""
    return math.floor(value / PERIOD + HALF)


def admit_site(site: Site) -> None:
    """Require exact Fraction fields, a normalized center and a radius in (0,1/2)."""
    if type(site) is not tuple or len(site) != 3:
        raise ValueError('A site must be a triple')
    for value in site:
        if type(value) is not Fraction:
            raise ValueError('Every site field must be an exact Fraction')
    s, t, radius = site
    if not (0 <= s < PERIOD and 0 <= t < PERIOD):
        raise ValueError('A site center lies outside [0,59)^2')
    if not 0 < radius < HALF:
        raise ValueError('A site radius lies outside (0,1/2)')


@dataclasses.dataclass(frozen=True, slots=True)
class Direction:
    """The midpoint direction and error bound of one direction cell."""

    vs: Fraction
    vt: Fraction
    error: Fraction


def direction(d: int, i: int) -> Direction:
    """Return v(tau_0) and E_u(d,i) for the direction cell I_{d,i}."""
    scale = 1 << d
    tau = Fraction(2 * i + 1 - 4 * scale, 2 * scale)
    endpoint = Fraction(i + 1 - 2 * scale, scale)
    denominator = tau * tau + tau + 1
    # the axial direction v(tau_0) with Q(v) = (100/21)^2
    vs = (tau * tau - 1) / (SCALE * denominator)
    vt = -tau * (tau + 2) / (SCALE * denominator)
    # the uniform rational bound on the direction error over the cell
    error = SQRT3_UPPER / (2 * scale * (endpoint * endpoint + endpoint + 1))
    return Direction(vs, vt, error)


def half_width(e: int) -> Fraction:
    """Return the axial half-width 59/2^(e+1) of a depth-e translation square."""
    return Fraction(PERIOD, 1 << (e + 1))


def midpoint(e: int, h: int, k: int) -> tuple[Fraction, Fraction]:
    """Return the axial midpoint of the translation square C_{e,h,k}."""
    denominator = 1 << (e + 1)
    return (
        Fraction(PERIOD * (2 * h + 1), denominator),
        Fraction(PERIOD * (2 * k + 1), denominator),
    )


@dataclasses.dataclass(frozen=True, slots=True)
class Cell:
    """A cell state (d,i;e,h,k): direction interval and translation square."""

    d: int
    i: int
    e: int
    h: int
    k: int

    def address(self: Cell) -> tuple[int, int, int, int, int]:
        """Return the five fields in wire order."""
        return (self.d, self.i, self.e, self.h, self.k)

    def children(self: Cell, kind: str) -> tuple[Cell, ...]:
        """Return the ordered children of a direction or translation split."""
        if kind == 'D':
            return tuple(
                Cell(self.d + 1, 2 * self.i + child, self.e, self.h, self.k)
                for child in (0, 1)
            )
        if kind == 'T':
            return tuple(
                Cell(self.d, self.i, self.e + 1, 2 * self.h + eps, 2 * self.k + delta)
                for eps, delta in ((0, 0), (0, 1), (1, 0), (1, 1))
            )
        raise ValueError(f'Unknown split kind: {kind!r}')


ROOT = Cell(0, 0, 0, 0, 0)


class Preorder:
    """Derive every cell of a preorder record stream from the global root."""

    def __init__(self: Preorder) -> None:
        """Start at the root with no record consumed."""
        self.pending = [ROOT]

    @property
    def complete(self: Preorder) -> bool:
        """Return whether the root subtree has closed."""
        return not self.pending

    def visit(self: Preorder, kind: str) -> Cell:
        """Consume one D, T or S record, returning the cell it describes."""
        if not self.pending:
            raise ValueError('A record follows the complete root subtree')
        cell = self.pending.pop()
        if kind in ('D', 'T'):
            self.pending.extend(reversed(cell.children(kind)))
        elif kind != 'S':
            raise ValueError(f'Unknown record kind: {kind!r}')
        return cell
