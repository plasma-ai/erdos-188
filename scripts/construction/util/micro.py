"""The cell-service disk that repairs a cell no base disk serves.

For a cell ``(d,i;e,h,k)`` and a step ``j`` the disk is centered at the image
of the translation square's midpoint under the step, reduced into the period
square, with radius ``(147/400) w_e + |j| E_u(d,i)`` for the axial half-width
``w_e = 59/2^(e+1)``. The factor ``147/400 = lambda * 7/4`` exceeds
``lambda * sqrt(3)``, so the disk passes the four-corner leaf test at that
cell, step and lift strictly whenever its radius stays below one half.
"""

from __future__ import annotations

from fractions import Fraction

from .geometry import Cell, Direction, half_width, midpoint, normalize
from .rationals import Site

__all__ = ['MICRO_FACTOR', 'service_disk']

# lambda * 7/4; Lemma A: 3 * 441/10000 = 1323/10000 < (147/400)^2 = 21609/160000
MICRO_FACTOR = Fraction(147, 400)


def service_disk(
    cell: Cell, step: int, direction: Direction,
) -> tuple[Site, tuple[int, int]]:
    """Return the cell-service disk of a cell and step with its reducing lift."""
    midpoint_s, midpoint_t = midpoint(cell.e, cell.h, cell.k)
    center_s, lift_s = normalize(midpoint_s + step * direction.vs)
    center_t, lift_t = normalize(midpoint_t + step * direction.vt)
    radius = MICRO_FACTOR * half_width(cell.e) + abs(step) * direction.error
    return (center_s, center_t, radius), (lift_s, lift_t)
