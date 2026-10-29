"""The four-corner leaf test and an exhaustive index of the disks that can pass it.

A leaf ``(j, disk, n)`` serves the cell ``(d,i;e,h,k)`` when the usable radius
``r_use = r - |j| E_u(d,i)`` is positive and every corner ``q`` of the
translation square satisfies ``lambda^2 Q(q + j v(tau_0) - a - 59n) <=
r_use^2``: the leaf test of the covering argument, equality admitted. The
index files the base disks so that, for a cell and step, every disk that can
pass is visited, most are excluded by integer enclosures, and the survivors
are decided exactly in step order and then table order.

Completeness. The square's image is convex, so a passing disk copy keeps the
image of the square's midpoint ``m = q_mid + j v(tau_0)`` within physical
distance ``r_use`` of its center; by ``Q >= 3 v_i^2 / 4`` each axial
coordinate of ``m - a - 59n`` is then below ``2 r_use / (lambda sqrt 3) <
(40/7) r_use <= (40/7) r``, the disk's *reach*. The reach is below 20/7, so
the lift is the nearest lift of ``m - a`` in each coordinate and is unique.
A disk of reach at most ``2**-c`` is filed on the grid of cell size ``2**-c``
(``59 * 2**c`` cells per period, so the wrap is exact) and can serve only
from a grid cell within one of the normalized midpoint image's cell; a disk
of reach above one is filed on the unit grid and can serve only from within
three cells. Every disk that can pass is therefore among the candidates.

Necessity of size. The corners ``(w,w)`` and ``(-w,-w)`` of the square are
opposite, and ``Q(x + c) + Q(x - c) >= 2 Q(c)`` gives some corner with
``Q >= 3 w^2``; so a passing disk needs ``r_use^2 >= 3 lambda^2 w^2``, and a
whole grid level whose disks fall short of that at a cell is skipped.
"""

from __future__ import annotations

import dataclasses
from fractions import Fraction
from typing import Optional

from .enclosure import beyond, ceil_scaled, floor_scaled
from .geometry import (
    PERIOD,
    Cell,
    Direction,
    distance_squared,
    half_width,
    midpoint,
)
from .rationals import Site

__all__ = ['STEP_ORDER', 'REACH', 'BITS', 'Leaf', 'serves', 'Index']

# the step order of the search: zero, then each magnitude with the negative first
STEP_ORDER = (
    0, *(step for magnitude in range(1, 21) for step in (-magnitude, magnitude)), -21,
)
# a passing disk copy keeps the midpoint image within axial distance (40/7) r_use
REACH = Fraction(40, 7)
# integer enclosures at scale 2**64 decide almost every candidate without rational work
BITS = 64
_SCALE = 1 << BITS
_PERIOD_SCALED = PERIOD << BITS
_HALF_PERIOD_SCALED = PERIOD << (BITS - 1)
# grid levels are multiples of this many bits; a disk lies on the coarsest that holds it
_LEVEL_STRIDE = 2
# lambda^2 = 441/10000; a size screen compares 10000 r_use^2 against 3 * 441 w^2
_NUMERATOR = 441
_DENOMINATOR = 10_000


@dataclasses.dataclass(frozen=True, slots=True)
class Leaf:
    """A passing witness: the step, the disk's table index and its lift."""

    step: int
    ordinal: int
    lift: tuple[int, int]


@dataclasses.dataclass(frozen=True)
class _Level:
    """One grid level: its cell size in bits, the neighbor range and the disks."""

    bits: int
    # grid cells per period, and how many cells a disk of the level can reach
    cells: int
    reach: int
    radius: Fraction
    radius_scaled: int
    buckets: dict[tuple[int, int], tuple[int, ...]]


def serves(
    cell: Cell, step: int, direction: Direction, site: Site, lift: tuple[int, int],
) -> bool:
    """Decide the four-corner leaf test exactly."""
    usable = site[2] - abs(step) * direction.error
    if usable <= 0:
        return False
    midpoint_s, midpoint_t = midpoint(cell.e, cell.h, cell.k)
    width = half_width(cell.e)
    offset_s = midpoint_s + step * direction.vs - site[0] - PERIOD * lift[0]
    offset_t = midpoint_t + step * direction.vt - site[1] - PERIOD * lift[1]
    bound = usable * usable
    for ds in (-width, width):
        for dt in (-width, width):
            if distance_squared(offset_s + ds, offset_t + dt) > bound:
                return False
    return True


def _too_small(usable: int, width: int) -> bool:
    """Decide from scaled bounds that a usable radius cannot cover a square."""
    return _DENOMINATOR * usable * usable < 3 * _NUMERATOR * width * width


def _level_bits(reach: Fraction) -> int:
    """Return the coarsest level, a stride multiple, whose cells hold the reach."""
    if reach > 1:
        return 0
    # floor(log2(1/reach)) from the integer part of 1/reach
    exact = (reach.denominator // reach.numerator).bit_length() - 1
    return min(exact - exact % _LEVEL_STRIDE, BITS)


class Index:
    """The base disks on dyadic grids by reach, with their enclosures."""

    def __init__(self: Index, base: tuple[Site, ...]) -> None:
        """File every disk on the level of its reach."""
        self.base = base
        # floors of the center coordinates and the ceiling of the radius
        self.enclosures = tuple(
            (
                floor_scaled(site[0], BITS),
                floor_scaled(site[1], BITS),
                ceil_scaled(site[2], BITS),
            )
            for site in base
        )
        self.max_radius = max((site[2] for site in base), default=Fraction(0))
        grouped: dict[int, list[int]] = {}
        for index, site in enumerate(base):
            grouped.setdefault(_level_bits(REACH * site[2]), []).append(index)
        levels = []
        for bits in sorted(grouped):
            members = grouped[bits]
            radius = max(base[index][2] for index in members)
            buckets: dict[tuple[int, int], list[int]] = {}
            for index in members:
                enclosure = self.enclosures[index]
                key = (enclosure[0] >> (BITS - bits), enclosure[1] >> (BITS - bits))
                buckets.setdefault(key, []).append(index)
            levels.append(_Level(
                bits, PERIOD << bits, ceil_scaled(REACH * radius, bits), radius,
                ceil_scaled(radius, BITS),
                {key: tuple(group) for key, group in buckets.items()},
            ))
        self.levels = tuple(levels)
        self.lookups = 0
        self.candidates = 0
        self.exact_tests = 0

    def serve(self: Index, cell: Cell, direction: Direction) -> Optional[Leaf]:
        """Return the first passing leaf in step order and table order, if any."""
        midpoint_s, midpoint_t = midpoint(cell.e, cell.h, cell.k)
        width = half_width(cell.e)
        width_floor = floor_scaled(width, BITS)
        # levels whose largest disk could cover this square at some step
        levels = [
            level for level in self.levels
            if not _too_small(level.radius_scaled, width_floor)
        ]
        if not levels:
            return None
        for step in STEP_ORDER:
            erosion_floor = floor_scaled(abs(step) * direction.error, BITS)
            image_s = midpoint_s + step * direction.vs
            image_t = midpoint_t + step * direction.vt
            # scaled floors of the midpoint image and of the four corners
            scaled_s = floor_scaled(image_s, BITS)
            scaled_t = floor_scaled(image_t, BITS)
            low_s = floor_scaled(image_s - width, BITS)
            high_s = floor_scaled(image_s + width, BITS)
            low_t = floor_scaled(image_t - width, BITS)
            high_t = floor_scaled(image_t + width, BITS)
            # the normalized midpoint image locates the grid cells to visit
            normal_s, normal_t = scaled_s % _PERIOD_SCALED, scaled_t % _PERIOD_SCALED
            candidates: list[int] = []
            for level in levels:
                usable_max = level.radius_scaled - erosion_floor
                if usable_max <= 0 or _too_small(usable_max, width_floor):
                    continue
                shift = BITS - level.bits
                key_s, key_t = normal_s >> shift, normal_t >> shift
                buckets, cells = level.buckets, level.cells
                for ds in range(-level.reach, level.reach + 1):
                    grid_s = (key_s + ds) % cells
                    for dt in range(-level.reach, level.reach + 1):
                        self.lookups += 1
                        members = buckets.get((grid_s, (key_t + dt) % cells))
                        if members is not None:
                            candidates.extend(members)
            if not candidates:
                continue
            candidates.sort()
            self.candidates += len(candidates)
            for ordinal in candidates:
                center_s, center_t, radius_ceil = self.enclosures[ordinal]
                usable = radius_ceil - erosion_floor
                if usable <= 0:
                    continue
                # the forced lift, read from the scaled midpoint displacement
                lift_s = (scaled_s - center_s + _HALF_PERIOD_SCALED) // _PERIOD_SCALED
                lift_t = (scaled_t - center_t + _HALF_PERIOD_SCALED) // _PERIOD_SCALED
                copy_s = center_s + _PERIOD_SCALED * lift_s
                copy_t = center_t + _PERIOD_SCALED * lift_t
                # every corner's displacement box must be able to lie within r_use
                excluded = False
                for corner_s in (low_s - copy_s, high_s - copy_s):
                    for corner_t in (low_t - copy_t, high_t - copy_t):
                        box = (corner_s - 1, corner_s + 1, corner_t - 1, corner_t + 1)
                        if beyond(box, usable):
                            excluded = True
                if excluded:
                    continue
                self.exact_tests += 1
                lift = (lift_s, lift_t)
                if serves(cell, step, direction, self.base[ordinal], lift):
                    return Leaf(step, ordinal, lift)
        return None
