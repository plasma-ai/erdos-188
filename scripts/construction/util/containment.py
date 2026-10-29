"""Containment routes from a disk into a lifted carrier, found exactly.

A disk ``(a, r)`` lies in the lifted carrier ``(c + 59n, R)`` when
``R - r >= 0`` and ``lambda^2 Q(a - c - 59n) <= (R - r)^2``, both boundaries
included: the route of the safety argument. The index below finds one such
carrier and lift for a disk, screening most carriers by integer enclosures
and deciding the survivors in exact rational arithmetic.

Completeness. Both radii lie in ``(0, 1/2)``, so a route needs
``lambda^2 Q(v) < 1/4`` for the displacement ``v = a - c - 59n``, hence
``Q(v) < 2500/441`` and, since ``Q(v) >= 3 v_i^2 / 4``, each coordinate has
``|v_i| < 3``. The integer parts of ``a`` and of the carrier copy therefore
differ by at most 3 in each coordinate, so bucketing the carriers by integer
parts and visiting the offsets in ``[-3, 3]^2`` around the disk's bucket, with
the lift read off the offset, meets every containing copy exactly once.
"""

from __future__ import annotations

import dataclasses
from typing import Optional

from .enclosure import beyond, ceil_scaled, floor_scaled
from .geometry import PERIOD, distance_squared
from .rationals import Site

__all__ = ['Route', 'Index']

# every coordinate of a containing displacement has absolute value below 3
_OFFSET_BOUND = 3
# integer enclosures at scale 2**16 decide most carriers without rational work
_BITS = 16
_PERIOD_SCALED = PERIOD << _BITS


@dataclasses.dataclass(frozen=True, slots=True)
class Route:
    """One carrier copy containing a disk: the carrier's table index and lift."""

    carrier: int
    lift: tuple[int, int]


class Index:
    """The carriers bucketed by the integer parts of their centers."""

    def __init__(self: Index, carriers: tuple[Site, ...]) -> None:
        """Enclose every carrier and file it under its integer-part cell."""
        self.carriers = carriers
        # floors of the center coordinates and the ceiling of the radius
        self.enclosures = tuple(
            (
                floor_scaled(site[0], _BITS),
                floor_scaled(site[1], _BITS),
                ceil_scaled(site[2], _BITS),
            )
            for site in carriers
        )
        grouped: dict[tuple[int, int], list[int]] = {}
        for index, site in enumerate(carriers):
            key = (floor_scaled(site[0], 0), floor_scaled(site[1], 0))
            grouped.setdefault(key, []).append(index)
        # members by decreasing radius, so a scan stops at the first carrier too small
        self.buckets = {
            key: tuple(sorted(members, key=lambda index: (-carriers[index][2], index)))
            for key, members in grouped.items()
        }
        self.pair_screens = 0
        self.exact_tests = 0

    def container(self: Index, site: Site) -> Optional[Route]:
        """Return the first containing carrier copy in offset order, largest first."""
        s, t, radius = site
        cell_s, cell_t = floor_scaled(s, 0), floor_scaled(t, 0)
        scaled_s, scaled_t = floor_scaled(s, _BITS), floor_scaled(t, _BITS)
        radius_floor = floor_scaled(radius, _BITS)
        for ds in range(-_OFFSET_BOUND, _OFFSET_BOUND + 1):
            for dt in range(-_OFFSET_BOUND, _OFFSET_BOUND + 1):
                raw_s, raw_t = cell_s + ds, cell_t + dt
                lift = (raw_s // PERIOD, raw_t // PERIOD)
                members = self.buckets.get(
                    (raw_s - PERIOD * lift[0], raw_t - PERIOD * lift[1]),
                )
                if members is None:
                    continue
                shift_s = scaled_s - _PERIOD_SCALED * lift[0]
                shift_t = scaled_t - _PERIOD_SCALED * lift[1]
                for index in members:
                    self.pair_screens += 1
                    carrier_s, carrier_t, carrier_radius = self.enclosures[index]
                    # the gap bounds the displacement; every later carrier is smaller
                    gap = carrier_radius - radius_floor
                    if gap < 0:
                        break
                    box = (
                        shift_s - carrier_s - 1, shift_s - carrier_s + 1,
                        shift_t - carrier_t - 1, shift_t - carrier_t + 1,
                    )
                    if beyond(box, gap):
                        continue
                    self.exact_tests += 1
                    carrier = self.carriers[index]
                    difference = carrier[2] - radius
                    if difference >= 0 and distance_squared(
                        s - carrier[0] - PERIOD * lift[0],
                        t - carrier[1] - PERIOD * lift[1],
                    ) <= difference * difference:
                        return Route(index, lift)
        return None
