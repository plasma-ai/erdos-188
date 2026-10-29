"""The conflict rule between carriers and plugs, scanned exactly.

A carrier ``(c, R)`` conflicts with a plug ``(p, r)`` when some period copy
``p + 59n`` of the plug lies in the closed forbidden annulus of the carrier,
``(1 - sigma)^2 <= lambda^2 Q(c - p - 59n) <= (1 + sigma)^2`` with
``sigma = R + r``; both boundaries count. The scan below enumerates every
carrier, plug and lift that can conflict, discards most pairs by an exact
integer enclosure, and decides the survivors in exact rational arithmetic.

Completeness. A conflict needs ``lambda^2 Q(v) <= (1 + sigma)^2 < 4`` for the
displacement ``v = c - p - 59n``, so ``Q(v) < 40000/441`` and, since
``Q(v) >= 3 v_i^2 / 4``, each coordinate has ``|v_i| < 11``. The integer parts
of ``c`` and of the plug copy therefore differ by at most 11 in each
coordinate, so bucketing the plugs by integer parts and visiting the offsets
in ``[-11, 11]^2`` around the carrier's bucket, with the lift read off the
offset, meets every conflicting copy exactly once.
"""

from __future__ import annotations

import dataclasses
from collections.abc import Callable, Iterator
from fractions import Fraction
from typing import Optional

from .enclosure import beyond, ceil_scaled, floor_scaled, within
from .geometry import PERIOD, distance_squared
from .rationals import Site

__all__ = ['Conflict', 'Scan', 'Index', 'scan']

# every coordinate of a conflicting displacement has absolute value below 11
_OFFSET_BOUND = 11
# integer enclosures at scale 2**8 decide most pairs without rational work
_SCALE_BITS = 8
_SCALE = 1 << _SCALE_BITS
_PERIOD_SCALED = PERIOD * _SCALE


@dataclasses.dataclass(frozen=True)
class Conflict:
    """One plug copy in a carrier's closed forbidden annulus."""

    carrier: int
    plug: int
    # the conflicting plug copy is plug + period * lift
    lift: tuple[int, int]
    distance_squared: Fraction
    lower_squared: Fraction
    upper_squared: Fraction


@dataclasses.dataclass(frozen=True)
class Scan:
    """Every conflict of a carrier family against a plug family, with work counts."""

    conflicts: tuple[Conflict, ...]
    bucket_visits: int
    pair_screens: int
    exact_tests: int

    @property
    def removed(self: Scan) -> tuple[int, ...]:
        """Return the sorted carrier indexes with at least one conflict."""
        return tuple(sorted({conflict.carrier for conflict in self.conflicts}))


@dataclasses.dataclass(frozen=True, slots=True)
class _Enclosure:
    """Integer bounds of one site at scale 2**8: floors of the center, ceiling of r."""

    s: int
    t: int
    r: int


@dataclasses.dataclass(frozen=True, slots=True)
class _Bucket:
    """The plugs sharing one integer-part cell, with their joint enclosure."""

    s_min: int
    s_max: int
    t_min: int
    t_max: int
    r_max: int
    members: tuple[int, ...]


def _enclose(site: Site) -> _Enclosure:
    """Bound a site by integers at scale 2**8 so that the box contains it."""
    return _Enclosure(
        floor_scaled(site[0], _SCALE_BITS),
        floor_scaled(site[1], _SCALE_BITS),
        ceil_scaled(site[2], _SCALE_BITS),
    )


def _excluded(box: tuple[int, int, int, int], sigma: int) -> bool:
    """Decide from enclosures alone that no displacement in the box conflicts.

    The box bounds 2**8 times the displacement and sigma bounds 2**8 times the
    radius sum from above. Either every point of the box is nearer than
    1 - sigma or every point is farther than 1 + sigma.
    """
    return within(box, _SCALE - sigma) or beyond(box, _SCALE + sigma)


def _offsets(sigma: int) -> tuple[tuple[int, int, int, int], ...]:
    """List the bucket offsets and lifts that can hold a conflict at this sigma bound.

    An offset ``(ds, dt)`` between the integer parts of the carrier and of a
    plug copy leaves the displacement in the open box ``(d - 1, d + 1)``; the
    offsets whose box is excluded for every radius sum up to ``sigma`` are
    dropped once per carrier radius class.
    """
    admitted = []
    for ds in range(-_OFFSET_BOUND, _OFFSET_BOUND + 1):
        for dt in range(-_OFFSET_BOUND, _OFFSET_BOUND + 1):
            box = (
                _SCALE * (ds - 1), _SCALE * (ds + 1),
                _SCALE * (dt - 1), _SCALE * (dt + 1),
            )
            if not _excluded(box, sigma):
                admitted.append((ds, dt))
    return tuple(admitted)


def _buckets(plugs: tuple[Site, ...]) -> dict[tuple[int, int], _Bucket]:
    """Group the plugs by the integer parts of their centers."""
    grouped: dict[tuple[int, int], list[int]] = {}
    enclosures = [_enclose(plug) for plug in plugs]
    for index, plug in enumerate(plugs):
        key = (floor_scaled(plug[0], 0), floor_scaled(plug[1], 0))
        grouped.setdefault(key, []).append(index)
    buckets = {}
    for key, members in grouped.items():
        boxes = [enclosures[index] for index in members]
        buckets[key] = _Bucket(
            min(box.s for box in boxes), max(box.s for box in boxes),
            min(box.t for box in boxes), max(box.t for box in boxes),
            max(box.r for box in boxes), tuple(members),
        )
    return buckets


def _conflict(
    carrier_index: int,
    carrier: Site,
    plug_index: int,
    plug: Site,
    lift: tuple[int, int],
) -> Optional[Conflict]:
    """Decide one carrier, plug copy pair exactly."""
    sigma = carrier[2] + plug[2]
    lower, upper = (1 - sigma) ** 2, (1 + sigma) ** 2
    square = distance_squared(
        carrier[0] - plug[0] - PERIOD * lift[0],
        carrier[1] - plug[1] - PERIOD * lift[1],
    )
    if lower <= square <= upper:
        return Conflict(carrier_index, plug_index, lift, square, lower, upper)
    return None


class Index:
    """The plugs bucketed by integer parts, queried one site at a time.

    The same closed annulus decides whether a carrier conflicts with a plug
    and whether a micro disk fails the strict plug-safety test, so the index
    serves both the removal rule and the micro fallback of the search.
    """

    def __init__(self: Index, plugs: tuple[Site, ...]) -> None:
        """Bucket and enclose the plugs once."""
        self.plugs = plugs
        self.buckets = _buckets(plugs)
        self.enclosures = [_enclose(plug) for plug in plugs]
        self.plug_radius = max((box.r for box in self.enclosures), default=0)
        self.offsets_by_class: dict[int, tuple[tuple[int, int], ...]] = {}
        self.bucket_visits = 0
        self.pair_screens = 0
        self.exact_tests = 0

    def conflicts(self: Index, index: int, site: Site) -> Iterator[Conflict]:
        """Yield every plug copy in the site's closed forbidden annulus."""
        enclosure = _enclose(site)
        cell_s, cell_t = floor_scaled(site[0], 0), floor_scaled(site[1], 0)
        # offsets are pruned once per radius class against the largest plug
        sigma_class = enclosure.r + self.plug_radius
        offsets = self.offsets_by_class.get(sigma_class)
        if offsets is None:
            offsets = _offsets(sigma_class)
            self.offsets_by_class[sigma_class] = offsets
        for ds, dt in offsets:
            raw_s, raw_t = cell_s + ds, cell_t + dt
            lift = (raw_s // PERIOD, raw_t // PERIOD)
            bucket = self.buckets.get(
                (raw_s - PERIOD * lift[0], raw_t - PERIOD * lift[1]),
            )
            if bucket is None:
                continue
            self.bucket_visits += 1
            shift_s = enclosure.s - _PERIOD_SCALED * lift[0]
            shift_t = enclosure.t - _PERIOD_SCALED * lift[1]
            # the whole bucket is excluded when its joint enclosure cannot conflict
            box = (
                shift_s - bucket.s_max - 1, shift_s - bucket.s_min + 1,
                shift_t - bucket.t_max - 1, shift_t - bucket.t_min + 1,
            )
            if _excluded(box, enclosure.r + bucket.r_max):
                continue
            for plug_index in bucket.members:
                self.pair_screens += 1
                plug_box = self.enclosures[plug_index]
                box = (
                    shift_s - plug_box.s - 1, shift_s - plug_box.s + 1,
                    shift_t - plug_box.t - 1, shift_t - plug_box.t + 1,
                )
                if _excluded(box, enclosure.r + plug_box.r):
                    continue
                self.exact_tests += 1
                conflict = _conflict(
                    index, site, plug_index, self.plugs[plug_index], lift,
                )
                if conflict is not None:
                    yield conflict


def scan(
    carriers: tuple[Site, ...],
    plugs: tuple[Site, ...],
    checkpoint: Callable[[], None],
) -> Scan:
    """Find every conflicting (carrier, plug, lift) triple exactly."""
    index = Index(plugs)
    conflicts = []
    for carrier_index, carrier in enumerate(carriers):
        checkpoint()
        conflicts.extend(index.conflicts(carrier_index, carrier))
    checkpoint()
    return Scan(
        tuple(conflicts), index.bucket_visits, index.pair_screens, index.exact_tests,
    )
