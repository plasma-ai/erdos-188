"""Check sufficient O4--O7 routes for already decoded exact site families."""

from __future__ import annotations

import dataclasses
from collections.abc import Callable
from fractions import Fraction

__all__ = [
    'Site', 'Family', 'Limits', 'Route', 'Failure', 'NoRoute', 'LimitExceeded',
    'Summary', 'check_routes',
]

Site = tuple[Fraction, Fraction, Fraction]
Family = tuple[Site, ...]

# the construction's fixed geometry, on which the candidate pruning relies
_PERIOD = 59
_SCALE_SQUARED = Fraction(441, 10000)
_HALF = Fraction(1, 2)
_HALF_PERIOD = Fraction(_PERIOD, 2)
_ZERO = Fraction(0)
# hard implementation ceilings; callers must supply explicit limits at or below these
_MAX_FAMILY_SITES = 300000
_MAX_TOTAL_SITES = 4 * _MAX_FAMILY_SITES
# normalized-input envelope, which bounds the widths of the exact arithmetic
_MAX_RATIONAL_BITS = 1536
_MAX_CANDIDATE_CHECKS = _MAX_FAMILY_SITES**2
# a containing disk forces each axial displacement to have absolute value below three
_BUCKET_OFFSETS = range(-3, 4)


@dataclasses.dataclass(frozen=True)
class Limits:
    """Explicit input and candidate ceilings, independent of external supervision."""

    max_family_sites: int
    max_total_sites: int
    rational_bits: int
    max_candidate_checks: int


@dataclasses.dataclass(frozen=True)
class Route:
    """One checked route between zero-based normalized-set family indexes."""

    obligation: str
    source_family: str
    source_index: int
    source_transform: str
    target_family: str
    target_index: int
    # the target physical disk uses target_center + period * lift
    lift: tuple[int, int]
    distance_squared: Fraction
    radius_difference: Fraction
    candidate_checks: int = 0
    preferred_candidate_checks: int = 0


@dataclasses.dataclass(frozen=True)
class Failure:
    """A failed sufficient route condition, with no whole-union disproof claim."""

    obligation: str
    source_family: str
    source_index: int
    reason: str
    # these O5 counts concern only the current source site
    candidate_checks: int = 0
    preferred_candidate_checks: int = 0


class NoRoute(RuntimeError):
    """Report a completely checked but unsuccessful sufficient route condition."""

    def __init__(self, failure: Failure) -> None:
        self.failure = failure
        message = (
            f'{failure.obligation}: no sufficient route for '
            f'{failure.source_family}[{failure.source_index}]; {failure.reason}'
        )
        super().__init__(message)


class LimitExceeded(RuntimeError):
    """Refuse incomplete work without interpreting it as a failed route."""


@dataclasses.dataclass(frozen=True)
class Summary:
    """Completed finite-family checks, returned only after the final checkpoint."""

    base_sites: int
    carrier_sites: int
    plug_sites: int
    micro_sites: int
    o4_routes: int
    o5_routes: int
    o6_base_routes: int
    o6_carrier_routes: int
    o6_plug_routes: int
    o7_routes: int
    candidate_checks: int
    preferred_candidate_checks: int
    # normally returned emitter calls, not a claim that records were persisted
    emitted_routes: int


@dataclasses.dataclass(frozen=True)
class _Bucket:
    """Disjoint ordered carrier indexes, with S minus B as the first hint."""

    preferred: tuple[int, ...]
    remaining: tuple[int, ...]


def _admit(
    families: tuple[tuple[str, Family], ...],
    limits: Limits,
    checkpoint: Callable[[], None],
) -> None:
    """Reject excessive, malformed, unnormalized or noncanonical family inputs."""
    if type(limits) is not Limits:
        raise ValueError('Expected the explicit finite-route Limits record')
    for value, minimum, maximum in (
        (limits.max_family_sites, 0, _MAX_FAMILY_SITES),
        (limits.max_total_sites, 0, _MAX_TOTAL_SITES),
        (limits.rational_bits, 1, _MAX_RATIONAL_BITS),
        (limits.max_candidate_checks, 0, _MAX_CANDIDATE_CHECKS),
    ):
        if type(value) is not int or not minimum <= value <= maximum:
            raise ValueError('Invalid finite-route limit')
    total = 0
    for name, family in families:
        if type(family) is not tuple:
            raise ValueError(f'{name}: expected an immutable tuple family')
        if len(family) > limits.max_family_sites:
            raise LimitExceeded(f'{name}: family site limit')
        total += len(family)
    if total > limits.max_total_sites:
        raise LimitExceeded('Combined family site limit')

    # bound every rational before arithmetic or strict-order comparison on its row
    for name, family in families:
        previous = None
        for index, site in enumerate(family):
            checkpoint()
            if type(site) is not tuple or len(site) != 3:
                raise ValueError(f'{name}[{index}]: expected a site triple')
            for value in site:
                if type(value) is not Fraction:
                    raise ValueError(f'{name}[{index}]: expected exact Fraction fields')
                width = max(
                    abs(value.numerator).bit_length(), value.denominator.bit_length(),
                )
                if width > limits.rational_bits:
                    raise LimitExceeded(f'{name}[{index}]: rational input bit limit')
            s, t, radius = site
            if not (0 <= s < _PERIOD and 0 <= t < _PERIOD and 0 < radius < _HALF):
                raise ValueError(f'{name}[{index}]: outside the normalized site domain')
            if previous is not None and not previous < site:
                raise ValueError(f'{name}[{index}]: family must be strictly ordered')
            previous = site


def _find(family: Family, target: Site, checkpoint: Callable[[], None]) -> int | None:
    """Find an exact numeric tuple by bounded, checkpointed binary search."""
    lower, upper = 0, len(family)
    while lower < upper:
        checkpoint()
        middle = (lower + upper) // 2
        if family[middle] < target:
            lower = middle + 1
        else:
            upper = middle
    checkpoint()
    if lower < len(family) and family[lower] == target:
        return lower
    return None


def _send(
    route: Route,
    checkpoint: Callable[[], None],
    emit: Callable[[Route], None] | None,
) -> int:
    """Complete a record boundary before invoking the optional streaming sink."""
    checkpoint()
    if emit is None:
        return 0
    emit(route)
    return 1


def _identity_routes(
    obligation: str,
    source_name: str,
    source: Family,
    targets: tuple[tuple[str, Family], ...],
    checkpoint: Callable[[], None],
    emit: Callable[[Route], None] | None,
) -> tuple[int, int]:
    """Check exact-site inclusions, selecting the first matching target family."""
    checked = emitted = 0
    for index, site in enumerate(source):
        checkpoint()
        for target_name, target in targets:
            target_index = _find(target, site, checkpoint)
            if target_index is not None:
                route = Route(
                    obligation, source_name, index, 'identity', target_name,
                    target_index, (0, 0), _ZERO, _ZERO,
                )
                emitted += _send(route, checkpoint, emit)
                checked += 1
                break
        else:
            raise NoRoute(Failure(obligation, source_name, index, 'exact_site_missing'))
    return checked, emitted


def _rotation_routes(
    name: str,
    family: Family,
    checkpoint: Callable[[], None],
    emit: Callable[[Route], None] | None,
) -> tuple[int, int]:
    """Route rho(source) to the same-radius normalized target plus its lift."""
    checked = emitted = 0
    for index, (s, t, radius) in enumerate(family):
        checkpoint()
        rotated_s, rotated_t = -t, s + t
        ns = rotated_s // _PERIOD
        nt = rotated_t // _PERIOD
        target = (rotated_s - _PERIOD * ns, rotated_t - _PERIOD * nt, radius)
        target_index = _find(family, target, checkpoint)
        if target_index is None:
            raise NoRoute(Failure(
                'O6', name, index, 'rotated_same_radius_site_missing',
            ))
        route = Route(
            'O6', name, index, 'rho', name, target_index, (ns, nt), _ZERO, _ZERO,
        )
        emitted += _send(route, checkpoint, emit)
        checked += 1
    return checked, emitted


def _carrier_buckets(
    base: Family,
    carriers: Family,
    checkpoint: Callable[[], None],
) -> dict[tuple[int, int], _Bucket]:
    """Partition all carriers into unit buckets and disjoint E-first hints."""
    grouped: dict[tuple[int, int], tuple[list[int], list[int]]] = {}
    for index, site in enumerate(carriers):
        checkpoint()
        key = (site[0] // 1, site[1] // 1)
        if key not in grouped:
            grouped[key] = ([], [])
        preferred, remaining = grouped[key]
        if _find(base, site, checkpoint) is None:
            preferred.append(index)
        else:
            remaining.append(index)
    result = {}
    for key, (preferred, remaining) in grouped.items():
        checkpoint()
        result[key] = _Bucket(tuple(preferred), tuple(remaining))
    return result


def _containment_route(
    index: int,
    micro: Site,
    carriers: Family,
    buckets: dict[tuple[int, int], _Bucket],
    available_checks: int,
    checkpoint: Callable[[], None],
) -> Route:
    """Search every possible single-carrier route without an occupancy bound."""
    center_s, center_t, radius = micro
    bucket_s, bucket_t = center_s // 1, center_t // 1
    checked = preferred_checked = 0
    for prefer_removed in (True, False):
        for offset_s in _BUCKET_OFFSETS:
            for offset_t in _BUCKET_OFFSETS:
                checkpoint()
                key = ((bucket_s + offset_s) % _PERIOD, (bucket_t + offset_t) % _PERIOD)
                bucket = buckets.get(key)
                if bucket is None:
                    continue
                candidates = bucket.preferred if prefer_removed else bucket.remaining
                for target_index in candidates:
                    checkpoint()
                    if checked >= available_checks:
                        raise LimitExceeded(
                            f'O5: candidate limit before M[{index}] completed',
                        )
                    checked += 1
                    preferred_checked += int(prefer_removed)
                    s, t, target_radius = carriers[target_index]
                    difference = target_radius - radius
                    if difference < 0:
                        continue
                    # any containing lift must be this coordinatewise nearest lift
                    ns = (center_s - s + _HALF_PERIOD) // _PERIOD
                    nt = (center_t - t + _HALF_PERIOD) // _PERIOD
                    ds = center_s - s - _PERIOD * ns
                    dt = center_t - t - _PERIOD * nt
                    distance_squared = _SCALE_SQUARED * (ds * ds + ds * dt + dt * dt)
                    if distance_squared <= difference * difference:
                        return Route(
                            'O5', 'M', index, 'identity', 'S', target_index,
                            (ns, nt), distance_squared, difference,
                            checked, preferred_checked,
                        )
    raise NoRoute(Failure(
        'O5', 'M', index, 'no_single_carrier_route', checked, preferred_checked,
    ))


def check_routes(
    *,
    B: Family,
    S: Family,
    P: Family,
    M: Family,
    limits: Limits,
    checkpoint: Callable[[], None],
    emit: Callable[[Route], None] | None = None,
) -> Summary:
    """Check O4, O7, O6 for B/S/P, then complete O5 single-carrier containment."""
    if not callable(checkpoint) or (emit is not None and not callable(emit)):
        raise ValueError('Expected a checkpoint and an optional callable route sink')
    checkpoint()
    _admit((('B', B), ('S', S), ('P', P), ('M', M)), limits, checkpoint)
    o4, emitted = _identity_routes('O4', 'B', B, (('S', S), ('P', P)), checkpoint, emit)
    o7, count = _identity_routes('O7', 'P', P, (('B', B),), checkpoint, emit)
    emitted += count
    o6_base, count = _rotation_routes('B', B, checkpoint, emit)
    emitted += count
    o6_carrier, count = _rotation_routes('S', S, checkpoint, emit)
    emitted += count
    o6_plug, count = _rotation_routes('P', P, checkpoint, emit)
    emitted += count
    buckets = _carrier_buckets(B, S, checkpoint)
    o5 = candidates = preferred = 0
    for index, micro in enumerate(M):
        checkpoint()
        route = _containment_route(
            index, micro, S, buckets, limits.max_candidate_checks - candidates,
            checkpoint,
        )
        emitted += _send(route, checkpoint, emit)
        candidates += route.candidate_checks
        preferred += route.preferred_candidate_checks
        o5 += 1
    checkpoint()
    return Summary(
        len(B), len(S), len(P), len(M), o4, o5, o6_base, o6_carrier, o6_plug,
        o7, candidates, preferred, emitted,
    )
