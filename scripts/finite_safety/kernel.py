"""Check complete periodic disk products with exact integer enclosures."""

from __future__ import annotations

import dataclasses
import fractions
import hashlib
import os
import pathlib
import re
import stat
from typing import Optional

__all__ = [
    'Site',
    'INPUT_PROFILE',
    'Limits',
    'Budget',
    'Incomplete',
    'Family',
    'Bounds',
    'Conflict',
    'ScanResult',
    'read_family',
    'rectangle_extrema',
    'block_safe',
    'scan',
]

Site = tuple[fractions.Fraction, fractions.Fraction, fractions.Fraction]

INPUT_PROFILE = 'bounded-tsv-1536-v1'

_SCALE = 1 << 64
_PERIOD = 59
_LEAF_SIZE = 8
_LIFTS = tuple((s, t) for s in (-1, 0, 1) for t in (-1, 0, 1))
_RATIONAL = re.compile(rb'([+-]?[0-9]+)(?:/([0-9]+))?')
_MAX_FILE_BYTES = 32 * 1024 * 1024
_MAX_ROWS = 300_000
_MAX_LINE_BYTES = 2_048
_MAX_TOKEN_BYTES = 1_024
_MAX_INTEGER_DIGITS = 512
_MAX_BITS = 1_536
_MAX_DEPTH = 64
_SPATIAL_DEPTH = _MAX_DEPTH - (_MAX_ROWS - 1).bit_length()


@dataclasses.dataclass(frozen=True)
class Limits:
    """Explicit finite invocation caps, defaulting to the calibration profile."""

    predicates: int = 2_000_000
    member_visits: int = 16_000_000
    tree_nodes: int = 1_200_000


class Incomplete(RuntimeError):
    """Raised when a work limit or stop marker prevents completion."""


class Budget:
    """Charge bounded work and check cancellation without deciding geometry."""

    def __init__(
        self: Budget,
        limits: Limits,
        *,
        stop_path: Optional[pathlib.Path] = None,
    ) -> None:
        """Initialize finite ceilings and the optional STOP path."""
        for field in dataclasses.fields(limits):
            value = getattr(limits, field.name)
            if type(value) is not int or value < 0:
                raise ValueError(f'Invalid {field.name} limit: {value!r}')
        self.ceilings = {
            'predicates': limits.predicates,
            'member_visits': limits.member_visits,
            'tree_nodes': limits.tree_nodes,
            'input_bytes': 2 * _MAX_FILE_BYTES,
            'input_rows': 2 * _MAX_ROWS,
            'enclosures': 2 * _MAX_ROWS,
        }
        self.counts = {name: 0 for name in self.ceilings}
        self.block_predicates = 0
        self.exact_predicates = 0
        self.stop_path = stop_path
        self._charges = 0

    def check(self: Budget) -> None:
        """Refuse externally stopped work."""
        if self.stop_path is not None and (
            self.stop_path.exists() or self.stop_path.is_symlink()
        ):
            raise Incomplete('Stop marker exists')

    def charge(self: Budget, name: str, amount: int = 1) -> None:
        """Reserve work before performing it, checking STOP at bounded intervals."""
        value = self.counts[name] + amount
        if value > self.ceilings[name]:
            raise Incomplete(f'{name} limit exhausted')
        self.counts[name] = value
        self._charges += 1
        if self._charges % 256 == 0:
            self.check()

    def predicate(self: Budget, *, exact: bool) -> None:
        """Charge one block-lift or exact pair-lift predicate."""
        self.charge('predicates')
        if exact:
            self.exact_predicates += 1
        else:
            self.block_predicates += 1

    def snapshot(self: Budget) -> dict[str, int]:
        """Return independent work counters for a scoped result."""
        return {
            **self.counts,
            'block_predicates': self.block_predicates,
            'exact_predicates': self.exact_predicates,
        }


@dataclasses.dataclass(frozen=True)
class Family:
    """Exact semantic sites and the identity of the bytes actually read."""

    sites: tuple[Site, ...]
    sha256: str
    raw_rows: int
    byte_count: int


@dataclasses.dataclass(frozen=True, slots=True)
class Bounds:
    """Closed integer center box and radius upper bound at scale 2**64."""

    s_min: int
    s_max: int
    t_min: int
    t_max: int
    r_max: int


@dataclasses.dataclass(frozen=True, slots=True)
class _Entry:
    """One exact site with its original semantic ordinal and checked bounds."""

    ordinal: int
    site: Site
    bounds: Bounds


@dataclasses.dataclass(frozen=True, slots=True)
class _Node:
    """A disjoint subtree with member count, bounds, and leaf-only members."""

    count: int
    bounds: Bounds
    left: Optional[_Node] = None
    right: Optional[_Node] = None
    members: tuple[_Entry, ...] = ()


@dataclasses.dataclass(frozen=True)
class Conflict:
    """An exact closed-annulus failure at two semantic ordinals and a lift."""

    left: int
    right: int
    lift: tuple[int, int]
    distance_squared: fractions.Fraction
    lower_squared: fractions.Fraction
    upper_squared: fractions.Fraction


@dataclasses.dataclass(frozen=True)
class ScanResult:
    """A verdict restricted to a named half-open left ordinal interval."""

    status: str
    begin: int
    end: int
    right_count: int
    certified: int
    required: int
    work: dict[str, int]
    conflict: Optional[Conflict] = None
    reason: str = ''


def _rational(token: bytes) -> fractions.Fraction:
    """Decode a bounded signed integer or rational without float parsing."""
    if len(token) > _MAX_TOKEN_BYTES:
        raise ValueError('Rational token exceeds its byte limit')
    match = _RATIONAL.fullmatch(token)
    if match is None:
        raise ValueError('Invalid rational spelling')
    numerator_token = match.group(1)
    denominator_token = match.group(2)
    if len(numerator_token.lstrip(b'+-')) > _MAX_INTEGER_DIGITS or (
        denominator_token is not None
        and len(denominator_token) > _MAX_INTEGER_DIGITS
    ):
        raise ValueError('Rational component exceeds its digit limit')
    numerator = int(numerator_token)
    denominator = int(denominator_token) if denominator_token is not None else 1
    if abs(numerator).bit_length() > _MAX_BITS or denominator.bit_length() > _MAX_BITS:
        raise ValueError('Rational integer exceeds its bit limit')
    if denominator <= 0:
        raise ValueError('Rational denominator must be positive')
    return fractions.Fraction(numerator, denominator)


def _validate_site(site: Site) -> None:
    """Check the exact domain required by the nine-lift reduction."""
    if not isinstance(site, tuple) or len(site) != 3:
        raise ValueError('A site must be an immutable rational triple')
    for value in site:
        if type(value) is not fractions.Fraction:
            raise ValueError('Every site value must be an exact Fraction')
        if abs(value.numerator).bit_length() > _MAX_BITS:
            raise ValueError('Site numerator exceeds its bit limit')
        if value.denominator.bit_length() > _MAX_BITS:
            raise ValueError('Site denominator exceeds its bit limit')
    s, t, radius = site
    if not (0 <= s < _PERIOD and 0 <= t < _PERIOD):
        raise ValueError('Site center is outside [0,59)**2')
    if not (0 < radius and 2 * radius < 1):
        raise ValueError('Site radius is outside (0,1/2)')


def _ordered_sites(distinct: set[Site], budget: Budget) -> tuple[Site, ...]:
    """Sort exact sites by a charged, interruptible bottom-up merge sort."""
    current: list[Site] = []
    for site in distinct:
        budget.charge('member_visits')
        current.append(site)
    target = current.copy()
    width = 1
    while width < len(current):
        budget.check()
        for begin in range(0, len(current), 2 * width):
            middle = min(begin + width, len(current))
            end = min(begin + 2 * width, len(current))
            left, right, output = begin, middle, begin
            while left < middle and right < end:
                budget.charge('member_visits')
                if current[left] < current[right]:
                    target[output] = current[left]
                    left += 1
                else:
                    target[output] = current[right]
                    right += 1
                output += 1
            while left < middle:
                budget.charge('member_visits')
                target[output] = current[left]
                left += 1
                output += 1
            while right < end:
                budget.charge('member_visits')
                target[output] = current[right]
                right += 1
                output += 1
        current, target = target, current
        width *= 2
    for index in range(1, len(current)):
        budget.charge('member_visits')
        if not current[index - 1] < current[index]:
            raise ValueError('Sorted family is not strictly increasing')
    budget.check()
    return tuple(current)


def read_family(
    path: pathlib.Path,
    *,
    sha256: str,
    byte_count: int,
    raw_rows: int,
    site_count: int,
    budget: Budget,
) -> Family:
    """Validate pinned TSV bytes and return their exact sorted set of sites."""
    if not (0 < byte_count <= _MAX_FILE_BYTES):
        raise ValueError('Expected byte count is outside the input limit')
    if not (0 < site_count <= raw_rows <= _MAX_ROWS):
        raise ValueError('Expected row counts are outside the input limit')
    budget.check()
    digest = hashlib.sha256()
    distinct: set[Site] = set()
    rows = 0
    consumed = 0
    with path.open('rb') as source:
        info = os.fstat(source.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size != byte_count:
            raise ValueError('Input is not a regular file of the pinned size')
        while line := source.readline(_MAX_LINE_BYTES + 1):
            budget.charge('input_bytes', len(line))
            budget.charge('input_rows')
            consumed += len(line)
            rows += 1
            if consumed > byte_count or rows > raw_rows:
                raise ValueError('Input exceeds its pinned size or row count')
            if len(line) > _MAX_LINE_BYTES or not line.endswith(b'\n'):
                raise ValueError('Invalid or oversized TSV line')
            digest.update(line)
            fields = line[:-1].split(b'\t')
            if len(fields) != 3:
                raise ValueError('A TSV row must contain exactly three fields')
            site = (_rational(fields[0]), _rational(fields[1]), _rational(fields[2]))
            _validate_site(site)
            distinct.add(site)
    if consumed != byte_count or rows != raw_rows:
        raise ValueError('Input has the wrong byte size or row count')
    if digest.hexdigest() != sha256:
        raise ValueError('Input SHA-256 does not match the pinned bytes')
    if len(distinct) != site_count:
        raise ValueError('Input has the wrong distinct site count')
    budget.check()
    sites = _ordered_sites(distinct, budget)
    budget.check()
    return Family(sites, digest.hexdigest(), rows, consumed)


def _entry(ordinal: int, site: Site, budget: Budget) -> _Entry:
    """Create and verify the integer enclosure of one exact site."""
    budget.charge('enclosures')
    _validate_site(site)
    endpoints: list[tuple[int, int]] = []
    for value in site[:2]:
        numerator = _SCALE * value.numerator
        denominator = value.denominator
        lower = numerator // denominator
        upper = -(-numerator // denominator)
        if not lower * denominator <= numerator <= upper * denominator:
            raise ValueError('Coordinate enclosure failed')
        endpoints.append((lower, upper))
    radius = site[2]
    numerator = _SCALE * radius.numerator
    upper_radius = -(-numerator // radius.denominator)
    if not (0 < numerator <= upper_radius * radius.denominator):
        raise ValueError('Radius enclosure failed')
    if upper_radius > _SCALE // 2:
        raise ValueError('Radius enclosure exceeds one half')
    bounds = Bounds(*endpoints[0], *endpoints[1], upper_radius)
    return _Entry(ordinal, site, bounds)


def _member_bounds(members: tuple[_Entry, ...], budget: Budget) -> Bounds:
    """Compute every coordinate extremum and radius maximum from members."""
    first = members[0].bounds
    s_min, s_max = first.s_min, first.s_max
    t_min, t_max = first.t_min, first.t_max
    r_max = first.r_max
    for member in members:
        budget.charge('member_visits')
        bounds = member.bounds
        s_min = min(s_min, bounds.s_min)
        s_max = max(s_max, bounds.s_max)
        t_min = min(t_min, bounds.t_min)
        t_max = max(t_max, bounds.t_max)
        r_max = max(r_max, bounds.r_max)
    return Bounds(s_min, s_max, t_min, t_max, r_max)


def _merge_bounds(left: Bounds, right: Bounds) -> Bounds:
    """Return the exact componentwise extrema of two integer bounds."""
    return Bounds(
        min(left.s_min, right.s_min),
        max(left.s_max, right.s_max),
        min(left.t_min, right.t_min),
        max(left.t_max, right.t_max),
        max(left.r_max, right.r_max),
    )


def _build_tree(members: tuple[_Entry, ...], budget: Budget, depth: int = 0) -> _Node:
    """Partition a full member sequence without discarding any ordinal."""
    budget.check()
    if depth > _MAX_DEPTH:
        raise Incomplete('Tree depth limit exhausted')
    budget.charge('tree_nodes')
    bounds = _member_bounds(members, budget)
    if len(members) <= _LEAF_SIZE:
        return _Node(len(members), bounds, members=members)

    # every member enters exactly one side of the spatial partition
    first: list[_Entry] = []
    second: list[_Entry] = []
    split_s = bounds.s_max - bounds.s_min >= bounds.t_max - bounds.t_min
    midpoint = bounds.s_min + bounds.s_max if split_s else bounds.t_min + bounds.t_max
    for member in members:
        budget.charge('member_visits')
        box = member.bounds
        coordinate = box.s_min + box.s_max if split_s else box.t_min + box.t_max
        if coordinate <= midpoint:
            first.append(member)
        else:
            second.append(member)
    if depth < _SPATIAL_DEPTH and first and second:
        left_members, right_members = tuple(first), tuple(second)
    else:
        middle = len(members) // 2
        left_members, right_members = members[:middle], members[middle:]
    left = _build_tree(left_members, budget, depth + 1)
    right = _build_tree(right_members, budget, depth + 1)
    return _Node(len(members), bounds, left=left, right=right)


def _validate_tree(root: _Node, entries: tuple[_Entry, ...], budget: Budget) -> None:
    """Check exact tree membership, parent extrema, and the entire ordinal range."""
    begin = entries[0].ordinal
    seen = bytearray(len(entries))
    found = 0
    pending = [root]
    while pending:
        budget.charge('member_visits')
        node = pending.pop()
        if node.members:
            if node.left is not None or node.right is not None:
                raise ValueError('A leaf also has children')
            if node.count != len(node.members) or node.count > _LEAF_SIZE:
                raise ValueError('A leaf has the wrong member count')
            if node.bounds != _member_bounds(node.members, budget):
                raise ValueError('A leaf has incorrect extrema')
            for member in node.members:
                budget.charge('member_visits')
                index = member.ordinal - begin
                if not 0 <= index < len(entries):
                    raise ValueError('Leaf ordinal is outside the required range')
                if seen[index] or member != entries[index]:
                    raise ValueError('Leaf membership is duplicated or altered')
                seen[index] = 1
                found += 1
        else:
            left, right = node.left, node.right
            if left is None or right is None:
                raise ValueError('An internal node lacks a child')
            if node.count != left.count + right.count:
                raise ValueError('An internal count omits or duplicates members')
            if node.bounds != _merge_bounds(left.bounds, right.bounds):
                raise ValueError('An internal node has incorrect extrema')
            pending.extend((right, left))
    if found != len(entries) or root.count != len(entries):
        raise ValueError('The tree does not cover the complete ordinal range')
    budget.check()


def rectangle_extrema(a: int, b: int, c: int, d: int) -> tuple[int, int]:
    """Return exact minimum and maximum of 4*(x*x+x*y+y*y) on a rectangle."""
    corners = tuple(4 * (x * x + x * y + y * y) for x in (a, b) for y in (c, d))
    minimum, maximum = min(corners), max(corners)
    for x in (a, b):
        if 2 * c <= -x <= 2 * d:
            minimum = min(minimum, 3 * x * x)
    for y in (c, d):
        if 2 * a <= -y <= 2 * b:
            minimum = min(minimum, 3 * y * y)
    if a <= 0 <= b and c <= 0 <= d:
        minimum = 0
    return minimum, maximum


def block_safe(left: Bounds, right: Bounds, lift: tuple[int, int]) -> bool:
    """Certify a whole node product at one lift, or decline to prune it."""
    shift_s = _PERIOD * _SCALE * lift[0]
    shift_t = _PERIOD * _SCALE * lift[1]
    minimum, maximum = rectangle_extrema(
        left.s_min - right.s_max + shift_s,
        left.s_max - right.s_min + shift_s,
        left.t_min - right.t_max + shift_t,
        left.t_max - right.t_min + shift_t,
    )
    radius = left.r_max + right.r_max
    if radius < _SCALE and 441 * maximum < 40_000 * (_SCALE - radius) ** 2:
        return True
    if 441 * minimum > 40_000 * (_SCALE + radius) ** 2:
        return True
    return False


def scan(
    left: tuple[Site, ...],
    right: tuple[Site, ...],
    *,
    budget: Budget,
    begin: int = 0,
    end: Optional[int] = None,
) -> ScanResult:
    """Check every pair and lift in a full product or explicit left-row shard."""
    if end is None:
        end = len(left)
    if not (0 < len(left) <= _MAX_ROWS and 0 < len(right) <= _MAX_ROWS):
        raise ValueError('Families must be nonempty and within the row limit')
    if type(begin) is not int or type(end) is not int:
        raise ValueError('Shard boundaries must be integers')
    if not 0 <= begin < end <= len(left):
        raise ValueError('Invalid or empty left ordinal interval')
    required = 9 * (end - begin) * len(right)
    certified = 0
    try:
        budget.check()
        left_entries = tuple(_entry(i, left[i], budget) for i in range(begin, end))
        right_entries = tuple(_entry(i, site, budget) for i, site in enumerate(right))
        left_root = _build_tree(left_entries, budget)
        right_root = _build_tree(right_entries, budget)
        _validate_tree(left_root, left_entries, budget)
        _validate_tree(right_root, right_entries, budget)

        # a cleared bit is certified only for this exact Cartesian product
        pending = [(left_root, right_root, (1 << len(_LIFTS)) - 1)]
        while pending:
            budget.check()
            a, b, mask = pending.pop()
            remaining = mask
            for bit, lift in enumerate(_LIFTS):
                if mask & (1 << bit):
                    budget.predicate(exact=False)
                    if block_safe(a.bounds, b.bounds, lift):
                        certified += a.count * b.count
                        remaining &= ~(1 << bit)
            if not remaining:
                continue

            # every residual leaf member pair receives the original exact test
            if a.members and b.members:
                for first in a.members:
                    for second in b.members:
                        sigma = first.site[2] + second.site[2]
                        lower, upper = (1 - sigma) ** 2, (1 + sigma) ** 2
                        for bit, lift in enumerate(_LIFTS):
                            if remaining & (1 << bit):
                                budget.predicate(exact=True)
                                s = first.site[0] - second.site[0] + _PERIOD * lift[0]
                                t = first.site[1] - second.site[1] + _PERIOD * lift[1]
                                distance = fractions.Fraction(441, 10_000) * (
                                    s * s + s * t + t * t
                                )
                                if lower <= distance <= upper:
                                    conflict = Conflict(
                                        first.ordinal,
                                        second.ordinal,
                                        lift,
                                        distance,
                                        lower,
                                        upper,
                                    )
                                    return ScanResult(
                                        status='unsafe',
                                        begin=begin,
                                        end=end,
                                        right_count=len(right),
                                        certified=certified,
                                        required=required,
                                        work=budget.snapshot(),
                                        conflict=conflict,
                                    )
                                certified += 1
                continue

            # split one nonleaf into its two disjoint, exhaustive products
            if not a.members and (b.members or a.count >= b.count):
                if a.left is None or a.right is None:
                    raise ValueError('Validated left node lost a child')
                pending.extend(((a.right, b, remaining), (a.left, b, remaining)))
            else:
                if b.left is None or b.right is None:
                    raise ValueError('Validated right node lost a child')
                pending.extend(((a, b.right, remaining), (a, b.left, remaining)))
        budget.check()
        if certified != required:
            raise ValueError('Certified predicate weight does not equal the product')
        return ScanResult(
            status='complete',
            begin=begin,
            end=end,
            right_count=len(right),
            certified=certified,
            required=required,
            work=budget.snapshot(),
        )
    except (Incomplete, KeyboardInterrupt, MemoryError) as error:
        return ScanResult(
            status='incomplete',
            begin=begin,
            end=end,
            right_count=len(right),
            certified=certified,
            required=required,
            work=budget.snapshot(),
            reason=str(error) or type(error).__name__,
        )
