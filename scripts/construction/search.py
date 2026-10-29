"""Search a covering tree over the base, carriers and plugs by the stated rules.

The search is a depth-first traversal of the covering grammar from the root
cell. At each cell it first excludes the single-disk leaf form when the
translation square is too large for any disk, then scans the base disks in
step order for the least one whose four-corner test passes, then tries the
cell-service disk of each step as a micro leaf, and otherwise splits:
direction when the direction error dominates the translation width, else
translation, the other way when the preferred depth is capped, and an exact
unresolved cell when both are. A micro leaf is admitted only when its radius
stays below one half (Lemma B), the disk lies in a lifted carrier and it is
strictly safe from every plug at nine lifts: the premises the safety argument
needs of a micro disk. The records emitted are the compact witness grammar
with one extra terminal, ``U reason``, for an unresolved cell.

The traversal terminates over inputs that admit a complete tree: dyadic cells
nest, both depths grow along any infinite path because the split rule compares
a quantity halving with the direction depth against one halving with the
translation depth, and a cell inside a leaf of some complete tree is served
by that leaf's witness, a base disk keeping its margin under refinement and a
cell-service disk shrinking into its parent's. That bounds the depth of the
tree found, not its size or the search's runtime.
"""

from __future__ import annotations

import dataclasses
import re
from collections.abc import Iterable
from typing import Optional

if __package__:
    from .util import conflict, containment, geometry, leaf, micro
    from .util.geometry import Cell
    from .util.rationals import Site, format_rational, parse_rational
else:
    from util import conflict, containment, geometry, leaf, micro
    from util.geometry import Cell
    from util.rationals import Site, format_rational, parse_rational

__all__ = [
    'TAG',
    'ATTEMPT_TAG',
    'END',
    'Decision',
    'Searcher',
    'format_record',
    'parse_record',
    'State',
    'replay',
]

TAG = b'PERIODIC_DISK_TREE_SEARCH_V1'
ATTEMPT_TAG = b'PERIODIC_DISK_TREE_ATTEMPT_V1'
END = b'END'
_STEP = re.compile(rb'0|-?[1-9][0-9]*')
# the split rule prefers direction when 21 E_u reaches lambda * sqrt3 * w_e
_DIRECTION_WEIGHT = len(geometry.STEPS) // 2
_TRANSLATION_SCALE = geometry.SCALE * geometry.SQRT3_UPPER
# a cell-service disk needs its radius below one half; the step-zero radius is least
_HALF = geometry.HALF


@dataclasses.dataclass(frozen=True)
class Decision:
    """What the search does with one cell: a leaf, a split or an unresolved cell."""

    kind: str
    step: int = 0
    site: Optional[Site] = None
    micro: bool = False
    # for an unresolved cell: the cap that stopped it and why no leaf served it
    reason: str = ''
    shortcut: bool = False
    failures: dict[str, int] = dataclasses.field(default_factory=dict)


class Searcher:
    """The leaf rules and the split rule over fixed base, carrier and plug tables."""

    def __init__(
        self: Searcher,
        base: tuple[Site, ...],
        carriers: tuple[Site, ...],
        plugs: tuple[Site, ...],
        direction_cap: Optional[int],
        translation_cap: Optional[int],
    ) -> None:
        """Index the three families once."""
        self.base = base
        self.leaves = leaf.Index(base)
        self.carriers = containment.Index(carriers)
        self.plugs = conflict.Index(plugs)
        self.direction_cap = direction_cap
        self.translation_cap = translation_cap
        self.directions: dict[tuple[int, int], geometry.Direction] = {}
        self.counts = {'shortcuts': 0, 'micro_attempts': 0}

    def _direction(self: Searcher, cell: Cell) -> geometry.Direction:
        """Return the cached direction quantities of the cell's direction interval."""
        key = (cell.d, cell.i)
        cached = self.directions.get(key)
        if cached is None:
            cached = self.directions[key] = geometry.direction(cell.d, cell.i)
        return cached

    def _micro(
        self: Searcher, cell: Cell, direction: geometry.Direction,
    ) -> tuple[Optional[Decision], dict[str, int]]:
        """Try the cell-service disk of each step as a micro leaf."""
        failures = {'radius': 0, 'containment': 0, 'plug_conflict': 0}
        for step in leaf.STEP_ORDER:
            disk, _ = micro.service_disk(cell, step, direction)
            if disk[2] >= _HALF:
                # the radius grows with |step|, and the order never decreases it
                failures['radius'] += len(leaf.STEP_ORDER) - leaf.STEP_ORDER.index(step)
                break
            self.counts['micro_attempts'] += 1
            if self.carriers.container(disk) is None:
                failures['containment'] += 1
                continue
            if next(self.plugs.conflicts(0, disk), None) is not None:
                failures['plug_conflict'] += 1
                continue
            return Decision('S', step, disk, micro=True), failures
        return None, failures

    def decide(self: Searcher, cell: Cell) -> Decision:
        """Serve, split or leave the cell unresolved by the stated rules."""
        direction = self._direction(cell)
        width = geometry.half_width(cell.e)
        may_direction = self.direction_cap is None or cell.d < self.direction_cap
        may_translation = self.translation_cap is None or cell.e < self.translation_cap
        # no disk covers a square whose opposite corners are farther apart than the
        # largest diameter, and the least cell-service radius is then one half or more
        if (
            self.leaves.max_radius ** 2 < 3 * geometry.SCALE_SQUARED * width * width
            and micro.MICRO_FACTOR * width >= _HALF
        ):
            self.counts['shortcuts'] += 1
            if may_translation:
                return Decision('T', shortcut=True)
            return Decision('U', reason='depth_limit', shortcut=True)
        found = self.leaves.serve(cell, direction)
        if found is not None:
            return Decision('S', found.step, self.base[found.ordinal])
        decision, failures = self._micro(cell, direction)
        if decision is not None:
            return decision
        prefer_direction = (
            _DIRECTION_WEIGHT * direction.error >= _TRANSLATION_SCALE * width
        )
        if prefer_direction and may_direction:
            return Decision('D', failures=failures)
        if may_translation:
            return Decision('T', failures=failures)
        if may_direction:
            return Decision('D', failures=failures)
        return Decision('U', reason='depth_limit', failures=failures)


def format_record(decision: Decision) -> bytes:
    """Encode one decision as a search record line without LF."""
    if decision.kind == 'S':
        if decision.site is None:
            raise ValueError('A leaf decision needs its disk')
        return b'S %d %s %s %s' % (
            decision.step,
            format_rational(decision.site[0]),
            format_rational(decision.site[1]),
            format_rational(decision.site[2]),
        )
    if decision.kind == 'U':
        return b'U ' + decision.reason.encode('ascii')
    if decision.kind in ('D', 'T'):
        return decision.kind.encode('ascii')
    raise ValueError(f'Unknown decision kind: {decision.kind!r}')


def parse_record(line: bytes) -> Decision:
    """Decode one search record line; the micro flag is settled by the caller."""
    if line in (b'D', b'T'):
        return Decision(line.decode('ascii'))
    fields = line.split(b' ')
    if len(fields) == 2 and fields[0] == b'U' and fields[1]:
        return Decision('U', reason=fields[1].decode('ascii'))
    if len(fields) == 5 and fields[0] == b'S' and _STEP.fullmatch(fields[1]):
        step = int(fields[1])
        if step not in geometry.STEPS:
            raise ValueError(f'Malformed search record step: {line[:60]!r}')
        return Decision('S', step, (
            parse_rational(fields[2]),
            parse_rational(fields[3]),
            parse_rational(fields[4]),
        ))
    raise ValueError(f'Malformed search record: {line[:60]!r}')


@dataclasses.dataclass
class State:
    """The resumable state of a search: what the emitted records determine."""

    walk: geometry.Preorder
    micros: set[Site]
    counts: dict[str, int]
    direction_depth: int
    translation_depth: int
    cells_by_depth: dict[tuple[int, int], int]
    last_cell: Optional[Cell]

    @classmethod
    def fresh(cls: type[State]) -> State:
        """Start at the root with nothing decided."""
        return cls(
            geometry.Preorder(), set(),
            {
                'cells': 0, 'records': 0, 'directions': 0, 'translations': 0,
                'base_leaves': 0, 'micro_leaves': 0, 'unresolved': 0,
            },
            0, 0, {}, None,
        )

    def apply(self: State, decision: Decision) -> Cell:
        """Consume the pending cell the decision is about and account for it."""
        cell = self.walk.visit('S' if decision.kind == 'U' else decision.kind)
        self.counts['cells'] += 1
        self.counts['records'] += 1
        if decision.kind == 'D':
            self.counts['directions'] += 1
        elif decision.kind == 'T':
            self.counts['translations'] += 1
        elif decision.kind == 'U':
            self.counts['unresolved'] += 1
        elif decision.micro:
            self.counts['micro_leaves'] += 1
            if decision.site is not None:
                self.micros.add(decision.site)
        else:
            self.counts['base_leaves'] += 1
        self.direction_depth = max(self.direction_depth, cell.d)
        self.translation_depth = max(self.translation_depth, cell.e)
        key = (cell.d, cell.e)
        self.cells_by_depth[key] = self.cells_by_depth.get(key, 0) + 1
        self.last_cell = cell
        return cell

    @property
    def leaves(self: State) -> int:
        """Return the served leaf count."""
        return self.counts['base_leaves'] + self.counts['micro_leaves']


def replay(lines: Iterable[bytes], base: set[Site]) -> State:
    """Rebuild the state from emitted records; a leaf outside the base is a micro."""
    state = State.fresh()
    for number, line in enumerate(lines, start=1):
        try:
            decision = parse_record(line)
            if decision.kind == 'S' and decision.site not in base:
                decision = dataclasses.replace(decision, micro=True)
            state.apply(decision)
        except ValueError as error:
            raise ValueError(f'Search record {number}: {error}') from error
    return state
