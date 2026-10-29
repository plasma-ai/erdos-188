"""Derive the six construction files from the orbit tables and a tree witness.

Everything here is a deterministic function of decoded inputs. The carrier
and plug families are the unions of the orbits of their orbit tables' rows;
the conflict rule removes carriers; the base is the retained carriers
together with the plugs; each leaf of the tree witness names a base disk or
the cell-service disk of its own cell and step; the ordered witness table is
the sorted disjoint union of base and micro disks; and every certificate
address, ordinal and lift follows. The independent checkers, not these
functions, establish the finite obligations of the construction.
"""

from __future__ import annotations

import dataclasses
from collections.abc import Callable, Iterable

if __package__:
    from .util import conflict, geometry, micro, orbits, witness
    from .util.rationals import Site
else:
    from util import conflict, geometry, micro, orbits, witness
    from util.rationals import Site

__all__ = ['Removal', 'Tree', 'families', 'remove_conflicting', 'base_family', 'expand']


@dataclasses.dataclass(frozen=True)
class Removal:
    """The conflict rule applied to admitted carriers and plugs."""

    # S minus E and E, both in table order
    retained: tuple[Site, ...]
    removed: tuple[Site, ...]
    scan: conflict.Scan


@dataclasses.dataclass(frozen=True)
class Tree:
    """A compiled covering tree: wire records, counts, depths and both families."""

    # D, T and S record lines without LF, in preorder
    records: tuple[bytes, ...]
    directions: int
    translations: int
    base_leaves: int
    micro_leaves: int
    direction_depth: int
    translation_depth: int
    # M, and F = sorted(B disjoint-union M)
    micros: tuple[Site, ...]
    sites: tuple[Site, ...]

    @property
    def leaves(self: Tree) -> int:
        """Return the leaf count."""
        return self.base_leaves + self.micro_leaves


def families(
    carrier_orbits: Iterable[Site], plug_orbits: Iterable[Site],
) -> tuple[tuple[Site, ...], tuple[Site, ...]]:
    """Expand the two orbit tables to the carrier and plug families, each sorted."""
    return orbits.expand(carrier_orbits), orbits.expand(plug_orbits)


def remove_conflicting(
    carriers: tuple[Site, ...],
    plugs: tuple[Site, ...],
    checkpoint: Callable[[], None],
) -> Removal:
    """Remove every carrier conflicting with some plug copy."""
    scan = conflict.scan(carriers, plugs, checkpoint)
    removed = set(scan.removed)
    return Removal(
        tuple(site for index, site in enumerate(carriers) if index not in removed),
        tuple(carriers[index] for index in sorted(removed)),
        scan,
    )


def base_family(retained: Iterable[Site], plugs: Iterable[Site]) -> tuple[Site, ...]:
    """Return the base B = (S minus E) union P as a sorted table."""
    return tuple(sorted({*retained, *plugs}))


def expand(
    records: Iterable[witness.Record],
    base: tuple[Site, ...],
    checkpoint: Callable[[], None],
) -> Tree:
    """Compile witness records into a certificate body, deriving M and F.

    A leaf's disk is a base disk, or else it must be the cell-service disk of
    the leaf's cell and step, which makes it a micro disk. The lift of a leaf
    is the nearest lift of the midpoint displacement: a passing leaf keeps
    every corner image, hence the midpoint image, within an axial distance
    below 20/7 of the disk copy's center, so no other lift can serve.
    """
    base_set = set(base)
    directions = {}
    walk = geometry.Preorder()
    pending: list[bytes | tuple[geometry.Cell, int, Site, tuple[int, int]]] = []
    micros: set[Site] = set()
    counts = {'D': 0, 'T': 0, 'base': 0, 'micro': 0}
    direction_depth = translation_depth = 0
    for number, record in enumerate(records):
        if number % 4_096 == 0:
            checkpoint()
        cell = walk.visit(record.kind)
        direction_depth = max(direction_depth, cell.d)
        translation_depth = max(translation_depth, cell.e)
        if record.kind != 'S':
            counts[record.kind] += 1
            kind = record.kind.encode('ascii')
            pending.append(b'%s %d %d %d %d %d' % (kind, *cell.address()))
            continue
        step, site = record.step, record.site
        if site is None or step not in geometry.STEPS:
            raise ValueError(
                f'Record {number + 1}: a leaf needs a disk and a step in [-21,20]',
            )
        cached = directions.get((cell.d, cell.i))
        if cached is None:
            cached = directions[(cell.d, cell.i)] = geometry.direction(cell.d, cell.i)
        if site in base_set:
            counts['base'] += 1
            midpoint_s, midpoint_t = geometry.midpoint(cell.e, cell.h, cell.k)
            lift = (
                geometry.nearest_lift(midpoint_s + step * cached.vs - site[0]),
                geometry.nearest_lift(midpoint_t + step * cached.vt - site[1]),
            )
        else:
            disk, lift = micro.service_disk(cell, step, cached)
            if disk != site:
                raise ValueError(
                    f'Record {number + 1}: the leaf names neither a base disk nor '
                    f'the cell-service disk of {cell.address()} at step {step}',
                )
            try:
                geometry.admit_site(disk)
            except ValueError as error:
                raise ValueError(
                    f'Record {number + 1}: cell-service disk: {error}',
                ) from error
            counts['micro'] += 1
            micros.add(disk)
        pending.append((cell, step, site, lift))
    if not walk.complete:
        raise ValueError('The witness ends before the root subtree closes')
    if micros & base_set:
        raise ValueError('A micro disk coincides with a base disk')
    checkpoint()

    # the ordered witness table fixes every ordinal; only then can leaves be written
    sites = tuple(sorted(base_set | micros))
    ordinals = {site: ordinal for ordinal, site in enumerate(sites)}
    lines = []
    for number, entry in enumerate(pending):
        if number % 4_096 == 0:
            checkpoint()
        if isinstance(entry, bytes):
            lines.append(entry)
            continue
        cell, step, site, lift = entry
        lines.append(b'S %d %d %d %d %d %d %d %d %d' % (
            *cell.address(), step, ordinals[site], *lift,
        ))
    checkpoint()
    return Tree(
        tuple(lines), counts['D'], counts['T'], counts['base'], counts['micro'],
        direction_depth, translation_depth, tuple(sorted(micros)), sites,
    )
