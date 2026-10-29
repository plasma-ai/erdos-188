"""Stream untrusted O1--O3 safety-tree and O4--O6 route certificates.

The existing arithmetic kernels remain unchanged. Independent consumers must
check domains, permutations, every inequality, complete coverage and exact EOF.

Run from the repository root with Python 3 (standard library only):

    python3 scripts/export_certificate.py --output /fresh/export/dir

The fresh directory receives ``certificate.ndjson`` and ``manifest.json``, the
inputs of ``lean_generators/gen_routes_chunks.py`` and
``lean_generators/gen_safety_chunks.py``.
"""

from __future__ import annotations

import argparse
import dataclasses
import fractions
import hashlib
import json
import os
import pathlib
import sys
import time
from collections.abc import Callable
from typing import Any, BinaryIO, Optional

from finite_routes import kernel as routes
from finite_safety import kernel as safety
from lean_generators import generation_subject as subject

__all__ = ['ExportStop', 'Stream', 'emit_safety', 'emit_routes', 'run', 'main']

_SCHEMA = 'periodic-disk-untrusted-certificate-v1'
_OUTPUT_BYTES = 512 * 1024 * 1024
_MANIFEST_BYTES = 65_536
_MANIFEST_RESERVE = 2 * _MANIFEST_BYTES
_LINE_BYTES = 65_536
_RECORDS = 8_000_000
_PERM_CHUNK = 4_096
_LIFTS = tuple((s, t) for s in (-1, 0, 1) for t in (-1, 0, 1))
_ROLE_FILES = {
    'B': 'base.tsv',
    'S': 'carriers.tsv',
    'P': 'plugs.tsv',
    'M': 'micro_representatives.tsv',
}
_PRODUCTS = (('O1', 'S', 'S'), ('O2', 'B', 'B'), ('O3', 'M', 'P'))


class ExportStop(RuntimeError):
    """Stop an incomplete export on cancellation or an engineering ceiling."""


class Stream:
    """Reserve and stream one bounded record at a time, with no whole-output buffer."""

    def __init__(
        self: Stream,
        target: BinaryIO,
        *,
        byte_limit: int = _OUTPUT_BYTES - _MANIFEST_RESERVE,
        record_limit: int = _RECORDS,
    ) -> None:
        """Bind an already-owned stream and explicitly finite local limits."""
        if (
            type(byte_limit) is not int
            or not 0 < byte_limit <= _OUTPUT_BYTES - _MANIFEST_RESERVE
        ):
            raise ValueError('Invalid stream byte ceiling')
        if type(record_limit) is not int or not 0 < record_limit <= _RECORDS:
            raise ValueError('Invalid record ceiling')
        self.target = target
        self.byte_limit = byte_limit
        self.record_limit = record_limit
        self.bytes = 0
        self.records = 0
        self.digest = hashlib.sha256()

    def write(self: Stream, record: list[Any]) -> None:
        """Refuse before a write that would exceed any declared output ceiling."""
        if self.records >= self.record_limit:
            raise ExportStop('Certificate record ceiling exhausted')
        content = (
            json.dumps(
                record,
                ensure_ascii=True,
                allow_nan=False,
                separators=(',', ':'),
            )
            + '\n'
        ).encode('ascii')
        if len(content) > _LINE_BYTES:
            raise ExportStop('Certificate line ceiling exhausted')
        if self.bytes + len(content) > self.byte_limit:
            raise ExportStop('Certificate byte ceiling exhausted')
        if self.target.write(content) != len(content):
            raise OSError('Short certificate write')
        self.digest.update(content)
        self.bytes += len(content)
        self.records += 1

    def prefix(self: Stream) -> dict[str, Any]:
        """Describe complete records already written, excluding a future footer."""
        return {
            'records_before_end': self.records,
            'bytes_before_end': self.bytes,
            'sha256_before_end': self.digest.hexdigest(),
        }


def _wire_mask(mask: int) -> int:
    """Map safety a-b+59*k bits to target-lift n=-k bits in lexicographic order."""
    return sum(1 << (8 - bit) for bit in range(9) if mask & (1 << bit))


def _layout(
    root: Any,
    budget: safety.Budget,
) -> tuple[list[int], dict[int, tuple[int, int]]]:
    """Flatten the validated tree left-first; every subtree becomes one interval."""
    permutation: list[int] = []
    ranges = {}

    def visit(node: Any) -> None:
        """Traverse one validated subtree in its deterministic member order."""
        budget.charge('member_visits')
        begin = len(permutation)
        if node.members:
            for member in node.members:
                budget.charge('member_visits')
                permutation.append(member.ordinal)
        else:
            visit(node.left)
            visit(node.right)
        end = len(permutation)
        if end - begin != node.count:
            raise ValueError('Tree layout lost a member')
        ranges[id(node)] = (begin, end)

    visit(root)
    return permutation, ranges


def emit_safety(
    obligation: str,
    left_role: str,
    right_role: str,
    left: tuple[safety.Site, ...],
    right: tuple[safety.Site, ...],
    writer: Stream,
    budget: safety.Budget,
) -> dict[str, int]:
    """Instrument the existing full-product walk without changing its predicates."""
    if type(left) is not tuple or type(right) is not tuple:
        raise ValueError('Safety families must be immutable tuples')
    n, m = len(left), len(right)
    if not 0 < n <= safety._MAX_ROWS or not 0 < m <= safety._MAX_ROWS:
        raise ValueError('Safety families must be nonempty and bounded')
    if safety._LIFTS != _LIFTS or safety._PERIOD != 59 or safety._SCALE != 1 << 64:
        raise ValueError('Pinned safety geometry changed')
    budget.check()
    for family in (left, right):
        for index, site in enumerate(family):
            budget.charge('member_visits')
            safety._validate_site(site)
            if index and not family[index - 1] < site:
                raise ValueError('Safety semantic family is not strictly ordered')
    entries_a = tuple(safety._entry(i, site, budget) for i, site in enumerate(left))
    entries_b = tuple(safety._entry(i, site, budget) for i, site in enumerate(right))
    root_a = safety._build_tree(entries_a, budget)
    root_b = safety._build_tree(entries_b, budget)
    safety._validate_tree(root_a, entries_a, budget)
    safety._validate_tree(root_b, entries_b, budget)
    permutation_a, ranges_a = _layout(root_a, budget)
    permutation_b, ranges_b = _layout(root_b, budget)
    stats = {
        'nodes': 0,
        'pairs': 0,
        'permutations': 0,
        'certified': 0,
        'required': 9 * n * m,
    }
    writer.write(['safety_begin', obligation, left_role, right_role, n, m])
    for side, permutation in (('left', permutation_a), ('right', permutation_b)):
        for offset in range(0, len(permutation), _PERM_CHUNK):
            writer.write(
                [
                    'perm',
                    obligation,
                    side,
                    offset,
                    permutation[offset : offset + _PERM_CHUNK],
                ]
            )
            stats['permutations'] += 1
    pending = [(root_a, root_b, 511)]
    while pending:
        budget.check()
        a, b, mask = pending.pop()
        a0, a1 = ranges_a[id(a)]
        b0, b1 = ranges_b[id(b)]
        remaining = mask
        # Same predicate calls, lift order and weighted accounting as safety.scan.
        for bit, lift in enumerate(safety._LIFTS):
            if mask & (1 << bit):
                budget.predicate(exact=False)
                if safety.block_safe(a.bounds, b.bounds, lift):
                    stats['certified'] += a.count * b.count
                    remaining &= ~(1 << bit)
        kind = cut = 0
        if remaining:
            if a.members and b.members:
                kind = 1
            elif not a.members and (b.members or a.count >= b.count):
                kind = 2
                cut = ranges_a[id(a.left)][1]
            else:
                kind = 3
                cut = ranges_b[id(b.left)][1]
        node_id = stats['nodes']
        writer.write(
            [
                'node',
                obligation,
                node_id,
                a0,
                a1,
                b0,
                b1,
                _wire_mask(mask),
                _wire_mask(mask ^ remaining),
                kind,
                cut,
            ]
        )
        stats['nodes'] += 1
        if kind == 1:
            for i, first in enumerate(a.members):
                for j, second in enumerate(b.members):
                    sigma = first.site[2] + second.site[2]
                    lower, upper = (1 - sigma) ** 2, (1 + sigma) ** 2
                    for bit, lift in enumerate(safety._LIFTS):
                        if remaining & (1 << bit):
                            budget.predicate(exact=True)
                            s = (
                                first.site[0]
                                - second.site[0]
                                + safety._PERIOD * lift[0]
                            )
                            t = (
                                first.site[1]
                                - second.site[1]
                                + safety._PERIOD * lift[1]
                            )
                            distance = fractions.Fraction(441, 10_000) * (
                                s * s + s * t + t * t
                            )
                            if lower <= distance <= upper:
                                raise ValueError(
                                    f'Unsafe {obligation} pair {first.ordinal},{second.ordinal} at kernel lift {lift}'
                                )
                            stats['certified'] += 1
                    writer.write(
                        [
                            'pair',
                            obligation,
                            node_id,
                            a0 + i,
                            b0 + j,
                            _wire_mask(remaining),
                        ]
                    )
                    stats['pairs'] += 1
        elif kind == 2:
            pending.extend(((a.right, b, remaining), (a.left, b, remaining)))
        elif kind == 3:
            pending.extend(((a, b.right, remaining), (a, b.left, remaining)))
    budget.check()
    if stats['certified'] != stats['required']:
        raise ValueError('Safety export did not account for the full product')
    writer.write(['safety_end', obligation, stats])
    return stats


def emit_routes(
    families: dict[str, tuple[safety.Site, ...]],
    writer: Stream,
    checkpoint: Callable[[], None],
) -> dict[str, Any]:
    """Stream existing kernel routes, filtering only O7 from the wire artifact."""
    expected = {
        'O4': len(families['B']),
        'O5': len(families['M']),
        'O6': sum(len(families[role]) for role in ('B', 'S', 'P')),
    }
    counts = dict.fromkeys(expected, 0)
    writer.write(['routes_begin', expected])

    def emit(route: routes.Route) -> None:
        """Persist only the three requested route obligations."""
        if route.obligation == 'O7':
            return
        if route.obligation not in counts:
            raise ValueError('Unexpected route obligation')
        writer.write(
            [
                'route',
                route.obligation,
                route.source_family,
                route.source_index,
                route.source_transform,
                route.target_family,
                route.target_index,
                *route.lift,
            ]
        )
        counts[route.obligation] += 1

    summary = routes.check_routes(
        **families,
        limits=routes.Limits(
            max_family_sites=300_000,
            max_total_sites=1_200_000,
            rational_bits=1_536,
            max_candidate_checks=100_000_000,
        ),
        checkpoint=checkpoint,
        emit=emit,
    )
    if (
        counts != expected
        or summary.emitted_routes != sum(counts.values()) + summary.o7_routes
    ):
        raise ValueError('Route emission did not match complete source coverage')
    result = {'counts': counts, 'kernel_summary': dataclasses.asdict(summary)}
    writer.write(['routes_end', result])
    return result


def _fingerprint(path: pathlib.Path) -> dict[str, Any]:
    """Hash a bounded regular file without interpreting its data."""
    content = path.read_bytes()
    if not 0 < len(content) <= 64 * 1024 * 1024:
        raise ValueError('Invalid bounded input file: ' + str(path))
    return {'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()}


def _declared() -> tuple[dict[str, tuple[int, str]], dict[str, tuple[int, int]]]:
    """Read the six gold identities and the four role counts.

    The identities are those of ``data/k42/manifest.json``, read through the
    generators' subject module, in manifest order; each role's rows are distinct
    sites, so its raw-row and distinct-site counts agree. Nothing here restates
    an identity.
    """
    declared = subject.resolve_subject()
    rows = (*(role.input for role in declared.roles), declared.cover, declared.tree)
    inputs = {entry.pin.name: (entry.pin.bytes, entry.pin.sha256) for entry in rows}
    counts = {role.name: (role.raw_rows, role.raw_rows) for role in declared.roles}
    if set(inputs) != {*_ROLE_FILES.values(), 'cover_sites.tsv', 'cover_tree.cert'}:
        raise ValueError('The gold manifest does not declare the six files')
    if set(counts) != set(_ROLE_FILES):
        raise ValueError('The subject does not declare the four roles')
    return inputs, counts


def _pin_inputs(
    data: pathlib.Path,
    inputs: dict[str, tuple[int, str]],
) -> dict[str, Any]:
    """Require all six fixed files by their gold identities."""
    result = {}
    for name, (size, digest) in inputs.items():
        result[name] = _fingerprint(data / name)
        if result[name] != {'bytes': size, 'sha256': digest}:
            raise ValueError('Pinned input changed: ' + name)
    return result


def _read_roles(
    data: pathlib.Path,
    inputs: dict[str, tuple[int, str]],
    counts: dict[str, tuple[int, int]],
) -> dict[str, Any]:
    """Read the four role tables with two bounded shared-parser ledgers."""
    families = {}
    # Two explicit two-file reader ledgers.
    for roles in (('B', 'S'), ('P', 'M')):
        budget = safety.Budget(
            safety.Limits(predicates=0, member_visits=16_000_000, tree_nodes=0),
        )
        for role in roles:
            name = _ROLE_FILES[role]
            size, digest = inputs[name]
            raw_rows, site_count = counts[role]
            family = safety.read_family(
                data / name,
                sha256=digest,
                byte_count=size,
                raw_rows=raw_rows,
                site_count=site_count,
                budget=budget,
            )
            families[role] = family.sites
        budget.check()
    return families


def _publish(path: pathlib.Path, value: dict[str, Any]) -> None:
    """Publish a bounded manifest atomically; a crash cannot leave a torn success."""
    content = (
        json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + '\n'
    ).encode('ascii')
    if len(content) > _MANIFEST_BYTES:
        raise ExportStop('Manifest reservation exhausted')
    pending = path.with_suffix('.pending.json')
    with pending.open('xb') as target:
        target.write(content)
        target.flush()
        os.fsync(target.fileno())
    os.replace(pending, path)
    descriptor = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _no_stop() -> None:
    """The kernels' cooperative checkpoint; this exporter has no STOP marker."""


def run(data: pathlib.Path, output: pathlib.Path) -> dict[str, Any]:
    """Create one proposed certificate; every partial result remains failed."""
    started = time.monotonic()
    output = output.expanduser().absolute()
    if os.path.lexists(output):
        raise ValueError('Output must be a fresh run directory')
    output.mkdir(parents=True, exist_ok=False)
    report: dict[str, Any] = {
        'schema': _SCHEMA + '-manifest',
        'status': 'incomplete',
        'exit_code': 1,
        'untrusted': True,
        'lean_accepted': False,
        'whole_plane_accepted': False,
        'input_pins': {},
        'safety': {},
        'routes': {},
        'reason': '',
        'complete': False,
    }

    with (output / 'certificate.ndjson').open('xb') as target:
        writer = Stream(target)
        try:
            declared, counts = _declared()
            report['input_pins'] = inputs = _pin_inputs(data, declared)
            families = _read_roles(data, declared, counts)
            writer.write(
                [
                    'header',
                    {
                        'schema': _SCHEMA,
                        'untrusted': True,
                        'input_pins': inputs,
                        'roles': {role: sites for role, (_, sites) in counts.items()},
                        'wire_lifts': _LIFTS,
                        'geometry': {
                            'period': 59,
                            'scale_squared': [441, 10_000],
                            'enclosure_scale': 1 << 64,
                        },
                        'limits': {
                            'total_output_bytes': _OUTPUT_BYTES,
                            'manifest_bytes': _MANIFEST_BYTES,
                            'manifest_reserved_bytes': _MANIFEST_RESERVE,
                            'line_bytes': _LINE_BYTES,
                            'records': _RECORDS,
                            'permutation_chunk': _PERM_CHUNK,
                            'route_candidates': 100_000_000,
                        },
                    },
                ]
            )
            for obligation, left_role, right_role in _PRODUCTS:
                left, right = families[left_role], families[right_role]
                n, m = len(left), len(right)
                # 27*n*m predicates; build/validation/layout at most 160*(n+m)
                # member visits and 2*(n+m) build nodes, with no pruning-rate assumption.
                budget = safety.Budget(
                    safety.Limits(
                        predicates=27 * n * m,
                        member_visits=160 * (n + m),
                        tree_nodes=2 * (n + m),
                    ),
                )
                report['safety'][obligation] = emit_safety(
                    obligation,
                    left_role,
                    right_role,
                    left,
                    right,
                    writer,
                    budget,
                )
            report['routes'] = emit_routes(families, writer, _no_stop)
            if _pin_inputs(data, declared) != inputs:
                raise ValueError('Final input identities changed')
            writer.write(
                [
                    'end',
                    {
                        'complete': True,
                        **writer.prefix(),
                        'safety': report['safety'],
                        'routes': report['routes']['counts'],
                    },
                ]
            )
            target.flush()
            os.fsync(target.fileno())
            report.update(
                status='untrusted_export_complete', exit_code=0, complete=True
            )
        except (
            ExportStop,
            safety.Incomplete,
            routes.LimitExceeded,
            KeyboardInterrupt,
            MemoryError,
        ) as error:
            report.update(reason=str(error) or type(error).__name__)
        except (OSError, ValueError, TypeError, routes.NoRoute) as error:
            report.update(
                status='refused_or_failed',
                exit_code=2,
                reason=f'{type(error).__name__}: {error}',
            )
        finally:
            target.flush()
            os.fsync(target.fileno())
            report['stream'] = {
                'file': 'certificate.ndjson',
                'bytes': writer.bytes,
                'records': writer.records,
                'sha256': writer.digest.hexdigest(),
                'actual_bytes': os.fstat(target.fileno()).st_size,
            }
    report['elapsed_seconds'] = time.monotonic() - started
    _publish(output / 'manifest.json', report)
    return report


def main(argv: Optional[list[str]] = None) -> int:
    """Export once with fixed engineering caps; --data-root may hold only the exact gold inputs."""
    parser = argparse.ArgumentParser(
        description=__doc__ or '', formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument('--output', type=pathlib.Path, required=True,
                        help='fresh export directory (must not exist)')
    parser.add_argument('--data-root', type=pathlib.Path, default=subject.DATA_DIR)
    args = parser.parse_args(argv)
    try:
        result = run(args.data_root, args.output)
    except (OSError, ValueError, ExportStop) as error:
        print('Export refused: ' + str(error), file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True, ensure_ascii=True, allow_nan=False))
    sys.stdout.flush()
    return result['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
