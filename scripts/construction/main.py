"""Compile the six construction files from the orbit tables and a tree witness.

The carrier and plug families are recorded as orbit tables, one row per
rotation orbit holding its least member; every mode expands them to the full
families by the rotation rule before anything else. From the repository root,
run with Python 3 (standard library only)::

    python3 scripts/construction/main.py \
        --witness WITNESS --out-dir DIR [--expect-manifest MANIFEST] \
        [--max-rows N] [--max-records N] [--max-direction-depth N] \
        [--max-translation-depth N] [--max-rss-mib N] [--stop-file STOP]

The first flag --compact instead turns a wire certificate and its ordered
witness table into a compact tree witness bound to the expanded families::

    python3 scripts/construction/main.py \
        --compact --certificate CERT --cover-sites F --witness WITNESS \
        [--stop-file STOP]

The first flag --search instead searches a fresh covering tree over the
expanded carriers and plugs, writing a resumable record stream and a progress
file at every checkpoint and, when the tree is complete, the compact witness
and a DONE marker naming it::

    python3 scripts/construction/main.py \
        --search --out-dir DIR [--resume] [--checkpoint-cells N] \
        [--max-cells N] [--max-rows N] [--max-records N] \
        [--max-direction-depth N] [--max-translation-depth N] \
        [--max-rss-mib N] [--stop-file STOP]

The first flag --orbits instead reduces two full rotation-closed tables to
their orbit tables and checks that expanding what it wrote reproduces them
byte for byte; it is the one mode that reads full carrier and plug tables::

    python3 scripts/construction/main.py \
        --orbits [--carriers S] [--plugs P] --out-dir DIR [--stop-file STOP]

The first flag --describe instead reads the two orbit tables and writes a
structural account of the families they record, asserting nothing about the
numbers it finds::

    python3 scripts/construction/main.py \
        --describe --out-dir DIR [--stop-file STOP]

Every mode defaults to the orbit tables of the K42 gold set under data/k42
(--orbits to its carrier and plug tables, and the compaction mode to its
certificate and ordered table); each writes a JSON report beside its
products. A Git LFS pointer standing in for an input is
refused. Every cap defaults to unlimited and there is no time cap of any kind;
a run ends on completion, at a declared cap or at the STOP marker. This is a
producer: its obligations are the identities its own products must satisfy
and warrant nothing about the construction; the finite obligations stay with
the independent checkers. Exit 0 means every product was written and every
identity held, 1 a failed identity or an incomplete run, 2 unusable input or
an operational error, and 130 an interruption.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime
import hashlib
import json
import math
import os
import pathlib
import resource
import sys
import tempfile
import time
from collections.abc import Callable, Iterable
from fractions import Fraction
from typing import Any, Optional

if __package__:
    from . import kernel, search
    from .checker import Checker
    from .util import certificate, geometry, micro, orbits, rationals, witness
else:
    import kernel
    import search
    from checker import Checker
    from util import certificate, geometry, micro, orbits, rationals, witness

__all__ = ['main']

_PACKAGE = pathlib.Path(__file__).resolve().parent
_ASSETS = _PACKAGE.parents[1] / 'data/k42'
_OUTPUT = _PACKAGE / 'output'
# the first line of a Git LFS pointer left in place of an unhydrated file
_POINTER = b'version https://git-lfs.github.com/spec/v1'
# the two orbit tables, one row per rotation orbit, and the families they record
_ORBIT_TABLES = (
    ('carrier_orbits.tsv', 'carriers'),
    ('plug_orbits.tsv', 'plugs'),
)
# the six products, their manifest keys and documentary roles
_PRODUCTS = (
    ('base.tsv', 'base', 'B'),
    ('carriers.tsv', 'carriers', 'full_S'),
    ('plugs.tsv', 'plugs', 'P'),
    ('micro_representatives.tsv', 'micro_representatives', 'M'),
    ('cover_sites.tsv', 'cover_sites', 'ordered_F'),
    ('cover_tree.cert', 'cover_tree', 'proposed_complete_cover_stream'),
)
# the certificate header names the identity of each produced table under these keys
_HEADER_TABLES = (
    ('carriers_sha256', 'carriers.tsv'),
    ('plugs_sha256', 'plugs.tsv'),
    ('base_sha256', 'base.tsv'),
    ('micro_representatives_sha256', 'micro_representatives.tsv'),
    ('cover_sites_sha256', 'cover_sites.tsv'),
)
# the fixed geometry vocabulary of the documentary manifest, which the
# finite-routes driver compares field by field with its subject
_CONVENTIONS = {
    'scale': [21, 100],
    'period': 59,
    'target_points': 42,
    'center_coordinates': 'rational_axial',
    'radius_units': 'physical_Euclidean',
    'disk_boundary': 'closed',
    'site_field_order': ['s', 't', 'r'],
    'certificate_ordinal_base': 0,
    'role_source': 'this_explicit_manifest_not_certificate_header_labels',
}
# the search's products in its output directory
_SEARCH_PRODUCTS = {
    'records': 'records.txt',
    'progress': 'progress.json',
    'witness': 'tree_witness.txt',
    'attempt': 'attempt.txt',
    'done': 'DONE',
}
# the progress file describes this many unresolved cells in full
_UNRESOLVED_REPORTED = 64
# the two commands of this program that regenerate the tree witness byte for byte
_WITNESS_ROUTES = (
    'main.py --search over carrier_orbits.tsv and plug_orbits.tsv',
    'main.py --compact over cover_tree.cert and cover_sites.tsv, bound to the '
    'carriers and plugs expanded from carrier_orbits.tsv and plug_orbits.tsv',
)
# the construction's scaffold: integer centers with this radius or more
_SCAFFOLD_RADIUS = Fraction(47, 100)
# the reducing lift of a cell image: |j v_s| < 100 and |s - midpoint| < 59 give |z| <= 2
_LIFTS = (-2, -1, 0, 1, 2)


class Stopped(Exception):
    """Raised when the STOP marker appears during a run."""


class Refused(ValueError):
    """Raised when an input cannot be decoded at all."""


class Failed(Exception):
    """Raised when a derived identity fails and the run cannot continue."""


class Capped(Exception):
    """Raised when a declared non-time cap is reached."""


@dataclasses.dataclass(frozen=True)
class Caps:
    """The declared non-time caps; None leaves a quantity unlimited."""

    rows: Optional[int] = None
    records: Optional[int] = None
    direction_depth: Optional[int] = None
    translation_depth: Optional[int] = None
    rss_mib: Optional[int] = None
    cells: Optional[int] = None


@dataclasses.dataclass(frozen=True)
class _Input:
    """One input file's bytes and identity."""

    path: pathlib.Path
    data: bytes

    @property
    def sha256(self: _Input) -> str:
        """Return the SHA-256 of the bytes read."""
        return hashlib.sha256(self.data).hexdigest()

    def identity(self: _Input) -> dict[str, Any]:
        """Describe the input for the report."""
        return {'path': str(self.path), 'bytes': len(self.data), 'sha256': self.sha256}


@dataclasses.dataclass(frozen=True)
class _Family:
    """One family expanded from its orbit table, with its canonical table bytes."""

    least: tuple[rationals.Site, ...]
    sites: tuple[rationals.Site, ...]
    data: bytes

    @property
    def sha256(self: _Family) -> str:
        """Return the SHA-256 of the canonical table of the expanded family."""
        return hashlib.sha256(self.data).hexdigest()

    def identity(self: _Family) -> dict[str, Any]:
        """Describe the expanded family for the report."""
        return {'bytes': len(self.data), 'sha256': self.sha256, 'rows': len(self.sites)}


def _peak_rss() -> int:
    """Return the process peak resident set size in bytes."""
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return peak if sys.platform == 'darwin' else peak * 1_024


def _stopper(
    stop_file: Optional[pathlib.Path], rss_mib: Optional[int],
) -> Callable[[], None]:
    """Return the cooperative checkpoint: a present or dangling STOP path stops.

    With a memory cap, a peak resident set above it ends the run at the next
    checkpoint; the cap is a monitored non-time ceiling, not a hard limit.
    """
    rss_bytes = None if rss_mib is None else rss_mib * 1_024 * 1_024

    def checkpoint() -> None:
        if stop_file is not None and os.path.lexists(stop_file):
            raise Stopped('Stop marker exists')
        if rss_bytes is not None and _peak_rss() > rss_bytes:
            raise Capped('memory_limit')

    return checkpoint


def _read(path: pathlib.Path, checkpoint: Callable[[], None]) -> _Input:
    """Read one input file completely, refusing a Git LFS pointer in its place."""
    checkpoint()
    try:
        data = path.read_bytes()
    except OSError as error:
        raise Refused(f'Cannot read {path}: {error}') from error
    if data.startswith(_POINTER):
        raise Refused(f'{path} is a Git LFS pointer; run `git lfs pull`')
    checkpoint()
    return _Input(path, data)


def _write(path: pathlib.Path, data: bytes, checkpoint: Callable[[], None]) -> None:
    """Publish one product atomically so a reader never sees a torn file."""
    checkpoint()
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f'.{path.name}.', delete=False,
    ) as stream:
        temporary = pathlib.Path(stream.name)
        try:
            stream.write(data)
            stream.flush()
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    os.replace(temporary, path)


def _json(document: Any) -> bytes:
    """Encode a report as sorted, indented JSON ending in LF."""
    return (json.dumps(document, indent=2, sort_keys=True) + '\n').encode('ascii')


def _table(source: _Input, name: str) -> tuple[rationals.Site, ...]:
    """Decode one role table, requiring the grammar, domain and strict order."""
    try:
        sites = rationals.parse_table(source.data)
        for site in sites:
            geometry.admit_site(site)
    except ValueError as error:
        raise Refused(f'{name}: {error}') from error
    return sites


def _row(site: rationals.Site) -> list[str]:
    """Spell a site for the report."""
    return [str(value) for value in site]


def _cap(name: str, value: int, limit: Optional[int]) -> None:
    """End the run at a declared cap when a counted quantity exceeds it."""
    if limit is not None and value > limit:
        raise Capped(f'{name}_limit: {value} above the cap {limit}')


def _caps(args: argparse.Namespace) -> Caps:
    """Read the declared caps, requiring nonnegative integers."""
    values = {}
    for field in dataclasses.fields(Caps):
        value = getattr(args, f'max_{field.name}', None)
        if value is not None and value < 0:
            raise Refused(f'--max-{field.name.replace("_", "-")} must be nonnegative')
        values[field.name] = value
    return Caps(**values)


def _removed_carriers(
    carriers: tuple[rationals.Site, ...],
    plugs: tuple[rationals.Site, ...],
    removal: kernel.Removal,
) -> list[dict[str, Any]]:
    """Describe every removed carrier with one exact conflict witness."""
    by_carrier: dict[int, list[Any]] = {}
    for conflict in removal.scan.conflicts:
        by_carrier.setdefault(conflict.carrier, []).append(conflict)
    rows = []
    for index in sorted(by_carrier):
        conflicts = by_carrier[index]
        first = conflicts[0]
        rows.append({
            'carrier': _row(carriers[index]),
            'orbit_representative': _row(orbits.representative(carriers[index])),
            'conflicting_plug_copies': len(conflicts),
            'first_conflict': {
                'plug': _row(plugs[first.plug]),
                'lift': list(first.lift),
                'distance_squared': str(first.distance_squared),
                'lower_squared': str(first.lower_squared),
                'upper_squared': str(first.upper_squared),
            },
        })
    return rows


def _manifest(
    produced: dict[str, dict[str, Any]], sources: dict[str, Any],
) -> dict[str, Any]:
    """Describe the produced bundle in the documentary manifest vocabulary.

    The source block names the producer, the two orbit tables by path and row
    count, the identities of the two families expanded from them and the
    witness record: its identity, byte and record counts and the two routes
    that regenerate it. Neither the orbit tables nor the witness is a file of
    the bundle.
    """
    return {
        'schema_version': 1,
        'kind': 'periodic-disk-raw-assets-v1',
        'purpose': (
            'Exact finite inputs of the 42-term construction, compiled from the '
            'carrier and plug orbit tables and the tree witness named under source'
        ),
        'manifest_role': 'documentary_asset_identity_and_provenance_only',
        'source': {
            'producer': 'scripts/construction/main.py',
            **sources,
        },
        'intended_conventions': dict(_CONVENTIONS),
        'payload_bytes': sum(entry['bytes'] for entry in produced.values()),
        'files': {
            key: {
                'path': name,
                'semantic_role': role,
                'bytes': produced[name]['bytes'],
                'sha256': produced[name]['sha256'],
            }
            for name, key, role in _PRODUCTS
        },
    }


def _expected(manifest: _Input) -> dict[str, tuple[int, str]]:
    """Read the expected byte counts and digests of a manifest, keyed by filename."""
    try:
        document = json.loads(manifest.data.decode('utf-8'))
        return {
            entry['path']: (int(entry['bytes']), str(entry['sha256']))
            for entry in document['files'].values()
        }
    except (KeyError, TypeError, ValueError, UnicodeDecodeError) as error:
        raise Refused(f'Unusable expected manifest: {error}') from error


def _inputs(
    args: argparse.Namespace,
    checker: Checker,
    checkpoint: Callable[[], None],
    caps: Caps,
    report: dict[str, Any],
) -> tuple[_Family, _Family]:
    """Admit the two orbit tables and expand them to the carrier and plug families.

    Every row of an orbit table must be the least member of its own orbit, so
    no two rows share an orbit and the reduction of the expanded family gives
    the table back. The expansion is closed under the rotation by construction;
    the closure obligation belongs to --orbits, where a full table can fail it.
    """
    carrier_input = _read(args.carrier_orbits, checkpoint)
    plug_input = _read(args.plug_orbits, checkpoint)
    report['inputs'] = {
        'carrier_orbits': carrier_input.identity(),
        'plug_orbits': plug_input.identity(),
    }
    carrier_orbits = _table(carrier_input, 'carrier orbits')
    plug_orbits = _table(plug_input, 'plug orbits')
    report['inputs']['carrier_orbits']['rows'] = len(carrier_orbits)
    report['inputs']['plug_orbits']['rows'] = len(plug_orbits)
    tables = (('carrier orbits', carrier_orbits), ('plug orbits', plug_orbits))
    for name, table in tables:
        checker.check(
            f'{name} admitted: canonical, normalized, strictly increasing', True,
        )
        defect = orbits.canonical_defect(table)
        checker.check(
            f'{name}: every row is the least member of its orbit',
            defect is None,
            '' if defect is None else f'{_row(defect)} is not least in its orbit',
        )
    checkpoint()
    carriers, plugs = (
        _Family(table, sites, rationals.format_table(sites))
        for table, sites in zip(
            (carrier_orbits, plug_orbits),
            kernel.families(carrier_orbits, plug_orbits),
            strict=True,
        )
    )
    for name, family in (('carriers', carriers), ('plugs', plugs)):
        _cap('row', len(family.sites), caps.rows)
        report['inputs'][name] = family.identity()
    checker.check(
        'carrier and plug families are disjoint',
        not set(carriers.sites) & set(plugs.sites),
    )
    return carriers, plugs


def _base(
    carriers: tuple[rationals.Site, ...],
    plugs: tuple[rationals.Site, ...],
    checker: Checker,
    checkpoint: Callable[[], None],
    caps: Caps,
    report: dict[str, Any],
) -> tuple[kernel.Removal, tuple[rationals.Site, ...]]:
    """Apply the conflict rule; the base is the retained carriers with the plugs."""
    removal = kernel.remove_conflicting(carriers, plugs, checkpoint)
    base = kernel.base_family(removal.retained, plugs)
    _cap('row', len(base), caps.rows)
    report['removed_carriers'] = _removed_carriers(carriers, plugs, removal)
    report['conflict_scan'] = {
        'conflicting_plug_copies': len(removal.scan.conflicts),
        'bucket_visits': removal.scan.bucket_visits,
        'pair_screens': removal.scan.pair_screens,
        'exact_tests': removal.scan.exact_tests,
    }
    defect = orbits.closure_defect(removal.removed)
    checker.check(
        'removed carriers form whole rotation orbits',
        defect is None,
        '' if defect is None else f'{_row(defect[0])} lacks its rotated image',
    )
    checker.check(
        'plugs lie in the base, which has |S| - |E| + |P| disks',
        set(plugs) <= set(base)
        and len(base) == len(carriers) - len(removal.removed) + len(plugs),
    )
    report['families'] = {
        'S': len(carriers),
        'P': len(plugs),
        'E': len(removal.removed),
        'E_orbits': len(orbits.orbits(removal.removed)),
        'B': len(base),
    }
    return removal, base


def _compile(
    args: argparse.Namespace, checker: Checker, checkpoint: Callable[[], None],
) -> dict[str, Any]:
    """Compile the six files, asserting the derived identities along the way."""
    previous = time.monotonic()
    timings: dict[str, float] = {}
    report: dict[str, Any] = {'kind': 'periodic-disk-construction-result-v1'}
    caps = _caps(args)
    report['caps'] = dataclasses.asdict(caps)

    def stage(name: str) -> None:
        nonlocal previous
        now = time.monotonic()
        timings[name] = round(now - previous, 3)
        previous = now

    # admit the two orbit tables and expand them to the families
    carriers, plugs = _inputs(args, checker, checkpoint, caps, report)
    witness_input = _read(args.witness, checkpoint)
    report['inputs']['witness'] = witness_input.identity()
    stage('inputs')

    # the witness must have been chosen against these carriers and plugs
    try:
        header, records = witness.parse(witness_input.data)
    except ValueError as error:
        raise Refused(str(error)) from error
    report['inputs']['witness']['records'] = len(records)
    _cap('record', len(records), caps.records)
    bound = (
        header.carriers_sha256 == carriers.sha256
        and header.plugs_sha256 == plugs.sha256
        and header.micro_factor == micro.MICRO_FACTOR
    )
    checker.check(
        'tree witness bound to the admitted carriers, plugs and micro factor',
        bound,
        f'the witness names {header.carriers_sha256[:12]}..., '
        f'{header.plugs_sha256[:12]}... and {header.micro_factor}',
    )
    if not bound:
        raise Failed('The witness was chosen against other inputs')
    stage('witness')

    # the conflict rule removes carriers; the base is the rest with the plugs
    removal, base = _base(
        carriers.sites, plugs.sites, checker, checkpoint, caps, report,
    )
    stage('conflicts')

    # the tree witness fixes the micro family, the ordered table and every leaf
    try:
        tree = kernel.expand(records, base, checkpoint)
    except ValueError as error:
        checker.check(
            'tree compiled: every leaf names a base disk or its cell-service disk',
            False,
            str(error),
        )
        raise Failed(str(error)) from error
    checker.check(
        'tree compiled: every leaf names a base disk or its cell-service disk', True,
    )
    _cap('direction_depth', tree.direction_depth, caps.direction_depth)
    _cap('translation_depth', tree.translation_depth, caps.translation_depth)
    _cap('row', len(tree.sites), caps.rows)
    counts = certificate.Counts(tree.directions, tree.translations, tree.leaves)
    checker.check(
        'tree complete: leaves = 1 + D + 3T',
        tree.leaves == 1 + tree.directions + 3 * tree.translations,
    )
    checker.check(
        'ordered witness table is the sorted disjoint union of base and micro disks',
        len(tree.sites) == len(base) + len(tree.micros)
        and tree.sites == tuple(sorted({*base, *tree.micros})),
    )
    report['families']['M'] = len(tree.micros)
    report['families']['F'] = len(tree.sites)
    report['tree'] = {
        'records': counts.records,
        'directions': tree.directions,
        'translations': tree.translations,
        'leaves': tree.leaves,
        'base_leaves': tree.base_leaves,
        'micro_leaves': tree.micro_leaves,
        'direction_depth': tree.direction_depth,
        'translation_depth': tree.translation_depth,
    }
    stage('tree')

    # serialize; the header names the identities of these very tables and of the witness
    tables = {
        'base.tsv': rationals.format_table(base),
        'carriers.tsv': carriers.data,
        'plugs.tsv': plugs.data,
        'micro_representatives.tsv': rationals.format_table(tree.micros),
        'cover_sites.tsv': rationals.format_table(tree.sites),
    }
    digests = {
        key: hashlib.sha256(tables[name]).hexdigest() for key, name in _HEADER_TABLES
    }
    digests['tree_witness_sha256'] = witness_input.sha256
    header_lines = certificate.render_header(certificate.Header(
        digests, micro.MICRO_FACTOR, tree.direction_depth, tree.translation_depth,
        counts, tree.base_leaves, tree.micro_leaves,
    ))
    tables['cover_tree.cert'] = certificate.assemble(header_lines, tree.records)
    report['header'] = [line.decode('ascii') for line in header_lines]
    rows = {
        'base.tsv': len(base),
        'carriers.tsv': len(carriers.sites),
        'plugs.tsv': len(plugs.sites),
        'micro_representatives.tsv': len(tree.micros),
        'cover_sites.tsv': len(tree.sites),
        'cover_tree.cert': counts.records,
    }
    report['produced'] = {}
    for name, _, _ in _PRODUCTS:
        _write(args.out_dir / name, tables[name], checkpoint)
        report['produced'][name] = {
            'bytes': len(tables[name]),
            'sha256': hashlib.sha256(tables[name]).hexdigest(),
            'rows': rows[name],
        }
    manifest = _manifest(report['produced'], {
        'carrier_orbits': {
            'path': args.carrier_orbits.name,
            'rows': report['inputs']['carrier_orbits']['rows'],
        },
        'plug_orbits': {
            'path': args.plug_orbits.name,
            'rows': report['inputs']['plug_orbits']['rows'],
        },
        'carriers_sha256': carriers.sha256,
        'plugs_sha256': plugs.sha256,
        'tree_witness': {
            'sha256': witness_input.sha256,
            'bytes': len(witness_input.data),
            'records': len(records),
            'regenerated_by': list(_WITNESS_ROUTES),
        },
    })
    _write(
        args.out_dir / 'manifest.json',
        (json.dumps(manifest, indent=2) + '\n').encode('ascii'),
        checkpoint,
    )
    stage('written')

    # a development-time comparison against declared identities, never a proof
    if args.expect_manifest is not None:
        expected = _expected(_read(args.expect_manifest, checkpoint))
        for name, _, _ in _PRODUCTS:
            entry = expected.get(name)
            produced = report['produced'][name]
            actual = (produced['bytes'], produced['sha256'])
            checker.check(
                f'{name} has the expected byte count and SHA-256',
                entry == actual,
                f'expected {entry}, produced {actual}',
            )
    report['stage_seconds'] = timings
    report['peak_rss_bytes'] = _peak_rss()
    return report


def _compact(
    args: argparse.Namespace, checker: Checker, checkpoint: Callable[[], None],
) -> dict[str, Any]:
    """Turn a wire certificate into a compact witness bound to the expanded families."""
    report: dict[str, Any] = {'kind': 'periodic-disk-tree-witness-result-v1'}
    carriers, plugs = _inputs(args, checker, checkpoint, Caps(), report)
    certificate_input = _read(args.certificate, checkpoint)
    sites_input = _read(args.cover_sites, checkpoint)
    try:
        header_lines, record_lines = certificate.split(certificate_input.data)
        header = certificate.parse_header(header_lines)
    except ValueError as error:
        raise Refused(f'certificate: {error}') from error
    checker.check('certificate header has the fixed 19-line shape', True)
    sites = _table(sites_input, 'cover_sites')

    # every record's address must be the one derived from the root
    walk = geometry.Preorder()
    entries = []
    counts = {'D': 0, 'T': 0, 'S': 0}
    for number, line in enumerate(record_lines, start=1):
        if number % 4_096 == 0:
            checkpoint()
        try:
            record = certificate.parse_record(line)
            cell = walk.visit(record.kind)
        except ValueError as error:
            raise Refused(f'certificate record {number}: {error}') from error
        if record.cell != cell:
            checker.check(
                'certificate records derive from the root and close it',
                False,
                f'record {number} carries {record.cell.address()}, '
                f'derived {cell.address()}',
            )
            raise Failed('A certificate address differs from its derivation')
        counts[record.kind] += 1
        entries.append((record.kind, record.step, record.ordinal))
    checker.check(
        'certificate records derive from the root and close it', walk.complete,
    )
    declared = header.counts
    checker.check(
        'certificate header counts agree with the records',
        (counts['D'], counts['T'], counts['S'])
        == (declared.directions, declared.translations, declared.leaves),
    )
    try:
        records = witness.compact(entries, sites)
    except ValueError as error:
        checker.check(
            'every witness ordinal resolves in the ordered table', False, str(error),
        )
        raise Failed(str(error)) from error
    checker.check('every witness ordinal resolves in the ordered table', True)
    data = witness.serialize(
        witness.Header(carriers.sha256, plugs.sha256, micro.MICRO_FACTOR), records,
    )
    _write(args.witness, data, checkpoint)
    # the certificate describes its own witness; a header naming another fails
    digest = hashlib.sha256(data).hexdigest()
    named = header.digests['tree_witness_sha256']
    checker.check(
        'certificate header names the witness it compacts to',
        digest == named,
        f'the witness written has digest {digest[:12]}..., the header names {named[:12]}...',
    )
    if digest != named:
        raise Failed('The certificate header names another witness')
    report['inputs']['certificate'] = certificate_input.identity()
    report['inputs']['cover_sites'] = {**sites_input.identity(), 'rows': len(sites)}
    report['records'] = counts
    report['witness'] = {
        'path': str(args.witness),
        'bytes': len(data),
        'sha256': digest,
    }
    report['peak_rss_bytes'] = _peak_rss()
    return report


def _stream_lines(data: bytes, header: witness.Header) -> list[bytes]:
    """Split a search record stream, requiring its tag and binding header.

    A last line without LF is a torn append and is dropped; the caller cuts
    the records to the count its progress file recorded.
    """
    lines = data.split(b'\n')
    lines.pop()
    if len(lines) < 4 or lines[0] != search.TAG:
        raise Refused('The record stream does not start with the search tag and header')
    try:
        bound = witness.parse_header(lines[1:4])
    except ValueError as error:
        raise Refused(f'record stream: {error}') from error
    if bound != header:
        raise Refused('The record stream was written for other carriers or plugs')
    return lines[4:]


def _resume(
    paths: dict[str, pathlib.Path],
    header: witness.Header,
    base: set[rationals.Site],
    checkpoint: Callable[[], None],
) -> tuple[search.State, dict[str, Any]]:
    """Rebuild the search state from the checkpoint stream and progress file."""
    progress_input = _read(paths['progress'], checkpoint)
    stream_input = _read(paths['records'], checkpoint)
    try:
        progress = json.loads(progress_input.data.decode('utf-8'))
        recorded = int(progress['counts']['records'])
        carried = {
            'elapsed_seconds': float(progress['elapsed_seconds']),
            'work': {key: int(value) for key, value in progress['work'].items()},
            'unresolved_cells': list(progress['unresolved_cells']),
            'checkpoints': int(progress['checkpoints']),
        }
    except (KeyError, TypeError, ValueError, UnicodeDecodeError) as error:
        raise Refused(f'Unusable progress file: {error}') from error
    lines = _stream_lines(stream_input.data, header)
    if len(lines) < recorded:
        raise Refused('The record stream is shorter than its progress file records')
    # cut the stream to the recorded records, dropping any later torn append
    kept = stream_input.data.split(b'\n', 4 + recorded)
    with paths['records'].open('r+b') as stream:
        stream.truncate(len(stream_input.data) - len(kept[-1]))
    try:
        state = search.replay(lines[:recorded], base)
    except ValueError as error:
        raise Refused(str(error)) from error
    return state, carried


def _search(
    args: argparse.Namespace, checker: Checker, checkpoint: Callable[[], None],
) -> dict[str, Any]:
    """Search a covering tree, checkpointing the record stream as it grows."""
    started = time.monotonic()
    report: dict[str, Any] = {'kind': 'periodic-disk-tree-search-progress-v1'}
    caps = _caps(args)
    if args.checkpoint_cells < 1:
        raise Refused('--checkpoint-cells must be positive')
    report['caps'] = dataclasses.asdict(caps)
    report['checkpoint_cells'] = args.checkpoint_cells
    carriers, plugs = _inputs(args, checker, checkpoint, caps, report)
    _, base = _base(carriers.sites, plugs.sites, checker, checkpoint, caps, report)
    base_set = set(base)
    header = witness.Header(carriers.sha256, plugs.sha256, micro.MICRO_FACTOR)
    paths = {
        name: args.out_dir / filename for name, filename in _SEARCH_PRODUCTS.items()
    }
    report['products'] = {name: str(path) for name, path in paths.items()}

    # a fresh run starts the stream; a resumed run continues the checkpointed one
    if args.resume:
        state, carried = _resume(paths, header, base_set, checkpoint)
    else:
        if paths['progress'].exists() or paths['records'].exists():
            raise Refused(
                f'A search checkpoint exists in {args.out_dir}; pass --resume to '
                'continue it or choose another --out-dir',
            )
        state = search.State.fresh()
        carried = {
            'elapsed_seconds': 0.0,
            'work': {},
            'unresolved_cells': [],
            'checkpoints': 0,
        }
        _write(
            paths['records'],
            b'\n'.join([search.TAG, *witness.format_header(header)]) + b'\n',
            checkpoint,
        )
    searcher = search.Searcher(
        base, carriers.sites, plugs.sites, caps.direction_depth, caps.translation_depth,
    )
    unresolved: list[dict[str, Any]] = carried['unresolved_cells']
    checkpoints = carried['checkpoints']

    def work() -> dict[str, int]:
        current = {
            **searcher.counts,
            'leaf_lookups': searcher.leaves.lookups,
            'leaf_candidates': searcher.leaves.candidates,
            'leaf_exact_tests': searcher.leaves.exact_tests,
            'containment_screens': searcher.carriers.pair_screens,
            'containment_exact_tests': searcher.carriers.exact_tests,
            'plug_bucket_visits': searcher.plugs.bucket_visits,
            'plug_pair_screens': searcher.plugs.pair_screens,
            'plug_exact_tests': searcher.plugs.exact_tests,
        }
        return {
            key: carried['work'].get(key, 0) + current.get(key, 0)
            for key in sorted({*carried['work'], *current})
        }

    def progress(status: str) -> dict[str, Any]:
        report.update({
            'status': status,
            'checkpoints': checkpoints,
            'counts': dict(state.counts),
            'leaves': state.leaves,
            'pending': len(state.walk.pending),
            'depths': {
                'direction': state.direction_depth,
                'translation': state.translation_depth,
            },
            'cells_by_depth': {
                f'{d},{e}': count
                for (d, e), count in sorted(state.cells_by_depth.items())
            },
            'last_cell': (
                None if state.last_cell is None else list(state.last_cell.address())
            ),
            'unresolved_cells': unresolved,
            'work': work(),
            'elapsed_seconds': round(
                carried['elapsed_seconds'] + time.monotonic() - started, 3,
            ),
            'checkpoint_utc': datetime.datetime.now(datetime.UTC).isoformat(
                timespec='seconds',
            ),
            'peak_rss_bytes': _peak_rss(),
        })
        report['families']['M'] = len(state.micros)
        report['families']['F'] = len(base) + len(state.micros)
        return report

    outcome, stop_reason = 'complete', ''
    with paths['records'].open('ab') as stream:
        try:
            while state.walk.pending:
                checkpoint()
                _cap('cell', state.counts['cells'] + 1, caps.cells)
                _cap('record', state.counts['records'] + 1, caps.records)
                decision = searcher.decide(state.walk.pending[-1])
                if decision.micro and decision.site not in state.micros:
                    _cap('row', len(base) + len(state.micros) + 1, caps.rows)
                cell = state.apply(decision)
                stream.write(search.format_record(decision) + b'\n')
                if decision.kind == 'U' and len(unresolved) < _UNRESOLVED_REPORTED:
                    unresolved.append({
                        'cell': list(cell.address()),
                        'reason': decision.reason,
                        'opposite_corner_exclusion': decision.shortcut,
                        'micro_failures': dict(decision.failures),
                    })
                if state.counts['cells'] % args.checkpoint_cells == 0:
                    stream.flush()
                    os.fsync(stream.fileno())
                    checkpoints += 1
                    _write(paths['progress'], _json(progress('running')), lambda: None)
        except Capped as error:
            outcome, stop_reason = 'incomplete', str(error)
        except (Stopped, KeyboardInterrupt):
            outcome, stop_reason = 'interrupted', 'interrupted'
        stream.flush()
        os.fsync(stream.fileno())
    if outcome == 'complete' and state.counts['unresolved']:
        outcome, stop_reason = 'incomplete', 'depth_limit'

    # the complete tree is the witness; anything else is an attempt with its frontier
    lines = _stream_lines(_read(paths['records'], lambda: None).data, header)
    pending = [
        b'U ' + stop_reason.split(':')[0].encode('ascii')
        for _ in reversed(state.walk.pending)
    ]
    if outcome == 'complete':
        _write(
            paths['witness'],
            b'\n'.join([
                witness.TAG, *witness.format_header(header), *lines, search.END,
            ]) + b'\n',
            lambda: None,
        )
        _write(
            paths['done'], os.fsencode(paths['witness']) + b'\n', lambda: None,
        )
    else:
        _write(
            paths['attempt'],
            b'\n'.join([
                search.ATTEMPT_TAG, *witness.format_header(header), *lines, *pending,
                search.END,
            ]) + b'\n',
            lambda: None,
        )
    checker.check(
        'search complete: every cell of the root is served by one leaf',
        outcome == 'complete',
        f'{stop_reason}; {state.counts["unresolved"]} unresolved, '
        f'{len(state.walk.pending)} pending',
    )
    progress(outcome)
    report['outcome'] = outcome
    report['stop_reason'] = stop_reason
    return report


def _orbits(
    args: argparse.Namespace, checker: Checker, checkpoint: Callable[[], None],
) -> dict[str, Any]:
    """Reduce two rotation-closed families to orbit tables that expand back to them."""
    previous = time.monotonic()
    timings: dict[str, float] = {}
    report: dict[str, Any] = {
        'kind': 'periodic-disk-orbit-tables-result-v1',
        'inputs': {},
        'orbits_by_length': {},
        'produced': {},
    }

    def stage(name: str) -> None:
        nonlocal previous
        now = time.monotonic()
        timings[name] = round(now - previous, 3)
        previous = now

    for product, name in _ORBIT_TABLES:
        source = _read(getattr(args, name), checkpoint)
        family = _table(source, name)
        report['inputs'][name] = {**source.identity(), 'rows': len(family)}
        checker.check(
            f'{name} admitted: canonical, normalized, strictly increasing', True,
        )
        # only a closed family is the union of the orbits of its least members
        defect = orbits.closure_defect(family)
        checker.check(
            f'{name} closed under the rotation with matching radii',
            defect is None,
            '' if defect is None else f'{_row(defect[0])} lacks its rotated image',
        )
        if defect is not None:
            raise Failed(f'The {name} are not closed under the rotation')
        checkpoint()
        table = rationals.format_table(orbits.representatives(family))
        _write(args.out_dir / product, table, checkpoint)
        # the table written must expand back to the family it was reduced from
        written = rationals.parse_table(_read(args.out_dir / product, checkpoint).data)
        lengths: dict[int, int] = {}
        for site in written:
            length = len(orbits.orbit(site))
            lengths[length] = lengths.get(length, 0) + 1
        report['orbits_by_length'][name] = {
            str(length): count for length, count in sorted(lengths.items())
        }
        report['produced'][product] = {
            'bytes': len(table),
            'sha256': hashlib.sha256(table).hexdigest(),
            'rows': len(written),
        }
        checker.check(
            f'expanding the written {product} reproduces {name} byte for byte',
            rationals.format_table(orbits.expand(written)) == source.data,
        )
        stage(name)
    report['stage_seconds'] = timings
    report['peak_rss_bytes'] = _peak_rss()
    return report


def _widest(sites: Iterable[rationals.Site]) -> int:
    """Return the greatest bit length of any numerator or denominator."""
    widest = 0
    for site in sites:
        for value in site:
            numerator, denominator = abs(value.numerator), value.denominator
            widest = max(widest, numerator.bit_length(), denominator.bit_length())
    return widest


def _longest(sites: Iterable[rationals.Site]) -> int:
    """Return the byte length of the longest row, its LF included."""
    return max((len(rationals.format_row(site)) for site in sites), default=0)


def _scaffold(sites: list[rationals.Site]) -> dict[str, Any]:
    """Describe the integer-center disks of scaffold radius and their least pair form.

    The least value of Q(a - b - 59 n) over distinct centers a, b and the nine
    lifts n in {-1,0,1}^2 is the quantity the construction's motif criterion
    bounds below.
    """
    centers = sorted({(int(site[0]), int(site[1])) for site in sites})
    least = None
    for a in centers:
        for b in centers:
            if a == b:
                continue
            for lift_s in (-1, 0, 1):
                for lift_t in (-1, 0, 1):
                    ds, dt = a[0] - b[0] - 59 * lift_s, a[1] - b[1] - 59 * lift_t
                    value = ds * ds + ds * dt + dt * dt
                    least = value if least is None or value < least else least
    return {
        'radius_at_least': str(_SCAFFOLD_RADIUS),
        'rows': len(sites),
        'distinct_centers': len(centers),
        'orbit_representatives': [_row(site) for site in orbits.representatives(sites)],
        'least_pair_quadratic_form': least,
    }


def _direction_candidate(
    step_s: Fraction, step_t: Fraction,
) -> Optional[tuple[int, int, int]]:
    """Return the (d, i, j) whose j v(tau_0) could equal a displacement, or None.

    Every direction of the sector has positive axial components, so both
    components carry the sign of the step, whose absolute value is the
    physical norm of the displacement. The direction then follows from the
    unit vector u = lambda v(tau_0) through tau_0 = -(u_s + 2 u_t + 1) /
    (u_t - u_s + 2), which the two component formulas imply, and tau_0 must
    be (2i + 1 - 4 * 2^d) / 2^(d+1) for a direction cell (d, i).
    """
    if step_s == 0 or step_t == 0 or (step_s > 0) != (step_t > 0):
        return None
    norm = geometry.distance_squared(step_s, step_t)
    if norm.denominator != 1:
        return None
    step = math.isqrt(norm.numerator)
    if step * step != norm.numerator:
        return None
    if step_s < 0:
        step = -step
    if step not in geometry.STEPS:
        return None
    unit_s, unit_t = geometry.SCALE * step_s / step, geometry.SCALE * step_t / step
    divisor = unit_t - unit_s + 2
    if divisor == 0:
        return None
    tau = -(unit_s + 2 * unit_t + 1) / divisor
    if tau.denominator < 2 or tau.denominator & (tau.denominator - 1):
        return None
    scale = tau.denominator // 2
    i, remainder = divmod(tau.numerator - 1 + 4 * scale, 2)
    if remainder or not 0 <= i < scale:
        return None
    return scale.bit_length() - 1, i, step


def _cell_image_matches(
    site: rationals.Site,
) -> list[tuple[geometry.Cell, int, Fraction]]:
    """Return every (cell, step, radius) whose cell-service disk has the site's center.

    The midpoint of a translation square has denominator exactly 2^(e+1) and
    the step displacement j v(tau_0) an odd denominator, so both center
    coordinates of a cell image have denominators of the same 2-adic
    valuation e+1, and the square's indices h and k are the residues that
    clear that power of two. The displacement from the midpoint at each
    reducing lift in {-2,...,2}^2 then fixes the step and the direction, and
    every candidate is confirmed by recomputing the cell-service disk exactly,
    so the list is complete under the rule and holds nothing else. A center
    equal to a midpoint is the step-zero image of every direction; it is
    listed once, under the root direction cell.
    """
    s, t, _ = site
    twos = s.denominator & -s.denominator
    if twos == 1 or twos != t.denominator & -t.denominator:
        return []
    e = twos.bit_length() - 2
    indices = []
    for value in (s, t):
        odd = value.denominator // twos
        residue = value.numerator * pow(59 * odd, -1, twos) % twos
        indices.append((residue - 1) // 2)
    h, k = indices
    midpoint_s, midpoint_t = geometry.midpoint(e, h, k)
    found = []
    for lift_s in _LIFTS:
        step_s = s - midpoint_s + geometry.PERIOD * lift_s
        for lift_t in _LIFTS:
            step_t = t - midpoint_t + geometry.PERIOD * lift_t
            if step_s == 0 and step_t == 0:
                cell, step = geometry.Cell(0, 0, e, h, k), 0
            else:
                candidate = _direction_candidate(step_s, step_t)
                if candidate is None:
                    continue
                d, i, step = candidate
                cell = geometry.Cell(d, i, e, h, k)
            disk, _ = micro.service_disk(cell, step, geometry.direction(cell.d, cell.i))
            if disk[:2] == (s, t):
                found.append((cell, step, disk[2]))
    return found


def _cell_images(family: _Family, checkpoint: Callable[[], None]) -> dict[str, Any]:
    """Count the rows and orbits of a family whose centers are cell images."""
    matched: set[rationals.Site] = set()
    rows = pure = ambiguous = micro_radius = 0
    depths: dict[tuple[int, int], int] = {}
    steps: dict[int, int] = {}
    for number, site in enumerate(family.sites):
        if number % 1_024 == 0:
            checkpoint()
        found = _cell_image_matches(site)
        if not found:
            continue
        rows += 1
        matched.add(orbits.representative(site))
        if len(found) > 1:
            ambiguous += 1
        for cell, step, radius in found:
            steps[step] = steps.get(step, 0) + 1
            if step == 0:
                pure += 1
            else:
                depths[(cell.d, cell.e)] = depths.get((cell.d, cell.e), 0) + 1
            if radius == site[2]:
                micro_radius += 1
    return {
        'rule': (
            'a center is a cell image when it is the center of the cell-service '
            'disk of some cell (d,i;e,h,k) of the covering grammar, at any depth, '
            'at some step in [-21,20]; the translation square follows from the '
            '2-adic structure of the center, the step and direction from the '
            'displacement to its midpoint at each reducing lift, and every '
            'candidate is confirmed exactly; a midpoint itself is the step-zero '
            'image of every direction and is counted once'
        ),
        'matched_orbits': len(matched),
        'residual_orbits': len(family.least) - len(matched),
        'matched_rows': rows,
        'pure_midpoint_rows': pure,
        'ambiguous_rows': ambiguous,
        'micro_rule_radius_matches': micro_radius,
        'cells_by_depth': {
            f'{d},{e}': count for (d, e), count in sorted(depths.items())
        },
        'steps': {str(step): count for step, count in sorted(steps.items())},
    }


def _describe_family(family: _Family, checkpoint: Callable[[], None]) -> dict[str, Any]:
    """Count a family's orbits, radii, integer centers, scaffold and cell images."""
    lengths: dict[int, int] = {}
    for site in family.least:
        length = len(orbits.orbit(site))
        lengths[length] = lengths.get(length, 0) + 1
    radii = sorted({site[2] for site in family.sites})
    integer_rows = [
        site for site in family.sites
        if site[0].denominator == 1 and site[1].denominator == 1
    ]
    by_radius: dict[Fraction, int] = {}
    for site in integer_rows:
        by_radius[site[2]] = by_radius.get(site[2], 0) + 1
    checkpoint()
    return {
        'rows': len(family.sites),
        'orbits': len(family.least),
        'orbits_by_length': {
            str(length): count for length, count in sorted(lengths.items())
        },
        'distinct_radii': len(radii),
        'least_radius': None if not radii else str(radii[0]),
        'greatest_radius': None if not radii else str(radii[-1]),
        'integer_center_rows': len(integer_rows),
        'integer_center_rows_by_radius': {
            str(radius): count
            for radius, count in sorted(by_radius.items(), reverse=True)
        },
        'scaffold': _scaffold(
            [site for site in integer_rows if site[2] >= _SCAFFOLD_RADIUS],
        ),
        'cell_images': _cell_images(family, checkpoint),
        'widest_component_bits': _widest(family.sites),
        'longest_row_bytes': _longest(family.sites),
        'orbit_table': {
            'widest_component_bits': _widest(family.least),
            'longest_row_bytes': _longest(family.least),
        },
    }


def _describe(
    args: argparse.Namespace, checker: Checker, checkpoint: Callable[[], None],
) -> dict[str, Any]:
    """Describe the structure of the families the two orbit tables record."""
    previous = time.monotonic()
    timings: dict[str, float] = {}
    report: dict[str, Any] = {'kind': 'periodic-disk-families-report-v1'}

    def stage(name: str) -> None:
        nonlocal previous
        now = time.monotonic()
        timings[name] = round(now - previous, 3)
        previous = now

    carriers, plugs = _inputs(args, checker, checkpoint, Caps(), report)
    stage('inputs')
    report['families'] = {}
    for name, family in (('carriers', carriers), ('plugs', plugs)):
        report['families'][name] = _describe_family(family, checkpoint)
        stage(name)
    report['stage_seconds'] = timings
    report['peak_rss_bytes'] = _peak_rss()
    return report


def _parser(mode: str) -> argparse.ArgumentParser:
    """Return the argument parser of the selected mode."""
    parser = argparse.ArgumentParser(description=__doc__ or '')
    parser.add_argument('--stop-file', type=pathlib.Path)
    if mode == 'orbits':
        # the one mode that reads full tables: the two families to reduce
        parser.add_argument(
            '--carriers', type=pathlib.Path, default=_ASSETS / 'carriers.tsv',
        )
        parser.add_argument('--plugs', type=pathlib.Path, default=_ASSETS / 'plugs.tsv')
        parser.add_argument('--out-dir', type=pathlib.Path, default=_OUTPUT / 'orbits')
        return parser
    parser.add_argument(
        '--carrier-orbits', type=pathlib.Path, default=_ASSETS / 'carrier_orbits.tsv',
    )
    parser.add_argument(
        '--plug-orbits', type=pathlib.Path, default=_ASSETS / 'plug_orbits.tsv',
    )
    if mode == 'describe':
        parser.add_argument(
            '--out-dir', type=pathlib.Path, default=_OUTPUT / 'describe',
        )
        return parser
    if mode == 'compact':
        parser.add_argument(
            '--witness',
            type=pathlib.Path,
            default=_OUTPUT / 'tree_witness.txt',
            help='the compact tree witness to write',
        )
        parser.add_argument(
            '--certificate', type=pathlib.Path, default=_ASSETS / 'cover_tree.cert',
        )
        parser.add_argument(
            '--cover-sites', type=pathlib.Path, default=_ASSETS / 'cover_sites.tsv',
        )
        return parser
    # the caps of a compilation or a search default to unlimited
    for name in ('rows', 'records', 'direction-depth', 'translation-depth', 'rss-mib'):
        parser.add_argument(f'--max-{name}', type=int)
    if mode == 'search':
        parser.add_argument('--max-cells', type=int)
        parser.add_argument('--out-dir', type=pathlib.Path, default=_OUTPUT / 'search')
        parser.add_argument(
            '--resume',
            action='store_true',
            help='continue the checkpointed search in --out-dir',
        )
        parser.add_argument(
            '--checkpoint-cells',
            type=int,
            default=4_096,
            help='write the stream and progress file every this many cells',
        )
        return parser
    parser.add_argument(
        '--witness',
        type=pathlib.Path,
        default=_OUTPUT / 'tree_witness.txt',
        help='the compact tree witness to compile',
    )
    parser.add_argument('--out-dir', type=pathlib.Path, default=_OUTPUT / 'k42')
    parser.add_argument(
        '--expect-manifest',
        type=pathlib.Path,
        help='compare the produced files against the identities in this manifest',
    )
    return parser


def main(argv: Optional[list[str]] = None) -> int:
    """Run one mode and return zero only when every product and identity holds."""
    arguments = sys.argv[1:] if argv is None else list(argv)
    first = arguments[0] if arguments else ''
    mode = {
        '--compact': 'compact',
        '--search': 'search',
        '--orbits': 'orbits',
        '--describe': 'describe',
    }.get(first, 'compile')
    args = _parser(mode).parse_args(arguments[1:] if mode != 'compile' else arguments)
    for name in (
        'carrier_orbits', 'plug_orbits', 'carriers', 'plugs', 'witness', 'certificate',
        'cover_sites', 'out_dir', 'expect_manifest', 'stop_file',
    ):
        value = getattr(args, name, None)
        if value is not None:
            setattr(args, name, value.expanduser().resolve())
    checkpoint = _stopper(args.stop_file, getattr(args, 'max_rss_mib', None))
    checker = Checker()
    status, code = 'complete', 0
    report: dict[str, Any] = {}
    try:
        checkpoint()
        if mode == 'compact':
            report = _compact(args, checker, checkpoint)
        elif mode == 'search':
            report = _search(args, checker, checkpoint)
            if report['outcome'] == 'interrupted':
                status, code = 'interrupted', 130
            elif report['outcome'] == 'incomplete':
                status, code = 'incomplete', 1
        elif mode == 'orbits':
            report = _orbits(args, checker, checkpoint)
        elif mode == 'describe':
            report = _describe(args, checker, checkpoint)
        else:
            report = _compile(args, checker, checkpoint)
        checkpoint()
    except Failed:
        status, code = 'failed', 1
    except Capped as error:
        status, code = 'incomplete', 1
        checker.check('run within the declared caps', False, str(error))
    except Refused as error:
        status, code = 'refused', 2
        checker.check('inputs decoded', False, str(error))
    except (Stopped, KeyboardInterrupt) as error:
        status, code = 'interrupted', 130
        checker.check('run completed', False, str(error) or 'interrupted')
    except OSError as error:
        status, code = 'error', 2
        checker.check('products written', False, str(error))
    harness_code = checker.finish()
    if code == 0 and harness_code:
        status, code = 'failed', harness_code
    report.update(status=status, exit_code=code, failed_checks=checker.failures)
    # a search that ran owns its progress file, whatever its outcome; one that was
    # refused or stopped before starting leaves an existing checkpoint untouched
    written = bool(report.get('kind')) if mode == 'search' else status != 'interrupted'
    if written:
        # the compile and orbit reports join their products; the compaction report
        # sits by the witness under the witness name; the search report is its
        # progress file; the description is its own product
        if mode == 'compact':
            report_path = args.witness.with_suffix('.report.json')
        elif mode == 'search':
            report_path = args.out_dir / _SEARCH_PRODUCTS['progress']
        elif mode == 'describe':
            report_path = args.out_dir / 'families_report.json'
        else:
            report_path = args.out_dir / 'report.json'
        try:
            _write(report_path, _json(report), lambda: None)
        except OSError as error:
            print(f'Report not written: {error}', file=sys.stderr)
            code = code or 2
    print(f'{status}: exit {code}', file=sys.stderr)
    return code


if __name__ == '__main__':
    sys.exit(main())
