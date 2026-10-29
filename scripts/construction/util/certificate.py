"""The wire covering certificate: a fixed header, preorder records and END.

Records use single spaces and canonical integers: ``D d i e h k`` and
``T d i e h k`` for splits, ``S d i e h k j ordinal lift_s lift_t`` for a
leaf, where the ordinal is the zero-based row of the ordered witness table
and the lift places the disk copy that serves the cell. The 19-line header is
the certificate's description of its own object: the identities of the five
tables and of the tree witness it was compiled from, the micro radius factor,
the period and window, the greatest direction and translation depth of any
cell, leaves included, and the record counts. The admitted depth ceilings
belong to the readers, not to the header.
"""

from __future__ import annotations

import dataclasses
import re
from collections.abc import Iterable
from fractions import Fraction

from .geometry import PERIOD, STEPS, Cell
from .rationals import format_rational, parse_rational

__all__ = [
    'HEADER_LINES', 'TAG', 'DIGEST_KEYS', 'Header', 'Counts', 'WireRecord',
    'parse_header', 'render_header', 'parse_record', 'format_record', 'split',
]

HEADER_LINES = 19
TAG = b'PERIODIC_DISK_COVER_TREE_V1'
# the six objects the header identifies, in header order
DIGEST_KEYS = (
    'carriers_sha256', 'plugs_sha256', 'base_sha256', 'micro_representatives_sha256',
    'cover_sites_sha256', 'tree_witness_sha256',
)
_END = b'END'
_DIGEST = re.compile(rb'[0-9a-f]{64}')
_COUNT = re.compile(rb'0|[1-9][0-9]*')
_RATIONAL = re.compile(rb'[0-9/-]+')
# five address fields, then for a leaf the step, ordinal and two lift fields
_ADDRESS = rb' (0|[1-9][0-9]*)' * 5
_SPLIT = re.compile(rb'([DT])' + _ADDRESS)
_LEAF = re.compile(
    rb'S' + _ADDRESS + rb' (0|-?[1-9][0-9]*) (0|[1-9][0-9]*)'
    + rb' (0|-?[1-9][0-9]*) (0|-?[1-9][0-9]*)',
)


@dataclasses.dataclass(frozen=True)
class Counts:
    """The record counts of one complete tree."""

    directions: int
    translations: int
    leaves: int

    @property
    def records(self: Counts) -> int:
        """Return the total record count."""
        return self.directions + self.translations + self.leaves


@dataclasses.dataclass(frozen=True)
class Header:
    """A decoded 19-line header: six digests, the micro factor, observed depths and counts."""

    digests: dict[str, str]
    micro_factor: Fraction
    direction_depth: int
    translation_depth: int
    counts: Counts
    base_leaves: int
    micro_leaves: int


@dataclasses.dataclass(frozen=True, slots=True)
class WireRecord:
    """One decoded certificate record."""

    kind: str
    cell: Cell
    step: int = 0
    ordinal: int = 0
    lift: tuple[int, int] = (0, 0)


def _value(line: bytes, key: str, pattern: re.Pattern[bytes]) -> bytes:
    """Return the value of a ``key value`` header line matching a pattern."""
    prefix = key.encode('ascii') + b' '
    if not line.startswith(prefix) or pattern.fullmatch(line[len(prefix):]) is None:
        raise ValueError(f'Malformed certificate header line for {key}')
    return line[len(prefix):]


def parse_header(lines: list[bytes]) -> Header:
    """Decode and validate the fixed header shape; the digests are not verified."""
    if len(lines) != HEADER_LINES or lines[0] != TAG:
        raise ValueError('The certificate header must be 19 lines under the fixed tag')
    digests = {
        key: _value(line, key, _DIGEST).decode('ascii')
        for key, line in zip(DIGEST_KEYS, lines[1:7], strict=True)
    }
    micro_factor = parse_rational(_value(lines[7], 'micro_radius_factor', _RATIONAL))
    fixed = (
        b'period %d' % PERIOD,
        b'length %d' % len(STEPS),
        b'step_interval %d %d' % (STEPS[0], STEPS[-1]),
    )
    for line, expected in zip(lines[8:11], fixed, strict=True):
        if line != expected:
            raise ValueError(f'Unexpected certificate header line: {line[:60]!r}')
    keys = (
        'direction_depth', 'translation_depth', 'tree_records', 'direction_records',
        'translation_records', 'leaf_records', 'base_leaves', 'micro_leaves',
    )
    values = {
        key: int(_value(line, key, _COUNT))
        for key, line in zip(keys, lines[11:], strict=True)
    }
    counts = Counts(
        values['direction_records'], values['translation_records'], values['leaf_records'],
    )
    # a complete tree has leaves = 1 + D + 3T, and every leaf names a base or micro disk
    if (
        values['tree_records'] != counts.records
        or counts.leaves != 1 + counts.directions + 3 * counts.translations
        or values['base_leaves'] + values['micro_leaves'] != counts.leaves
    ):
        raise ValueError('The certificate header counts do not describe a tree')
    return Header(
        digests, micro_factor, values['direction_depth'], values['translation_depth'],
        counts, values['base_leaves'], values['micro_leaves'],
    )


def render_header(header: Header) -> list[bytes]:
    """Write the 19 header lines of a compiled tree."""
    lines = [TAG]
    lines.extend(
        b'%s %s' % (key.encode('ascii'), header.digests[key].encode('ascii'))
        for key in DIGEST_KEYS
    )
    lines.extend((
        b'micro_radius_factor ' + format_rational(header.micro_factor),
        b'period %d' % PERIOD,
        b'length %d' % len(STEPS),
        b'step_interval %d %d' % (STEPS[0], STEPS[-1]),
        b'direction_depth %d' % header.direction_depth,
        b'translation_depth %d' % header.translation_depth,
        b'tree_records %d' % header.counts.records,
        b'direction_records %d' % header.counts.directions,
        b'translation_records %d' % header.counts.translations,
        b'leaf_records %d' % header.counts.leaves,
        b'base_leaves %d' % header.base_leaves,
        b'micro_leaves %d' % header.micro_leaves,
    ))
    return lines


def parse_record(line: bytes) -> WireRecord:
    """Decode one certificate record without checking it against the tree."""
    match = _SPLIT.fullmatch(line)
    if match is not None:
        return WireRecord(
            match.group(1).decode('ascii'),
            Cell(*(int(match.group(index)) for index in range(2, 7))),
        )
    match = _LEAF.fullmatch(line)
    if match is None:
        raise ValueError(f'Malformed certificate record: {line[:60]!r}')
    values = [int(match.group(index)) for index in range(1, 10)]
    return WireRecord(
        'S', Cell(*values[:5]), values[5], values[6], (values[7], values[8]),
    )


def format_record(record: WireRecord) -> bytes:
    """Encode one record in the wire grammar."""
    if record.kind == 'S':
        return b'S %d %d %d %d %d %d %d %d %d' % (
            *record.cell.address(), record.step, record.ordinal, *record.lift,
        )
    return b'%s %d %d %d %d %d' % (record.kind.encode('ascii'), *record.cell.address())


def split(data: bytes) -> tuple[list[bytes], list[bytes]]:
    """Separate a certificate into its header lines and its record lines."""
    if not data.endswith(b'\n'):
        raise ValueError('A certificate must end with LF')
    lines = data[:-1].split(b'\n')
    if len(lines) < HEADER_LINES + 1 or lines[-1] != _END:
        raise ValueError('A certificate must hold its header, records and a final END')
    return lines[:HEADER_LINES], lines[HEADER_LINES:-1]


def assemble(header: Iterable[bytes], records: Iterable[bytes]) -> bytes:
    """Join header lines, record lines and the END marker into certificate bytes."""
    return b'\n'.join((*header, *records, _END)) + b'\n'
