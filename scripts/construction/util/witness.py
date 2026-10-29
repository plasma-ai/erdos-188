"""The compact tree witness: the choice content of a covering tree.

The witness lists the tree's records in preorder, one per line: ``D`` for a
direction split, ``T`` for a translation split and ``S j s t r`` for a leaf
with step ``j`` served by the disk ``(s, t, r)``, spelled canonically. It
carries no address, ordinal or lift; the producer derives those. A header
binds the witness to the carriers and plugs it was chosen against and to the
micro radius factor, and ``END`` closes the stream.
"""

from __future__ import annotations

import dataclasses
import re
from collections.abc import Iterable, Sequence
from fractions import Fraction
from typing import Optional

from .rationals import Site, format_rational, parse_rational

__all__ = [
    'TAG', 'Header', 'Record', 'parse_header', 'format_header', 'parse', 'serialize',
    'compact',
]

TAG = b'PERIODIC_DISK_TREE_WITNESS_V1'
_END = b'END'
_DIGEST = re.compile(rb'[0-9a-f]{64}')
_STEP = re.compile(rb'0|-?[1-9][0-9]*')


@dataclasses.dataclass(frozen=True)
class Header:
    """The inputs a witness was chosen against."""

    carriers_sha256: str
    plugs_sha256: str
    micro_factor: Fraction


@dataclasses.dataclass(frozen=True, slots=True)
class Record:
    """One preorder record: a split, or a leaf's step and disk."""

    kind: str
    step: int = 0
    site: Optional[Site] = None


def _header_line(line: bytes, key: bytes) -> bytes:
    """Return the value of a ``key value`` header line."""
    prefix = key + b' '
    if not line.startswith(prefix) or b' ' in line[len(prefix):]:
        raise ValueError(f'Malformed witness header line: {line[:60]!r}')
    return line[len(prefix):]


def _digest(value: bytes) -> str:
    """Require one lowercase hexadecimal SHA-256."""
    if _DIGEST.fullmatch(value) is None:
        raise ValueError('A witness header digest is not a lowercase SHA-256')
    return value.decode('ascii')


def parse_header(lines: Sequence[bytes]) -> Header:
    """Decode the three binding lines that follow a witness tag."""
    if len(lines) != 3:
        raise ValueError('A tree witness header has three binding lines')
    return Header(
        _digest(_header_line(lines[0], b'carriers_sha256')),
        _digest(_header_line(lines[1], b'plugs_sha256')),
        parse_rational(_header_line(lines[2], b'micro_radius_factor')),
    )


def format_header(header: Header) -> list[bytes]:
    """Encode the three binding lines that follow a witness tag."""
    return [
        b'carriers_sha256 ' + header.carriers_sha256.encode('ascii'),
        b'plugs_sha256 ' + header.plugs_sha256.encode('ascii'),
        b'micro_radius_factor ' + format_rational(header.micro_factor),
    ]


def parse(data: bytes) -> tuple[Header, list[Record]]:
    """Decode a witness file into its header and preorder records."""
    if not data.endswith(b'\n'):
        raise ValueError('A tree witness must end with LF')
    lines = data[:-1].split(b'\n')
    if len(lines) < 5 or lines[0] != TAG:
        raise ValueError('A tree witness must start with its tag and header')
    header = parse_header(lines[1:4])
    if lines[-1] != _END:
        raise ValueError('A tree witness must close with END')
    records = []
    for number, line in enumerate(lines[4:-1], start=5):
        if line == b'D' or line == b'T':
            records.append(Record(line.decode('ascii')))
            continue
        fields = line.split(b' ')
        if len(fields) != 5 or fields[0] != b'S' or _STEP.fullmatch(fields[1]) is None:
            raise ValueError(f'Line {number}: malformed witness record')
        records.append(Record(
            'S', int(fields[1]),
            (
                parse_rational(fields[2]),
                parse_rational(fields[3]),
                parse_rational(fields[4]),
            ),
        ))
    return header, records


def serialize(header: Header, records: Iterable[Record]) -> bytes:
    """Encode a header and preorder records as one witness file."""
    lines = [TAG, *format_header(header)]
    for record in records:
        if record.kind == 'S':
            if record.site is None:
                raise ValueError('A leaf record needs its disk')
            lines.append(b'S %d %s %s %s' % (
                record.step, format_rational(record.site[0]),
                format_rational(record.site[1]), format_rational(record.site[2]),
            ))
        elif record.kind in ('D', 'T'):
            lines.append(record.kind.encode('ascii'))
        else:
            raise ValueError(f'Unknown witness record kind: {record.kind!r}')
    lines.append(_END)
    return b'\n'.join(lines) + b'\n'


def compact(
    kinds_steps_ordinals: Iterable[tuple[str, int, int]], sites: Sequence[Site],
) -> list[Record]:
    """Turn wire records into witness records by resolving ordinals to disks."""
    records = []
    for kind, step, ordinal in kinds_steps_ordinals:
        if kind == 'S':
            if not 0 <= ordinal < len(sites):
                raise ValueError(f'A witness ordinal {ordinal} does not resolve')
            records.append(Record('S', step, sites[ordinal]))
        else:
            records.append(Record(kind))
    return records
