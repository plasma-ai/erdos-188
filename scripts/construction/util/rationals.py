"""Canonical rational tokens and header-free site tables.

A token is an integer ``0`` or ``-?[1-9][0-9]*``, or a reduced fraction
``num/den`` with ``den > 1``. This is the spelling ``str(fractions.Fraction)``
produces, so parsing and formatting are inverse byte for byte. A table row is
``s<TAB>t<TAB>r<LF>`` and a table is strictly increasing in numeric triple
order, so a table equals its own sorted set and has one serialization.
"""

from __future__ import annotations

import math
import re
from collections.abc import Iterable
from fractions import Fraction

__all__ = [
    'Site',
    'parse_rational',
    'format_rational',
    'parse_row',
    'format_row',
    'parse_table',
    'format_table',
]

# an exact site: normalized axial center coordinates and a physical radius
Site = tuple[Fraction, Fraction, Fraction]

_INTEGER = re.compile(rb'0|-?[1-9][0-9]*')
_FRACTION = re.compile(rb'(-?[1-9][0-9]*)/([1-9][0-9]*)')


def parse_rational(token: bytes) -> Fraction:
    """Decode one canonical token; every other spelling is a grammar error."""
    if _INTEGER.fullmatch(token):
        return Fraction(int(token))
    match = _FRACTION.fullmatch(token)
    if match is None:
        raise ValueError(f'Noncanonical rational token: {token[:40]!r}')
    numerator, denominator = int(match.group(1)), int(match.group(2))
    if denominator == 1 or math.gcd(numerator, denominator) != 1:
        raise ValueError(f'Unreduced rational token: {token[:40]!r}')
    return Fraction(numerator, denominator)


def format_rational(value: Fraction) -> bytes:
    """Spell an exact rational canonically, as ``str(Fraction)`` does."""
    if value.denominator == 1:
        return b'%d' % value.numerator
    return b'%d/%d' % (value.numerator, value.denominator)


def parse_row(line: bytes) -> Site:
    """Decode one LF-stripped row of three tab-separated canonical rationals."""
    fields = line.split(b'\t')
    if len(fields) != 3:
        raise ValueError('A site row must contain exactly three tab-separated fields')
    return (
        parse_rational(fields[0]),
        parse_rational(fields[1]),
        parse_rational(fields[2]),
    )


def format_row(site: Site) -> bytes:
    """Serialize one site as its LF-terminated canonical row."""
    return b'\t'.join(format_rational(value) for value in site) + b'\n'


def parse_table(data: bytes) -> tuple[Site, ...]:
    """Decode a whole table, requiring LF framing and strictly increasing rows.

    Duplicate rows and rows out of numeric order are refused, not repaired, so a
    decoded table is exactly the sorted set of its rows.
    """
    if not data:
        return ()
    if not data.endswith(b'\n'):
        raise ValueError('A site table must end with LF')
    sites = []
    previous = None
    for number, line in enumerate(data[:-1].split(b'\n'), start=1):
        if b'\r' in line:
            raise ValueError(f'Row {number}: carriage returns are not admitted')
        try:
            site = parse_row(line)
        except ValueError as error:
            raise ValueError(f'Row {number}: {error}') from error
        if previous is not None and not previous < site:
            raise ValueError(f'Row {number}: rows must strictly increase')
        sites.append(site)
        previous = site
    return tuple(sites)


def format_table(sites: Iterable[Site]) -> bytes:
    """Serialize already sorted distinct sites as one canonical table."""
    return b''.join(format_row(site) for site in sites)
