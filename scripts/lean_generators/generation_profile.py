"""Refuse invalid generator controls before payload I/O or output planning.

These finite knob limits are an operational preflight, not an authenticated
generation manifest or a time/RSS guarantee. Input identities, canonical wire
grammar, cross-stage module identities, and exclusive output custody are separate
requirements. In particular, accepting these controls never authorizes a run.
"""

from __future__ import annotations

import argparse

__all__ = ['validate_generation_args', 'validate_full_generation_args']

# These ceilings bound accepted control values; they are not measured memory costs.
MAX_CHUNK = 4096
MAX_REC_DEPTH = 1_000_000
MAX_COST = 1_000_000
MAX_BUDGET = 1_000_000_000
MAX_CHUNKS = 1_000_000
KINDS = ('cover', 'routes', 'membership', 'safety')
OBLIGATIONS = ('O1', 'O2', 'O3')


def _value(args: argparse.Namespace, name: str) -> object:
    """Get a required control without substituting a caller's missing value."""
    try:
        return getattr(args, name)
    except AttributeError:
        raise SystemExit(f'missing --{name.replace("_", "-")}') from None


def _integer(args: argparse.Namespace, name: str, minimum: int, maximum: int) -> int:
    """Require an exact integer in a finite interval, never a bool or coercion."""
    value = _value(args, name)
    if type(value) is not int or not minimum <= value <= maximum:
        raise SystemExit(
            f'--{name.replace("_", "-")} must be an integer in [{minimum}, {maximum}]'
        )
    return value


def _boolean(args: argparse.Namespace, name: str) -> bool:
    """Require an explicit boolean for a boolean control."""
    value = _value(args, name)
    if type(value) is not bool:
        raise SystemExit(f'--{name.replace("_", "-")} must be a boolean')
    return value


def validate_generation_args(
    kind: str, args: argparse.Namespace, *, full: bool = False
) -> None:
    """Validate one generator's controls without consulting paths or payloads.

    ``full`` rejects explicit measurement/negative slices. Its default preserves
    the standalone partial workflow; it is not a full artifact acceptance flag.
    The caller must invoke this at the start of ``generate``, before payload I/O.
    """
    if type(kind) is not str or kind not in KINDS:
        raise SystemExit('unknown generator kind')
    if type(full) is not bool:
        raise SystemExit('full must be a boolean')

    _integer(args, 'max_rec_depth', 1, MAX_REC_DEPTH)
    if kind != 'safety':
        chunk = _integer(args, 'site_chunk', 1, MAX_CHUNK)
        if chunk & (chunk - 1):
            raise SystemExit('--site-chunk must be a power of two')

    if kind in ('cover', 'routes'):
        _integer(args, 'record_chunk', 1, MAX_CHUNK)
        _boolean(args, 'verify')
    elif kind == 'membership':
        negative = _boolean(args, 'negative')
        if negative:
            _integer(args, 'negative_index', 0, args.site_chunk - 1)
            if full:
                raise SystemExit('--negative is not permitted for full generation')
    else:
        _integer(args, 'max_records', 1, MAX_CHUNK)
        _integer(args, 'table_group', 1, MAX_CHUNK)
        for name in ('chunk_budget', 'table_budget'):
            _integer(args, name, 1, MAX_BUDGET)
        for name in ('node_cost', 'bit_cost', 'pair_cost'):
            _integer(args, name, 1, MAX_COST)

        stage = _value(args, 'stage')
        if type(stage) is not str or stage not in ('sites', 'records', 'all'):
            raise SystemExit('--stage must be sites, records, or all')
        only = _value(args, 'only')
        if only is not None:
            if (
                type(only) not in (list, tuple)
                or not 1 <= len(only) <= len(OBLIGATIONS)
                or any(
                    type(name) is not str or name not in OBLIGATIONS for name in only
                )
                or len(set(only)) != len(only)
            ):
                raise SystemExit(
                    '--only must name one or more distinct O1, O2, O3 obligations'
                )
        max_chunks = _value(args, 'max_chunks')
        if max_chunks is not None:
            _integer(args, 'max_chunks', 0, MAX_CHUNKS)
        if full and (stage != 'all' or only is not None or max_chunks is not None):
            raise SystemExit(
                'full generation requires --stage all and no partial selectors'
            )


def validate_full_generation_args(
    cover: argparse.Namespace,
    routes: argparse.Namespace,
    membership: argparse.Namespace,
    safety: argparse.Namespace,
) -> None:
    """Check the shared fixed-4096 partition before any of the four stages run.

    Safety's source fixes its site block size to 4096. Cover and membership must
    have identical partitions, and routes must supply that topology to safety.
    This check does not authenticate actual counts, depths, modules or inputs.
    """
    for kind, args in zip(KINDS, (cover, routes, membership, safety), strict=True):
        validate_generation_args(kind, args, full=True)
    if any(args.site_chunk != MAX_CHUNK for args in (cover, routes, membership)):
        raise SystemExit(
            'full generation requires matching 4096-site cover/routes/membership blocks'
        )
