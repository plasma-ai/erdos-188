"""The k42 generation subject: the six gold raw inputs and the two export inputs.

Importing this module performs no I/O. The gold identities (byte count and
SHA-256) of the six raw inputs are read from ``data/k42/manifest.json``, the
one declaration of the gold set in this repository, and every raw read must
match them. The exported certificate and its manifest are named by path; their
observed digests are returned with the bytes read. Raw input reads return the
bytes read, with their observed digest, not paths for an unverified second
read. No mathematical parser or generator runs here.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
import pathlib
from typing import Any, Optional

__all__ = [
    'DATA_DIR', 'GenerationRefused', 'Pin', 'Input', 'Role', 'Subject',
    'PinnedBytes', 'resolve_subject', 'read_input',
]

# the repository's raw input directory, whose manifest declares the gold set
DATA_DIR = pathlib.Path(__file__).resolve().parent.parent.parent / 'data' / 'k42'
_MANIFEST = 'manifest.json'
_RAW_BYTES = 32 * 1_024 * 1_024
# role, manifest key, semantic role, file name, raw rows (every raw row is a distinct site)
_ROLES = (
    ('B', 'base', 'B', 'base.tsv', 30_469),
    ('S', 'carriers', 'full_S', 'carriers.tsv', 19_435),
    ('P', 'plugs', 'P', 'plugs.tsv', 11_064),
    ('M', 'micro_representatives', 'M', 'micro_representatives.tsv', 10_108),
)
# input ID, manifest key, semantic role, file name of the two non-role raw inputs
_OTHERS = (
    ('F', 'cover_sites', 'ordered_F', 'cover_sites.tsv'),
    ('cover_tree', 'cover_tree', 'proposed_complete_cover_stream', 'cover_tree.cert'),
)


class GenerationRefused(ValueError):
    """Refuse a malformed manifest, a changed identity, or an unknown input."""


@dataclasses.dataclass(frozen=True)
class Pin:
    """A relative input path, with its exact byte identity when that identity is gold."""

    name: str
    bytes: Optional[int]
    sha256: Optional[str]


@dataclasses.dataclass(frozen=True)
class Input:
    """One raw or export input, with an explicit root space."""

    key: str
    space: str
    pin: Pin


@dataclasses.dataclass(frozen=True)
class Role:
    """A raw role and its row count; every row is a distinct site."""

    name: str
    manifest_key: str
    raw_rows: int
    input: Input


@dataclasses.dataclass(frozen=True)
class Subject:
    """The gold raw inputs declared by the manifest and the two export inputs."""

    roles: tuple[Role, ...]
    cover: Input
    tree: Input
    certificate: Input
    export_manifest: Input

    def inputs(self) -> tuple[Input, ...]:
        """Return the eight exact inputs, keeping the raw and export spaces distinct."""
        return (
            *(role.input for role in self.roles), self.cover, self.tree,
            self.certificate, self.export_manifest,
        )

    def input(self, key: str) -> Input:
        """Select one known input ID, never a caller path or caller digest."""
        for entry in self.inputs():
            if entry.key == key:
                return entry
        raise GenerationRefused('Unknown generation input ID')


@dataclasses.dataclass(frozen=True)
class PinnedBytes:
    """An immutable byte buffer and its observed digest; parse it without reopening a path."""

    input: Input
    data: bytes = dataclasses.field(repr=False)
    sha256: str


def _pin(files: dict[str, Any], key: str, semantic: str, name: str) -> Pin:
    """Read one gold manifest row: a path with its exact byte count and SHA-256."""
    row = files.get(key)
    if (
        type(row) is not dict or row.get('path') != name
        or row.get('semantic_role') != semantic
        or type(row.get('bytes')) is not int or not 0 < row['bytes'] <= _RAW_BYTES
        or type(row.get('sha256')) is not str or len(row['sha256']) != 64
    ):
        raise GenerationRefused('Invalid manifest row for ' + key)
    return Pin(name, row['bytes'], row['sha256'])


def resolve_subject(data_dir: pathlib.Path = DATA_DIR) -> Subject:
    """Decode the gold identities of ``<data_dir>/manifest.json``; no payload is read."""
    try:
        document = json.loads((data_dir / _MANIFEST).read_text(encoding='ascii'))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise GenerationRefused('Cannot read the gold manifest: ' + str(error)) from error
    files = document.get('files') if type(document) is dict else None
    if type(files) is not dict or set(files) != {
        *(key for _, key, _, _, _ in _ROLES), *(key for _, key, _, _ in _OTHERS),
    }:
        raise GenerationRefused('The gold manifest does not declare the six files')
    roles = tuple(
        Role(name, key, rows, Input(name, 'raw', _pin(files, key, semantic, file_name)))
        for name, key, semantic, file_name, rows in _ROLES
    )
    cover, tree = (
        Input(name, 'raw', _pin(files, key, semantic, file_name))
        for name, key, semantic, file_name in _OTHERS
    )
    return Subject(
        roles, cover, tree,
        Input('certificate', 'export', Pin('certificate.ndjson', None, None)),
        Input('export_manifest', 'export', Pin('manifest.json', None, None)),
    )


def read_input(
    subject: Subject, input_id: str, roots: dict[str, pathlib.Path],
) -> PinnedBytes:
    """Return input bytes and their observed digest; a gold pin's size and SHA-256 must match.

    roots maps the raw and export spaces to directories; only the selected
    input's space is consulted. No line, rational, JSON, count, geometry or
    Lean check happens here.
    """
    entry = subject.input(input_id)
    try:
        content = (roots[entry.space] / entry.pin.name).read_bytes()
    except (KeyError, OSError) as error:
        raise GenerationRefused('Cannot read input ' + input_id + ': ' + str(error)) from error
    observed = hashlib.sha256(content).hexdigest()
    if entry.pin.bytes is not None and (
        len(content) != entry.pin.bytes or observed != entry.pin.sha256
    ):
        raise GenerationRefused('Pinned input length or SHA-256 mismatch: ' + entry.pin.name)
    return PinnedBytes(entry, content, observed)
