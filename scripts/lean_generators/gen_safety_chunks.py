#!/usr/bin/env python3
"""Generate the Lean data and check modules for the K42 safety-tree certificate.

Inputs (read only): the exported certificate ``certificate.ndjson`` with its
``manifest.json``, and the four role tables ``carriers.tsv`` (S), ``base.tsv``
(B), ``plugs.tsv`` (P) and ``micro_representatives.tsv`` (M), each one site per
row as ``s<TAB>t<TAB>r`` with canonical integers or reduced ``num/den``. The four
role tables are gold: their SHA-256 identities are verified against
``data/k42/manifest.json`` before use. The certificate and manifest are read by path;
the certificate's observed digest is recorded in the module docstrings, and the
manifest read must describe the certificate read (stream digest and record
count) and carry the tables' registered identities.

Tables, certificate and manifest are parsed only from immutable buffers read
once. The routes site modules below are pathname-read dependencies: the routes
lane must have written them under the same ``--out-dir`` first.

Outputs, under ``<out>/Data`` and ``<out>/Checks`` (module names
``Erdos188.UpperBound.Data.*`` and ``Erdos188.UpperBound.Checks.*``):

* the site trees are the routes lane's ``SitesRoutes<R>_NNN.lean`` /
  ``SitesRoutes<R>.lean`` (``routesSites<R>``, ``routesDepth<R>``; ordinal = TSV
  row, depth-12 blocks of at most 4,096 leaves), which this generator verifies
  leaf by leaf against the tables instead of emitting a second encoding; their
  shape and validity theorems live in ``Checks/RoutesValid<R>.lean``;
* ``Perm<Obl><Side>_NNN.lean`` / ``Perm<Obl><Side>.lean``: the position-to-ordinal
  permutation as an ``OrdTree`` of the family's depth, and ``Inv<Obl><Side>*``: its
  inverse (ordinal-to-position), used by the chunked surjectivity check. When the
  left and right permutations of a self-product obligation are identical the
  generator emits one tree ``perm<Obl>`` / ``inv<Obl>`` used for both sides;
* ``Families<Obl>.lean``: the ``WireFamily`` values of one obligation (``famO1``,
  ``famO2``, ``famO3L``, ``famO3R``);
* ``BoxTable<Obl><A|B>_NNN.lean`` / ``BoxTable<Obl><A|B>.lean``: the laminar tree
  of node ranges of one side of an obligation with the claimed range box of every
  interval (``BoxTree``), cut into subtrees whose minimal intervals total at most
  ``--table-budget`` positions; ``Checks/BoxTable<Obl><A|B>_NNN.lean`` checks each
  subtree in the kernel (minimal intervals by recomputation, splits as one union) and
  ``Checks/BoxTable<Obl><A|B>.lean`` combines them into ``boxCheck<Obl><A|B>``;
* ``Records<Obl>_NNN.lean``: the node and pair records of one chunk in stream
  order; ``SafetyStates<Obl>.lean``: the replay state before every chunk (Python
  replay, untrusted; the kernel verifies each chunk against them);
* ``Checks/SafetyStep<Obl>_NNN.lean``: one kernel-checked chunk theorem over the fast
  replay ``safetyStepFast`` (node boxes from the two tables, recursor lookups);
* ``Checks/SafetySurj<Obl><Side>_NNN.lean``: the per-chunk surjectivity checks of a
  permutation through its inverse, grouped by ``--table-group``;
  ``Checks/SafetyFamilies.lean``: their combination; ``Checks/SafetyAll.lean``: the chained fast replay per obligation,
  its conversion to ``safetyStep`` by ``safetyStepFast_sound``, and the three final
  theorems.

Depth convention (``IndexTree.get?``): at a node with ``depth + 1`` levels left,
position ``p`` descends left when ``p < 2 ^ depth`` and right with ``p - 2 ^ depth``
otherwise, so the path of ``p`` reads its binary digits from bit ``depth - 1``
down to bit ``0``. A block of ``2 ^ 12`` ordinals starting at ``k * 2 ^ 12`` is a
depth-12 subtree, and the top tree spends the remaining ``depth - 12`` bits
selecting the block, so ``routesSites<R>.get? routesDepth<R> n`` finds ordinal ``n``.

Chunking. The kernel keeps every intermediate reduction of one ``decide +kernel``
declaration, so the memory of a chunk theorem grows with the work it contains. A
node record costs ``--node-cost`` units plus ``--bit-cost`` per pruned bit (block
test), a pair record ``--pair-cost`` units (one exact test per residual bit; the
certificate has exactly one). A chunk closes when adding the next record would
exceed ``--chunk-budget`` or ``--max-records``. Box tables are cut so that the
minimal intervals of one subtree total at most ``--table-budget`` positions
(measured: a member visit of the recomputation costs about 0.65 MB with the
original lookups, less with the fast ones).
"""

from __future__ import annotations

import argparse
import io
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

if __package__:
    from .generation_profile import validate_generation_args
    from .generation_subject import GenerationRefused, read_input, resolve_subject
else:
    from generation_profile import validate_generation_args
    from generation_subject import GenerationRefused, read_input, resolve_subject

DATA_DIR = Path(__file__).resolve().parent.parent.parent / "data" / "k42"
ROLES = {"S": "carriers.tsv", "B": "base.tsv", "P": "plugs.tsv", "M": "micro_representatives.tsv"}
OBLIGATIONS = [("O1", "S", "S"), ("O2", "B", "B"), ("O3", "M", "P")]
SITE_BITS = 12
SITE_CHUNK = 2**SITE_BITS
MAX_LINE = 100
DYADIC = 2**64
FIELD_RE = re.compile(r"(-?\d+)(?:/(\d+))?")
GENERATED = (
    "Generated by `gen_safety_chunks.py` under\n"
    "`scripts/lean_generators/`; do not edit by hand."
)

# ----------------------------------------------------------------------------
# Inputs


def parse_fraction(text: str, where: str) -> tuple[int, int]:
    match = FIELD_RE.fullmatch(text)
    if match is None:
        raise SystemExit(f"{where}: bad field {text!r}")
    num = int(match.group(1))
    if match.group(2) is None:
        return num, 1
    den = int(match.group(2))
    if den <= 1 or math.gcd(num, den) != 1:
        raise SystemExit(f"{where}: field {text!r} is not a reduced fraction")
    return num, den


def read_sites(data: bytes, path: Path) -> list[tuple[int, int, int, int, int, int]]:
    """Read one role table; verify reduced fields, validity, and strict
    rational-lexicographic increase (hence distinctness) in row order.
    The path labels errors and is never opened; data is the verified buffer."""
    sites = []
    previous = None
    # Match Path.open(): default encoding and universal newline translation.
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        for line_number, line in enumerate(handle, 1):
            where = f"{path.name}:{line_number}"
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 3:
                raise SystemExit(f"{where}: expected three fields, got {len(parts)}")
            (s_num, s_den), (t_num, t_den), (r_num, r_den) = (parse_fraction(p, where) for p in parts)
            key = (Fraction(s_num, s_den), Fraction(t_num, t_den), Fraction(r_num, r_den))
            if not (0 <= key[0] < 59 and 0 <= key[1] < 59 and 0 < key[2] < Fraction(1, 2)):
                raise SystemExit(f"{where}: site outside the valid domain")
            if previous is not None and not key > previous:
                raise SystemExit(f"{where}: rows are not strictly increasing")
            previous = key
            sites.append((s_num, s_den, t_num, t_den, r_num, r_den))
    return sites


class Obligation:
    def __init__(self, name: str, left: str, right: str, n: int, m: int):
        self.name, self.left, self.right, self.n, self.m = name, left, right, n, m
        self.perm_chunks = {"left": [], "right": []}
        self.records: list[tuple] = []  # ("node", a0, a1, b0, b1, in, pruned, kind, cut) | ("pair", a, b, mask)
        self.node_ids: list[int] = []  # the node id of each node record, in stream order
        self.pair_nodes: list[int] = []  # the node id named by each pair record
        self.end = None
        self.perm = {}
        self.inv = {}


def read_manifest(data: bytes) -> dict:
    """Match the former Path.read_text() JSON parse without reopening its path."""
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        return json.loads(handle.read())


def read_certificate(data: bytes, records: int) -> dict[str, Obligation]:
    """Parse verified bytes with the original binary-line NDJSON grammar; the stream must hold
    the record count its receipt describes."""
    obligations: dict[str, Obligation] = {}
    order = []
    records_seen = 0
    with io.BytesIO(data) as handle:
        for raw in handle:
            records_seen += 1
            record = json.loads(raw)
            kind = record[0]
            if kind == "header":
                if record[1].get("schema") != "periodic-disk-untrusted-certificate-v1":
                    raise SystemExit("unexpected header schema")
            elif kind == "safety_begin":
                _, name, left, right, n, m = record
                if name in obligations:
                    raise SystemExit(f"{name}: repeated safety section")
                obligations[name] = Obligation(name, left, right, n, m)
                order.append(name)
            elif kind == "perm":
                _, name, side, offset, values = record
                obligations[name].perm_chunks[side].append((offset, values))
            elif kind == "node":
                _, name, node_id, a0, a1, b0, b1, in_mask, pruned, node_kind, cut = record
                obligation = obligations[name]
                if node_id != len(obligation.node_ids):
                    raise SystemExit(f"{name}: node ids are not consecutive at {node_id}")
                obligation.node_ids.append(node_id)
                obligation.records.append(("node", a0, a1, b0, b1, in_mask, pruned, node_kind, cut))
            elif kind == "pair":
                _, name, node_id, a_pos, b_pos, mask = record
                obligation = obligations[name]
                obligation.pair_nodes.append(node_id)
                obligation.records.append(("pair", a_pos, b_pos, mask))
            elif kind == "safety_end":
                _, name, info = record
                obligations[name].end = info
            elif kind == "end":
                info = record[1]
                if not info.get("complete") or info.get("records_before_end") != records_seen - 1:
                    raise SystemExit("incomplete stream or record count mismatch in the end record")
    if records_seen != records:
        raise SystemExit(f"the receipt describes {records} records, read {records_seen}")
    if [(o, l, r) for o, l, r in OBLIGATIONS] != [(n, obligations[n].left, obligations[n].right) for n in order]:
        raise SystemExit(f"unexpected obligation order or roles: {order}")
    for obligation in obligations.values():
        info = obligation.end
        nodes = len(obligation.node_ids)
        pairs = len(obligation.pair_nodes)
        perm_records = sum(len(c) for c in obligation.perm_chunks.values())
        if info is None or info["nodes"] != nodes or info["pairs"] != pairs or info["permutations"] != perm_records:
            raise SystemExit(f"{obligation.name}: safety_end counts do not match the stream")
        if info["certified"] != info["required"] or info["required"] != 9 * obligation.n * obligation.m:
            raise SystemExit(f"{obligation.name}: certified total is not 9 n m")
        for side, count in (("left", obligation.n), ("right", obligation.m)):
            offset = 0
            values: list[int] = []
            for chunk_offset, chunk in obligation.perm_chunks[side]:
                if chunk_offset != offset or not 0 < len(chunk) <= 4096:
                    raise SystemExit(f"{obligation.name} {side}: permutation chunks are not contiguous")
                offset += len(chunk)
                values.extend(chunk)
            if len(values) != count or sorted(values) != list(range(count)):
                raise SystemExit(f"{obligation.name} {side}: permutation is not a bijection of [0, {count})")
            obligation.perm[side] = values
            inverse = [0] * count
            for position, ordinal in enumerate(values):
                inverse[ordinal] = position
            obligation.inv[side] = inverse
    return obligations


# ----------------------------------------------------------------------------
# Python replay of the replay discipline (untrusted; mirrors SafetyData.safetyStepOne)


def residual_mask(in_mask: int, pruned: int) -> int:
    return in_mask ^ (in_mask & pruned)


def node_continue(a0, a1, b0, b1, residual, kind, cut, stack):
    if kind == 0:
        if residual == 0 and cut == 0:
            return stack
    elif kind == 1:
        if residual != 0 and cut == 0:
            return [("pair", a1, b0, b1, residual, a0, b0)] + stack
    elif kind == 2:
        if a0 < cut < a1:
            return [("node", a0, cut, b0, b1, residual), ("node", cut, a1, b0, b1, residual)] + stack
    elif kind == 3:
        if b0 < cut < b1:
            return [("node", a0, a1, b0, cut, residual), ("node", a0, a1, cut, b1, residual)] + stack
    return None


def advance_pair(a1, b0, b1, mask, a_pos, b_pos, stack):
    if b_pos + 1 < b1:
        return [("pair", a1, b0, b1, mask, a_pos, b_pos + 1)] + stack
    if a_pos + 1 < a1:
        return [("pair", a1, b0, b1, mask, a_pos + 1, b0)] + stack
    return stack


def step_one(state: list, record: tuple):
    """`safetyStepOne` without the box and pair predicates (the kernel checks those)."""
    if not state:
        return None
    top, stack = state[0], state[1:]
    if top[0] == "node" and record[0] == "node":
        _, a0, a1, b0, b1, mask = top
        _, a0p, a1p, b0p, b1p, in_mask, pruned, kind, cut = record
        if (a0, a1, b0, b1) == (a0p, a1p, b0p, b1p) and in_mask == mask and pruned & mask == pruned:
            return node_continue(a0, a1, b0, b1, residual_mask(mask, pruned), kind, cut, stack)
        return None
    if top[0] == "pair" and record[0] == "pair":
        _, a1, b0, b1, mask, a_pos, b_pos = top
        _, a_posp, b_posp, maskp = record
        if (a_pos, b_pos, mask) == (a_posp, b_posp, maskp):
            return advance_pair(a1, b0, b1, mask, a_pos, b_pos, stack)
        return None
    return None


def replay(obligation: Obligation, boundaries: list[int]) -> list[list]:
    """The state before each chunk start in ``boundaries`` (sorted, starting at 0) and the
    final state; every transition must succeed structurally."""
    state = [("node", 0, obligation.n, 0, obligation.m, 511)]
    states = []
    next_boundary = 0
    pair_index = 0
    current_node = None  # the id of the node whose pairs are being emitted
    node_index = 0
    for index, record in enumerate(obligation.records):
        if next_boundary < len(boundaries) and index == boundaries[next_boundary]:
            states.append(list(state))
            next_boundary += 1
        if record[0] == "node":
            current_node = obligation.node_ids[node_index]
            node_index += 1
        else:
            if obligation.pair_nodes[pair_index] != current_node:
                raise SystemExit(f"{obligation.name}: pair record {pair_index} names node "
                                 f"{obligation.pair_nodes[pair_index]}, expected {current_node}")
            pair_index += 1
        state = step_one(state, record)
        if state is None:
            raise SystemExit(f"{obligation.name}: structural replay fails at record {index}: {record}")
    if state:
        raise SystemExit(f"{obligation.name}: {len(state)} obligations remain after the last record")
    states.append([])
    return states


# ----------------------------------------------------------------------------
# Boxes (untrusted; mirrors SafetyData.siteBox / NodeBox.union / rangeBox)


def floor_div(a: int, b: int) -> int:
    return a // b


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def site_box(site: tuple) -> tuple[int, int, int, int, int]:
    s_num, s_den, t_num, t_den, r_num, r_den = site
    return (floor_div(DYADIC * s_num, s_den), ceil_div(DYADIC * s_num, s_den),
            floor_div(DYADIC * t_num, t_den), ceil_div(DYADIC * t_num, t_den),
            ceil_div(DYADIC * r_num, r_den))


def range_box(boxes: list[tuple], perm: list[int], lo: int, hi: int) -> tuple[int, int, int, int, int]:
    members = [boxes[perm[p]] for p in range(lo, hi)]
    return (min(b[0] for b in members), max(b[1] for b in members),
            min(b[2] for b in members), max(b[3] for b in members),
            max(b[4] for b in members))


# ----------------------------------------------------------------------------
# Lean text


def lean_int(value: int) -> str:
    return f"({value})" if value < 0 else str(value)


def wrap_items(items: list[str], indent: int, open_text: str, close_text: str,
               limit: int = MAX_LINE) -> str:
    """Lay out ``open_text item, item, ... close_text`` in lines of at most ``limit`` columns."""
    lines = []
    current = " " * indent + open_text
    first_on_line = True
    for position, item in enumerate(items):
        piece = item + ("," if position + 1 < len(items) else close_text)
        candidate = current + ("" if first_on_line else " ") + piece
        if len(candidate) > limit and not first_on_line:
            lines.append(current)
            current = " " * (indent + 2) + piece
        else:
            current = candidate
        first_on_line = False
    if not items:
        current += close_text
    lines.append(current)
    return "\n".join(lines)


def wrap_words(words: list[str], indent: int) -> str:
    lines = []
    current = " " * indent
    for word in words:
        candidate = current + ("" if current.strip() == "" else " ") + word
        if len(candidate) > MAX_LINE and current.strip() != "":
            lines.append(current)
            current = " " * indent + word
        else:
            current = candidate
    lines.append(current)
    return "\n".join(lines)


def paren(text: str) -> str:
    stripped = text.lstrip(" ")
    indent = len(text) - len(stripped)
    if "\n" not in stripped and " " not in stripped:
        return text
    return " " * indent + "(" + stripped + ")"


def module_header(title: str, body: str) -> str:
    return f"/-!\n# {title}\n\n{body}\n{GENERATED}\n-/\n"


def options(rec_depth: int, async_off: bool = False) -> str:
    text = f"set_option autoImplicit false\nset_option maxRecDepth {rec_depth}\nset_option maxHeartbeats 0\n"
    if async_off:
        text += "set_option Elab.async false\n"
    return text


def subtree_text(values: list, lo: int, hi: int, bits: int, indent: int, leaf) -> str:
    """The depth-``bits`` tree over ordinals ``[lo, hi)`` (``hi - lo = 2 ^ bits``); ordinals at
    or beyond ``len(values)`` are ``empty``."""
    pad = " " * indent
    if lo >= len(values):
        return pad + ".empty"
    if bits == 0:
        return leaf(values[lo], indent)
    mid = lo + 2 ** (bits - 1)
    left = subtree_text(values, lo, mid, bits - 1, indent + 2, leaf)
    right = subtree_text(values, mid, hi, bits - 1, indent + 2, leaf)
    return f"{pad}.node\n{paren(left)}\n{paren(right)}"


def site_leaf(site: tuple, indent: int) -> str:
    return wrap_items([lean_int(v) for v in site], indent, ".leaf ⟨", "⟩", MAX_LINE - indent // 2 - 1)


def ordinal_leaf(value: int, indent: int) -> str:
    return " " * indent + f".leaf {value}"


def top_text(prefix: str, blocks: int, lo_block: int, bits: int, indent: int) -> str:
    pad = " " * indent
    if lo_block >= blocks:
        return pad + ".empty"
    if bits == 0:
        return pad + f"{prefix}_{lo_block:03d}"
    half = 2 ** (bits - 1)
    left = top_text(prefix, blocks, lo_block, bits - 1, indent + 2)
    right = top_text(prefix, blocks, lo_block + half, bits - 1, indent + 2)
    return f"{pad}.node\n{paren(left)}\n{paren(right)}"


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def family_depth(count: int) -> int:
    return max(SITE_BITS, math.ceil(math.log2(count)))


LEAF_RE = re.compile(r"⟨([^⟩]*)⟩")


def verify_routes_sites(out_dir: Path, role: str, table: list, depth: int) -> None:
    """The routes lane's site modules must hold exactly the table rows, in row order, in
    depth-12 blocks, with the family depth; abort otherwise."""
    data_dir = out_dir / "Data"
    blocks = math.ceil(len(table) / SITE_CHUNK)
    found = []
    for block in range(blocks):
        text = (data_dir / f"SitesRoutes{role}_{block:03d}.lean").read_text()
        for match in LEAF_RE.finditer(text):
            found.append(tuple(int(v.strip("() ")) for v in match.group(1).split(",")))
    if found != table:
        raise SystemExit(f"SitesRoutes{role}: leaves differ from {ROLES[role]}")
    top = (data_dir / f"SitesRoutes{role}.lean").read_text()
    if f"def routesDepth{role} : ℕ := {depth}\n" not in top:
        raise SystemExit(f"SitesRoutes{role}: depth is not {depth}")
    body = top[top.index(f"def routesSites{role} :"):]
    if len(re.findall(rf"routesSites{role}_\d{{3}}", body)) != blocks:
        raise SystemExit(f"SitesRoutes{role}: top tree does not reference {blocks} blocks")


def record_text(record: tuple) -> str:
    if record[0] == "node":
        return ".node " + " ".join(str(v) for v in record[1:])
    return ".pair " + " ".join(str(v) for v in record[1:])


def task_text(task: tuple) -> str:
    return f".{task[0]} " + " ".join(str(v) for v in task[1:])


def box_text(box: tuple) -> str:
    return "⟨" + ", ".join(lean_int(v) for v in box) + "⟩"


# ----------------------------------------------------------------------------
# Tree modules (sites, permutations, inverses)


class TreeEmitter:
    def __init__(self, out_dir: Path, rec_depth: int, source_lines: str):
        self.data_dir = out_dir / "Data"
        self.checks_dir = out_dir / "Checks"
        self.rec_depth = rec_depth
        self.source_lines = source_lines

    def emit_tree(self, file_prefix: str, name: str, type_name: str, values: list, leaf,
                  what: str, depth: int, source_note: str, import_module: str,
                  depth_name: str | None = None) -> int:
        """Blocks ``<file_prefix>_NNN.lean`` with ``<name>_NNN`` and the top module
        ``<file_prefix>.lean`` with ``<name>`` (and ``<depth_name>``); returns the block count."""
        blocks = math.ceil(len(values) / SITE_CHUNK)
        top_bits = depth - SITE_BITS
        if 2**top_bits < blocks:
            raise SystemExit(f"{name}: depth {depth} cannot address {blocks} blocks")
        for block in range(blocks):
            lo = block * SITE_CHUNK
            hi = min(lo + SITE_CHUNK, len(values))
            local = "n" if lo == 0 else f"(n - {lo})"
            doc = module_header(
                f"{what} block {block:03d}",
                f"Entries {lo} to {hi - 1} of {source_note} as a depth-{SITE_BITS} `{type_name}`:\n"
                f"`{name}_{block:03d}.get? {SITE_BITS} {local}` returns entry `n` for `{lo} ≤ n < {hi}`.\n"
                f"{self.source_lines}",
            )
            body = (
                f"import {import_module}\n\n{doc}\n{options(self.rec_depth)}\nnamespace Erdos188.UpperBound\n\n"
                f"/-- Entries {lo} to {hi - 1} of {source_note}. -/\n"
                f"def {name}_{block:03d} : {type_name} :=\n"
                f"{subtree_text(values, lo, lo + SITE_CHUNK, SITE_BITS, 2, leaf)}\n\n"
                "end Erdos188.UpperBound\n"
            )
            write(self.data_dir / f"{file_prefix}_{block:03d}.lean", body)
        imports = "\n".join(
            f"import Erdos188.UpperBound.Data.{file_prefix}_{block:03d}" for block in range(blocks))
        doc = module_header(
            f"{what} tree",
            f"The {len(values)} entries of {source_note} as one depth-{depth} `{type_name}`: the top\n"
            f"{top_bits} bits of an index select one of {2**top_bits} block slots, of which slots 0 to\n"
            f"{blocks - 1} hold `{name}_000` to `{name}_{blocks - 1:03d}` (each a depth-{SITE_BITS} tree\n"
            f"over {SITE_CHUNK} consecutive indexes) and the rest are `empty`, so\n"
            f"`{name}.get? {depth} n` returns entry `n` for `n < {len(values)}`.\n{self.source_lines}",
        )
        depth_def = ""
        if depth_name is not None:
            depth_def = (
                f"/-- The lookup depth of the {what.lower()} tree: the smallest depth with\n"
                f"`2 ^ depth ≥ {len(values)}`. -/\n"
                f"def {depth_name} : ℕ := {depth}\n\n"
            )
        body = (
            f"{imports}\n\n{doc}\nset_option autoImplicit false\n\nnamespace Erdos188.UpperBound\n\n{depth_def}"
            f"/-- All of {source_note}, indexed through `IndexTree.get?` at depth {depth}. -/\n"
            f"def {name} : {type_name} :=\n{top_text(name, blocks, 0, top_bits, 2)}\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(self.data_dir / f"{file_prefix}.lean", body)
        return blocks


# ----------------------------------------------------------------------------
# Generation


def perm_names(obligation: Obligation) -> dict[str, tuple[str, str]]:
    """(perm name, inv name) per side; shared when both sides are identical."""
    if obligation.perm["left"] == obligation.perm["right"]:
        shared = (f"perm{obligation.name}", f"inv{obligation.name}")
        return {"left": shared, "right": shared}
    return {side: (f"perm{obligation.name}{tag}", f"inv{obligation.name}{tag}")
            for side, tag in (("left", "L"), ("right", "R"))}


def family_names(obligation: Obligation) -> tuple[str, str]:
    if obligation.left == obligation.right and obligation.perm["left"] == obligation.perm["right"]:
        return (f"fam{obligation.name}", f"fam{obligation.name}")
    return (f"fam{obligation.name}L", f"fam{obligation.name}R")


def plan_chunks(records: list[tuple], budget: int, node_cost: int, bit_cost: int, pair_cost: int,
                max_records: int) -> list[tuple[int, int]]:
    """``(lo, hi)`` per chunk under the memory cost model."""
    if type(max_records) is not int or max_records <= 0:
        raise SystemExit("max_records must be a positive integer")

    def cost(record):
        if record[0] == "node":
            return node_cost + bit_cost * bin(record[6]).count("1")
        return pair_cost
    chunks = []
    index = 0
    while index < len(records):
        total = 0
        end = index
        while end < len(records) and end - index < max_records:
            step = cost(records[end])
            if total + step > budget and end > index:
                break
            total += step
            end += 1
        chunks.append((index, end))
        index = end
    return chunks


class IntervalTree:
    """The laminar family of one side's node ranges with the claimed box of every interval."""

    def __init__(self, obligation: Obligation, side: str, boxes: list[tuple]):
        kind = 2 if side == "A" else 3
        count = obligation.n if side == "A" else obligation.m
        perm = obligation.perm["left" if side == "A" else "right"]
        self.cuts: dict[tuple[int, int], int] = {}
        seen = set()
        for record in obligation.records:
            if record[0] != "node":
                continue
            _, a0, a1, b0, b1, _, _, node_kind, cut = record
            lo, hi = (a0, a1) if side == "A" else (b0, b1)
            seen.add((lo, hi))
            if node_kind == kind:
                previous = self.cuts.setdefault((lo, hi), cut)
                if previous != cut:
                    raise SystemExit(f"{obligation.name} {side}: interval {(lo, hi)} split at {previous} and {cut}")
        self.root = (0, count)
        derived = set()
        stack = [self.root]
        while stack:
            interval = stack.pop()
            derived.add(interval)
            if interval in self.cuts:
                lo, hi = interval
                cut = self.cuts[interval]
                if not lo < cut < hi:
                    raise SystemExit(f"{obligation.name} {side}: cut {cut} outside {(lo, hi)}")
                stack += [(lo, cut), (cut, hi)]
        if not seen <= derived:
            raise SystemExit(f"{obligation.name} {side}: node ranges are not laminar")
        self.box: dict[tuple[int, int], tuple] = {}
        self.minimal_total: dict[tuple[int, int], int] = {}
        self.size: dict[tuple[int, int], int] = {}

        def fill(interval):
            lo, hi = interval
            if interval in self.cuts:
                cut = self.cuts[interval]
                left, right = fill((lo, cut)), fill((cut, hi))
                self.box[interval] = (min(left[0], right[0]), max(left[1], right[1]),
                                      min(left[2], right[2]), max(left[3], right[3]), max(left[4], right[4]))
                self.minimal_total[interval] = self.minimal_total[(lo, cut)] + self.minimal_total[(cut, hi)]
                self.size[interval] = 1 + self.size[(lo, cut)] + self.size[(cut, hi)]
            else:
                self.box[interval] = range_box(boxes, perm, lo, hi)
                self.minimal_total[interval] = hi - lo
                self.size[interval] = 1
            return self.box[interval]

        sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
        fill(self.root)
        self.intervals = len(self.box)
        self.minimal = sum(1 for interval in self.box if interval not in self.cuts)

    def text(self, interval: tuple[int, int], indent: int, stop: dict) -> str:
        """The `BoxTree` literal of ``interval``; subtrees in ``stop`` are referenced by name."""
        pad = " " * indent
        if interval in stop:
            return pad + stop[interval]
        lo, hi = interval
        if interval not in self.cuts:
            return f"{pad}.leaf {lo} {hi} {box_text(self.box[interval])}"
        cut = self.cuts[interval]
        left = self.text((lo, cut), indent + 2, stop)
        right = self.text((cut, hi), indent + 2, stop)
        return f"{pad}.split {lo} {cut} {hi} {box_text(self.box[interval])}\n{paren(left)}\n{paren(right)}"

    def plan(self, budget: int) -> list[tuple[int, int]]:
        """The subtrees, in preorder, whose minimal intervals total at most ``budget``."""
        blocks = []

        def visit(interval):
            if self.minimal_total[interval] <= budget or interval not in self.cuts:
                blocks.append(interval)
                return
            lo, hi = interval
            cut = self.cuts[interval]
            visit((lo, cut))
            visit((cut, hi))

        visit(self.root)
        return blocks


def generate(args: argparse.Namespace) -> None:
    validate_generation_args("safety", args)
    subject = resolve_subject()
    counts = {role.name: role.raw_rows for role in subject.roles}
    roots = {"raw": DATA_DIR.absolute(), "export": args.cert_dir.absolute()}
    certificate = read_input(subject, "certificate", roots)
    cert_sha = certificate.sha256
    manifest_source = read_input(subject, "export_manifest", roots)
    manifest_sha = manifest_source.sha256
    manifest = read_manifest(manifest_source.data)
    if manifest["stream"]["sha256"] != cert_sha:
        raise SystemExit("manifest does not describe this certificate")
    records = manifest["stream"]["records"]
    table_sha = {}
    table_sources = {}
    for role, file_name in ROLES.items():
        source = read_input(subject, role, roots)
        table_sources[role] = source
        table_sha[role] = source.input.pin.sha256
        pinned = manifest["input_pins"][file_name]["sha256"]
        if table_sha[role] != pinned:
            raise SystemExit(f"{file_name}: SHA-256 {table_sha[role]} differs from the manifest pin {pinned}")
    print(f"certificate sha256 {cert_sha} ({len(certificate.data)} bytes, {records} records)")
    print(f"manifest sha256 {manifest_sha}")
    for role, file_name in ROLES.items():
        print(f"{file_name} sha256 {table_sha[role]}")

    sites = {
        role: read_sites(table_sources[role].data, DATA_DIR / file_name)
        for role, file_name in ROLES.items()
    }
    del table_sources, source
    for role, table in sites.items():
        if len(table) != counts[role]:
            raise SystemExit(f"{ROLES[role]}: {len(table)} rows, expected {counts[role]}")
    obligations = read_certificate(certificate.data, records)
    del certificate
    for name, left, right in OBLIGATIONS:
        obligation = obligations[name]
        if obligation.n != len(sites[left]) or obligation.m != len(sites[right]):
            raise SystemExit(f"{name}: family counts differ from the tables")
        print(f"{name}: {left}x{right} n={obligation.n} m={obligation.m} nodes={len(obligation.node_ids)} "
              f"pairs={len(obligation.pair_nodes)} shared perm={obligation.perm['left'] == obligation.perm['right']}")

    source_lines = (
        f"Certificate SHA-256: `{cert_sha}`.\n"
        + "\n".join(f"`{ROLES[role]}` SHA-256: `{table_sha[role]}`." for role in ROLES)
    )
    out = TreeEmitter(args.out_dir, args.max_rec_depth, source_lines)
    depths = {role: family_depth(len(table)) for role, table in sites.items()}
    role_names = {"S": "carrier", "B": "base", "P": "plug", "M": "micro-representative"}

    for role in ROLES:
        verify_routes_sites(args.out_dir, role, sites[role], depths[role])
        print(f"routesSites{role}: {math.ceil(len(sites[role]) / SITE_CHUNK)} blocks verified, depth {depths[role]}")

    if args.stage in ("sites", "all"):
        emitted = set()
        for name, left, right in OBLIGATIONS:
            obligation = obligations[name]
            names = perm_names(obligation)
            for side, role, count in (("left", left, obligation.n), ("right", right, obligation.m)):
                perm_name, inv_name = names[side]
                if perm_name in emitted:
                    continue
                emitted.add(perm_name)
                sides = "both sides" if names["left"] == names["right"] else f"the {side} side"
                out.emit_tree(
                    perm_name[0].upper() + perm_name[1:], perm_name, "OrdTree", obligation.perm[side],
                    ordinal_leaf, f"{name} {sides} permutation", depths[role],
                    f"the {name} {sides} position-to-ordinal permutation of role {role} ({count} positions)",
                    "Erdos188.UpperBound.SafetyData")
                out.emit_tree(
                    inv_name[0].upper() + inv_name[1:], inv_name, "OrdTree", obligation.inv[side],
                    ordinal_leaf, f"{name} {sides} inverse permutation", depths[role],
                    f"the ordinal-to-position inverse of `{perm_name}` ({count} ordinals)",
                    "Erdos188.UpperBound.SafetyData")
        # families, one module per obligation
        for name, left, right in OBLIGATIONS:
            obligation = obligations[name]
            names = perm_names(obligation)
            fams = family_names(obligation)
            imports = sorted({f"Erdos188.UpperBound.Data.SitesRoutes{left}",
                              f"Erdos188.UpperBound.Data.SitesRoutes{right}"} |
                             {f"Erdos188.UpperBound.Data.{names[s][0][0].upper()}{names[s][0][1:]}"
                              for s in ("left", "right")})
            defs = []
            for side, role, count, fam in (("left", left, obligation.n, fams[0]),
                                           ("right", right, obligation.m, fams[1])):
                if side == "right" and fams[0] == fams[1]:
                    continue
                which = "both sides" if fams[0] == fams[1] else f"the {side} side"
                defs.append(
                    f"/-- {which.capitalize()} of {name}: the role-{role} table with its {name} permutation. -/\n"
                    f"def {fam} : WireFamily := ⟨routesSites{role}, routesDepth{role}, {names[side][0]}, {count}⟩\n")
            doc = module_header(
                f"{name} wire families",
                f"The `WireFamily` value of each side of {name}: the role's site tree and depth from the\n"
                "route modules, the obligation's position permutation, and the family count.\n" + source_lines)
            body = ("\n".join(f"import {m}" for m in imports) + f"\n\n{doc}\nset_option autoImplicit false\n\n"
                    "namespace Erdos188.UpperBound\n\n" + "\n".join(defs) + "\nend Erdos188.UpperBound\n")
            write(out.data_dir / f"Families{name}.lean", body)

    if args.stage in ("records", "all"):
        generate_records(args, out, obligations, sites, depths, source_lines, cert_sha)


def generate_records(args, out: TreeEmitter, obligations, sites, depths, source_lines, cert_sha) -> None:
    per_obligation = {}
    for name, left, right in OBLIGATIONS:
        if args.only and name not in args.only:
            continue
        obligation = obligations[name]
        chunks = plan_chunks(obligation.records, args.chunk_budget, args.node_cost, args.bit_cost,
                             args.pair_cost, args.max_records)
        states = replay(obligation, [lo for lo, _ in chunks])
        assert len(states) == len(chunks) + 1
        print(f"{name}: {len(chunks)} record chunks; max boundary state {max(len(s) for s in states)} tasks")
        per_obligation[name] = (chunks, states)
        fams = family_names(obligation)
        boxes = {"A": [site_box(w) for w in sites[left]], "B": [site_box(w) for w in sites[right]]}
        # box tables
        for side, fam in (("A", fams[0]), ("B", fams[1])):
            tree = IntervalTree(obligation, side, boxes[side])
            blocks = tree.plan(args.table_budget)
            table = f"boxTable{name}{side}"
            print(f"{name} {side}: {tree.intervals} intervals, {tree.minimal} minimal, "
                  f"{len(blocks)} table blocks (budget {args.table_budget})")
            stop = {interval: f"{table}_{index:03d}" for index, interval in enumerate(blocks)}
            for index, interval in enumerate(blocks):
                doc = module_header(
                    f"{name} side {side} box table block {index:03d}",
                    f"The node ranges of the {name} section inside positions `[{interval[0]}, {interval[1]})` of\n"
                    f"`{fam}` with the claimed box of each ({tree.size[interval]} intervals, minimal intervals\n"
                    f"totaling {tree.minimal_total[interval]} positions); the kernel checks the claims in\n"
                    f"`Checks/BoxTable{name}{side}_{index // args.table_group:03d}.lean`.\n{source_lines}")
                body = (f"import Erdos188.UpperBound.SafetyDataExtra\n\n{doc}\n{options(args.max_rec_depth)}\n"
                        f"namespace Erdos188.UpperBound\n\n/-- Block {index:03d} of the {name} side-{side} box table. -/\n"
                        f"def {table}_{index:03d} : BoxTree :=\n{tree.text(interval, 2, {})}\n\nend Erdos188.UpperBound\n")
                write(out.data_dir / f"BoxTable{name}{side}_{index:03d}.lean", body)
            imports = "\n".join(f"import Erdos188.UpperBound.Data.BoxTable{name}{side}_{i:03d}" for i in range(len(blocks)))
            doc = module_header(
                f"{name} side {side} box table",
                f"The laminar tree of the {len(tree.box)} node ranges of the {name} section on `{fam}` with the\n"
                f"claimed range box of every interval: {len(blocks)} blocks under a top tree of splits.\n"
                f"{source_lines}")
            body = (f"{imports}\n\n{doc}\nset_option autoImplicit false\nset_option maxRecDepth {args.max_rec_depth}\n\n"
                    f"namespace Erdos188.UpperBound\n\n/-- The {name} side-{side} box table. -/\n"
                    f"def {table} : BoxTree :=\n{tree.text(tree.root, 2, stop)}\n\nend Erdos188.UpperBound\n")
            write(out.data_dir / f"BoxTable{name}{side}.lean", body)
            # block checks, grouped
            groups = math.ceil(len(blocks) / args.table_group)
            for group in range(groups):
                members = range(group * args.table_group, min((group + 1) * args.table_group, len(blocks)))
                theorems = [
                    f"/-- Block {index:03d} of the {name} side-{side} box table is accepted. -/\n"
                    f"theorem boxCheck{name}{side}_{index:03d} : {table}_{index:03d}.check {fam} = true := by\n"
                    "  decide +kernel\n" for index in members]
                doc = module_header(
                    f"{name} side {side} box table checks {group:03d}",
                    f"Kernel checks of blocks {members.start:03d} to {members.stop - 1:03d} of `{table}`.\n{source_lines}")
                body = (f"import Erdos188.UpperBound.SafetyDataExtra\nimport Erdos188.UpperBound.Data.Families{name}\n"
                        + "\n".join(f"import Erdos188.UpperBound.Data.BoxTable{name}{side}_{i:03d}" for i in members)
                        + f"\n\n{doc}\n{options(args.max_rec_depth, async_off=True)}\nnamespace Erdos188.UpperBound\n\n"
                        + "\n".join(theorems) + "\nend Erdos188.UpperBound\n")
                write(out.checks_dir / f"BoxTable{name}{side}_{group:03d}.lean", body)

            def combine(interval, indent):
                pad = " " * indent
                if interval in stop:
                    return pad + f"boxCheck{name}{side}_{blocks.index(interval):03d}"
                lo, hi = interval
                cut = tree.cuts[interval]
                return (f"{pad}(BoxTree.check_split_of (by decide +kernel)\n"
                        f"{combine((lo, cut), indent + 2)}\n{combine((cut, hi), indent + 2)})")

            doc = module_header(
                f"{name} side {side} box table check",
                f"Every claimed box of `{table}` is the recomputed range box of its interval, combined from\n"
                f"the {len(blocks)} block checks along the top tree.\n{source_lines}")
            body = ("\n".join(f"import Erdos188.UpperBound.Checks.BoxTable{name}{side}_{g:03d}" for g in range(groups))
                    + f"\nimport Erdos188.UpperBound.Data.BoxTable{name}{side}\n\n{doc}\nset_option autoImplicit false\n"
                    f"set_option maxRecDepth {args.max_rec_depth}\n\nnamespace Erdos188.UpperBound\n\n"
                    f"/-- The {name} side-{side} box table is accepted. -/\n"
                    f"theorem boxCheck{name}{side} : {table}.check {fam} = true :=\n{combine(tree.root, 2)}\n\n"
                    "end Erdos188.UpperBound\n")
            write(out.checks_dir / f"BoxTable{name}{side}.lean", body)
        # records
        emitted_chunks = chunks if args.max_chunks is None else chunks[:args.max_chunks]
        for index, (lo, hi) in enumerate(emitted_chunks):
            doc = module_header(
                f"{name} records chunk {index:03d}",
                f"Records {lo} to {hi - 1} of the {name} safety section (node and pair records of the\n"
                f"certificate in stream order, without the obligation and node identifiers).\n{source_lines}")
            items = [record_text(r) for r in obligation.records[lo:hi]]
            lines = [("  [" if i == 0 else "    ") + item + ("," if i + 1 < len(items) else "]")
                     for i, item in enumerate(items)]
            body = (f"import Erdos188.UpperBound.SafetyData\n\n{doc}\n{options(args.max_rec_depth)}\n"
                    f"namespace Erdos188.UpperBound\n\n/-- Records {lo} to {hi - 1} of the {name} section. -/\n"
                    f"def records{name}_{index:03d} : List SafetyRecord :=\n" + "\n".join(lines)
                    + "\n\nend Erdos188.UpperBound\n")
            write(out.data_dir / f"Records{name}_{index:03d}.lean", body)
        # states
        defs = []
        for index, state in enumerate(states):
            if index == 0:
                note = f"The state before chunk 000: the root product `[0, {obligation.n}) × [0, {obligation.m})`."
            elif index == len(chunks):
                note = f"The state after chunk {len(chunks) - 1:03d}: no pending obligation."
            else:
                note = f"The state before chunk {index:03d}, top first ({len(state)} tasks)."
            literal = wrap_items([task_text(t) for t in state], 2, "[", "]")
            defs.append(f"/-- {note} -/\ndef safetyState{name}_{index:03d} : SafetyState :=\n{literal}\n")
        doc = module_header(
            f"{name} replay states",
            f"The pending-obligation stack before each of the {len(chunks)} record chunks of the {name}\n"
            "section and the empty stack after the last one, computed by an untrusted Python replay of\n"
            "the structural discipline of `safetyStepOne`; the chunk theorems under `Checks/` verify\n"
            f"every transition in the kernel.\n{source_lines}")
        body = (f"import Erdos188.UpperBound.SafetyData\n\n{doc}\nset_option autoImplicit false\n\n"
                "namespace Erdos188.UpperBound\n\n" + "\n".join(defs) + "\nend Erdos188.UpperBound\n")
        write(out.data_dir / f"SafetyStates{name}.lean", body)
        # chunk checks
        for index, (lo, hi) in enumerate(emitted_chunks):
            state_lo = f"safetyState{name}_{index:03d}"
            state_hi = f"safetyState{name}_{index + 1:03d}"
            records_name = f"records{name}_{index:03d}"
            doc = module_header(
                f"{name} replay check {index:03d}",
                f"Kernel fast replay of records {lo} to {hi - 1} of the {name} section from `{state_lo}` to\n"
                f"`{state_hi}`, with node boxes from `boxTable{name}A` and `boxTable{name}B`.\n{source_lines}")
            body = (f"import Erdos188.UpperBound.SafetyDataExtra\nimport Erdos188.UpperBound.Data.Families{name}\n"
                    f"import Erdos188.UpperBound.Data.BoxTable{name}A\nimport Erdos188.UpperBound.Data.BoxTable{name}B\n"
                    f"import Erdos188.UpperBound.Data.SafetyStates{name}\n"
                    f"import Erdos188.UpperBound.Data.Records{name}_{index:03d}\n\n{doc}\n"
                    f"{options(args.max_rec_depth, async_off=True)}\nnamespace Erdos188.UpperBound\n\n"
                    f"/-- Chunk {index:03d} of {name} replays from `{state_lo}` to `{state_hi}`. -/\n"
                    f"theorem safetyStep{name}_{index:03d} :\n"
                    f"    safetyStepFast {fams[0]} {fams[1]} boxTable{name}A boxTable{name}B {state_lo} {records_name} =\n"
                    f"      some {state_hi} := by\n  decide +kernel\n\nend Erdos188.UpperBound\n")
            write(out.checks_dir / f"SafetyStep{name}_{index:03d}.lean", body)

    if args.max_chunks is not None or args.only:
        print("partial emission: SafetyFamilies and SafetyAll not written")
        return
    generate_family_checks(args, out, obligations, sites, depths, source_lines)
    generate_all(args, out, obligations, per_obligation, sites, depths, source_lines)


def generate_family_checks(args, out: TreeEmitter, obligations, sites, depths, source_lines) -> None:
    """Per-chunk surjectivity checks per permutation side, combined in
    `Checks/SafetyFamilies.lean` (shape and validity come from `Checks/RoutesValid<R>.lean`)."""
    combos = []
    imports = []
    emitted = set()
    for name, left, right in OBLIGATIONS:
        obligation = obligations[name]
        names = perm_names(obligation)
        for side, role, count in (("left", left, obligation.n), ("right", right, obligation.m)):
            perm_name, inv_name = names[side]
            if perm_name in emitted:
                continue
            emitted.add(perm_name)
            tag = perm_name[4:]
            chunks = math.ceil(count / SITE_CHUNK)
            groups = math.ceil(chunks / args.table_group)
            for group in range(groups):
                members = range(group * args.table_group, min((group + 1) * args.table_group, chunks))
                theorems = []
                for chunk in members:
                    lo = chunk * SITE_CHUNK
                    length = min(SITE_CHUNK, count - lo)
                    theorems.append(
                        f"/-- Ordinals `[{lo}, {lo + length})` are hit by positions below {count} through `{inv_name}`. -/\n"
                        f"theorem surj{tag}_{chunk:03d} :\n"
                        f"    surjCheck {perm_name} {inv_name} routesDepth{role} {count} {lo} {length} = true := by\n"
                        "  decide +kernel\n")
                doc = module_header(
                    f"{tag} surjectivity checks {group:03d}",
                    f"Ordinal chunks {members.start:03d} to {members.stop - 1:03d} of the surjectivity check of\n"
                    f"`{perm_name}` through `{inv_name}` (at most {SITE_CHUNK} ordinals each).\n{source_lines}")
                body = (f"import Erdos188.UpperBound.SafetyDataExtra\n"
                        f"import Erdos188.UpperBound.Data.{perm_name[0].upper()}{perm_name[1:]}\n"
                        f"import Erdos188.UpperBound.Data.{inv_name[0].upper()}{inv_name[1:]}\n"
                        f"import Erdos188.UpperBound.Data.SitesRoutes{role}\n\n{doc}\n"
                        f"{options(args.max_rec_depth, async_off=True)}\nnamespace Erdos188.UpperBound\n\n"
                        + "\n".join(theorems) + "\nend Erdos188.UpperBound\n")
                write(out.checks_dir / f"SafetySurj{tag}_{group:03d}.lean", body)
            imports += [f"Erdos188.UpperBound.Checks.SafetySurj{tag}_{g:03d}" for g in range(groups)]
            chain = f"surj{tag}_000"
            for chunk in range(1, chunks):
                total = min((chunk + 1) * SITE_CHUNK, count)
                chain = (f"(surjCheck_chainAt {total} {chain} surj{tag}_{chunk:03d} (by decide +kernel)\n"
                         f"    (by decide +kernel))")
            combos.append(
                f"/-- Every ordinal below {count} is hit by a position below {count} under `{perm_name}`. -/\n"
                f"theorem surj{tag} : surjCheck {perm_name} {inv_name} routesDepth{role} {count} 0 {count} = true :=\n"
                f"  {chain}\n")
    doc = module_header(
        "Safety permutation checks",
        "The surjectivity of every obligation's position permutation onto its family's ordinals,\n"
        "combined from the per-chunk kernel checks.\n" + source_lines)
    body = ("import Erdos188.UpperBound.SafetyDataChain\n" + "\n".join(f"import {m}" for m in imports)
            + f"\n\n{doc}\n{options(args.max_rec_depth)}\nnamespace Erdos188.UpperBound\n\n"
            + "\n".join(combos) + "\nend Erdos188.UpperBound\n")
    write(out.checks_dir / "SafetyFamilies.lean", body)


def generate_all(args, out: TreeEmitter, obligations, per_obligation, sites, depths, source_lines) -> None:
    imports = ["Erdos188.UpperBound.Checks.SafetyFamilies"] + \
        [f"Erdos188.UpperBound.Checks.RoutesValid{role}" for role in ROLES]
    sections = []
    finals = []
    for name, left, right in OBLIGATIONS:
        obligation = obligations[name]
        chunks, states = per_obligation[name]
        fams = family_names(obligation)
        names = perm_names(obligation)
        imports += [f"Erdos188.UpperBound.Checks.BoxTable{name}A", f"Erdos188.UpperBound.Checks.BoxTable{name}B"]
        imports += [f"Erdos188.UpperBound.Checks.SafetyStep{name}_{i:03d}" for i in range(len(chunks))]
        all_text = wrap_words(
            [f"records{name}_{i:03d}" + (" ++" if i + 1 < len(chunks) else "") for i in range(len(chunks))], 2)
        # left-nested chain, matching the left-associative `++` of the concatenation:
        # chain_k : safetyStepFast fam fam' tA tB state_0 ((records_0 ++ ...) ++ records_k) = some state_{k+1}
        chain_lines = []
        previous = f"safetyStep{name}_000"
        for index in range(1, len(chunks)):
            chain_lines.append(f"  have chain_{index:03d} := safetyStepFast_chain {previous} safetyStep{name}_{index:03d}")
            previous = f"chain_{index:03d}"
        tag_l = names["left"][0][4:]
        tag_r = names["right"][0][4:]
        sections.append(
            f"/-- Every record of the {name} section in order: the {len(chunks)} chunks concatenated. -/\n"
            f"def records{name}All : List SafetyRecord :=\n{all_text}\n\n"
            f"/-- The whole {name} section fast-replays from the root product to no pending obligation. -/\n"
            f"theorem safetyStreamFast_{name} :\n"
            f"    safetyStepFast {fams[0]} {fams[1]} boxTable{name}A boxTable{name}B\n"
            f"      [.node 0 {obligation.n} 0 {obligation.m} 511] records{name}All = some [] := by\n"
            + "\n".join(chain_lines) + f"\n  exact {previous}\n\n"
            f"/-- The whole {name} section replays from the root product to no pending obligation. -/\n"
            f"theorem safetyStream_{name} :\n"
            f"    safetyStep {fams[0]} {fams[1]} [.node 0 {obligation.n} 0 {obligation.m} 511] records{name}All =\n"
            f"      some [] :=\n"
            f"  safetyStepFast_sound {fams[0]} {fams[1]} boxTable{name}A boxTable{name}B boxCheck{name}A\n"
            f"    boxCheck{name}B records{name}All _ _ safetyStreamFast_{name}\n")
        if fams[0] == fams[1]:
            role = left
            finals.append(
                f"/-- The periodic union of the {ROLES[role][:-4]} sites (role {role}) is unit independent. -/\n"
                f"theorem unitIndependent_{role}_real : UnitIndependent (U (wireSet routesSites{role}.toList)) :=\n"
                f"  unitIndependent_U_of_safetyPieces {fams[0]} records{name}All routesSites{role}_shape\n"
                f"    (surjCheck_sound_all surj{tag_l}) routesSites{role}_valid safetyStream_{name}\n")
        else:
            finals.append(
                f"/-- The periodic unions of the {ROLES[left][:-4]} sites (role {left}) and the\n"
                f"{ROLES[right][:-4]} sites (role {right}) are cross-safe. -/\n"
                f"theorem crossSafe_{left}{right}_real :\n"
                f"    CrossSafe (U (wireSet routesSites{left}.toList)) (U (wireSet routesSites{right}.toList)) :=\n"
                f"  crossSafe_U_of_safetyPieces {fams[0]} {fams[1]} records{name}All routesSites{left}_shape\n"
                f"    routesSites{right}_shape (surjCheck_sound_all surj{tag_l}) (surjCheck_sound_all surj{tag_r})\n"
                f"    routesSites{left}_valid routesSites{right}_valid safetyStream_{name}\n")
    doc = (
        "/-!\n"
        "# Safety certificate chained replay\n"
        "\n"
        "The chunk theorems of each obligation chained through `safetyStepFast_chain`\n"
        "into the fast replay of the whole section, its conversion to a run of the\n"
        "trusted checker `safetyStep` by `safetyStepFast_sound`, and the three final\n"
        "theorems: unit independence of the carrier and base unions and cross-safety of\n"
        "the micro-representative and plug unions. The conversion is one-directional:\n"
        "an accepted fast replay yields an accepted trusted run, and nothing is claimed\n"
        "about the converse. The four role tables are exact assets of the 42-term\n"
        "construction under\n"
        "`data/k42/`.\n"
        "The certificate is the documented output of `export_certificate.py` over those\n"
        "tables; it is identified here by its SHA-256 and is not retained in the\n"
        "repository, since the generated `Data/` modules carry every replayed record.\n"
        + source_lines
        + "\n"
        "Generated by `gen_safety_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand.\n"
        "No claim identity is asserted in this module.\n"
        "-/\n"
    )
    body = ("\n".join(f"import {m}" for m in imports) + f"\n\n{doc}\n{options(args.max_rec_depth)}\n"
            "namespace Erdos188.UpperBound\n\n" + "\n".join(sections) + "\n" + "\n".join(finals)
            + "\nend Erdos188.UpperBound\n")
    write(out.checks_dir / "SafetyAll.lean", body)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--cert-dir", type=Path, required=True,
                        help="directory holding the exported certificate.ndjson and manifest.json")
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="fresh regeneration root holding the routes lane's output; never the "
                             "committed Erdos188/UpperBound")
    parser.add_argument("--stage", choices=["sites", "records", "all"], default="all")
    parser.add_argument("--chunk-budget", type=int, default=40000,
                        help="cost units (about 0.1 MB each) per chunk theorem")
    parser.add_argument("--node-cost", type=int, default=3, help="cost units per node record")
    parser.add_argument("--bit-cost", type=int, default=5, help="cost units per pruned bit of a node record")
    parser.add_argument("--pair-cost", type=int, default=4, help="cost units per pair record")
    parser.add_argument("--max-records", type=int, default=4096, help="records per chunk at most")
    parser.add_argument("--table-budget", type=int, default=6000,
                        help="minimal-interval positions per box table block theorem")
    parser.add_argument("--table-group", type=int, default=8, help="box table block theorems per module")
    parser.add_argument("--max-rec-depth", type=int, default=100000)
    parser.add_argument("--only", nargs="*", choices=[name for name, _, _ in OBLIGATIONS],
                        help="emit records and checks for these obligations only (measurement mode)")
    parser.add_argument("--max-chunks", type=int, default=None,
                        help="emit only the first chunks of each obligation (measurement mode)")
    args = parser.parse_args()
    try:
        generate(args)
    except GenerationRefused as error:
        raise SystemExit(str(error)) from None


if __name__ == "__main__":
    main()
