#!/usr/bin/env python3
"""Generate the Lean data modules for the K42 route certificate.

Reads the four role tables (``carriers.tsv`` = S, ``base.tsv`` = B, ``plugs.tsv`` = P,
``micro_representatives.tsv`` = M; one site per row, ``s<TAB>t<TAB>r`` with each field a
canonical integer or reduced ``num/den``) and the ``route`` records of the untrusted
certificate stream ``certificate.ndjson``, verifies the role tables' gold SHA-256 identities, the
strict rational-lexicographic row order that defines the ordinals, and the wire contract
of the route blocks, and writes, under ``<out>/Data`` and ``<out>/Checks``:

* ``SitesRoutes<R>_NNN.lean``: one balanced ``IndexTree SiteWire`` per block of at most
  ``--site-chunk`` consecutive ordinals (a power of two) of role ``R``;
* ``SitesRoutes<R>.lean``: ``routesSites<R>`` combining the blocks and ``routesDepth<R>``;
* ``Routes<Block>_NNN.lean``: one ``List RouteRecord`` literal per block of at most
  ``--record-chunk`` consecutive records of one route block (``O4B``, ``O6B``, ``O6S``,
  ``O6P``, ``O5M``), with the boundary counters in the module docstring;
* ``Checks/Routes<Block>_NNN.lean``: one ``decide +kernel`` step theorem per chunk;
* ``Checks/RoutesValid<R>_NNN.lean``: the ``decide +kernel`` validity and shape theorems of one
  site block, and ``Checks/RoutesValid<R>.lean``: their combination along the top tree;
* ``Checks/RoutesAll.lean``: the chained replays, the passing obligation checks, and the
  five final theorems.

Depth convention (see ``IndexTree.get?``): ordinal ``n`` is looked up by reading its binary
digits from bit ``depth - 1`` down to bit ``0``, ``0`` for the left child and ``1`` for the
right child. A block of ``2^b`` ordinals starting at ``m * 2^b`` is a depth-``b`` tree, and
the top tree spends the remaining ``depth - b`` bits selecting the block, so
``routesSites<R>.get? routesDepth<R> n`` finds ordinal ``n`` of the table.

Lift convention (see ``export_certificate.md``): a wire lift ``n`` places the target at
``a' + 59 n``, and ``shiftSite q' l`` has center ``a' - 59 l``; the Lean checkers negate the
wire lift themselves, so the records carry the wire values ``ns nt`` verbatim.

The four gold role tables are authenticated against ``data/k42/manifest.json`` before
parsing; the certificate is read by path, and its observed digest is recorded in the module
headers. Text decoding retains the original default-encoding/universal-newline semantics.
"""

from __future__ import annotations

import argparse
import io
import json
import math
import re
from fractions import Fraction
from pathlib import Path

if __package__:
    from .generation_profile import validate_generation_args
    from .generation_subject import GenerationRefused, read_input, resolve_subject
else:
    from generation_profile import validate_generation_args
    from generation_subject import GenerationRefused, read_input, resolve_subject

DEFAULT_DATA_DIR = Path(__file__).resolve().parent.parent.parent / "data" / "k42"
MAX_LINE = 100
FIELD_RE = re.compile(r"(-?\d+)(?:/(\d+))?")

ROLE_FILES = {"S": "carriers.tsv", "B": "base.tsv", "P": "plugs.tsv", "M": "micro_representatives.tsv"}
ROLE_ORDER = ["B", "S", "P", "M"]

# The route blocks in stream order: name, obligation, source role, transform, the target role
# to `tgtRole` map for identity records (the target of a rho record is the source table), and
# the Lean checker with its target tables (`None` = the empty tree).
BLOCKS = [
    {"name": "O4B", "obligation": "O4", "source": "B", "transform": "identity",
     "targets": {"S": False, "P": True}, "checker": "contain", "tgtA": "S", "tgtB": "P"},
    {"name": "O6B", "obligation": "O6", "source": "B", "transform": "rho",
     "targets": {"B": None}, "checker": "rotation"},
    {"name": "O6S", "obligation": "O6", "source": "S", "transform": "rho",
     "targets": {"S": None}, "checker": "rotation"},
    {"name": "O6P", "obligation": "O6", "source": "P", "transform": "rho",
     "targets": {"P": None}, "checker": "rotation"},
    {"name": "O5M", "obligation": "O5", "source": "M", "transform": "identity",
     "targets": {"S": False}, "checker": "contain", "tgtA": "S", "tgtB": None},
]

# ----------------------------------------------------------------------------
# Input


def parse_fraction(text: str) -> tuple[int, int]:
    match = FIELD_RE.fullmatch(text)
    if match is None:
        raise SystemExit(f"bad site field {text!r}")
    num = int(match.group(1))
    den = int(match.group(2)) if match.group(2) is not None else 1
    if den <= 0:
        raise SystemExit(f"non-positive denominator in {text!r}")
    if math.gcd(num, den) != 1 or (match.group(2) is not None and den == 1):
        raise SystemExit(f"non-canonical field {text!r}")
    return num, den


def parse_sites(data: bytes, path: Path) -> list[tuple[int, int, int, int, int, int]]:
    """The rows as six-integer wires, after checking the grammar, the domain, and the strict
    rational-lexicographic order that makes the row index the ordinal."""
    sites = []
    previous = None
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.endswith("\n"):
                raise SystemExit(f"{path}:{line_number}: missing newline")
            parts = line[:-1].split("\t")
            if len(parts) != 3:
                raise SystemExit(f"{path}:{line_number}: expected three fields, got {len(parts)}")
            (s_num, s_den), (t_num, t_den), (r_num, r_den) = (parse_fraction(p) for p in parts)
            key = (Fraction(s_num, s_den), Fraction(t_num, t_den), Fraction(r_num, r_den))
            if not (0 <= key[0] < 59 and 0 <= key[1] < 59 and 0 < key[2] < Fraction(1, 2)):
                raise SystemExit(f"{path}:{line_number}: site outside the domain")
            if previous is not None and not previous < key:
                raise SystemExit(f"{path}:{line_number}: rows are not strictly increasing")
            previous = key
            sites.append((s_num, s_den, t_num, t_den, r_num, r_den))
    return sites


def parse_routes(
    data: bytes, path: Path, counts: dict[str, int], pins: dict[str, str],
) -> list[list[list]]:
    """The route records of the stream split into the five blocks, after checking the header
    pins against the registered role identities, the block order and transforms, the exact
    one-record-per-source coverage in order, and the target roles and ranges."""
    blocks: list[list[list]] = [[] for _ in BLOCKS]
    current = -1
    seen_begin = seen_end = seen_final = False
    header = None
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        for line_number, line in enumerate(handle, 1):
            record = json.loads(line)
            kind = record[0]
            if line_number == 1:
                if kind != "header":
                    raise SystemExit("certificate does not start with a header")
                header = record[1]
                continue
            if kind == "routes_begin":
                seen_begin = True
                expected = {"O4": counts["B"], "O5": counts["M"], "O6": counts["B"] + counts["S"] + counts["P"]}
                if record[1] != expected:
                    raise SystemExit(f"routes_begin announces {record[1]}, expected {expected}")
            elif kind == "route":
                if not seen_begin or seen_end:
                    raise SystemExit(f"line {line_number}: route outside the routes section")
                _, obligation, source_role, source_index, transform, target_role, target_index, ns, nt = record
                if current < 0 or (obligation, source_role) != (
                    BLOCKS[current]["obligation"], BLOCKS[current]["source"]):
                    current += 1
                    if current >= len(BLOCKS) or (obligation, source_role) != (
                        BLOCKS[current]["obligation"], BLOCKS[current]["source"]):
                        raise SystemExit(f"line {line_number}: unexpected block {obligation}/{source_role}")
                block = BLOCKS[current]
                if transform != block["transform"] or target_role not in block["targets"]:
                    raise SystemExit(f"line {line_number}: bad transform or target role {record}")
                if source_index != len(blocks[current]):
                    raise SystemExit(f"line {line_number}: source {source_index} out of order")
                if not 0 <= target_index < counts[target_role]:
                    raise SystemExit(f"line {line_number}: target index {target_index} out of range")
                if not (isinstance(ns, int) and isinstance(nt, int)):
                    raise SystemExit(f"line {line_number}: non-integer lift")
                blocks[current].append(record)
            elif kind == "routes_end":
                seen_end = True
                if record[1]["counts"] != {"O4": counts["B"], "O5": counts["M"],
                                           "O6": counts["B"] + counts["S"] + counts["P"]}:
                    raise SystemExit(f"routes_end counts {record[1]['counts']} unexpected")
            elif kind == "end":
                seen_final = True
                if not record[1].get("complete"):
                    raise SystemExit("end record is not complete")
    if header is None or not (seen_begin and seen_end and seen_final):
        raise SystemExit("certificate lacks header, routes section, or end record")
    if header.get("schema") != "periodic-disk-untrusted-certificate-v1":
        raise SystemExit(f"unexpected schema {header.get('schema')!r}")
    if header["roles"] != counts:
        raise SystemExit(f"header roles {header['roles']} differ from the tables {counts}")
    for role, name in ROLE_FILES.items():
        pin = header["input_pins"][name]["sha256"]
        if pin != pins[role]:
            raise SystemExit(f"header pins {name} to {pin}, expected {pins[role]}")
    if current != len(BLOCKS) - 1:
        raise SystemExit("not every route block is present")
    for block, records in zip(BLOCKS, blocks):
        if len(records) != counts[block["source"]]:
            raise SystemExit(f"block {block['name']} has {len(records)} records, expected {counts[block['source']]}")
    return blocks


# ----------------------------------------------------------------------------
# Python replay of the integer checkers (untrusted)


def gap_q_num(q: tuple, qp: tuple, n_s: int, n_t: int) -> int:
    """``ExactSafety.gapQNum``, transcribed."""
    gap_s = q[0] * qp[1] - qp[0] * q[1] + 59 * n_s * (q[1] * qp[1])
    gap_t = q[2] * qp[3] - qp[2] * q[3] + 59 * n_t * (q[3] * qp[3])
    s_den = q[1] * qp[1]
    t_den = q[3] * qp[3]
    return gap_s**2 * t_den**2 + gap_s * gap_t * s_den * t_den + gap_t**2 * s_den**2


def contain_check(q: tuple, qp: tuple, n_s: int, n_t: int) -> bool:
    """``ExactSafety.containCheck``, transcribed."""
    radius_diff = qp[4] * q[5] - q[4] * qp[5]
    gap_q_den = (q[1] * qp[1] * (q[3] * qp[3])) ** 2
    radius_sum_den = q[5] * qp[5]
    return radius_diff >= 0 and (
        441 * gap_q_num(q, qp, n_s, n_t) * radius_sum_den**2 <= 10000 * radius_diff**2 * gap_q_den
    )


def rotate_match_check(q: tuple, qp: tuple, n_s: int, n_t: int) -> bool:
    """``ExactSafety.rotateMatchCheck``, transcribed."""
    return (
        -q[2] * qp[1] == (qp[0] - 59 * n_s * qp[1]) * q[3]
        and (q[0] * q[3] + q[2] * q[1]) * qp[3] == (qp[2] - 59 * n_t * qp[3]) * (q[1] * q[3])
        and q[4] * qp[5] == qp[4] * q[5]
    )


def verify_routes(tables: dict[str, list], blocks: list[list[list]]) -> None:
    checked = 0
    for block, records in zip(BLOCKS, blocks):
        for record in records:
            source = tables[record[2]][record[3]]
            target = tables[record[5]][record[6]]
            n_s, n_t = -record[7], -record[8]
            check = contain_check if block["transform"] == "identity" else rotate_match_check
            if not check(source, target, n_s, n_t):
                raise SystemExit(f"block {block['name']}: route {record} fails the Python check")
            checked += 1
    print(f"Python route checks run: {checked}")


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
    """Pack space-separated words into lines of at most MAX_LINE columns."""
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


def module_header(title: str, body: str) -> str:
    return f"/-!\n# {title}\n\n{body}\n-/\n"


def paren(text: str) -> str:
    """Parenthesize a possibly multi-line term whose first line carries the indentation."""
    stripped = text.lstrip(" ")
    indent = len(text) - len(stripped)
    if "\n" not in stripped and " " not in stripped:
        return text
    return " " * indent + "(" + stripped + ")"


def site_tree_text(sites: list[tuple], lo: int, hi: int, bits: int, indent: int) -> str:
    """The depth-``bits`` tree over ordinals ``[lo, hi)`` (``hi - lo = 2^bits``)."""
    pad = " " * indent
    if lo >= len(sites):
        return pad + ".empty"
    if bits == 0:
        # leave room for the opening parenthesis and the closing ones of the enclosing nodes
        return wrap_items([lean_int(v) for v in sites[lo]], indent, ".leaf ⟨", "⟩",
                          MAX_LINE - indent // 2 - 1)
    mid = lo + 2 ** (bits - 1)
    left = site_tree_text(sites, lo, mid, bits - 1, indent + 2)
    right = site_tree_text(sites, mid, hi, bits - 1, indent + 2)
    return f"{pad}.node\n{paren(left)}\n{paren(right)}"


def record_text(record: list, block: dict) -> str:
    _, _, _, source_index, _, target_role, target_index, ns, nt = record
    if block["transform"] == "identity":
        role = "true" if block["targets"][target_role] else "false"
        return f".identity {source_index} {role} {target_index} {lean_int(ns)} {lean_int(nt)}"
    return f".rho {source_index} {target_index} {lean_int(ns)} {lean_int(nt)}"


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def step_call(block: dict, depths: dict[str, int], counter: str, records: str) -> str:
    """The checker application of a block, without the result."""
    source = block["source"]
    if block["checker"] == "rotation":
        return f"rotationRoutesStep routesSites{source} routesDepth{source} {counter} {records}"
    tgt_a = block["tgtA"]
    tgt_b = block["tgtB"]
    trees = f"routesSites{source} routesSites{tgt_a} " + (
        f"routesSites{tgt_b}" if tgt_b else "IndexTree.empty")
    depth_args = f"routesDepth{source} routesDepth{tgt_a} " + (f"routesDepth{tgt_b}" if tgt_b else "0")
    return f"containRoutesStep {trees} {depth_args}\n      {counter} {records}"


def check_call(block: dict, count: int, records: str) -> str:
    source = block["source"]
    if block["checker"] == "rotation":
        return f"rotationRoutesCheck routesSites{source} routesDepth{source} {count} {records}"
    tgt_a = block["tgtA"]
    tgt_b = block["tgtB"]
    trees = f"routesSites{source} routesSites{tgt_a} " + (
        f"routesSites{tgt_b}" if tgt_b else "IndexTree.empty")
    depth_args = f"routesDepth{source} routesDepth{tgt_a} " + (f"routesDepth{tgt_b}" if tgt_b else "0")
    return f"containRoutesCheck {trees} {depth_args}\n      {count} {records}"


def generate(args: argparse.Namespace) -> None:
    validate_generation_args("routes", args)

    subject = resolve_subject()
    certificate = args.certificate
    if certificate.name != subject.certificate.pin.name:
        raise GenerationRefused("--certificate must name the exported certificate.ndjson")
    roots = {"raw": args.data_dir, "export": certificate.parent}
    cert_input = read_input(subject, "certificate", roots)
    cert_sha = cert_input.sha256
    tables: dict[str, list] = {}
    shas: dict[str, str] = {}
    for role in ROLE_ORDER:
        table_input = read_input(subject, role, roots)
        path = args.data_dir / ROLE_FILES[role]
        shas[role] = table_input.input.pin.sha256
        tables[role] = parse_sites(table_input.data, path)
        del table_input
        print(f"role {role} {ROLE_FILES[role]} sites {len(tables[role])} sha256 {shas[role]}")
    counts = {role: len(tables[role]) for role in ["B", "S", "P", "M"]}
    blocks = parse_routes(cert_input.data, certificate, counts, shas)
    del cert_input
    print(f"certificate sha256 {cert_sha}; route blocks "
          + ", ".join(f"{block['name']}={len(records)}" for block, records in zip(BLOCKS, blocks)))
    if args.verify:
        verify_routes(tables, blocks)

    site_bits = args.site_chunk.bit_length() - 1
    data_dir = args.out_dir / "Data"
    checks_dir = args.out_dir / "Checks"
    generated = (
        "Generated by `gen_routes_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand."
    )
    options = (
        "set_option autoImplicit false\n"
        f"set_option maxRecDepth {args.max_rec_depth}\n"
        "set_option maxHeartbeats 0\n"
    )
    depths: dict[str, int] = {}
    site_module_count = 0

    # role tables
    for role in ROLE_ORDER:
        sites = tables[role]
        table = ROLE_FILES[role]
        site_blocks = math.ceil(len(sites) / args.site_chunk)
        top_bits = math.ceil(math.log2(site_blocks)) if site_blocks > 1 else 0
        depth = site_bits + top_bits
        depths[role] = depth
        for block in range(site_blocks):
            lo = block * args.site_chunk
            hi = min(lo + args.site_chunk, len(sites))
            name = f"routesSites{role}_{block:03d}"
            local = "n" if lo == 0 else f"(n - {lo})"
            doc = module_header(
                f"Route site block {role} {block:03d}",
                f"Sites {lo} to {hi - 1} of `{table}` (role {role}) as a depth-{site_bits}\n"
                f"`IndexTree SiteWire`: `{name}.get? {site_bits} {local}` returns ordinal `n` for\n"
                f"`{lo} ≤ n < {hi}`. Ordinals are row positions of the strictly increasing table.\n"
                f"Source SHA-256: `{shas[role]}`.\n{generated}",
            )
            body = (
                f"import Erdos188.UpperBound.RoutesData\n\n{doc}\n{options}\nnamespace Erdos188.UpperBound\n\n"
                f"/-- Sites {lo} to {hi - 1} of the role-{role} table. -/\n"
                f"def {name} : IndexTree SiteWire :=\n"
                f"{site_tree_text(sites, lo, lo + args.site_chunk, site_bits, 2)}\n\n"
                "end Erdos188.UpperBound\n"
            )
            write(data_dir / f"SitesRoutes{role}_{block:03d}.lean", body)
            site_module_count += 1

        def top_text(lo_block: int, bits: int, indent: int) -> str:
            pad = " " * indent
            if lo_block >= site_blocks:
                return pad + ".empty"
            if bits == 0:
                return pad + f"routesSites{role}_{lo_block:03d}"
            half = 2 ** (bits - 1)
            left = top_text(lo_block, bits - 1, indent + 2)
            right = top_text(lo_block + half, bits - 1, indent + 2)
            return f"{pad}.node\n{paren(left)}\n{paren(right)}"

        imports = "\n".join(
            f"import Erdos188.UpperBound.Data.SitesRoutes{role}_{block:03d}" for block in range(site_blocks)
        )
        doc = module_header(
            f"Route site tree {role}",
            f"The {len(sites)} sites of `{table}` (role {role}) as one depth-{depth}\n"
            f"`IndexTree SiteWire`: the top {top_bits} bits of an ordinal select one of {2**top_bits}\n"
            f"block slots, of which slots 0 to {site_blocks - 1} hold `routesSites{role}_000` to\n"
            f"`routesSites{role}_{site_blocks - 1:03d}` (each a depth-{site_bits} tree over\n"
            f"{args.site_chunk} consecutive ordinals) and the rest are `empty`, so\n"
            f"`routesSites{role}.get? routesDepth{role} n` returns ordinal `n` for `n < {len(sites)}`.\n"
            f"Source SHA-256: `{shas[role]}`.\n{generated}",
        )
        body = (
            f"{imports}\n\n{doc}\nset_option autoImplicit false\n\nnamespace Erdos188.UpperBound\n\n"
            f"/-- The lookup depth of the role-{role} table: `2 ^ {depth} ≥ {len(sites)}`. -/\n"
            f"def routesDepth{role} : ℕ := {depth}\n\n"
            f"/-- The whole role-{role} table, indexed by ordinal through `IndexTree.get?`. -/\n"
            f"def routesSites{role} : IndexTree SiteWire :=\n{top_text(0, top_bits, 2)}\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(data_dir / f"SitesRoutes{role}.lean", body)

        # validity and shape of the table: one kernel theorem pair per block, so that no single
        # kernel check visits more than one block, combined along the top tree by the node lemmas
        for block in range(site_blocks):
            lo = block * args.site_chunk
            hi = min(lo + args.site_chunk, len(sites))
            name = f"routesSites{role}_{block:03d}"
            doc = module_header(
                f"Route site validity {role} {block:03d}",
                f"Kernel checks of sites {lo} to {hi - 1} of `{table}` (role {role}): every stored wire\n"
                f"is valid, and the block has the shape of the ordinals `[0, {hi - lo})`.\n"
                f"Source SHA-256: `{shas[role]}`.\n{generated}",
            )
            body = (
                f"import Erdos188.UpperBound.Data.SitesRoutes{role}_{block:03d}\n\n{doc}\n{options}\n"
                "namespace Erdos188.UpperBound\n\n"
                f"/-- Every stored site of block {block:03d} of the role-{role} table is a valid wire. -/\n"
                f"theorem {name}_valid_all : {name}.toList.all SiteWire.valid = true := by\n"
                "  decide +kernel\n\n"
                f"/-- Block {block:03d} of the role-{role} table has the shape of the ordinals\n"
                f"`[0, {hi - lo})`. -/\n"
                f"theorem {name}_shape : {name}.shapeCheck {site_bits} {hi - lo} = true := by\n"
                "  decide +kernel\n\n"
                "end Erdos188.UpperBound\n"
            )
            write(checks_dir / f"RoutesValid{role}_{block:03d}.lean", body)

        def valid_term(lo_block: int, bits: int, indent: int) -> str:
            """The proof of `toList.all SiteWire.valid` for the top subtree of block slots
            `[lo_block, lo_block + 2^bits)`, from the block theorems."""
            pad = " " * indent
            if lo_block >= site_blocks:
                return pad + "(IndexTree.all_empty SiteWire.valid)"
            if bits == 0:
                return pad + f"routesSites{role}_{lo_block:03d}_valid_all"
            half = 2 ** (bits - 1)
            return (f"{pad}(IndexTree.all_node_of SiteWire.valid _ _\n"
                    f"{valid_term(lo_block, bits - 1, indent + 2)}\n"
                    f"{valid_term(lo_block + half, bits - 1, indent + 2)})")

        def shape_term(lo_block: int, bits: int, count: int, indent: int) -> str:
            """The proof of `shapeCheck (site_bits + bits) count` for the top subtree of block
            slots `[lo_block, lo_block + 2^bits)`; the half counts are the `min` and subtraction
            of `shapeCheck`, which the elaborator evaluates on literals."""
            pad = " " * indent
            if lo_block >= site_blocks:
                return pad + f"(IndexTree.shapeCheck_empty {site_bits + bits})"
            if bits == 0:
                return pad + f"routesSites{role}_{lo_block:03d}_shape"
            half = 2 ** (bits - 1)
            split = half * args.site_chunk
            return (f"{pad}(IndexTree.shapeCheck_node_of _ _ {site_bits + bits - 1} {count}\n"
                    f"{shape_term(lo_block, bits - 1, min(count, split), indent + 2)}\n"
                    f"{shape_term(lo_block + half, bits - 1, max(count - split, 0), indent + 2)})")

        imports = "\n".join(
            f"import Erdos188.UpperBound.Checks.RoutesValid{role}_{block:03d}" for block in range(site_blocks)
        )
        doc = module_header(
            f"Route site validity {role}",
            f"The {site_blocks} block checks of `{table}` (role {role}) combined along the top tree:\n"
            f"every stored wire is valid, and the tree has the shape of the ordinals `[0, {len(sites)})`.\n"
            f"Source SHA-256: `{shas[role]}`.\n{generated}",
        )
        body = (
            f"{imports}\nimport Erdos188.UpperBound.Data.SitesRoutes{role}\n\n{doc}\n"
            "set_option autoImplicit false\n\nnamespace Erdos188.UpperBound\n\n"
            f"/-- Every stored site of the role-{role} table is a valid wire. -/\n"
            f"theorem routesSites{role}_valid_all : routesSites{role}.toList.all SiteWire.valid = true :=\n"
            f"{valid_term(0, top_bits, 2)}\n\n"
            f"/-- The role-{role} table has the shape of the ordinals `[0, {len(sites)})`. -/\n"
            f"theorem routesSites{role}_shape : routesSites{role}.shapeCheck routesDepth{role} {len(sites)} = true :=\n"
            f"{shape_term(0, top_bits, len(sites), 2)}\n\n"
            f"/-- Validity of every stored site of the role-{role} table, in hypothesis form. -/\n"
            f"theorem routesSites{role}_valid : ∀ w ∈ routesSites{role}.toList, w.valid = true :=\n"
            f"  IndexTree.valid_of_all routesSites{role} routesSites{role}_valid_all\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(checks_dir / f"RoutesValid{role}.lean", body)

    # route blocks
    chunk_counts: dict[str, int] = {}
    for block, records in zip(BLOCKS, blocks):
        name = block["name"]
        source = block["source"]
        record_blocks = math.ceil(len(records) / args.record_chunk)
        chunk_counts[name] = record_blocks
        for chunk in range(record_blocks):
            lo = chunk * args.record_chunk
            hi = min(lo + args.record_chunk, len(records))
            literal = f"routes{name}_{chunk:03d}"
            doc = module_header(
                f"Route block {name} chunk {chunk:03d}",
                f"Records {lo} to {hi - 1} of the {block['obligation']} `{block['transform']}` routes\n"
                f"of role {source} in `certificate.ndjson`, in stream order; the boundary counters are\n"
                f"`{lo}` before and `{hi}` after the chunk. Wire lifts are kept verbatim.\n"
                f"Certificate SHA-256: `{cert_sha}`.\n{generated}",
            )
            items = [record_text(record, block) for record in records[lo:hi]]
            lines = [
                ("  [" if position == 0 else "    ") + item + ("," if position + 1 < len(items) else "]")
                for position, item in enumerate(items)
            ]
            body = (
                f"import Erdos188.UpperBound.RoutesData\n\n{doc}\n{options}\nnamespace Erdos188.UpperBound\n\n"
                f"/-- Records {lo} to {hi - 1} of route block {name}. -/\n"
                f"def {literal} : List RouteRecord :=\n" + "\n".join(lines) + "\n\nend Erdos188.UpperBound\n"
            )
            write(data_dir / f"Routes{name}_{chunk:03d}.lean", body)

            roles = [source] + ([block["tgtA"]] + ([block["tgtB"]] if block.get("tgtB") else [])
                                if block["checker"] == "contain" else [])
            imports = "\n".join(f"import Erdos188.UpperBound.Data.SitesRoutes{role}" for role in roles)
            doc = module_header(
                f"Route block {name} check {chunk:03d}",
                f"Kernel replay of records {lo} to {hi - 1} of route block {name} from counter `{lo}`\n"
                f"to counter `{hi}`.\nCertificate SHA-256: `{cert_sha}`.\n{generated}",
            )
            body = (
                f"{imports}\nimport Erdos188.UpperBound.Data.Routes{name}_{chunk:03d}\n\n{doc}\n{options}\n"
                "namespace Erdos188.UpperBound\n\n"
                f"/-- Chunk {chunk:03d} (records {lo} to {hi - 1}) of route block {name} replays from\n"
                f"counter `{lo}` to counter `{hi}`. -/\n"
                f"theorem routes{name}_step_{chunk:03d} :\n"
                f"    {step_call(block, depths, str(lo), literal)} = some {hi} := by\n"
                "  decide +kernel\n\n"
                "end Erdos188.UpperBound\n"
            )
            write(checks_dir / f"Routes{name}_{chunk:03d}.lean", body)

    # the chained theorems and the final statements
    imports = [f"import Erdos188.UpperBound.Checks.RoutesValid{role}" for role in ROLE_ORDER]
    for block in BLOCKS:
        imports += [f"import Erdos188.UpperBound.Checks.Routes{block['name']}_{chunk:03d}"
                    for chunk in range(chunk_counts[block["name"]])]
    doc = module_header(
        "Route certificate chained replay",
        "The chunk theorems of the five route blocks chained through the step chain\n"
        "lemmas into the replay of every route record of the exported certificate\n"
        "`certificate.ndjson` against the four role tables, the passing obligation\n"
        "checks, and the five final theorems: the periodic union of B lies in the union\n"
        "of those of S and P, the periodic union of M lies in that of S, and the\n"
        "periodic unions of B, S, and P are rotation invariant. The four role tables\n"
        "are exact assets of the 42-term construction under\n"
        "`data/k42/`.\n"
        "The certificate is the documented output of `export_certificate.py` over those\n"
        "tables; it is identified here by its SHA-256 and is not retained in the\n"
        "repository, since the generated `Data/` modules carry every replayed record.\n"
        f"Certificate SHA-256: `{cert_sha}`.\n"
        + "".join(f"Table {ROLE_FILES[role]} SHA-256: `{shas[role]}`.\n" for role in ROLE_ORDER)
        + "Generated by `gen_routes_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand.\n"
        "No claim identity is asserted in this module.",
    )
    sections = []
    for block, records in zip(BLOCKS, blocks):
        name = block["name"]
        source = block["source"]
        count = len(records)
        record_blocks = chunk_counts[name]
        all_name = f"routes{name}All"
        all_text = wrap_words(
            [f"routes{name}_{chunk:03d}" + (" ++" if chunk + 1 < record_blocks else "")
             for chunk in range(record_blocks)],
            2,
        )
        chain = "containRoutesStep_chain" if block["checker"] == "contain" else "rotationRoutesStep_chain"
        chain_lines = []
        previous = f"routes{name}_step_000"
        for chunk in range(1, record_blocks):
            chain_lines.append(f"  have chain_{chunk:03d} := {chain} {previous} routes{name}_step_{chunk:03d}")
            previous = f"chain_{chunk:03d}"
        of_step = "containRoutesCheck_of_step" if block["checker"] == "contain" else "rotationRoutesCheck_of_step"
        underscores = "_ _ _ _ _ _ _ _" if block["checker"] == "contain" else "_ _ _ _"
        sections.append(
            f"/-- Every record of route block {name} in order: the {record_blocks} chunks concatenated. -/\n"
            f"def {all_name} : List RouteRecord :=\n{all_text}\n\n"
            f"/-- Route block {name} replays from counter `0` to counter `{count}`. -/\n"
            f"theorem routes{name}_step_real :\n"
            f"    {step_call(block, depths, '0', all_name)} = some {count} := by\n"
            + ("\n".join(chain_lines) + "\n" if chain_lines else "")
            + f"  exact {previous}\n\n"
            f"/-- The whole route obligation of block {name} passes. -/\n"
            f"theorem routes{name}_check_real :\n"
            f"    {check_call(block, count, all_name)} = true :=\n"
            f"  {of_step} {underscores} routesSites{source}_shape routes{name}_step_real\n"
        )
    n_b, n_s, n_p, n_m = counts["B"], counts["S"], counts["P"], counts["M"]
    finals = (
        "/-- The periodic union of the literal base family lies in the union of the periodic unions of\n"
        "the literal carrier and plug families. -/\n"
        "theorem U_B_subset_S_union_P_real :\n"
        "    U (wireSet routesSitesB.toList) ⊆\n"
        "      U (wireSet routesSitesS.toList) ∪ U (wireSet routesSitesP.toList) :=\n"
        "  U_subset_of_containRoutes routesSitesB routesSitesS routesSitesP routesDepthB routesDepthS\n"
        f"    routesDepthP {n_b} routesO4BAll routesSitesB_valid routesSitesS_valid routesSitesP_valid\n"
        "    routesO4B_check_real\n\n"
        "/-- The periodic union of the literal micro family lies in that of the literal carrier\n"
        "family. -/\n"
        "theorem U_M_subset_S_real :\n"
        "    U (wireSet routesSitesM.toList) ⊆ U (wireSet routesSitesS.toList) :=\n"
        f"  U_subset_of_containRoutes_empty routesSitesM routesSitesS routesDepthM routesDepthS 0 {n_m}\n"
        "    routesO5MAll routesSitesM_valid routesSitesS_valid routesO5M_check_real\n\n"
        "/-- The periodic union of the literal base family is rotation invariant. -/\n"
        "theorem rotationInvariant_U_B_real : RotationInvariant (U (wireSet routesSitesB.toList)) :=\n"
        f"  rotationRoutesCheck_sound routesSitesB routesDepthB {n_b} routesO6BAll routesSitesB_valid\n"
        "    routesO6B_check_real\n\n"
        "/-- The periodic union of the literal carrier family is rotation invariant. -/\n"
        "theorem rotationInvariant_U_S_real : RotationInvariant (U (wireSet routesSitesS.toList)) :=\n"
        f"  rotationRoutesCheck_sound routesSitesS routesDepthS {n_s} routesO6SAll routesSitesS_valid\n"
        "    routesO6S_check_real\n\n"
        "/-- The periodic union of the literal plug family is rotation invariant. -/\n"
        "theorem rotationInvariant_U_P_real : RotationInvariant (U (wireSet routesSitesP.toList)) :=\n"
        f"  rotationRoutesCheck_sound routesSitesP routesDepthP {n_p} routesO6PAll routesSitesP_valid\n"
        "    routesO6P_check_real\n"
    )
    body = (
        "\n".join(imports) + f"\n\n{doc}\nset_option autoImplicit false\n"
        f"set_option maxRecDepth {args.max_rec_depth}\n\nnamespace Erdos188.UpperBound\n\n"
        + "\n".join(sections) + "\n" + finals + "\nend Erdos188.UpperBound\n"
    )
    write(checks_dir / "RoutesAll.lean", body)
    total_chunks = sum(chunk_counts.values())
    print(
        f"depths {depths}; wrote {site_module_count} site block modules, 4 site tree modules, "
        f"{site_module_count} block validity modules, 4 validity modules, {total_chunks} record modules, {total_chunks} check modules "
        f"({chunk_counts}), RoutesAll under {args.out_dir}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA_DIR)
    parser.add_argument("--certificate", type=Path, required=True,
                        help="the exported certificate.ndjson")
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="fresh regeneration root; never the committed Erdos188/UpperBound")
    parser.add_argument("--site-chunk", type=int, default=4096, help="sites per block (power of two)")
    parser.add_argument("--record-chunk", type=int, default=4096, help="records per chunk")
    parser.add_argument("--max-rec-depth", type=int, default=100000,
                        help="elaboration recursion budget; the compiler pass over a 4096-leaf tree "
                             "needs more than 20000")
    parser.add_argument("--verify", action="store_true", help="also run the Python route checks")
    args = parser.parse_args()
    try:
        generate(args)
    except GenerationRefused as error:
        raise SystemExit(str(error)) from None


if __name__ == "__main__":
    main()
