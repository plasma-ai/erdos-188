#!/usr/bin/env python3
"""Generate the Lean data modules for the K42 cover certificate.

Reads ``cover_sites.tsv`` (one site per row, ``s<TAB>t<TAB>r`` with each field a
canonical integer or ``num/den``) and ``cover_tree.cert`` (19 header lines, then
``D``/``T``/``S`` records, then ``END``) and writes, under ``<out>/Data`` and
``<out>/Checks``:

* ``CoverSites_NNN.lean``: one balanced ``SiteTree`` per block of at most
  ``--site-chunk`` consecutive ordinals (a power of two);
* ``CoverSites.lean``: ``coverSiteTree`` combining the blocks and
  ``coverSiteDepth``, the lookup depth;
* ``CoverRecords_NNN.lean``: one ``List CoverRecord`` literal per block of at
  most ``--record-chunk`` consecutive records;
* ``CoverStacks.lean``: the cell stack before every record block, replayed in
  Python (untrusted; the kernel verifies each block against them);
* ``Checks/CoverStep_NNN.lean``: one ``decide +kernel`` theorem per block;
* ``Checks/CoverAll.lean``: the chained replay and ``certified_real``.

Depth convention (see ``SiteTree.get?``): ordinal ``n`` is looked up by reading
its binary digits from bit ``depth - 1`` down to bit ``0``, ``0`` for the left
child and ``1`` for the right child. A block of ``2^b`` ordinals starting at
``m * 2^b`` is a depth-``b`` tree, and the top tree spends the remaining
``depth - b`` bits selecting the block, so ``coverSiteTree.get? coverSiteDepth n``
finds ordinal ``n`` of the table.

Both inputs are authenticated against the gold identities of ``data/k42/manifest.json``
before parsing. Text decoding retains the original default-encoding/universal-newline
semantics.
"""

from __future__ import annotations

import argparse
import io
import math
import re
from pathlib import Path

if __package__:
    from .generation_profile import validate_generation_args
    from .generation_subject import GenerationRefused, read_input, resolve_subject
else:
    from generation_profile import validate_generation_args
    from generation_subject import GenerationRefused, read_input, resolve_subject

DEFAULT_DATA_DIR = Path(__file__).resolve().parent.parent.parent / "data" / "k42"
HEADER_LINES = 19
MAX_LINE = 100
FIELD_RE = re.compile(r"(-?\d+)(?:/(\d+))?")

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
    return num, den


def parse_sites(data: bytes, path: Path) -> list[tuple[int, int, int, int, int, int]]:
    """Parse bytes with the legacy default encoding and universal newlines."""
    sites = []
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        for line_number, line in enumerate(handle, 1):
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 3:
                raise SystemExit(f"{path}:{line_number}: expected three fields, got {len(parts)}")
            (s_num, s_den), (t_num, t_den), (r_num, r_den) = (parse_fraction(p) for p in parts)
            sites.append((s_num, s_den, t_num, t_den, r_num, r_den))
    return sites


def parse_records(data: bytes, path: Path) -> tuple[list[str], list[tuple]]:
    """Return the header lines and the records as tuples led by their kind."""
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        lines = handle.read().split("\n")
    if lines[-1] != "":
        raise SystemExit(f"{path}: missing trailing newline")
    lines.pop()
    if len(lines) < HEADER_LINES + 1 or lines[-1] != "END":
        raise SystemExit(f"{path}: expected exactly one END line at the end")
    header = lines[:HEADER_LINES]
    body = lines[HEADER_LINES:-1]
    declared = None
    for line in header:
        if line.startswith("tree_records "):
            declared = int(line.split()[1])
    if declared is None or declared != len(body):
        raise SystemExit(f"{path}: header declares {declared} tree records, body has {len(body)}")
    records = []
    for offset, line in enumerate(body):
        parts = line.split(" ")
        kind = parts[0]
        if kind in ("D", "T") and len(parts) == 6:
            records.append((kind, *map(int, parts[1:])))
        elif kind == "S" and len(parts) == 10:
            records.append((kind, *map(int, parts[1:])))
        else:
            raise SystemExit(f"{path}:{HEADER_LINES + offset + 1}: bad record {line!r}")
    return header, records


# ----------------------------------------------------------------------------
# Python replay of the stack discipline (untrusted)


def direction_child(cell: tuple, bit: int) -> tuple:
    d, i, e, h, k = cell
    return (d + 1, 2 * i + bit, e, h, k)


def translation_child(cell: tuple, eps: int, delta: int) -> tuple:
    d, i, e, h, k = cell
    return (d, i, e + 1, 2 * h + eps, 2 * k + delta)


def leaf_check(cell: tuple, j: int, site: tuple, lift_s: int, lift_t: int) -> bool:
    """The integer leaf test of ``ExactCover.leafCheck``, transcribed."""
    d, i, e, h, k = cell
    s_num, s_den, t_num, t_den, r_num, r_den = site
    if not (-21 <= j <= 20 and s_den > 0 and t_den > 0 and r_den > 0):
        return False
    a = 2**d
    t_mid = 2 * i + 1 - 4 * a
    u = i + 1 - 2 * a
    h_den = t_mid * t_mid + 2 * a * t_mid + 4 * a * a
    g_den = u * u + a * u + a * a
    p_s = t_mid * t_mid - 4 * a * a
    p_t = -t_mid * (t_mid + 4 * a)
    r_use = 2000 * g_den * r_num - 1733 * a * abs(j) * r_den
    if r_use <= 0:
        return False
    v_den = 2000 * g_den * r_den
    scale = 2**e
    w_den = 21 * h_den * scale * s_den * t_den
    for eps in (0, 1):
        x = (
            59 * (h + eps) * (21 * h_den) * s_den * t_den
            + 100 * j * p_s * scale * s_den * t_den
            - 21 * h_den * scale * s_num * t_den
            - 59 * lift_s * w_den
        )
        for delta in (0, 1):
            y = (
                59 * (k + delta) * (21 * h_den) * s_den * t_den
                + 100 * j * p_t * scale * s_den * t_den
                - 21 * h_den * scale * t_num * s_den
                - 59 * lift_t * w_den
            )
            if 441 * (x * x + x * y + y * y) * v_den * v_den > 10000 * w_den * w_den * r_use * r_use:
                return False
    return True


def replay(records: list[tuple], sites: list[tuple], chunk: int, verify: bool) -> list[list[tuple]]:
    """Return the stack before each record block; the last entry is the final stack."""
    stack = [(0, 0, 0, 0, 0)]
    boundaries = []
    verified = 0
    for index, record in enumerate(records):
        if index % chunk == 0:
            boundaries.append(list(stack))
        if not stack:
            raise SystemExit(f"record {index}: empty stack")
        cell = stack.pop()
        kind, d, i, e, h, k = record[:6]
        if cell != (d, i, e, h, k):
            raise SystemExit(f"record {index}: address {(d, i, e, h, k)} but cell {cell}")
        if kind == "D":
            stack.append(direction_child(cell, 1))
            stack.append(direction_child(cell, 0))
        elif kind == "T":
            stack.append(translation_child(cell, 1, 1))
            stack.append(translation_child(cell, 1, 0))
            stack.append(translation_child(cell, 0, 1))
            stack.append(translation_child(cell, 0, 0))
        else:
            j, ordinal, lift_s, lift_t = record[6:]
            if not 0 <= ordinal < len(sites):
                raise SystemExit(f"record {index}: ordinal {ordinal} outside the site table")
            if verify:
                if not leaf_check(cell, j, sites[ordinal], lift_s, lift_t):
                    raise SystemExit(f"record {index}: leaf check fails")
                verified += 1
    if stack:
        raise SystemExit(f"final stack has {len(stack)} cells")
    boundaries.append([])
    print(f"replayed {len(records)} records; Python leaf checks run: {verified}")
    return boundaries


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


def paren(text: str) -> str:
    """Parenthesize a possibly multi-line term whose first line carries the indentation."""
    stripped = text.lstrip(" ")
    indent = len(text) - len(stripped)
    if "\n" not in stripped and " " not in stripped:
        return text
    return " " * indent + "(" + stripped + ")"


def record_text(record: tuple) -> str:
    kind = record[0]
    if kind == "D":
        return ".direction " + " ".join(str(v) for v in record[1:])
    if kind == "T":
        return ".translation " + " ".join(str(v) for v in record[1:])
    return ".leaf " + " ".join(lean_int(v) for v in record[1:])


def cell_text(cell: tuple) -> str:
    return "⟨" + ", ".join(str(v) for v in cell) + "⟩"


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def generate(args: argparse.Namespace) -> None:
    validate_generation_args("cover", args)

    subject = resolve_subject()
    roots = {"raw": args.data_dir}
    sites_input = read_input(subject, "F", roots)
    sites_path = args.data_dir / sites_input.input.pin.name
    sites_sha = sites_input.sha256
    sites = parse_sites(sites_input.data, sites_path)
    del sites_input
    cert_input = read_input(subject, "cover_tree", roots)
    cert_path = args.data_dir / cert_input.input.pin.name
    cert_sha = cert_input.sha256
    header, records = parse_records(cert_input.data, cert_path)
    del cert_input
    print(f"sites {len(sites)} sha256 {sites_sha}")
    print(f"records {len(records)} sha256 {cert_sha} header[0] {header[0]!r}")

    site_bits = args.site_chunk.bit_length() - 1
    site_blocks = math.ceil(len(sites) / args.site_chunk)
    top_bits = max(0, math.ceil(math.log2(site_blocks))) if site_blocks > 1 else 0
    depth = site_bits + top_bits
    record_blocks = math.ceil(len(records) / args.record_chunk)
    boundaries = replay(records, sites, args.record_chunk, args.verify)
    assert len(boundaries) == record_blocks + 1
    print(
        f"site blocks {site_blocks} (2^{site_bits} each, depth {depth}); "
        f"record blocks {record_blocks} (at most {args.record_chunk} each); "
        f"max boundary stack {max(len(b) for b in boundaries)}"
    )

    data_dir = args.out_dir / "Data"
    checks_dir = args.out_dir / "Checks"
    generated = (
        "Generated by `gen_cover_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand."
    )
    options = (
        "set_option autoImplicit false\n"
        f"set_option maxRecDepth {args.max_rec_depth}\n"
        "set_option maxHeartbeats 0\n"
    )

    # site blocks
    for block in range(site_blocks):
        lo = block * args.site_chunk
        hi = min(lo + args.site_chunk, len(sites))
        name = f"coverSites_{block:03d}"
        local = "n" if lo == 0 else f"(n - {lo})"
        doc = module_header(
            f"Cover site block {block:03d}",
            f"Sites {lo} to {hi - 1} of `cover_sites.tsv` as a depth-{site_bits} `SiteTree`:\n"
            f"`{name}.get? {site_bits} {local}` returns ordinal `n` for `{lo} ≤ n < {hi}`.\n"
            f"Source SHA-256: `{sites_sha}`.\n{generated}",
        )
        body = (
            f"import Erdos188.UpperBound.CoverData\n\n{doc}\n{options}\nnamespace Erdos188.UpperBound\n\n"
            f"/-- Sites {lo} to {hi - 1} of the cover site table. -/\n"
            f"def {name} : SiteTree :=\n"
            f"{site_tree_text(sites, lo, lo + args.site_chunk, site_bits, 2)}\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(data_dir / f"CoverSites_{block:03d}.lean", body)

    # top tree
    def top_text(lo_block: int, bits: int, indent: int) -> str:
        pad = " " * indent
        if lo_block >= site_blocks:
            return pad + ".empty"
        if bits == 0:
            return pad + f"coverSites_{lo_block:03d}"
        half = 2 ** (bits - 1)
        left = top_text(lo_block, bits - 1, indent + 2)
        right = top_text(lo_block + half, bits - 1, indent + 2)
        return f"{pad}.node\n{paren(left)}\n{paren(right)}"

    imports = "\n".join(
        f"import Erdos188.UpperBound.Data.CoverSites_{block:03d}" for block in range(site_blocks)
    )
    doc = module_header(
        "Cover site tree",
        f"The {len(sites)} sites of `cover_sites.tsv` as one depth-{depth} `SiteTree`: the top\n"
        f"{top_bits} bits of an ordinal select one of {2**top_bits} block slots, of which slots 0 to\n"
        f"{site_blocks - 1} hold `coverSites_000` to `coverSites_{site_blocks - 1:03d}` (each a\n"
        f"depth-{site_bits} tree over {args.site_chunk} consecutive ordinals) and the rest are\n"
        f"`empty`, so `coverSiteTree.get? coverSiteDepth n` returns ordinal `n` for\n"
        f"`n < {len(sites)}`.\nSource SHA-256: `{sites_sha}`.\n{generated}",
    )
    body = (
        f"{imports}\n\n{doc}\nset_option autoImplicit false\n\nnamespace Erdos188.UpperBound\n\n"
        f"/-- The lookup depth of the cover site tree: `2 ^ {depth} ≥ {len(sites)}`. -/\n"
        f"def coverSiteDepth : ℕ := {depth}\n\n"
        "/-- The whole cover site table, indexed by ordinal through `SiteTree.get?`. -/\n"
        f"def coverSiteTree : SiteTree :=\n{top_text(0, top_bits, 2)}\n\n"
        "end Erdos188.UpperBound\n"
    )
    write(data_dir / "CoverSites.lean", body)

    # record blocks
    for block in range(record_blocks):
        lo = block * args.record_chunk
        hi = min(lo + args.record_chunk, len(records))
        name = f"coverRecords_{block:03d}"
        doc = module_header(
            f"Cover certificate block {block:03d}",
            f"Records {lo} to {hi - 1} of `cover_tree.cert`, in certificate order.\n"
            f"Source SHA-256: `{cert_sha}`.\n{generated}",
        )
        items = [record_text(record) for record in records[lo:hi]]
        lines = [
            ("  [" if position == 0 else "    ") + item + ("," if position + 1 < len(items) else "]")
            for position, item in enumerate(items)
        ]
        body = (
            f"import Erdos188.UpperBound.CoverData\n\n{doc}\n{options}\nnamespace Erdos188.UpperBound\n\n"
            f"/-- Records {lo} to {hi - 1} of the cover certificate. -/\n"
            f"def {name} : List CoverRecord :=\n" + "\n".join(lines) + "\n\nend Erdos188.UpperBound\n"
        )
        write(data_dir / f"CoverRecords_{block:03d}.lean", body)

    # boundary stacks
    doc = module_header(
        "Cover replay stacks",
        f"The cell stack before each of the {record_blocks} record blocks of `cover_tree.cert`,\n"
        "and the empty stack after the last block, computed by an untrusted Python replay of\n"
        "the stack discipline of `coverStreamStep`; the block theorems under `Checks/` verify\n"
        f"every transition in the kernel.\nSource SHA-256: `{cert_sha}`.\n{generated}",
    )
    stack_defs = []
    for index, stack in enumerate(boundaries):
        if index == 0:
            literal = "  [rootCell]"
            note = "The stack before block 000: the root cell alone."
        elif index == record_blocks:
            literal = "  []"
            note = f"The stack after block {record_blocks - 1:03d}: empty."
        else:
            # the Lean stack lists top first; the Python list keeps the top last
            literal = wrap_items([cell_text(cell) for cell in reversed(stack)], 2, "[", "]")
            note = f"The stack before block {index:03d}, top first ({len(stack)} cells)."
        stack_defs.append(
            f"/-- {note} -/\ndef coverStack_{index:03d} : List Cell :=\n{literal}\n"
        )
    body = (
        f"import Erdos188.UpperBound.CoverData\n\n{doc}\nset_option autoImplicit false\n\n"
        "namespace Erdos188.UpperBound\n\n" + "\n".join(stack_defs) + "\nend Erdos188.UpperBound\n"
    )
    write(data_dir / "CoverStacks.lean", body)

    # block checks
    for block in range(record_blocks):
        lo = block * args.record_chunk
        hi = min(lo + args.record_chunk, len(records))
        doc = module_header(
            f"Cover replay check {block:03d}",
            f"Kernel replay of records {lo} to {hi - 1} of `cover_tree.cert` from\n"
            f"`coverStack_{block:03d}` to `coverStack_{block + 1:03d}`.\n"
            f"Source SHA-256: `{cert_sha}`.\n{generated}",
        )
        body = (
            "import Erdos188.UpperBound.Data.CoverSites\n"
            "import Erdos188.UpperBound.Data.CoverStacks\n"
            f"import Erdos188.UpperBound.Data.CoverRecords_{block:03d}\n\n{doc}\n{options}\n"
            "namespace Erdos188.UpperBound\n\n"
            f"/-- Block {block:03d} (records {lo} to {hi - 1}) replays from `coverStack_{block:03d}` to\n"
            f"`coverStack_{block + 1:03d}`. -/\n"
            f"theorem coverStep_{block:03d} :\n"
            f"    coverStreamStep coverSiteTree coverSiteDepth coverStack_{block:03d}\n"
            f"      coverRecords_{block:03d} = some coverStack_{block + 1:03d} := by\n"
            "  decide +kernel\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(checks_dir / f"CoverStep_{block:03d}.lean", body)

    # the chained theorem
    imports = "\n".join(
        f"import Erdos188.UpperBound.Checks.CoverStep_{block:03d}" for block in range(record_blocks)
    )
    doc = module_header(
        "Cover certificate chained replay",
        f"The {record_blocks} block theorems chained through `coverStreamStep_chain` into the\n"
        f"replay of all {len(records)} records of `cover_tree.cert` against the {len(sites)}\n"
        "sites of `cover_sites.tsv`, and the certified root cell (`certified_real`).\n"
        "Both inputs are exact assets of the 42-term construction under\n"
        "`data/k42/`.\n"
        f"Certificate SHA-256: `{cert_sha}`.\n"
        f"Site table SHA-256: `{sites_sha}`.\n"
        "Generated by `gen_cover_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand.\n"
        "No claim identity is asserted in this module.",
    )
    all_text = wrap_words(
        [f"coverRecords_{block:03d}" + (" ++" if block + 1 < record_blocks else "")
         for block in range(record_blocks)],
        2,
    )
    chain_lines = []
    previous = "coverStep_000"
    for block in range(1, record_blocks):
        chain_lines.append(
            f"  have chain_{block:03d} := coverStreamStep_chain {previous} coverStep_{block:03d}"
        )
        previous = f"chain_{block:03d}"
    body = (
        f"{imports}\n\n{doc}\nset_option autoImplicit false\n"
        f"set_option maxRecDepth {args.max_rec_depth}\n\nnamespace Erdos188.UpperBound\n\n"
        f"/-- Every certificate record in order: the {record_blocks} blocks concatenated. -/\n"
        f"def coverRecordsAll : List CoverRecord :=\n{all_text}\n\n"
        "/-- The whole certificate replays from the root cell alone to the empty stack. -/\n"
        "theorem coverStream_real :\n"
        "    coverStreamStep coverSiteTree coverSiteDepth [rootCell] coverRecordsAll = some [] := by\n"
        + "\n".join(chain_lines) + f"\n  exact {previous}\n\n"
        "/-- The literal certificate certifies the root cell for the literal site family. -/\n"
        "theorem certified_real : Certified (coverSiteSet coverSiteTree) rootCell :=\n"
        "  coverStreamStep_certified coverSiteTree coverSiteDepth coverRecordsAll coverStream_real\n\n"
        "end Erdos188.UpperBound\n"
    )
    write(checks_dir / "CoverAll.lean", body)
    print(
        f"wrote {site_blocks} site modules, {record_blocks} record modules, {record_blocks} check "
        f"modules, CoverSites, CoverStacks, CoverAll under {args.out_dir}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA_DIR)
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="fresh regeneration root; never the committed Erdos188/UpperBound")
    parser.add_argument("--site-chunk", type=int, default=4096, help="sites per block (power of two)")
    parser.add_argument("--record-chunk", type=int, default=4096, help="records per block")
    parser.add_argument("--max-rec-depth", type=int, default=100000,
                        help="elaboration recursion budget; the compiler pass over a 4096-leaf tree "
                             "needs more than 20000")
    parser.add_argument("--verify", action="store_true", help="also run the Python leaf checks")
    args = parser.parse_args()
    try:
        generate(args)
    except GenerationRefused as error:
        raise SystemExit(str(error)) from None


if __name__ == "__main__":
    main()
