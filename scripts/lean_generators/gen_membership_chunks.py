"""Generate the chunked kernel check that every cover site is a base site or a micro site.

Reads ``cover_sites.tsv`` (F), ``base.tsv`` (B) and ``micro_representatives.tsv`` (M), one site
per row ``s<TAB>t<TAB>r`` with each field a canonical integer or ``num/den``, verifies the pinned
SHA-256 identities, checks in exact rational arithmetic that each table is strictly increasing
in the lexicographic order on ``(s, t, r)`` and that F is the disjoint merge of B and M, then
replays the cursor walk of ``MembershipData.membershipStep`` (untrusted) to obtain the cursor
pair before each block of ``--site-chunk`` cover sites. It emits ``Data/MembershipStates.lean``
(the boundary cursor pairs), one ``Checks/Membership_NNN.lean`` per cover site block (a
``decide +kernel`` theorem that the block walks from its boundary pair to the next), and
``Checks/MembershipAll.lean`` (the chained walk over the concatenation of the block lists, the
equation between the flattened cover tree and that concatenation, and the inclusion of the cover
family in the union of the base and micro wire families). With ``--negative`` it also writes a
negative-control module outside the mathematics library: block 000 with one site replaced by a
foreign site, whose walk must reduce to ``none``.

The block lists are ``coverSites_NNN.toList`` of the cover lane's site block modules, so the
site chunk must equal the cover lane's (4096) and the block count the cover lane's.

The three tables are authenticated against ``data/k42/manifest.json``, and verified
immutable buffers supply every parsed table. No export file is opened.
"""

from __future__ import annotations

import argparse
import io
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
DEFAULT_NEGATIVE_DIR = Path(__file__).resolve().parent.parent / "output" / "negative"
MAX_LINE = 100
FIELD_RE = re.compile(r"(-?\d+)(?:/(\d+))?")

TABLE_FILES = {"F": "cover_sites.tsv", "B": "base.tsv", "M": "micro_representatives.tsv"}
FOREIGN_SITE = (1, 1, 1, 1, 1, 10)

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


def read_sites(data: bytes, path: Path) -> list[tuple[int, int, int, int, int, int]]:
    """Parse verified bytes; path labels errors and is never opened."""
    sites = []
    # Match Path.open(): default encoding and universal newline translation.
    with io.TextIOWrapper(io.BytesIO(data)) as handle:
        for line_number, line in enumerate(handle, 1):
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 3:
                raise SystemExit(f"{path}:{line_number}: expected three fields, got {len(parts)}")
            (s_num, s_den), (t_num, t_den), (r_num, r_den) = (parse_fraction(p) for p in parts)
            sites.append((s_num, s_den, t_num, t_den, r_num, r_den))
    return sites


def rational_key(site: tuple) -> tuple[Fraction, Fraction, Fraction]:
    s_num, s_den, t_num, t_den, r_num, r_den = site
    return (Fraction(s_num, s_den), Fraction(t_num, t_den), Fraction(r_num, r_den))


# ----------------------------------------------------------------------------
# Untrusted checks and replay


def check_strictly_increasing(name: str, sites: list[tuple]) -> None:
    keys = [rational_key(site) for site in sites]
    for index in range(1, len(keys)):
        if not keys[index - 1] < keys[index]:
            raise SystemExit(f"{name}: rows {index - 1} and {index} are not strictly increasing")
    print(f"{name}: {len(sites)} sites, strictly increasing in (s, t, r)")


def check_merge(cover: list[tuple], base: list[tuple], micro: list[tuple]) -> None:
    """F must be exactly the merge of B and M as wire tuples, with B and M disjoint."""
    if len(cover) != len(base) + len(micro):
        raise SystemExit(f"F has {len(cover)} sites but B + M has {len(base) + len(micro)}")
    merged = sorted(base + micro, key=rational_key)
    if merged != cover:
        first = next(i for i, (a, b) in enumerate(zip(merged, cover)) if a != b)
        raise SystemExit(f"F differs from the merge of B and M first at row {first}")
    if set(base) & set(micro):
        raise SystemExit("B and M share a site")
    if len(set(rational_key(s) for s in cover)) != len(cover):
        raise SystemExit("F has two wires with the same rational value")
    print(f"F = merge(B, M) as wire tuples: {len(cover)} = {len(base)} + {len(micro)}, disjoint")


def replay(cover: list[tuple], base: list[tuple], micro: list[tuple], chunk: int) -> list[tuple[int, int]]:
    """The cursor pair before each cover block, and the final pair, by the walk of
    `membershipStep`: match the base cursor first, else the micro cursor, else fail."""
    b_pos = m_pos = 0
    boundaries = []
    for index, site in enumerate(cover):
        if index % chunk == 0:
            boundaries.append((b_pos, m_pos))
        if b_pos < len(base) and base[b_pos] == site:
            b_pos += 1
        elif m_pos < len(micro) and micro[m_pos] == site:
            m_pos += 1
        else:
            raise SystemExit(f"cover site {index} matches neither cursor")
    boundaries.append((b_pos, m_pos))
    if (b_pos, m_pos) != (len(base), len(micro)):
        raise SystemExit(f"walk ends at {(b_pos, m_pos)}, not {(len(base), len(micro))}")
    print(f"replayed {len(cover)} cover sites; final cursors {(b_pos, m_pos)}")
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


def paren(text: str) -> str:
    """Parenthesize a possibly multi-line term whose first line carries the indentation."""
    stripped = text.lstrip(" ")
    indent = len(text) - len(stripped)
    if "\n" not in stripped and " " not in stripped:
        return text
    return " " * indent + "(" + stripped + ")"


def site_tree_text(sites: list[tuple], lo: int, hi: int, bits: int, indent: int) -> str:
    """The depth-``bits`` `SiteTree` over ordinals ``[lo, hi)`` (``hi - lo = 2^bits``)."""
    pad = " " * indent
    if lo >= len(sites):
        return pad + ".empty"
    if bits == 0:
        return wrap_items([lean_int(v) for v in sites[lo]], indent, ".leaf ⟨", "⟩",
                          MAX_LINE - indent // 2 - 1)
    mid = lo + 2 ** (bits - 1)
    left = site_tree_text(sites, lo, mid, bits - 1, indent + 2)
    right = site_tree_text(sites, mid, hi, bits - 1, indent + 2)
    return f"{pad}.node\n{paren(left)}\n{paren(right)}"


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


WALK = "membershipStep routesSitesB routesSitesM routesDepthB routesDepthM"


def generate(args: argparse.Namespace) -> None:
    validate_generation_args("membership", args)
    subject = resolve_subject()
    # membership reads only raw inputs
    roots = {"raw": args.data_dir.absolute()}
    tables = {}
    digests = {}
    for role, file_name in TABLE_FILES.items():
        source = read_input(subject, role, roots)
        path = args.data_dir / file_name
        digests[role] = source.input.pin.sha256
        tables[role] = read_sites(source.data, path)
        del source
        print(f"table {role} {file_name} sites {len(tables[role])} sha256 {digests[role]}")
    cover, base, micro = tables["F"], tables["B"], tables["M"]
    for role, sites in tables.items():
        check_strictly_increasing(role, sites)
    check_merge(cover, base, micro)
    if args.negative:
        if args.negative_index >= min(args.site_chunk, len(cover)):
            raise SystemExit("--negative-index must name a cover site in block 000")
        if FOREIGN_SITE in set(cover):
            raise SystemExit("the foreign site is a cover site")

    site_bits = args.site_chunk.bit_length() - 1
    blocks = math.ceil(len(cover) / args.site_chunk)
    top_bits = math.ceil(math.log2(blocks)) if blocks > 1 else 0
    boundaries = replay(cover, base, micro, args.site_chunk)
    assert len(boundaries) == blocks + 1
    print(f"cover blocks {blocks} (2^{site_bits} each); boundary cursor pairs {len(boundaries)}")

    data_dir = args.out_dir / "Data"
    checks_dir = args.out_dir / "Checks"
    generated = (
        "Generated by `gen_membership_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand."
    )
    shas = (
        f"Cover table SHA-256: `{digests['F']}`.\n"
        f"Base table SHA-256: `{digests['B']}`.\n"
        f"Micro table SHA-256: `{digests['M']}`."
    )
    options = (
        "set_option autoImplicit false\n"
        f"set_option maxRecDepth {args.max_rec_depth}\n"
        "set_option maxHeartbeats 0\n"
    )

    # boundary cursor pairs
    doc = module_header(
        "Membership walk cursors",
        f"The cursor pair into the base and micro tables before each of the {blocks} cover site\n"
        f"blocks of `cover_sites.tsv`, and the pair after the last block, computed by an untrusted\n"
        "Python replay of the walk of `membershipStep`; the block theorems under `Checks/` verify\n"
        f"every transition in the kernel.\n{shas}\n{generated}",
    )
    state_defs = []
    for index, (b_pos, m_pos) in enumerate(boundaries):
        if index == 0:
            note = "The cursor pair before block 000: both tables at their first site."
        elif index == blocks:
            note = f"The cursor pair after block {blocks - 1:03d}: both tables exhausted."
        else:
            note = f"The cursor pair before block {index:03d}."
        state_defs.append(
            f"/-- {note} -/\ndef membershipState_{index:03d} : MembershipState := ({b_pos}, {m_pos})\n"
        )
    body = (
        f"import Erdos188.UpperBound.MembershipData\n\n{doc}\nset_option autoImplicit false\n\n"
        "namespace Erdos188.UpperBound\n\n" + "\n".join(state_defs) + "\nend Erdos188.UpperBound\n"
    )
    write(data_dir / "MembershipStates.lean", body)

    # block checks
    for block in range(blocks):
        lo = block * args.site_chunk
        hi = min(lo + args.site_chunk, len(cover))
        doc = module_header(
            f"Membership check {block:03d}",
            f"Kernel walk of cover sites {lo} to {hi - 1} of `cover_sites.tsv` (the leaves of\n"
            f"`coverSites_{block:03d}`) from `membershipState_{block:03d}` to\n"
            f"`membershipState_{block + 1:03d}`: every site is stored at the base or the micro\n"
            f"cursor.\n{shas}\n{generated}",
        )
        body = (
            f"import Erdos188.UpperBound.Data.CoverSites_{block:03d}\n"
            "import Erdos188.UpperBound.Data.MembershipStates\n"
            "import Erdos188.UpperBound.Data.SitesRoutesB\n"
            "import Erdos188.UpperBound.Data.SitesRoutesM\n\n"
            f"{doc}\n{options}\nnamespace Erdos188.UpperBound\n\n"
            f"/-- Block {block:03d} (cover sites {lo} to {hi - 1}) walks from\n"
            f"`membershipState_{block:03d}` to `membershipState_{block + 1:03d}`. -/\n"
            f"theorem membership_{block:03d} :\n"
            f"    {WALK} membershipState_{block:03d}\n"
            f"      coverSites_{block:03d}.toList = some membershipState_{block + 1:03d} := by\n"
            "  decide +kernel\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(checks_dir / f"Membership_{block:03d}.lean", body)

    # the chained theorem and the inclusion
    imports = "\n".join(
        [f"import Erdos188.UpperBound.Checks.Membership_{block:03d}" for block in range(blocks)]
        + ["import Erdos188.UpperBound.Data.CoverSites"]
    )
    doc = module_header(
        "Membership chained walk",
        f"The {blocks} block theorems chained through `membershipStep_chain` into the walk over\n"
        f"all {len(cover)} cover sites of `cover_sites.tsv`, the equation between the flattened\n"
        "cover site tree and the concatenation of the block lists, and the inclusion of\n"
        "the cover family in the union of the base and micro wire families\n"
        "(`F_subset_B_union_M_real`). The three tables are exact assets of the 42-term\n"
        "construction under\n"
        "`data/k42/`.\n"
        f"{shas}\n"
        "Generated by `gen_membership_chunks.py` under\n"
        "`scripts/lean_generators/`; do not edit by hand.\n"
        "No claim identity is asserted in this module.",
    )
    all_text = wrap_words(
        [f"coverSites_{block:03d}.toList" + (" ++" if block + 1 < blocks else "")
         for block in range(blocks)],
        2,
    )
    chain_lines = []
    previous = "membership_000"
    for block in range(1, blocks):
        chain_lines.append(
            f"  have chain_{block:03d} := membershipStep_chain {previous} membership_{block:03d}"
        )
        previous = f"chain_{block:03d}"
    final = f"membershipState_{blocks:03d}"
    body = (
        f"{imports}\n\n{doc}\nset_option autoImplicit false\n"
        f"set_option maxRecDepth {args.max_rec_depth}\n\nnamespace Erdos188.UpperBound\n\n"
        f"/-- Every cover site in order: the {blocks} block lists concatenated. -/\n"
        f"def coverSitesListAll : List SiteWire :=\n{all_text}\n\n"
        "/-- The whole cover table walks from the initial cursor pair to the exhausted pair. -/\n"
        "theorem membership_real :\n"
        f"    {WALK} membershipState_000\n"
        f"      coverSitesListAll = some {final} := by\n"
        + "\n".join(chain_lines) + f"\n  exact {previous}\n\n"
        "/-- The flattened cover site tree is the concatenation of its block lists; the top tree\n"
        "has the block subtrees and `empty` slots at its leaves, so only `SiteTree.toList` on\n"
        "nodes and `empty` is unfolded. -/\n"
        "theorem coverSiteTree_toList : coverSiteTree.toList = coverSitesListAll := by\n"
        "  simp only [coverSiteTree, coverSitesListAll, SiteTree.toList, List.append_nil,\n"
        "    List.append_assoc]\n\n"
        "/-- Every cover site is stored in the base table or in the micro table. -/\n"
        "theorem coverSiteTree_mem_base_or_micro :\n"
        "    ∀ site ∈ coverSiteTree.toList, site ∈ routesSitesB.toList ∨ site ∈ routesSitesM.toList := by\n"
        "  rw [coverSiteTree_toList]\n"
        "  exact membershipStep_sound routesSitesB routesSitesM routesDepthB routesDepthM\n"
        f"    coverSitesListAll membershipState_000 {final} membership_real\n\n"
        "/-- The literal cover family lies in the union of the literal base and micro families. -/\n"
        "theorem F_subset_B_union_M_real :\n"
        "    coverSiteSet coverSiteTree ⊆ wireSet routesSitesB.toList ∪ wireSet routesSitesM.toList :=\n"
        "  coverSiteSet_subset_wireSet_union coverSiteTree routesSitesB routesSitesM\n"
        "    coverSiteTree_mem_base_or_micro\n\n"
        "end Erdos188.UpperBound\n"
    )
    write(checks_dir / "MembershipAll.lean", body)
    print(f"wrote MembershipStates, {blocks} check modules, MembershipAll under {args.out_dir}")

    # negative control, outside the mathematics library
    if args.negative:
        corrupted = list(cover[: args.site_chunk])
        corrupted[args.negative_index] = FOREIGN_SITE
        doc = module_header(
            "Membership negative control",
            f"Block 000 of `cover_sites.tsv` with cover site {args.negative_index} replaced by the\n"
            f"foreign site `{FOREIGN_SITE}`; the walk from `membershipState_000` must fail. This\n"
            "module lives outside `Erdos188/` and is checked with `lake env lean`; it is not part of\n"
            f"the mathematics library.\n{generated}",
        )
        body = (
            "import Erdos188.UpperBound.Data.MembershipStates\n"
            "import Erdos188.UpperBound.Data.SitesRoutesB\n"
            "import Erdos188.UpperBound.Data.SitesRoutesM\n\n"
            f"{doc}\n{options}\nnamespace Erdos188.UpperBound\n\n"
            f"/-- Block 000 with cover site {args.negative_index} replaced by a foreign site. -/\n"
            "def coverSitesCorrupted_000 : SiteTree :=\n"
            f"{site_tree_text(corrupted, 0, args.site_chunk, site_bits, 2)}\n\n"
            "/-- The corrupted block fails the walk. -/\n"
            "theorem membershipCorrupted_000 :\n"
            f"    {WALK} membershipState_000\n"
            "      coverSitesCorrupted_000.toList = none := by\n"
            "  decide +kernel\n\n"
            "end Erdos188.UpperBound\n"
        )
        write(args.negative_dir / "MembershipNegative_000.lean", body)
        print(f"wrote the negative control under {args.negative_dir}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA_DIR)
    parser.add_argument("--out-dir", type=Path, required=True,
                        help="fresh regeneration root; never the committed Erdos188/UpperBound")
    parser.add_argument("--site-chunk", type=int, default=4096,
                        help="cover sites per block (power of two; must match the cover lane)")
    parser.add_argument("--max-rec-depth", type=int, default=100000,
                        help="maxRecDepth for the generated modules")
    parser.add_argument("--negative", action="store_true", help="also write the negative control")
    parser.add_argument("--negative-dir", type=Path, default=DEFAULT_NEGATIVE_DIR)
    parser.add_argument("--negative-index", type=int, default=2049,
                        help="position in block 000 replaced by the foreign site")
    args = parser.parse_args()
    try:
        generate(args)
    except GenerationRefused as error:
        raise SystemExit(str(error)) from None


if __name__ == "__main__":
    main()
