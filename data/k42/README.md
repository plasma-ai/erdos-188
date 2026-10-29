# The six construction files of the 42-term disk coloring

The six gold files in this directory are the finite object from which the
$K_*\le42$ Lean proof under `Erdos188/UpperBound/` is generated: the four disk
families of the construction, the ordered witness table and the covering
certificate. Beside them sit the two orbit tables they were produced from and
`manifest.json`, which records the byte counts and SHA-256 identities of the
six files and the inputs they were produced from. The files themselves
establish nothing; the Lean modules generated from them, and checked by Lean,
do.

## Regeneration

The 1,518 generated modules under `Erdos188/UpperBound/Data/` and
`Erdos188/UpperBound/Checks/` are produced from these files by the Python
programs in `scripts/` (standard library only). From the repository root,

```sh
git lfs pull                  # the five large files are LFS objects
python3 scripts/regenerate.py
```

exports the route and safety certificate from the six files
(`scripts/export_certificate.py`), runs the four generators in
`scripts/lean_generators/` into a fresh directory and compares the result with
the committed `Data/` and `Checks/` by file name and raw bytes. The exported
certificate is not committed: it is reproduced byte for byte by every export,
and the generated modules carry its SHA-256 and every record they replay.

The six files are in turn produced from the two orbit tables by
`scripts/construction/main.py`:

```sh
python3 scripts/construction/main.py --search --out-dir OUT/search
python3 scripts/construction/main.py --witness OUT/search/tree_witness.txt \
    --out-dir OUT/k42 --expect-manifest data/k42/manifest.json
```

The search finds the covering tree afresh and writes its tree witness, in about
a quarter of an hour; `--compact` recovers the same witness from
`cover_tree.cert` and `cover_sites.tsv` in seconds. The compilation writes the
six files and `manifest.json`, equal byte for byte to the committed ones, and
`--expect-manifest` compares their byte counts and SHA-256 with the committed
manifest. `--orbits` reduces `carriers.tsv` and `plugs.tsv` back to the two
orbit tables.

## Inputs and products

| File | Role |
| --- | --- |
| `carrier_orbits.tsv` | the carrier orbit table: one row per rotation orbit of $\mathcal S$, holding its least member |
| `plug_orbits.tsv` | the plug orbit table: one row per rotation orbit of $\mathcal P$, holding its least member |
| `carriers.tsv` | $\mathcal S$, the full carrier family |
| `plugs.tsv` | $\mathcal P$, the plug family |
| `base.tsv` | $\mathcal B=(\mathcal S\setminus\mathcal E)\cup\mathcal P$, where $\mathcal E$ is the family of the 30 carriers that conflict with a plug |
| `micro_representatives.tsv` | $\mathcal M$, the micro representatives: the distinct cell-service disks of the micro-served leaves of the covering tree |
| `cover_sites.tsv` | $\mathcal F$, the rational-lexicographic interleaving of $\mathcal B$ and $\mathcal M$; its zero-based rows are the certificate's ordinals |
| `cover_tree.cert` | the covering tree: a 19-line header, one record per cell in preorder and an `END` line |

The two orbit tables are the construction's inputs. They record the choices of
the construction's design search: one row per rotation orbit of the family,
holding the least member of that orbit in the tables' rational-lexicographic
order, in the same grammar as the six files. The carrier orbit table has 3,240
rows (the origin's fixed orbit and 3,239 orbits of six) and the plug orbit
table 1,844 rows, all orbits of six. Expanding every row to its full orbit
under $\rho(s,t)=(-t,s+t)$ modulo 59, with the radius unchanged, and sorting
the union gives $\mathcal S$ (19,435 rows) and $\mathcal P$ (11,064 rows), so a
$\rho$-closed family and its orbit table determine each other. The other files
are products of the two: $\mathcal B$ by the conflict rule, $\mathcal M$ and
every leaf by the tree witness below, $\mathcal F$ as the sorted disjoint
union of $\mathcal B$ and $\mathcal M$, and every address, ordinal and lift of
the certificate by replaying the witness from the root.
`scripts/construction/main.py` performs these steps; the orbit tables are kept
here as the record of the construction's choices, and the design search that
made them is not part of this repository.

For a rational triple $q=(s,t,r)$, set

$$
\begin{aligned}
\lambda&=21/100,\\
b(s,t)&=\lambda(s+t/2,\sqrt3\,t/2),\\
D(q)&=\{x\in\mathbb R^2:\|x-b(s,t)\|\le r\},\\
U(A)&=\bigcup_{q\in A}\ \bigcup_{n\in\mathbb Z^2}
       \bigl(D(q)+b(59n)\bigr).
\end{aligned}
$$

With $\mathcal B$ and $\mathcal M$ the sets of triples in their tables, the red
set is

$$
R=U(\mathcal B)\cup\bigcup_{k=0}^{5}g^kU(\mathcal M),\qquad
g(x,y)=((x-\sqrt3y)/2,(\sqrt3x+y)/2).
$$

The carrier family is a proof family, not a red component: the safety
argument needs $\mathcal S$ unit-independent, $\mathcal B$ unit-independent,
and $\mathcal M$ safe against $\mathcal P$ and contained in lifted carriers,
and the covering argument needs the certificate to cover every location and
direction with disks of $\mathcal F$.

## Gold identities

These six files are the gold set: their bytes are the identity of the finite
object the proof is generated from. They are never edited by hand. The
exporter and the generators read the identities from `manifest.json` and
refuse any input whose byte count or SHA-256 differs; the generated modules
quote the same digests.

Five of the six files, all over 1 MB, are Git LFS objects: `base.tsv`,
`carriers.tsv`, `plugs.tsv`, `cover_sites.tsv` and `cover_tree.cert`. Their
committed blobs are pointers whose `oid` is the SHA-256 below,
`micro_representatives.tsv` is an ordinary blob, and a clone needs
`git lfs pull` before the scripts read this directory. The two orbit tables,
both under 1 MB, are ordinary blobs.

| File | Bytes | Rows or records | SHA-256 |
| --- | ---: | ---: | --- |
| `base.tsv` | 3,934,547 | 30,469 | `7a8231e89a49e6362114a1972b96b5580d3e56f5da21f23f2e10e54f894f5f9e` |
| `carriers.tsv` | 2,648,567 | 19,435 | `8f3e5195055f7270ae1ea4bfa9ccf6dbad580f3519bd134367b6bfae5ee94efd` |
| `plugs.tsv` | 1,289,786 | 11,064 | `ff7d237f892bfa4b2b805836ff2e3f7367d3cfbcc41dae66284a8b22d6eff249` |
| `micro_representatives.tsv` | 625,531 | 10,108 | `4af5864472f88e5f65215c1ff5088ab08193113841d9ce09ea872fdd6ba28877` |
| `cover_sites.tsv` | 4,560,078 | 40,577 | `6d2115abac144af8a3f1da30d2ea235f0ef8b6ec74a28450dee606027af81cef` |
| `cover_tree.cert` | 9,649,387 | 411,033 | `643180ce10a52ebaf5d7a1fe0c63b54c3c0b592fbe335bbd8ad59f9d3a32e207` |

The payload is 22,707,896 bytes. The manifest's `files` block carries the same
six rows, and its `source` block names the two orbit tables by path and row
count, the identities of the two families expanded from them and the tree
witness record. The manifest assigns the roles; a filename or a
certificate header label does not. In particular the full carrier family and
the carriers kept in the base are different families.

## The tree witness

The witness is the covering tree's choice content: one line per record in
preorder, `D` and `T` for the splits and `S j s t r` for a leaf served at step
$j$ by the disk $(s,t,r)$, under a header binding it to the SHA-256 of
`carriers.tsv` and `plugs.tsv` and to the micro radius factor $147/400$. A
leaf names its disk by its exact triple, never by a table position. The
witness of this object has SHA-256
`0b75b2c23cece10f3eef95d00b92c648bf3a2f0455a95e2e364e1d70386173f0`,
41,195,486 bytes and 411,033 records. It is not committed: the certificate
`cover_tree.cert` is the retained witness of the covering, and its header
names the witness's digest.

## Grammar and conventions

Each TSV holds header-free rows of three tab-separated exact rationals in the
order `(s, t, r)`, ended by LF. An integer is spelled without sign, leading
zero or negative zero; a fraction is a reduced signed numerator over a
denominator above one, as Python's `str(Fraction)` spells them. The first two
fields are axial coordinates in $[0,59)$ and the third a physical Euclidean
radius in $(0,1/2)$. Every table is strictly increasing in numeric rational
order, so it equals its own sorted set and has one serialization. The readers
check this grammar and domain on every row and repair nothing.

The certificate's 19 header lines describe its own object:

```text
PERIODIC_DISK_COVER_TREE_V1
carriers_sha256 <identity of carriers.tsv>
plugs_sha256 <identity of plugs.tsv>
base_sha256 <identity of base.tsv>
micro_representatives_sha256 <identity of micro_representatives.tsv>
cover_sites_sha256 <identity of cover_sites.tsv>
tree_witness_sha256 <identity of the tree witness>
micro_radius_factor 147/400
period 59
length 42
step_interval -21 20
direction_depth 16
translation_depth 15
tree_records 411033
direction_records 80952
translation_records 62282
leaf_records 267799
base_leaves 257499
micro_leaves 10300
```

The two depths are the greatest direction and translation depth of any cell,
leaves included. The records follow in preorder, with single spaces and
canonical integers:

```text
D d i e h k
T d i e h k
S d i e h k j ordinal lift_s lift_t
```

A `D` record splits the cell $(d,i;e,h,k)$ into $(d+1,2i)$ and $(d+1,2i+1)$,
a `T` record into $(e+1,2h+\epsilon,2k+\delta)$ in the order
$(0,0),(0,1),(1,0),(1,1)$, and an `S` record serves the cell at step $j$ by the
disk at row `ordinal` of $\mathcal F$ under the lift `(lift_s, lift_t)`. Every
address is derived from the root, and the root subtree closes exactly at the
last record, so the leaf count is $1+D+3T$. One `END` line ends the file.

An ordinal is a zero-based row position $z$ in $\mathcal F$; the one-based disk
label in the covering argument is $\ell=z+1$. Moving a center by $-59(a,b)$
changes the lift of the same periodic copy by $+(a,b)$, so a re-encoding of
either table owes a checked total ordinal map carrying the lifts with it. Do
not replace `cover_sites.tsv` by a concatenation, a deduplicated table or a
text-lexicographic sort; the covering replay requires it strictly increasing
and equal to the merged $\mathcal B$ and $\mathcal M$ at every ordinal.

## Admitted domain

The readers admit at most 300,000 rows per table, 1,536 bits per rational
component and 2,048 bytes per line. This object lies inside every ceiling: its
largest table has 40,577 rows, the certificate 411,033 records, the depths are
16 and 15, its widest component has 1,462 bits and its longest line 1,768
bytes; the orbit tables' widest component has 1,460 bits and their longest
line 1,763 bytes. The header states the observed depths, not the ceilings.
