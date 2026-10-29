# Erdős Problem 188

This Lean 4 project proves new bounds for [Erdős Problem 188](https://www.erdosproblems.com/188), as cataloged by Thomas F. Bloom. Let `K*` be the least `k` for which the plane can be colored red and blue with no two red points at distance one and no `k` blue points `z, z + d, …, z + (k - 1)d` with `|d| = 1`. We prove

```
8 ≤ K* ≤ 42.
```

The previously published bounds are `6 ≤ K* ≤ 6330`. Carson Crocker independently and concurrently obtained `7 ≤ K* ≤ 60`. To our knowledge, both bounds proved here are new. The exact value of `K*` remains open.

## Literature and scope

Erdős and Graham posed the question in *Old and new problems and results in combinatorial number theory: van der Waerden's theorem and related topics* (L'Enseignement Mathématique, 1979). The unit-step restriction matters: without it, van der Waerden's theorem rules out every finite length. Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus proved `K* ≥ 5` in *Euclidean Ramsey theorems. II* (1975). Tsaturian proved `K* ≥ 6` in [*A Euclidean Ramsey result in the plane*](https://doi.org/10.37236/7148) (2017). That bound has an independent Lean formalization against the same formal-conjectures statement, [`jsp-000181-erdos188-lean`](https://github.com/baobingzhang/jsp-000181-erdos188-lean), submitted to the Justin Sun Prize as JSP-000181. Conlon and Fox's general bounds give a planar estimate of `10^10`, and Currier, Mody, Xie, and Zhang improved it to `6330` in [*Improved bounds for lines and 1-separated sets in Euclidean Ramsey theory*](https://arxiv.org/abs/2606.17194).

Carson Crocker posted `7 ≤ K* ≤ 60` on October 7, 2026 in [*Erdős Problem #188: 7 ≤ k ≤ 60, with code and certificates*](https://doi.org/10.5281/zenodo.23405962), first deposited as [10.5281/zenodo.23151059](https://doi.org/10.5281/zenodo.23151059). His lower bound follows Arman and Tsaturian's three-dimensional argument, with Tsaturian's planar argument as the model, and his upper bound is a periodic coloring by red cells of several sizes in the cell framework of Currier, Mody, Xie, and Zhang. Both halves are computer-assisted and unrefereed, and Alexander Towell has published external checks of the two finite components of the upper bound. The bounds proved here were obtained independently of that work, by different arguments.

The "to our knowledge" novelty claim reflects targeted searches on October 7 and October 29, 2026 of arXiv, the web, and Bloom's problem entry and its discussion thread; the first also covered the papers citing Tsaturian's result. They found nothing beyond `6 ≤ K* ≤ 6330` and Crocker's `7 ≤ K* ≤ 60`.

**Lower bound.** `Erdos188/LowerBound/` proves that every coloring of the plane with no red unit pair contains seven collinear blue points with consecutive spacing one. The argument restricts a counterexample to the algebraic plane and averages over a translation- and rotation-invariant measure on its labelings. A fourteen-point pattern inequality, checked over all 210 admissible patterns, bounds the red–red correlation. The spectral measure of the red indicator is radial on the ordinary characters, and a nonnegative Bessel kernel `F(t) = 191 + Σ Cₙ J₀(√n t)`, certified on `[0, 81]` by rational polynomial approximation and beyond by an energy bound, gives the contradiction. The spectral rigidity and invariant-mean inputs come from OpenAI's [*The Euclidean plane is not five-colorable*](https://github.com/openai/math/tree/main/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026) and its Lean formalization, ported in `OAI/`.

**Upper bound.** `Erdos188/UpperBound/` constructs an explicit red set. Write `b(s, t) = (21/100)(s + t/2, √3 t/2)` for the axial coordinates of a triangular lattice, let `U(F)` be the union of the closed disks of a finite family `F` of rational records `(s, t, r)` together with all their translates by `b(59ℤ²)`, and let `g` be rotation by `π/3`. For the base family `B` and the micro family `M` in `data/k42/`, the red set is

```
R = U(B) ∪ g⁰U(M) ∪ g¹U(M) ∪ … ∪ g⁵U(M).
```

*Safety* (`Families`, `Safety`, `ExactSafety`). Two auxiliary families, the carriers `S` and the plugs `P`, organize the proof that `R` has no unit pair. Exact finite checks show that `U(S)` and `U(B)` are unit-independent and that no point of `U(M)` is at distance one from `U(P)`, with strict annulus exclusion rather than containment at the forbidden distance. Route checks show that every micro disk lies in a lifted carrier, that the base lies in the carrier-and-plug union, and that the families are invariant under the rotation. A carrier composition theorem turns these facts into unit independence of all of `R`.

*Covering* (`Directions`, `Covering`, `ExactCover`). A covering certificate subdivides a fundamental cell of translations and a sector of directions into closed cells, boundaries included, and proves at every leaf that the 42-point progressions starting and pointing in that cell all meet a disk of `B ∪ M`. Periodicity and rotation invariance extend this to every start in the plane and every unit direction, and every covering disk lies in `R`. No direction or start is sampled.

`Final.lean` combines the two halves for the same set into `k42_real`. The 1518 modules under `Erdos188/UpperBound/Data/` and `Checks/` hold the literal tables and one kernel-checked theorem per certificate chunk. `python3 scripts/regenerate.py` re-exports the certificate from the six files in `data/k42/` (after `git lfs pull`), regenerates all 1518 modules and checks that they equal the committed ones byte for byte; it uses only the Python standard library and takes about a minute. `scripts/construction/main.py` produces the six files themselves from the two orbit tables in `data/k42/`: `--search` finds the covering tree afresh in about a quarter of an hour, `--compact` recovers the same tree witness from `cover_tree.cert` in seconds, and the default mode compiles the six files from that witness, byte for byte equal to the committed ones. The design search that chose the orbit tables is not part of this repository.

## Publication layout

`Challenge.lean` states both bounds using only Mathlib imports. Its two `sorry` proofs are deliberate: this file contains the statements to audit. The definitions of the admissible set `Erdos188.s` and of `Set.IsAPOfLengthWith` are copied verbatim from [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/8adf5b7d199d83d7c69d2f89d0e7327362ead98a/FormalConjectures/ErdosProblems/188.lean), where the plane is `ℂ`. `Solution.lean` imports the proof development and supplies the two theorems. `comparator.json` selects their names and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

`Erdos188/Statement.lean` repeats the formal-conjectures definitions for the proof development. `Erdos188/UpperBound/Transfer.lean` carries the construction's red set in `EuclideanSpace ℝ (Fin 2)` to membership in `Erdos188.s`, and `Erdos188/FinalAssembly.lean` combines the two bounds. The hand-written development and `Challenge.lean` use the module system. The 1518 generated modules are ordinary Lean files, and so are the files that import them (`UpperBound/Construction.lean`, `UpperBound/Final.lean`, `FinalAssembly.lean`, and `Solution.lean`), since a module cannot import an ordinary file.

`OAI/` holds 34 modules from the `lean/` directory of [openai/math](https://github.com/openai/math) at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under its Apache 2.0 license (`OAI/LICENSE`). They are the import closure of `OAI.Analysis.PlaneSpectrum.Ergodicity`, `OAI.Analysis.PlaneSpectrum.CircleDecay`, and `OAI.Geometry.PlaneColoring.BorelTransfer`. Their `import Mathlib` headers are replaced by the specific Mathlib modules each file needs. Like the rest of the hand-written development, they are converted to the module system: each file starts with `module`, uses `public import`, and declares `@[expose] public section`. Because a public import does not re-export a dependency's private imports, four files import Mathlib modules they previously reached transitively (`InnerProductSpace.Dual` and `InnerProductSpace.Adjoint`, `CStarAlgebra.GelfandDuality`, `LpSpace.InfiniteSum`). Porting to the toolchain and the module system changed these proofs: two `Measurable.piecewise` steps became `Measurable.ite` (in `CompactFactors/Kernels.lean` and `CompactFactors/AlgebraModels.lean`); `PlaneSpectrum/SpectralMeasure.lean` raises `synthInstance.maxHeartbeats` for `adjoin_comm`; `PlaneSpectrum/Representations.lean` uses `lipschitzWith` for a deprecated name; the statements of `wild_line_average_zero` and `wild_line_average_re_zero` pass the bound `B` explicitly; `pickSupport` in `PlaneColoring/BorelTransfer.lean` is no longer `private`, since an exposed definition uses it; and one `measurable_const` there names its point explicitly. Two deprecated Mathlib imports were also renamed.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warnings. The proofs in `Solution` can also be built directly with `lake build Solution`, and the lower bound alone with `lake build Erdos188.LowerBound.Main`.

The upper-bound tables make the full build expensive. Lake runs one `lean` process per worker thread, and the largest generated module needs about 6 GB, so cap the thread count to fit the available memory. With `LEAN_NUM_THREADS=4`, a full build takes about an hour and peaks near 21 GB.
