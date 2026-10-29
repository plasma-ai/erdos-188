module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Erdős Problem 188: unit-step progressions in the plane

Let `K*` be the least `k` for which the plane can be colored red and blue with
no two red points at distance one and no `k` blue points of the form
`z, z + d, …, z + (k - 1) d` with `‖d‖ = 1`. The start `z` and the direction of
the unit vector `d` are arbitrary, and the length counts points, not gaps.

**Claim.** `8 ≤ K* ≤ 42`.

The previously published bounds are `6 ≤ K* ≤ 6330`: the lower bound is due to
Tsaturian (Electron. J. Combin. 24(4), 2017) and the upper bound to Currier,
Mody, Xie, and Zhang (arXiv:2606.17194). Carson Crocker independently and
concurrently obtained `7 ≤ K* ≤ 60` (Zenodo, doi:10.5281/zenodo.23405962). To
our knowledge, both bounds proved here are new. Thomas F. Bloom catalogs the
question as
[Erdős Problem 188](https://www.erdosproblems.com/188).

The definitions below are copied verbatim from `formal-conjectures`
(`FormalConjectures/ErdosProblems/188.lean` and
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` at commit
`8adf5b7d199d83d7c69d2f89d0e7327362ead98a`). There the plane is `ℂ`, and
`Erdos188.s` is the set of admissible lengths `k`, so that `K*` is its least
element. The set is upward closed, since a coloring with no blue `k`-term
progression has no longer one either.

The two theorems below have deliberate proof holes. `Solution.lean` supplies
their proofs, and Comparator checks them against these statements.
-/

@[expose] public section

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `s.IsAPOfLengthWith l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.
-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

namespace Erdos188

/--
The set of numbers $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1.
-/
def s := { k : ℕ | ∃ blue : Set ℂ,
  (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) ∧
    ¬ (∃ᵉ (bs ⊆ blue) (z) (d), ‖d‖ = 1 ∧ bs.IsAPOfLengthWith k z d) }

/-- Every coloring with no red unit pair has a blue seven-term unit-step
progression, so every admissible length is at least eight. -/
theorem lower_bound : ∀ k ∈ s, 8 ≤ k := by
  sorry

/-- Some coloring with no red unit pair has no blue 42-term unit-step
progression. -/
theorem upper_bound : 42 ∈ s := by
  sorry

end Erdos188
