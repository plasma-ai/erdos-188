module

public import Erdos188.UpperBound.Families
public import Erdos188.Statement
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# From a hitting red set to an admissible length

`Erdos188.s` colors `ℂ` and asks for no blue progression, while the
construction works in `EuclideanSpace ℝ (Fin 2)` and asks the red set to meet
every progression. The real-linear isometry `Complex.orthonormalBasisOneI.repr`
carries one form to the other: the blue set is the complement of the pulled
back red set, and every blue progression would map to a progression that the
red set misses.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- A unit-independent red set meeting every `k`-term unit-step progression
makes `k` an admissible length. -/
theorem mem_s_of_hits {k : ℕ} (redSet : Set Plane) (hred : UnitIndependent redSet)
    (hhits : Hits k redSet) : k ∈ Erdos188.s := by
  let φ := Complex.orthonormalBasisOneI.repr
  refine ⟨{c | φ c ∉ redSet}, ?_, ?_⟩
  -- the non-blue points map into the red set, which has no unit pair
  · rintro x ⟨-, hx⟩ y ⟨-, hy⟩ -
    have hx' : φ x ∈ redSet := not_not.mp hx
    have hy' : φ y ∈ redSet := not_not.mp hy
    rw [← φ.dist_map]
    exact hred _ hx' _ hy'
  -- the red set meets the image of every blue progression
  · rintro ⟨bs, hbs, z, d, hd, -, rfl⟩
    have hφd : ‖φ d‖ = 1 := by rw [φ.norm_map, hd]
    obtain ⟨index, hindex⟩ := hhits (φ z) (φ d) hφd
    have hmem : z + index.val • d ∈ {z + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} :=
      ⟨index.val, by exact_mod_cast index.isLt, rfl⟩
    apply hbs hmem
    rwa [map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ]

end Erdos188.UpperBound
