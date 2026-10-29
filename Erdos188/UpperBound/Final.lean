import Erdos188.UpperBound.Construction
import Erdos188.UpperBound.Checks.SafetyAll

/-!
# The unconditional theorem

The three kernel-checked safety theorems of `Checks.SafetyAll` discharge the
hypotheses of `Construction.redSet_unitIndependent_of_safety`, giving unit
independence of the red set, and together with `redSet_hits42_real` the
existence of a unit-independent plane set meeting every 42-term unit-step
progression (`k42_real`). The literal tables are the construction files in
`data/k42/`. The generic whole-plane argument is outlined in the repository
`README.md`. No claim identity is asserted in
this module.
-/

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- No two points of the red set are at distance one. -/
theorem redSet_unitIndependent_real : UnitIndependent redSet :=
  redSet_unitIndependent_of_safety unitIndependent_S_real unitIndependent_B_real crossSafe_MP_real

/-- A unit-independent set of the plane meeting every 42-term unit-step progression. -/
theorem k42_real : ∃ redSet : Set Plane, UnitIndependent redSet ∧ Hits 42 redSet :=
  ⟨redSet, redSet_unitIndependent_real, redSet_hits42_real⟩

end Erdos188.UpperBound
