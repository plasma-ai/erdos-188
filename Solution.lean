import Erdos188.FinalAssembly

/-!
# Proof of the bounds for Erdős Problem 188

Comparator checks the two theorems in this module against the Mathlib-only
statements in `Challenge.lean`.
-/

namespace Erdos188

/-- Every coloring with no red unit pair has a blue seven-term unit-step
progression, so every admissible length is at least eight. -/
theorem lower_bound : ∀ k ∈ s, 8 ≤ k :=
  lower_bound_proved

/-- Some coloring with no red unit pair has no blue 42-term unit-step
progression. -/
theorem upper_bound : 42 ∈ s :=
  upper_bound_proved

end Erdos188
