import Erdos188.LowerBound.Main
import Erdos188.UpperBound.Final
import Erdos188.UpperBound.Transfer

/-!
# The bounds `8 ≤ K* ≤ 42`

The lower bound is the seven-term obstruction of `Erdos188.LowerBound`. The
upper bound transfers the periodic disk coloring of `Erdos188.UpperBound` to
the formal-conjectures statement.
-/

set_option autoImplicit false

namespace Erdos188

/-- Every admissible length is at least eight. -/
theorem lower_bound_proved : ∀ k ∈ s, 8 ≤ k :=
  LowerBound.erdos188_lower_bound

/-- The length 42 is admissible. -/
theorem upper_bound_proved : 42 ∈ s := by
  obtain ⟨redSet, hred, hhits⟩ := UpperBound.k42_real
  exact UpperBound.mem_s_of_hits redSet hred hhits

end Erdos188
