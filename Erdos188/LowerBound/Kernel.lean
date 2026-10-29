module

public import Erdos188.LowerBound.Bessel.Tail
public import Erdos188.LowerBound.Certificate.Soundness

/-!
# Positivity of the kernel

`F(t) = 191 + ∑ₙ Cₙ J₀(√n t) ≥ 0` for every `t ≥ 0`: the rational certificate covers
`[0, 81]` and the energy estimate covers `[81, ∞)`.
-/

@[expose] public section

namespace Erdos188.LowerBound

theorem kernelF_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ kernelF t := by
  rcases le_total t 81 with h81 | h81
  · exact Certificate.kernelF_nonneg_of_le ht h81
  · linarith [kernelF_tail h81]

end Erdos188.LowerBound
