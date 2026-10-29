module

public import Erdos188.UpperBound.SafetyDataExtra

/-!
# Chaining surjectivity ranges by explicit totals

The one lemma the generated `Checks/SafetyFamilies.lean` needs to chain the
per-chunk surjectivity checks of `SafetyDataExtra`: the range bounds of the
combined check are given as literals and the two arithmetic side conditions
are separate hypotheses, so that elaboration never has to evaluate `surjCheck`
to unify a sum of literals with a literal. It is kept in its own module so
that the generated chunk modules importing `SafetyDataExtra` do not depend on
it.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- Two consecutive passing ranges pass as one range, with the next start and the total length
given explicitly. -/
theorem surjCheck_chainAt {perm inv : OrdTree} {depth n lo first second lo' : ℕ} (total : ℕ)
    (firstPass : surjCheck perm inv depth n lo first = true)
    (secondPass : surjCheck perm inv depth n lo' second = true)
    (startEq : lo + first = lo') (totalEq : first + second = total) :
    surjCheck perm inv depth n lo total = true := by
  subst startEq totalEq
  exact surjCheck_chain firstPass secondPass

end Erdos188.UpperBound
