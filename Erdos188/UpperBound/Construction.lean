import Erdos188.UpperBound.Checks.CoverAll
import Erdos188.UpperBound.Checks.MembershipAll
import Erdos188.UpperBound.Checks.RoutesAll
import Erdos188.UpperBound.Covering
import Erdos188.UpperBound.Safety

/-!
# The literal red set and its assembled properties

The four semantic families are the wire families of the literal role tables,
and the red set is the base union together with the six rotated copies of the
micro union. The literal tables are the construction files in `data/k42/`;
the generated modules under `Data/` and `Checks/` encode those tables and the
kernel-checked certificates over them. The certificates supply periodicity and
rotation invariance of the red set, the inclusion of the cover family in the
red set, and hence the 42-term hitting property, with no hypothesis left. Unit
independence of the red set is assembled from the containment and rotation
theorems of `Checks.RoutesAll` and the carrier composition of `Safety`,
conditional on the three safety theorems taken as hypotheses here and
supplied by `Checks.SafetyAll` in `Final`: unit independence of the carrier
and base unions and cross-safety of the micro and plug unions. No claim
identity is asserted in this module.
-/

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- The base family: the sites of the literal base table. -/
def baseSet : Set Site := wireSet routesSitesB.toList

/-- The carrier family: the sites of the literal carrier table. -/
def carrierSet : Set Site := wireSet routesSitesS.toList

/-- The plug family: the sites of the literal plug table. -/
def plugSet : Set Site := wireSet routesSitesP.toList

/-- The micro family: the sites of the literal micro table. -/
def microSet : Set Site := wireSet routesSitesM.toList

/-- The red set: the base union together with the six rotated copies of the micro union. -/
def redSet : Set Plane := R baseSet microSet

/-- The red set is invariant under every integer period translation. -/
theorem redSet_periodic : Periodic redSet :=
  periodic_R baseSet microSet

/-- The red set is invariant under the one-step rotation, by the base rotation routes. -/
theorem redSet_rotationInvariant : RotationInvariant redSet :=
  rotationInvariant_R baseSet microSet rotationInvariant_U_B_real

/-- Every cover site is a base site or a micro site. -/
theorem coverSiteSet_subset_base_union_micro : coverSiteSet coverSiteTree ⊆ baseSet ∪ microSet :=
  F_subset_B_union_M_real

/-- The periodic union of the cover family lies in the red set. -/
theorem U_F_subset_redSet : U (coverSiteSet coverSiteTree) ⊆ redSet := by
  intro point membership
  have inUnion := U_mono _ _ coverSiteSet_subset_base_union_micro membership
  rw [U_union] at inUnion
  rcases inUnion with inBase | inMicro
  · exact Or.inl inBase
  · exact Or.inr (subset_C6 (U microSet) inMicro)

/-- Every 42-term unit-step progression meets the red set. -/
theorem redSet_hits42_real : Hits 42 redSet :=
  wholePlane redSet (coverSiteSet coverSiteTree) redSet_periodic redSet_rotationInvariant
    U_F_subset_redSet certified_real

/-- The carrier hypotheses of the literal families from the route theorems and the three safety
theorems taken as hypotheses. -/
theorem carrierHypotheses_of_safety (hS : UnitIndependent (U carrierSet))
    (hB : UnitIndependent (U baseSet)) (hMP : CrossSafe (U microSet) (U plugSet)) :
    CarrierHypotheses (U baseSet) (U carrierSet) (U plugSet) (U microSet) where
  base_independent := hB
  carrier_independent := hS
  base_subset_carrier_union_plug := U_B_subset_S_union_P_real
  micro_subset_carrier := U_M_subset_S_real
  micro_plug_cross_safe := hMP
  base_rotation := rotationInvariant_U_B_real
  carrier_rotation := rotationInvariant_U_S_real
  plug_rotation := rotationInvariant_U_P_real

/-- No two points of the red set are at distance one, given the three safety theorems. -/
theorem redSet_unitIndependent_of_safety (hS : UnitIndependent (U carrierSet))
    (hB : UnitIndependent (U baseSet)) (hMP : CrossSafe (U microSet) (U plugSet)) :
    UnitIndependent redSet :=
  CarrierHypotheses.unitIndependent_red (U baseSet) (U carrierSet) (U plugSet) (U microSet)
    (carrierHypotheses_of_safety hS hB hMP)

/-- A unit-independent set of the plane meeting every 42-term unit-step progression, given the
three safety theorems. -/
theorem k42_statement_of_safety (hS : UnitIndependent (U carrierSet))
    (hB : UnitIndependent (U baseSet)) (hMP : CrossSafe (U microSet) (U plugSet)) :
    ∃ redSet : Set Plane, UnitIndependent redSet ∧ Hits 42 redSet :=
  ⟨redSet, redSet_unitIndependent_of_safety hS hB hMP, redSet_hits42_real⟩

end Erdos188.UpperBound
