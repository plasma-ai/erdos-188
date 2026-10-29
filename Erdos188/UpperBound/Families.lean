module

public import Erdos188.UpperBound.Coordinates
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Semantic periodic disk families

Rational sites and their closed disks, the periodic union `U` of a site set,
the six rotated copies `C6`, the red set `R` of a base and a micro family, the
family roles, and the plane predicates the whole argument is about: unit
independence, cross-safety, periodicity, rotation invariance, and the 42-term
hitting property `Hits`. Sites are rational and need not be normalized; the
set-valued definitions choose no finite storage representation and identify
no source ordinals. The vocabulary follows the construction and
safety argument outlined in the repository `README.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Erdos188.UpperBound

/-- A rational axial center and a rational physical radius. -/
structure Site where
  center : ℚ × ℚ
  radius : ℚ

/-- Normalized representatives and the strict radius domain are separate data. -/
def SiteValid (site : Site) : Prop :=
  0 ≤ site.center.1 ∧ site.center.1 < 59 ∧
    0 ≤ site.center.2 ∧ site.center.2 < 59 ∧
      0 < site.radius ∧ site.radius < (1 / 2 : ℚ)

/-- Cast the rational axial center into the physical Euclidean plane. -/
def siteCenter (site : Site) : Plane :=
  basisMap (ratAxialToReal site.center)

/-- The closed physical disk belonging to one unshifted site. -/
def closedDisk (site : Site) : Set Plane :=
  {point | ‖point - siteCenter site‖ ≤ (site.radius : ℝ)}

/-- The union of every integer period lift of every site in a semantic family. -/
def U (siteSet : Set Site) : Set Plane :=
  {point | ∃ site ∈ siteSet, ∃ lift : ℤ × ℤ,
    ‖point - (siteCenter site + periodVector lift)‖ ≤ (site.radius : ℝ)}

/-- The union of the six rotational images of a physical set. -/
def C6 (points : Set Plane) : Set Plane :=
  {point | ∃ power : Fin 6, ∃ witness ∈ points,
    point = (rotate ^ power.val) witness}

/-- Only the base union and the six rotated micro unions are red. -/
def R (baseSites microSites : Set Site) : Set Plane :=
  U baseSites ∪ C6 (U microSites)

/-- Four semantic roles; these are not different types of site. -/
structure FamilyRoles where
  baseSites : Set Site
  carrierSites : Set Site
  plugSites : Set Site
  microSites : Set Site

/-- The corresponding four roles may also be stated directly as physical sets. -/
structure PhysicalRoles where
  base : Set Plane
  carrier : Set Plane
  plug : Set Plane
  micro : Set Plane

/-- Interpret all four semantic roles using the same periodic-union operation. -/
def FamilyRoles.toPhysical (roles : FamilyRoles) : PhysicalRoles where
  base := U roles.baseSites
  carrier := U roles.carrierSites
  plug := U roles.plugSites
  micro := U roles.microSites

theorem FamilyRoles.toPhysical_base (roles : FamilyRoles) :
    roles.toPhysical.base = U roles.baseSites := rfl

theorem FamilyRoles.toPhysical_carrier (roles : FamilyRoles) :
    roles.toPhysical.carrier = U roles.carrierSites := rfl

theorem FamilyRoles.toPhysical_plug (roles : FamilyRoles) :
    roles.toPhysical.plug = U roles.plugSites := rfl

theorem FamilyRoles.toPhysical_micro (roles : FamilyRoles) :
    roles.toPhysical.micro = U roles.microSites := rfl

/-- Explicit equalities bind independently named physical and semantic roles. -/
structure FamilySemantics (roles : FamilyRoles) (physical : PhysicalRoles) : Prop where
  base_eq : physical.base = U roles.baseSites
  carrier_eq : physical.carrier = U roles.carrierSites
  plug_eq : physical.plug = U roles.plugSites
  micro_eq : physical.micro = U roles.microSites

theorem FamilyRoles.toPhysical_semantics (roles : FamilyRoles) :
    FamilySemantics roles roles.toPhysical :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- No two points of the set are at distance one. -/
def UnitIndependent (points : Set Plane) : Prop :=
  ∀ first ∈ points, ∀ second ∈ points, dist first second ≠ 1

/-- No point of the first set is at distance one from a point of the second. -/
def CrossSafe (firstPoints secondPoints : Set Plane) : Prop :=
  ∀ first ∈ firstPoints, ∀ second ∈ secondPoints, dist first second ≠ 1

/-- Membership is invariant under every integer period translation. -/
def Periodic (points : Set Plane) : Prop :=
  ∀ lift : ℤ × ℤ, ∀ point : Plane,
    point + periodVector lift ∈ points ↔ point ∈ points

/-- Membership is invariant under the one-step physical rotation. -/
def RotationInvariant (points : Set Plane) : Prop :=
  ∀ point : Plane, rotate point ∈ points ↔ point ∈ points

/-- Rotation invariance extends to every power of the rotation. -/
theorem RotationInvariant.pow_mem_iff (points : Set Plane) (invariant : RotationInvariant points)
    (power : ℕ) (point : Plane) : (rotate ^ power) point ∈ points ↔ point ∈ points := by
  induction power with
  | zero => simp
  | succ power inductionHypothesis =>
      rw [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply, invariant,
        inductionHypothesis]

/-- Every length-`count` unit-step progression has a point in the set. -/
def Hits (count : ℕ) (points : Set Plane) : Prop :=
  ∀ start direction : Plane, ‖direction‖ = 1 →
    ∃ index : Fin count, start + (index.val : ℝ) • direction ∈ points

/-- The exact physical premises of the later carrier theorem. -/
structure CarrierHypotheses
    (base carrier plug micro : Set Plane) : Prop where
  base_independent : UnitIndependent base
  carrier_independent : UnitIndependent carrier
  base_subset_carrier_union_plug : base ⊆ carrier ∪ plug
  micro_subset_carrier : micro ⊆ carrier
  micro_plug_cross_safe : CrossSafe micro plug
  base_rotation : RotationInvariant base
  carrier_rotation : RotationInvariant carrier
  plug_rotation : RotationInvariant plug

/-- Pull back the same hypothesis record without adding a semantic premise. -/
abbrev FamilyRoles.SafetyHypotheses (roles : FamilyRoles) : Prop :=
  CarrierHypotheses (U roles.baseSites) (U roles.carrierSites)
    (U roles.plugSites) (U roles.microSites)

theorem carrierHypotheses_iff_semantic
    (roles : FamilyRoles) (physical : PhysicalRoles)
    (binding : FamilySemantics roles physical) :
    CarrierHypotheses physical.base physical.carrier physical.plug physical.micro ↔
      roles.SafetyHypotheses := by
  rw [binding.base_eq, binding.carrier_eq, binding.plug_eq, binding.micro_eq]

/-- The part of the carrier cross-safe from the plug set. -/
def safeCarrier (carrier plug : Set Plane) : Set Plane :=
  {point | point ∈ carrier ∧ ∀ plugPoint ∈ plug, dist point plugPoint ≠ 1}

theorem mem_closedDisk_iff (site : Site) (point : Plane) :
    point ∈ closedDisk site ↔ ‖point - siteCenter site‖ ≤ (site.radius : ℝ) :=
  Iff.rfl

theorem mem_U_iff (siteSet : Set Site) (point : Plane) :
    point ∈ U siteSet ↔ ∃ site ∈ siteSet, ∃ lift : ℤ × ℤ,
      ‖point - (siteCenter site + periodVector lift)‖ ≤ (site.radius : ℝ) :=
  Iff.rfl

/-- The physical sum in `U` is exactly the axial center plus the lifted period. -/
theorem siteCenter_add_periodVector (site : Site) (lift : ℤ × ℤ) :
    siteCenter site + periodVector lift =
      basisMap (ratAxialToReal site.center + (59 : ℝ) • intAxialToReal lift) := by
  exact (map_add basisMap (ratAxialToReal site.center)
    ((59 : ℝ) • intAxialToReal lift)).symm

theorem mem_U_axial_iff (siteSet : Set Site) (point : Plane) :
    point ∈ U siteSet ↔ ∃ site ∈ siteSet, ∃ lift : ℤ × ℤ,
      ‖point - basisMap
        (ratAxialToReal site.center + (59 : ℝ) • intAxialToReal lift)‖ ≤
          (site.radius : ℝ) := by
  simp only [mem_U_iff, siteCenter_add_periodVector]

theorem U_mono (siteSet otherSites : Set Site) (inclusion : siteSet ⊆ otherSites) :
    U siteSet ⊆ U otherSites := by
  rintro point ⟨site, membership, lift, bound⟩
  exact ⟨site, inclusion membership, lift, bound⟩

theorem U_union (siteSet otherSites : Set Site) :
    U (siteSet ∪ otherSites) = U siteSet ∪ U otherSites := by
  apply Set.ext
  intro point
  constructor
  · rintro ⟨site, membership, lift, bound⟩
    rcases membership with membership | membership
    · exact Or.inl ⟨site, membership, lift, bound⟩
    · exact Or.inr ⟨site, membership, lift, bound⟩
  · intro membership
    rcases membership with ⟨site, membership, lift, bound⟩ |
      ⟨site, membership, lift, bound⟩
    · exact ⟨site, Or.inl membership, lift, bound⟩
    · exact ⟨site, Or.inr membership, lift, bound⟩

/-- An arbitrary index type is a view of a semantic family, not its storage. -/
theorem mem_U_range_iff {ι : Type*} (sites : ι → Site) (point : Plane) :
    point ∈ U (Set.range sites) ↔ ∃ index : ι, ∃ lift : ℤ × ℤ,
      ‖point - (siteCenter (sites index) + periodVector lift)‖ ≤
        ((sites index).radius : ℝ) := by
  constructor
  · rintro ⟨site, ⟨index, rfl⟩, lift, bound⟩
    exact ⟨index, lift, bound⟩
  · rintro ⟨index, lift, bound⟩
    exact ⟨sites index, ⟨index, rfl⟩, lift, bound⟩

theorem periodic_U (siteSet : Set Site) : Periodic (U siteSet) := by
  intro shift point
  constructor
  · rintro ⟨site, membership, lift, bound⟩
    refine ⟨site, membership, lift - shift, ?_⟩
    have difference :
        point - (siteCenter site + periodVector (lift - shift)) =
          point + periodVector shift - (siteCenter site + periodVector lift) := by
      rw [periodVector_sub]
      abel
    rw [difference]
    exact bound
  · rintro ⟨site, membership, lift, bound⟩
    refine ⟨site, membership, lift + shift, ?_⟩
    have difference :
        point + periodVector shift - (siteCenter site + periodVector (lift + shift)) =
          point - (siteCenter site + periodVector lift) := by
      rw [periodVector_add]
      abel
    rw [difference]
    exact bound

/-- Shift a representative center by minus an integer period. -/
def shiftSite (site : Site) (shift : ℤ × ℤ) : Site where
  center := (site.center.1 - 59 * (shift.1 : ℚ),
    site.center.2 - 59 * (shift.2 : ℚ))
  radius := site.radius

theorem shiftSite_radius (site : Site) (shift : ℤ × ℤ) :
    (shiftSite site shift).radius = site.radius := rfl

/-- The old lift `lift` is the shifted representative's lift `lift + shift`. -/
theorem shiftSite_center_copy (site : Site) (lift shift : ℤ × ℤ) :
    site.center + (59 : ℚ) • intAxialToRat lift =
      (shiftSite site shift).center + (59 : ℚ) • intAxialToRat (lift + shift) := by
  apply Prod.ext <;>
    simp [shiftSite, intAxialToRat, smul_eq_mul] <;> ring

theorem siteCenter_shiftSite (site : Site) (shift : ℤ × ℤ) :
    siteCenter (shiftSite site shift) = siteCenter site - periodVector shift := by
  change basisMap (ratAxialToReal (shiftSite site shift).center) =
    basisMap (ratAxialToReal site.center) -
      basisMap (59 * (shift.1 : ℝ), 59 * (shift.2 : ℝ))
  rw [← map_sub]
  congr 1
  apply Prod.ext <;> simp [shiftSite, ratAxialToReal]

/-- Per-index shifts preserve the union even when several indices name one site. -/
theorem U_range_shiftSite {ι : Type*}
    (sites : ι → Site) (shifts : ι → ℤ × ℤ) :
    U (Set.range (fun index => shiftSite (sites index) (shifts index))) =
      U (Set.range sites) := by
  apply Set.ext
  intro point
  constructor
  · rintro ⟨site, ⟨index, rfl⟩, lift, bound⟩
    refine ⟨sites index, ⟨index, rfl⟩, lift - shifts index, ?_⟩
    have center_eq :
        siteCenter (shiftSite (sites index) (shifts index)) + periodVector lift =
          siteCenter (sites index) + periodVector (lift - shifts index) := by
      rw [siteCenter_shiftSite, periodVector_sub]
      abel
    change ‖point - (siteCenter (shiftSite (sites index) (shifts index)) +
      periodVector lift)‖ ≤ ((sites index).radius : ℝ) at bound
    rw [center_eq] at bound
    exact bound
  · rintro ⟨site, ⟨index, rfl⟩, lift, bound⟩
    refine ⟨shiftSite (sites index) (shifts index), ⟨index, rfl⟩,
      lift + shifts index, ?_⟩
    have center_eq :
        siteCenter (shiftSite (sites index) (shifts index)) +
            periodVector (lift + shifts index) =
          siteCenter (sites index) + periodVector lift := by
      rw [siteCenter_shiftSite, periodVector_add]
      abel
    change ‖point - (siteCenter (shiftSite (sites index) (shifts index)) +
      periodVector (lift + shifts index))‖ ≤ ((sites index).radius : ℝ)
    rw [center_eq]
    exact bound

/-- Rotate the rational center; representative validity is not assumed. -/
def rotateSite (site : Site) : Site where
  center := axialRotateRat site.center
  radius := site.radius

theorem rotateSite_radius (site : Site) :
    (rotateSite site).radius = site.radius := rfl

theorem siteCenter_rotateSite (site : Site) :
    siteCenter (rotateSite site) = rotate (siteCenter site) := by
  change basisMap (ratAxialToReal (axialRotateRat site.center)) =
    rotate (basisMap (ratAxialToReal site.center))
  rw [← axialRotateRat_cast, rotate_basisMap]

/-- The integer lattice equivalence accounts for every lift in both directions. -/
theorem rotate_image_U (siteSet : Set Site) :
    rotate '' U siteSet = U (rotateSite '' siteSet) := by
  apply Set.ext
  intro point
  constructor
  · rintro ⟨witness, ⟨site, membership, lift, bound⟩, rfl⟩
    refine ⟨rotateSite site, ⟨site, membership, rfl⟩, axialRotateInt lift, ?_⟩
    change ‖rotate witness - (siteCenter (rotateSite site) +
      periodVector (axialRotateInt lift))‖ ≤ (site.radius : ℝ)
    rw [siteCenter_rotateSite, ← rotate_periodVector, ← map_add, ← map_sub,
      rotate.norm_map]
    exact bound
  · rintro ⟨site, ⟨original, membership, rfl⟩, lift, bound⟩
    refine ⟨rotate.symm point, ?_, rotate.apply_symm_apply point⟩
    refine ⟨original, membership, axialRotateInt.symm lift, ?_⟩
    rw [← rotate.norm_map
      (rotate.symm point - (siteCenter original +
        periodVector (axialRotateInt.symm lift)))]
    rw [map_sub, rotate.apply_symm_apply, map_add, rotate_periodVector,
      axialRotateInt.apply_symm_apply, ← siteCenter_rotateSite]
    exact bound

theorem C6_mono (points otherPoints : Set Plane) (inclusion : points ⊆ otherPoints) :
    C6 points ⊆ C6 otherPoints := by
  rintro point ⟨power, witness, membership, equality⟩
  exact ⟨power, witness, inclusion membership, equality⟩

theorem subset_C6 (points : Set Plane) : points ⊆ C6 points := by
  intro point membership
  refine ⟨⟨0, by decide⟩, point, membership, ?_⟩
  simp

theorem rotate_mem_C6 (points : Set Plane) (point : Plane)
    (membership : point ∈ C6 points) : rotate point ∈ C6 points := by
  rcases membership with ⟨power, witness, membership, rfl⟩
  refine ⟨⟨(power.val + 1) % 6, Nat.mod_lt _ (by decide)⟩,
    witness, membership, ?_⟩
  change (rotate * rotate ^ power.val) witness =
    (rotate ^ ((power.val + 1) % 6)) witness
  have power_eq : rotate * rotate ^ power.val = rotate ^ ((power.val + 1) % 6) := by
    rw [← pow_succ']
    exact pow_eq_pow_mod (power.val + 1) rotate_pow_six
  exact congrArg (fun map : Plane ≃ₗᵢ[ℝ] Plane => map witness) power_eq

theorem rotate_pow_mem_C6 (points : Set Plane) (power : ℕ) (point : Plane)
    (membership : point ∈ C6 points) : (rotate ^ power) point ∈ C6 points := by
  induction power with
  | zero => simpa using membership
  | succ power inductionHypothesis =>
      simpa only [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply]
        using rotate_mem_C6 points ((rotate ^ power) point) inductionHypothesis

theorem rotate_image_C6 (points : Set Plane) : rotate '' C6 points = C6 points := by
  apply Set.ext
  intro point
  constructor
  · rintro ⟨witness, membership, rfl⟩
    exact rotate_mem_C6 points witness membership
  · intro membership
    refine ⟨(rotate ^ 5) point, rotate_pow_mem_C6 points 5 point membership, ?_⟩
    change (rotate * rotate ^ 5) point = point
    rw [← pow_succ', rotate_pow_six]
    rfl

theorem rotationInvariant_C6 (points : Set Plane) : RotationInvariant (C6 points) := by
  intro point
  constructor
  · intro membership
    rw [← rotate_image_C6 points] at membership
    rcases membership with ⟨witness, membership, equality⟩
    have witness_eq : witness = point := rotate.injective equality
    simpa only [witness_eq] using membership
  · exact rotate_mem_C6 points point

theorem Periodic.sub_mem_iff (points : Set Plane) (periodic : Periodic points)
    (lift : ℤ × ℤ) (point : Plane) :
    point - periodVector lift ∈ points ↔ point ∈ points := by
  simpa only [periodVector_neg, sub_eq_add_neg] using periodic (-lift) point

/-- Powers of rotation preserve periodicity through the inverse integer map. -/
theorem periodic_rotate_pow_image (points : Set Plane) (periodic : Periodic points)
    (power : ℕ) : Periodic ((rotate ^ power) '' points) := by
  intro lift point
  let inverseLift : ℤ × ℤ := (axialRotateInt ^ power).symm lift
  have transport :
      (rotate ^ power) (periodVector inverseLift) = periodVector lift := by
    rw [rotate_pow_periodVector]
    exact congrArg periodVector ((axialRotateInt ^ power).apply_symm_apply lift)
  constructor
  · rintro ⟨witness, membership, equality⟩
    refine ⟨witness - periodVector inverseLift,
      (Periodic.sub_mem_iff points periodic inverseLift witness).2 membership, ?_⟩
    rw [map_sub, transport, equality, add_sub_cancel_right]
  · rintro ⟨witness, membership, equality⟩
    refine ⟨witness + periodVector inverseLift,
      (periodic inverseLift witness).2 membership, ?_⟩
    rw [map_add, transport, equality]

theorem periodic_C6 (points : Set Plane) (periodic : Periodic points) :
    Periodic (C6 points) := by
  intro lift point
  constructor
  · rintro ⟨power, witness, membership, equality⟩
    have translated : point + periodVector lift ∈ (rotate ^ power.val) '' points :=
      ⟨witness, membership, equality.symm⟩
    have original : point ∈ (rotate ^ power.val) '' points :=
      (periodic_rotate_pow_image points periodic power.val lift point).1 translated
    rcases original with ⟨originalWitness, originalMembership, originalEquality⟩
    exact ⟨power, originalWitness, originalMembership, originalEquality.symm⟩
  · rintro ⟨power, witness, membership, equality⟩
    have original : point ∈ (rotate ^ power.val) '' points :=
      ⟨witness, membership, equality.symm⟩
    have translated : point + periodVector lift ∈ (rotate ^ power.val) '' points :=
      (periodic_rotate_pow_image points periodic power.val lift point).2 original
    rcases translated with ⟨translatedWitness, translatedMembership, translatedEquality⟩
    exact ⟨power, translatedWitness, translatedMembership, translatedEquality.symm⟩

theorem periodic_union (points otherPoints : Set Plane)
    (periodic : Periodic points) (otherPeriodic : Periodic otherPoints) :
    Periodic (points ∪ otherPoints) := by
  intro lift point
  exact or_congr (periodic lift point) (otherPeriodic lift point)

theorem rotationInvariant_union (points otherPoints : Set Plane)
    (invariant : RotationInvariant points) (otherInvariant : RotationInvariant otherPoints) :
    RotationInvariant (points ∪ otherPoints) := by
  intro point
  exact or_congr (invariant point) (otherInvariant point)

theorem periodic_R (baseSites microSites : Set Site) : Periodic (R baseSites microSites) :=
  periodic_union (U baseSites) (C6 (U microSites))
    (periodic_U baseSites) (periodic_C6 (U microSites) (periodic_U microSites))

theorem rotationInvariant_R (baseSites microSites : Set Site)
    (baseInvariant : RotationInvariant (U baseSites)) :
    RotationInvariant (R baseSites microSites) :=
  rotationInvariant_union (U baseSites) (C6 (U microSites))
    baseInvariant (rotationInvariant_C6 (U microSites))

theorem Hits.mono (count : ℕ) (points otherPoints : Set Plane)
    (inclusion : points ⊆ otherPoints) (hits : Hits count points) : Hits count otherPoints := by
  intro start direction unitNorm
  rcases hits start direction unitNorm with ⟨index, membership⟩
  exact ⟨index, inclusion membership⟩

end Erdos188.UpperBound
