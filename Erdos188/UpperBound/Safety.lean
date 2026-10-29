module

public import Erdos188.UpperBound.Families
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Generic safety implications for periodic disk families

The sufficient implications of the project's safety account: closed-disk
annulus exclusion for one pair of sites at one lift, the reduction of
cross-safety of two periodic unions to the nine relative lifts, containment
and rotation routes between periodic unions, and the carrier composition
theorem giving unit independence and rotation invariance of the red set from
the carrier hypotheses. Every statement is about arbitrary semantic site sets
or physical sets; no finite family, numeric table, or certificate format
appears. The argument follows
the safety argument outlined in the repository `README.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Erdos188.UpperBound

/-- The relative period lift lies in the nine-element square `{-1, 0, 1}²`. -/
def NineLift (lift : ℤ × ℤ) : Prop := |lift.1| ≤ 1 ∧ |lift.2| ≤ 1

/-- The real axial vector from the center of the lifted target to the source center. -/
def axialGap (source target : Site) (lift : ℤ × ℤ) : ℝ × ℝ :=
  ratAxialToReal source.center - ratAxialToReal target.center +
    (59 : ℝ) • intAxialToReal lift

/-- First axial coordinate of the gap in explicit cast form. -/
theorem axialGap_fst (source target : Site) (lift : ℤ × ℤ) :
    (axialGap source target lift).1 =
      (source.center.1 : ℝ) - (target.center.1 : ℝ) + 59 * (lift.1 : ℝ) := by
  simp [axialGap, ratAxialToReal, intAxialToReal]

/-- Second axial coordinate of the gap in explicit cast form. -/
theorem axialGap_snd (source target : Site) (lift : ℤ × ℤ) :
    (axialGap source target lift).2 =
      (source.center.2 : ℝ) - (target.center.2 : ℝ) + 59 * (lift.2 : ℝ) := by
  simp [axialGap, ratAxialToReal, intAxialToReal]

/-- The physical center gap of a shifted target is the basis image of the axial gap. -/
theorem siteCenter_sub_shiftSite (source target : Site) (lift : ℤ × ℤ) :
    siteCenter source - siteCenter (shiftSite target lift) =
      basisMap (axialGap source target lift) := by
  rw [siteCenter_shiftSite]
  simp only [siteCenter, axialGap, periodVector, map_add, map_sub]
  abel

/-- The exact squared physical center gap from the axial quadratic form. -/
theorem siteCenter_sub_shiftSite_norm_sq (source target : Site) (lift : ℤ × ℤ) :
    ‖siteCenter source - siteCenter (shiftSite target lift)‖ ^ 2 =
      (441 / 10000 : ℝ) * axialQ (axialGap source target lift) := by
  rw [siteCenter_sub_shiftSite, basisMap_norm_sq]

/-- A site disk is the metric closed ball of its physical center and cast radius. -/
theorem closedDisk_eq_closedBall (site : Site) :
    closedDisk site = Metric.closedBall (siteCenter site) (site.radius : ℝ) := by
  ext point
  rw [mem_closedDisk_iff, Metric.mem_closedBall, dist_eq_norm]

/-- A point lies in a shifted disk exactly when its period translate lies in the original. -/
theorem mem_closedDisk_shiftSite_iff (site : Site) (lift : ℤ × ℤ) (point : Plane) :
    point ∈ closedDisk (shiftSite site lift) ↔
      point + periodVector lift ∈ closedDisk site := by
  rw [mem_closedDisk_iff, mem_closedDisk_iff, siteCenter_shiftSite, shiftSite_radius]
  have difference :
      point - (siteCenter site - periodVector lift) =
        point + periodVector lift - siteCenter site := by
    abel
  rw [difference]

/-- Translating a point by minus a period matches the lifted-center norm bound in `U`. -/
theorem sub_periodVector_mem_closedDisk_iff (site : Site) (lift : ℤ × ℤ) (point : Plane) :
    point - periodVector lift ∈ closedDisk site ↔
      ‖point - (siteCenter site + periodVector lift)‖ ≤ (site.radius : ℝ) := by
  rw [mem_closedDisk_iff, sub_sub, add_comm]

/-- Membership in the periodic union is membership of a period translate in one disk. -/
theorem mem_U_iff_closedDisk (siteSet : Set Site) (point : Plane) :
    point ∈ U siteSet ↔ ∃ site ∈ siteSet, ∃ lift : ℤ × ℤ,
      point - periodVector lift ∈ closedDisk site := by
  simp only [mem_U_iff, sub_periodVector_mem_closedDisk_iff]

/-- Rotation carries a site disk onto the disk of the rotated site. -/
theorem rotate_image_closedDisk (site : Site) :
    rotate '' closedDisk site = closedDisk (rotateSite site) := by
  ext point
  constructor
  · rintro ⟨witness, membership, rfl⟩
    rw [mem_closedDisk_iff, siteCenter_rotateSite, rotateSite_radius, ← map_sub, rotate_norm]
    exact membership
  · intro membership
    refine ⟨rotate.symm point, ?_, rotate.apply_symm_apply point⟩
    rw [mem_closedDisk_iff, siteCenter_rotateSite, rotateSite_radius] at membership
    rw [mem_closedDisk_iff, ← rotate_norm, map_sub, rotate.apply_symm_apply]
    exact membership

/-! ## Closed-disk exclusion -/

/-- Near branch: every cross distance is at most the center distance plus both radii. -/
theorem crossSafe_closedBall_near (center otherCenter : Plane) (radius otherRadius : ℝ)
    (near : dist center otherCenter + (radius + otherRadius) < 1) :
    CrossSafe (Metric.closedBall center radius) (Metric.closedBall otherCenter otherRadius) := by
  intro first firstMem second secondMem
  rw [Metric.mem_closedBall] at firstMem secondMem
  have chain := dist_triangle4 first center otherCenter second
  rw [dist_comm otherCenter second] at chain
  intro unit
  linarith

/-- Far branch: every cross distance is at least the center distance minus both radii. -/
theorem crossSafe_closedBall_far (center otherCenter : Plane) (radius otherRadius : ℝ)
    (far : 1 + (radius + otherRadius) < dist center otherCenter) :
    CrossSafe (Metric.closedBall center radius) (Metric.closedBall otherCenter otherRadius) := by
  intro first firstMem second secondMem
  rw [Metric.mem_closedBall] at firstMem secondMem
  have chain := dist_triangle4 center first second otherCenter
  rw [dist_comm center first] at chain
  intro unit
  linarith

/-- The strict squared annulus test excludes unit distances between two closed balls. -/
theorem crossSafe_closedBall_of_annulus (center otherCenter : Plane) (radius otherRadius : ℝ)
    (radiusNonneg : 0 ≤ radius) (otherNonneg : 0 ≤ otherRadius)
    (sumLe : radius + otherRadius ≤ 1)
    (annulus : ‖center - otherCenter‖ ^ 2 < (1 - (radius + otherRadius)) ^ 2 ∨
      (1 + (radius + otherRadius)) ^ 2 < ‖center - otherCenter‖ ^ 2) :
    CrossSafe (Metric.closedBall center radius) (Metric.closedBall otherCenter otherRadius) := by
  rcases annulus with near | far
  · apply crossSafe_closedBall_near
    have bound := (sq_lt_sq₀ (norm_nonneg _) (by linarith)).1 near
    rw [dist_eq_norm]
    linarith
  · apply crossSafe_closedBall_far
    have bound := (sq_lt_sq₀ (by linarith) (norm_nonneg _)).1 far
    rw [dist_eq_norm]
    linarith

/-- The annulus test for two site disks, stated on their physical centers. -/
theorem crossSafe_closedDisk_of_annulus (first second : Site)
    (firstNonneg : 0 ≤ first.radius) (secondNonneg : 0 ≤ second.radius)
    (sumLe : first.radius + second.radius ≤ 1)
    (annulus : ‖siteCenter first - siteCenter second‖ ^ 2 <
        (1 - ((first.radius : ℝ) + (second.radius : ℝ))) ^ 2 ∨
      (1 + ((first.radius : ℝ) + (second.radius : ℝ))) ^ 2 <
        ‖siteCenter first - siteCenter second‖ ^ 2) :
    CrossSafe (closedDisk first) (closedDisk second) := by
  rw [closedDisk_eq_closedBall, closedDisk_eq_closedBall]
  apply crossSafe_closedBall_of_annulus
  · exact_mod_cast firstNonneg
  · exact_mod_cast secondNonneg
  · exact_mod_cast sumLe
  · exact annulus

/-- The annulus test for a source disk against a period-shifted target disk, in axial form. -/
theorem crossSafe_closedDisk_shiftSite_of_annulus (source target : Site) (lift : ℤ × ℤ)
    (sourceNonneg : 0 ≤ source.radius) (targetNonneg : 0 ≤ target.radius)
    (sumLe : source.radius + target.radius ≤ 1)
    (annulus : (441 / 10000 : ℝ) * axialQ (axialGap source target lift) <
        (1 - ((source.radius : ℝ) + (target.radius : ℝ))) ^ 2 ∨
      (1 + ((source.radius : ℝ) + (target.radius : ℝ))) ^ 2 <
        (441 / 10000 : ℝ) * axialQ (axialGap source target lift)) :
    CrossSafe (closedDisk source) (closedDisk (shiftSite target lift)) := by
  apply crossSafe_closedDisk_of_annulus source (shiftSite target lift)
    sourceNonneg targetNonneg sumLe
  rw [siteCenter_sub_shiftSite_norm_sq]
  exact annulus

/-! ## Nine relative lifts -/

/-- Completing the square bounds the quadratic form below by the first coordinate. -/
theorem axialQ_ge_fst_sq (a : ℝ × ℝ) : (3 / 4 : ℝ) * a.1 ^ 2 ≤ axialQ a := by
  dsimp [axialQ]
  nlinarith [sq_nonneg (a.2 + a.1 / 2)]

/-- Completing the square bounds the quadratic form below by the second coordinate. -/
theorem axialQ_ge_snd_sq (a : ℝ × ℝ) : (3 / 4 : ℝ) * a.2 ^ 2 ≤ axialQ a := by
  dsimp [axialQ]
  nlinarith [sq_nonneg (a.1 + a.2 / 2)]

/-- A lift outside the nine-element square has a coordinate of absolute value at least two. -/
theorem two_le_abs_of_not_nineLift (lift : ℤ × ℤ) (far : ¬ NineLift lift) :
    2 ≤ |lift.1| ∨ 2 ≤ |lift.2| := by
  rcases not_and_or.1 far with large | large
  · exact Or.inl (Int.add_one_le_iff.2 (not_le.1 large))
  · exact Or.inr (Int.add_one_le_iff.2 (not_le.1 large))

/-- Normalized coordinates and a lift coordinate of absolute value two exceed `59` apart. -/
theorem large_lift_coordinate_sq (first second : ℝ) (lift : ℤ)
    (firstNonneg : 0 ≤ first) (firstLt : first < 59)
    (secondNonneg : 0 ≤ second) (secondLt : second < 59) (large : 2 ≤ |lift|) :
    3481 < (first - second + 59 * (lift : ℝ)) ^ 2 := by
  rcases le_abs'.1 large with negative | positive
  · have cast : (lift : ℝ) ≤ -2 := by exact_mod_cast negative
    have below : first - second + 59 * (lift : ℝ) < -59 := by linarith
    nlinarith
  · have cast : (2 : ℝ) ≤ (lift : ℝ) := by exact_mod_cast positive
    have above : 59 < first - second + 59 * (lift : ℝ) := by linarith
    nlinarith

/-- Two valid sites at a relative lift outside the nine square have centers more than two apart. -/
theorem far_lift_center_norm_sq (source target : Site) (lift : ℤ × ℤ)
    (sourceValid : SiteValid source) (targetValid : SiteValid target)
    (far : ¬ NineLift lift) :
    4 < ‖siteCenter source - siteCenter (shiftSite target lift)‖ ^ 2 := by
  rw [siteCenter_sub_shiftSite_norm_sq]
  obtain ⟨sourceFstNonneg, sourceFstLt, sourceSndNonneg, sourceSndLt, -, -⟩ := sourceValid
  obtain ⟨targetFstNonneg, targetFstLt, targetSndNonneg, targetSndLt, -, -⟩ := targetValid
  have sourceFstNonnegR : (0 : ℝ) ≤ (source.center.1 : ℝ) := by exact_mod_cast sourceFstNonneg
  have sourceFstLtR : (source.center.1 : ℝ) < 59 := by exact_mod_cast sourceFstLt
  have sourceSndNonnegR : (0 : ℝ) ≤ (source.center.2 : ℝ) := by exact_mod_cast sourceSndNonneg
  have sourceSndLtR : (source.center.2 : ℝ) < 59 := by exact_mod_cast sourceSndLt
  have targetFstNonnegR : (0 : ℝ) ≤ (target.center.1 : ℝ) := by exact_mod_cast targetFstNonneg
  have targetFstLtR : (target.center.1 : ℝ) < 59 := by exact_mod_cast targetFstLt
  have targetSndNonnegR : (0 : ℝ) ≤ (target.center.2 : ℝ) := by exact_mod_cast targetSndNonneg
  have targetSndLtR : (target.center.2 : ℝ) < 59 := by exact_mod_cast targetSndLt
  rcases two_le_abs_of_not_nineLift lift far with large | large
  · have coordinate := large_lift_coordinate_sq (source.center.1 : ℝ) (target.center.1 : ℝ)
      lift.1 sourceFstNonnegR sourceFstLtR targetFstNonnegR targetFstLtR large
    have form := axialQ_ge_fst_sq (axialGap source target lift)
    rw [axialGap_fst] at form
    linarith
  · have coordinate := large_lift_coordinate_sq (source.center.2 : ℝ) (target.center.2 : ℝ)
      lift.2 sourceSndNonnegR sourceSndLtR targetSndNonnegR targetSndLtR large
    have form := axialQ_ge_snd_sq (axialGap source target lift)
    rw [axialGap_snd] at form
    linarith

/-- Disks of valid sites at an omitted relative lift are cross-safe by the far branch. -/
theorem crossSafe_closedDisk_far_lift (source target : Site) (lift : ℤ × ℤ)
    (sourceValid : SiteValid source) (targetValid : SiteValid target)
    (far : ¬ NineLift lift) :
    CrossSafe (closedDisk source) (closedDisk (shiftSite target lift)) := by
  have separation := far_lift_center_norm_sq source target lift sourceValid targetValid far
  have sourceRadius : (source.radius : ℝ) < 1 / 2 := by
    have cast := (Rat.cast_lt (K := ℝ)).2 sourceValid.2.2.2.2.2
    push_cast at cast
    exact cast
  have targetRadius : (target.radius : ℝ) < 1 / 2 := by
    have cast := (Rat.cast_lt (K := ℝ)).2 targetValid.2.2.2.2.2
    push_cast at cast
    exact cast
  rw [closedDisk_eq_closedBall, closedDisk_eq_closedBall, shiftSite_radius]
  apply crossSafe_closedBall_far
  have centerGap : 2 < ‖siteCenter source - siteCenter (shiftSite target lift)‖ :=
    (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).1 (by nlinarith)
  rw [dist_eq_norm]
  linarith

/-- Cross-safety of two periodic unions of valid sites from the nine relative lifts. -/
theorem crossSafe_U_of_nine_lifts (siteSet otherSites : Set Site)
    (valid : ∀ site ∈ siteSet, SiteValid site)
    (otherValid : ∀ site ∈ otherSites, SiteValid site)
    (safe : ∀ site ∈ siteSet, ∀ other ∈ otherSites, ∀ lift : ℤ × ℤ, NineLift lift →
      CrossSafe (closedDisk site) (closedDisk (shiftSite other lift))) :
    CrossSafe (U siteSet) (U otherSites) := by
  intro first firstMem second secondMem
  rw [mem_U_iff_closedDisk] at firstMem secondMem
  obtain ⟨site, siteMem, lift, firstDisk⟩ := firstMem
  obtain ⟨other, otherMem, otherLift, secondDisk⟩ := secondMem
  have secondShifted :
      second - periodVector lift ∈ closedDisk (shiftSite other (lift - otherLift)) := by
    rw [mem_closedDisk_shiftSite_iff, periodVector_sub]
    have difference :
        second - periodVector lift + (periodVector lift - periodVector otherLift) =
          second - periodVector otherLift := by
      abel
    rw [difference]
    exact secondDisk
  rw [← dist_sub_right first second (periodVector lift)]
  by_cases nine : NineLift (lift - otherLift)
  · exact safe site siteMem other otherMem (lift - otherLift) nine
      (first - periodVector lift) firstDisk (second - periodVector lift) secondShifted
  · exact crossSafe_closedDisk_far_lift site other (lift - otherLift)
      (valid site siteMem) (otherValid other otherMem) nine
      (first - periodVector lift) firstDisk (second - periodVector lift) secondShifted

/-- Unit independence of a periodic union of valid sites from the nine relative lifts. -/
theorem unitIndependent_U_of_nine_lifts (siteSet : Set Site)
    (valid : ∀ site ∈ siteSet, SiteValid site)
    (safe : ∀ site ∈ siteSet, ∀ other ∈ siteSet, ∀ lift : ℤ × ℤ, NineLift lift →
      CrossSafe (closedDisk site) (closedDisk (shiftSite other lift))) :
    UnitIndependent (U siteSet) :=
  crossSafe_U_of_nine_lifts siteSet siteSet valid valid safe

/-! ## Containment routes -/

/-- Radius order and the squared center bound place one closed ball inside another. -/
theorem closedBall_subset_closedBall_of_sq (center target : Plane) (radius targetRadius : ℝ)
    (radiusOrder : radius ≤ targetRadius)
    (route : ‖center - target‖ ^ 2 ≤ (targetRadius - radius) ^ 2) :
    Metric.closedBall center radius ⊆ Metric.closedBall target targetRadius := by
  apply Metric.closedBall_subset_closedBall'
  have bound := (sq_le_sq₀ (norm_nonneg _) (by linarith)).1 route
  rw [dist_eq_norm]
  linarith

/-- A containment route from a source site into a period-shifted target site. -/
theorem closedDisk_subset_closedDisk_shiftSite (source target : Site) (lift : ℤ × ℤ)
    (radiusOrder : source.radius ≤ target.radius)
    (route : (441 / 10000 : ℝ) * axialQ (axialGap source target lift) ≤
      ((target.radius : ℝ) - (source.radius : ℝ)) ^ 2) :
    closedDisk source ⊆ closedDisk (shiftSite target lift) := by
  rw [closedDisk_eq_closedBall, closedDisk_eq_closedBall, shiftSite_radius]
  apply closedBall_subset_closedBall_of_sq
  · exact_mod_cast radiusOrder
  · rw [siteCenter_sub_shiftSite_norm_sq]
    exact route

/-- One disk inclusion per source site transfers to the whole periodic unions. -/
theorem U_subset_U_of_routes (siteSet targetSites : Set Site)
    (routes : ∀ site ∈ siteSet, ∃ target ∈ targetSites, ∃ lift : ℤ × ℤ,
      closedDisk site ⊆ closedDisk (shiftSite target lift)) :
    U siteSet ⊆ U targetSites := by
  intro point membership
  rw [mem_U_iff_closedDisk] at membership ⊢
  obtain ⟨site, siteMem, lift, disk⟩ := membership
  obtain ⟨target, targetMem, shift, route⟩ := routes site siteMem
  refine ⟨target, targetMem, lift - shift, ?_⟩
  have shifted := (mem_closedDisk_shiftSite_iff target shift (point - periodVector lift)).1
    (route disk)
  have difference :
      point - periodVector (lift - shift) =
        point - periodVector lift + periodVector shift := by
    rw [periodVector_sub]
    abel
  rw [difference]
  exact shifted

/-- Exact containment routes for every source site prove inclusion of the periodic unions. -/
theorem U_subset_U_of_containment_routes (siteSet targetSites : Set Site)
    (routes : ∀ site ∈ siteSet, ∃ target ∈ targetSites, ∃ lift : ℤ × ℤ,
      site.radius ≤ target.radius ∧
        (441 / 10000 : ℝ) * axialQ (axialGap site target lift) ≤
          ((target.radius : ℝ) - (site.radius : ℝ)) ^ 2) :
    U siteSet ⊆ U targetSites := by
  apply U_subset_U_of_routes
  intro site membership
  obtain ⟨target, targetMem, lift, radiusOrder, route⟩ := routes site membership
  exact ⟨target, targetMem, lift,
    closedDisk_subset_closedDisk_shiftSite site target lift radiusOrder route⟩

/-! ## Rotation routes -/

/-- Routing every rotated disk into a shifted site disk bounds the rotated union. -/
theorem rotate_image_U_subset_of_rotation_routes (siteSet : Set Site)
    (routes : ∀ site ∈ siteSet, ∃ target ∈ siteSet, ∃ lift : ℤ × ℤ,
      closedDisk (rotateSite site) ⊆ closedDisk (shiftSite target lift)) :
    rotate '' U siteSet ⊆ U siteSet := by
  rw [rotate_image_U]
  apply U_subset_U_of_routes
  rintro site ⟨original, membership, rfl⟩
  exact routes original membership

/-- One more rotation power is one more application of the rotation. -/
theorem rotate_pow_apply_succ (power : ℕ) (point : Plane) :
    (rotate ^ (power + 1)) point = rotate ((rotate ^ power) point) := by
  simp only [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply]

/-- Order six turns a one-way rotation inclusion into rotation invariance. -/
theorem rotationInvariant_of_rotate_image_subset (points : Set Plane)
    (inclusion : rotate '' points ⊆ points) : RotationInvariant points := by
  have powerSubset : ∀ power : ℕ, ∀ point ∈ points, (rotate ^ power) point ∈ points := by
    intro power
    induction power with
    | zero =>
        intro point membership
        simpa using membership
    | succ power inductionHypothesis =>
        intro point membership
        rw [rotate_pow_apply_succ]
        exact inclusion ⟨(rotate ^ power) point, inductionHypothesis point membership, rfl⟩
  intro point
  constructor
  · intro membership
    have unwind : (rotate ^ 5) (rotate point) = point := by
      change (rotate ^ 5 * rotate) point = point
      rw [← pow_succ, rotate_pow_six]
      rfl
    rw [← unwind]
    exact powerSubset 5 (rotate point) membership
  · intro membership
    exact inclusion ⟨point, membership, rfl⟩

/-- A rotation-invariant set equals its rotated image. -/
theorem RotationInvariant.rotate_image_eq (points : Set Plane)
    (invariant : RotationInvariant points) : rotate '' points = points := by
  ext point
  constructor
  · rintro ⟨witness, membership, rfl⟩
    exact (invariant witness).2 membership
  · intro membership
    refine ⟨rotate.symm point, ?_, rotate.apply_symm_apply point⟩
    rw [← invariant, rotate.apply_symm_apply]
    exact membership

/-- Rotation routes for every site give rotation invariance of the periodic union. -/
theorem rotationInvariant_U_of_rotation_routes (siteSet : Set Site)
    (routes : ∀ site ∈ siteSet, ∃ target ∈ siteSet, ∃ lift : ℤ × ℤ,
      closedDisk (rotateSite site) ⊆ closedDisk (shiftSite target lift)) :
    RotationInvariant (U siteSet) :=
  rotationInvariant_of_rotate_image_subset (U siteSet)
    (rotate_image_U_subset_of_rotation_routes siteSet routes)

/-- Exactly matched rotated sites, up to a period shift, give rotation invariance. -/
theorem rotationInvariant_U_of_exact_rotation_routes (siteSet : Set Site)
    (routes : ∀ site ∈ siteSet, ∃ target ∈ siteSet, ∃ lift : ℤ × ℤ,
      rotateSite site = shiftSite target lift) :
    RotationInvariant (U siteSet) := by
  apply rotationInvariant_U_of_rotation_routes
  intro site membership
  obtain ⟨target, targetMem, lift, equality⟩ := routes site membership
  exact ⟨target, targetMem, lift, by rw [equality]⟩

/-! ## Carrier composition -/

/-- The six rotated copies of a subset of a rotation-invariant set stay inside it. -/
theorem C6_subset_of_rotationInvariant (points container : Set Plane)
    (inclusion : points ⊆ container) (invariant : RotationInvariant container) :
    C6 points ⊆ container := by
  rintro point ⟨power, witness, membership, rfl⟩
  exact (RotationInvariant.pow_mem_iff container invariant power.val witness).2
    (inclusion membership)

/-- A base point and a rotated micro point are never at unit distance. -/
theorem CarrierHypotheses.base_C6_micro_safe (base carrier plug micro : Set Plane)
    (hypotheses : CarrierHypotheses base carrier plug micro) :
    CrossSafe base (C6 micro) := by
  intro basePoint baseMem microPoint microMem
  have microInCarrier : C6 micro ⊆ carrier :=
    C6_subset_of_rotationInvariant micro carrier
      hypotheses.micro_subset_carrier hypotheses.carrier_rotation
  rcases hypotheses.base_subset_carrier_union_plug baseMem with inCarrier | inPlug
  · exact hypotheses.carrier_independent basePoint inCarrier microPoint (microInCarrier microMem)
  · obtain ⟨power, witness, witnessMem, rfl⟩ := microMem
    have unrotated : (rotate ^ power.val).symm basePoint ∈ plug := by
      rw [← RotationInvariant.pow_mem_iff plug hypotheses.plug_rotation power.val,
        LinearIsometryEquiv.apply_symm_apply]
      exact inPlug
    have transport :
        dist basePoint ((rotate ^ power.val) witness) =
          dist witness ((rotate ^ power.val).symm basePoint) := by
      rw [dist_comm, ← (rotate ^ power.val).dist_map witness ((rotate ^ power.val).symm basePoint),
        LinearIsometryEquiv.apply_symm_apply]
    rw [transport]
    exact hypotheses.micro_plug_cross_safe witness witnessMem _ unrotated

/-- The carrier hypotheses make the base together with the rotated micro set unit-independent. -/
theorem CarrierHypotheses.unitIndependent_red (base carrier plug micro : Set Plane)
    (hypotheses : CarrierHypotheses base carrier plug micro) :
    UnitIndependent (base ∪ C6 micro) := by
  have microInCarrier : C6 micro ⊆ carrier :=
    C6_subset_of_rotationInvariant micro carrier
      hypotheses.micro_subset_carrier hypotheses.carrier_rotation
  have mixed := CarrierHypotheses.base_C6_micro_safe base carrier plug micro hypotheses
  intro first firstMem second secondMem
  rcases firstMem with firstBase | firstMicro <;> rcases secondMem with secondBase | secondMicro
  · exact hypotheses.base_independent first firstBase second secondBase
  · exact mixed first firstBase second secondMicro
  · rw [dist_comm]
    exact mixed second secondBase first firstMicro
  · exact hypotheses.carrier_independent first (microInCarrier firstMicro)
      second (microInCarrier secondMicro)

/-- The carrier hypotheses make the base together with the rotated micro set rotation invariant. -/
theorem CarrierHypotheses.rotationInvariant_red (base carrier plug micro : Set Plane)
    (hypotheses : CarrierHypotheses base carrier plug micro) :
    RotationInvariant (base ∪ C6 micro) :=
  rotationInvariant_union base (C6 micro) hypotheses.base_rotation (rotationInvariant_C6 micro)

/-- Under a semantic binding the physical red set is the semantic red set. -/
theorem FamilySemantics.red_eq (roles : FamilyRoles) (physical : PhysicalRoles)
    (binding : FamilySemantics roles physical) :
    physical.base ∪ C6 physical.micro = R roles.baseSites roles.microSites := by
  rw [R, binding.base_eq, binding.micro_eq]

/-- The semantic red set is unit-independent, rotation invariant, and periodic. -/
theorem FamilyRoles.red_safe (roles : FamilyRoles) (hypotheses : roles.SafetyHypotheses) :
    UnitIndependent (R roles.baseSites roles.microSites) ∧
      RotationInvariant (R roles.baseSites roles.microSites) ∧
        Periodic (R roles.baseSites roles.microSites) :=
  ⟨CarrierHypotheses.unitIndependent_red (U roles.baseSites) (U roles.carrierSites)
      (U roles.plugSites) (U roles.microSites) hypotheses,
    rotationInvariant_R roles.baseSites roles.microSites hypotheses.base_rotation,
    periodic_R roles.baseSites roles.microSites⟩

/-- Physical carrier hypotheses bound to semantic roles give the same red-set conclusions. -/
theorem red_safe_of_physical (roles : FamilyRoles) (physical : PhysicalRoles)
    (binding : FamilySemantics roles physical)
    (hypotheses : CarrierHypotheses physical.base physical.carrier physical.plug physical.micro) :
    UnitIndependent (R roles.baseSites roles.microSites) ∧
      RotationInvariant (R roles.baseSites roles.microSites) ∧
        Periodic (R roles.baseSites roles.microSites) :=
  FamilyRoles.red_safe roles
    ((carrierHypotheses_iff_semantic roles physical binding).1 hypotheses)

end Erdos188.UpperBound
