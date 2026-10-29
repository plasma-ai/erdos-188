module

public import Erdos188.UpperBound.Directions
public import Erdos188.UpperBound.Families
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Certified covering of unit-step progressions

The generic covering interface. A mixed dyadic cell pairs a closed direction
interval with a closed axial translation square. One leaf witness covers its
whole cell through four rational corner tests, a certified tree is built from
leaves by direction halving and translation quartering, and a certified root
tree turns periodicity, rotation invariance, and witness inclusion into the
42-term hitting property on the entire plane (`wholePlane`). No finite family,
tree, or numeric table is supplied here. The argument follows
the covering outlined in the repository `README.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Erdos188.UpperBound

/-- A mixed dyadic cell: direction depth and index, translation depth and two indices. -/
structure Cell where
  directionDepth : ℕ
  directionIndex : ℕ
  translationDepth : ℕ
  translationIndexS : ℕ
  translationIndexT : ℕ

/-- Every index lies below the dyadic count at its own depth. -/
def Cell.WellFormed (cell : Cell) : Prop :=
  cell.directionIndex < 2 ^ cell.directionDepth ∧
    cell.translationIndexS < 2 ^ cell.translationDepth ∧
      cell.translationIndexT < 2 ^ cell.translationDepth

/-- The root cell: the whole closed parameter sector and the whole period square. -/
def rootCell : Cell := ⟨0, 0, 0, 0, 0⟩

/-- Halve the direction interval; the bit selects the lower or the upper half. -/
def Cell.directionChild (cell : Cell) (bit : Fin 2) : Cell :=
  { cell with
    directionDepth := cell.directionDepth + 1
    directionIndex := 2 * cell.directionIndex + bit.val }

/-- Quarter the translation square; the two bits select the quadrant. -/
def Cell.translationChild (cell : Cell) (ε δ : Fin 2) : Cell :=
  { cell with
    translationDepth := cell.translationDepth + 1
    translationIndexS := 2 * cell.translationIndexS + ε.val
    translationIndexT := 2 * cell.translationIndexT + δ.val }

/-- The root cell is well-formed. -/
theorem rootCell_wellFormed : rootCell.WellFormed := by
  simp [rootCell, Cell.WellFormed]

/-- Direction halving preserves well-formedness. -/
theorem Cell.WellFormed.directionChild {cell : Cell} (wellFormed : cell.WellFormed)
    (bit : Fin 2) : (cell.directionChild bit).WellFormed := by
  obtain ⟨hi, hh, hk⟩ := wellFormed
  refine ⟨?_, hh, hk⟩
  change 2 * cell.directionIndex + bit.val < 2 ^ (cell.directionDepth + 1)
  have hbit := bit.isLt
  rw [pow_succ]
  omega

/-- Translation quartering preserves well-formedness. -/
theorem Cell.WellFormed.translationChild {cell : Cell} (wellFormed : cell.WellFormed)
    (ε δ : Fin 2) : (cell.translationChild ε δ).WellFormed := by
  obtain ⟨hi, hh, hk⟩ := wellFormed
  refine ⟨hi, ?_, ?_⟩
  · change 2 * cell.translationIndexS + ε.val < 2 ^ (cell.translationDepth + 1)
    have hε := ε.isLt
    rw [pow_succ]
    omega
  · change 2 * cell.translationIndexT + δ.val < 2 ^ (cell.translationDepth + 1)
    have hδ := δ.isLt
    rw [pow_succ]
    omega

/-- Lower endpoint of a dyadic translation interval inside one period. -/
def translationLeft (e h : ℕ) : ℝ := 59 * (h : ℝ) / (2 : ℝ) ^ e

/-- Upper endpoint of a dyadic translation interval inside one period. -/
def translationRight (e h : ℕ) : ℝ := 59 * ((h : ℝ) + 1) / (2 : ℝ) ^ e

/-- Midpoint of a dyadic translation interval. -/
def translationMidpoint (e h : ℕ) : ℝ :=
  59 * (2 * (h : ℝ) + 1) / (2 : ℝ) ^ (e + 1)

/-- The closed dyadic translation interval along one axial axis. -/
def translationInterval (e h : ℕ) : Set ℝ :=
  Set.Icc (translationLeft e h) (translationRight e h)

/-- The closed axial translation square at a translation depth and index pair. -/
def translationSquare (e h k : ℕ) : Set (ℝ × ℝ) :=
  translationInterval e h ×ˢ translationInterval e k

/-- One endpoint of a translation interval, selected by a bit. -/
def translationEndpoint (e h : ℕ) : Fin 2 → ℝ
  | 0 => translationLeft e h
  | 1 => translationRight e h

/-- One of the four closed corners of a translation square. -/
def translationCorner (e h k : ℕ) (ε δ : Fin 2) : ℝ × ℝ :=
  (translationEndpoint e h ε, translationEndpoint e k δ)

/-- The closed direction interval of a cell. -/
def Cell.interval (cell : Cell) : Set ℝ :=
  directionInterval cell.directionDepth cell.directionIndex

/-- The midpoint direction parameter of a cell. -/
def Cell.midpoint (cell : Cell) : ℝ :=
  directionMidpoint cell.directionDepth cell.directionIndex

/-- The rational direction-error allowance of a cell. -/
def Cell.errorAllowance (cell : Cell) : ℝ :=
  directionError cell.directionDepth cell.directionIndex

/-- The closed axial translation square of a cell. -/
def Cell.square (cell : Cell) : Set (ℝ × ℝ) :=
  translationSquare cell.translationDepth cell.translationIndexS cell.translationIndexT

/-- One of the four closed corners of a cell's translation square. -/
def Cell.corner (cell : Cell) (ε δ : Fin 2) : ℝ × ℝ :=
  translationCorner cell.translationDepth cell.translationIndexS cell.translationIndexT ε δ

/-- A translation interval is never degenerate in the wrong direction. -/
theorem translationLeft_le_right (e h : ℕ) : translationLeft e h ≤ translationRight e h := by
  dsimp [translationLeft, translationRight]
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt (pow_pos (by norm_num) e))

/-- The lower translation child starts at the parent's left endpoint. -/
theorem translationLeft_child_zero (e h : ℕ) :
    translationLeft (e + 1) (2 * h) = translationLeft e h := by
  have hpower : (2 : ℝ) ^ e ≠ 0 := ne_of_gt (pow_pos (by norm_num) e)
  dsimp [translationLeft]
  rw [pow_succ]
  push_cast
  field_simp

/-- The lower translation child ends at the parent's midpoint. -/
theorem translationRight_child_zero (e h : ℕ) :
    translationRight (e + 1) (2 * h) = translationMidpoint e h := by
  dsimp [translationRight, translationMidpoint]
  push_cast
  ring

/-- The upper translation child starts at the parent's midpoint. -/
theorem translationLeft_child_one (e h : ℕ) :
    translationLeft (e + 1) (2 * h + 1) = translationMidpoint e h := by
  dsimp [translationLeft, translationMidpoint]
  push_cast
  ring

/-- The upper translation child ends at the parent's right endpoint. -/
theorem translationRight_child_one (e h : ℕ) :
    translationRight (e + 1) (2 * h + 1) = translationRight e h := by
  have hpower : (2 : ℝ) ^ e ≠ 0 := ne_of_gt (pow_pos (by norm_num) e)
  dsimp [translationRight]
  rw [pow_succ]
  push_cast
  field_simp
  ring

/-- Every point of a translation interval lies in one of its two dyadic halves. -/
theorem translationInterval_split (e h : ℕ) (s : ℝ) (hs : s ∈ translationInterval e h) :
    ∃ bit : Fin 2, s ∈ translationInterval (e + 1) (2 * h + bit.val) := by
  change translationLeft e h ≤ s ∧ s ≤ translationRight e h at hs
  rcases le_total s (translationMidpoint e h) with hlow | hhigh
  · refine ⟨0, ?_⟩
    change translationLeft (e + 1) (2 * h) ≤ s ∧ s ≤ translationRight (e + 1) (2 * h)
    rw [translationLeft_child_zero, translationRight_child_zero]
    exact ⟨hs.1, hlow⟩
  · refine ⟨1, ?_⟩
    change translationLeft (e + 1) (2 * h + 1) ≤ s ∧ s ≤ translationRight (e + 1) (2 * h + 1)
    rw [translationLeft_child_one, translationRight_child_one]
    exact ⟨hhigh, hs.2⟩

/-- Every point of a translation square lies in one of its four dyadic quarters. -/
theorem translationSquare_split (e h k : ℕ) (q : ℝ × ℝ)
    (hq : q ∈ translationSquare e h k) :
    ∃ ε δ : Fin 2, q ∈ translationSquare (e + 1) (2 * h + ε.val) (2 * k + δ.val) := by
  obtain ⟨ε, hε⟩ := translationInterval_split e h q.1 hq.1
  obtain ⟨δ, hδ⟩ := translationInterval_split e k q.2 hq.2
  exact ⟨ε, δ, hε, hδ⟩

/-- The closed translation square is the convex hull of its four corners. -/
theorem translationSquare_eq_convexHull (e h k : ℕ) :
    translationSquare e h k =
      convexHull ℝ ({translationLeft e h, translationRight e h} ×ˢ
        {translationLeft e k, translationRight e k}) := by
  rw [convexHull_prod, convexHull_pair, convexHull_pair,
    segment_eq_Icc (translationLeft_le_right e h), segment_eq_Icc (translationLeft_le_right e k)]
  rfl

/-- A convex set containing the four corners contains the whole translation square. -/
theorem translationSquare_subset_of_corners (e h k : ℕ) (target : Set (ℝ × ℝ))
    (convex : Convex ℝ target)
    (corners : ∀ ε δ : Fin 2, translationCorner e h k ε δ ∈ target) :
    translationSquare e h k ⊆ target := by
  rw [translationSquare_eq_convexHull]
  apply convexHull_min _ convex
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact corners 0 0
  · exact corners 0 1
  · exact corners 1 0
  · exact corners 1 1

/-- The lower direction child starts at the parent's left endpoint. -/
theorem directionLeft_child_zero (d i : ℕ) :
    directionLeft (d + 1) (2 * i) = directionLeft d i := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  dsimp [directionLeft]
  rw [pow_succ]
  push_cast
  field_simp

/-- The lower direction child ends at the parent's midpoint. -/
theorem directionRight_child_zero (d i : ℕ) :
    directionRight (d + 1) (2 * i) = directionMidpoint d i := by
  dsimp [directionRight, directionMidpoint]
  push_cast
  ring

/-- The upper direction child starts at the parent's midpoint. -/
theorem directionLeft_child_one (d i : ℕ) :
    directionLeft (d + 1) (2 * i + 1) = directionMidpoint d i := by
  dsimp [directionLeft, directionMidpoint]
  push_cast
  ring

/-- The upper direction child ends at the parent's right endpoint. -/
theorem directionRight_child_one (d i : ℕ) :
    directionRight (d + 1) (2 * i + 1) = directionRight d i := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  dsimp [directionRight]
  rw [pow_succ]
  push_cast
  field_simp
  ring

/-- Every parameter of a direction interval lies in one of its two dyadic halves. -/
theorem directionInterval_split (d i : ℕ) (τ : ℝ) (hτ : τ ∈ directionInterval d i) :
    τ ∈ directionInterval (d + 1) (2 * i) ∨ τ ∈ directionInterval (d + 1) (2 * i + 1) := by
  change directionLeft d i ≤ τ ∧ τ ≤ directionRight d i at hτ
  rcases le_total τ (directionMidpoint d i) with hlow | hhigh
  · left
    change directionLeft (d + 1) (2 * i) ≤ τ ∧ τ ≤ directionRight (d + 1) (2 * i)
    rw [directionLeft_child_zero, directionRight_child_zero]
    exact ⟨hτ.1, hlow⟩
  · right
    change directionLeft (d + 1) (2 * i + 1) ≤ τ ∧ τ ≤ directionRight (d + 1) (2 * i + 1)
    rw [directionLeft_child_one, directionRight_child_one]
    exact ⟨hhigh, hτ.2⟩

/-- The data of a leaf witness: a signed step, a site, and an integer period lift. -/
structure Witness where
  step : ℤ
  site : Site
  lift : ℤ × ℤ

/-- The physical center of the lifted witness site. -/
def Witness.center (witness : Witness) : Plane :=
  siteCenter witness.site + periodVector witness.lift

/-- The witness radius left after paying for the direction error over the cell. -/
def usableRadius (cell : Cell) (witness : Witness) : ℝ :=
  (witness.site.radius : ℝ) - |(witness.step : ℝ)| * cell.errorAllowance

/-- The axial offset from the lifted center to a corner stepped along the midpoint direction. -/
def cornerOffset (cell : Cell) (witness : Witness) (ε δ : Fin 2) : ℝ × ℝ :=
  cell.corner ε δ + (witness.step : ℝ) • directionAxial cell.midpoint -
    (ratAxialToReal witness.site.center + (59 : ℝ) • intAxialToReal witness.lift)

/-- The exact leaf test: bounded step, listed site, positive usable radius, four corners. -/
structure LeafValid (siteSet : Set Site) (cell : Cell) (witness : Witness) : Prop where
  /-- The step is at least the first index of the centered progression. -/
  step_lower : -21 ≤ witness.step
  /-- The step is at most the last index of the centered progression. -/
  step_upper : witness.step ≤ 20
  /-- The witness site belongs to the semantic family. -/
  site_mem : witness.site ∈ siteSet
  /-- The radius survives the direction error with strict room to spare. -/
  radius_pos : 0 < usableRadius cell witness
  /-- Each of the four stepped corners lies within the usable radius. -/
  corner_bound : ∀ ε δ : Fin 2,
    (441 / 10000 : ℝ) * axialQ (cornerOffset cell witness ε δ) ≤ usableRadius cell witness ^ 2

/-- Every parameter pair of the cell has a bounded step landing in the witness union. -/
def Covered (siteSet : Set Site) (cell : Cell) : Prop :=
  ∀ τ ∈ cell.interval, ∀ q ∈ cell.square,
    ∃ step : ℤ, -21 ≤ step ∧ step ≤ 20 ∧
      basisMap q + (step : ℝ) • direction τ ∈ U siteSet

/-- A complete certificate tree: leaves, direction halvings, and translation quarterings. -/
inductive Certified (siteSet : Set Site) : Cell → Prop
  /-- One witness passes the exact leaf test for the whole cell. -/
  | leaf (cell : Cell) (witness : Witness) (valid : LeafValid siteSet cell witness) :
      Certified siteSet cell
  /-- Both dyadic direction halves are certified. -/
  | directionSplit (cell : Cell)
      (lower : Certified siteSet (cell.directionChild 0))
      (upper : Certified siteSet (cell.directionChild 1)) :
      Certified siteSet cell
  /-- All four dyadic translation quarters are certified. -/
  | translationSplit (cell : Cell)
      (quarters : ∀ ε δ : Fin 2, Certified siteSet (cell.translationChild ε δ)) :
      Certified siteSet cell

/-- The physical form of one stepped corner offset. -/
theorem basisMap_cornerOffset (cell : Cell) (witness : Witness) (ε δ : Fin 2) :
    basisMap (cornerOffset cell witness ε δ) =
      basisMap (cell.corner ε δ) + (witness.step : ℝ) • direction cell.midpoint -
        witness.center := by
  rw [cornerOffset, map_sub, map_add, map_smul, Witness.center, siteCenter_add_periodVector]
  rfl

/-- Each stepped physical corner lies within the usable radius of the lifted center. -/
theorem leafValid_corner_norm (siteSet : Set Site) (cell : Cell) (witness : Witness)
    (valid : LeafValid siteSet cell witness) (ε δ : Fin 2) :
    ‖basisMap (cell.corner ε δ) + (witness.step : ℝ) • direction cell.midpoint -
      witness.center‖ ≤ usableRadius cell witness := by
  rw [← basisMap_cornerOffset]
  apply (sq_le_sq₀ (norm_nonneg _) (le_of_lt valid.radius_pos)).1
  rw [basisMap_norm_sq]
  exact valid.corner_bound ε δ

/-- The axial preimage of a closed physical ball around a shifted center is convex. -/
theorem convex_axial_ball (shift center : Plane) (radius : ℝ) :
    Convex ℝ {q : ℝ × ℝ | ‖basisMap q + shift - center‖ ≤ radius} := by
  have set_eq : {q : ℝ × ℝ | ‖basisMap q + shift - center‖ ≤ radius} =
      (basisMap : (ℝ × ℝ) →ₗ[ℝ] Plane) ⁻¹'
        Metric.closedBall (center - shift) radius := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
      LinearEquiv.coe_coe, sub_sub_eq_add_sub]
  rw [set_eq]
  exact (convex_closedBall (center - shift) radius).linear_preimage _

/-- At the midpoint direction, every point of the square is within the usable radius. -/
theorem leafValid_square_norm (siteSet : Set Site) (cell : Cell) (witness : Witness)
    (valid : LeafValid siteSet cell witness) (q : ℝ × ℝ) (hq : q ∈ cell.square) :
    ‖basisMap q + (witness.step : ℝ) • direction cell.midpoint - witness.center‖ ≤
      usableRadius cell witness := by
  have square_subset := translationSquare_subset_of_corners cell.translationDepth
    cell.translationIndexS cell.translationIndexT
    {p : ℝ × ℝ |
      ‖basisMap p + (witness.step : ℝ) • direction cell.midpoint - witness.center‖ ≤
        usableRadius cell witness}
    (convex_axial_ball _ _ _) (leafValid_corner_norm siteSet cell witness valid)
  exact square_subset hq

/-- A valid leaf witness covers every parameter pair of its well-formed cell. -/
theorem leafValid_covered (siteSet : Set Site) (cell : Cell) (witness : Witness)
    (wellFormed : cell.WellFormed) (valid : LeafValid siteSet cell witness) :
    Covered siteSet cell := by
  intro τ hτ q hq
  refine ⟨witness.step, valid.step_lower, valid.step_upper, witness.site, valid.site_mem,
    witness.lift, ?_⟩
  have midpoint_bound := leafValid_square_norm siteSet cell witness valid q hq
  have error_bound : ‖direction τ - direction cell.midpoint‖ ≤ cell.errorAllowance :=
    direction_error_dyadic cell.directionDepth cell.directionIndex wellFormed.1 τ hτ
  have decomposition :
      basisMap q + (witness.step : ℝ) • direction τ - witness.center =
        (basisMap q + (witness.step : ℝ) • direction cell.midpoint - witness.center) +
          (witness.step : ℝ) • (direction τ - direction cell.midpoint) := by
    rw [smul_sub]
    abel
  change ‖basisMap q + (witness.step : ℝ) • direction τ - witness.center‖ ≤
    (witness.site.radius : ℝ)
  rw [decomposition]
  calc
    ‖(basisMap q + (witness.step : ℝ) • direction cell.midpoint - witness.center) +
        (witness.step : ℝ) • (direction τ - direction cell.midpoint)‖ ≤
        ‖basisMap q + (witness.step : ℝ) • direction cell.midpoint - witness.center‖ +
          ‖(witness.step : ℝ) • (direction τ - direction cell.midpoint)‖ :=
      norm_add_le _ _
    _ ≤ usableRadius cell witness + |(witness.step : ℝ)| * cell.errorAllowance := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add midpoint_bound (mul_le_mul_of_nonneg_left error_bound (abs_nonneg _))
    _ = (witness.site.radius : ℝ) := by
      dsimp [usableRadius]
      ring

/-- Covered direction halves cover their parent cell. -/
theorem covered_of_directionChildren (siteSet : Set Site) (cell : Cell)
    (lower : Covered siteSet (cell.directionChild 0))
    (upper : Covered siteSet (cell.directionChild 1)) :
    Covered siteSet cell := by
  intro τ hτ q hq
  rcases directionInterval_split cell.directionDepth cell.directionIndex τ hτ with hlow | hhigh
  · exact lower τ hlow q hq
  · exact upper τ hhigh q hq

/-- Covered translation quarters cover their parent cell. -/
theorem covered_of_translationChildren (siteSet : Set Site) (cell : Cell)
    (quarters : ∀ ε δ : Fin 2, Covered siteSet (cell.translationChild ε δ)) :
    Covered siteSet cell := by
  intro τ hτ q hq
  obtain ⟨ε, δ, hquarter⟩ := translationSquare_split cell.translationDepth
    cell.translationIndexS cell.translationIndexT q hq
  exact quarters ε δ τ hτ q hquarter

/-- Every certified well-formed cell is covered. -/
theorem Certified.covered {siteSet : Set Site} {cell : Cell}
    (certified : Certified siteSet cell) (wellFormed : cell.WellFormed) :
    Covered siteSet cell := by
  induction certified with
  | leaf cell witness valid =>
      exact leafValid_covered siteSet cell witness wellFormed valid
  | directionSplit cell lower upper lowerCovered upperCovered =>
      exact covered_of_directionChildren siteSet cell
        (lowerCovered (wellFormed.directionChild 0)) (upperCovered (wellFormed.directionChild 1))
  | translationSplit cell quarters quartersCovered =>
      exact covered_of_translationChildren siteSet cell
        (fun ε δ => quartersCovered ε δ (wellFormed.translationChild ε δ))

/-- The integer period lift that reduces a real axial coordinate into the fundamental window. -/
def periodLift (s : ℝ) : ℤ := ⌊s / 59⌋

/-- The reduced real axial coordinate in the closed fundamental window. -/
def periodReduce (s : ℝ) : ℝ := s - 59 * (periodLift s : ℝ)

/-- The reduced coordinate lies in the root translation interval. -/
theorem periodReduce_mem (s : ℝ) : periodReduce s ∈ translationInterval 0 0 := by
  have hfloor := Int.floor_le (s / 59)
  have hlt := Int.lt_floor_add_one (s / 59)
  change translationLeft 0 0 ≤ periodReduce s ∧ periodReduce s ≤ translationRight 0 0
  dsimp [translationLeft, translationRight, periodReduce, periodLift]
  constructor <;> · norm_num; linarith

/-- The root direction interval is the closed sector. -/
theorem mem_directionInterval_root (τ : ℝ) (hτ : τ ∈ Set.Icc (-2 : ℝ) (-1)) :
    τ ∈ directionInterval 0 0 := by
  change directionLeft 0 0 ≤ τ ∧ τ ≤ directionRight 0 0
  dsimp [directionLeft, directionRight]
  constructor <;> · norm_num; linarith [hτ.1, hτ.2]

/-- Reducing both axial coordinates subtracts the corresponding period vector. -/
theorem basisMap_periodReduce (axial : ℝ × ℝ) :
    basisMap (periodReduce axial.1, periodReduce axial.2) =
      basisMap axial - periodVector (periodLift axial.1, periodLift axial.2) := by
  rw [periodVector, ← map_sub]
  rfl

/-- A certified root tree turns the semantic premises into the 42-term hitting property. -/
theorem wholePlane (redSet : Set Plane) (siteSet : Set Site)
    (periodic : Periodic redSet) (invariant : RotationInvariant redSet)
    (inclusion : U siteSet ⊆ redSet) (certified : Certified siteSet rootCell) :
    Hits 42 redSet := by
  intro start dir unitNorm
  obtain ⟨k, τ, hτ, hdir⟩ := direction_sector_covers dir unitNorm
  have root_covered : Covered siteSet rootCell := certified.covered rootCell_wellFormed
  obtain ⟨axial, haxial⟩ : ∃ axial : ℝ × ℝ,
      basisMap axial = (rotate ^ (k : ℕ)).symm (start + (21 : ℝ) • dir) :=
    basisMap.surjective _
  have reduced_mem : (periodReduce axial.1, periodReduce axial.2) ∈ rootCell.square :=
    ⟨periodReduce_mem axial.1, periodReduce_mem axial.2⟩
  obtain ⟨step, hlower, hupper, hmem⟩ :=
    root_covered τ (mem_directionInterval_root τ hτ) _ reduced_mem
  have shifted := (periodic (periodLift axial.1, periodLift axial.2) _).2 (inclusion hmem)
  rw [basisMap_periodReduce] at shifted
  have rearranged :
      basisMap axial - periodVector (periodLift axial.1, periodLift axial.2) +
          (step : ℝ) • direction τ + periodVector (periodLift axial.1, periodLift axial.2) =
        basisMap axial + (step : ℝ) • direction τ := by
    abel
  rw [rearranged] at shifted
  have rotated := (RotationInvariant.pow_mem_iff redSet invariant (k : ℕ) _).2 shifted
  have rotated_eq : (rotate ^ (k : ℕ)) (basisMap axial + (step : ℝ) • direction τ) =
      start + (21 : ℝ) • dir + (step : ℝ) • dir := by
    rw [map_add, map_smul, haxial, LinearIsometryEquiv.apply_symm_apply, ← hdir]
  rw [rotated_eq] at rotated
  have step_nonneg : 0 ≤ 21 + step := by omega
  refine ⟨⟨(21 + step).toNat, by omega⟩, ?_⟩
  have cast_eq : (((21 + step).toNat : ℕ) : ℝ) = 21 + (step : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg step_nonneg
  show start + (((21 + step).toNat : ℕ) : ℝ) • dir ∈ redSet
  rw [cast_eq, add_smul, ← add_assoc]
  exact rotated

end Erdos188.UpperBound
