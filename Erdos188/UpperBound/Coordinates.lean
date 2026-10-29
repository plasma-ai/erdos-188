module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Coordinates for periodic disk families

The physical plane with its Euclidean norm, the axial coordinate system with
its quadratic form and scale, the basis equivalence between the two, the
one-step rotation as a linear isometry equivalence with its powers, the
rational and integer axial coordinate maps, and the period vectors of the
integer lattice. The product type is used only for axial coordinates; the
physical plane keeps its Euclidean norm. Every statement is generic: no finite
family or numeric table appears here. The conventions follow the
construction outlined in the repository `README.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Erdos188.UpperBound

/-- The physical Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The physical length of one axial basis vector. -/
def scale : ℝ := 21 / 100

/-- The quadratic form in axial coordinates. -/
def axialQ (a : ℝ × ℝ) : ℝ := a.1 ^ 2 + a.1 * a.2 + a.2 ^ 2

theorem sqrt_three_pos : 0 < Real.sqrt 3 :=
  Real.sqrt_pos.mpr (by norm_num)

theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 :=
  ne_of_gt sqrt_three_pos

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

theorem scale_pos : 0 < scale := by
  norm_num [scale]

theorem scale_ne_zero : scale ≠ 0 :=
  ne_of_gt scale_pos

/-- Equality of the two physical coordinates determines a plane vector. -/
theorem plane_ext (x y : Plane) (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem plane_norm_sq (x : Plane) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]

/-- The axial basis map, with its explicit inverse in physical coordinates. -/
def basisMap : (ℝ × ℝ) ≃ₗ[ℝ] Plane where
  toFun a := !₂[scale * (a.1 + a.2 / 2), scale * (Real.sqrt 3 * a.2 / 2)]
  invFun x := ((100 / 21 : ℝ) * (x 0 - x 1 / Real.sqrt 3),
    (200 / 21 : ℝ) * x 1 / Real.sqrt 3)
  left_inv a := by
    apply Prod.ext
    · change (100 / 21 : ℝ) *
          (scale * (a.1 + a.2 / 2) - scale * (Real.sqrt 3 * a.2 / 2) /
            Real.sqrt 3) = a.1
      dsimp [scale]
      field_simp [sqrt_three_ne_zero]
      ring
    · change (200 / 21 : ℝ) * (scale * (Real.sqrt 3 * a.2 / 2)) /
          Real.sqrt 3 = a.2
      dsimp [scale]
      field_simp [sqrt_three_ne_zero]
      ring
  right_inv x := by
    apply plane_ext
    · change scale * ((100 / 21 : ℝ) * (x 0 - x 1 / Real.sqrt 3) +
          ((200 / 21 : ℝ) * x 1 / Real.sqrt 3) / 2) = x 0
      dsimp [scale]
      field_simp [sqrt_three_ne_zero]
      ring
    · change scale * (Real.sqrt 3 * ((200 / 21 : ℝ) * x 1 / Real.sqrt 3) / 2) = x 1
      dsimp [scale]
      field_simp [sqrt_three_ne_zero]
      ring
  map_add' a b := by
    apply plane_ext
    · change scale * (a.1 + b.1 + (a.2 + b.2) / 2) =
          scale * (a.1 + a.2 / 2) + scale * (b.1 + b.2 / 2)
      ring
    · change scale * (Real.sqrt 3 * (a.2 + b.2) / 2) =
          scale * (Real.sqrt 3 * a.2 / 2) + scale * (Real.sqrt 3 * b.2 / 2)
      ring
  map_smul' r a := by
    apply plane_ext
    · change scale * (r * a.1 + r * a.2 / 2) = r * (scale * (a.1 + a.2 / 2))
      ring
    · change scale * (Real.sqrt 3 * (r * a.2) / 2) =
          r * (scale * (Real.sqrt 3 * a.2 / 2))
      ring

@[simp]
theorem basisMap_apply_zero (a : ℝ × ℝ) :
    basisMap a 0 = scale * (a.1 + a.2 / 2) := rfl

@[simp]
theorem basisMap_apply_one (a : ℝ × ℝ) :
    basisMap a 1 = scale * (Real.sqrt 3 * a.2 / 2) := rfl

theorem basisMap_apply (a : ℝ × ℝ) :
    basisMap a = !₂[scale * (a.1 + a.2 / 2), scale * (Real.sqrt 3 * a.2 / 2)] :=
  rfl

theorem basisMap_symm_apply (x : Plane) :
    basisMap.symm x = ((100 / 21 : ℝ) * (x 0 - x 1 / Real.sqrt 3),
      (200 / 21 : ℝ) * x 1 / Real.sqrt 3) := rfl

/-- The exact physical norm associated with the axial quadratic form. -/
theorem basisMap_norm_sq (a : ℝ × ℝ) :
    ‖basisMap a‖ ^ 2 = (441 / 10000 : ℝ) * axialQ a := by
  rw [plane_norm_sq, basisMap_apply_zero, basisMap_apply_one]
  calc
    (scale * (a.1 + a.2 / 2)) ^ 2 + (scale * (Real.sqrt 3 * a.2 / 2)) ^ 2 =
        scale ^ 2 * (a.1 ^ 2 + a.1 * a.2 + (1 + Real.sqrt 3 ^ 2) / 4 * a.2 ^ 2) :=
      by ring
    _ = (441 / 10000 : ℝ) * axialQ a := by
      rw [sqrt_three_sq]
      norm_num [scale, axialQ]

/-- The same axial rotation matrix over any commutative coefficient ring. -/
def axialRotation (R : Type*) [CommRing R] : (R × R) ≃ₗ[R] (R × R) where
  toFun a := (-a.2, a.1 + a.2)
  invFun a := (a.1 + a.2, -a.1)
  left_inv a := by
    apply Prod.ext <;> dsimp <;> ring
  right_inv a := by
    apply Prod.ext <;> dsimp <;> ring
  map_add' a b := by
    apply Prod.ext <;> dsimp <;> ring
  map_smul' r a := by
    apply Prod.ext
    · change -(r * a.2) = r * (-a.2)
      ring
    · change r * a.1 + r * a.2 = r * (a.1 + a.2)
      ring

@[simp]
theorem axialRotation_apply (R : Type*) [CommRing R] (a : R × R) :
    axialRotation R a = (-a.2, a.1 + a.2) := rfl

@[simp]
theorem axialRotation_symm_apply (R : Type*) [CommRing R] (a : R × R) :
    (axialRotation R).symm a = (a.1 + a.2, -a.1) := rfl

theorem axialRotation_pow_three (R : Type*) [CommRing R] (a : R × R) :
    (axialRotation R ^ 3) a = -a := by
  simp only [pow_succ, pow_zero, LinearEquiv.mul_apply, LinearEquiv.coe_one,
    Function.id_def, axialRotation_apply]
  apply Prod.ext <;> dsimp <;> ring

theorem axialRotation_pow_five (R : Type*) [CommRing R] (a : R × R) :
    (axialRotation R ^ 5) a = (a.1 + a.2, -a.1) := by
  simp only [pow_succ, pow_zero, LinearEquiv.mul_apply, LinearEquiv.coe_one,
    Function.id_def, axialRotation_apply]
  apply Prod.ext <;> dsimp <;> ring

theorem axialRotation_pow_six (R : Type*) [CommRing R] :
    axialRotation R ^ 6 = 1 := by
  apply LinearEquiv.ext
  intro a
  rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, LinearEquiv.mul_apply]
  simp only [axialRotation_pow_three, neg_neg, LinearEquiv.coe_one, Function.id_def]

theorem axialRotation_symm_eq_pow_five (R : Type*) [CommRing R] :
    (axialRotation R).symm = axialRotation R ^ 5 := by
  apply LinearEquiv.ext
  intro a
  rw [axialRotation_symm_apply, axialRotation_pow_five]

/-- Axial rotation on real coordinates. -/
def axialRotateReal : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) := axialRotation ℝ

/-- Axial rotation on rational site centers. -/
def axialRotateRat : (ℚ × ℚ) ≃ₗ[ℚ] (ℚ × ℚ) := axialRotation ℚ

/-- Axial rotation on integer period lifts. -/
def axialRotateInt : (ℤ × ℤ) ≃ₗ[ℤ] (ℤ × ℤ) := axialRotation ℤ

@[simp]
theorem axialRotateReal_apply (a : ℝ × ℝ) :
    axialRotateReal a = (-a.2, a.1 + a.2) := rfl

@[simp]
theorem axialRotateRat_apply (a : ℚ × ℚ) :
    axialRotateRat a = (-a.2, a.1 + a.2) := rfl

@[simp]
theorem axialRotateInt_apply (a : ℤ × ℤ) :
    axialRotateInt a = (-a.2, a.1 + a.2) := rfl

theorem axialRotateReal_pow_three (a : ℝ × ℝ) :
    (axialRotateReal ^ 3) a = -a := axialRotation_pow_three ℝ a

theorem axialRotateReal_pow_six : axialRotateReal ^ 6 = 1 :=
  axialRotation_pow_six ℝ

theorem axialRotateRat_pow_six : axialRotateRat ^ 6 = 1 :=
  axialRotation_pow_six ℚ

theorem axialRotateInt_pow_six : axialRotateInt ^ 6 = 1 :=
  axialRotation_pow_six ℤ

@[simp]
theorem axialRotateInt_symm_apply (a : ℤ × ℤ) :
    axialRotateInt.symm a = (a.1 + a.2, -a.1) := rfl

theorem axialRotateInt_symm_eq_pow_five : axialRotateInt.symm = axialRotateInt ^ 5 :=
  axialRotation_symm_eq_pow_five ℤ

theorem axialQ_axialRotateReal (a : ℝ × ℝ) :
    axialQ (axialRotateReal a) = axialQ a := by
  dsimp [axialQ, axialRotateReal, axialRotation]
  ring

/-- The physical rotation, obtained from its exact axial matrix. -/
def rotate : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv := (basisMap.symm.trans axialRotateReal).trans basisMap
  norm_map' x := by
    change ‖basisMap (axialRotateReal (basisMap.symm x))‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      ‖basisMap (axialRotateReal (basisMap.symm x))‖ ^ 2 =
          (441 / 10000 : ℝ) * axialQ (basisMap.symm x) := by
        rw [basisMap_norm_sq, axialQ_axialRotateReal]
      _ = ‖basisMap (basisMap.symm x)‖ ^ 2 :=
        (basisMap_norm_sq (basisMap.symm x)).symm
      _ = ‖x‖ ^ 2 := by rw [basisMap.apply_symm_apply]

theorem rotate_basisMap (a : ℝ × ℝ) :
    rotate (basisMap a) = basisMap (axialRotateReal a) := by
  change basisMap (axialRotateReal (basisMap.symm (basisMap a))) =
    basisMap (axialRotateReal a)
  rw [basisMap.symm_apply_apply]

/-- The Cartesian formula fixes the sign and orientation of the rotation. -/
theorem rotate_apply (x : Plane) :
    rotate x = !₂[(x 0 - Real.sqrt 3 * x 1) / 2,
      (Real.sqrt 3 * x 0 + x 1) / 2] := by
  obtain ⟨a, rfl⟩ := basisMap.surjective x
  rw [rotate_basisMap]
  apply plane_ext
  · change scale * (-a.2 + (a.1 + a.2) / 2) =
      (scale * (a.1 + a.2 / 2) - Real.sqrt 3 *
        (scale * (Real.sqrt 3 * a.2 / 2))) / 2
    calc
      scale * (-a.2 + (a.1 + a.2) / 2) =
          (scale * (a.1 + a.2 / 2) - scale * Real.sqrt 3 ^ 2 * a.2 / 2) / 2 := by
        rw [sqrt_three_sq]
        ring
      _ = (scale * (a.1 + a.2 / 2) - Real.sqrt 3 *
          (scale * (Real.sqrt 3 * a.2 / 2))) / 2 := by ring
  · change scale * (Real.sqrt 3 * (a.1 + a.2) / 2) =
      (Real.sqrt 3 * (scale * (a.1 + a.2 / 2)) +
        scale * (Real.sqrt 3 * a.2 / 2)) / 2
    ring

@[simp]
theorem rotate_apply_zero (x : Plane) :
    rotate x 0 = (x 0 - Real.sqrt 3 * x 1) / 2 :=
  congrArg (fun y : Plane => y 0) (rotate_apply x)

@[simp]
theorem rotate_apply_one (x : Plane) :
    rotate x 1 = (Real.sqrt 3 * x 0 + x 1) / 2 :=
  congrArg (fun y : Plane => y 1) (rotate_apply x)

theorem rotate_norm (x : Plane) : ‖rotate x‖ = ‖x‖ :=
  rotate.norm_map x

theorem rotate_dist (x y : Plane) : dist (rotate x) (rotate y) = dist x y :=
  rotate.dist_map x y

theorem rotate_pow_basisMap (k : ℕ) (a : ℝ × ℝ) :
    (rotate ^ k) (basisMap a) = basisMap ((axialRotateReal ^ k) a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply,
        LinearEquiv.mul_apply, ih, rotate_basisMap]

theorem rotate_pow_three (x : Plane) : (rotate ^ 3) x = -x := by
  obtain ⟨a, rfl⟩ := basisMap.surjective x
  rw [rotate_pow_basisMap, axialRotateReal_pow_three, map_neg]

theorem rotate_pow_six : rotate ^ 6 = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := basisMap.surjective x
  simpa only [axialRotateReal_pow_six, LinearEquiv.coe_one,
    LinearIsometryEquiv.coe_one, Function.id_def] using rotate_pow_basisMap 6 a

/-- Cast a rational axial center to physical real coefficients. -/
def ratAxialToReal (a : ℚ × ℚ) : ℝ × ℝ := ((a.1 : ℝ), (a.2 : ℝ))

/-- Cast an integer period lift to real axial coefficients. -/
def intAxialToReal (a : ℤ × ℤ) : ℝ × ℝ := ((a.1 : ℝ), (a.2 : ℝ))

/-- Cast an integer period lift to rational site coordinates. -/
def intAxialToRat (a : ℤ × ℤ) : ℚ × ℚ := ((a.1 : ℚ), (a.2 : ℚ))

@[simp]
theorem ratAxialToReal_zero : ratAxialToReal 0 = 0 := by
  simp [ratAxialToReal]

@[simp]
theorem ratAxialToReal_add (a b : ℚ × ℚ) :
    ratAxialToReal (a + b) = ratAxialToReal a + ratAxialToReal b := by
  ext <;> simp [ratAxialToReal]

@[simp]
theorem ratAxialToReal_neg (a : ℚ × ℚ) :
    ratAxialToReal (-a) = -ratAxialToReal a := by
  ext <;> simp [ratAxialToReal]

@[simp]
theorem ratAxialToReal_sub (a b : ℚ × ℚ) :
    ratAxialToReal (a - b) = ratAxialToReal a - ratAxialToReal b := by
  ext <;> simp [ratAxialToReal]

@[simp]
theorem ratAxialToReal_smul (r : ℚ) (a : ℚ × ℚ) :
    ratAxialToReal (r • a) = (r : ℝ) • ratAxialToReal a := by
  ext <;> simp [ratAxialToReal, smul_eq_mul]

@[simp]
theorem intAxialToReal_zero : intAxialToReal 0 = 0 := by
  simp [intAxialToReal]

@[simp]
theorem intAxialToReal_add (a b : ℤ × ℤ) :
    intAxialToReal (a + b) = intAxialToReal a + intAxialToReal b := by
  ext <;> simp [intAxialToReal]

@[simp]
theorem intAxialToReal_neg (a : ℤ × ℤ) :
    intAxialToReal (-a) = -intAxialToReal a := by
  ext <;> simp [intAxialToReal]

@[simp]
theorem intAxialToReal_sub (a b : ℤ × ℤ) :
    intAxialToReal (a - b) = intAxialToReal a - intAxialToReal b := by
  ext <;> simp [intAxialToReal]

@[simp]
theorem intAxialToReal_smul (r : ℤ) (a : ℤ × ℤ) :
    intAxialToReal (r • a) = (r : ℝ) • intAxialToReal a := by
  ext <;> simp [intAxialToReal, smul_eq_mul]

@[simp]
theorem intAxialToRat_zero : intAxialToRat 0 = 0 := by
  simp [intAxialToRat]

@[simp]
theorem intAxialToRat_add (a b : ℤ × ℤ) :
    intAxialToRat (a + b) = intAxialToRat a + intAxialToRat b := by
  ext <;> simp [intAxialToRat]

@[simp]
theorem intAxialToRat_neg (a : ℤ × ℤ) :
    intAxialToRat (-a) = -intAxialToRat a := by
  ext <;> simp [intAxialToRat]

@[simp]
theorem intAxialToRat_sub (a b : ℤ × ℤ) :
    intAxialToRat (a - b) = intAxialToRat a - intAxialToRat b := by
  ext <;> simp [intAxialToRat]

@[simp]
theorem intAxialToRat_smul (r : ℤ) (a : ℤ × ℤ) :
    intAxialToRat (r • a) = (r : ℚ) • intAxialToRat a := by
  ext <;> simp [intAxialToRat, smul_eq_mul]

@[simp]
theorem ratAxialToReal_intAxialToRat (a : ℤ × ℤ) :
    ratAxialToReal (intAxialToRat a) = intAxialToReal a := by
  ext <;> simp [ratAxialToReal, intAxialToRat, intAxialToReal]

theorem axialRotateRat_cast (a : ℚ × ℚ) :
    axialRotateReal (ratAxialToReal a) = ratAxialToReal (axialRotateRat a) := by
  ext <;> simp [ratAxialToReal]

theorem axialRotateInt_cast (a : ℤ × ℤ) :
    axialRotateReal (intAxialToReal a) = intAxialToReal (axialRotateInt a) := by
  ext <;> simp [intAxialToReal]

theorem axialRotateInt_ratCast (a : ℤ × ℤ) :
    axialRotateRat (intAxialToRat a) = intAxialToRat (axialRotateInt a) := by
  ext <;> simp [intAxialToRat]

/-- The physical period attached to an unrestricted integer lattice lift. -/
def periodVector (n : ℤ × ℤ) : Plane :=
  basisMap ((59 : ℝ) • intAxialToReal n)

theorem periodVector_eq (n : ℤ × ℤ) :
    periodVector n = basisMap ((59 : ℝ) * (n.1 : ℝ), (59 : ℝ) * (n.2 : ℝ)) := rfl

@[simp]
theorem periodVector_zero : periodVector 0 = 0 := by
  simp [periodVector]

@[simp]
theorem periodVector_add (m n : ℤ × ℤ) :
    periodVector (m + n) = periodVector m + periodVector n := by
  simp [periodVector, smul_add]

@[simp]
theorem periodVector_neg (n : ℤ × ℤ) : periodVector (-n) = -periodVector n := by
  simp [periodVector]

@[simp]
theorem periodVector_sub (m n : ℤ × ℤ) :
    periodVector (m - n) = periodVector m - periodVector n := by
  simp [periodVector, smul_sub]

theorem rotate_periodVector (n : ℤ × ℤ) :
    rotate (periodVector n) = periodVector (axialRotateInt n) := by
  simp only [periodVector, rotate_basisMap, map_smul, axialRotateInt_cast]

theorem rotate_pow_periodVector (k : ℕ) (n : ℤ × ℤ) :
    (rotate ^ k) (periodVector n) = periodVector ((axialRotateInt ^ k) n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [pow_succ', LinearIsometryEquiv.coe_mul, Function.comp_apply,
        LinearEquiv.mul_apply, ih, rotate_periodVector]

theorem rotate_symm_periodVector (n : ℤ × ℤ) :
    rotate.symm (periodVector n) = periodVector (axialRotateInt.symm n) := by
  apply rotate.injective
  rw [rotate.apply_symm_apply, rotate_periodVector, axialRotateInt.apply_symm_apply]

/-- Rotation permutes the entire period lattice, with no bound on its lifts. -/
theorem rotate_image_periodLattice :
    rotate '' Set.range periodVector = Set.range periodVector := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨axialRotateInt n, (rotate_periodVector n).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨periodVector (axialRotateInt.symm n), ⟨axialRotateInt.symm n, rfl⟩, ?_⟩
    rw [rotate_periodVector, axialRotateInt.apply_symm_apply]

end Erdos188.UpperBound
