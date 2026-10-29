module

public import Erdos188.UpperBound.Coordinates
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Rational directions for the periodic disk interface

The rational parametrization of unit directions on one sector, with its chord,
norm and difference identities and bounds; the closed direction intervals of
the dyadic subdivision with their midpoints, radii and error allowances; and
the cone parametrization by which every unit direction is a rotation power of
a sector direction (`direction_sector_covers`). Every statement is a generic
identity or bound; no finite construction or progression-hitting instance is
supplied. The plane, axial quadratic form, scale, basis equivalence, and
rotation come from `Coordinates`. The cone inverse uses `coneNumerator` and
`coneDenominator`, distinct from any family size or disk. The argument follows
the covering outlined in the repository `README.md`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Erdos188.UpperBound

/-- The positive scalar denominator of the rational direction map. -/
def directionDenom (τ : ℝ) : ℝ := τ ^ 2 + τ + 1

/-- The first axial numerator of the rational direction map. -/
def directionNumS (τ : ℝ) : ℝ := τ ^ 2 - 1

/-- The second axial numerator of the rational direction map. -/
def directionNumT (τ : ℝ) : ℝ := -τ * (τ + 2)

/-- The direction map in axial coordinates. -/
def directionAxial (τ : ℝ) : ℝ × ℝ :=
  ((100 / 21 : ℝ) * (directionNumS τ / directionDenom τ),
    (100 / 21 : ℝ) * (directionNumT τ / directionDenom τ))

/-- The physical direction given by the rational map at a real parameter. -/
def direction (τ : ℝ) : Plane := basisMap (directionAxial τ)

theorem directionDenom_pos (τ : ℝ) : 0 < directionDenom τ := by
  dsimp [directionDenom]
  nlinarith [sq_nonneg (τ + 1 / 2)]

theorem directionDenom_ne_zero (τ : ℝ) : directionDenom τ ≠ 0 :=
  ne_of_gt (directionDenom_pos τ)

theorem direction_numerator_identity (τ : ℝ) :
    (directionNumS τ) ^ 2 + directionNumS τ * directionNumT τ +
      (directionNumT τ) ^ 2 = (directionDenom τ) ^ 2 := by
  dsimp [directionNumS, directionNumT, directionDenom]
  ring

theorem direction_numS_difference (τ σ : ℝ) :
    directionNumS τ * directionDenom σ -
      directionNumS σ * directionDenom τ =
        (τ - σ) * (τ * σ + 2 * τ + 2 * σ + 1) := by
  dsimp [directionNumS, directionDenom]
  ring

theorem direction_numT_difference (τ σ : ℝ) :
    directionNumT τ * directionDenom σ -
      directionNumT σ * directionDenom τ =
        (τ - σ) * (τ * σ - τ - σ - 2) := by
  dsimp [directionNumT, directionDenom]
  ring

theorem direction_chord_polynomial (τ σ : ℝ) :
    axialQ (τ * σ + 2 * τ + 2 * σ + 1, τ * σ - τ - σ - 2) =
      3 * directionDenom τ * directionDenom σ := by
  dsimp [axialQ, directionDenom]
  ring

theorem direction_norm_sq (τ : ℝ) : ‖direction τ‖ ^ 2 = 1 := by
  rw [direction, basisMap_norm_sq]
  dsimp [directionAxial, axialQ, directionNumS, directionNumT]
  field_simp [directionDenom_ne_zero τ]
  dsimp [directionDenom]
  ring

theorem direction_norm (τ : ℝ) : ‖direction τ‖ = 1 := by
  have hsq := direction_norm_sq τ
  have hnonneg := norm_nonneg (direction τ)
  nlinarith

theorem direction_neg_two : direction (-2) = !₂[(1 : ℝ), 0] := by
  apply plane_ext <;>
    norm_num [direction, directionAxial, directionNumS, directionNumT,
      directionDenom, basisMap_apply_zero, basisMap_apply_one, scale]

theorem direction_neg_one :
    direction (-1) = !₂[(1 / 2 : ℝ), Real.sqrt 3 / 2] := by
  apply plane_ext <;>
    norm_num [direction, directionAxial, directionNumS, directionNumT,
      directionDenom, basisMap_apply_zero, basisMap_apply_one, scale]
  ring

/-- The exact squared chord length, for every pair of real parameters. -/
theorem direction_chord_sq (τ σ : ℝ) :
    ‖direction τ - direction σ‖ ^ 2 =
      3 * (τ - σ) ^ 2 / (directionDenom τ * directionDenom σ) := by
  change ‖basisMap (directionAxial τ) - basisMap (directionAxial σ)‖ ^ 2 = _
  rw [← map_sub basisMap, basisMap_norm_sq]
  dsimp [directionAxial, axialQ, directionNumS, directionNumT]
  field_simp [directionDenom_ne_zero τ, directionDenom_ne_zero σ]
  dsimp [directionDenom]
  ring

theorem directionDenom_sub (τ σ : ℝ) :
    directionDenom τ - directionDenom σ = (τ - σ) * (τ + σ + 1) := by
  dsimp [directionDenom]
  ring

/-- On the left of -1, increasing the parameter decreases its denominator. -/
theorem directionDenom_antitone {τ σ : ℝ} (horder : τ ≤ σ) (hσ : σ ≤ -1) :
    directionDenom σ ≤ directionDenom τ := by
  have hproduct : 0 ≤ (τ - σ) * (τ + σ + 1) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hid := directionDenom_sub τ σ
  linarith

/-- A chord bound using an upper endpoint and a certified parameter radius. -/
theorem direction_chord_bound {τ σ upper radius : ℝ}
    (hτ : τ ≤ upper) (hσ : σ ≤ upper) (hupper : upper ≤ -1)
    (hradius : 0 ≤ radius) (hdiff : |τ - σ| ≤ radius) :
    ‖direction τ - direction σ‖ ≤
      (1733 / 1000 : ℝ) * radius / directionDenom upper := by
  have hden := directionDenom_pos upper
  have hdenτ := directionDenom_pos τ
  have hdenσ := directionDenom_pos σ
  have hτden := directionDenom_antitone hτ hupper
  have hσden := directionDenom_antitone hσ hupper
  have hproduct : (directionDenom upper) ^ 2 ≤
      directionDenom τ * directionDenom σ := by
    simpa only [pow_two] using
      mul_le_mul hτden hσden (le_of_lt hden) (le_of_lt hdenτ)
  have hdiff_sq : (τ - σ) ^ 2 ≤ radius ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (τ - σ)) hradius).2 hdiff
    simpa only [sq_abs] using h
  have hcoefficient : (3 : ℝ) < (1733 / 1000 : ℝ) ^ 2 := by
    norm_num
  have hsquared : ‖direction τ - direction σ‖ ^ 2 ≤
      ((1733 / 1000 : ℝ) * radius / directionDenom upper) ^ 2 := by
    rw [direction_chord_sq]
    calc
      3 * (τ - σ) ^ 2 / (directionDenom τ * directionDenom σ) ≤
          3 * radius ^ 2 / (directionDenom τ * directionDenom σ) :=
        div_le_div_of_nonneg_right (by nlinarith)
          (le_of_lt (mul_pos hdenτ hdenσ))
      _ ≤ 3 * radius ^ 2 / (directionDenom upper) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden) hproduct
      _ ≤ ((1733 / 1000 : ℝ) ^ 2 * radius ^ 2) /
          (directionDenom upper) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_of_lt hcoefficient) (sq_nonneg radius))
          (le_of_lt (sq_pos_of_pos hden))
      _ = ((1733 / 1000 : ℝ) * radius / directionDenom upper) ^ 2 := by
        simp only [div_pow, mul_pow]
  have hright : 0 ≤ (1733 / 1000 : ℝ) * radius / directionDenom upper :=
    div_nonneg (mul_nonneg (by norm_num) hradius) (le_of_lt hden)
  exact (sq_le_sq₀ (norm_nonneg _) hright).1 hsquared

/-- Left endpoint of the closed dyadic parameter interval. -/
def directionLeft (d i : ℕ) : ℝ := -2 + (i : ℝ) / (2 : ℝ) ^ d

/-- Right endpoint of the closed dyadic parameter interval. -/
def directionRight (d i : ℕ) : ℝ := -2 + ((i : ℝ) + 1) / (2 : ℝ) ^ d

/-- Midpoint of the closed dyadic parameter interval. -/
def directionMidpoint (d i : ℕ) : ℝ :=
  -2 + (2 * (i : ℝ) + 1) / (2 : ℝ) ^ (d + 1)

/-- Half the length of a depth-d parameter interval. -/
def directionRadius (d : ℕ) : ℝ := 1 / (2 : ℝ) ^ (d + 1)

/-- The whole closed interval, including both dyadic endpoints. -/
def directionInterval (d i : ℕ) : Set ℝ :=
  Set.Icc (directionLeft d i) (directionRight d i)

/-- The rational physical direction-error allowance in the covering interface. -/
def directionError (d i : ℕ) : ℝ :=
  (1733 / 1000 : ℝ) * directionRadius d / directionDenom (directionRight d i)

theorem directionRadius_pos (d : ℕ) : 0 < directionRadius d := by
  dsimp [directionRadius]
  positivity

theorem directionMidpoint_sub_left (d i : ℕ) :
    directionMidpoint d i - directionLeft d i = directionRadius d := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  dsimp [directionMidpoint, directionLeft, directionRadius]
  simp only [pow_succ]
  field_simp [hpower]
  ring

theorem directionRight_sub_midpoint (d i : ℕ) :
    directionRight d i - directionMidpoint d i = directionRadius d := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  dsimp [directionMidpoint, directionRight, directionRadius]
  simp only [pow_succ]
  field_simp [hpower]
  ring

theorem directionLeft_ge_neg_two (d i : ℕ) : -2 ≤ directionLeft d i := by
  have hquotient : 0 ≤ (i : ℝ) / (2 : ℝ) ^ d := by positivity
  dsimp [directionLeft]
  linarith

theorem directionRight_le_neg_one (d i : ℕ) (hi : i < 2 ^ d) :
    directionRight d i ≤ -1 := by
  have hcast : (i : ℝ) + 1 ≤ (2 : ℝ) ^ d := by
    have hnat : i + 1 ≤ 2 ^ d := Nat.succ_le_of_lt hi
    have hreal : ((i + 1 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) := Nat.cast_le.2 hnat
    simpa using hreal
  have hpower : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
  have hquotient : ((i : ℝ) + 1) / (2 : ℝ) ^ d ≤ 1 :=
    (div_le_one hpower).2 hcast
  dsimp [directionRight]
  linarith

theorem directionMidpoint_mem (d i : ℕ) :
    directionMidpoint d i ∈ directionInterval d i := by
  change directionLeft d i ≤ directionMidpoint d i ∧
    directionMidpoint d i ≤ directionRight d i
  have hleft := directionMidpoint_sub_left d i
  have hright := directionRight_sub_midpoint d i
  have hradius := directionRadius_pos d
  constructor <;> linarith

theorem directionInterval_subset_sector (d i : ℕ) (hi : i < 2 ^ d) :
    directionInterval d i ⊆ Set.Icc (-2 : ℝ) (-1) := by
  intro τ hτ
  change directionLeft d i ≤ τ ∧ τ ≤ directionRight d i at hτ
  exact ⟨le_trans (directionLeft_ge_neg_two d i) hτ.1,
    le_trans hτ.2 (directionRight_le_neg_one d i hi)⟩

/-- The exact closed-interval error bound; no parameter samples are assumed. -/
theorem direction_error_dyadic (d i : ℕ) (hi : i < 2 ^ d)
    (τ : ℝ) (hτ : τ ∈ directionInterval d i) :
    ‖direction τ - direction (directionMidpoint d i)‖ ≤ directionError d i := by
  change directionLeft d i ≤ τ ∧ τ ≤ directionRight d i at hτ
  have hmid := directionMidpoint_mem d i
  change directionLeft d i ≤ directionMidpoint d i ∧
    directionMidpoint d i ≤ directionRight d i at hmid
  have hleft := directionMidpoint_sub_left d i
  have hright := directionRight_sub_midpoint d i
  have hdiff : |τ - directionMidpoint d i| ≤ directionRadius d := by
    apply abs_le.2
    constructor <;> linarith
  simpa only [directionError] using
    direction_chord_bound hτ.2 hmid.2 (directionRight_le_neg_one d i hi)
      (le_of_lt (directionRadius_pos d)) hdiff

/-- Numerator of the inverse parameter for the nonnegative axial cone. -/
def coneNumerator (α β : ℝ) : ℝ := 2 * α + β + 2

/-- Denominator of the inverse parameter for the nonnegative axial cone. -/
def coneDenominator (α β : ℝ) : ℝ := α + 2 * β + 1

/-- The inverse direction parameter associated with normalized cone coordinates. -/
def coneParameter (α β : ℝ) : ℝ := -coneNumerator α β / coneDenominator α β

theorem coneNumerator_pos (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 < coneNumerator α β := by
  dsimp [coneNumerator]
  linarith

theorem coneDenominator_pos (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 < coneDenominator α β := by
  dsimp [coneDenominator]
  linarith

theorem cone_beta_le_one (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hQ : axialQ (α, β) = 1) : β ≤ 1 := by
  change α ^ 2 + α * β + β ^ 2 = 1 at hQ
  have hproduct := mul_nonneg hα hβ
  nlinarith [sq_nonneg α]

theorem coneParameter_mem_sector (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hQ : axialQ (α, β) = 1) : coneParameter α β ∈ Set.Icc (-2 : ℝ) (-1) := by
  have hden := coneDenominator_pos α β hα hβ
  have hβone := cone_beta_le_one α β hα hβ hQ
  have hupper : coneNumerator α β ≤ 2 * coneDenominator α β := by
    dsimp [coneNumerator, coneDenominator]
    linarith
  have hlower : coneDenominator α β ≤ coneNumerator α β := by
    dsimp [coneNumerator, coneDenominator]
    linarith
  constructor
  · change -2 ≤ -coneNumerator α β / coneDenominator α β
    apply (le_div_iff₀ hden).2
    linarith
  · change -coneNumerator α β / coneDenominator α β ≤ -1
    apply (div_le_iff₀ hden).2
    linarith

theorem cone_polynomial_identities (α β : ℝ) (hQ : axialQ (α, β) = 1) :
    (coneNumerator α β) ^ 2 - coneNumerator α β * coneDenominator α β +
        (coneDenominator α β) ^ 2 = 3 * coneNumerator α β ∧
      (coneNumerator α β) ^ 2 - (coneDenominator α β) ^ 2 =
        3 * α * coneNumerator α β ∧
      coneNumerator α β * (2 * coneDenominator α β - coneNumerator α β) =
        3 * β * coneNumerator α β := by
  change α ^ 2 + α * β + β ^ 2 = 1 at hQ
  dsimp [coneNumerator, coneDenominator]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · ring

/-- The inverse cone parameter recovers both normalized axial coordinates. -/
theorem coneParameter_coordinates (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hQ : axialQ (α, β) = 1) :
    directionNumS (coneParameter α β) / directionDenom (coneParameter α β) = α ∧
      directionNumT (coneParameter α β) / directionDenom (coneParameter α β) = β := by
  have hden := ne_of_gt (coneDenominator_pos α β hα hβ)
  have hnum := ne_of_gt (coneNumerator_pos α β hα hβ)
  have hidentities := cone_polynomial_identities α β hQ
  have hD : directionDenom (coneParameter α β) =
      3 * coneNumerator α β / (coneDenominator α β) ^ 2 := by
    dsimp [directionDenom, coneParameter]
    field_simp [hden]
    nlinarith [hidentities.1]
  have hS : directionNumS (coneParameter α β) =
      3 * α * coneNumerator α β / (coneDenominator α β) ^ 2 := by
    dsimp [directionNumS, coneParameter]
    field_simp [hden]
    nlinarith [hidentities.2.1]
  have hT : directionNumT (coneParameter α β) =
      3 * β * coneNumerator α β / (coneDenominator α β) ^ 2 := by
    have h3 : 2 * coneDenominator α β - coneNumerator α β = 3 * β :=
      mul_left_cancel₀ hnum (by linear_combination hidentities.2.2)
    dsimp [directionNumT, coneParameter]
    field_simp [hden]
    linear_combination h3
  constructor
  · rw [hS, hD]
    field_simp [hden, hnum]
  · rw [hT, hD]
    field_simp [hden, hnum]

/-- Six closed cones cover every axial pair, with an explicit nonnegative preimage. -/
theorem axial_cone_decomposition (a : ℝ × ℝ) :
    ∃ k : Fin 6, ∃ q : ℝ × ℝ,
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧ a = (axialRotateReal ^ (k : ℕ)) q ∧
        axialQ q = axialQ a := by
  rcases a with ⟨s, t⟩
  by_cases hs : 0 ≤ s
  · by_cases ht : 0 ≤ t
    · refine ⟨⟨0, by norm_num⟩, (s, t), hs, ht, ?_, rfl⟩
      simp
    · by_cases hsum : 0 ≤ s + t
      · refine ⟨⟨5, by norm_num⟩, (-t, s + t), by linarith, hsum, ?_, ?_⟩
        · apply Prod.ext <;> simp [pow_succ, axialRotateReal_apply]
        · dsimp [axialQ]
          ring
      · refine ⟨⟨4, by norm_num⟩, (-s - t, s), by linarith, hs, ?_, ?_⟩
        · apply Prod.ext <;> simp [pow_succ, axialRotateReal_apply]
        · dsimp [axialQ]
          ring
  · by_cases ht : 0 ≤ t
    · by_cases hsum : 0 ≤ s + t
      · refine ⟨⟨1, by norm_num⟩, (s + t, -s), hsum, by linarith, ?_, ?_⟩
        · apply Prod.ext <;> simp [pow_succ, axialRotateReal_apply]
        · dsimp [axialQ]
          ring
      · refine ⟨⟨2, by norm_num⟩, (t, -s - t), ht, by linarith, ?_, ?_⟩
        · apply Prod.ext <;> simp [pow_succ, axialRotateReal_apply]
        · dsimp [axialQ]
          ring
    · refine ⟨⟨3, by norm_num⟩, (-s, -t), by linarith, by linarith, ?_, ?_⟩
      · apply Prod.ext <;> simp [pow_succ, axialRotateReal_apply]
      · dsimp [axialQ]
        ring

/-- Every physical unit direction is one of six rotates of the closed parameter sector. -/
theorem direction_sector_covers (w : Plane) (hw : ‖w‖ = 1) :
    ∃ k : Fin 6, ∃ τ : ℝ, τ ∈ Set.Icc (-2 : ℝ) (-1) ∧
      w = (rotate ^ (k : ℕ)) (direction τ) := by
  let a : ℝ × ℝ := basisMap.symm w
  rcases axial_cone_decomposition a with ⟨k, q, hqS, hqT, ha, hqQ⟩
  have hnorm : ‖basisMap a‖ ^ 2 = 1 := by
    change ‖basisMap (basisMap.symm w)‖ ^ 2 = 1
    rw [basisMap.apply_symm_apply, hw]
    norm_num
  have hqnorm : (441 / 10000 : ℝ) * axialQ q = 1 := by
    rw [hqQ, ← basisMap_norm_sq]
    exact hnorm
  let α : ℝ := scale * q.1
  let β : ℝ := scale * q.2
  have hscale : 0 ≤ scale := by norm_num [scale]
  have hα : 0 ≤ α := mul_nonneg hscale hqS
  have hβ : 0 ≤ β := mul_nonneg hscale hqT
  have hQ : axialQ (α, β) = 1 := by
    calc
      axialQ (α, β) = (441 / 10000 : ℝ) * axialQ q := by
        dsimp [α, β, scale, axialQ]
        ring
      _ = 1 := hqnorm
  let τ : ℝ := coneParameter α β
  have hτ : τ ∈ Set.Icc (-2 : ℝ) (-1) :=
    coneParameter_mem_sector α β hα hβ hQ
  have hcoordinates := coneParameter_coordinates α β hα hβ hQ
  have haxial : directionAxial τ = q := by
    apply Prod.ext
    · change (100 / 21 : ℝ) *
        (directionNumS (coneParameter α β) /
          directionDenom (coneParameter α β)) = q.1
      rw [hcoordinates.1]
      dsimp [α, scale]
      ring
    · change (100 / 21 : ℝ) *
        (directionNumT (coneParameter α β) /
          directionDenom (coneParameter α β)) = q.2
      rw [hcoordinates.2]
      dsimp [β, scale]
      ring
  refine ⟨k, τ, hτ, ?_⟩
  calc
    w = basisMap a := (basisMap.apply_symm_apply w).symm
    _ = basisMap ((axialRotateReal ^ (k : ℕ)) q) := congrArg basisMap ha
    _ = (rotate ^ (k : ℕ)) (basisMap q) := (rotate_pow_basisMap (k : ℕ) q).symm
    _ = (rotate ^ (k : ℕ)) (direction τ) := by rw [direction, haxial]

end Erdos188.UpperBound
