module

public import Erdos188.LowerBound.Bessel.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The tail of the kernel

Coarse bounds on `J₀(1)` and `J₀'(1)`, the decreasing energy
`H(x) = x (J₀' + J₀/(2x))² + (x + 1/(4x)) J₀²`, the consequence `4x J₀(x)² ≤ 3` for
`x ≥ 1`, and positivity of the kernel `F(t)` for `t ≥ 81` from eleven integer
fourth-power comparisons.
-/

@[expose] public section

namespace Erdos188.LowerBound

open Real

/-- The quartic Taylor bound `cos x ≤ 1 - x²/2 + x⁴/24`. -/
theorem cos_le_quartic (x : ℝ) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  wlog hx : 0 ≤ x generalizing x
  · simpa [Even.neg_pow (by decide : Even 4)] using this (-x) (by linarith)
  have hf (y : ℝ) : HasDerivAt (fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - cos y)
      (sin y - (y - y ^ 3 / 6)) y := by
    convert ((((hasDerivAt_pow 2 y).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 y).div_const 24)).sub (hasDerivAt_cos y) using 1
    norm_num
    ring
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun y _ => (hf y).continuousAt.continuousWithinAt) (fun y _ => (hf y).hasDerivWithinAt)
    (fun y hy => by
      rw [interior_Ici] at hy
      linarith [sin_ge_sub_cube (le_of_lt hy)])
  have := hmono Set.self_mem_Ici hx hx
  norm_num at this
  linarith

/-- The integral of an even quartic in `cos θ` over a full period. -/
theorem integral_quartic_cos (a b c : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, (a + b * cos θ ^ 2 + c * cos θ ^ 4) =
      2 * π * (a + b / 2 + 3 * c / 8) := by
  have h2 : ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 = π := by simp
  have h4 : ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 4 = 3 * π / 4 := by
    have := integral_cos_pow (a := 0) (b := 2 * π) (n := 2)
    norm_num at this
    rw [this]
    ring
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h2, h4,
    intervalIntegral.integral_const]
  · simp
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- `s sin s ≤ s²`. -/
theorem mul_sin_le_sq (s : ℝ) : s * sin s ≤ s ^ 2 :=
  calc s * sin s ≤ |s| * |sin s| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |s| * |s| := mul_le_mul_of_nonneg_left abs_sin_le_abs (abs_nonneg s)
    _ = s ^ 2 := by rw [← sq, sq_abs]

/-- `s² - s⁴/6 ≤ s sin s`. -/
theorem sq_sub_le_mul_sin (s : ℝ) : s ^ 2 - s ^ 4 / 6 ≤ s * sin s := by
  wlog hs : 0 ≤ s generalizing s
  · simpa [Even.neg_pow (by decide : Even 4)] using this (-s) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left (sin_ge_sub_cube hs) hs]

theorem besselJ0_one_bounds : 3 / 4 ≤ besselJ0 1 ∧ besselJ0 1 ≤ 49 / 64 := by
  have hlo := intervalIntegral.integral_mono (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (by positivity)
    (f := fun θ => 1 + -1 / 2 * cos θ ^ 2 + 0 * cos θ ^ 4) (g := fun θ => cos (1 * cos θ))
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun θ => by simp only [one_mul]; linarith [one_sub_sq_div_two_le_cos (x := cos θ)])
  have hhi := intervalIntegral.integral_mono (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (by positivity)
    (f := fun θ => cos (1 * cos θ)) (g := fun θ => 1 + -1 / 2 * cos θ ^ 2 + 1 / 24 * cos θ ^ 4)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun θ => by simp only [one_mul]; linarith [cos_le_quartic (cos θ)])
  simp only [integral_quartic_cos] at hlo hhi
  have hπ := pi_pos
  unfold besselJ0
  constructor
  · rw [le_inv_mul_iff₀ (by positivity)]
    linarith
  · rw [inv_mul_le_iff₀ (by positivity)]
    linarith

theorem besselJ0Deriv_one_bounds : -1 / 2 ≤ besselJ0Deriv 1 ∧ besselJ0Deriv 1 ≤ -7 / 16 := by
  have hlo := intervalIntegral.integral_mono (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (by positivity)
    (f := fun θ => 0 + 1 * cos θ ^ 2 + -1 / 6 * cos θ ^ 4)
    (g := fun θ => cos θ * sin (1 * cos θ))
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun θ => by simp only [one_mul]; linarith [sq_sub_le_mul_sin (cos θ)])
  have hhi := intervalIntegral.integral_mono (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (by positivity)
    (f := fun θ => cos θ * sin (1 * cos θ)) (g := fun θ => 0 + 1 * cos θ ^ 2 + 0 * cos θ ^ 4)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun θ => by simp only [one_mul]; linarith [mul_sin_le_sq (cos θ)])
  simp only [integral_quartic_cos] at hlo hhi
  have hπ := pi_pos
  set I := ∫ θ in (0 : ℝ)..2 * π, cos θ * sin (1 * cos θ)
  have h₁ : (2 * π)⁻¹ * I ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have h₂ : 7 / 16 ≤ (2 * π)⁻¹ * I := by
    rw [le_inv_mul_iff₀ (by positivity)]
    linarith
  unfold besselJ0Deriv
  constructor <;> linarith

/-- The energy `H(x) = x (J₀' + J₀/(2x))² + (x + 1/(4x)) J₀²`. -/
noncomputable def besselEnergy (x : ℝ) : ℝ :=
  x * (besselJ0Deriv x + besselJ0 x / (2 * x)) ^ 2 + (x + 1 / (4 * x)) * besselJ0 x ^ 2

/-- `H' = -J₀²/(2x²)` by Bessel's equation. -/
theorem hasDerivAt_besselEnergy {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt besselEnergy (-(besselJ0 x ^ 2 / (2 * x ^ 2))) x := by
  have hJ := hasDerivAt_besselJ0 x
  have hJ' := hasDerivAt_besselJ0Deriv x
  have hid := hasDerivAt_id' x
  convert ((hid.mul ((hJ'.add (hJ.div (hid.const_mul 2) (by positivity))).pow 2)).add
    ((hid.add ((hasDerivAt_const x 1).div (hid.const_mul 4) (by positivity))).mul
      (hJ.pow 2))) using 1
  · rfl
  simp only [Pi.add_apply, Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat, pow_one,
    Nat.add_one_sub_one]
  field_simp
  linear_combination (-16 * x * (2 * x * besselJ0Deriv x + besselJ0 x)) * besselJ0_ode x

/-- The energy is nonincreasing on `[1, ∞)`. -/
theorem antitoneOn_besselEnergy : AntitoneOn besselEnergy (Set.Ici 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
    (fun x hx => (hasDerivAt_besselEnergy ?_).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_besselEnergy ?_).hasDerivWithinAt) (fun x _ => ?_)
  · exact (zero_lt_one.trans_le hx).ne'
  · rw [interior_Ici] at hx
    exact (zero_lt_one.trans hx).ne'
  · exact neg_nonpos.mpr (by positivity)

/-- The energy of `√x J₀(x)` bounds `J₀` for `x ≥ 1`. -/
theorem four_mul_sq_besselJ0_le {x : ℝ} (hx : 1 ≤ x) : 4 * x * besselJ0 x ^ 2 ≤ 3 := by
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_one_bounds
  obtain ⟨hJ'₁, hJ'₂⟩ := besselJ0Deriv_one_bounds
  have h₁ : besselEnergy 1 ≤ 12261 / 16384 := by
    unfold besselEnergy
    nlinarith
  have h₂ := antitoneOn_besselEnergy Set.self_mem_Ici hx hx
  have h₃ : x * besselJ0 x ^ 2 ≤ besselEnergy x := by
    unfold besselEnergy
    have hx₀ : 0 < x := by linarith
    have := mul_nonneg hx₀.le (sq_nonneg (besselJ0Deriv x + besselJ0 x / (2 * x)))
    have : 0 ≤ 1 / (4 * x) * besselJ0 x ^ 2 := by positivity
    nlinarith
  nlinarith

/-- `|J₀(√n t)| ≤ R/2304` for `t ≥ 81` whenever `9 · 256⁴ ≤ 16 n R⁴`. -/
theorem abs_besselJ0_sqrt_mul_le {n : ℕ} {R t : ℝ} (hR : 0 ≤ R)
    (hnR : 9 * 256 ^ 4 ≤ 16 * n * R ^ 4) (ht : 81 ≤ t) :
    |besselJ0 (√n * t)| ≤ R / 2304 := by
  have hn : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · norm_num [h] at hnR
    · exact_mod_cast h
  have hs : 1 ≤ √(n : ℝ) := one_le_sqrt.mpr hn
  have hss : √(n : ℝ) ^ 2 = n := sq_sqrt (by positivity)
  set s := √(n : ℝ)
  set J := besselJ0 (s * t)
  have h₁ : 324 * s * J ^ 2 ≤ 3 := by
    nlinarith [four_mul_sq_besselJ0_le (x := s * t) (by nlinarith),
      mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 4 * s * J ^ 2)]
  have h₂ : 3 * 2304 ^ 2 ≤ 324 * s * R ^ 2 := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    nlinarith
  have h₃ : J ^ 2 ≤ (R / 2304) ^ 2 := by
    have : 324 * s * (J ^ 2 * 2304 ^ 2) ≤ 324 * s * R ^ 2 := by nlinarith
    have := le_of_mul_le_mul_left this (by positivity)
    rw [div_pow, le_div_iff₀ (by positivity)]
    linarith
  exact (sq_le_sq.mp h₃).trans_eq (abs_of_nonneg (by positivity))

/-- `F(t) ≥ 1915/192` for `t ≥ 81`. -/
theorem kernelF_tail {t : ℝ} (ht : 81 ≤ t) : 1915 / 192 ≤ kernelF t := by
  let R : Fin 11 → ℕ := ![222, 169, 157, 137, 128, 117, 111, 104, 94, 91, 87]
  have hR : ∀ i, 9 * 256 ^ 4 ≤ 16 * kernelRadius i * R i ^ 4 := by decide
  have hterm (i : Fin 11) : -(|(kernelCoeff i : ℝ)| * (R i / 2304)) ≤
      (kernelCoeff i : ℝ) * besselJ0 (√(kernelRadius i : ℝ) * t) := by
    have h := abs_besselJ0_sqrt_mul_le (R := R i) (by positivity) (by exact_mod_cast hR i) ht
    calc -(|(kernelCoeff i : ℝ)| * (R i / 2304))
        ≤ -(|(kernelCoeff i : ℝ)| * |besselJ0 (√(kernelRadius i : ℝ) * t)|) := by gcongr
      _ = -|(kernelCoeff i : ℝ) * besselJ0 (√(kernelRadius i : ℝ) * t)| := by rw [abs_mul]
      _ ≤ (kernelCoeff i : ℝ) * besselJ0 (√(kernelRadius i : ℝ) * t) := neg_abs_le _
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  have : ∑ i : Fin 11, -(|(kernelCoeff i : ℝ)| * (R i / 2304)) = -(34757 / 192) := by
    simp [Fin.sum_univ_succ, kernelCoeff, R]
    norm_num
  unfold kernelF
  linarith

end Erdos188.LowerBound
