module

public import Erdos188.LowerBound.Bessel.Basic
public import Erdos188.LowerBound.Bessel.ODEError
public import Erdos188.LowerBound.Certificate.Run
public import Erdos188.LowerBound.Certificate.Spec
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Soundness of the rational certificate

The polynomial approximations built by the checker are within the certified error of
`J₀(√n t)` on `[0, 81]` (by the energy estimate and the join bounds), and their weighted
combination has Bernstein coefficients above the error budget, so `F(t) ≥ 0` there.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

open Real Set

/-! ### The scaled Bessel function -/

lemma hasDerivAt_besselJ0_mul (c t : ℝ) :
    HasDerivAt (fun t ↦ besselJ0 (c * t)) (c * besselJ0Deriv (c * t)) t :=
  ((hasDerivAt_besselJ0 (c * t)).comp t ((hasDerivAt_id' t).const_mul c)).congr_deriv
    (by ring)

lemma hasDerivAt_besselJ0Deriv_mul (c t : ℝ) :
    HasDerivAt (fun t ↦ c * besselJ0Deriv (c * t)) (c * c * besselJ0Deriv2 (c * t)) t :=
  (((hasDerivAt_besselJ0Deriv (c * t)).comp t ((hasDerivAt_id' t).const_mul c)).const_mul
    c).congr_deriv (by ring)

/-- `y(t) = J₀(√n t)` solves `t y'' + y' + n t y = 0`, with `y'(t) = √n J₀'(√n t)` and
`y''(t) = n J₀''(√n t)`. -/
theorem besselJ0_scaled_ode {n : ℝ} (hn : 0 ≤ n) (t : ℝ) :
    t * (n * besselJ0Deriv2 (√n * t)) + √n * besselJ0Deriv (√n * t) +
      n * t * besselJ0 (√n * t) = 0 := by
  linear_combination √n * besselJ0_ode (√n * t) -
    (t * besselJ0Deriv2 (√n * t) + t * besselJ0 (√n * t)) * sq_sqrt hn

/-! ### The energy of the error -/

/-- The energy `(y' - p')² + n (y - p)²` at `t` of the error of the approximation
`p(t) = evalReal c (t - a)` of `y(t) = J₀(√n t)`. -/
noncomputable def errorEnergy (n a : ℝ) (c : List ℚ) (t : ℝ) : ℝ :=
  (√n * besselJ0Deriv (√n * t) - evalReal (derivPoly c) (t - a)) ^ 2 +
    n * (besselJ0 (√n * t) - evalReal c (t - a)) ^ 2

/-- A passing `residualBound` gives a continuous residual `R` of `p(t) = evalReal c (t - a)`
on `[a, a + h]`, with `t R(t) = t p''(t) + p'(t) + n t p(t)` and `∫ |R| ≤ r`. -/
theorem exists_residual {n a : ℕ} {h r : ℚ} {c : List ℚ} (hh : 0 ≤ h)
    (hr : residualBound n a h c = some r) :
    ∃ R : ℝ → ℝ, ContinuousOn R (Icc (a : ℝ) (a + h)) ∧
      (∀ t : ℝ, 0 < t → t * evalReal (derivPoly (derivPoly c)) (t - a) +
        evalReal (derivPoly c) (t - a) + n * t * evalReal c (t - a) = t * R t) ∧
      ∫ s in (a : ℝ)..(a + h), |R s| ≤ r := by
  have hQ (t : ℝ) : evalReal (residualNum n a c) (t - a) =
      t * evalReal (derivPoly (derivPoly c)) (t - a) + evalReal (derivPoly c) (t - a) +
        n * t * evalReal c (t - a) := by
    rw [evalReal_residualNum]
    push_cast
    ring
  simp only [residualBound] at hr
  split_ifs at hr with ha hq
  · -- `a = 0`: the residual is the polynomial `evalReal Q.tail`
    obtain rfl := Option.some.inj hr
    subst ha
    simp only [Nat.cast_zero, sub_zero, zero_add] at hQ hq ⊢
    exact ⟨evalReal (residualNum n 0 c).tail, (continuous_evalReal _).continuousOn,
      fun t _ ↦ by rw [← hQ, evalReal_eq_mul_tail hq], integral_abs_evalReal_le hh _⟩
  · -- `a > 0`: the residual is `R(t) = Q(t - a) / t`, and `t ≥ a` on the interval
    obtain rfl := Option.some.inj hr
    have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
    have hRc : ContinuousOn (fun t ↦ evalReal (residualNum n a c) (t - a) / t)
        (Icc (a : ℝ) (a + h)) :=
      ((continuous_evalReal _).comp (continuous_id.sub continuous_const)).continuousOn.div
        continuousOn_id fun t ht ↦ (ha0.trans_le ht.1).ne'
    refine ⟨fun t ↦ evalReal (residualNum n a c) (t - a) / t, hRc,
      fun t ht ↦ by rw [mul_div_cancel₀ _ ht.ne', hQ], ?_⟩
    have hah : (a : ℝ) ≤ a + h := le_add_of_nonneg_right (by exact_mod_cast hh)
    calc ∫ s in (a : ℝ)..(a + h), |evalReal (residualNum n a c) (s - a) / s|
        ≤ ∫ s in (a : ℝ)..(a + h), |evalReal (residualNum n a c) (s - a)| / a := by
          refine intervalIntegral.integral_mono_on hah
            (hRc.abs.intervalIntegrable_of_Icc hah)
            (((continuous_evalReal _).comp (continuous_id.sub continuous_const)).abs.div_const
              _ |>.intervalIntegrable _ _) fun s hs ↦ ?_
          rw [abs_div, abs_of_pos (ha0.trans_le hs.1)]
          exact div_le_div_of_nonneg_left (abs_nonneg _) ha0 hs.1
      _ = (∫ z in (0 : ℝ)..h, |evalReal (residualNum n a c) z|) / a := by
          rw [intervalIntegral.integral_div,
            intervalIntegral.integral_comp_sub_right (fun z ↦ |evalReal (residualNum n a c) z|),
            sub_self, add_sub_cancel_left]
      _ ≤ (absIntBound h (residualNum n a c) : ℝ) / a :=
          div_le_div_of_nonneg_right (integral_abs_evalReal_le hh _) ha0.le
      _ = ((absIntBound h (residualNum n a c) / a : ℚ) : ℝ) := by push_cast; rfl

/-- The energy estimate on one interval: the energy norm of the error grows by at most the
residual bound. -/
theorem sqrt_errorEnergy_le {n a : ℕ} {h r : ℚ} {c : List ℚ} (hh : 0 ≤ h)
    (hr : residualBound n a h c = some r) {t : ℝ} (ht : t ∈ Icc (a : ℝ) (a + h)) :
    √(errorEnergy n a c t) ≤ √(errorEnergy n a c a) + r := by
  obtain ⟨R, hRc, hR, hRint⟩ := exists_residual hh hr
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hpc (c : List ℚ) : Continuous fun t : ℝ ↦ evalReal c (t - a) :=
    (continuous_evalReal c).comp (continuous_id.sub continuous_const)
  have hp (c : List ℚ) (t : ℝ) :
      HasDerivAt (fun t ↦ evalReal c (t - a)) (evalReal (derivPoly c) (t - a)) t :=
    (hasDerivAt_evalReal c (t - a)).comp_sub_const t a
  have key := energy_error_bound hn a.cast_nonneg
    (y := fun t ↦ besselJ0 (√n * t)) (y' := fun t ↦ √n * besselJ0Deriv (√n * t))
    (y'' := fun t ↦ n * besselJ0Deriv2 (√n * t))
    (continuous_besselJ0.comp (continuous_const.mul continuous_id)).continuousOn
    (continuous_const.mul
      (continuous_besselJ0Deriv.comp (continuous_const.mul continuous_id))).continuousOn
    (hpc c).continuousOn (hpc (derivPoly c)).continuousOn
    (fun t _ ↦ hasDerivAt_besselJ0_mul √n t)
    (fun t _ ↦ by simpa [mul_self_sqrt hn] using hasDerivAt_besselJ0Deriv_mul √n t)
    (fun t _ ↦ hp c t) (fun t _ ↦ hp (derivPoly c) t)
    (fun t _ ↦ besselJ0_scaled_ode hn t) (fun t ht ↦ hR t (a.cast_nonneg.trans_lt ht.1))
    hRc ht
  have hint : ∫ s in (a : ℝ)..t, |R s| ≤ ∫ s in (a : ℝ)..(a + h), |R s| :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun s ↦ abs_nonneg (R s))
      (hRc.abs.intervalIntegrable_of_Icc (ht.1.trans ht.2))
  simp only [errorEnergy]
  linarith

/-- The energy jump at a join: passing at `a + h` from `p(t) = evalReal c (t - a)` to
`p̃(t) = evalReal c' (t - (a + h))`, whose value and derivative at `a + h` are `c₀` and
`c₁`, increases the energy norm by at most `|p'(a + h) - c₁| + q |p(a + h) - c₀|`. -/
theorem sqrt_errorEnergy_join {n q : ℝ} (hn : 0 ≤ n) (hq : 0 ≤ q) (hqn : n ≤ q ^ 2)
    (a h : ℝ) {c c' : List ℚ} {c₀ c₁ : ℝ} (h₀ : evalReal c' 0 = c₀)
    (h₁ : evalReal (derivPoly c') 0 = c₁) :
    √(errorEnergy n (a + h) c' (a + h)) ≤
      √(errorEnergy n a c (a + h)) + |evalReal (derivPoly c) h - c₁| +
        q * |evalReal c h - c₀| := by
  set e := besselJ0 (√n * (a + h)) - evalReal c h
  set e' := √n * besselJ0Deriv (√n * (a + h)) - evalReal (derivPoly c) h
  have hE : errorEnergy n a c (a + h) = e' ^ 2 + n * e ^ 2 := by
    simp only [errorEnergy, add_sub_cancel_left, e, e']
  have hE' : errorEnergy n (a + h) c' (a + h) =
      (e' + (evalReal (derivPoly c) h - c₁)) ^ 2 + n * (e + (evalReal c h - c₀)) ^ 2 := by
    simp only [errorEnergy, sub_self, h₀, h₁, e, e']
    ring
  rw [hE, hE']
  exact sqrt_energy_join hn hq hqn e e' _ _

/-! ### The checks -/

lemma joinBound_nonneg (n : ℕ) (h : ℚ) (c : List ℚ) (s : ℚ × ℚ) :
    0 ≤ joinBound n h c s :=
  add_nonneg Rat.abs_nonneg (mul_nonneg (Nat.cast_nonneg _) Rat.abs_nonneg)

lemma joinBound_cast (n : ℕ) (h : ℚ) (c : List ℚ) (s : ℚ × ℚ) :
    (joinBound n h c s : ℝ) =
      |evalReal (derivPoly c) h - s.2| + joinWeight n * |evalReal c h - s.1| := by
  rw [evalReal_cast, evalReal_cast, joinBound, rat_abs_eq, rat_abs_eq]
  push_cast
  rfl

lemma checkRadius_eq_true {k : ℕ} (hk : k < numIntervals) (i : Fin 11) :
    checkRadius k i = true := by
  have h := checkInterval_eq_true k hk
  simp only [checkInterval, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  exact h.1 i

/-- The facts given by `checkRadius`: exact starting values on the first interval,
`n ≤ q_n²`, and a residual bound `r` with `r + join ≤ errorBound k i`. -/
theorem checkRadius_spec {k : ℕ} {i : Fin 11} (h : checkRadius k i = true) :
    (k = 0 → startValue k i = (1, 0)) ∧
      kernelRadius i ≤ joinWeight (kernelRadius i) * joinWeight (kernelRadius i) ∧
      ∃ r, residualBound (kernelRadius i) (intervalStart k) (intervalWidth k)
          (approxPoly k i) = some r ∧
        r + (if k + 1 < numIntervals then
            joinBound (kernelRadius i) (intervalWidth k) (approxPoly k i) (startValue (k + 1) i)
          else 0) ≤ errorBound k i := by
  simp only [checkRadius, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hs, hq⟩, hr⟩ := h
  refine ⟨fun hk ↦ ?_, hq, ?_⟩
  · simpa [hk] using hs
  · split at hr
    · exact ⟨_, ‹_›, of_decide_eq_true hr⟩
    · exact absurd hr Bool.false_ne_true

/-! ### The error of the approximations -/

lemma one_le_kernelRadius (i : Fin 11) : 1 ≤ kernelRadius i := by
  revert i
  decide

/-- At the start of interval `k`, the energy norm of the error of the `i`-th approximation is
at most the accumulated error bounds of the earlier intervals. -/
theorem sqrt_errorEnergy_start_le (i : Fin 11) :
    ∀ k, k < numIntervals →
      √(errorEnergy (kernelRadius i) (intervalStart k) (approxPoly k i) (intervalStart k)) ≤
        ∑ j ∈ Finset.range k, (errorBound j i : ℝ)
  | 0, hk => by
    have hs := (checkRadius_spec (checkRadius_eq_true hk i)).1 rfl
    obtain ⟨h₀, h₁⟩ := evalReal_approxPoly_zero 0 i
    rw [hs] at h₀ h₁
    simp [errorEnergy, intervalStart, h₀, h₁, besselJ0_zero, besselJ0Deriv_zero]
  | k + 1, hk => by
    have hk' : k < numIntervals := by omega
    obtain ⟨-, hqn, r, hr, hle⟩ := checkRadius_spec (checkRadius_eq_true hk' i)
    rw [ite_eq_left hk] at hle
    have hle' : (r : ℝ) + joinBound (kernelRadius i) (intervalWidth k) (approxPoly k i)
        (startValue (k + 1) i) ≤ errorBound k i := by exact_mod_cast hle
    rw [joinBound_cast] at hle'
    obtain ⟨h₀, h₁⟩ := evalReal_approxPoly_zero (k + 1) i
    have hb : ((intervalStart (k + 1) : ℕ) : ℝ) =
        intervalStart k + ((intervalWidth k : ℚ) : ℝ) := by
      rw [intervalWidth, ite_eq_left hk, intervalStart, intervalStart]
      push_cast
      ring
    have hjoin := sqrt_errorEnergy_join (Nat.cast_nonneg (kernelRadius i))
      (Nat.cast_nonneg (joinWeight (kernelRadius i)))
      (by rw [sq]; exact_mod_cast hqn) (intervalStart k) ((intervalWidth k : ℚ) : ℝ) h₀ h₁
      (c := approxPoly k i)
    have hstep := sqrt_errorEnergy_le (by positivity) hr
      (t := intervalStart k + ((intervalWidth k : ℚ) : ℝ))
      ⟨le_add_of_nonneg_right (by positivity), le_rfl⟩
    have ih := sqrt_errorEnergy_start_le i k hk'
    rw [hb, Finset.sum_range_succ]
    linarith

/-- On interval `k`, the `i`-th approximation is within the total error bound
`∑ⱼ errorBound j i` of `J₀(√n t)`. -/
theorem abs_besselJ0_sub_approx_le {k : ℕ} (hk : k < numIntervals) (i : Fin 11) {t : ℝ}
    (ht : t ∈ Icc (intervalStart k : ℝ) (intervalStart k + intervalWidth k)) :
    |besselJ0 (√(kernelRadius i) * t) - evalReal (approxPoly k i) (t - intervalStart k)| ≤
      ∑ j ∈ Finset.range numIntervals, (errorBound j i : ℝ) := by
  obtain ⟨-, -, r, hr, hle⟩ := checkRadius_spec (checkRadius_eq_true hk i)
  have hjoin : 0 ≤ if k + 1 < numIntervals then
      joinBound (kernelRadius i) (intervalWidth k) (approxPoly k i) (startValue (k + 1) i)
    else 0 := by
    split_ifs
    · exact joinBound_nonneg _ _ _ _
    · exact le_rfl
  have hr' : (r : ℝ) ≤ errorBound k i := by exact_mod_cast (by linarith : r ≤ errorBound k i)
  have hn : (1 : ℝ) ≤ kernelRadius i := by exact_mod_cast one_le_kernelRadius i
  calc |besselJ0 (√(kernelRadius i) * t) - evalReal (approxPoly k i) (t - intervalStart k)|
      ≤ √(errorEnergy (kernelRadius i) (intervalStart k) (approxPoly k i) t) :=
        abs_le_sqrt_energy hn _ _
    _ ≤ √(errorEnergy (kernelRadius i) (intervalStart k) (approxPoly k i) (intervalStart k)) +
        r := sqrt_errorEnergy_le (by positivity) hr (by simpa using ht)
    _ ≤ ∑ j ∈ Finset.range (k + 1), (errorBound j i : ℝ) := by
        rw [Finset.sum_range_succ]
        linarith [sqrt_errorEnergy_start_le i k hk]
    _ ≤ ∑ j ∈ Finset.range numIntervals, (errorBound j i : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
          fun j _ _ ↦ by exact_mod_cast errorBound_nonneg j i

/-! ### Positivity of the kernel -/

theorem kernelF_nonneg_of_le {t : ℝ} (h0 : 0 ≤ t) (h81 : t ≤ 81) : 0 ≤ kernelF t := by
  -- the interval `k` containing `t`
  obtain ⟨k, hk, ht⟩ : ∃ k, k < numIntervals ∧
      t ∈ Icc (intervalStart k : ℝ) (intervalStart k + intervalWidth k) := by
    rcases lt_or_ge t 80 with h80 | h80
    · have hfl : ⌊t / 2⌋₊ < 40 := (Nat.floor_lt (by positivity)).2 (by norm_num; linarith)
      refine ⟨⌊t / 2⌋₊, by rw [numIntervals]; omega, ?_, ?_⟩
      · have := Nat.floor_le (show 0 ≤ t / 2 by positivity)
        rw [intervalStart]
        push_cast
        linarith
      · have := Nat.lt_floor_add_one (t / 2)
        rw [intervalWidth, ite_eq_left (by rw [numIntervals]; omega), intervalStart]
        push_cast
        linarith
    · refine ⟨40, by decide, ?_, ?_⟩ <;>
        norm_num [intervalStart, intervalWidth, numIntervals] <;> linarith
  -- the combined polynomial is at least the error budget
  have hc := checkInterval_eq_true k hk
  simp only [checkInterval, Bool.and_eq_true] at hc
  have hP := errorBudget_le_of_checkPieces_of_ne_nil (combinedPoly_ne_nil k) hc.2
    (z := t - intervalStart k)
    ⟨by push_cast; linarith [ht.1], by push_cast; linarith [ht.2]⟩
  rw [evalReal_combinedPoly] at hP
  -- the weighted error is within the error budget
  have hE : ∑ i : Fin 11, |(kernelCoeff i : ℝ)| *
      ∑ j ∈ Finset.range numIntervals, (errorBound j i : ℝ) ≤ errorBudget := by
    have h := checkErrorBudget_eq_true
    rw [checkErrorBudget, decide_eq_true_eq, totalError_eq] at h
    exact_mod_cast h
  have hi (i : Fin 11) : -(|(kernelCoeff i : ℝ)| *
      ∑ j ∈ Finset.range numIntervals, (errorBound j i : ℝ)) ≤
      (kernelCoeff i : ℝ) * (besselJ0 (√(kernelRadius i) * t) -
        evalReal (approxPoly k i) (t - intervalStart k)) := by
    calc -(|(kernelCoeff i : ℝ)| * ∑ j ∈ Finset.range numIntervals, (errorBound j i : ℝ))
        ≤ -(|(kernelCoeff i : ℝ)| * |besselJ0 (√(kernelRadius i) * t) -
            evalReal (approxPoly k i) (t - intervalStart k)|) :=
          neg_le_neg (mul_le_mul_of_nonneg_left (abs_besselJ0_sub_approx_le hk i ht)
            (abs_nonneg _))
      _ ≤ _ := by rw [← abs_mul]; exact neg_abs_le _
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hi i
  simp only [Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib] at hsum
  have hb : (0 : ℝ) ≤ errorBudget := by norm_num [errorBudget]
  rw [kernelF]
  linarith

end Erdos188.LowerBound.Certificate
