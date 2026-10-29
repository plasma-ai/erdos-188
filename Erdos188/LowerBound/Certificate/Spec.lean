module

public import Erdos188.LowerBound.Certificate.Checker
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Meaning of the checker

The real-valued meaning of the rational checker's operations: coefficient lists evaluate to
polynomial functions with the expected derivatives, the residual numerator is the stated
expression, `absIntBound` bounds the integral of `|p|`, the combined polynomial is
`191 + ∑ᵢ Cᵢ pᵢ`, and a passing positivity check gives a pointwise lower bound.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

open Set

/-- The real polynomial function `x ↦ ∑ₖ c[k] xᵏ` of a rational coefficient list. -/
noncomputable def evalReal : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * evalReal cs x

theorem evalReal_cast (c : List ℚ) (x : ℚ) : evalReal c x = (evalPoly c x : ℝ) := by
  induction c with
  | nil => simp [evalReal, evalPoly]
  | cons c cs ih => simp [evalReal, evalPoly, ih]

theorem continuous_evalReal (c : List ℚ) : Continuous (evalReal c) := by
  induction c with
  | nil => exact continuous_const
  | cons c cs ih => exact continuous_const.add (continuous_id.mul ih)

/-! ### Evaluation of the list operations -/

theorem evalReal_addPoly (p q : List ℚ) (x : ℝ) :
    evalReal (addPoly p q) x = evalReal p x + evalReal q x := by
  induction p generalizing q with
  | nil => simp [addPoly, evalReal]
  | cons a p ih =>
    cases q with
    | nil => simp [addPoly, evalReal]
    | cons b q => simp only [addPoly, evalReal, ih, Rat.cast_add]; ring

theorem evalReal_scalePoly (r : ℚ) (p : List ℚ) (x : ℝ) :
    evalReal (scalePoly r p) x = r * evalReal p x := by
  induction p with
  | nil => simp [scalePoly, evalReal]
  | cons a p ih =>
    simp only [scalePoly, List.map_cons, evalReal] at ih ⊢
    rw [ih]; push_cast; ring

theorem evalReal_mulLinear (u w : ℚ) (p : List ℚ) (x : ℝ) :
    evalReal (mulLinear u w p) x = (u + w * x) * evalReal p x := by
  induction p with
  | nil => simp [mulLinear, evalReal]
  | cons a p ih =>
    simp only [mulLinear, evalReal, evalReal_addPoly, ih]; push_cast; ring

/-- `shiftPoly` is the affine substitution `x ↦ u + w * x`. -/
theorem evalReal_shiftPoly (u w : ℚ) (p : List ℚ) (x : ℝ) :
    evalReal (shiftPoly u w p) x = evalReal p (u + w * x) := by
  induction p with
  | nil => simp [shiftPoly, evalReal]
  | cons a p ih =>
    simp only [shiftPoly, evalReal, evalReal_addPoly, evalReal_mulLinear, ih]; ring

/-- `derivAux (k + 1) c` is `derivAux k c + c` coefficientwise. -/
theorem evalReal_derivAux_succ (k : ℕ) (c : List ℚ) (x : ℝ) :
    evalReal (derivAux (k + 1) c) x = evalReal (derivAux k c) x + evalReal c x := by
  induction c generalizing k with
  | nil => simp [derivAux, evalReal]
  | cons a c ih => simp only [derivAux, evalReal, ih]; push_cast; ring

/-- `derivAux 0 c` has coefficients `j * c[j]`, so it evaluates to `x * c'(x)`. -/
theorem evalReal_derivAux_zero (c : List ℚ) (x : ℝ) :
    evalReal (derivAux 0 c) x = x * evalReal (derivPoly c) x := by
  cases c <;> simp [derivAux, derivPoly, evalReal]

theorem hasDerivAt_evalReal (c : List ℚ) (x : ℝ) :
    HasDerivAt (evalReal c) (evalReal (derivPoly c) x) x := by
  induction c with
  | nil => simpa [evalReal, derivPoly] using hasDerivAt_const x (0 : ℝ)
  | cons a c ih =>
    have h := ((hasDerivAt_id x).mul ih).const_add (a : ℝ)
    rw [derivPoly, evalReal_derivAux_succ, evalReal_derivAux_zero]
    convert h using 1
    · funext y; simp [evalReal]
    · simp only [id, one_mul]; ring

theorem evalReal_residualNum (n a : ℚ) (p : List ℚ) (z : ℝ) :
    evalReal (residualNum n a p) z =
      (a + z) * evalReal (derivPoly (derivPoly p)) z + evalReal (derivPoly p) z +
        n * (a + z) * evalReal p z := by
  simp only [residualNum, evalReal_addPoly, evalReal_mulLinear, evalReal_scalePoly]
  push_cast; ring

/-- A coefficient list with zero constant term is `z` times its tail. -/
theorem evalReal_eq_mul_tail {q : List ℚ} (hq : q.headD 0 = 0) (z : ℝ) :
    evalReal q z = z * evalReal q.tail z := by
  cases q with
  | nil => simp [evalReal]
  | cons c q => simp_all [evalReal]

/-- Core's `Rat.abs` is the absolute value. -/
theorem rat_abs_eq (q : ℚ) : Rat.abs q = |q| := by
  unfold Rat.abs
  split_ifs with hq
  exacts [(abs_of_nonneg hq).symm, (abs_of_neg (not_le.mp hq)).symm]

/-- `absIntAux h hᵏ⁺¹ k c` bounds `∫₀ʰ |zᵏ ∑ⱼ c[j] zʲ| dz`. -/
theorem integral_abs_pow_mul_evalReal_le {h : ℚ} (hh : 0 ≤ h) (k : ℕ) (c : List ℚ) :
    ∫ z in (0 : ℝ)..h, |z ^ k * evalReal c z| ≤ (absIntAux h (h ^ (k + 1)) k c : ℝ) := by
  induction c generalizing k with
  | nil => simp [evalReal, absIntAux]
  | cons a c ih =>
    have hh' : (0 : ℝ) ≤ h := by exact_mod_cast hh
    have hc := continuous_evalReal c
    calc ∫ z in (0 : ℝ)..h, |z ^ k * evalReal (a :: c) z|
        ≤ ∫ z in (0 : ℝ)..h, (|(a : ℝ)| * z ^ k + |z ^ (k + 1) * evalReal c z|) := by
          refine intervalIntegral.integral_mono_on hh' ?_ ?_ fun z hz ↦ ?_
          · exact ((continuous_pow k).mul (continuous_evalReal _)).abs.intervalIntegrable _ _
          · exact (continuous_const.mul (continuous_pow k)).add
              ((continuous_pow (k + 1)).mul hc).abs |>.intervalIntegrable _ _
          · have hzk : 0 ≤ z ^ k := pow_nonneg hz.1 k
            calc |z ^ k * evalReal (a :: c) z| = |a * z ^ k + z ^ (k + 1) * evalReal c z| := by
                  rw [evalReal]; ring_nf
              _ ≤ |(a : ℝ)| * z ^ k + |z ^ (k + 1) * evalReal c z| := by
                  refine (abs_add_le _ _).trans_eq ?_
                  rw [abs_mul, abs_of_nonneg hzk]
      _ = |(a : ℝ)| * (h ^ (k + 1) / (k + 1)) +
            ∫ z in (0 : ℝ)..h, |z ^ (k + 1) * evalReal c z| := by
          rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, integral_pow]
          · simp
          · exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
          · exact ((continuous_pow (k + 1)).mul hc).abs.intervalIntegrable _ _
      _ ≤ |(a : ℝ)| * (h ^ (k + 1) / (k + 1)) +
            (absIntAux h (h ^ (k + 1 + 1)) (k + 1) c : ℝ) :=
          add_le_add_right (ih (k + 1)) _
      _ = (absIntAux h (h ^ (k + 1)) k (a :: c) : ℝ) := by
          rw [absIntAux, rat_abs_eq, ← pow_succ]
          push_cast
          ring

/-- `absIntBound h c` bounds `∫₀ʰ |∑ₖ c[k] zᵏ| dz`. -/
theorem integral_abs_evalReal_le {h : ℚ} (hh : 0 ≤ h) (c : List ℚ) :
    ∫ z in (0 : ℝ)..h, |evalReal c z| ≤ (absIntBound h c : ℝ) := by
  simpa [absIntBound] using integral_abs_pow_mul_evalReal_le hh 0 c

theorem evalReal_approxPoly_zero (k : ℕ) (i : Fin 11) :
    evalReal (approxPoly k i) 0 = (startValue k i).1 ∧
      evalReal (derivPoly (approxPoly k i)) 0 = (startValue k i).2 := by
  simp only [approxPoly, buildPoly, derivPoly, derivAux, evalReal]
  simp

theorem evalReal_foldr_addPoly {ι : Type*} (l : List ι) (C : ι → ℚ) (p : ι → List ℚ)
    (init : List ℚ) (z : ℝ) :
    evalReal (l.foldr (fun i acc ↦ addPoly (scalePoly (C i) (p i)) acc) init) z =
      evalReal init z + (l.map fun i ↦ (C i : ℝ) * evalReal (p i) z).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, evalReal_addPoly, evalReal_scalePoly, ih, List.map_cons,
      List.sum_cons]
    ring

theorem evalReal_combinedPoly (k : ℕ) (z : ℝ) :
    evalReal (combinedPoly k) z =
      191 + ∑ i : Fin 11, (kernelCoeff i : ℝ) * evalReal (approxPoly k i) z := by
  rw [combinedPoly, evalReal_foldr_addPoly, Fin.sum_univ_def]
  simp [evalReal]

/-! ### Bernstein coefficients -/

/-- The Bernstein basis polynomial `B_{N,j}(s) = (N choose j) * s ^ j * (1 - s) ^ (N - j)`. -/
noncomputable def bernsteinWeight (N j : ℕ) (s : ℝ) : ℝ :=
  N.choose j * s ^ j * (1 - s) ^ (N - j)

/-- `bernsteinForm N j b s = ∑ₗ b[l] * B_{N,j+l}(s)`. -/
noncomputable def bernsteinForm (N : ℕ) : ℕ → List ℚ → ℝ → ℝ
  | _, [], _ => 0
  | j, b :: bs, s => b * bernsteinWeight N j s + bernsteinForm N (j + 1) bs s

theorem bernsteinWeight_nonneg (N j : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ bernsteinWeight N j s := by
  have := hs.1
  have : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  unfold bernsteinWeight
  positivity

/-- `(j + 1) / (M + 1) * B_{M+1,j+1}(s) = s * B_{M,j}(s)`. -/
theorem succ_div_mul_bernsteinWeight (M j : ℕ) (s : ℝ) :
    ((j : ℝ) + 1) / ((M : ℝ) + 1) * bernsteinWeight (M + 1) (j + 1) s =
      s * bernsteinWeight M j s := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.add_one_mul_choose_eq M j)
  push_cast at h
  unfold bernsteinWeight
  rw [Nat.add_sub_add_right, pow_succ]
  field_simp
  linear_combination s * s ^ j * (1 - s) ^ (M - j) * h.symm

/-- The Bernstein basis polynomials of degree `N` sum to `1`. -/
theorem bernsteinForm_replicate_one (N : ℕ) (s : ℝ) :
    bernsteinForm N 0 (List.replicate (N + 1) 1) s = 1 := by
  have h : ∀ m j, bernsteinForm N j (List.replicate m 1) s =
      ∑ l ∈ Finset.range m, bernsteinWeight N (j + l) s := by
    intro m
    induction m with
    | zero => simp [bernsteinForm]
    | succ m ih =>
      intro j
      rw [List.replicate_succ, bernsteinForm, ih, Finset.sum_range_succ']
      simp only [Rat.cast_one, one_mul, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [add_assoc, add_comm 1 l]
  have h1 := add_pow s (1 - s) N
  rw [add_sub_cancel, one_pow] at h1
  rw [h, h1]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [zero_add, bernsteinWeight]
  ring

theorem length_bernsteinAux (a : ℚ) (N j : ℕ) (bs : List ℚ) :
    (bernsteinAux a N j bs).length = bs.length := by
  induction bs generalizing j with
  | nil => rfl
  | cons b bs ih => simp [bernsteinAux, ih]

theorem length_bernstein (c : List ℚ) : (bernstein c).length = c.length := by
  induction c with
  | nil => rfl
  | cons a c ih => simp [bernstein, length_bernsteinAux, ih]

theorem bernsteinForm_bernsteinAux (a : ℚ) (M j : ℕ) (bs : List ℚ) (s : ℝ) :
    bernsteinForm (M + 1) (j + 1) (bernsteinAux a (M + 1) j bs) s =
      a * bernsteinForm (M + 1) (j + 1) (List.replicate bs.length 1) s +
        s * bernsteinForm M j bs s := by
  induction bs generalizing j with
  | nil => simp [bernsteinAux, bernsteinForm]
  | cons b bs ih =>
    simp only [bernsteinAux, bernsteinForm, List.length_cons, List.replicate_succ, ih]
    push_cast
    linear_combination (b : ℝ) * succ_div_mul_bernsteinWeight M j s

/-- `evalReal c s = ∑ⱼ (bernstein c)[j] * B_{N,j}(s)` for `c` of length `N + 1`. -/
theorem evalReal_eq_bernsteinForm (a : ℚ) (cs : List ℚ) (s : ℝ) :
    evalReal (a :: cs) s = bernsteinForm cs.length 0 (bernstein (a :: cs)) s := by
  induction cs generalizing a with
  | nil => simp [bernstein, bernsteinAux, bernsteinForm, bernsteinWeight, evalReal]
  | cons a' cs ih =>
    have h1 := bernsteinForm_replicate_one (cs.length + 1) s
    rw [List.replicate_succ, bernsteinForm, Rat.cast_one, one_mul] at h1
    rw [bernstein, List.length_cons, bernsteinForm, bernsteinForm_bernsteinAux,
      length_bernstein, List.length_cons, ← ih, evalReal]
    linear_combination -(a : ℝ) * h1

theorem le_bernsteinForm {β : ℚ} {bs : List ℚ} (hb : ∀ b ∈ bs, β ≤ b) (N j : ℕ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    β * bernsteinForm N j (List.replicate bs.length 1) s ≤ bernsteinForm N j bs s := by
  induction bs generalizing j with
  | nil => simp [bernsteinForm]
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hb
    simp only [List.length_cons, List.replicate_succ, bernsteinForm, Rat.cast_one, one_mul,
      mul_add]
    have hβ : (β : ℝ) ≤ b := by exact_mod_cast hb.1
    have := ih hb.2 (j + 1)
    have := mul_le_mul_of_nonneg_right hβ (bernsteinWeight_nonneg N j hs)
    linarith

/-- A polynomial is at least the minimum of its Bernstein coefficients on `[0, 1]`. -/
theorem le_evalReal_of_bernstein {β : ℚ} {c : List ℚ} (hc : c ≠ [])
    (hb : ∀ b ∈ bernstein c, β ≤ b) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (β : ℝ) ≤ evalReal c s := by
  obtain ⟨a, cs, rfl⟩ := List.exists_cons_of_ne_nil hc
  have h := le_bernsteinForm hb cs.length 0 hs
  rw [length_bernstein, List.length_cons, bernsteinForm_replicate_one, mul_one] at h
  rw [evalReal_eq_bernsteinForm]
  exact h

theorem shiftPoly_ne_nil (u w : ℚ) {p : List ℚ} (hp : p ≠ []) : shiftPoly u w p ≠ [] := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hp
  rw [shiftPoly]
  cases mulLinear u w (shiftPoly u w cs) <;> simp [addPoly]

/-- A passing piece check bounds the polynomial below by the error budget on the piece. -/
theorem errorBudget_le_of_checkPiece {P : List ℚ} (hP : P ≠ []) {u v : ℚ}
    (hc : checkPiece P u v = true) {z : ℝ} (hz : z ∈ Icc (u : ℝ) v) :
    (errorBudget : ℝ) ≤ evalReal P z := by
  simp only [checkPiece, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨huv, hb⟩ := hc
  have huv' : (0 : ℝ) < v - u := sub_pos.mpr (by exact_mod_cast huv)
  have hs : (z - u) / (v - u) ∈ Icc (0 : ℝ) 1 := by
    rw [mem_Icc, div_le_one huv']
    exact ⟨div_nonneg (sub_nonneg.mpr hz.1) huv'.le, by linarith [hz.2]⟩
  have h := le_evalReal_of_bernstein (shiftPoly_ne_nil u (v - u) hP) hb hs
  rw [evalReal_shiftPoly] at h
  convert h using 2
  push_cast
  field_simp
  ring

/-- A passing positivity check bounds the polynomial below by the error budget, for a
nonempty coefficient list. -/
theorem errorBudget_le_of_checkPieces_of_ne_nil {P : List ℚ} (hP : P ≠ []) {h u : ℚ}
    {vs : List ℚ} (hc : checkPieces P h u vs = true) {z : ℝ} (hz : z ∈ Icc (u : ℝ) h) :
    (errorBudget : ℝ) ≤ evalReal P z := by
  induction vs generalizing u with
  | nil => simp [checkPieces] at hc
  | cons v vs ih =>
    cases vs with
    | nil =>
      simp only [checkPieces, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc, rfl⟩ := hc
      exact errorBudget_le_of_checkPiece hP hc hz
    | cons w vs =>
      simp only [checkPieces, Bool.and_eq_true] at hc
      rcases le_total z v with hzv | hzv
      · exact errorBudget_le_of_checkPiece hP hc.1 ⟨hz.1, hzv⟩
      · exact ih hc.2 ⟨hzv, hz.2⟩

theorem addPoly_ne_nil (p : List ℚ) {q : List ℚ} (hq : q ≠ []) : addPoly p q ≠ [] := by
  cases p <;> cases q <;> simp_all [addPoly]

/-- The combined polynomial is nonempty, being built on `[191]`. -/
theorem combinedPoly_ne_nil (k : ℕ) : combinedPoly k ≠ [] := by
  rw [combinedPoly]
  induction List.finRange 11 with
  | nil => simp
  | cons i l ih => exact addPoly_ne_nil _ ih

theorem errorBound_nonneg (k : ℕ) (i : Fin 11) : 0 ≤ errorBound k i := by
  rw [errorBound, Rat.mkRat_eq_div]
  positivity

theorem foldr_add_eq_sum {ι : Type*} (l : List ι) (f : ι → ℚ) :
    l.foldr (fun i s ↦ f i + s) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

theorem totalError_eq :
    totalError = ∑ i : Fin 11, |(kernelCoeff i : ℚ)| *
      ∑ k ∈ Finset.range numIntervals, errorBound k i := by
  rw [totalError, Fin.sum_univ_def, ← foldr_add_eq_sum]
  simp only [foldr_add_eq_sum (List.range numIntervals), rat_abs_eq, Finset.sum_eq_multiset_sum,
    Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

end Erdos188.LowerBound.Certificate
