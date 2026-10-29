module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy estimates for approximate solutions of Bessel's equation

Let `y` solve `t y'' + y' + n t y = 0` and let `p` be an approximate solution with
residual `R = p'' + p'/t + n p`. For the error `e = y - p` and its energy
`E = e'² + n e²`, we have `E' = -2e'²/t - 2e'R ≤ 2√E |R|`, so
`√E(t) ≤ √E(a) + ∫ₐᵗ |R|`. The residual is given as `R` with `t R(t)` equal to the
residual numerator, so the estimate also covers the singular endpoint `a = 0`.
-/

@[expose] public section

namespace Erdos188.LowerBound

open Real Set

/-- Energy estimate: the energy of the error grows at most by the integrated residual. -/
theorem energy_error_bound {n a b : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a)
    {y y' y'' p p' p'' R : ℝ → ℝ}
    (hyc : ContinuousOn y (Icc a b)) (hy'c : ContinuousOn y' (Icc a b))
    (hpc : ContinuousOn p (Icc a b)) (hp'c : ContinuousOn p' (Icc a b))
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (y' t) t)
    (hy' : ∀ t ∈ Ioo a b, HasDerivAt y' (y'' t) t)
    (hp : ∀ t ∈ Ioo a b, HasDerivAt p (p' t) t)
    (hp' : ∀ t ∈ Ioo a b, HasDerivAt p' (p'' t) t)
    (hode : ∀ t ∈ Ioo a b, t * y'' t + y' t + n * t * y t = 0)
    (hR : ∀ t ∈ Ioo a b, t * p'' t + p' t + n * t * p t = t * R t)
    (hRc : ContinuousOn R (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    √((y' t - p' t) ^ 2 + n * (y t - p t) ^ 2) ≤
      √((y' a - p' a) ^ 2 + n * (y a - p a) ^ 2) + ∫ s in a..t, |R s| := by
  set E : ℝ → ℝ := fun s ↦ (y' s - p' s) ^ 2 + n * (y s - p s) ^ 2
  have hE0 : ∀ s, 0 ≤ E s := fun s ↦ by positivity
  have hEc : ContinuousOn E (Icc a b) :=
    ((hy'c.sub hp'c).pow 2).add (continuousOn_const.mul ((hyc.sub hpc).pow 2))
  -- `E' = -2e'²/s - 2e'R ≤ 2 |e'| |R|` on the open interval, where `s > 0`
  set E' : ℝ → ℝ := fun s ↦
    2 * (y' s - p' s) * (y'' s - p'' s) + n * (2 * (y s - p s) * (y' s - p' s))
  have hEd : ∀ s ∈ Ioo a b, HasDerivAt E (E' s) s := fun s hs ↦
    (((hy' s hs).sub (hp' s hs)).pow 2 |>.congr_deriv (by simp only [Pi.sub_apply]; ring)).add
      ((((hy s hs).sub (hp s hs)).pow 2).const_mul n |>.congr_deriv
        (by simp only [Pi.sub_apply]; ring))
  have hE'le : ∀ s ∈ Ioo a b, E' s ≤ 2 * |y' s - p' s| * |R s| := by
    intro s hs
    have hs0 : 0 < s := ha.trans_lt hs.1
    have key : s * E' s = -2 * (y' s - p' s) ^ 2 - 2 * s * ((y' s - p' s) * R s) := by
      linear_combination (2 * (y' s - p' s)) * (hode s hs) - (2 * (y' s - p' s)) * (hR s hs)
    have habs : -((y' s - p' s) * R s) ≤ |y' s - p' s| * |R s| := by
      rw [← abs_mul]; exact neg_le_abs _
    refine le_of_mul_le_mul_left ?_ hs0
    nlinarith [sq_nonneg (y' s - p' s)]
  -- the integrated residual is continuous, with derivative `|R|` on the open interval
  have hab : a ≤ b := ht.1.trans ht.2
  have hRa : ContinuousOn (fun s ↦ |R s|) (Icc a b) := hRc.abs
  have hIc : ContinuousOn (fun s ↦ ∫ u in a..s, |R u|) (Icc a b) := by
    simpa [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval (a := a) (b := b)
        (μ := MeasureTheory.volume) (by simpa [uIcc_of_le hab] using hRa.integrableOn_Icc)
  have hI' : ∀ s ∈ Ioo a b, HasDerivAt (fun s ↦ ∫ u in a..s, |R u|) |R s| s := fun s hs ↦
    intervalIntegral.integral_hasDerivAt_right
      ((hRa.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hRa.mono Ioo_subset_Icc_self) s hs)
      (hRa.continuousAt (Icc_mem_nhds hs.1 hs.2))
  -- for `η > 0`, `√(E + η²) - ∫ |R|` is antitone
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have hEη : ∀ s, 0 < E s + η ^ 2 := fun s ↦ by positivity
  have hanti : AntitoneOn (fun s ↦ √(E s + η ^ 2) - ∫ u in a..s, |R u|) (Icc a t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a t)
      (((hEc.add continuousOn_const).sqrt).sub hIc |>.mono (Icc_subset_Icc le_rfl ht.2))
      (f' := fun s ↦ E' s / (2 * √(E s + η ^ 2)) - |R s|) ?_ ?_ <;> rw [interior_Icc] <;>
      intro s hs <;> have hs' : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le ht.2⟩
    · exact (((hEd s hs').add_const _).sqrt (hEη s).ne' |>.sub (hI' s hs')).hasDerivWithinAt
    · have hsq : |y' s - p' s| ≤ √(E s + η ^ 2) := by
        rw [← sqrt_sq_eq_abs]
        exact sqrt_le_sqrt (by nlinarith [sq_nonneg (y s - p s), sq_nonneg η])
      rw [sub_nonpos, div_le_iff₀ (by positivity)]
      nlinarith [hE'le s hs', abs_nonneg (R s)]
  have h := hanti ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  simp only [intervalIntegral.integral_same, sub_zero] at h
  have h1 : √(E t) ≤ √(E t + η ^ 2) := sqrt_le_sqrt (by linarith [sq_nonneg η])
  have h2 : √(E a + η ^ 2) ≤ √(E a) + η := by
    rw [sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_sqrt (hE0 a), sqrt_nonneg (E a)]
  linarith

/-- The energy norm changes by at most `|d'| + q|d|` when the approximation jumps by
`(d, d')`, where `n ≤ q²`. -/
theorem sqrt_energy_join {n q : ℝ} (hn : 0 ≤ n) (hq : 0 ≤ q) (hqn : n ≤ q ^ 2)
    (e e' d d' : ℝ) :
    √((e' + d') ^ 2 + n * (e + d) ^ 2) ≤ √(e' ^ 2 + n * e ^ 2) + |d'| + q * |d| := by
  set S := √(e' ^ 2 + n * e ^ 2)
  have hS : S ^ 2 = e' ^ 2 + n * e ^ 2 := sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := sqrt_nonneg _
  -- `S ≥ |e'|` and `q S ≥ n |e|`
  have h1 : |e'| ≤ S := by
    rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt (by nlinarith [sq_nonneg e])
  have h2 : n * |e| ≤ q * S := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, sq_abs, hS]
    nlinarith [mul_nonneg (sub_nonneg.2 hqn) (sq_nonneg S), mul_nonneg hn (sq_nonneg e')]
  rw [sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h3 : e' * d' ≤ S * |d'| := by
    calc e' * d' ≤ |e'| * |d'| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ S * |d'| := by gcongr
  have h4 : n * (e * d) ≤ q * S * |d| := by
    calc n * (e * d) ≤ n * |e| * |d| := by
          rw [mul_assoc, ← abs_mul]; exact mul_le_mul_of_nonneg_left (le_abs_self _) hn
      _ ≤ q * S * |d| := by gcongr
  have h5 : n * d ^ 2 ≤ q ^ 2 * |d| ^ 2 := by
    rw [sq_abs]; exact mul_le_mul_of_nonneg_right hqn (sq_nonneg d)
  nlinarith [sq_abs d', abs_nonneg d', abs_nonneg d, mul_nonneg hq (abs_nonneg d),
    mul_nonneg (abs_nonneg d') (mul_nonneg hq (abs_nonneg d))]

/-- The energy norm bounds the error itself when `1 ≤ n`. -/
theorem abs_le_sqrt_energy {n : ℝ} (hn : 1 ≤ n) (e e' : ℝ) :
    |e| ≤ √(e' ^ 2 + n * e ^ 2) := by
  rw [← sqrt_sq_eq_abs]
  exact sqrt_le_sqrt (by nlinarith [sq_nonneg e', sq_nonneg e])

end Erdos188.LowerBound
