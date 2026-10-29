module

public import Erdos188.LowerBound.LabelModel
public import Erdos188.LowerBound.Pattern

/-!
# Correlation inequalities

Integrating the pointwise constraints of an admissible labeling against the stationary
measure: the density satisfies `7α ≥ 1`, unit-distance correlations vanish, correlations
are radial on `E`, and the fourteen-point inequality integrates to `Q(ρ) ≤ -6α`.
Stationarity cancels the expected potentials and the half-turn symmetrizes the cost.
In the kernel normalization, `322 ρ(1) + 32 Q(ρ) ≤ -192 α`.
-/

@[expose] public section

noncomputable section

namespace Erdos188.LowerBound.LabelModel

open MeasureTheory
open OAI OAI.PlaneFiveColor.Spectral

variable (ω₀ : Space)

/-- The algebraic point `√n` on the real axis. -/
def radialPoint (n : ℕ) : E := ⟨(√(n : ℝ) : ℂ), by
  apply mem_algebraicClosure_iff.mpr
  apply IsAlgebraic.of_pow (n := 2) two_pos
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa using isAlgebraic_natCast (R := ℚ) (A := ℂ) n⟩

lemma norm_radialPoint (n : ℕ) : ‖(radialPoint n : ℂ)‖ = √(n : ℝ) := by
  change ‖((√(n : ℝ) : ℝ) : ℂ)‖ = √(n : ℝ)
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-! ### Integrals over the stationary measure -/

attribute [local fun_prop] continuous_redAt

lemma integrable_of_continuous {g : Space → ℝ} (hg : Continuous g) :
    Integrable g (measure ω₀) :=
  hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

lemma integral_trans (a : E) (g : Space → ℝ) :
    ∫ ω, g (trans a ω) ∂measure ω₀ = ∫ ω, g ω ∂measure ω₀ :=
  (trans_preserving ω₀ a).integral_comp (transHomeo a).measurableEmbedding g

lemma integral_rotate (b : K) (g : Space → ℝ) :
    ∫ ω, g (rotate b ω) ∂measure ω₀ = ∫ ω, g ω ∂measure ω₀ :=
  (rotate_preserving ω₀ b).integral_comp (rotateHomeo b).measurableEmbedding g

lemma integral_redAt (a : E) : ∫ ω, redAt a ω ∂measure ω₀ = alpha ω₀ := by
  rw [alpha, ← integral_trans ω₀ a (redAt 0)]
  simp [redAt]

lemma integral_redAt_mul (a b : E) :
    ∫ ω, redAt a ω * redAt b ω ∂measure ω₀ = corr ω₀ (b - a) := by
  rw [corr, ← integral_trans ω₀ a (fun ω => redAt 0 ω * redAt (b - a) ω)]
  simp [redAt]

theorem one_le_seven_mul_alpha : 1 ≤ 7 * alpha ω₀ := by
  have h (ω : Space) : 1 ≤ ∑ j : Fin 7, redAt ((j : ℕ) : E) ω := by
    obtain ⟨j, hj⟩ := ω.property.2 0 1 (by simp)
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => ?_) (Finset.mem_univ j))
    · simp_all [redAt]
    · unfold redAt
      split_ifs <;> norm_num
  have hi := integral_mono (integrable_const 1)
    (integrable_finsetSum _ fun _ _ => integrable_of_continuous ω₀ (continuous_redAt _)) h
  rw [integral_const, integral_finsetSum _ fun _ _ =>
    integrable_of_continuous ω₀ (continuous_redAt _)] at hi
  simpa [integral_redAt] using hi

theorem corr_unit {u : E} (hu : ‖(u : ℂ)‖ = 1) : corr ω₀ u = 0 := by
  have h (ω : Space) : redAt 0 ω * redAt u ω = 0 := by
    have hn := ω.property.1 0 u (by simpa using hu)
    unfold redAt
    split_ifs <;> simp_all
  simp [corr, h]

theorem corr_radial {z w : E} (h : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) : corr ω₀ z = corr ω₀ w := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hw : w = 0 := by
      apply Subtype.ext
      simpa [eq_comm] using h
    rw [hw]
  have hz' : (z : ℂ) ≠ 0 := by simpa using hz
  let b : K := ⟨⟨((w / z : E) : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [IntermediateField.coe_div, norm_div, ← h, div_self (norm_ne_zero_iff.mpr hz')])⟩,
    mem_algebraicClosure_iff.mp (w / z).property⟩
  have hb : kCoeff b * z = w := by
    rw [show kCoeff b = w / z from rfl, div_mul_cancel₀ w hz]
  rw [← hb, corr, corr, ← integral_rotate ω₀ b (fun ω => redAt 0 ω * redAt z ω)]
  simp only [redAt, rotate_apply, mul_zero]
  rfl

lemma corr_eq_radialPoint {z : E} {n : ℕ} (h : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = n) :
    corr ω₀ z = corr ω₀ (radialPoint n) := by
  apply corr_radial
  rw [norm_radialPoint, Complex.norm_eq_sqrt_sq_add_sq, h]

/-! ### The fourteen-point word -/

/-- The unit `v = e^{iπ/3}`. -/
def sixthRoot : E := (1 + radialPoint 3 * imagUnit) / 2

lemma coe_sixthRoot : (sixthRoot : ℂ) = ⟨1 / 2, √3 / 2⟩ := by
  have h₂ : ((2 : E) : ℂ) = 2 := rfl
  apply Complex.ext <;> simp [sixthRoot, radialPoint, h₂]

lemma norm_sub_eq_one {x y : E} (h : ((x : ℂ) - y).re ^ 2 + ((x : ℂ) - y).im ^ 2 = 1) :
    ‖(x : ℂ) - y‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, h, Real.sqrt_one]

lemma sqrt_three_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The column of `ω` at `x`: the labels of `x` and `x + v`. -/
def column (ω : Space) (x : E) : Pattern.Column :=
  if ω.val x = true then 1 else if ω.val (x + sixthRoot) = true then 2 else 0

/-- The fourteen-point word of `ω`, with columns at `0, 1, …, 6`. -/
def wordOf (ω : Space) : Pattern.Word := fun j => column ω ((j : ℕ) : E)

lemma lower_column (ω : Space) (x : E) :
    (Pattern.lower (column ω x) : ℝ) = redAt x ω := by
  unfold column redAt Pattern.lower
  split_ifs <;> simp_all

lemma upper_column (ω : Space) (x : E) :
    (Pattern.upper (column ω x) : ℝ) = redAt (x + sixthRoot) ω := by
  have hn := ω.property.1 x (x + sixthRoot) (norm_sub_eq_one (by
    simp [coe_sixthRoot]
    nlinarith [sqrt_three_sq]))
  unfold column redAt Pattern.upper
  split_ifs <;> simp_all

lemma column_ext {c d : Pattern.Column} (hl : (Pattern.lower c : ℝ) = Pattern.lower d)
    (hu : (Pattern.upper c : ℝ) = Pattern.upper d) : c = d := by
  have key : ∀ c d : Pattern.Column, Pattern.lower c = Pattern.lower d →
      Pattern.upper c = Pattern.upper d → c = d := by decide
  exact key c d (by exact_mod_cast hl) (by exact_mod_cast hu)

lemma continuous_column (x : E) : Continuous fun ω => column ω x := by
  have h : Continuous fun ω : Space => (ω.val x, ω.val (x + sixthRoot)) :=
    ((continuous_apply x).comp continuous_subtype_val).prodMk
      ((continuous_apply _).comp continuous_subtype_val)
  exact (continuous_of_discreteTopology (f := fun p : Bool × Bool =>
    if p.1 = true then (1 : Pattern.Column) else if p.2 = true then 2 else 0)).comp h

lemma continuous_wordOf : Continuous wordOf :=
  continuous_pi fun _ => continuous_column _

lemma integrable_wordOf (f : Pattern.Word → ℝ) {T : Space → Space} (hT : Continuous T) :
    Integrable (fun ω => f (wordOf (T ω))) (measure ω₀) :=
  integrable_of_continuous ω₀
    ((continuous_of_discreteTopology (f := f)).comp (continuous_wordOf.comp hT))

lemma compatible_column (ω : Space) (x : E) :
    Pattern.compatible (column ω x) (column ω (x + 1)) = true := by
  have h₁ := ω.property.1 x (x + 1) (norm_sub_eq_one (by simp))
  have h₂ := ω.property.1 (x + sixthRoot) (x + 1 + sixthRoot) (norm_sub_eq_one (by simp))
  have h₃ := ω.property.1 (x + sixthRoot) (x + 1) (norm_sub_eq_one (by
    simp [coe_sixthRoot]
    nlinarith [sqrt_three_sq]))
  unfold column
  split_ifs <;> simp_all <;> decide

lemma admissible_wordOf (ω : Space) : Pattern.admissible (wordOf ω) = true := by
  obtain ⟨i, hi⟩ := ω.property.2 0 1 (by simp)
  obtain ⟨j, hj⟩ := ω.property.2 sixthRoot 1 (by simp)
  have hc := compatible_column ω
  simp only [Pattern.admissible, Bool.and_eq_true, List.any_eq_true, List.mem_ofFn]
  refine ⟨⟨?_, ⟨_, ⟨i, rfl⟩, ?_⟩⟩, ⟨_, ⟨j, rfl⟩, ?_⟩⟩
  · simp [List.ofFn_succ, Pattern.chain, wordOf]
    exact ⟨by simpa using hc 0, hc _, hc _, hc _, hc _, hc _⟩
  · simp_all [wordOf, column]
  · have hn := ω.property.1 j (j + sixthRoot) (norm_sub_eq_one (by
      simp [coe_sixthRoot]
      nlinarith [sqrt_three_sq]))
    simp_all [wordOf, column, add_comm]

lemma column_trans (a : E) (ω : Space) (x : E) : column (trans a ω) x = column ω (x + a) := by
  simp only [column, trans_apply, add_right_comm]

/-- The last six columns of the word of `ω` are the first six of its translate by `e`. -/
lemma window₁_wordOf (ω : Space) :
    Pattern.window₁ (wordOf ω) = Pattern.window₀ (wordOf (trans 1 ω)) := by
  simp only [Pattern.window₁, Pattern.window₀, wordOf, column_trans]
  congr 1
  funext i
  simp

/-- The half-turn of the word of `ω` is the word of `ω` under the half-turn `x ↦ 6 + v - x`. -/
lemma halfTurnWord_wordOf (ω : Space) :
    Pattern.halfTurnWord (wordOf ω) = wordOf (rotate minusOne (trans (6 + sixthRoot) ω)) := by
  funext j
  have hl : ∀ c, Pattern.lower (Pattern.swapRows c) = Pattern.upper c := by decide
  have hu : ∀ c, Pattern.upper (Pattern.swapRows c) = Pattern.lower c := by decide
  have hj : ((j.rev : ℕ) : E) = 6 - (j : ℕ) := by
    have h : (j.rev : ℕ) + j = 6 := by
      rw [Fin.val_rev]
      omega
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h
  apply column_ext
  · rw [Pattern.halfTurnWord, wordOf, wordOf, hl, upper_column, lower_column]
    simp only [redAt, rotate_apply, trans_apply, kCoeff_minusOne, hj]
    ring_nf
  · rw [Pattern.halfTurnWord, wordOf, wordOf, hu, upper_column, lower_column]
    simp only [redAt, rotate_apply, trans_apply, kCoeff_minusOne, hj]
    ring_nf

/-- The cost of the word of `ω`, in red indicators. -/
lemma cost_wordOf (ω : Space) :
    (Pattern.cost (wordOf ω) : ℝ) =
      -3 * (redAt 0 ω + redAt sixthRoot ω) -
        ∑ j : Fin 6, (((rowTable j).1 : ℝ) *
            (redAt 0 ω * redAt ((j + 1 : ℕ) : E) ω +
              redAt sixthRoot ω * redAt (((j + 1 : ℕ) : E) + sixthRoot) ω) +
          ((rowTable j).2.1 : ℝ) * (redAt 0 ω * redAt (((j + 1 : ℕ) : E) + sixthRoot) ω) +
          ((rowTable j).2.2 : ℝ) * (redAt sixthRoot ω * redAt ((j + 1 : ℕ) : E) ω)) := by
  rw [Pattern.cost, ← Fin.sum_univ_def]
  push_cast
  simp only [wordOf, lower_column, upper_column, Fin.val_zero, Fin.val_succ, Nat.cast_zero,
    zero_add]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by push_cast; ring

/-- The expected cost, with each correlation at its radius:
`|j| = j`, `|j + v| = √(j² + j + 1)`, and `|j - v| = √(j² - j + 1)`. -/
lemma integral_cost :
    ∫ ω, (Pattern.cost (wordOf ω) : ℝ) ∂measure ω₀ =
      -6 * alpha ω₀ -
        ∑ j : Fin 6, (2 * ((rowTable j).1 : ℝ) * corr ω₀ (radialPoint (((j : ℕ) + 1) ^ 2)) +
          ((rowTable j).2.1 : ℝ) *
            corr ω₀ (radialPoint (((j : ℕ) + 1) ^ 2 + ((j : ℕ) + 1) + 1)) +
          ((rowTable j).2.2 : ℝ) * corr ω₀ (radialPoint ((j : ℕ) ^ 2 + (j : ℕ) + 1))) := by
  have hi {g : Space → ℝ} (hg : Continuous g) := integrable_of_continuous ω₀ hg
  simp_rw [cost_wordOf]
  rw [integral_sub (hi (by fun_prop)) (hi (by fun_prop)), integral_const_mul,
    integral_add (hi (by fun_prop)) (hi (by fun_prop)), integral_redAt, integral_redAt,
    integral_finsetSum _ fun _ _ => hi (by fun_prop)]
  congr 1
  · ring
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    integral_add (hi (by fun_prop)) (hi (by fun_prop)), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    integral_redAt_mul, integral_redAt_mul, integral_redAt_mul, integral_redAt_mul,
    sub_zero, sub_zero, add_sub_cancel_right]
  have h₁ : corr ω₀ (((j : ℕ) + 1 : ℕ) : E) = corr ω₀ (radialPoint (((j : ℕ) + 1) ^ 2)) :=
    corr_eq_radialPoint ω₀ (by simp)
  have h₂ : corr ω₀ ((((j : ℕ) + 1 : ℕ) : E) + sixthRoot) =
      corr ω₀ (radialPoint (((j : ℕ) + 1) ^ 2 + ((j : ℕ) + 1) + 1)) :=
    corr_eq_radialPoint ω₀ (by
      simp [coe_sixthRoot]
      nlinarith [sqrt_three_sq])
  have h₃ : corr ω₀ ((((j : ℕ) + 1 : ℕ) : E) - sixthRoot) =
      corr ω₀ (radialPoint ((j : ℕ) ^ 2 + (j : ℕ) + 1)) :=
    corr_eq_radialPoint ω₀ (by
      simp [coe_sixthRoot]
      nlinarith [sqrt_three_sq])
  rw [h₁, h₂, h₃]
  ring

/-- The integrated fourteen-point inequality, in the normalization of the kernel `F`. -/
theorem kernel_correlation_le :
    ∑ i : Fin 11, (kernelCoeff i : ℝ) * corr ω₀ (radialPoint (kernelRadius i)) ≤
      -192 * alpha ω₀ := by
  have hP := integrable_wordOf ω₀ (fun w => (Pattern.potential (Pattern.window₀ w) : ℝ))
    continuous_id'
  have hP' := integrable_wordOf ω₀ (fun w => (Pattern.potential (Pattern.window₀ w) : ℝ))
    (trans_continuous 1)
  have hC := integrable_wordOf ω₀ (fun w => (Pattern.cost w : ℝ)) continuous_id'
  have hC' := integrable_wordOf ω₀ (fun w => (Pattern.cost w : ℝ))
    (T := fun ω => rotate minusOne (trans (6 + sixthRoot) ω))
    ((rotate_continuous _).comp (trans_continuous _))
  -- the pattern inequality for every labeling
  have hw (ω : Space) :
      (Pattern.potential (Pattern.window₀ (wordOf ω)) : ℝ) -
          Pattern.potential (Pattern.window₀ (wordOf (trans 1 ω))) ≤
        Pattern.cost (wordOf ω) +
          Pattern.cost (wordOf (rotate minusOne (trans (6 + sixthRoot) ω))) := by
    have h := Pattern.pattern_inequality (wordOf ω) (admissible_wordOf ω)
    rw [window₁_wordOf, halfTurnWord_wordOf] at h
    exact_mod_cast h
  -- stationarity cancels the potentials, and the half-turn symmetrizes the cost
  have hi : ∫ ω, ((Pattern.potential (Pattern.window₀ (wordOf ω)) : ℝ) -
        Pattern.potential (Pattern.window₀ (wordOf (trans 1 ω)))) ∂measure ω₀ ≤
      ∫ ω, ((Pattern.cost (wordOf ω) : ℝ) +
        Pattern.cost (wordOf (rotate minusOne (trans (6 + sixthRoot) ω)))) ∂measure ω₀ :=
    integral_mono (hP.sub hP') (hC.add hC') hw
  rw [integral_sub hP hP', integral_add hC hC',
    integral_trans ω₀ 1 fun ω => (Pattern.potential (Pattern.window₀ (wordOf ω)) : ℝ),
    integral_trans ω₀ (6 + sixthRoot) fun ω => (Pattern.cost (wordOf (rotate minusOne ω)) : ℝ),
    integral_rotate ω₀ minusOne fun ω => (Pattern.cost (wordOf ω) : ℝ), sub_self,
    integral_cost] at hi
  have h₁ := corr_unit ω₀ (u := radialPoint 1) (by simp [norm_radialPoint])
  simp [Fin.sum_univ_succ, kernelCoeff, kernelRadius, rowTable] at hi ⊢
  linarith

end Erdos188.LowerBound.LabelModel

end
