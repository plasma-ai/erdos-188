module

public import Erdos188.LowerBound.Correlation
public import Erdos188.LowerBound.Kernel
public import Erdos188.LowerBound.Spectral
public import Erdos188.Statement

/-!
# A lower bound of eight for Erdős Problem 188

Every red/blue coloring of the plane with no red unit pair contains seven collinear
blue points with consecutive spacing one. Hence every `k ∈ Erdos188.s` is at least `8`.

The proof combines the integrated fourteen-point inequality
`322 ρ(1) + 32 Q(ρ) ≤ -192 α`, the radial spectral representation
`ρ(z) = ∫ J₀(|z| |ξ|) dν(ξ)` with `ν(ℂ) ≤ α`, and positivity of the kernel `F`:

`0 ≤ ∫ F(|ξ|) dν = 191 ν(ℂ) + 322 ρ(1) + 32 Q(ρ) ≤ 191 α - 192 α < 0`.
-/

@[expose] public section

namespace Erdos188.LowerBound

open MeasureTheory
open OAI.PlaneFiveColor.Spectral

/-- No admissible labeling of the algebraic plane exists. -/
theorem LabelModel.not_space (ω₀ : LabelModel.Space) : False := by
  obtain ⟨ν, hν, hmass, hcorr⟩ := LabelModel.exists_radial_measure ω₀
  -- each radial Bessel profile is bounded and continuous, hence `ν`-integrable
  have hint (r : ℝ) : Integrable (fun ξ : ℂ => besselJ0 (r * ‖ξ‖)) ν :=
    (integrable_const (1 : ℝ)).mono'
      (continuous_besselJ0.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
      (ae_of_all _ fun ξ => abs_besselJ0_le_one _)
  -- the correlations at the (nonzero) radial points
  have hcorr' (i : Fin 11) : LabelModel.corr ω₀ (LabelModel.radialPoint (kernelRadius i)) =
      ∫ ξ, besselJ0 (√(kernelRadius i : ℝ) * ‖ξ‖) ∂ν := by
    have hpos : (0 : ℝ) < kernelRadius i := by fin_cases i <;> norm_num [kernelRadius]
    rw [hcorr, LabelModel.norm_radialPoint]
    intro h
    have := LabelModel.norm_radialPoint (kernelRadius i)
    rw [h, ZeroMemClass.coe_zero, norm_zero] at this
    exact (Real.sqrt_pos.mpr hpos).ne this
  -- integrating `F(|ξ|)` against `ν`
  have hF : ∫ ξ, kernelF ‖ξ‖ ∂ν = 191 * ν.real Set.univ +
      ∑ i : Fin 11, (kernelCoeff i : ℝ) * LabelModel.corr ω₀
        (LabelModel.radialPoint (kernelRadius i)) := by
    unfold kernelF
    rw [integral_add (integrable_const _)
        (integrable_finsetSum _ fun i _ => (hint _).const_mul _),
      integral_const, integral_finsetSum _ fun i _ => (hint _).const_mul _, smul_eq_mul,
      mul_comm]
    simp only [integral_const_mul, hcorr']
  have h0 : 0 ≤ ∫ ξ, kernelF ‖ξ‖ ∂ν := integral_nonneg fun ξ => kernelF_nonneg (norm_nonneg ξ)
  have h1 := LabelModel.kernel_correlation_le ω₀
  have h7 := LabelModel.one_le_seven_mul_alpha ω₀
  linarith

/-- Every coloring of the plane with no red unit pair has a blue seven-term progression
of unit step. -/
theorem seven_term_blue (blue : Set ℂ)
    (hred : (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1)) :
    ∃ z d : ℂ, ‖d‖ = 1 ∧ ∀ n : ℕ, n < 7 → z + n • d ∈ blue := by
  classical
  by_contra h
  push Not at h
  -- the non-blue points of the algebraic plane form an admissible labeling
  refine LabelModel.not_space ⟨fun x => decide ((x : ℂ) ∉ blue), ?_, ?_⟩
  · rintro x y hxy ⟨hx, hy⟩
    have hne : (x : ℂ) ≠ y := by
      intro e
      rw [e, sub_self, norm_zero] at hxy
      exact zero_ne_one hxy
    exact hred ⟨trivial, of_decide_eq_true hx⟩ ⟨trivial, of_decide_eq_true hy⟩ hne
      (by rw [dist_eq_norm, hxy])
  · intro x u hu
    obtain ⟨n, hn, hnb⟩ := h x u hu
    refine ⟨⟨n, hn⟩, decide_eq_true ?_⟩
    simpa [nsmul_eq_mul] using hnb

/-- No `k ≤ 7` lies in `Erdos188.s`: the first `k` terms of the blue seven-term
progression form a blue `k`-term progression. -/
theorem not_mem_s_of_le_seven {k : ℕ} (hk : k ≤ 7) : k ∉ Erdos188.s := by
  rintro ⟨blue, hred, hno⟩
  obtain ⟨z, d, hd, hblue⟩ := seven_term_blue blue hred
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
  -- `n ↦ z + n • d` is injective
  have hinj : Function.Injective fun i : Fin k => z + (i : ℕ) • d := by
    intro i j hij
    simp only [add_right_inj, nsmul_eq_mul] at hij
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hd0 hij)
  have hrange : {z + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} =
      Set.range fun i : Fin k => z + (i : ℕ) • d := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, by exact_mod_cast hn⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by exact_mod_cast i.isLt, rfl⟩
  refine hno ⟨_, ?_, z, d, hd, ?_, rfl⟩
  · rintro x ⟨n, hn, rfl⟩
    exact hblue n (lt_of_lt_of_le (by exact_mod_cast hn) hk)
  · rw [hrange, ENat.card_congr (Equiv.ofInjective _ hinj).symm, ENat.card_eq_coe_fintype_card,
      Fintype.card_fin]

theorem seven_not_mem_s : 7 ∉ Erdos188.s :=
  not_mem_s_of_le_seven le_rfl

/-- Erdős Problem 188: the answer is at least `8`. -/
theorem erdos188_lower_bound : ∀ k ∈ Erdos188.s, 8 ≤ k := by
  intro k hk
  by_contra h
  exact not_mem_s_of_le_seven (by omega) hk

end Erdos188.LowerBound
