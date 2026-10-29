module

public import OAI.Analysis.PlaneSpectrum.Representations

/-!
# The stationary label model

Red/blue labelings of the algebraic plane `E` with no red unit pair and a red point in
every seven-term unit progression form a compact space. Translations by `E` and
rotations by the algebraic unit circle `K` act on it, and OpenAI's stationary mean
gives an invariant probability measure from any one labeling. This mirrors
`OAI.PlaneFiveColor.LabelModel`, with progression hitting in place of properness.

The red indicator at the origin gives the density `α`, the correlations `ρ(z)`, and the
vector of `L²` whose translation coefficients are those correlations.
-/

@[expose] public section

noncomputable section

namespace Erdos188.LowerBound.LabelModel

open MeasureTheory
open OAI OAI.PlaneFiveColor.Spectral OAI.EuclideanFiveColor OAI.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace

/-- A labeling of `E` (`true` is red) with no red unit pair and a red point in every
seven-term progression of unit step. -/
def Admissible (ω : E → Bool) : Prop :=
  (∀ x y : E, ‖(x : ℂ) - (y : ℂ)‖ = 1 → ¬(ω x = true ∧ ω y = true)) ∧
    ∀ x u : E, ‖(u : ℂ)‖ = 1 → ∃ j : Fin 7, ω (x + (j : ℕ) * u) = true

/-- The space of admissible labelings. -/
abbrev Space := {ω : E → Bool // Admissible ω}

theorem isClosed_admissible : IsClosed {ω : E → Bool | Admissible ω} := by
  unfold Admissible
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
    have hc : Continuous (fun ω : E → Bool => (ω x, ω y)) :=
      (continuous_apply x).prodMk (continuous_apply y)
    exact (isClosed_discrete {p : Bool × Bool | ¬(p.1 = true ∧ p.2 = true)}).preimage hc
  · refine isClosed_iInter fun x => isClosed_iInter fun u => isClosed_iInter fun _ => ?_
    simp only [Set.ofPred_exists]
    refine isClosed_iUnion_of_finite fun j => ?_
    have hc : Continuous (fun ω : E → Bool => ω (x + (j : ℕ) * u)) :=
      continuous_apply (x + (j : ℕ) * u)
    exact (isClosed_discrete ({true} : Set Bool)).preimage hc

instance : CompactSpace Space := isCompact_iff_compactSpace.mp isClosed_admissible.isCompact

/-- Translation by `a`. -/
def trans (a : E) (ω : Space) : Space := ⟨fun x => ω.val (x + a), by
  refine ⟨fun x y h => ω.property.1 (x + a) (y + a) ?_, fun x u hu => ?_⟩
  · change ‖(x : ℂ) + (a : ℂ) - ((y : ℂ) + (a : ℂ))‖ = 1
    simpa only [add_sub_add_right_eq_sub] using h
  · obtain ⟨j, hj⟩ := ω.property.2 (x + a) u hu
    exact ⟨j, (congrArg ω.val (add_right_comm _ _ _)).trans hj⟩⟩

/-- Rotation by `b`. -/
def rotate (b : K) (ω : Space) : Space := ⟨fun x => ω.val (kCoeff b * x), by
  refine ⟨fun x y h => ω.property.1 (kCoeff b * x) (kCoeff b * y) ?_, fun x u hu => ?_⟩
  · change ‖(b.val : ℂ) * (x : ℂ) - (b.val : ℂ) * (y : ℂ)‖ = 1
    rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul, h]
  · have hb : ‖((kCoeff b * u : E) : ℂ)‖ = 1 := by
      change ‖(b.val : ℂ) * (u : ℂ)‖ = 1
      rw [norm_mul, Circle.norm_coe, one_mul, hu]
    obtain ⟨j, hj⟩ := ω.property.2 (kCoeff b * x) (kCoeff b * u) hb
    exact ⟨j, (congrArg ω.val (by ring)).trans hj⟩⟩

@[simp] lemma trans_apply (a : E) (ω : Space) (x : E) : (trans a ω).val x = ω.val (x + a) := rfl

@[simp] lemma rotate_apply (b : K) (ω : Space) (x : E) :
    (rotate b ω).val x = ω.val (kCoeff b * x) := rfl

lemma trans_continuous (a : E) : Continuous (trans a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma rotate_continuous (b : K) : Continuous (rotate b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b * x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space) : trans 0 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma trans_add (a b : E) (ω : Space) : trans a (trans b ω) = trans (a + b) ω := by
  apply Subtype.ext
  funext x
  simp [add_assoc]

@[simp] lemma rotate_one (ω : Space) : rotate 1 ω = ω := by
  apply Subtype.ext
  funext x
  have h1 : kCoeff 1 = 1 := rfl
  simp [h1]

lemma rotate_mul (a b : K) (ω : Space) : rotate a (rotate b ω) = rotate (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a * b) * x)
  have he : kCoeff (a * b) = kCoeff a * kCoeff b := by rfl
  rw [he]; ring_nf

lemma covariance (a : E) (b : K) (ω : Space) :
    trans a (rotate b ω) = rotate b (trans (kCoeff b * a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, mul_add]

/-- Translation as a homeomorphism. -/
def transHomeo (a : E) : Space ≃ₜ Space where
  toFun := trans a
  invFun := trans (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := trans_continuous a
  continuous_invFun := trans_continuous (-a)

/-- Rotation as a homeomorphism. -/
def rotateHomeo (b : K) : Space ≃ₜ Space where
  toFun := rotate b
  invFun := rotate b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := rotate_continuous b
  continuous_invFun := rotate_continuous b⁻¹

/-- Translations, indexed by the discrete additive group. -/
abbrev Trans := Additive DiscreteE

/-- The translation action used by the stationary mean. -/
def tr (a : Trans) : Space → Space := trans (Multiplicative.toAdd (Additive.toMul a))

/-- The rotation action used by the stationary mean. -/
def ro (b : Rot) : Space → Space := rotate (rotMul b)

/-- The invariant probability measure generated by the labeling `ω₀`. -/
def measure (ω₀ : Space) : Measure Space := StationaryMean.measure tr ro ω₀

instance (ω₀ : Space) : IsProbabilityMeasure (measure ω₀) :=
  inferInstanceAs (IsProbabilityMeasure (StationaryMean.measure tr ro ω₀))

lemma trans_preserving (ω₀ : Space) (a : E) :
    MeasurePreserving (trans a) (measure ω₀) (measure ω₀) := by
  apply StationaryMean.preserving_of_average tr ro ω₀ (transHomeo a)
  intro f
  apply StationaryMean.average_translation tr ro ω₀
    (fun a b x => trans_add _ _ x)
    (fun b a => Additive.ofMul (Multiplicative.ofAdd
      (kCoeff (rotMul b) * Multiplicative.toAdd (Additive.toMul a))))
    (fun a b x => covariance _ _ x) (Additive.ofMul (Multiplicative.ofAdd a)) f
    (trans_continuous a)

lemma rotate_preserving (ω₀ : Space) (b : K) :
    MeasurePreserving (rotate b) (measure ω₀) (measure ω₀) := by
  apply StationaryMean.preserving_of_average tr ro ω₀ (rotateHomeo b)
  intro f
  exact StationaryMean.average_rotation tr ro ω₀
    (fun a b x => rotate_mul _ _ x) (mulRot b) f (rotate_continuous b)

variable (ω₀ : Space)

/-- The `L²` space of the stationary measure. -/
abbrev Hilbert := Lp ℂ 2 (measure ω₀)

/-- The Koopman operator of a translation. -/
def translation (a : E) : unitary (Hilbert ω₀ →L[ℂ] Hilbert ω₀) :=
  Koopman.unitary (measure ω₀) (transHomeo a).toMeasurableEquiv (trans_preserving ω₀ a)

/-- The Koopman operator of a rotation. -/
def rotation (b : K) : unitary (Hilbert ω₀ →L[ℂ] Hilbert ω₀) :=
  Koopman.unitary (measure ω₀) (rotateHomeo b).toMeasurableEquiv (rotate_preserving ω₀ b)

/-- The translation representation of the discrete algebraic plane. -/
def representation : DiscreteE →* unitary (Hilbert ω₀ →L[ℂ] Hilbert ω₀) where
  toFun a := translation ω₀ (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans 0) (trans_preserving ω₀ 0) v = v
    have he : trans 0 = id := funext trans_zero
    simp only [he, Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans (Multiplicative.toAdd a + Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans (Multiplicative.toAdd a)) _
        (Lp.compMeasurePreserving (trans (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans c x) (add_comm _ _)).trans (trans_add _ _ x).symm

lemma op_apply (a : E) (v : Hilbert ω₀) : op (representation ω₀) a v =
    Lp.compMeasurePreserving (trans a) (trans_preserving ω₀ a) v := rfl

lemma rotation_covariance (b : K) (a : E) (v : Hilbert ω₀) :
    (rotation ω₀ b : Hilbert ω₀ →L[ℂ] Hilbert ω₀) (op (representation ω₀) a v) =
      op (representation ω₀) (kCoeff b * a)
        ((rotation ω₀ b : Hilbert ω₀ →L[ℂ] Hilbert ω₀) v) := by
  change Lp.compMeasurePreserving (rotate b) (rotate_preserving ω₀ b)
      (Lp.compMeasurePreserving (trans a) (trans_preserving ω₀ a) v) =
    Lp.compMeasurePreserving (trans (kCoeff b * a)) (trans_preserving ω₀ (kCoeff b * a))
      (Lp.compMeasurePreserving (rotate b) (rotate_preserving ω₀ b) v)
  simp only [← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance a b x

/-- The red indicator at `x`. -/
def redAt (x : E) (ω : Space) : ℝ := if ω.val x = true then 1 else 0

lemma continuous_redAt (x : E) : Continuous (redAt x) :=
  (continuous_of_discreteTopology (f := fun c : Bool => if c = true then (1 : ℝ) else 0)).comp
    ((continuous_apply x).comp continuous_subtype_val)

/-- The density of red points. -/
def alpha : ℝ := ∫ ω, redAt 0 ω ∂measure ω₀

/-- The red–red correlation at displacement `z`. -/
def corr (z : E) : ℝ := ∫ ω, redAt 0 ω * redAt z ω ∂measure ω₀

lemma red_memLp : MemLp (fun ω => (redAt 0 ω : ℂ)) 2 (measure ω₀) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (Complex.continuous_ofReal.comp (continuous_redAt 0)).aestronglyMeasurable
  · exact .of_forall fun ω => by dsimp [redAt]; split_ifs <;> simp

/-- The red indicator at the origin, as a vector of `L²`. -/
def redVector : Hilbert ω₀ := (red_memLp ω₀).toLp fun ω => (redAt 0 ω : ℂ)

lemma red_ae : redVector ω₀ =ᵐ[measure ω₀] fun ω => (redAt 0 ω : ℂ) :=
  (red_memLp ω₀).coeFn_toLp

/-- Translation coefficients of the red vector are the correlations. -/
lemma inner_redVector (z : E) :
    ⟪redVector ω₀, op (representation ω₀) z (redVector ω₀)⟫_ℂ = (corr ω₀ z : ℂ) := by
  rw [op_apply, L2.inner_def, corr, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [red_ae ω₀, Lp.coeFn_compMeasurePreserving (redVector ω₀) (trans_preserving ω₀ z),
    (trans_preserving ω₀ z).quasiMeasurePreserving.ae (red_ae ω₀)] with ω h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, redAt, trans_apply, zero_add]
  split_ifs <;> simp

lemma norm_redVector_sq : ‖redVector ω₀‖ ^ 2 = alpha ω₀ := by
  have h : ⟪redVector ω₀, redVector ω₀⟫_ℂ = (alpha ω₀ : ℂ) := by
    rw [L2.inner_def, alpha, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [red_ae ω₀] with ω h1
    simp only [h1, redAt]
    split_ifs <;> simp
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖redVector ω₀‖ ^ 2 : ℝ) : ℂ) = (alpha ω₀ : ℂ) := by push_cast; exact h
  exact Complex.ofReal_injective h'

lemma rotation_redVector (b : K) :
    (rotation ω₀ b : Hilbert ω₀ →L[ℂ] Hilbert ω₀) (redVector ω₀) = redVector ω₀ := by
  change Lp.compMeasurePreserving (rotate b) (rotate_preserving ω₀ b) (redVector ω₀) = redVector ω₀
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (redVector ω₀) (rotate_preserving ω₀ b),
    (rotate_preserving ω₀ b).quasiMeasurePreserving.ae (red_ae ω₀), red_ae ω₀] with ω h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, redAt, rotate_apply, mul_zero]

end Erdos188.LowerBound.LabelModel

end
