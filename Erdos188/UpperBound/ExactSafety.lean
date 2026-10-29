module

public import Erdos188.UpperBound.Safety
public import Erdos188.UpperBound.Wire
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Integer checkers for exact and block-pruned safety

Computable Boolean checkers over integer wire data, each proved sound against
the semantic safety layer of `Safety`: the strict annulus test for one site
pair at one lift, the block test on dyadic integer enclosures of two node
boxes, containment routes, and exact rotation routes. Every checker uses
cleared-denominator integer arithmetic so that `decide` can evaluate it in the
kernel; the real-valued notions stay in the imported modules, and this file
deliberately opens no `noncomputable section`. No finite family, tree, or
certificate appears here.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-! ## Wire sites -/

/-- Positive denominators, `0 ≤ s < 59`, `0 ≤ t < 59`, and `0 < r < 1 / 2`, cross-multiplied. -/
def SiteWire.valid (w : SiteWire) : Bool :=
  decide (0 < w.sDen) && (decide (0 < w.tDen) && (decide (0 < w.rDen) &&
    (decide (0 ≤ w.sNum) && (decide (w.sNum < 59 * w.sDen) &&
      (decide (0 ≤ w.tNum) && (decide (w.tNum < 59 * w.tDen) &&
        (decide (0 < w.rNum) && decide (2 * w.rNum < w.rDen))))))))

/-- The Boolean validity test unpacked into its nine integer inequalities. -/
theorem SiteWire.valid_iff (w : SiteWire) :
    w.valid = true ↔ 0 < w.sDen ∧ 0 < w.tDen ∧ 0 < w.rDen ∧
      0 ≤ w.sNum ∧ w.sNum < 59 * w.sDen ∧ 0 ≤ w.tNum ∧ w.tNum < 59 * w.tDen ∧
        0 < w.rNum ∧ 2 * w.rNum < w.rDen := by
  simp only [SiteWire.valid, Bool.and_eq_true, decide_eq_true_eq]

/-- A valid wire names a valid site. -/
theorem SiteWire.valid_toSite (w : SiteWire) (valid : w.valid = true) : SiteValid w.toSite := by
  obtain ⟨sDenPos, tDenPos, rDenPos, sNonneg, sLt, tNonneg, tLt, rPos, rLt⟩ :=
    w.valid_iff.1 valid
  have sDenPosQ : (0 : ℚ) < w.sDen := by exact_mod_cast sDenPos
  have tDenPosQ : (0 : ℚ) < w.tDen := by exact_mod_cast tDenPos
  have rDenPosQ : (0 : ℚ) < w.rDen := by exact_mod_cast rDenPos
  refine ⟨div_nonneg (by exact_mod_cast sNonneg) sDenPosQ.le, ?_,
    div_nonneg (by exact_mod_cast tNonneg) tDenPosQ.le, ?_,
    div_pos (by exact_mod_cast rPos) rDenPosQ, ?_⟩
  · show (w.sNum : ℚ) / w.sDen < 59
    rw [div_lt_iff₀ sDenPosQ]
    exact_mod_cast sLt
  · show (w.tNum : ℚ) / w.tDen < 59
    rw [div_lt_iff₀ tDenPosQ]
    exact_mod_cast tLt
  · show (w.rNum : ℚ) / w.rDen < 1 / 2
    rw [div_lt_iff₀ rDenPosQ]
    have cast : (2 * w.rNum : ℚ) < w.rDen := by exact_mod_cast rLt
    linarith

/-! ## Cleared gap and radius fractions -/

/-- Numerator of the first axial gap coordinate over the denominator `q.sDen * q'.sDen`. -/
def gapSNum (q q' : SiteWire) (nS : ℤ) : ℤ :=
  q.sNum * q'.sDen - q'.sNum * q.sDen + 59 * nS * (q.sDen * q'.sDen)

/-- Numerator of the second axial gap coordinate over the denominator `q.tDen * q'.tDen`. -/
def gapTNum (q q' : SiteWire) (nT : ℤ) : ℤ :=
  q.tNum * q'.tDen - q'.tNum * q.tDen + 59 * nT * (q.tDen * q'.tDen)

/-- Numerator of the axial form of the gap over `gapQDen`. -/
def gapQNum (q q' : SiteWire) (nS nT : ℤ) : ℤ :=
  gapSNum q q' nS ^ 2 * (q.tDen * q'.tDen) ^ 2 +
    gapSNum q q' nS * gapTNum q q' nT * (q.sDen * q'.sDen) * (q.tDen * q'.tDen) +
      gapTNum q q' nT ^ 2 * (q.sDen * q'.sDen) ^ 2

/-- Denominator of the axial form of the gap: the squared product of the center denominators. -/
def gapQDen (q q' : SiteWire) : ℤ := (q.sDen * q'.sDen * (q.tDen * q'.tDen)) ^ 2

/-- Numerator of the radius sum `r + r'` over `radiusSumDen`. -/
def radiusSumNum (q q' : SiteWire) : ℤ := q.rNum * q'.rDen + q'.rNum * q.rDen

/-- Common denominator `rDen * rDen'` of the radius sum and the radius difference. -/
def radiusSumDen (q q' : SiteWire) : ℤ := q.rDen * q'.rDen

/-- Numerator of the radius difference `r' - r` over `radiusSumDen`. -/
def radiusDiffNum (q q' : SiteWire) : ℤ := q'.rNum * q.rDen - q.rNum * q'.rDen

/-- The gap denominator of two valid wires is positive. -/
theorem gapQDen_pos (q q' : SiteWire) (qValid : q.valid = true) (q'Valid : q'.valid = true) :
    (0 : ℝ) < gapQDen q q' := by
  obtain ⟨sDenPos, tDenPos, -, -⟩ := q.valid_iff.1 qValid
  obtain ⟨sDenPos', tDenPos', -, -⟩ := q'.valid_iff.1 q'Valid
  have sDenPosR : (0 : ℝ) < q.sDen := by exact_mod_cast sDenPos
  have tDenPosR : (0 : ℝ) < q.tDen := by exact_mod_cast tDenPos
  have sDenPosR' : (0 : ℝ) < q'.sDen := by exact_mod_cast sDenPos'
  have tDenPosR' : (0 : ℝ) < q'.tDen := by exact_mod_cast tDenPos'
  simp only [gapQDen]
  push_cast
  positivity

/-- The radius denominator of two valid wires is positive. -/
theorem radiusSumDen_pos (q q' : SiteWire) (qValid : q.valid = true) (q'Valid : q'.valid = true) :
    (0 : ℝ) < radiusSumDen q q' := by
  obtain ⟨-, -, rDenPos, -⟩ := q.valid_iff.1 qValid
  obtain ⟨-, -, rDenPos', -⟩ := q'.valid_iff.1 q'Valid
  have rDenPosR : (0 : ℝ) < q.rDen := by exact_mod_cast rDenPos
  have rDenPosR' : (0 : ℝ) < q'.rDen := by exact_mod_cast rDenPos'
  simp only [radiusSumDen]
  push_cast
  positivity

/-- The real axial form of the wire gap is the cleared integer fraction. -/
theorem axialQ_axialGap_toSite (q q' : SiteWire) (lift : ℤ × ℤ)
    (qValid : q.valid = true) (q'Valid : q'.valid = true) :
    axialQ (axialGap q.toSite q'.toSite lift) =
      (gapQNum q q' lift.1 lift.2 : ℝ) / (gapQDen q q' : ℝ) := by
  obtain ⟨sDenPos, tDenPos, -, -⟩ := q.valid_iff.1 qValid
  obtain ⟨sDenPos', tDenPos', -, -⟩ := q'.valid_iff.1 q'Valid
  have sDenNe : (q.sDen : ℝ) ≠ 0 := by exact_mod_cast sDenPos.ne'
  have tDenNe : (q.tDen : ℝ) ≠ 0 := by exact_mod_cast tDenPos.ne'
  have sDenNe' : (q'.sDen : ℝ) ≠ 0 := by exact_mod_cast sDenPos'.ne'
  have tDenNe' : (q'.tDen : ℝ) ≠ 0 := by exact_mod_cast tDenPos'.ne'
  rw [axialQ, axialGap_fst, axialGap_snd]
  simp only [SiteWire.toSite, gapQNum, gapQDen, gapSNum, gapTNum]
  push_cast
  field_simp

/-- The real radius sum of two wire sites is the cleared integer fraction. -/
theorem radiusSum_toSite (q q' : SiteWire) (qValid : q.valid = true) (q'Valid : q'.valid = true) :
    ((q.toSite.radius : ℚ) : ℝ) + ((q'.toSite.radius : ℚ) : ℝ) =
      (radiusSumNum q q' : ℝ) / (radiusSumDen q q' : ℝ) := by
  obtain ⟨-, -, rDenPos, -⟩ := q.valid_iff.1 qValid
  obtain ⟨-, -, rDenPos', -⟩ := q'.valid_iff.1 q'Valid
  have rDenNe : (q.rDen : ℝ) ≠ 0 := by exact_mod_cast rDenPos.ne'
  have rDenNe' : (q'.rDen : ℝ) ≠ 0 := by exact_mod_cast rDenPos'.ne'
  simp only [SiteWire.toSite, radiusSumNum, radiusSumDen]
  push_cast
  field_simp

/-- The real radius difference of two wire sites is the cleared integer fraction. -/
theorem radiusDiff_toSite (q q' : SiteWire) (qValid : q.valid = true) (q'Valid : q'.valid = true) :
    ((q'.toSite.radius : ℚ) : ℝ) - ((q.toSite.radius : ℚ) : ℝ) =
      (radiusDiffNum q q' : ℝ) / (radiusSumDen q q' : ℝ) := by
  obtain ⟨-, -, rDenPos, -⟩ := q.valid_iff.1 qValid
  obtain ⟨-, -, rDenPos', -⟩ := q'.valid_iff.1 q'Valid
  have rDenNe : (q.rDen : ℝ) ≠ 0 := by exact_mod_cast rDenPos.ne'
  have rDenNe' : (q'.rDen : ℝ) ≠ 0 := by exact_mod_cast rDenPos'.ne'
  simp only [SiteWire.toSite, radiusDiffNum, radiusSumDen]
  push_cast
  field_simp

/-! ## Clearing denominators in the annulus and route tests -/

/-- Near branch: the cleared strict inequality gives the squared annulus bound. -/
theorem near_of_cleared (QN QD SN SD : ℝ) (denPos : 0 < QD) (sumDenPos : 0 < SD)
    (cleared : 441 * QN * SD ^ 2 < 10000 * (SD - SN) ^ 2 * QD) :
    (441 / 10000 : ℝ) * (QN / QD) < (1 - SN / SD) ^ 2 := by
  have lhs : (441 / 10000 : ℝ) * (QN / QD) = (441 * QN) / (10000 * QD) := by
    field_simp
  have rhs : (1 - SN / SD) ^ 2 = (SD - SN) ^ 2 / SD ^ 2 := by
    field_simp
  rw [lhs, rhs, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Far branch: the cleared strict inequality gives the squared annulus bound. -/
theorem far_of_cleared (QN QD SN SD : ℝ) (denPos : 0 < QD) (sumDenPos : 0 < SD)
    (cleared : 10000 * (SD + SN) ^ 2 * QD < 441 * QN * SD ^ 2) :
    (1 + SN / SD) ^ 2 < (441 / 10000 : ℝ) * (QN / QD) := by
  have lhs : (441 / 10000 : ℝ) * (QN / QD) = (441 * QN) / (10000 * QD) := by
    field_simp
  have rhs : (1 + SN / SD) ^ 2 = (SD + SN) ^ 2 / SD ^ 2 := by
    field_simp
  rw [lhs, rhs, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Containment: the cleared inequality gives the squared route bound. -/
theorem contain_of_cleared (QN QD DN SD : ℝ) (denPos : 0 < QD) (sumDenPos : 0 < SD)
    (cleared : 441 * QN * SD ^ 2 ≤ 10000 * DN ^ 2 * QD) :
    (441 / 10000 : ℝ) * (QN / QD) ≤ (DN / SD) ^ 2 := by
  have lhs : (441 / 10000 : ℝ) * (QN / QD) = (441 * QN) / (10000 * QD) := by
    field_simp
  rw [lhs, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-! ## Exact pair check -/

/-- The strict annulus test `441 Q(gap) < 10000 (1 - σ)² ∨ 10000 (1 + σ)² < 441 Q(gap)`, with
`σ = r + r'`, in cleared integer arithmetic. -/
def pairCheck (q q' : SiteWire) (nS nT : ℤ) : Bool :=
  decide (441 * gapQNum q q' nS nT * radiusSumDen q q' ^ 2 <
      10000 * (radiusSumDen q q' - radiusSumNum q q') ^ 2 * gapQDen q q') ||
    decide (10000 * (radiusSumDen q q' + radiusSumNum q q') ^ 2 * gapQDen q q' <
      441 * gapQNum q q' nS nT * radiusSumDen q q' ^ 2)

/-- A passing exact pair check makes the two disks cross-safe at that lift. -/
theorem pairCheck_sound (q q' : SiteWire) (lift : ℤ × ℤ)
    (qValid : q.valid = true) (q'Valid : q'.valid = true)
    (pass : pairCheck q q' lift.1 lift.2 = true) :
    CrossSafe (closedDisk q.toSite) (closedDisk (shiftSite q'.toSite lift)) := by
  have qSite := q.valid_toSite qValid
  have q'Site := q'.valid_toSite q'Valid
  have denPos := gapQDen_pos q q' qValid q'Valid
  have sumDenPos := radiusSumDen_pos q q' qValid q'Valid
  apply crossSafe_closedDisk_shiftSite_of_annulus q.toSite q'.toSite lift
    qSite.2.2.2.2.1.le q'Site.2.2.2.2.1.le
  · have qLt := qSite.2.2.2.2.2
    have q'Lt := q'Site.2.2.2.2.2
    linarith
  · rw [axialQ_axialGap_toSite q q' lift qValid q'Valid, radiusSum_toSite q q' qValid q'Valid]
    simp only [pairCheck, Bool.or_eq_true, decide_eq_true_eq] at pass
    rcases pass with near | far
    · exact Or.inl (near_of_cleared _ _ _ _ denPos sumDenPos (by exact_mod_cast near))
    · exact Or.inr (far_of_cleared _ _ _ _ denPos sumDenPos (by exact_mod_cast far))

/-! ## Extrema of the quadratic form on an integer rectangle -/

/-- Four times the axial form on integer coordinates. -/
def fourQ (x y : ℤ) : ℤ := 4 * (x ^ 2 + x * y + y ^ 2)

/-- The smallest corner value of `4 Q` on the rectangle `[a, b] × [c, d]`. -/
def cornerMin (a b c d : ℤ) : ℤ :=
  min (min (fourQ a c) (fourQ a d)) (min (fourQ b c) (fourQ b d))

/-- The stationary value `3 e²` of `4 Q` on the edge at coordinate `e` when the stationary point
`-e / 2` lies in the opposite range `[lo, hi]`; otherwise the fallback. -/
def edgeCandidate (e lo hi fallback : ℤ) : ℤ :=
  if 2 * lo ≤ -e ∧ -e ≤ 2 * hi then 3 * e ^ 2 else fallback

/-- Zero when the rectangle `[a, b] × [c, d]` contains the origin; otherwise the fallback. -/
def originCandidate (a b c d fallback : ℤ) : ℤ :=
  if a ≤ 0 ∧ 0 ≤ b ∧ c ≤ 0 ∧ 0 ≤ d then 0 else fallback

/-- The minimum of `4 Q` on `[a, b] × [c, d]`: corners, admissible edge stationary values, and the
origin when it lies inside. -/
def boxMin (a b c d : ℤ) : ℤ :=
  min (cornerMin a b c d)
    (min (min (edgeCandidate a c d (cornerMin a b c d)) (edgeCandidate b c d (cornerMin a b c d)))
      (min (min (edgeCandidate c a b (cornerMin a b c d)) (edgeCandidate d a b (cornerMin a b c d)))
        (originCandidate a b c d (cornerMin a b c d))))

/-- The maximum of `4 Q` on `[a, b] × [c, d]`: the largest corner value. -/
def boxMax (a b c d : ℤ) : ℤ :=
  max (max (fourQ a c) (fourQ a d)) (max (fourQ b c) (fourQ b d))

/-- The real cast of `fourQ`. -/
theorem fourQ_cast (x y : ℤ) : (fourQ x y : ℝ) = 4 * ((x : ℝ) ^ 2 + x * y + y ^ 2) := by
  simp only [fourQ]
  push_cast
  ring

/-- The box minimum is at most the corner `(a, c)`. -/
theorem boxMin_le_ac (a b c d : ℤ) : boxMin a b c d ≤ fourQ a c :=
  le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))

/-- The box minimum is at most the corner `(a, d)`. -/
theorem boxMin_le_ad (a b c d : ℤ) : boxMin a b c d ≤ fourQ a d :=
  le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))

/-- The box minimum is at most the corner `(b, c)`. -/
theorem boxMin_le_bc (a b c d : ℤ) : boxMin a b c d ≤ fourQ b c :=
  le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))

/-- The box minimum is at most the corner `(b, d)`. -/
theorem boxMin_le_bd (a b c d : ℤ) : boxMin a b c d ≤ fourQ b d :=
  le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

/-- An admissible edge candidate is the stationary value. -/
theorem edgeCandidate_le (e lo hi fallback : ℤ) (admissible : 2 * lo ≤ -e ∧ -e ≤ 2 * hi) :
    edgeCandidate e lo hi fallback ≤ 3 * e ^ 2 := by
  rw [edgeCandidate, ite_eq_left admissible]

/-- The box minimum is at most the admissible stationary value on the edge `x = a`. -/
theorem boxMin_le_edge_a (a b c d : ℤ) (admissible : 2 * c ≤ -a ∧ -a ≤ 2 * d) :
    boxMin a b c d ≤ 3 * a ^ 2 :=
  le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (edgeCandidate_le _ _ _ _ admissible)))

/-- The box minimum is at most the admissible stationary value on the edge `x = b`. -/
theorem boxMin_le_edge_b (a b c d : ℤ) (admissible : 2 * c ≤ -b ∧ -b ≤ 2 * d) :
    boxMin a b c d ≤ 3 * b ^ 2 :=
  le_trans (min_le_right _ _) (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (edgeCandidate_le _ _ _ _ admissible)))

/-- The box minimum is at most the admissible stationary value on the edge `y = c`. -/
theorem boxMin_le_edge_c (a b c d : ℤ) (admissible : 2 * a ≤ -c ∧ -c ≤ 2 * b) :
    boxMin a b c d ≤ 3 * c ^ 2 :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (edgeCandidate_le _ _ _ _ admissible))))

/-- The box minimum is at most the admissible stationary value on the edge `y = d`. -/
theorem boxMin_le_edge_d (a b c d : ℤ) (admissible : 2 * a ≤ -d ∧ -d ≤ 2 * b) :
    boxMin a b c d ≤ 3 * d ^ 2 :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (edgeCandidate_le _ _ _ _ admissible))))

/-- The box minimum is at most zero when the rectangle contains the origin. -/
theorem boxMin_le_zero (a b c d : ℤ) (inside : a ≤ 0 ∧ 0 ≤ b ∧ c ≤ 0 ∧ 0 ≤ d) :
    boxMin a b c d ≤ 0 := by
  refine le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) ?_))
  rw [originCandidate, ite_eq_left inside]

/-- The corner `(a, c)` is at most the box maximum. -/
theorem ac_le_boxMax (a b c d : ℤ) : fourQ a c ≤ boxMax a b c d :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- The corner `(a, d)` is at most the box maximum. -/
theorem ad_le_boxMax (a b c d : ℤ) : fourQ a d ≤ boxMax a b c d :=
  le_trans (le_max_right _ _) (le_max_left _ _)

/-- The corner `(b, c)` is at most the box maximum. -/
theorem bc_le_boxMax (a b c d : ℤ) : fourQ b c ≤ boxMax a b c d :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- The corner `(b, d)` is at most the box maximum. -/
theorem bd_le_boxMax (a b c d : ℤ) : fourQ b d ≤ boxMax a b c d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- Convexity in each coordinate: on the rectangle the form is at most a corner value. -/
theorem fourQ_le_boxMax (a b c d : ℤ) (x y : ℝ)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) (hcy : (c : ℝ) ≤ y) (hyd : y ≤ d) :
    4 * (x ^ 2 + x * y + y ^ 2) ≤ (boxMax a b c d : ℝ) := by
  have ac : 4 * ((a : ℝ) ^ 2 + a * c + c ^ 2) ≤ boxMax a b c d := by
    rw [← fourQ_cast]
    exact_mod_cast ac_le_boxMax a b c d
  have ad : 4 * ((a : ℝ) ^ 2 + a * d + d ^ 2) ≤ boxMax a b c d := by
    rw [← fourQ_cast]
    exact_mod_cast ad_le_boxMax a b c d
  have bc : 4 * ((b : ℝ) ^ 2 + b * c + c ^ 2) ≤ boxMax a b c d := by
    rw [← fourQ_cast]
    exact_mod_cast bc_le_boxMax a b c d
  have bd : 4 * ((b : ℝ) ^ 2 + b * d + d ^ 2) ≤ boxMax a b c d := by
    rw [← fourQ_cast]
    exact_mod_cast bd_le_boxMax a b c d
  rcases le_or_gt 0 ((a : ℝ) + b + y) with signX | signX
  · have stepX : x ^ 2 + x * y + y ^ 2 ≤ (b : ℝ) ^ 2 + b * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hxb) (show (0 : ℝ) ≤ b + x + y by linarith)]
    rcases le_or_gt 0 ((c : ℝ) + d + b) with signY | signY
    · have stepY : (b : ℝ) ^ 2 + b * y + y ^ 2 ≤ (b : ℝ) ^ 2 + b * d + d ^ 2 := by
        linarith [mul_nonneg (sub_nonneg.2 hyd) (show (0 : ℝ) ≤ d + y + b by linarith)]
      linarith
    · have stepY : (b : ℝ) ^ 2 + b * y + y ^ 2 ≤ (b : ℝ) ^ 2 + b * c + c ^ 2 := by
        linarith [mul_nonneg (sub_nonneg.2 hcy) (show (0 : ℝ) ≤ -(c + y + b) by linarith)]
      linarith
  · have stepX : x ^ 2 + x * y + y ^ 2 ≤ (a : ℝ) ^ 2 + a * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hax) (show (0 : ℝ) ≤ -(a + x + y) by linarith)]
    rcases le_or_gt 0 ((c : ℝ) + d + a) with signY | signY
    · have stepY : (a : ℝ) ^ 2 + a * y + y ^ 2 ≤ (a : ℝ) ^ 2 + a * d + d ^ 2 := by
        linarith [mul_nonneg (sub_nonneg.2 hyd) (show (0 : ℝ) ≤ d + y + a by linarith)]
      linarith
    · have stepY : (a : ℝ) ^ 2 + a * y + y ^ 2 ≤ (a : ℝ) ^ 2 + a * c + c ^ 2 := by
        linarith [mul_nonneg (sub_nonneg.2 hcy) (show (0 : ℝ) ≤ -(c + y + a) by linarith)]
      linarith

/-- On the edge at fixed coordinate `e`, a bound below both endpoint values and below the
stationary value `3 e²` whenever `-e / 2` lies in `[lo, hi]` bounds the form on the whole edge. -/
theorem edge_lower_bound (e lo hi : ℤ) (y M : ℝ) (hlo : (lo : ℝ) ≤ y) (hhi : y ≤ hi)
    (atLo : M ≤ 4 * ((e : ℝ) ^ 2 + e * lo + lo ^ 2))
    (atHi : M ≤ 4 * ((e : ℝ) ^ 2 + e * hi + hi ^ 2))
    (stationary : 2 * lo ≤ -e ∧ -e ≤ 2 * hi → M ≤ 3 * (e : ℝ) ^ 2) :
    M ≤ 4 * ((e : ℝ) ^ 2 + e * y + y ^ 2) := by
  rcases le_or_gt 0 (2 * (lo : ℝ) + e) with low | low
  · have step : (e : ℝ) ^ 2 + e * lo + lo ^ 2 ≤ (e : ℝ) ^ 2 + e * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hlo) (show (0 : ℝ) ≤ y + lo + e by linarith)]
    linarith
  rcases le_or_gt (2 * (hi : ℝ) + e) 0 with high | high
  · have step : (e : ℝ) ^ 2 + e * hi + hi ^ 2 ≤ (e : ℝ) ^ 2 + e * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hhi) (show (0 : ℝ) ≤ -(y + hi + e) by linarith)]
    linarith
  · have admissible : 2 * lo ≤ -e ∧ -e ≤ 2 * hi :=
      ⟨le_of_lt (by exact_mod_cast (show 2 * (lo : ℝ) < -e by linarith)),
        le_of_lt (by exact_mod_cast (show -(e : ℝ) < 2 * hi by linarith))⟩
    have edge := stationary admissible
    linarith [sq_nonneg (2 * y + (e : ℝ))]

/-- The interior case with `y < 0`: the `x`-stationary line crosses the rectangle strictly and
the `y`-stationary line crosses its upper edge, so the minimum is the origin, the corner `(a, d)`,
or a stationary value on the edge `x = a` or `y = d`. The mirrored case with `x < 0` follows by
swapping the coordinates. -/
theorem lower_bound_of_signs (a b c d : ℤ) (x y M : ℝ)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) (hcy : (c : ℝ) ≤ y) (hyd : y ≤ d)
    (leftA : 2 * (a : ℝ) + y < 0) (rightB : 0 < 2 * (b : ℝ) + y) (highD : 0 < 2 * (d : ℝ) + x)
    (yNeg : y < 0) (ad : M ≤ 4 * ((a : ℝ) ^ 2 + a * d + d ^ 2))
    (edgeA : 2 * c ≤ -a ∧ -a ≤ 2 * d → M ≤ 3 * (a : ℝ) ^ 2)
    (edgeD : 2 * a ≤ -d ∧ -d ≤ 2 * b → M ≤ 3 * (d : ℝ) ^ 2)
    (origin : a ≤ 0 ∧ 0 ≤ b ∧ c ≤ 0 ∧ 0 ≤ d → M ≤ 0) :
    M ≤ 4 * (x ^ 2 + x * y + y ^ 2) := by
  have bPos : (0 : ℝ) < b := by linarith
  have cNeg : (c : ℝ) < 0 := by linarith
  rcases le_or_gt (a : ℝ) 0 with aNonpos | aPos <;>
    rcases le_or_gt 0 (d : ℝ) with dNonneg | dNeg
  · have inside := origin ⟨by exact_mod_cast aNonpos, le_of_lt (by exact_mod_cast bPos),
      le_of_lt (by exact_mod_cast cNeg), by exact_mod_cast dNonneg⟩
    linarith [sq_nonneg (2 * x + y), sq_nonneg y]
  · have edge := edgeD ⟨by exact_mod_cast (show 2 * (a : ℝ) ≤ -d by linarith),
      le_of_lt (by exact_mod_cast (show -(d : ℝ) < 2 * b by linarith))⟩
    linarith [sq_nonneg (2 * x + y),
      mul_nonneg (sub_nonneg.2 hyd) (show (0 : ℝ) ≤ -(y + d) by linarith)]
  · have edge := edgeA ⟨le_of_lt (by exact_mod_cast (show 2 * (c : ℝ) < -a by linarith)),
      le_of_lt (by exact_mod_cast (show -(a : ℝ) < 2 * d by linarith))⟩
    linarith [sq_nonneg (2 * x + y), sq_nonneg (a : ℝ),
      mul_pos (show (0 : ℝ) < -y - 2 * a by linarith) (show (0 : ℝ) < -y + 2 * a by linarith)]
  · -- The rectangle lies in the open fourth quadrant.
    rcases le_or_gt 0 (2 * (a : ℝ) + d) with nearTop | nearTop
    · rcases le_or_gt ((a : ℝ) + 2 * d) 0 with nearLeft | nearLeft
      · linarith [mul_nonneg (sub_nonneg.2 hax) nearTop,
          mul_nonneg (sub_nonneg.2 hyd) (neg_nonneg.2 nearLeft),
          sq_nonneg (x - a - (d - y)), sq_nonneg (x - (a : ℝ)), sq_nonneg ((d : ℝ) - y)]
      · have edge := edgeA ⟨le_of_lt (by exact_mod_cast (show 2 * (c : ℝ) < -a by linarith)),
          le_of_lt (by exact_mod_cast (show -(a : ℝ) < 2 * d by linarith))⟩
        linarith [sq_nonneg (2 * y + x),
          mul_nonneg (sub_nonneg.2 hax) (show (0 : ℝ) ≤ x + a by linarith)]
    · have edge := edgeD ⟨le_of_lt (by exact_mod_cast (show 2 * (a : ℝ) < -d by linarith)),
        le_of_lt (by exact_mod_cast (show -(d : ℝ) < 2 * b by linarith))⟩
      linarith [sq_nonneg (2 * x + y),
        mul_nonneg (sub_nonneg.2 hyd) (show (0 : ℝ) ≤ -(y + d) by linarith)]

/-- The box minimum bounds the form below on the whole real rectangle: the minimum is reached at
a corner, at an admissible edge stationary point, or at the origin. -/
theorem boxMin_le_fourQ (a b c d : ℤ) (x y : ℝ)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) (hcy : (c : ℝ) ≤ y) (hyd : y ≤ d) :
    (boxMin a b c d : ℝ) ≤ 4 * (x ^ 2 + x * y + y ^ 2) := by
  have ac : (boxMin a b c d : ℝ) ≤ 4 * ((a : ℝ) ^ 2 + a * c + c ^ 2) := by
    rw [← fourQ_cast]
    exact_mod_cast boxMin_le_ac a b c d
  have ad : (boxMin a b c d : ℝ) ≤ 4 * ((a : ℝ) ^ 2 + a * d + d ^ 2) := by
    rw [← fourQ_cast]
    exact_mod_cast boxMin_le_ad a b c d
  have bc : (boxMin a b c d : ℝ) ≤ 4 * ((b : ℝ) ^ 2 + b * c + c ^ 2) := by
    rw [← fourQ_cast]
    exact_mod_cast boxMin_le_bc a b c d
  have bd : (boxMin a b c d : ℝ) ≤ 4 * ((b : ℝ) ^ 2 + b * d + d ^ 2) := by
    rw [← fourQ_cast]
    exact_mod_cast boxMin_le_bd a b c d
  have edgeA : 2 * c ≤ -a ∧ -a ≤ 2 * d → (boxMin a b c d : ℝ) ≤ 3 * (a : ℝ) ^ 2 :=
    fun admissible => by exact_mod_cast boxMin_le_edge_a a b c d admissible
  have edgeB : 2 * c ≤ -b ∧ -b ≤ 2 * d → (boxMin a b c d : ℝ) ≤ 3 * (b : ℝ) ^ 2 :=
    fun admissible => by exact_mod_cast boxMin_le_edge_b a b c d admissible
  have edgeC : 2 * a ≤ -c ∧ -c ≤ 2 * b → (boxMin a b c d : ℝ) ≤ 3 * (c : ℝ) ^ 2 :=
    fun admissible => by exact_mod_cast boxMin_le_edge_c a b c d admissible
  have edgeD : 2 * a ≤ -d ∧ -d ≤ 2 * b → (boxMin a b c d : ℝ) ≤ 3 * (d : ℝ) ^ 2 :=
    fun admissible => by exact_mod_cast boxMin_le_edge_d a b c d admissible
  have origin : a ≤ 0 ∧ 0 ≤ b ∧ c ≤ 0 ∧ 0 ≤ d → (boxMin a b c d : ℝ) ≤ 0 :=
    fun inside => by exact_mod_cast boxMin_le_zero a b c d inside
  -- Away from the stationary line the form increases towards the edge `x = a`.
  rcases le_or_gt 0 (2 * (a : ℝ) + y) with leftA | leftA
  · have stepX : (a : ℝ) ^ 2 + a * y + y ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hax) (show (0 : ℝ) ≤ x + a + y by linarith)]
    have edge := edge_lower_bound a c d y (boxMin a b c d) hcy hyd ac ad edgeA
    linarith
  -- Towards the edge `x = b`.
  rcases le_or_gt (2 * (b : ℝ) + y) 0 with rightB | rightB
  · have stepX : (b : ℝ) ^ 2 + b * y + y ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hxb) (show (0 : ℝ) ≤ -(x + b + y) by linarith)]
    have edge := edge_lower_bound b c d y (boxMin a b c d) hcy hyd bc bd edgeB
    linarith
  -- Towards the edge `y = c`.
  rcases le_or_gt 0 (2 * (c : ℝ) + x) with lowC | lowC
  · have stepY : x ^ 2 + x * c + (c : ℝ) ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hcy) (show (0 : ℝ) ≤ y + c + x by linarith)]
    have edge := edge_lower_bound c a b x (boxMin a b c d) hax hxb (by linarith) (by linarith) edgeC
    linarith
  -- Towards the edge `y = d`.
  rcases le_or_gt (2 * (d : ℝ) + x) 0 with highD | highD
  · have stepY : x ^ 2 + x * d + (d : ℝ) ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hyd) (show (0 : ℝ) ≤ -(y + d + x) by linarith)]
    have edge := edge_lower_bound d a b x (boxMin a b c d) hax hxb (by linarith) (by linarith) edgeD
    linarith
  -- Both stationary lines cross the rectangle strictly; split on the signs of the point.
  rcases le_or_gt 0 x with xNonneg | xNeg <;> rcases le_or_gt 0 y with yNonneg | yNeg
  · have inside := origin ⟨le_of_lt (by exact_mod_cast (show (a : ℝ) < 0 by linarith)),
      by exact_mod_cast (show (0 : ℝ) ≤ b by linarith),
      le_of_lt (by exact_mod_cast (show (c : ℝ) < 0 by linarith)),
      by exact_mod_cast (show (0 : ℝ) ≤ d by linarith)⟩
    linarith [sq_nonneg (2 * x + y), sq_nonneg y]
  · exact lower_bound_of_signs a b c d x y (boxMin a b c d) hax hxb hcy hyd leftA rightB highD
      yNeg ad edgeA edgeD origin
  · have mirrored := lower_bound_of_signs c d a b y x (boxMin a b c d) hcy hyd hax hxb lowC highD
      rightB xNeg (by linarith) edgeC edgeB
      (fun inside => origin ⟨inside.2.2.1, inside.2.2.2, inside.1, inside.2.1⟩)
    linarith
  · have inside := origin ⟨le_of_lt (by exact_mod_cast (show (a : ℝ) < 0 by linarith)),
      le_of_lt (by exact_mod_cast (show (0 : ℝ) < b by linarith)),
      le_of_lt (by exact_mod_cast (show (c : ℝ) < 0 by linarith)),
      le_of_lt (by exact_mod_cast (show (0 : ℝ) < d by linarith))⟩
    linarith [sq_nonneg (2 * x + y), sq_nonneg y]

/-! ## Integer enclosures and the block check -/

/-- The dyadic scale `D = 2 ^ 64` of the integer enclosures. -/
def dyadicScale : ℤ := 2 ^ 64

/-- The dyadic scale is positive. -/
theorem dyadicScale_pos : 0 < dyadicScale := by
  unfold dyadicScale
  positivity

/-- Coordinate minima and maxima and the radius upper bound of one node, in `D`-scaled integers. -/
structure NodeBox where
  sMin : ℤ
  sMax : ℤ
  tMin : ℤ
  tMax : ℤ
  rMax : ℤ

/-- The `D`-scaled center of a site lies in the box and its scaled radius is below the bound. -/
def NodeBox.Encloses (box : NodeBox) (site : Site) : Prop :=
  (box.sMin : ℚ) ≤ dyadicScale * site.center.1 ∧ dyadicScale * site.center.1 ≤ box.sMax ∧
    (box.tMin : ℚ) ≤ dyadicScale * site.center.2 ∧
      dyadicScale * site.center.2 ≤ box.tMax ∧ dyadicScale * site.radius ≤ box.rMax

/-- Floor and ceiling enclosures of the scaled coordinates and radius give box membership. -/
theorem NodeBox.encloses_of_floor_ceil (box : NodeBox) (site : Site)
    (sLo : box.sMin ≤ ⌊(dyadicScale : ℚ) * site.center.1⌋)
    (sHi : ⌈(dyadicScale : ℚ) * site.center.1⌉ ≤ box.sMax)
    (tLo : box.tMin ≤ ⌊(dyadicScale : ℚ) * site.center.2⌋)
    (tHi : ⌈(dyadicScale : ℚ) * site.center.2⌉ ≤ box.tMax)
    (rHi : ⌈(dyadicScale : ℚ) * site.radius⌉ ≤ box.rMax) :
    box.Encloses site :=
  ⟨le_trans (by exact_mod_cast sLo) (Int.floor_le _),
    le_trans (Int.le_ceil _) (by exact_mod_cast sHi),
    le_trans (by exact_mod_cast tLo) (Int.floor_le _),
    le_trans (Int.le_ceil _) (by exact_mod_cast tHi),
    le_trans (Int.le_ceil _) (by exact_mod_cast rHi)⟩

/-- `lo ≤ D · num / den ≤ hi` for a positive denominator, cleared. -/
def coordinateCheck (num den lo hi : ℤ) : Bool :=
  decide (lo * den ≤ dyadicScale * num) && decide (dyadicScale * num ≤ hi * den)

/-- `D · num / den ≤ rUp` for a positive denominator, cleared. -/
def radiusCheck (num den rUp : ℤ) : Bool :=
  decide (dyadicScale * num ≤ rUp * den)

/-- `lo ≤ D s ≤ hi` and `D r ≤ rUp` for a wire site, cleared. -/
def encloseCheck (w : SiteWire) (lo hi : ℤ) (rUp : ℤ) : Bool :=
  coordinateCheck w.sNum w.sDen lo hi && radiusCheck w.rNum w.rDen rUp

/-- Full box membership of a wire site: the `s` enclosure with the radius bound, and the `t`
enclosure. -/
def NodeBox.memberCheck (box : NodeBox) (w : SiteWire) : Bool :=
  encloseCheck w box.sMin box.sMax box.rMax && coordinateCheck w.tNum w.tDen box.tMin box.tMax

/-- A passing coordinate check encloses the scaled fraction. -/
theorem coordinateCheck_sound (num den lo hi : ℤ) (denPos : 0 < den)
    (pass : coordinateCheck num den lo hi = true) :
    (lo : ℚ) ≤ dyadicScale * ((num : ℚ) / den) ∧
      dyadicScale * ((num : ℚ) / den) ≤ hi := by
  simp only [coordinateCheck, Bool.and_eq_true, decide_eq_true_eq] at pass
  have denPosQ : (0 : ℚ) < den := by exact_mod_cast denPos
  rw [mul_div_assoc']
  constructor
  · rw [le_div_iff₀ denPosQ]
    exact_mod_cast pass.1
  · rw [div_le_iff₀ denPosQ]
    exact_mod_cast pass.2

/-- A passing radius check bounds the scaled fraction. -/
theorem radiusCheck_sound (num den rUp : ℤ) (denPos : 0 < den)
    (pass : radiusCheck num den rUp = true) :
    dyadicScale * ((num : ℚ) / den) ≤ rUp := by
  simp only [radiusCheck, decide_eq_true_eq] at pass
  have denPosQ : (0 : ℚ) < den := by exact_mod_cast denPos
  rw [mul_div_assoc', div_le_iff₀ denPosQ]
  exact_mod_cast pass

/-- A passing enclosure check encloses the scaled `s` coordinate and bounds the scaled radius. -/
theorem encloseCheck_sound (w : SiteWire) (lo hi rUp : ℤ) (valid : w.valid = true)
    (pass : encloseCheck w lo hi rUp = true) :
    (lo : ℚ) ≤ dyadicScale * w.toSite.center.1 ∧ dyadicScale * w.toSite.center.1 ≤ hi ∧
      dyadicScale * w.toSite.radius ≤ rUp := by
  obtain ⟨sDenPos, -, rDenPos, -⟩ := w.valid_iff.1 valid
  simp only [encloseCheck, Bool.and_eq_true] at pass
  obtain ⟨sLo, sHi⟩ := coordinateCheck_sound w.sNum w.sDen lo hi sDenPos pass.1
  exact ⟨sLo, sHi, radiusCheck_sound w.rNum w.rDen rUp rDenPos pass.2⟩

/-- A passing member check places the wire site inside the box. -/
theorem NodeBox.memberCheck_sound (box : NodeBox) (w : SiteWire) (valid : w.valid = true)
    (pass : box.memberCheck w = true) : box.Encloses w.toSite := by
  obtain ⟨-, tDenPos, -, -⟩ := w.valid_iff.1 valid
  simp only [NodeBox.memberCheck, Bool.and_eq_true] at pass
  obtain ⟨sLo, sHi, rHi⟩ := encloseCheck_sound w box.sMin box.sMax box.rMax valid pass.1
  obtain ⟨tLo, tHi⟩ := coordinateCheck_sound w.tNum w.tDen box.tMin box.tMax tDenPos pass.2
  exact ⟨sLo, sHi, tLo, tHi, rHi⟩

/-- Lower `s` end of the gap rectangle of two boxes at horizontal lift `u`. -/
def NodeBox.gapSMin (boxA boxB : NodeBox) (u : ℤ) : ℤ :=
  boxA.sMin - boxB.sMax + 59 * dyadicScale * u

/-- Upper `s` end of the gap rectangle of two boxes at horizontal lift `u`. -/
def NodeBox.gapSMax (boxA boxB : NodeBox) (u : ℤ) : ℤ :=
  boxA.sMax - boxB.sMin + 59 * dyadicScale * u

/-- Lower `t` end of the gap rectangle of two boxes at vertical lift `v`. -/
def NodeBox.gapTMin (boxA boxB : NodeBox) (v : ℤ) : ℤ :=
  boxA.tMin - boxB.tMax + 59 * dyadicScale * v

/-- Upper `t` end of the gap rectangle of two boxes at vertical lift `v`. -/
def NodeBox.gapTMax (boxA boxB : NodeBox) (v : ℤ) : ℤ :=
  boxA.tMax - boxB.tMin + 59 * dyadicScale * v

/-- The block test of the specification: with `R = A.rMax + B.rMax` and the extrema
`L ≤ 4 Q ≤ H` over the gap rectangle, accept when `R < D ∧ 441 H < 40000 (D - R)²` or
`441 L > 40000 (D + R)²`. -/
def blockCheck (boxA boxB : NodeBox) (u v : ℤ) : Bool :=
  (decide (boxA.rMax + boxB.rMax < dyadicScale) &&
    decide (441 * boxMax (boxA.gapSMin boxB u) (boxA.gapSMax boxB u)
        (boxA.gapTMin boxB v) (boxA.gapTMax boxB v) <
      40000 * (dyadicScale - (boxA.rMax + boxB.rMax)) ^ 2)) ||
    decide (40000 * (dyadicScale + (boxA.rMax + boxB.rMax)) ^ 2 <
      441 * boxMin (boxA.gapSMin boxB u) (boxA.gapSMax boxB u)
        (boxA.gapTMin boxB v) (boxA.gapTMax boxB v))

/-- A passing block check makes every enclosed valid pair cross-safe at that lift. -/
theorem blockCheck_sound (boxA boxB : NodeBox) (u v : ℤ) (source target : Site)
    (sourceValid : SiteValid source) (targetValid : SiteValid target)
    (sourceIn : boxA.Encloses source) (targetIn : boxB.Encloses target)
    (pass : blockCheck boxA boxB u v = true) :
    CrossSafe (closedDisk source) (closedDisk (shiftSite target (u, v))) := by
  obtain ⟨-, -, -, -, sourcePos, sourceLt⟩ := sourceValid
  obtain ⟨-, -, -, -, targetPos, targetLt⟩ := targetValid
  obtain ⟨sLoA, sHiA, tLoA, tHiA, rA⟩ := sourceIn
  obtain ⟨sLoB, sHiB, tLoB, tHiB, rB⟩ := targetIn
  have scalePos : (0 : ℝ) < dyadicScale := by exact_mod_cast dyadicScale_pos
  have sLoA' : (boxA.sMin : ℝ) ≤ dyadicScale * (source.center.1 : ℝ) := by exact_mod_cast sLoA
  have sHiA' : (dyadicScale : ℝ) * (source.center.1 : ℝ) ≤ boxA.sMax := by exact_mod_cast sHiA
  have tLoA' : (boxA.tMin : ℝ) ≤ dyadicScale * (source.center.2 : ℝ) := by exact_mod_cast tLoA
  have tHiA' : (dyadicScale : ℝ) * (source.center.2 : ℝ) ≤ boxA.tMax := by exact_mod_cast tHiA
  have rA' : (dyadicScale : ℝ) * (source.radius : ℝ) ≤ boxA.rMax := by exact_mod_cast rA
  have sLoB' : (boxB.sMin : ℝ) ≤ dyadicScale * (target.center.1 : ℝ) := by exact_mod_cast sLoB
  have sHiB' : (dyadicScale : ℝ) * (target.center.1 : ℝ) ≤ boxB.sMax := by exact_mod_cast sHiB
  have tLoB' : (boxB.tMin : ℝ) ≤ dyadicScale * (target.center.2 : ℝ) := by exact_mod_cast tLoB
  have tHiB' : (dyadicScale : ℝ) * (target.center.2 : ℝ) ≤ boxB.tMax := by exact_mod_cast tHiB
  have rB' : (dyadicScale : ℝ) * (target.radius : ℝ) ≤ boxB.rMax := by exact_mod_cast rB
  have sourcePos' : (0 : ℝ) < source.radius := by exact_mod_cast sourcePos
  have targetPos' : (0 : ℝ) < target.radius := by exact_mod_cast targetPos
  -- The scaled gap lies in the integer rectangle.
  have gapFst : (axialGap source target (u, v)).1 =
      (source.center.1 : ℝ) - (target.center.1 : ℝ) + 59 * (u : ℝ) := axialGap_fst _ _ _
  have gapSnd : (axialGap source target (u, v)).2 =
      (source.center.2 : ℝ) - (target.center.2 : ℝ) + 59 * (v : ℝ) := axialGap_snd _ _ _
  have xLo : ((boxA.gapSMin boxB u : ℤ) : ℝ) ≤
      dyadicScale * (axialGap source target (u, v)).1 := by
    rw [gapFst, NodeBox.gapSMin]
    push_cast
    linarith
  have xHi : (dyadicScale : ℝ) * (axialGap source target (u, v)).1 ≤
      (boxA.gapSMax boxB u : ℤ) := by
    rw [gapFst, NodeBox.gapSMax]
    push_cast
    linarith
  have yLo : ((boxA.gapTMin boxB v : ℤ) : ℝ) ≤
      dyadicScale * (axialGap source target (u, v)).2 := by
    rw [gapSnd, NodeBox.gapTMin]
    push_cast
    linarith
  have yHi : (dyadicScale : ℝ) * (axialGap source target (u, v)).2 ≤
      (boxA.gapTMax boxB v : ℤ) := by
    rw [gapSnd, NodeBox.gapTMax]
    push_cast
    linarith
  have lower := boxMin_le_fourQ (boxA.gapSMin boxB u) (boxA.gapSMax boxB u)
    (boxA.gapTMin boxB v) (boxA.gapTMax boxB v) _ _ xLo xHi yLo yHi
  have upper := fourQ_le_boxMax (boxA.gapSMin boxB u) (boxA.gapSMax boxB u)
    (boxA.gapTMin boxB v) (boxA.gapTMax boxB v) _ _ xLo xHi yLo yHi
  have scaled : 4 * (((dyadicScale : ℝ) * (axialGap source target (u, v)).1) ^ 2 +
      (dyadicScale : ℝ) * (axialGap source target (u, v)).1 *
        ((dyadicScale : ℝ) * (axialGap source target (u, v)).2) +
      ((dyadicScale : ℝ) * (axialGap source target (u, v)).2) ^ 2) =
      4 * (dyadicScale : ℝ) ^ 2 * axialQ (axialGap source target (u, v)) := by
    simp only [axialQ]
    ring
  rw [scaled] at lower upper
  -- The scaled radius sum is below the stored bound.
  have radiusSum : (dyadicScale : ℝ) * ((source.radius : ℝ) + (target.radius : ℝ)) ≤
      (boxA.rMax : ℝ) + boxB.rMax := by
    linarith
  apply crossSafe_closedDisk_shiftSite_of_annulus source target (u, v) sourcePos.le targetPos.le
    (by linarith)
  simp only [blockCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at pass
  rcases pass with ⟨guard, near⟩ | far
  · left
    have guard' : (boxA.rMax : ℝ) + boxB.rMax < dyadicScale := by exact_mod_cast guard
    have near' : 441 * (boxMax (boxA.gapSMin boxB u) (boxA.gapSMax boxB u)
        (boxA.gapTMin boxB v) (boxA.gapTMax boxB v) : ℝ) <
        40000 * ((dyadicScale : ℝ) - ((boxA.rMax : ℝ) + boxB.rMax)) ^ 2 := by
      exact_mod_cast near
    have squares : ((dyadicScale : ℝ) - ((boxA.rMax : ℝ) + boxB.rMax)) ^ 2 ≤
        ((dyadicScale : ℝ) - dyadicScale * ((source.radius : ℝ) + (target.radius : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have key : (dyadicScale : ℝ) ^ 2 * (441 * axialQ (axialGap source target (u, v))) <
        (dyadicScale : ℝ) ^ 2 *
          (10000 * (1 - ((source.radius : ℝ) + (target.radius : ℝ))) ^ 2) := by
      nlinarith
    have cancelled := lt_of_mul_lt_mul_left key (by positivity)
    linarith
  · right
    have far' : 40000 * ((dyadicScale : ℝ) + ((boxA.rMax : ℝ) + boxB.rMax)) ^ 2 <
        441 * (boxMin (boxA.gapSMin boxB u) (boxA.gapSMax boxB u)
          (boxA.gapTMin boxB v) (boxA.gapTMax boxB v) : ℝ) := by
      exact_mod_cast far
    have squares :
        ((dyadicScale : ℝ) + dyadicScale * ((source.radius : ℝ) + target.radius)) ^ 2 ≤
          ((dyadicScale : ℝ) + ((boxA.rMax : ℝ) + boxB.rMax)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have key : (dyadicScale : ℝ) ^ 2 *
          (10000 * (1 + ((source.radius : ℝ) + (target.radius : ℝ))) ^ 2) <
        (dyadicScale : ℝ) ^ 2 * (441 * axialQ (axialGap source target (u, v))) := by
      nlinarith
    have cancelled := lt_of_mul_lt_mul_left key (by positivity)
    linarith

/-- The block check for wire sites certified inside their boxes by the member checks. -/
theorem blockCheck_sound_wire (boxA boxB : NodeBox) (u v : ℤ) (q q' : SiteWire)
    (qValid : q.valid = true) (q'Valid : q'.valid = true)
    (qIn : boxA.memberCheck q = true) (q'In : boxB.memberCheck q' = true)
    (pass : blockCheck boxA boxB u v = true) :
    CrossSafe (closedDisk q.toSite) (closedDisk (shiftSite q'.toSite (u, v))) :=
  blockCheck_sound boxA boxB u v q.toSite q'.toSite (q.valid_toSite qValid)
    (q'.valid_toSite q'Valid) (boxA.memberCheck_sound q qValid qIn)
    (boxB.memberCheck_sound q' q'Valid q'In) pass

/-! ## Containment and rotation routes -/

/-- `r ≤ r'` and `441 Q(gap) ≤ 10000 (r' - r)²`, in cleared integer arithmetic. -/
def containCheck (q q' : SiteWire) (nS nT : ℤ) : Bool :=
  decide (0 ≤ radiusDiffNum q q') &&
    decide (441 * gapQNum q q' nS nT * radiusSumDen q q' ^ 2 ≤
      10000 * radiusDiffNum q q' ^ 2 * gapQDen q q')

/-- A passing containment check places the source disk inside the shifted target disk. -/
theorem containCheck_sound (q q' : SiteWire) (lift : ℤ × ℤ)
    (qValid : q.valid = true) (q'Valid : q'.valid = true)
    (pass : containCheck q q' lift.1 lift.2 = true) :
    closedDisk q.toSite ⊆ closedDisk (shiftSite q'.toSite lift) := by
  obtain ⟨-, -, rDenPos, -⟩ := q.valid_iff.1 qValid
  obtain ⟨-, -, rDenPos', -⟩ := q'.valid_iff.1 q'Valid
  have denPos := gapQDen_pos q q' qValid q'Valid
  have sumDenPos := radiusSumDen_pos q q' qValid q'Valid
  simp only [containCheck, Bool.and_eq_true, decide_eq_true_eq] at pass
  apply closedDisk_subset_closedDisk_shiftSite
  · show (q.rNum : ℚ) / q.rDen ≤ (q'.rNum : ℚ) / q'.rDen
    rw [div_le_div_iff₀ (by exact_mod_cast rDenPos) (by exact_mod_cast rDenPos')]
    have order : (0 : ℚ) ≤ q'.rNum * q.rDen - q.rNum * q'.rDen := by exact_mod_cast pass.1
    linarith
  · rw [axialQ_axialGap_toSite q q' lift qValid q'Valid, radiusDiff_toSite q q' qValid q'Valid]
    exact contain_of_cleared _ _ _ _ denPos sumDenPos (by exact_mod_cast pass.2)

/-- The rotated center `(-t, s + t)` equals `(s' - 59 nS, t' - 59 nT)` and `r = r'`, cleared. -/
def rotateMatchCheck (q q' : SiteWire) (nS nT : ℤ) : Bool :=
  decide (-q.tNum * q'.sDen = (q'.sNum - 59 * nS * q'.sDen) * q.tDen) &&
    (decide ((q.sNum * q.tDen + q.tNum * q.sDen) * q'.tDen =
        (q'.tNum - 59 * nT * q'.tDen) * (q.sDen * q.tDen)) &&
      decide (q.rNum * q'.rDen = q'.rNum * q.rDen))

/-- A passing rotation match is an exact rotation route. -/
theorem rotateMatchCheck_sound (q q' : SiteWire) (lift : ℤ × ℤ)
    (qValid : q.valid = true) (q'Valid : q'.valid = true)
    (pass : rotateMatchCheck q q' lift.1 lift.2 = true) :
    rotateSite q.toSite = shiftSite q'.toSite lift := by
  obtain ⟨sDenPos, tDenPos, rDenPos, -⟩ := q.valid_iff.1 qValid
  obtain ⟨sDenPos', tDenPos', rDenPos', -⟩ := q'.valid_iff.1 q'Valid
  have sDenNe : (q.sDen : ℚ) ≠ 0 := by exact_mod_cast sDenPos.ne'
  have tDenNe : (q.tDen : ℚ) ≠ 0 := by exact_mod_cast tDenPos.ne'
  have rDenNe : (q.rDen : ℚ) ≠ 0 := by exact_mod_cast rDenPos.ne'
  have sDenNe' : (q'.sDen : ℚ) ≠ 0 := by exact_mod_cast sDenPos'.ne'
  have tDenNe' : (q'.tDen : ℚ) ≠ 0 := by exact_mod_cast tDenPos'.ne'
  have rDenNe' : (q'.rDen : ℚ) ≠ 0 := by exact_mod_cast rDenPos'.ne'
  simp only [rotateMatchCheck, Bool.and_eq_true, decide_eq_true_eq] at pass
  obtain ⟨first, second, radius⟩ := pass
  have first' : (-q.tNum * q'.sDen : ℚ) = (q'.sNum - 59 * lift.1 * q'.sDen) * q.tDen := by
    exact_mod_cast first
  have second' : ((q.sNum * q.tDen + q.tNum * q.sDen) * q'.tDen : ℚ) =
      (q'.tNum - 59 * lift.2 * q'.tDen) * (q.sDen * q.tDen) := by
    exact_mod_cast second
  have radius' : (q.rNum * q'.rDen : ℚ) = q'.rNum * q.rDen := by exact_mod_cast radius
  simp only [rotateSite, shiftSite, SiteWire.toSite, axialRotateRat_apply, Site.mk.injEq,
    Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · field_simp
    linear_combination first'
  · field_simp
    linear_combination second'
  · rw [div_eq_div_iff rDenNe rDenNe']
    linear_combination radius'

/-! ## Lists of wire sites -/

/-- The nine relative lifts `{-1, 0, 1}²` as an explicit list. -/
def nineLifts : List (ℤ × ℤ) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]

/-- Every lift of the nine square is listed. -/
theorem mem_nineLifts_of_nineLift (lift : ℤ × ℤ) (nine : NineLift lift) :
    lift ∈ nineLifts := by
  obtain ⟨first, second⟩ := lift
  have firstLe : |first| ≤ 1 := nine.1
  have secondLe : |second| ≤ 1 := nine.2
  rw [abs_le] at firstLe secondLe
  have firstCases : first = -1 ∨ first = 0 ∨ first = 1 := by omega
  have secondCases : second = -1 ∨ second = 0 ∨ second = 1 := by omega
  rcases firstCases with rfl | rfl | rfl <;> rcases secondCases with rfl | rfl | rfl <;>
    simp [nineLifts]

/-- Every pair from the two lists passes the exact check at each of the nine lifts. -/
def pairCheckAll (sites others : List SiteWire) : Bool :=
  sites.all fun q => others.all fun q' => nineLifts.all fun lift => pairCheck q q' lift.1 lift.2

/-- The semantic site set named by a list of wire sites. -/
def wireSet (sites : List SiteWire) : Set Site :=
  {site | ∃ q ∈ sites, q.toSite = site}

/-- Every site of a wire set of valid wires is valid. -/
theorem wireSet_valid (sites : List SiteWire) (valid : ∀ q ∈ sites, q.valid = true) :
    ∀ site ∈ wireSet sites, SiteValid site := by
  rintro site ⟨q, qMem, rfl⟩
  exact q.valid_toSite (valid q qMem)

/-- A passing list check gives the nine-lift hypothesis of `crossSafe_U_of_nine_lifts`. -/
theorem pairCheck_all_sound (sites others : List SiteWire)
    (valid : ∀ q ∈ sites, q.valid = true) (otherValid : ∀ q ∈ others, q.valid = true)
    (pass : pairCheckAll sites others = true) :
    ∀ site ∈ wireSet sites, ∀ other ∈ wireSet others, ∀ lift : ℤ × ℤ,
      NineLift lift → CrossSafe (closedDisk site) (closedDisk (shiftSite other lift)) := by
  rintro site ⟨q, qMem, rfl⟩ other ⟨q', q'Mem, rfl⟩ lift nine
  simp only [pairCheckAll, List.all_eq_true] at pass
  exact pairCheck_sound q q' lift (valid q qMem) (otherValid q' q'Mem)
    (pass q qMem q' q'Mem lift (mem_nineLifts_of_nineLift lift nine))

/-- Cross-safety of the periodic unions of two wire lists from the list check. -/
theorem crossSafe_U_of_pairCheckAll (sites others : List SiteWire)
    (valid : ∀ q ∈ sites, q.valid = true) (otherValid : ∀ q ∈ others, q.valid = true)
    (pass : pairCheckAll sites others = true) :
    CrossSafe (U (wireSet sites)) (U (wireSet others)) :=
  crossSafe_U_of_nine_lifts (wireSet sites) (wireSet others)
    (wireSet_valid sites valid) (wireSet_valid others otherValid)
    (pairCheck_all_sound sites others valid otherValid pass)

/-! ## Examples -/

/-- A small valid wire site. -/
example : SiteWire.valid ⟨100, 21, 0, 1, 1, 1000⟩ = true := by decide

/-- A radius of one half is not valid. -/
example : SiteWire.valid ⟨1, 1, 1, 1, 1, 2⟩ = false := by decide

/-- Two coincident small disks: the near branch accepts. -/
example : pairCheck ⟨1, 1, 1, 1, 1, 10⟩ ⟨1, 1, 1, 1, 1, 10⟩ 0 0 = true := by decide

/-- Centers at axial gap `100 / 21`, physical distance exactly one: rejected. -/
example : pairCheck ⟨100, 21, 0, 1, 1, 1000⟩ ⟨0, 1, 0, 1, 1, 1000⟩ 0 0 = false := by decide

/-- Centers thirty axial units apart: the far branch accepts. -/
example : pairCheck ⟨30, 1, 0, 1, 1, 10⟩ ⟨0, 1, 0, 1, 1, 10⟩ 0 0 = true := by decide

/-- One site against itself passes at all nine lifts. -/
example : pairCheckAll [⟨1, 1, 1, 1, 1, 10⟩] [⟨1, 1, 1, 1, 1, 10⟩] = true := by decide

/-- A disk of radius `1 / 10` centered half an axial unit away fits inside radius `1 / 4`. -/
example : containCheck ⟨1, 2, 0, 1, 1, 10⟩ ⟨0, 1, 0, 1, 1, 4⟩ 0 0 = true := by decide

/-- The same disk does not fit inside radius `1 / 5`. -/
example : containCheck ⟨1, 2, 0, 1, 1, 10⟩ ⟨0, 1, 0, 1, 1, 5⟩ 0 0 = false := by decide

/-- Rotating `(1, 2)` gives `(-2, 3)`, which is `(57, 3)` shifted by the lift `(1, 0)`. -/
example : rotateMatchCheck ⟨1, 1, 2, 1, 1, 10⟩ ⟨57, 1, 3, 1, 1, 10⟩ 1 0 = true := by decide

/-- A mismatched second coordinate is rejected. -/
example : rotateMatchCheck ⟨1, 1, 2, 1, 1, 10⟩ ⟨57, 1, 4, 1, 1, 10⟩ 1 0 = false := by decide

/-- Two degenerate boxes at the origin with tiny radius bounds pass the near branch. -/
example : blockCheck ⟨0, 0, 0, 0, 1⟩ ⟨0, 0, 0, 0, 1⟩ 0 0 = true := by decide

end Erdos188.UpperBound
