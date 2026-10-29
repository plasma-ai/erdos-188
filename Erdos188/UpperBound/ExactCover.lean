module

public import Erdos188.UpperBound.Covering
public import Erdos188.UpperBound.Wire
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Exact integer checker for covering certificates

The executable side of the covering interface. A wire site is six integers, a
certificate record is one of the three productions `D`, `T`, `S`, and the leaf
test is the literal integer comparison of the exact corner arithmetic: every
real inequality of `LeafValid` is multiplied through by the positive
denominators of the dyadic cell, the rational direction map, and the rational
site. The stream checker replays a preorder certificate from the root cell
with an explicit stack. Both checkers are computable Boolean functions whose
acceptance is proved to imply the semantic `LeafValid` and `Certified`
predicates of `Covering`. No finite family or certificate is supplied here;
the small examples at the end only demonstrate computability.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- One certificate record: a direction halving, a translation quartering, or a leaf. -/
inductive CoverRecord where
  /-- `D d i e h k`: halve the direction interval of the addressed cell. -/
  | direction (d i e h k : ℕ)
  /-- `T d i e h k`: quarter the translation square of the addressed cell. -/
  | translation (d i e h k : ℕ)
  /-- `S d i e h k j ordinal lift_s lift_t`: one lifted site closes the addressed cell. -/
  | leaf (d i e h k : ℕ) (j : ℤ) (ordinal : ℕ) (liftS liftT : ℤ)

/-- `A = 2^d`, the dyadic direction scale as an integer. -/
def directionScale (d : ℕ) : ℤ := 2 ^ d

/-- `T = 2i + 1 - 4A`; the midpoint direction parameter is `T / (2A)`. -/
def midpointNum (d i : ℕ) : ℤ := 2 * i + 1 - 4 * directionScale d

/-- `U = i + 1 - 2A`; the right direction endpoint is `U / A`. -/
def rightNum (d i : ℕ) : ℤ := i + 1 - 2 * directionScale d

/-- `H = T² + 2AT + 4A²`; the direction denominator at the midpoint is `H / (4A²)`. -/
def midpointDenomNum (d i : ℕ) : ℤ :=
  midpointNum d i ^ 2 + 2 * directionScale d * midpointNum d i + 4 * directionScale d ^ 2

/-- `G = U² + AU + A²`; the direction denominator at the right endpoint is `G / A²`. -/
def rightDenomNum (d i : ℕ) : ℤ :=
  rightNum d i ^ 2 + directionScale d * rightNum d i + directionScale d ^ 2

/-- `P_s = T² - 4A²`; the first axial midpoint-direction coordinate is `100 P_s / (21 H)`. -/
def axialNumS (d i : ℕ) : ℤ := midpointNum d i ^ 2 - 4 * directionScale d ^ 2

/-- `P_t = -T(T + 4A)`; the second axial midpoint-direction coordinate is `100 P_t / (21 H)`. -/
def axialNumT (d i : ℕ) : ℤ := -midpointNum d i * (midpointNum d i + 4 * directionScale d)

/-- `R = 2000 G n_r - 1733 A |j| d_r`, the numerator of the usable radius. -/
def usableNum (cell : Cell) (j : ℤ) (site : SiteWire) : ℤ :=
  2000 * rightDenomNum cell.directionDepth cell.directionIndex * site.rNum -
    1733 * directionScale cell.directionDepth * j.natAbs * site.rDen

/-- `V = 2000 G d_r`, the positive denominator of the usable radius. -/
def usableDen (cell : Cell) (site : SiteWire) : ℤ :=
  2000 * rightDenomNum cell.directionDepth cell.directionIndex * site.rDen

/-- `W = 21 H C d_s d_t`, the common positive denominator of both corner offsets. -/
def offsetDen (cell : Cell) (site : SiteWire) : ℤ :=
  21 * midpointDenomNum cell.directionDepth cell.directionIndex * 2 ^ cell.translationDepth *
    site.sDen * site.tDen

/-- `X`, the first corner-offset numerator over `W`; lift `n_s` shifts the center by `59 n_s`. -/
def offsetNumS (cell : Cell) (j : ℤ) (site : SiteWire) (liftS : ℤ) (ε : Fin 2) : ℤ :=
  59 * ((cell.translationIndexS + ε.val : ℕ) : ℤ) *
      (21 * midpointDenomNum cell.directionDepth cell.directionIndex) * site.sDen * site.tDen +
    100 * j * axialNumS cell.directionDepth cell.directionIndex * 2 ^ cell.translationDepth *
      site.sDen * site.tDen -
    21 * midpointDenomNum cell.directionDepth cell.directionIndex * 2 ^ cell.translationDepth *
      site.sNum * site.tDen -
    59 * liftS * offsetDen cell site

/-- `Y`, the second corner-offset numerator over `W`; lift `n_t` shifts the center by `59 n_t`. -/
def offsetNumT (cell : Cell) (j : ℤ) (site : SiteWire) (liftT : ℤ) (δ : Fin 2) : ℤ :=
  59 * ((cell.translationIndexT + δ.val : ℕ) : ℤ) *
      (21 * midpointDenomNum cell.directionDepth cell.directionIndex) * site.sDen * site.tDen +
    100 * j * axialNumT cell.directionDepth cell.directionIndex * 2 ^ cell.translationDepth *
      site.sDen * site.tDen -
    21 * midpointDenomNum cell.directionDepth cell.directionIndex * 2 ^ cell.translationDepth *
      site.tNum * site.sDen -
    59 * liftT * offsetDen cell site

/-- The exact squared comparison at one corner: `441 (X² + XY + Y²) V² ≤ 10000 W² R²`. -/
def cornerCheck (cell : Cell) (j : ℤ) (site : SiteWire) (liftS liftT : ℤ) (ε δ : Fin 2) : Bool :=
  decide (441 * (offsetNumS cell j site liftS ε ^ 2 +
      offsetNumS cell j site liftS ε * offsetNumT cell j site liftT δ +
        offsetNumT cell j site liftT δ ^ 2) * usableDen cell site ^ 2 ≤
    10000 * offsetDen cell site ^ 2 * usableNum cell j site ^ 2)

/-- The integer leaf test: bounded step, positive denominators and usable radius, four corners. -/
def leafCheck (cell : Cell) (j : ℤ) (site : SiteWire) (liftS liftT : ℤ) : Bool :=
  decide (-21 ≤ j) && decide (j ≤ 20) &&
    decide (0 < site.sDen) && decide (0 < site.tDen) && decide (0 < site.rDen) &&
    decide (0 < usableNum cell j site) &&
    cornerCheck cell j site liftS liftT 0 0 && cornerCheck cell j site liftS liftT 0 1 &&
    cornerCheck cell j site liftS liftT 1 0 && cornerCheck cell j site liftS liftT 1 1

/-- The record address equals the five coordinates of the current cell. -/
def Cell.hasAddress (cell : Cell) (d i e h k : ℕ) : Bool :=
  decide (cell.directionDepth = d) && decide (cell.directionIndex = i) &&
    decide (cell.translationDepth = e) && decide (cell.translationIndexS = h) &&
    decide (cell.translationIndexT = k)

/-- The leaf test against the site at a table ordinal; a missing ordinal fails. -/
def siteLeafCheck (sites : List SiteWire) (ordinal : ℕ) (cell : Cell) (j liftS liftT : ℤ) :
    Bool :=
  match sites[ordinal]? with
  | none => false
  | some site => leafCheck cell j site liftS liftT

/-- Replay preorder records against an explicit cell stack; both must run out together. -/
def coverStreamAux (sites : List SiteWire) : List Cell → List CoverRecord → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | cell :: stack, CoverRecord.direction d i e h k :: rest =>
      cell.hasAddress d i e h k &&
        coverStreamAux sites (cell.directionChild 0 :: cell.directionChild 1 :: stack) rest
  | cell :: stack, CoverRecord.translation d i e h k :: rest =>
      cell.hasAddress d i e h k &&
        coverStreamAux sites (cell.translationChild 0 0 :: cell.translationChild 0 1 ::
          cell.translationChild 1 0 :: cell.translationChild 1 1 :: stack) rest
  | cell :: stack, CoverRecord.leaf d i e h k j ordinal liftS liftT :: rest =>
      cell.hasAddress d i e h k && siteLeafCheck sites ordinal cell j liftS liftT &&
        coverStreamAux sites stack rest

/-- The whole certificate check: replay every record from the root cell alone. -/
def coverStreamCheck (sites : List SiteWire) (records : List CoverRecord) : Bool :=
  coverStreamAux sites [rootCell] records

/-- The direction scale is positive. -/
theorem directionScale_pos (d : ℕ) : 0 < directionScale d := by
  unfold directionScale
  positivity

/-- `H = (T + A)² + 3A²` is positive. -/
theorem midpointDenomNum_pos (d i : ℕ) : 0 < midpointDenomNum d i := by
  have hA := directionScale_pos d
  unfold midpointDenomNum
  nlinarith [sq_nonneg (midpointNum d i + directionScale d)]

/-- `4G = (2U + A)² + 3A²` is positive. -/
theorem rightDenomNum_pos (d i : ℕ) : 0 < rightDenomNum d i := by
  have hA := directionScale_pos d
  unfold rightDenomNum
  nlinarith [sq_nonneg (2 * rightNum d i + directionScale d)]

/-- The usable-radius denominator is positive when the radius denominator is. -/
theorem usableDen_pos (cell : Cell) (site : SiteWire) (hr : 0 < site.rDen) :
    0 < usableDen cell site := by
  have hG := rightDenomNum_pos cell.directionDepth cell.directionIndex
  unfold usableDen
  positivity

/-- The offset denominator is positive when both center denominators are. -/
theorem offsetDen_pos (cell : Cell) (site : SiteWire) (hs : 0 < site.sDen) (ht : 0 < site.tDen) :
    0 < offsetDen cell site := by
  have hH := midpointDenomNum_pos cell.directionDepth cell.directionIndex
  unfold offsetDen
  positivity

/-- The midpoint direction parameter is `T / (2A)`. -/
theorem directionMidpoint_eq (d i : ℕ) :
    directionMidpoint d i = ((midpointNum d i : ℤ) : ℝ) / (2 * (2 : ℝ) ^ d) := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  unfold directionMidpoint midpointNum directionScale
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- The right direction endpoint is `U / A`. -/
theorem directionRight_eq (d i : ℕ) :
    directionRight d i = ((rightNum d i : ℤ) : ℝ) / (2 : ℝ) ^ d := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  unfold directionRight rightNum directionScale
  push_cast
  field_simp
  ring

/-- The direction denominator at the midpoint is `H / (4A²)`. -/
theorem directionDenom_midpoint (d i : ℕ) :
    directionDenom (directionMidpoint d i) =
      ((midpointDenomNum d i : ℤ) : ℝ) / (4 * ((2 : ℝ) ^ d) ^ 2) := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  rw [directionMidpoint_eq]
  unfold directionDenom midpointDenomNum directionScale
  push_cast
  field_simp
  ring

/-- The first direction numerator at the midpoint is `P_s / (4A²)`. -/
theorem directionNumS_midpoint (d i : ℕ) :
    directionNumS (directionMidpoint d i) =
      ((axialNumS d i : ℤ) : ℝ) / (4 * ((2 : ℝ) ^ d) ^ 2) := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  rw [directionMidpoint_eq]
  unfold directionNumS axialNumS directionScale
  push_cast
  field_simp
  ring

/-- The second direction numerator at the midpoint is `P_t / (4A²)`. -/
theorem directionNumT_midpoint (d i : ℕ) :
    directionNumT (directionMidpoint d i) =
      ((axialNumT d i : ℤ) : ℝ) / (4 * ((2 : ℝ) ^ d) ^ 2) := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  rw [directionMidpoint_eq]
  unfold directionNumT axialNumT directionScale
  push_cast
  field_simp
  ring

/-- The first axial coordinate of the midpoint direction is `100 P_s / (21 H)`. -/
theorem directionAxial_midpoint_fst (d i : ℕ) :
    (directionAxial (directionMidpoint d i)).1 =
      100 * ((axialNumS d i : ℤ) : ℝ) / (21 * ((midpointDenomNum d i : ℤ) : ℝ)) := by
  have hfour : (4 * ((2 : ℝ) ^ d) ^ 2) ≠ 0 := by positivity
  unfold directionAxial
  dsimp only
  rw [directionNumS_midpoint, directionDenom_midpoint, div_div_div_cancel_right₀ hfour]
  ring

/-- The second axial coordinate of the midpoint direction is `100 P_t / (21 H)`. -/
theorem directionAxial_midpoint_snd (d i : ℕ) :
    (directionAxial (directionMidpoint d i)).2 =
      100 * ((axialNumT d i : ℤ) : ℝ) / (21 * ((midpointDenomNum d i : ℤ) : ℝ)) := by
  have hfour : (4 * ((2 : ℝ) ^ d) ^ 2) ≠ 0 := by positivity
  unfold directionAxial
  dsimp only
  rw [directionNumT_midpoint, directionDenom_midpoint, div_div_div_cancel_right₀ hfour]
  ring

/-- The direction-error allowance is `1733 A / (2000 G)`. -/
theorem directionError_eq (d i : ℕ) :
    directionError d i = 1733 * (2 : ℝ) ^ d / (2000 * ((rightDenomNum d i : ℤ) : ℝ)) := by
  have hpower : (2 : ℝ) ^ d ≠ 0 := ne_of_gt (pow_pos (by norm_num) d)
  have hG : ((rightDenomNum d i : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (rightDenomNum_pos d i).ne'
  have hden : directionDenom (directionRight d i) =
      ((rightDenomNum d i : ℤ) : ℝ) / ((2 : ℝ) ^ d) ^ 2 := by
    rw [directionRight_eq]
    unfold directionDenom rightDenomNum directionScale
    push_cast
    field_simp
  unfold directionError directionRadius
  rw [hden, pow_succ]
  field_simp
  ring

/-- The usable radius of a wire witness is `R / V`. -/
theorem usableRadius_eq (cell : Cell) (j : ℤ) (site : SiteWire) (lift : ℤ × ℤ)
    (hr : 0 < site.rDen) :
    usableRadius cell ⟨j, site.toSite, lift⟩ =
      ((usableNum cell j site : ℤ) : ℝ) / ((usableDen cell site : ℤ) : ℝ) := by
  have hG : ((rightDenomNum cell.directionDepth cell.directionIndex : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (rightDenomNum_pos cell.directionDepth cell.directionIndex).ne'
  have hr' : (site.rDen : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold usableRadius Cell.errorAllowance
  rw [directionError_eq]
  unfold usableNum usableDen SiteWire.toSite directionScale
  push_cast [Nat.cast_natAbs]
  field_simp

/-- One endpoint of a translation interval, uniformly in the selecting bit. -/
theorem translationEndpoint_eq (e h : ℕ) :
    ∀ ε : Fin 2, translationEndpoint e h ε = 59 * ((h + ε.val : ℕ) : ℝ) / (2 : ℝ) ^ e
  | 0 => by simp [translationEndpoint, translationLeft]
  | 1 => by simp [translationEndpoint, translationRight]

/-- The first corner-offset coordinate of a wire witness is `X / W`. -/
theorem cornerOffset_fst (cell : Cell) (j : ℤ) (site : SiteWire) (lift : ℤ × ℤ) (ε δ : Fin 2)
    (hs : 0 < site.sDen) (ht : 0 < site.tDen) :
    (cornerOffset cell ⟨j, site.toSite, lift⟩ ε δ).1 =
      ((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) / ((offsetDen cell site : ℤ) : ℝ) := by
  have hH : ((midpointDenomNum cell.directionDepth cell.directionIndex : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (midpointDenomNum_pos cell.directionDepth cell.directionIndex).ne'
  have hpower : (2 : ℝ) ^ cell.translationDepth ≠ 0 :=
    ne_of_gt (pow_pos (by norm_num) cell.translationDepth)
  have hs' : (site.sDen : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht' : (site.tDen : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold cornerOffset Cell.corner translationCorner Cell.midpoint
  simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, ratAxialToReal,
    intAxialToReal]
  rw [translationEndpoint_eq, directionAxial_midpoint_fst]
  unfold offsetNumS offsetDen SiteWire.toSite
  push_cast
  field_simp
  ring

/-- The second corner-offset coordinate of a wire witness is `Y / W`. -/
theorem cornerOffset_snd (cell : Cell) (j : ℤ) (site : SiteWire) (lift : ℤ × ℤ) (ε δ : Fin 2)
    (hs : 0 < site.sDen) (ht : 0 < site.tDen) :
    (cornerOffset cell ⟨j, site.toSite, lift⟩ ε δ).2 =
      ((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) / ((offsetDen cell site : ℤ) : ℝ) := by
  have hH : ((midpointDenomNum cell.directionDepth cell.directionIndex : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast (midpointDenomNum_pos cell.directionDepth cell.directionIndex).ne'
  have hpower : (2 : ℝ) ^ cell.translationDepth ≠ 0 :=
    ne_of_gt (pow_pos (by norm_num) cell.translationDepth)
  have hs' : (site.sDen : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht' : (site.tDen : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold cornerOffset Cell.corner translationCorner Cell.midpoint
  simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, ratAxialToReal,
    intAxialToReal]
  rw [translationEndpoint_eq, directionAxial_midpoint_snd]
  unfold offsetNumT offsetDen SiteWire.toSite
  push_cast
  field_simp
  ring

/-- A passing integer corner comparison is the real corner bound of `LeafValid`. -/
theorem cornerCheck_sound (cell : Cell) (j : ℤ) (site : SiteWire) (lift : ℤ × ℤ) (ε δ : Fin 2)
    (hs : 0 < site.sDen) (ht : 0 < site.tDen) (hr : 0 < site.rDen)
    (hcheck : cornerCheck cell j site lift.1 lift.2 ε δ = true) :
    (441 / 10000 : ℝ) * axialQ (cornerOffset cell ⟨j, site.toSite, lift⟩ ε δ) ≤
      usableRadius cell ⟨j, site.toSite, lift⟩ ^ 2 := by
  have hW : (0 : ℝ) < ((offsetDen cell site : ℤ) : ℝ) := by
    exact_mod_cast offsetDen_pos cell site hs ht
  have hV : (0 : ℝ) < ((usableDen cell site : ℤ) : ℝ) := by
    exact_mod_cast usableDen_pos cell site hr
  simp only [cornerCheck, decide_eq_true_eq] at hcheck
  have hreal : (441 : ℝ) * (((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) ^ 2 +
      ((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) * ((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) +
        ((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) ^ 2) * ((usableDen cell site : ℤ) : ℝ) ^ 2 ≤
      10000 * ((offsetDen cell site : ℤ) : ℝ) ^ 2 * ((usableNum cell j site : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast hcheck
  unfold axialQ
  rw [cornerOffset_fst cell j site lift ε δ hs ht, cornerOffset_snd cell j site lift ε δ hs ht,
    usableRadius_eq cell j site lift hr]
  have hcombine : (441 / 10000 : ℝ) *
      ((((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) / ((offsetDen cell site : ℤ) : ℝ)) ^ 2 +
        ((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) / ((offsetDen cell site : ℤ) : ℝ) *
          (((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) / ((offsetDen cell site : ℤ) : ℝ)) +
        (((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) / ((offsetDen cell site : ℤ) : ℝ)) ^ 2) =
      441 * (((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) ^ 2 +
        ((offsetNumS cell j site lift.1 ε : ℤ) : ℝ) * ((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) +
          ((offsetNumT cell j site lift.2 δ : ℤ) : ℝ) ^ 2) /
        (10000 * ((offsetDen cell site : ℤ) : ℝ) ^ 2) := by
    field_simp
  rw [hcombine, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [hreal]

/-- A passing integer leaf test is a valid semantic leaf; the wire lift is the witness lift. -/
theorem leafCheck_sound (siteSet : Set Site) (cell : Cell) (j : ℤ) (site : SiteWire)
    (lift : ℤ × ℤ) (hmem : site.toSite ∈ siteSet)
    (hcheck : leafCheck cell j site lift.1 lift.2 = true) :
    LeafValid siteSet cell ⟨j, site.toSite, lift⟩ := by
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hcheck
  obtain ⟨hlower, hupper, hs, ht, hr, hpos, h00, h01, h10, h11⟩ := hcheck
  have hcorners : ∀ ε δ : Fin 2, cornerCheck cell j site lift.1 lift.2 ε δ = true := by
    simp only [Fin.forall_fin_two]
    exact ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
  refine ⟨hlower, hupper, hmem, ?_, ?_⟩
  · rw [usableRadius_eq cell j site lift hr]
    apply div_pos
    · exact_mod_cast hpos
    · exact_mod_cast usableDen_pos cell site hr
  · intro ε δ
    exact cornerCheck_sound cell j site lift ε δ hs ht hr (hcorners ε δ)

/-- A passing ordinal leaf test names a listed site that passes the leaf test. -/
theorem siteLeafCheck_sound (sites : List SiteWire) (ordinal : ℕ) (cell : Cell)
    (j liftS liftT : ℤ) (hcheck : siteLeafCheck sites ordinal cell j liftS liftT = true) :
    ∃ site ∈ sites, leafCheck cell j site liftS liftT = true := by
  rcases hget : sites[ordinal]? with _ | site
  · simp [siteLeafCheck, hget] at hcheck
  · simp only [siteLeafCheck, hget] at hcheck
    exact ⟨site, List.mem_of_getElem? hget, hcheck⟩

/-- A passing replay from any stack certifies every cell on that stack. -/
theorem coverStreamAux_sound (siteSet : Set Site) (sites : List SiteWire)
    (hsites : ∀ site ∈ sites, site.toSite ∈ siteSet) (records : List CoverRecord) :
    ∀ stack : List Cell, coverStreamAux sites stack records = true →
      ∀ cell ∈ stack, Certified siteSet cell := by
  induction records with
  | nil =>
      intro stack hcheck cell hcell
      cases stack with
      | nil => simp at hcell
      | cons top stack => simp [coverStreamAux] at hcheck
  | cons record rest ih =>
      intro stack hcheck cell hcell
      cases stack with
      | nil => simp [coverStreamAux] at hcheck
      | cons top stack =>
          cases record with
          | direction d i e h k =>
              simp only [coverStreamAux, Bool.and_eq_true] at hcheck
              have children := ih _ hcheck.2
              rcases List.mem_cons.mp hcell with heq | hmem
              · rw [heq]
                exact Certified.directionSplit top (children _ (by simp)) (children _ (by simp))
              · exact children cell (by simp [hmem])
          | translation d i e h k =>
              simp only [coverStreamAux, Bool.and_eq_true] at hcheck
              have children := ih _ hcheck.2
              rcases List.mem_cons.mp hcell with heq | hmem
              · rw [heq]
                refine Certified.translationSplit top ?_
                simp only [Fin.forall_fin_two]
                exact ⟨⟨children _ (by simp), children _ (by simp)⟩,
                  ⟨children _ (by simp), children _ (by simp)⟩⟩
              · exact children cell (by simp [hmem])
          | leaf d i e h k j ordinal liftS liftT =>
              simp only [coverStreamAux, Bool.and_eq_true] at hcheck
              obtain ⟨⟨_, hleaf⟩, hrest⟩ := hcheck
              rcases List.mem_cons.mp hcell with heq | hmem
              · rw [heq]
                obtain ⟨site, hsite, hpass⟩ :=
                  siteLeafCheck_sound sites ordinal top j liftS liftT hleaf
                exact Certified.leaf top ⟨j, site.toSite, (liftS, liftT)⟩
                  (leafCheck_sound siteSet top j site (liftS, liftT) (hsites site hsite) hpass)
              · exact ih stack hrest cell hmem

/-- A passing certificate check certifies the root cell for any family listing the sites. -/
theorem coverStreamCheck_sound (siteSet : Set Site) (sites : List SiteWire)
    (hsites : ∀ site ∈ sites, site.toSite ∈ siteSet) (records : List CoverRecord)
    (hcheck : coverStreamCheck sites records = true) : Certified siteSet rootCell :=
  coverStreamAux_sound siteSet sites hsites records [rootCell] hcheck rootCell
    (List.mem_singleton_self rootCell)

/-- A wide site centered in the period square, for the computability examples only. -/
def wideSite : SiteWire := ⟨59, 2, 59, 2, 20, 1⟩

example : leafCheck ⟨3, 5, 11, 100, 200⟩ 0 ⟨11859, 4096, 23659, 4096, 1, 50⟩ 0 0 = true := by
  decide

example :
    leafCheck ⟨3, 5, 11, 100, 200⟩ 3 ⟨-504941235, 10350592, 109298403, 1478656, 3, 10⟩ 1 (-1) =
      true := by
  decide

example : coverStreamCheck [wideSite]
    [.direction 0 0 0 0 0, .translation 1 0 0 0 0,
      .leaf 1 0 1 0 0 0 0 0 0, .leaf 1 0 1 0 1 0 0 0 0,
      .leaf 1 0 1 1 0 0 0 0 0, .leaf 1 0 1 1 1 0 0 0 0,
      .leaf 1 1 0 0 0 1 0 0 0] = true := by
  decide

example : coverStreamCheck [wideSite] [.leaf 0 0 0 0 0 0 0 0 0, .leaf 0 0 0 0 0 0 0 0 0] =
    false := by
  decide

example : coverStreamCheck [wideSite]
    [.direction 0 0 0 0 0, .leaf 1 0 0 0 0 0 0 0 0, .leaf 1 0 0 0 0 0 0 0 0] = false := by
  decide

example : coverStreamCheck [wideSite]
    [.direction 0 0 0 0 0, .leaf 1 0 0 0 0 0 0 0 0, .leaf 1 1 0 0 0 (-21) 0 0 0] = false := by
  decide

end Erdos188.UpperBound
