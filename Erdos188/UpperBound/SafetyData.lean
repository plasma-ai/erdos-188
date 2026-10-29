module

public import Erdos188.UpperBound.ExactSafety
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Kernel checker for safety-tree certificates

The computable replay of one safety obligation of the certificate: two
families of wire sites stored in balanced index trees, the two position
permutations, and the preorder node and pair records of the product
partition. The checker recomputes every node box from the members of its
range, replays the block test for every pruned lift bit and the exact pair
test for every residual bit of every emitted pair, and accepts only when the
structural recursion closes the root product exactly. Acceptance is proved to
give cross-safety of the two named site sets at all nine relative lifts, hence
of their periodic unions. Every definition consumed by `decide` is computable
and structurally recursive so that the kernel can reduce it; the step form is
chunkable through an append lemma. No finite family or certificate appears
here.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-! ## Index trees

A tree of `depth` levels addresses the positions `[0, 2 ^ depth)`. At a node with `depth + 1`
levels left, position `p` descends left when `p < 2 ^ depth` and right with `p - 2 ^ depth`
otherwise, so bit `depth` of `p` selects the child and in-order leaves are in position order. A
leaf answers only at depth `0` and position `0`; every other lookup is absent. -/

/-- A balanced binary tree with values at position-addressed leaves. -/
inductive IndexTree (α : Type) where
  /-- No value below this point. -/
  | empty : IndexTree α
  /-- One stored value, well placed only at depth zero. -/
  | leaf (value : α) : IndexTree α
  /-- The lower and upper halves of a position range. -/
  | node (left right : IndexTree α) : IndexTree α

/-- Position lookup by bit descent, in `O(depth)` steps. -/
def IndexTree.get? {α : Type} : IndexTree α → ℕ → ℕ → Option α
  | .empty, _, _ => none
  | .leaf value, 0, 0 => some value
  | .leaf _, 0, _ + 1 => none
  | .leaf _, _ + 1, _ => none
  | .node _ _, 0, _ => none
  | .node left right, depth + 1, p =>
      if p < 2 ^ depth then left.get? depth p else right.get? depth (p - 2 ^ depth)

/-- The stored values in position order. -/
def IndexTree.toList {α : Type} : IndexTree α → List α
  | .empty => []
  | .leaf value => [value]
  | .node left right => left.toList ++ right.toList

/-- A found value is a stored value. -/
theorem IndexTree.get?_mem {α : Type} (tree : IndexTree α) (depth p : ℕ) (value : α)
    (found : tree.get? depth p = some value) : value ∈ tree.toList := by
  induction tree generalizing depth p with
  | empty => simp [IndexTree.get?] at found
  | leaf stored =>
      cases depth with
      | zero =>
          cases p with
          | zero =>
              simp only [IndexTree.get?, Option.some.injEq] at found
              simp [IndexTree.toList, found]
          | succ p => simp [IndexTree.get?] at found
      | succ depth => simp [IndexTree.get?] at found
  | node left right leftIH rightIH =>
      cases depth with
      | zero => simp [IndexTree.get?] at found
      | succ depth =>
          simp only [IndexTree.get?] at found
          simp only [IndexTree.toList, List.mem_append]
          split at found
          · exact Or.inl (leftIH depth p found)
          · exact Or.inr (rightIH depth _ found)

/-- The stored values sit at positions below `count`: an empty subtree carries no position, a
leaf at depth zero carries position `0` when `count` is positive, and a node splits `count` at
`2 ^ depth`. Only this inclusion is used; the check also rejects a leaf at positive depth. -/
def IndexTree.shapeCheck {α : Type} : IndexTree α → ℕ → ℕ → Bool
  | .empty, _, count => decide (count = 0)
  | .leaf _, 0, count => decide (0 < count)
  | .leaf _, _ + 1, _ => false
  | .node _ _, 0, _ => false
  | .node left right, depth + 1, count =>
      left.shapeCheck depth (min count (2 ^ depth)) && right.shapeCheck depth (count - 2 ^ depth)

/-- Every stored value of a well-shaped tree is found at a position below `count`. -/
theorem IndexTree.shapeCheck_get? {α : Type} (tree : IndexTree α) (depth count : ℕ)
    (shape : tree.shapeCheck depth count = true) :
    ∀ value ∈ tree.toList, ∃ p, p < count ∧ tree.get? depth p = some value := by
  induction tree generalizing depth count with
  | empty => simp [IndexTree.toList]
  | leaf stored =>
      cases depth with
      | zero =>
          simp only [IndexTree.shapeCheck, decide_eq_true_eq] at shape
          intro value mem
          simp only [IndexTree.toList, List.mem_singleton] at mem
          exact ⟨0, shape, by simp [IndexTree.get?, mem]⟩
      | succ depth => simp [IndexTree.shapeCheck] at shape
  | node left right leftIH rightIH =>
      cases depth with
      | zero => simp [IndexTree.shapeCheck] at shape
      | succ depth =>
          simp only [IndexTree.shapeCheck, Bool.and_eq_true] at shape
          intro value mem
          simp only [IndexTree.toList, List.mem_append] at mem
          rcases mem with mem | mem
          · obtain ⟨p, lt, found⟩ := leftIH depth _ shape.1 value mem
            refine ⟨p, lt_of_lt_of_le lt (min_le_left _ _), ?_⟩
            simp only [IndexTree.get?, ite_eq_left (lt_of_lt_of_le lt (min_le_right _ _))]
            exact found
          · obtain ⟨p, lt, found⟩ := rightIH depth _ shape.2 value mem
            refine ⟨2 ^ depth + p, by omega, ?_⟩
            simp only [IndexTree.get?, ite_eq_right (by omega : ¬ 2 ^ depth + p < 2 ^ depth),
              Nat.add_sub_cancel_left]
            exact found

/-- Insert a value at a free position, building the descent path; `none` when the position is
occupied, out of range, or blocked by a misplaced leaf. -/
def IndexTree.insert? {α : Type} : IndexTree α → ℕ → ℕ → α → Option (IndexTree α)
  | .empty, 0, 0, value => some (.leaf value)
  | .empty, 0, _ + 1, _ => none
  | .empty, depth + 1, p, value =>
      if p < 2 ^ depth then
        (IndexTree.insert? .empty depth p value).map fun left => .node left .empty
      else
        (IndexTree.insert? .empty depth (p - 2 ^ depth) value).map fun right => .node .empty right
  | .leaf _, _, _, _ => none
  | .node _ _, 0, _, _ => none
  | .node left right, depth + 1, p, value =>
      if p < 2 ^ depth then
        (left.insert? depth p value).map fun left' => .node left' right
      else
        (right.insert? depth (p - 2 ^ depth) value).map fun right' => .node left right'

/-- The node case of `insert?_spec`, given the specification one level down. -/
theorem IndexTree.insert?_spec_node {α : Type} (depth : ℕ)
    (below : ∀ (tree : IndexTree α) (p : ℕ) (value : α) (tree' : IndexTree α),
      tree.insert? depth p value = some tree' →
        tree.get? depth p = none ∧
          ∀ q, tree'.get? depth q = if q = p then some value else tree.get? depth q)
    (left right : IndexTree α) (p : ℕ) (value : α) (tree' : IndexTree α)
    (inserted : (IndexTree.node left right).insert? (depth + 1) p value = some tree') :
    (IndexTree.node left right).get? (depth + 1) p = none ∧
      ∀ q, tree'.get? (depth + 1) q =
        if q = p then some value else (IndexTree.node left right).get? (depth + 1) q := by
  simp only [IndexTree.insert?] at inserted
  split at inserted
  · rename_i lt
    obtain ⟨left', insertedLeft, rfl⟩ := Option.map_eq_some_iff.1 inserted
    obtain ⟨free, spec⟩ := below left p value left' insertedLeft
    refine ⟨by simp only [IndexTree.get?, ite_eq_left lt, free], fun q => ?_⟩
    by_cases qlt : q < 2 ^ depth
    · simp only [IndexTree.get?, ite_eq_left qlt, spec q]
    · have ne : q ≠ p := by omega
      simp only [IndexTree.get?, ite_eq_right qlt, ite_eq_right ne]
  · rename_i ge
    obtain ⟨right', insertedRight, rfl⟩ := Option.map_eq_some_iff.1 inserted
    obtain ⟨free, spec⟩ := below right (p - 2 ^ depth) value right' insertedRight
    refine ⟨by simp only [IndexTree.get?, ite_eq_right ge, free], fun q => ?_⟩
    by_cases qlt : q < 2 ^ depth
    · have ne : q ≠ p := by omega
      simp only [IndexTree.get?, ite_eq_left qlt, ite_eq_right ne]
    · have shift : q - 2 ^ depth = p - 2 ^ depth ↔ q = p := by omega
      simp only [IndexTree.get?, ite_eq_right qlt, spec (q - 2 ^ depth), shift]

/-- A successful insertion fills exactly one free position. -/
theorem IndexTree.insert?_spec {α : Type} (depth : ℕ) :
    ∀ (tree : IndexTree α) (p : ℕ) (value : α) (tree' : IndexTree α),
      tree.insert? depth p value = some tree' →
        tree.get? depth p = none ∧
          ∀ q, tree'.get? depth q = if q = p then some value else tree.get? depth q := by
  induction depth with
  | zero =>
      intro tree p value tree' inserted
      cases tree with
      | empty =>
          cases p with
          | zero =>
              simp only [IndexTree.insert?, Option.some.injEq] at inserted
              subst inserted
              refine ⟨rfl, fun q => ?_⟩
              cases q <;> simp [IndexTree.get?]
          | succ p => simp [IndexTree.insert?] at inserted
      | leaf stored => simp [IndexTree.insert?] at inserted
      | node left right => simp [IndexTree.insert?] at inserted
  | succ depth ih =>
      intro tree p value tree' inserted
      cases tree with
      | leaf stored => simp [IndexTree.insert?] at inserted
      | node left right =>
          exact IndexTree.insert?_spec_node depth ih left right p value tree' inserted
      | empty =>
          have asNode : (IndexTree.empty : IndexTree α).insert? (depth + 1) p value =
              (IndexTree.node .empty .empty).insert? (depth + 1) p value := rfl
          rw [asNode] at inserted
          obtain ⟨free, spec⟩ :=
            IndexTree.insert?_spec_node depth ih .empty .empty p value tree' inserted
          refine ⟨by simp [IndexTree.get?], fun q => ?_⟩
          rw [spec q]
          simp [IndexTree.get?]

/-! ## Position permutations -/

/-- A tree of family ordinals addressed by position. -/
abbrev OrdTree := IndexTree ℕ

/-- Mark, in position order, the ordinal of every position below `count` in a tree of marks;
`none` on a missing position, an ordinal at or above `n`, or a repeated ordinal. -/
def markPositions (perm : OrdTree) (depth n : ℕ) : ℕ → IndexTree Unit → Option (IndexTree Unit)
  | 0, marks => some marks
  | count + 1, marks =>
      match markPositions perm depth n count marks with
      | none => none
      | some marked =>
          match perm.get? depth count with
          | none => none
          | some ordinal => if ordinal < n then marked.insert? depth ordinal () else none

/-- All `n` positions carry distinct ordinals below `n`. -/
def permBijection (perm : OrdTree) (depth n : ℕ) : Bool :=
  (markPositions perm depth n n .empty).isSome

/-- A completed marking run marks every processed ordinal, keeps earlier marks, and never
processes one ordinal at two positions. -/
theorem markPositions_spec (perm : OrdTree) (depth n : ℕ) (count : ℕ) :
    ∀ marks marked : IndexTree Unit, markPositions perm depth n count marks = some marked →
      (∀ o, marks.get? depth o = some () → marked.get? depth o = some ()) ∧
        (∀ p, p < count → ∃ o, o < n ∧ perm.get? depth p = some o ∧ marked.get? depth o = some ()) ∧
          ∀ p q o, p < count → q < count →
            perm.get? depth p = some o → perm.get? depth q = some o → p = q := by
  induction count with
  | zero =>
      intro marks marked run
      simp only [markPositions, Option.some.injEq] at run
      subst run
      exact ⟨fun _ h => h, fun p lt => absurd lt (Nat.not_lt_zero p),
        fun p _ _ lt _ _ _ => absurd lt (Nat.not_lt_zero p)⟩
  | succ count ih =>
      intro marks marked run
      simp only [markPositions] at run
      revert run
      rcases firstRun : markPositions perm depth n count marks with _ | marked₁ <;> intro run
      · simp at run
      rcases ordinalEq : perm.get? depth count with _ | ordinal
      · simp [ordinalEq] at run
      simp only [ordinalEq] at run
      split at run
      · rename_i ordinalLt
        obtain ⟨mono, members, injective⟩ := ih marks marked₁ firstRun
        obtain ⟨free, spec⟩ := IndexTree.insert?_spec depth marked₁ ordinal () marked run
        refine ⟨fun o marked₀ => ?_, fun p lt => ?_, fun p q o pLt qLt pEq qEq => ?_⟩
        · rw [spec o]
          split
          · rfl
          · exact mono o marked₀
        · rcases Nat.lt_succ_iff_lt_or_eq.1 lt with lt | rfl
          · obtain ⟨o, oLt, found, isMarked⟩ := members p lt
            refine ⟨o, oLt, found, ?_⟩
            rw [spec o]
            split
            · rfl
            · exact isMarked
          · exact ⟨ordinal, ordinalLt, ordinalEq, by rw [spec ordinal, ite_eq_left rfl]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 pLt with pLt | rfl <;>
            rcases Nat.lt_succ_iff_lt_or_eq.1 qLt with qLt | rfl
          · exact injective p q o pLt qLt pEq qEq
          · obtain ⟨o', -, found, isMarked⟩ := members p pLt
            rw [pEq] at found
            rw [qEq] at ordinalEq
            cases found
            cases ordinalEq
            rw [free] at isMarked
            exact absurd isMarked (by simp)
          · obtain ⟨o', -, found, isMarked⟩ := members q qLt
            rw [qEq] at found
            rw [pEq] at ordinalEq
            cases found
            cases ordinalEq
            rw [free] at isMarked
            exact absurd isMarked (by simp)
          · rfl
      · simp at run

/-- A passing bijection check hits every ordinal below `n` from some position below `n`. -/
theorem permBijection_sound (perm : OrdTree) (depth n : ℕ)
    (pass : permBijection perm depth n = true) :
    ∀ o, o < n → ∃ p, p < n ∧ perm.get? depth p = some o := by
  simp only [permBijection, Option.isSome_iff_exists] at pass
  obtain ⟨marked, run⟩ := pass
  obtain ⟨-, members, injective⟩ := markPositions_spec perm depth n n .empty marked run
  have bounded : ∀ p : Fin n, (perm.get? depth p).getD 0 < n := fun p => by
    obtain ⟨o, oLt, found, -⟩ := members p.1 p.2
    rw [found]
    exact oLt
  let map : Fin n → Fin n := fun p => ⟨(perm.get? depth p).getD 0, bounded p⟩
  have mapInjective : Function.Injective map := by
    intro p q eq
    obtain ⟨o, -, pFound, -⟩ := members p.1 p.2
    obtain ⟨o', -, qFound, -⟩ := members q.1 q.2
    have values : (perm.get? depth p).getD 0 = (perm.get? depth q).getD 0 := congrArg Fin.val eq
    rw [pFound, qFound] at values
    simp only [Option.getD_some] at values
    subst values
    exact Fin.ext (injective p.1 q.1 o p.2 q.2 pFound qFound)
  intro o oLt
  obtain ⟨p, hit⟩ := Finite.injective_iff_surjective.1 mapInjective ⟨o, oLt⟩
  obtain ⟨o', -, found, -⟩ := members p.1 p.2
  have value : (perm.get? depth p).getD 0 = o := congrArg Fin.val hit
  rw [found, Option.getD_some] at value
  subst value
  exact ⟨p.1, p.2, found⟩

/-! ## Wire families -/

/-- One family of an obligation: ordinal-addressed sites, the shared tree depth, the
position-to-ordinal permutation, and the family count. -/
structure WireFamily where
  sites : IndexTree SiteWire
  depth : ℕ
  perm : OrdTree
  count : ℕ

/-- The site at a position: its ordinal through the permutation, then the site tree. -/
def WireFamily.siteAt (fam : WireFamily) (p : ℕ) : Option SiteWire :=
  match fam.perm.get? fam.depth p with
  | none => none
  | some ordinal => fam.sites.get? fam.depth ordinal

/-- The site tree has the shape of the ordinals `[0, count)` and the permutation is a bijection. -/
def WireFamily.wellFormed (fam : WireFamily) : Bool :=
  fam.sites.shapeCheck fam.depth fam.count && permBijection fam.perm fam.depth fam.count

/-- A site found at a position is a stored site. -/
theorem WireFamily.siteAt_mem (fam : WireFamily) (p : ℕ) (w : SiteWire)
    (found : fam.siteAt p = some w) : w ∈ fam.sites.toList := by
  unfold WireFamily.siteAt at found
  revert found
  rcases fam.perm.get? fam.depth p with _ | ordinal <;> intro found
  · simp at found
  · exact fam.sites.get?_mem fam.depth ordinal w found

/-- Every stored site of a well-formed family sits at some position below its count. -/
theorem WireFamily.wellFormed_siteAt (fam : WireFamily) (pass : fam.wellFormed = true) :
    ∀ w ∈ fam.sites.toList, ∃ p, p < fam.count ∧ fam.siteAt p = some w := by
  simp only [WireFamily.wellFormed, Bool.and_eq_true] at pass
  intro w mem
  obtain ⟨ordinal, ordinalLt, found⟩ :=
    fam.sites.shapeCheck_get? fam.depth fam.count pass.1 w mem
  obtain ⟨p, pLt, permEq⟩ :=
    permBijection_sound fam.perm fam.depth fam.count pass.2 ordinal ordinalLt
  refine ⟨p, pLt, ?_⟩
  simp only [WireFamily.siteAt, permEq]
  exact found

/-! ## Wire lift bits

Wire bit `i` names the `i`-th entry of `nineLifts`, the lexicographic order `(-1, -1), (-1, 0),
…, (1, 1)`. A wire lift `n` places the target at `a' + 59 n`, while `shiftSite q' l` has center
`a' - 59 l`, so bit `i` decodes to `shiftSite q' (-n_i)`, and both `blockCheck` and `pairCheck`
are called with `(u, v) = -n_i`. -/

/-- The `(u, v)` of `shiftSite` named by wire bit `i`: minus the `i`-th wire lift. -/
def checkLift (i : ℕ) : ℤ × ℤ :=
  (-(nineLifts.getD i (0, 0)).1, -(nineLifts.getD i (0, 0)).2)

/-- The nine wire bit indices. -/
def liftIndices : List ℕ := List.range 9

/-- Every lift of the nine square is the decoding of some wire bit. -/
theorem exists_checkLift (lift : ℤ × ℤ) (nine : NineLift lift) :
    ∃ i, i < 9 ∧ checkLift i = lift := by
  have listed : ∀ l ∈ nineLifts, ∃ i, i < 9 ∧ checkLift i = l := by decide
  exact listed lift (mem_nineLifts_of_nineLift lift nine)

/-! ## Box recomputation -/

/-- `⌊a / b⌋` for a positive denominator, as Euclidean division. -/
def floorDiv (a b : ℤ) : ℤ := a / b

/-- `⌈a / b⌉ = -⌊-a / b⌋` for a positive denominator. -/
def ceilDiv (a b : ℤ) : ℤ := -((-a) / b)

/-- The integer floor is below the rational quotient. -/
theorem floorDiv_le (a b : ℤ) (bPos : 0 < b) : (floorDiv a b : ℚ) ≤ (a : ℚ) / b := by
  have bPosQ : (0 : ℚ) < b := by exact_mod_cast bPos
  rw [le_div_iff₀ bPosQ]
  exact_mod_cast Int.ediv_mul_le a bPos.ne'

/-- The rational quotient is below the integer ceiling. -/
theorem le_ceilDiv (a b : ℤ) (bPos : 0 < b) : (a : ℚ) / b ≤ (ceilDiv a b : ℚ) := by
  have bPosQ : (0 : ℚ) < b := by exact_mod_cast bPos
  rw [div_le_iff₀ bPosQ]
  have key : ((-a) / b : ℤ) * b ≤ -a := Int.ediv_mul_le (-a) bPos.ne'
  have cast : (((-a) / b : ℤ) : ℚ) * b ≤ -a := by exact_mod_cast key
  simp only [ceilDiv]
  push_cast
  linarith

/-- The exact `D`-scaled enclosure of one wire site: floors and ceilings of its coordinates and
the ceiling of its radius. -/
def siteBox (w : SiteWire) : NodeBox where
  sMin := floorDiv (dyadicScale * w.sNum) w.sDen
  sMax := ceilDiv (dyadicScale * w.sNum) w.sDen
  tMin := floorDiv (dyadicScale * w.tNum) w.tDen
  tMax := ceilDiv (dyadicScale * w.tNum) w.tDen
  rMax := ceilDiv (dyadicScale * w.rNum) w.rDen

/-- The coordinate-wise union of two boxes. -/
def NodeBox.union (box other : NodeBox) : NodeBox where
  sMin := min box.sMin other.sMin
  sMax := max box.sMax other.sMax
  tMin := min box.tMin other.tMin
  tMax := max box.tMax other.tMax
  rMax := max box.rMax other.rMax

/-- A valid wire site lies in its own box. -/
theorem siteBox_encloses (w : SiteWire) (valid : w.valid = true) :
    (siteBox w).Encloses w.toSite := by
  obtain ⟨sDenPos, tDenPos, rDenPos, -⟩ := w.valid_iff.1 valid
  apply NodeBox.encloses_of_floor_ceil
  · rw [Int.le_floor]
    show ((floorDiv (dyadicScale * w.sNum) w.sDen : ℤ) : ℚ) ≤
      (dyadicScale : ℚ) * ((w.sNum : ℚ) / w.sDen)
    rw [mul_div_assoc']
    exact_mod_cast floorDiv_le (dyadicScale * w.sNum) w.sDen sDenPos
  · rw [Int.ceil_le]
    show (dyadicScale : ℚ) * ((w.sNum : ℚ) / w.sDen) ≤
      ((ceilDiv (dyadicScale * w.sNum) w.sDen : ℤ) : ℚ)
    rw [mul_div_assoc']
    exact_mod_cast le_ceilDiv (dyadicScale * w.sNum) w.sDen sDenPos
  · rw [Int.le_floor]
    show ((floorDiv (dyadicScale * w.tNum) w.tDen : ℤ) : ℚ) ≤
      (dyadicScale : ℚ) * ((w.tNum : ℚ) / w.tDen)
    rw [mul_div_assoc']
    exact_mod_cast floorDiv_le (dyadicScale * w.tNum) w.tDen tDenPos
  · rw [Int.ceil_le]
    show (dyadicScale : ℚ) * ((w.tNum : ℚ) / w.tDen) ≤
      ((ceilDiv (dyadicScale * w.tNum) w.tDen : ℤ) : ℚ)
    rw [mul_div_assoc']
    exact_mod_cast le_ceilDiv (dyadicScale * w.tNum) w.tDen tDenPos
  · rw [Int.ceil_le]
    show (dyadicScale : ℚ) * ((w.rNum : ℚ) / w.rDen) ≤
      ((ceilDiv (dyadicScale * w.rNum) w.rDen : ℤ) : ℚ)
    rw [mul_div_assoc']
    exact_mod_cast le_ceilDiv (dyadicScale * w.rNum) w.rDen rDenPos

/-- The union encloses everything the first box encloses. -/
theorem NodeBox.union_encloses_left (box other : NodeBox) (site : Site)
    (inside : box.Encloses site) : (box.union other).Encloses site := by
  obtain ⟨sLo, sHi, tLo, tHi, rHi⟩ := inside
  exact ⟨le_trans (Int.cast_le.2 (min_le_left _ _)) sLo,
    le_trans sHi (Int.cast_le.2 (le_max_left _ _)),
    le_trans (Int.cast_le.2 (min_le_left _ _)) tLo,
    le_trans tHi (Int.cast_le.2 (le_max_left _ _)),
    le_trans rHi (Int.cast_le.2 (le_max_left _ _))⟩

/-- The union encloses everything the second box encloses. -/
theorem NodeBox.union_encloses_right (box other : NodeBox) (site : Site)
    (inside : other.Encloses site) : (box.union other).Encloses site := by
  obtain ⟨sLo, sHi, tLo, tHi, rHi⟩ := inside
  exact ⟨le_trans (Int.cast_le.2 (min_le_right _ _)) sLo,
    le_trans sHi (Int.cast_le.2 (le_max_right _ _)),
    le_trans (Int.cast_le.2 (min_le_right _ _)) tLo,
    le_trans tHi (Int.cast_le.2 (le_max_right _ _)),
    le_trans rHi (Int.cast_le.2 (le_max_right _ _))⟩

/-- Fold the boxes of `count` consecutive positions from `start` into an accumulator; `none` on
a missing site. Each visit costs two `O(depth)` lookups, since positions reach the ordinal-addressed
site tree through the permutation and are not contiguous there. -/
def WireFamily.rangeBoxAux (fam : WireFamily) : ℕ → ℕ → NodeBox → Option NodeBox
  | _, 0, box => some box
  | start, count + 1, box =>
      match fam.siteAt start with
      | none => none
      | some w => fam.rangeBoxAux (start + 1) count (box.union (siteBox w))

/-- The recomputed box of the nonempty position range `[lo, hi)`. -/
def WireFamily.rangeBox (fam : WireFamily) (lo hi : ℕ) : Option NodeBox :=
  match fam.siteAt lo with
  | none => none
  | some w => if lo < hi then fam.rangeBoxAux (lo + 1) (hi - (lo + 1)) (siteBox w) else none

/-- The fold only grows the accumulator and encloses every visited valid site. -/
theorem WireFamily.rangeBoxAux_encloses (fam : WireFamily) (start count : ℕ) :
    ∀ box box' : NodeBox, fam.rangeBoxAux start count box = some box' →
      (∀ site, box.Encloses site → box'.Encloses site) ∧
        ∀ k, k < count → ∀ w, fam.siteAt (start + k) = some w → w.valid = true →
          box'.Encloses w.toSite := by
  induction count generalizing start with
  | zero =>
      intro box box' run
      simp only [WireFamily.rangeBoxAux, Option.some.injEq] at run
      subst run
      exact ⟨fun _ inside => inside, fun k lt => absurd lt (Nat.not_lt_zero k)⟩
  | succ count ih =>
      intro box box' run
      simp only [WireFamily.rangeBoxAux] at run
      revert run
      rcases wEq : fam.siteAt start with _ | w₀ <;> intro run
      · simp at run
      obtain ⟨mono, members⟩ := ih (start + 1) _ _ run
      refine ⟨fun site inside => mono site (NodeBox.union_encloses_left _ _ site inside), ?_⟩
      intro k lt w wEq' valid
      cases k with
      | zero =>
          rw [Nat.add_zero, wEq] at wEq'
          cases wEq'
          exact mono _ (NodeBox.union_encloses_right _ _ _ (siteBox_encloses _ valid))
      | succ k =>
          have shift : start + 1 + k = start + (k + 1) := by omega
          exact members k (by omega) w (by rw [shift]; exact wEq') valid

/-- A recomputed range box encloses every valid site at a position of the range. -/
theorem WireFamily.rangeBox_encloses (fam : WireFamily) (lo hi : ℕ) (box : NodeBox)
    (boxEq : fam.rangeBox lo hi = some box) (p : ℕ) (loLe : lo ≤ p) (pLt : p < hi) (w : SiteWire)
    (wEq : fam.siteAt p = some w) (valid : w.valid = true) : box.Encloses w.toSite := by
  simp only [WireFamily.rangeBox] at boxEq
  revert boxEq
  rcases w₀Eq : fam.siteAt lo with _ | w₀ <;> intro boxEq
  · simp at boxEq
  dsimp only at boxEq
  split at boxEq
  · obtain ⟨mono, members⟩ := fam.rangeBoxAux_encloses (lo + 1) (hi - (lo + 1)) _ _ boxEq
    rcases Nat.eq_or_lt_of_le loLe with rfl | loLt
    · rw [w₀Eq] at wEq
      cases wEq
      exact mono _ (siteBox_encloses _ valid)
    · have shift : lo + 1 + (p - (lo + 1)) = p := by omega
      exact members (p - (lo + 1)) (by omega) w (by rw [shift]; exact wEq) valid
  · simp at boxEq

/-! ## Certificate records and replay state -/

/-- One wire record of a safety section, without the obligation and node identifiers. -/
inductive SafetyRecord where
  /-- `node a0 a1 b0 b1 in_mask pruned_mask kind cut`: one product node in preorder. -/
  | node (a0 a1 b0 b1 inMask prunedMask kind cut : ℕ)
  /-- `pair a_position b_position remaining_mask`: one exact pair of a kind-1 node. -/
  | pair (aPos bPos mask : ℕ)

/-- One pending obligation of the replay: a product awaiting its node record with the expected
incoming mask, or a kind-1 node whose next expected pair is `(aPos, bPos)` in left-major order
over `[·, a1) × [b0, b1)` with the residual mask. -/
inductive SafetyTask where
  /-- The product `[a0, a1) × [b0, b1)` must be certified for every bit of `mask`. -/
  | node (a0 a1 b0 b1 mask : ℕ)
  /-- The pairs from `(aPos, bPos)` to `(a1 - 1, b1 - 1)` must each pass every bit of `mask`. -/
  | pair (a1 b0 b1 mask aPos bPos : ℕ)
  deriving DecidableEq

/-- The explicit stack of pending obligations. -/
abbrev SafetyState := List SafetyTask

/-- `in_mask & ~pruned_mask` on nine-bit masks. -/
def residualMask (inMask pruned : ℕ) : ℕ := inMask ^^^ (inMask &&& pruned)

/-- Every bit of `mask` passes the block test at its decoded lift. -/
def blockBits (boxA boxB : NodeBox) (mask : ℕ) : Bool :=
  liftIndices.all fun i => !mask.testBit i || blockCheck boxA boxB (checkLift i).1 (checkLift i).2

/-- Every bit of `mask` passes the exact pair test at its decoded lift. -/
def pairBits (q q' : SiteWire) (mask : ℕ) : Bool :=
  liftIndices.all fun i => !mask.testBit i || pairCheck q q' (checkLift i).1 (checkLift i).2

/-- The pending obligations after the pair `(aPos, bPos)`: the next pair in left-major order, or
the rest of the stack after the last pair. -/
def advancePair (a1 b0 b1 mask aPos bPos : ℕ) (stack : SafetyState) : SafetyState :=
  if bPos + 1 < b1 then .pair a1 b0 b1 mask aPos (bPos + 1) :: stack
  else if aPos + 1 < a1 then .pair a1 b0 b1 mask (aPos + 1) b0 :: stack
  else stack

/-- The obligations opened by a checked node according to its kind: kind `0` closes the node with
residual zero, kind `1` opens its pair sequence, kinds `2` and `3` push the two children of a
left or right split at `cut`, in preorder. -/
def nodeContinue (a0 a1 b0 b1 residual kind cut : ℕ) (stack : SafetyState) : Option SafetyState :=
  match kind with
  | 0 => if decide (residual = 0) && decide (cut = 0) then some stack else none
  | 1 =>
      if decide (residual ≠ 0) && decide (cut = 0) then
        some (.pair a1 b0 b1 residual a0 b0 :: stack)
      else none
  | 2 =>
      if decide (a0 < cut) && decide (cut < a1) then
        some (.node a0 cut b0 b1 residual :: .node cut a1 b0 b1 residual :: stack)
      else none
  | 3 =>
      if decide (b0 < cut) && decide (cut < b1) then
        some (.node a0 a1 b0 cut residual :: .node a0 a1 cut b1 residual :: stack)
      else none
  | _ => none

/-- Replay one record against the top obligation: a node record must repeat the expected ranges
and mask, prune a subset of them with passing block tests on the recomputed boxes, and continue by
kind; a pair record must be the expected pair with the residual mask and pass every residual bit. -/
def safetyStepOne (fam fam' : WireFamily) : SafetyState → SafetyRecord → Option SafetyState
  | .node a0 a1 b0 b1 mask :: stack, .node a0' a1' b0' b1' inMask pruned kind cut =>
      if decide (a0 = a0') && decide (a1 = a1') && decide (b0 = b0') && decide (b1 = b1') &&
          decide (inMask = mask) && decide (pruned &&& mask = pruned) then
        match fam.rangeBox a0 a1, fam'.rangeBox b0 b1 with
        | some boxA, some boxB =>
            if blockBits boxA boxB pruned then
              nodeContinue a0 a1 b0 b1 (residualMask mask pruned) kind cut stack
            else none
        | _, _ => none
      else none
  | .pair a1 b0 b1 mask aPos bPos :: stack, .pair aPos' bPos' mask' =>
      if decide (aPos = aPos') && decide (bPos = bPos') && decide (mask = mask') then
        match fam.siteAt aPos, fam'.siteAt bPos with
        | some q, some q' =>
            if pairBits q q' mask then some (advancePair a1 b0 b1 mask aPos bPos stack) else none
        | _, _ => none
      else none
  | _, _ => none

/-- Replay a chunk of records from a state; the boundary state is explicit so that a stream can
be split into chunks. -/
def safetyStep (fam fam' : WireFamily) : SafetyState → List SafetyRecord → Option SafetyState
  | state, [] => some state
  | state, record :: rest =>
      match safetyStepOne fam fam' state record with
      | none => none
      | some state' => safetyStep fam fam' state' rest

/-- Chunks chain: replaying a concatenation is replaying the first chunk and then the second. -/
theorem safetyStep_append (fam fam' : WireFamily) (state : SafetyState)
    (first second : List SafetyRecord) :
    safetyStep fam fam' state (first ++ second) =
      (safetyStep fam fam' state first).bind fun state' => safetyStep fam fam' state' second := by
  induction first generalizing state with
  | nil => simp [safetyStep]
  | cons record rest ih =>
      simp only [List.cons_append, safetyStep]
      cases safetyStepOne fam fam' state record with
      | none => rfl
      | some state' => exact ih state'

/-- The whole obligation: both families well formed, then the record stream replayed from the
root product `[0, n) × [0, m)` with all nine bits, ending with no pending obligation. -/
def safetyCertCheck (left right : IndexTree SiteWire) (dl dr n m : ℕ) (permL permR : OrdTree)
    (records : List SafetyRecord) : Bool :=
  let fam : WireFamily := ⟨left, dl, permL, n⟩
  let fam' : WireFamily := ⟨right, dr, permR, m⟩
  fam.wellFormed && fam'.wellFormed &&
    match safetyStep fam fam' [.node 0 n 0 m 511] records with
    | some [] => true
    | _ => false

/-! ## Soundness -/

/-- The sites at two positions are cross-safe at the lift decoded from bit `i`. -/
def PairSafe (fam fam' : WireFamily) (p q i : ℕ) : Prop :=
  ∀ w w' : SiteWire, fam.siteAt p = some w → fam'.siteAt q = some w' →
    CrossSafe (closedDisk w.toSite) (closedDisk (shiftSite w'.toSite (checkLift i)))

/-- The pairs from `(aPos, bPos)` onwards in left-major order over `[·, a1) × [b0, b1)`. -/
def PairRemaining (a1 b0 b1 aPos bPos p q : ℕ) : Prop :=
  (p = aPos ∧ bPos ≤ q ∧ q < b1) ∨ (aPos < p ∧ p < a1 ∧ b0 ≤ q ∧ q < b1)

/-- Every position pair and mask bit of a pending obligation is certified. -/
def SafetyTask.Safe (fam fam' : WireFamily) : SafetyTask → Prop
  | .node a0 a1 b0 b1 mask =>
      ∀ p q, a0 ≤ p → p < a1 → b0 ≤ q → q < b1 → ∀ i, i < 9 → mask.testBit i = true →
        PairSafe fam fam' p q i
  | .pair a1 b0 b1 mask aPos bPos =>
      ∀ p q, PairRemaining a1 b0 b1 aPos bPos p q → ∀ i, i < 9 → mask.testBit i = true →
        PairSafe fam fam' p q i

/-- A bit of the residual is an incoming bit that is not pruned. -/
theorem residualMask_testBit (inMask pruned i : ℕ) :
    (residualMask inMask pruned).testBit i = (inMask.testBit i && !pruned.testBit i) := by
  simp only [residualMask, Nat.testBit_xor, Nat.testBit_and]
  cases inMask.testBit i <;> cases pruned.testBit i <;> rfl

/-- A passing block bit list passes the block test at every set bit. -/
theorem blockBits_sound (boxA boxB : NodeBox) (mask : ℕ) (pass : blockBits boxA boxB mask = true)
    (i : ℕ) (lt : i < 9) (bit : mask.testBit i = true) :
    blockCheck boxA boxB (checkLift i).1 (checkLift i).2 = true := by
  simp only [blockBits, liftIndices, List.all_eq_true, List.mem_range] at pass
  have := pass i lt
  rwa [bit, Bool.not_true, Bool.false_or] at this

/-- A passing pair bit list passes the exact pair test at every set bit. -/
theorem pairBits_sound (q q' : SiteWire) (mask : ℕ) (pass : pairBits q q' mask = true)
    (i : ℕ) (lt : i < 9) (bit : mask.testBit i = true) :
    pairCheck q q' (checkLift i).1 (checkLift i).2 = true := by
  simp only [pairBits, liftIndices, List.all_eq_true, List.mem_range] at pass
  have := pass i lt
  rwa [bit, Bool.not_true, Bool.false_or] at this

/-- A pruned bit of a node certifies every position pair of its product. -/
theorem blockBits_pairSafe (fam fam' : WireFamily)
    (famValid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (fam'Valid : ∀ w ∈ fam'.sites.toList, w.valid = true) (a0 a1 b0 b1 : ℕ) (boxA boxB : NodeBox)
    (boxAEq : fam.rangeBox a0 a1 = some boxA) (boxBEq : fam'.rangeBox b0 b1 = some boxB)
    (pruned : ℕ) (pass : blockBits boxA boxB pruned = true) (p q : ℕ) (a0p : a0 ≤ p) (pa1 : p < a1)
    (b0q : b0 ≤ q) (qb1 : q < b1) (i : ℕ) (lt : i < 9) (bit : pruned.testBit i = true) :
    PairSafe fam fam' p q i := by
  intro w w' wEq w'Eq
  have wValid := famValid w (fam.siteAt_mem p w wEq)
  have w'Valid := fam'Valid w' (fam'.siteAt_mem q w' w'Eq)
  have check := blockBits_sound boxA boxB pruned pass i lt bit
  have encloseA := fam.rangeBox_encloses a0 a1 boxA boxAEq p a0p pa1 w wEq wValid
  have encloseB := fam'.rangeBox_encloses b0 b1 boxB boxBEq q b0q qb1 w' w'Eq w'Valid
  obtain ⟨u, v, liftEq⟩ : ∃ u v, checkLift i = (u, v) := ⟨_, _, rfl⟩
  rw [liftEq] at check ⊢
  exact blockCheck_sound boxA boxB u v w.toSite w'.toSite (w.valid_toSite wValid)
    (w'.valid_toSite w'Valid) encloseA encloseB check

/-- A passing pair record certifies its pair at every bit of its mask. -/
theorem pairBits_pairSafe (fam fam' : WireFamily)
    (famValid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (fam'Valid : ∀ w ∈ fam'.sites.toList, w.valid = true) (p q : ℕ) (w w' : SiteWire)
    (wEq : fam.siteAt p = some w) (w'Eq : fam'.siteAt q = some w') (mask : ℕ)
    (pass : pairBits w w' mask = true) (i : ℕ) (lt : i < 9) (bit : mask.testBit i = true) :
    PairSafe fam fam' p q i := by
  intro w₀ w₀' w₀Eq w₀'Eq
  rw [wEq] at w₀Eq
  rw [w'Eq] at w₀'Eq
  cases w₀Eq
  cases w₀'Eq
  exact pairCheck_sound _ _ (checkLift i) (famValid _ (fam.siteAt_mem p _ wEq))
    (fam'Valid _ (fam'.siteAt_mem q _ w'Eq)) (pairBits_sound _ _ mask pass i lt bit)

/-- Advancing keeps the rest of the stack. -/
theorem advancePair_mem (a1 b0 b1 mask aPos bPos : ℕ) (stack : SafetyState) (task : SafetyTask)
    (mem : task ∈ stack) : task ∈ advancePair a1 b0 b1 mask aPos bPos stack := by
  unfold advancePair
  split
  · exact List.mem_cons.2 (Or.inr mem)
  · split
    · exact List.mem_cons.2 (Or.inr mem)
    · exact mem

/-- A remaining pair is the current pair or remains after advancing. -/
theorem advancePair_remaining (a1 b0 b1 mask aPos bPos p q : ℕ) (stack : SafetyState)
    (remaining : PairRemaining a1 b0 b1 aPos bPos p q) :
    (p = aPos ∧ q = bPos) ∨ ∃ aNext bNext,
      SafetyTask.pair a1 b0 b1 mask aNext bNext ∈ advancePair a1 b0 b1 mask aPos bPos stack ∧
        PairRemaining a1 b0 b1 aNext bNext p q := by
  unfold PairRemaining at remaining
  unfold advancePair
  split
  · by_cases current : p = aPos ∧ q = bPos
    · exact Or.inl current
    · exact Or.inr ⟨aPos, bPos + 1, List.mem_cons.2 (Or.inl rfl), by unfold PairRemaining; omega⟩
  · split
    · by_cases current : p = aPos ∧ q = bPos
      · exact Or.inl current
      · exact Or.inr ⟨aPos + 1, b0, List.mem_cons.2 (Or.inl rfl), by unfold PairRemaining; omega⟩
    · exact Or.inl (by omega)

/-- A checked node continuation certifies the residual bits of its product and keeps the stack. -/
theorem nodeContinue_sound (fam fam' : WireFamily) (a0 a1 b0 b1 residual kind cut : ℕ)
    (stack state' : SafetyState)
    (continued : nodeContinue a0 a1 b0 b1 residual kind cut stack = some state')
    (safe' : ∀ task ∈ state', task.Safe fam fam') :
    (∀ task ∈ stack, task.Safe fam fam') ∧
      ∀ p q, a0 ≤ p → p < a1 → b0 ≤ q → q < b1 → ∀ i, i < 9 → residual.testBit i = true →
        PairSafe fam fam' p q i := by
  rcases kind with _ | _ | _ | _ | kind
  · simp only [nodeContinue] at continued
    split at continued
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      simp only [Option.some.injEq] at continued
      subst continued
      refine ⟨safe', fun p q _ _ _ _ i _ bit => ?_⟩
      rw [cond.1, Nat.zero_testBit] at bit
      exact absurd bit Bool.false_ne_true
    · simp at continued
  · simp only [nodeContinue] at continued
    split at continued
    · simp only [Option.some.injEq] at continued
      subst continued
      refine ⟨fun task mem => safe' task (List.mem_cons.2 (Or.inr mem)),
        fun p q a0p pa1 b0q qb1 i lt bit => ?_⟩
      exact safe' (.pair a1 b0 b1 residual a0 b0) (List.mem_cons.2 (Or.inl rfl)) p q
        (by unfold PairRemaining; omega) i lt bit
    · simp at continued
  · simp only [nodeContinue] at continued
    split at continued
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      simp only [Option.some.injEq] at continued
      subst continued
      refine ⟨fun task mem => safe' task (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr mem)))),
        fun p q a0p pa1 b0q qb1 i lt bit => ?_⟩
      by_cases pCut : p < cut
      · exact safe' (.node a0 cut b0 b1 residual) (List.mem_cons.2 (Or.inl rfl)) p q a0p pCut b0q
          qb1 i lt bit
      · exact safe' (.node cut a1 b0 b1 residual)
          (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
          p q (by omega) pa1 b0q qb1 i lt bit
    · simp at continued
  · simp only [nodeContinue] at continued
    split at continued
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      simp only [Option.some.injEq] at continued
      subst continued
      refine ⟨fun task mem => safe' task (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr mem)))),
        fun p q a0p pa1 b0q qb1 i lt bit => ?_⟩
      by_cases qCut : q < cut
      · exact safe' (.node a0 a1 b0 cut residual) (List.mem_cons.2 (Or.inl rfl)) p q a0p pa1 b0q
          qCut i lt bit
      · exact safe' (.node a0 a1 cut b1 residual)
          (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
          p q a0p pa1 (by omega) qb1 i lt bit
    · simp at continued
  · simp [nodeContinue] at continued

/-- One replayed record certifies the top obligation, given the obligations it leaves behind. -/
theorem safetyStepOne_sound (fam fam' : WireFamily)
    (famValid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (fam'Valid : ∀ w ∈ fam'.sites.toList, w.valid = true) (state : SafetyState)
    (record : SafetyRecord) (state' : SafetyState)
    (step : safetyStepOne fam fam' state record = some state')
    (safe' : ∀ task ∈ state', task.Safe fam fam') : ∀ task ∈ state, task.Safe fam fam' := by
  cases state with
  | nil => cases record <;> simp [safetyStepOne] at step
  | cons top stack =>
    cases top with
    | node a0 a1 b0 b1 mask =>
      cases record with
      | pair _ _ _ => simp [safetyStepOne] at step
      | node a0' a1' b0' b1' inMask pruned kind cut =>
        simp only [safetyStepOne] at step
        split at step
        · revert step
          rcases boxAEq : fam.rangeBox a0 a1 with _ | boxA <;>
            rcases boxBEq : fam'.rangeBox b0 b1 with _ | boxB <;> intro step
          · simp at step
          · simp at step
          · simp at step
          · dsimp only at step
            split at step
            · rename_i blocks
              obtain ⟨stackSafe, residualSafe⟩ :=
                nodeContinue_sound fam fam' a0 a1 b0 b1 (residualMask mask pruned) kind cut stack
                  state' step safe'
              intro task mem
              rcases List.mem_cons.1 mem with rfl | mem
              · intro p q a0p pa1 b0q qb1 i lt bit
                by_cases prunedBit : pruned.testBit i = true
                · exact blockBits_pairSafe fam fam' famValid fam'Valid a0 a1 b0 b1 boxA boxB boxAEq
                    boxBEq pruned blocks p q a0p pa1 b0q qb1 i lt prunedBit
                · simp only [Bool.not_eq_true] at prunedBit
                  refine residualSafe p q a0p pa1 b0q qb1 i lt ?_
                  rw [residualMask_testBit, bit, prunedBit]
                  rfl
              · exact stackSafe task mem
            · simp at step
        · simp at step
    | pair a1 b0 b1 mask aPos bPos =>
      cases record with
      | node _ _ _ _ _ _ _ _ => simp [safetyStepOne] at step
      | pair aPos' bPos' mask' =>
        simp only [safetyStepOne] at step
        split at step
        · revert step
          rcases wEq : fam.siteAt aPos with _ | w <;>
            rcases w'Eq : fam'.siteAt bPos with _ | w' <;> intro step
          · simp at step
          · simp at step
          · simp at step
          · dsimp only at step
            split at step
            · rename_i bits
              simp only [Option.some.injEq] at step
              subst step
              intro task mem
              rcases List.mem_cons.1 mem with rfl | mem
              · intro p q remaining i lt bit
                rcases advancePair_remaining a1 b0 b1 mask aPos bPos p q stack remaining with
                  ⟨rfl, rfl⟩ | ⟨aNext, bNext, memNext, remainingNext⟩
                · exact pairBits_pairSafe fam fam' famValid fam'Valid _ _ w w' wEq w'Eq mask bits
                    i lt bit
                · exact safe' _ memNext p q remainingNext i lt bit
              · exact safe' task (advancePair_mem a1 b0 b1 mask aPos bPos stack task mem)
            · simp at step
        · simp at step

/-- A replay that ends with no pending obligation certifies every obligation it started from. -/
theorem safetyStep_sound (fam fam' : WireFamily)
    (famValid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (fam'Valid : ∀ w ∈ fam'.sites.toList, w.valid = true) (records : List SafetyRecord) :
    ∀ state : SafetyState, safetyStep fam fam' state records = some [] →
      ∀ task ∈ state, task.Safe fam fam' := by
  induction records with
  | nil =>
      intro state run
      simp only [safetyStep, Option.some.injEq] at run
      subst run
      simp
  | cons record rest ih =>
      intro state run
      simp only [safetyStep] at run
      revert run
      rcases step : safetyStepOne fam fam' state record with _ | state' <;> intro run
      · simp at run
      · exact safetyStepOne_sound fam fam' famValid fam'Valid state record state' step
          (ih state' run)

/-- A passing certificate makes every site of the left tree cross-safe against every site of the
right tree at all nine relative lifts; both trees must hold valid wires. -/
theorem safetyCertCheck_sound (left right : IndexTree SiteWire) (dl dr n m : ℕ)
    (permL permR : OrdTree) (records : List SafetyRecord)
    (leftValid : ∀ w ∈ left.toList, w.valid = true)
    (rightValid : ∀ w ∈ right.toList, w.valid = true)
    (pass : safetyCertCheck left right dl dr n m permL permR records = true) :
    ∀ q ∈ wireSet left.toList, ∀ q' ∈ wireSet right.toList, ∀ lift : ℤ × ℤ, NineLift lift →
      CrossSafe (closedDisk q) (closedDisk (shiftSite q' lift)) := by
  simp only [safetyCertCheck, Bool.and_eq_true] at pass
  obtain ⟨⟨wellL, wellR⟩, run⟩ := pass
  have runEq : safetyStep ⟨left, dl, permL, n⟩ ⟨right, dr, permR, m⟩ [.node 0 n 0 m 511] records =
      some [] := by
    revert run
    cases safetyStep ⟨left, dl, permL, n⟩ ⟨right, dr, permR, m⟩ [.node 0 n 0 m 511] records with
    | none => intro run; simp at run
    | some state =>
        cases state with
        | nil => intro _; rfl
        | cons task rest => intro run; simp at run
  have rootSafe := safetyStep_sound ⟨left, dl, permL, n⟩ ⟨right, dr, permR, m⟩ leftValid rightValid
    records [.node 0 n 0 m 511] runEq (.node 0 n 0 m 511) (List.mem_cons.2 (Or.inl rfl))
  have allBits : ∀ i, i < 9 → Nat.testBit 511 i = true := by decide
  rintro q ⟨w, wMem, rfl⟩ q' ⟨w', w'Mem, rfl⟩ lift nine
  obtain ⟨p, pLt, wEq⟩ := WireFamily.wellFormed_siteAt ⟨left, dl, permL, n⟩ wellL w wMem
  obtain ⟨p', p'Lt, w'Eq⟩ := WireFamily.wellFormed_siteAt ⟨right, dr, permR, m⟩ wellR w' w'Mem
  obtain ⟨i, iLt, liftEq⟩ := exists_checkLift lift nine
  rw [← liftEq]
  exact rootSafe p p' (Nat.zero_le p) pLt (Nat.zero_le p') p'Lt i iLt (allBits i iLt) w w' wEq w'Eq

/-- Cross-safety of the two periodic unions from a passing certificate. -/
theorem crossSafe_U_of_safetyCert (left right : IndexTree SiteWire) (dl dr n m : ℕ)
    (permL permR : OrdTree) (records : List SafetyRecord)
    (leftValid : ∀ w ∈ left.toList, w.valid = true)
    (rightValid : ∀ w ∈ right.toList, w.valid = true)
    (pass : safetyCertCheck left right dl dr n m permL permR records = true) :
    CrossSafe (U (wireSet left.toList)) (U (wireSet right.toList)) :=
  crossSafe_U_of_nine_lifts (wireSet left.toList) (wireSet right.toList)
    (wireSet_valid left.toList leftValid) (wireSet_valid right.toList rightValid)
    (safetyCertCheck_sound left right dl dr n m permL permR records leftValid rightValid pass)

/-- Unit independence of one periodic union from a passing self-product certificate. -/
theorem unitIndependent_U_of_safetyCert (sites : IndexTree SiteWire) (depth n : ℕ) (perm : OrdTree)
    (records : List SafetyRecord) (valid : ∀ w ∈ sites.toList, w.valid = true)
    (pass : safetyCertCheck sites sites depth depth n n perm perm records = true) :
    UnitIndependent (U (wireSet sites.toList)) :=
  unitIndependent_U_of_nine_lifts (wireSet sites.toList) (wireSet_valid sites.toList valid)
    (safetyCertCheck_sound sites sites depth depth n n perm perm records valid valid pass)

/-! ## Examples

Two sites, `(1, 1)` and `(30, 30)` with radius `1 / 10`, in one tree of depth one with the
identity permutation. Every site pair passes the exact test at all nine lifts; the root box pair
prunes every lift but `(0, 0)` (mask `495 = 511 - 16`), and every singleton box pair prunes all
nine bits. -/

/-- The site at ordinal `0`. -/
def exampleSiteA : SiteWire := ⟨1, 1, 1, 1, 1, 10⟩

/-- The site at ordinal `1`. -/
def exampleSiteB : SiteWire := ⟨30, 1, 30, 1, 1, 10⟩

/-- The depth-one site tree. -/
def exampleSites : IndexTree SiteWire := .node (.leaf exampleSiteA) (.leaf exampleSiteB)

/-- The identity permutation on two positions. -/
def examplePerm : OrdTree := .node (.leaf 0) (.leaf 1)

/-- The example family. -/
def exampleFamily : WireFamily := ⟨exampleSites, 1, examplePerm, 2⟩

/-- A root split, a kind-1 child with two pairs, and a kind-3 child with two kind-0 leaves. -/
def exampleRecords : List SafetyRecord :=
  [.node 0 2 0 2 511 495 2 1, .node 0 1 0 2 16 0 1 0, .pair 0 0 16, .pair 0 1 16,
    .node 1 2 0 2 16 0 3 1, .node 1 2 0 1 16 16 0 0, .node 1 2 1 2 16 16 0 0]

/-- Position lookup descends by the top bit. -/
example : examplePerm.get? 1 1 = some 1 := by decide

/-- A position beyond the depth is absent. -/
example : examplePerm.get? 1 2 = none := by decide

/-- The identity is a bijection; a constant map is not. -/
example : permBijection examplePerm 1 2 = true := by decide
example : permBijection (.node (.leaf 0) (.leaf 0)) 1 2 = false := by decide

/-- The tree certificate is accepted. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm examplePerm exampleRecords =
    true := by
  decide

/-- A flat certificate: the root itself is a kind-1 node with four pairs. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm examplePerm
    [.node 0 2 0 2 511 495 1 0, .pair 0 0 16, .pair 0 1 16, .pair 1 0 16, .pair 1 1 16] = true := by
  decide

/-- The same stream in two chunks through the explicit boundary state. -/
example : safetyStep exampleFamily exampleFamily [.node 0 2 0 2 511] (exampleRecords.take 2) =
    some [.pair 1 0 2 16 0 0, .node 1 2 0 2 16] := by
  decide
example : safetyStep exampleFamily exampleFamily [.pair 1 0 2 16 0 0, .node 1 2 0 2 16]
    (exampleRecords.drop 2) = some [] := by
  decide

/-- A missing pair record leaves an open obligation. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm examplePerm
    [.node 0 2 0 2 511 495 1 0, .pair 0 0 16, .pair 0 1 16, .pair 1 0 16] = false := by
  decide

/-- A child whose incoming mask is not the parent's residual is rejected. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm examplePerm
    [.node 0 2 0 2 511 495 2 1, .node 0 1 0 2 17 0 1 0, .pair 0 0 17, .pair 0 1 17,
      .node 1 2 0 2 16 0 3 1, .node 1 2 0 1 16 16 0 0, .node 1 2 1 2 16 16 0 0] = false := by
  decide

/-- A split cut outside the open range is rejected. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm examplePerm
    [.node 0 2 0 2 511 495 2 2, .node 0 2 0 2 16 0 1 0, .pair 0 0 16, .pair 0 1 16, .pair 1 0 16,
      .pair 1 1 16] = false := by
  decide

/-- Pruning the lift `(0, 0)` at the root fails its block test. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm examplePerm
    [.node 0 2 0 2 511 511 0 0] = false := by
  decide

/-- A permutation that is not a bijection is rejected before any replay. -/
example : safetyCertCheck exampleSites exampleSites 1 1 2 2 examplePerm (.node (.leaf 0) (.leaf 0))
    exampleRecords = false := by
  decide

end Erdos188.UpperBound
