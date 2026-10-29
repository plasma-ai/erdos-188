module

public import Erdos188.UpperBound.SafetyData

/-!
# Chunked evidence and a fast replay for the safety checker

What the generated data layer needs to feed `SafetyData` in kernel-sized
pieces without changing that module. Chaining lemmas split a record stream
into chunks. Range boxes of large intervals are recovered from the boxes of
their halves. A permutation is shown surjective onto the family ordinals
through an explicit inverse tree in position chunks (the mark tree of
`permBijection` is too costly for the kernel on the real families). A fast
replay `safetyStepFast` reads every node box from a laminar interval tree of
claimed boxes (`BoxTree`), whose minimal intervals the kernel recomputes and
whose split intervals it checks as one union of the two children, and looks
sites up through the raw recursor with Boolean comparisons.

The fast replay is sound in one direction only: `safetyStepFast_sound` turns
every accepted fast replay into the same accepted run of the trusted checker
`safetyStep`, so every consumed statement is about the original checker. No
converse is stated or needed; a rejected fast replay proves nothing. The
assembly of `safetyStep_sound` with the shape and validity results of
`RoutesData` gives cross-safety and unit independence of the periodic unions.
No finite family or certificate appears here.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

-- Precomputed boxes are compared field by field by `decide`.
deriving instance DecidableEq for NodeBox

/-! ## Chaining chunks -/

/-- Two consecutive passing chunks pass as one chunk. -/
theorem safetyStep_chain {fam fam' : WireFamily} {state middle final : SafetyState}
    {first second : List SafetyRecord} (firstRun : safetyStep fam fam' state first = some middle)
    (secondRun : safetyStep fam fam' middle second = some final) :
    safetyStep fam fam' state (first ++ second) = some final := by
  rw [safetyStep_append, firstRun]
  exact secondRun

/-! ## Range boxes from halves -/

/-- The box union is associative. -/
theorem NodeBox.union_assoc (box other third : NodeBox) :
    (box.union other).union third = box.union (other.union third) := by
  simp only [NodeBox.union, min_assoc, max_assoc]

/-- Folding a sum of counts folds the first count and then the second from its result. -/
theorem WireFamily.rangeBoxAux_add (fam : WireFamily) (first : ℕ) :
    ∀ (start second : ℕ) (box : NodeBox), fam.rangeBoxAux start (first + second) box =
      (fam.rangeBoxAux start first box).bind fun box' => fam.rangeBoxAux (start + first) second box' := by
  induction first with
  | zero => intro start second box; simp [WireFamily.rangeBoxAux]
  | succ first ih =>
      intro start second box
      have shift : first + 1 + second = first + second + 1 := by omega
      rw [shift]
      simp only [WireFamily.rangeBoxAux]
      cases fam.siteAt start with
      | none => rfl
      | some w =>
          dsimp only
          rw [ih (start + 1) second]
          have shift' : start + 1 + first = start + (first + 1) := by omega
          rw [shift']

/-- Folding from a union accumulates around the first box. -/
theorem WireFamily.rangeBoxAux_union (fam : WireFamily) (count : ℕ) :
    ∀ (start : ℕ) (box other : NodeBox), fam.rangeBoxAux start count (box.union other) =
      (fam.rangeBoxAux start count other).map box.union := by
  induction count with
  | zero => intro start box other; simp [WireFamily.rangeBoxAux]
  | succ count ih =>
      intro start box other
      simp only [WireFamily.rangeBoxAux]
      cases fam.siteAt start with
      | none => rfl
      | some w =>
          dsimp only
          rw [NodeBox.union_assoc, ih]

/-- The box of a range splits at any interior position into the union of the two half boxes. -/
theorem WireFamily.rangeBox_split (fam : WireFamily) (lo mid hi : ℕ) (loLt : lo < mid)
    (midLt : mid < hi) : fam.rangeBox lo hi =
      (fam.rangeBox lo mid).bind fun box => (fam.rangeBox mid hi).map box.union := by
  simp only [WireFamily.rangeBox]
  cases fam.siteAt lo with
  | none => rfl
  | some w =>
      simp only [ite_eq_left (lt_trans loLt midLt), ite_eq_left loLt]
      have counts : hi - (lo + 1) = (mid - (lo + 1)) + (hi - mid) := by omega
      rw [counts, fam.rangeBoxAux_add]
      have startEq : lo + 1 + (mid - (lo + 1)) = mid := by omega
      rw [startEq]
      cases fam.rangeBoxAux (lo + 1) (mid - (lo + 1)) (siteBox w) with
      | none => rfl
      | some box =>
          simp only [Option.bind_some]
          have step : hi - mid = (hi - (mid + 1)) + 1 := by omega
          rw [step]
          simp only [WireFamily.rangeBoxAux]
          cases fam.siteAt mid with
          | none => rfl
          | some w' =>
              simp only [ite_eq_left midLt, fam.rangeBoxAux_union]

/-- A range box from the recomputed boxes of its two halves. -/
theorem rangeBox_of_split (fam : WireFamily) (lo mid hi : ℕ) (loLt : lo < mid) (midLt : mid < hi)
    {left right : NodeBox} (leftEq : fam.rangeBox lo mid = some left)
    (rightEq : fam.rangeBox mid hi = some right) : fam.rangeBox lo hi = some (left.union right) := by
  rw [fam.rangeBox_split lo mid hi loLt midLt, leftEq, rightEq]
  rfl

/-! ## Surjectivity of a permutation through an inverse tree -/

/-- Every ordinal of `[lo, lo + len)` is, through `inv`, the image of a position below `n`. -/
def surjCheck (perm inv : OrdTree) (depth n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, len + 1 =>
      (match inv.get? depth lo with
        | none => false
        | some p => decide (p < n) && decide (perm.get? depth p = some lo)) &&
        surjCheck perm inv depth n (lo + 1) len

/-- A passing range check hits every ordinal of its range from a position below `n`. -/
theorem surjCheck_sound (perm inv : OrdTree) (depth n : ℕ) (len : ℕ) :
    ∀ lo, surjCheck perm inv depth n lo len = true →
      ∀ o, lo ≤ o → o < lo + len → ∃ p, p < n ∧ perm.get? depth p = some o := by
  induction len with
  | zero => intro lo _ o loLe oLt; omega
  | succ len ih =>
      intro lo pass o loLe oLt
      simp only [surjCheck, Bool.and_eq_true] at pass
      obtain ⟨first, rest⟩ := pass
      by_cases oEq : o = lo
      · rw [oEq]
        revert first
        cases inv.get? depth lo with
        | none => intro first; simp at first
        | some p =>
            intro first
            simp only [Bool.and_eq_true, decide_eq_true_eq] at first
            exact ⟨p, first.1, first.2⟩
      · exact ih (lo + 1) rest o (by omega) (by omega)

/-- Two consecutive passing ranges pass as one range. -/
theorem surjCheck_chain {perm inv : OrdTree} {depth n lo first second : ℕ}
    (firstPass : surjCheck perm inv depth n lo first = true)
    (secondPass : surjCheck perm inv depth n (lo + first) second = true) :
    surjCheck perm inv depth n lo (first + second) = true := by
  induction first generalizing lo with
  | zero =>
      rw [Nat.add_zero] at secondPass
      rw [Nat.zero_add]
      exact secondPass
  | succ first ih =>
      simp only [surjCheck, Bool.and_eq_true] at firstPass
      have shift : first + 1 + second = first + second + 1 := by omega
      rw [shift]
      simp only [surjCheck, Bool.and_eq_true]
      refine ⟨firstPass.1, ih firstPass.2 ?_⟩
      have shift' : lo + 1 + first = lo + (first + 1) := by omega
      rw [shift']
      exact secondPass

/-- The whole-range form consumed by the soundness assembly. -/
theorem surjCheck_sound_all {perm inv : OrdTree} {depth n : ℕ}
    (pass : surjCheck perm inv depth n 0 n = true) :
    ∀ o, o < n → ∃ p, p < n ∧ perm.get? depth p = some o :=
  fun o oLt => surjCheck_sound perm inv depth n n 0 pass o (Nat.zero_le o) (by omega)

/-! ## Fast lookups

`IndexTree.get?` reaches the kernel through its `brecOn` and matcher compilation, and most of a
replay is spent unfolding that machinery. The recursor form below descends with Boolean
comparisons and is proved equal to `get?`, so the fast replay may use it while every consumed
statement stays about `get?`. -/

/-- Position lookup through the raw recursor with Boolean comparisons. -/
noncomputable def IndexTree.getFast {α : Type} (tree : IndexTree α) : ℕ → ℕ → Option α :=
  IndexTree.rec (motive := fun _ => ℕ → ℕ → Option α)
    (fun _ _ => none)
    (fun value depth p => bif Nat.beq depth 0 && Nat.beq p 0 then some value else none)
    (fun _ _ leftGet rightGet depth p =>
      Nat.casesOn (motive := fun _ => Option α) depth none fun k =>
        bif Nat.blt p (2 ^ k) then leftGet k p else rightGet k (p - 2 ^ k))
    tree

/-- The node step of the fast lookup. -/
theorem IndexTree.getFast_node {α : Type} (left right : IndexTree α) (depth p : ℕ) :
    (IndexTree.node left right).getFast (depth + 1) p =
      bif Nat.blt p (2 ^ depth) then left.getFast depth p else right.getFast depth (p - 2 ^ depth) :=
  rfl

/-- The fast lookup is the position lookup. -/
theorem IndexTree.getFast_eq {α : Type} (tree : IndexTree α) :
    ∀ depth p, tree.getFast depth p = tree.get? depth p := by
  induction tree with
  | empty => intro depth p; rfl
  | leaf value =>
      intro depth p
      cases depth with
      | zero => cases p <;> rfl
      | succ depth => rfl
  | node left right leftIH rightIH =>
      intro depth p
      cases depth with
      | zero => rfl
      | succ depth =>
          rw [IndexTree.getFast_node, leftIH, rightIH]
          simp only [IndexTree.get?, cond_eq_ite, Nat.blt_eq]

/-- The site at a position through the fast lookups. -/
noncomputable def WireFamily.siteAtFast (fam : WireFamily) (p : ℕ) : Option SiteWire :=
  match fam.perm.getFast fam.depth p with
  | none => none
  | some ordinal => fam.sites.getFast fam.depth ordinal

/-- The fast site lookup is `siteAt`. -/
theorem WireFamily.siteAtFast_eq (fam : WireFamily) (p : ℕ) : fam.siteAtFast p = fam.siteAt p := by
  simp only [WireFamily.siteAtFast, WireFamily.siteAt, IndexTree.getFast_eq]
  cases fam.perm.get? fam.depth p <;> rfl

/-- The box fold through the fast lookups. -/
noncomputable def WireFamily.rangeBoxAuxFast (fam : WireFamily) : ℕ → ℕ → NodeBox → Option NodeBox
  | _, 0, box => some box
  | start, count + 1, box =>
      match fam.siteAtFast start with
      | none => none
      | some w => fam.rangeBoxAuxFast (start + 1) count (box.union (siteBox w))

/-- The fast fold is `rangeBoxAux`. -/
theorem WireFamily.rangeBoxAuxFast_eq (fam : WireFamily) (count : ℕ) :
    ∀ start box, fam.rangeBoxAuxFast start count box = fam.rangeBoxAux start count box := by
  induction count with
  | zero => intro start box; rfl
  | succ count ih =>
      intro start box
      simp only [WireFamily.rangeBoxAuxFast, WireFamily.rangeBoxAux, WireFamily.siteAtFast_eq]
      cases fam.siteAt start with
      | none => rfl
      | some w =>
          dsimp only
          exact ih (start + 1) (box.union (siteBox w))

/-- The range box through the fast lookups. -/
noncomputable def WireFamily.rangeBoxFast (fam : WireFamily) (lo hi : ℕ) : Option NodeBox :=
  match fam.siteAtFast lo with
  | none => none
  | some w => if lo < hi then fam.rangeBoxAuxFast (lo + 1) (hi - (lo + 1)) (siteBox w) else none

/-- The fast range box is `rangeBox`. -/
theorem WireFamily.rangeBoxFast_eq (fam : WireFamily) (lo hi : ℕ) :
    fam.rangeBoxFast lo hi = fam.rangeBox lo hi := by
  simp only [WireFamily.rangeBoxFast, WireFamily.rangeBox, WireFamily.siteAtFast_eq,
    WireFamily.rangeBoxAuxFast_eq]
  cases fam.siteAt lo <;> rfl

/-! ## Interval trees of claimed boxes

The node ranges of one side of a certificate form a laminar family: every range is the root
`[0, count)` or one half of a split range. A `BoxTree` stores that family with a claimed box per
interval. The kernel checks a minimal interval by recomputation and a split interval as the
union of its two children, and the lookup by interval ends finds the box of any stored range in
one descent, so a replay never recomputes a box over the members of a range. -/

/-- A laminar tree of position intervals with a claimed range box per interval. -/
inductive BoxTree where
  /-- A minimal interval `[lo, hi)` with its claimed box. -/
  | leaf (lo hi : ℕ) (box : NodeBox)
  /-- The interval `[lo, hi)` split at `mid` into the two subtrees, with its claimed box. -/
  | split (lo mid hi : ℕ) (box : NodeBox) (left right : BoxTree)

/-- The lower end of the root interval. -/
def BoxTree.lo : BoxTree → ℕ
  | .leaf lo _ _ => lo
  | .split lo _ _ _ _ _ => lo

/-- The upper end of the root interval. -/
def BoxTree.hi : BoxTree → ℕ
  | .leaf _ hi _ => hi
  | .split _ _ hi _ _ _ => hi

/-- The claimed box of the root interval. -/
def BoxTree.box : BoxTree → NodeBox
  | .leaf _ _ box => box
  | .split _ _ _ box _ _ => box

/-- The local conditions of a split: the children cover `[lo, mid)` and `[mid, hi)` with
`lo < mid < hi`, and the claimed box is the union of their claimed boxes. -/
def BoxTree.splitOk (lo mid hi : ℕ) (box : NodeBox) (left right : BoxTree) : Bool :=
  decide (left.lo = lo) && decide (left.hi = mid) && decide (right.lo = mid) &&
    decide (right.hi = hi) && decide (lo < mid) && decide (mid < hi) &&
      decide (box = left.box.union right.box)

/-- Every claimed box is the recomputed box of its interval: minimal intervals by recomputation,
split intervals through their children. -/
noncomputable def BoxTree.check (fam : WireFamily) : BoxTree → Bool
  | .leaf lo hi box => decide (fam.rangeBoxFast lo hi = some box)
  | .split lo mid hi box left right =>
      BoxTree.splitOk lo mid hi box left right && left.check fam && right.check fam

/-- A split passes from its local conditions and its two children. -/
theorem BoxTree.check_split_of {fam : WireFamily} {lo mid hi : ℕ} {box : NodeBox}
    {left right : BoxTree} (ok : BoxTree.splitOk lo mid hi box left right = true)
    (leftPass : left.check fam = true) (rightPass : right.check fam = true) :
    (BoxTree.split lo mid hi box left right).check fam = true := by
  simp only [BoxTree.check, ok, leftPass, rightPass, Bool.and_self]

/-- The claimed box of the interval `[a0, a1)`, by descending to the subtree containing it. -/
noncomputable def BoxTree.lookup (tree : BoxTree) : ℕ → ℕ → Option NodeBox :=
  BoxTree.rec (motive := fun _ => ℕ → ℕ → Option NodeBox)
    (fun lo hi box a0 a1 => bif Nat.beq a0 lo && Nat.beq a1 hi then some box else none)
    (fun lo mid hi box _ _ leftLookup rightLookup a0 a1 =>
      bif Nat.beq a0 lo && Nat.beq a1 hi then some box
      else bif Nat.ble a1 mid then leftLookup a0 a1
      else bif Nat.ble mid a0 then rightLookup a0 a1
      else none)
    tree

/-- The leaf step of the lookup. -/
theorem BoxTree.lookup_leaf (lo hi : ℕ) (box : NodeBox) (a0 a1 : ℕ) :
    (BoxTree.leaf lo hi box).lookup a0 a1 =
      bif Nat.beq a0 lo && Nat.beq a1 hi then some box else none :=
  rfl

/-- The split step of the lookup. -/
theorem BoxTree.lookup_split (lo mid hi : ℕ) (box : NodeBox) (left right : BoxTree) (a0 a1 : ℕ) :
    (BoxTree.split lo mid hi box left right).lookup a0 a1 =
      (bif Nat.beq a0 lo && Nat.beq a1 hi then some box
      else bif Nat.ble a1 mid then left.lookup a0 a1
      else bif Nat.ble mid a0 then right.lookup a0 a1
      else none) :=
  rfl

/-- The lookup of the root interval is the root box. -/
theorem BoxTree.lookup_root (tree : BoxTree) : tree.lookup tree.lo tree.hi = some tree.box := by
  cases tree with
  | leaf lo hi box => simp [BoxTree.lookup_leaf, BoxTree.lo, BoxTree.hi, BoxTree.box, Nat.beq_refl]
  | split lo mid hi box left right =>
      simp [BoxTree.lookup_split, BoxTree.lo, BoxTree.hi, BoxTree.box, Nat.beq_refl]

/-- In a checked tree, every box found by the lookup is the recomputed box of its interval. -/
theorem BoxTree.lookup_sound (fam : WireFamily) :
    ∀ tree : BoxTree, tree.check fam = true →
      ∀ a0 a1 box, tree.lookup a0 a1 = some box → fam.rangeBox a0 a1 = some box := by
  intro tree
  induction tree with
  | leaf lo hi claimed =>
      intro pass a0 a1 box found
      simp only [BoxTree.check, decide_eq_true_eq, WireFamily.rangeBoxFast_eq] at pass
      rw [BoxTree.lookup_leaf] at found
      revert found
      cases root : (Nat.beq a0 lo && Nat.beq a1 hi) <;> intro found
      · simp at found
      · simp only [Bool.and_eq_true, Nat.beq_eq] at root
        simp only [Bool.cond_true, Option.some.injEq] at found
        rw [root.1, root.2, ← found]
        exact pass
  | split lo mid hi claimed left right leftIH rightIH =>
      intro pass a0 a1 box found
      simp only [BoxTree.check, Bool.and_eq_true] at pass
      obtain ⟨⟨ok, leftPass⟩, rightPass⟩ := pass
      simp only [BoxTree.splitOk, Bool.and_eq_true, decide_eq_true_eq] at ok
      obtain ⟨⟨⟨⟨⟨⟨leftLo, leftHi⟩, rightLo⟩, rightHi⟩, loLt⟩, midLt⟩, boxEq⟩ := ok
      rw [BoxTree.lookup_split] at found
      revert found
      cases root : (Nat.beq a0 lo && Nat.beq a1 hi) <;> intro found
      · simp only [Bool.cond_false] at found
        revert found
        cases inLeft : Nat.ble a1 mid <;> intro found
        · simp only [Bool.cond_false] at found
          revert found
          cases inRight : Nat.ble mid a0 <;> intro found
          · simp at found
          · simp only [Bool.cond_true] at found
            exact rightIH rightPass a0 a1 box found
        · simp only [Bool.cond_true] at found
          exact leftIH leftPass a0 a1 box found
      · simp only [Bool.and_eq_true, Nat.beq_eq] at root
        simp only [Bool.cond_true, Option.some.injEq] at found
        have leftBox := leftIH leftPass left.lo left.hi left.box left.lookup_root
        have rightBox := rightIH rightPass right.lo right.hi right.box right.lookup_root
        rw [leftLo, leftHi] at leftBox
        rw [rightLo, rightHi] at rightBox
        rw [root.1, root.2, ← found, boxEq]
        exact rangeBox_of_split fam lo mid hi loLt midLt leftBox rightBox

/-! ## The fast replay -/

/-- `safetyStepOne` with both node boxes read from the interval trees and sites looked up
through the fast lookups. -/
noncomputable def safetyStepOneFast (fam fam' : WireFamily) (tableA tableB : BoxTree) :
    SafetyState → SafetyRecord → Option SafetyState
  | .node a0 a1 b0 b1 mask :: stack, .node a0' a1' b0' b1' inMask pruned kind cut =>
      if decide (a0 = a0') && decide (a1 = a1') && decide (b0 = b0') && decide (b1 = b1') &&
          decide (inMask = mask) && decide (pruned &&& mask = pruned) then
        match tableA.lookup a0 a1, tableB.lookup b0 b1 with
        | some boxA, some boxB =>
            if blockBits boxA boxB pruned then
              nodeContinue a0 a1 b0 b1 (residualMask mask pruned) kind cut stack
            else none
        | _, _ => none
      else none
  | .pair a1 b0 b1 mask aPos bPos :: stack, .pair aPos' bPos' mask' =>
      if decide (aPos = aPos') && decide (bPos = bPos') && decide (mask = mask') then
        match fam.siteAtFast aPos, fam'.siteAtFast bPos with
        | some q, some q' =>
            if pairBits q q' mask then some (advancePair a1 b0 b1 mask aPos bPos stack) else none
        | _, _ => none
      else none
  | _, _ => none

/-- `safetyStep` through `safetyStepOneFast`. -/
noncomputable def safetyStepFast (fam fam' : WireFamily) (tableA tableB : BoxTree) :
    SafetyState → List SafetyRecord → Option SafetyState
  | state, [] => some state
  | state, record :: rest =>
      match safetyStepOneFast fam fam' tableA tableB state record with
      | none => none
      | some state' => safetyStepFast fam fam' tableA tableB state' rest

/-- Fast chunks chain like `safetyStep_append`. -/
theorem safetyStepFast_append (fam fam' : WireFamily) (tableA tableB : BoxTree)
    (state : SafetyState) (first second : List SafetyRecord) :
    safetyStepFast fam fam' tableA tableB state (first ++ second) =
      (safetyStepFast fam fam' tableA tableB state first).bind fun state' =>
        safetyStepFast fam fam' tableA tableB state' second := by
  induction first generalizing state with
  | nil => simp [safetyStepFast]
  | cons record rest ih =>
      simp only [List.cons_append, safetyStepFast]
      cases safetyStepOneFast fam fam' tableA tableB state record with
      | none => rfl
      | some state' => exact ih state'

/-- Two consecutive passing fast chunks pass as one fast chunk. -/
theorem safetyStepFast_chain {fam fam' : WireFamily} {tableA tableB : BoxTree}
    {state middle final : SafetyState} {first second : List SafetyRecord}
    (firstRun : safetyStepFast fam fam' tableA tableB state first = some middle)
    (secondRun : safetyStepFast fam fam' tableA tableB middle second = some final) :
    safetyStepFast fam fam' tableA tableB state (first ++ second) = some final := by
  rw [safetyStepFast_append, firstRun]
  exact secondRun

/-- One accepted fast step is an accepted step of `safetyStepOne` when both trees are checked. -/
theorem safetyStepOneFast_sound (fam fam' : WireFamily) (tableA tableB : BoxTree)
    (passA : tableA.check fam = true) (passB : tableB.check fam' = true) (state : SafetyState)
    (record : SafetyRecord) (state' : SafetyState)
    (step : safetyStepOneFast fam fam' tableA tableB state record = some state') :
    safetyStepOne fam fam' state record = some state' := by
  cases state with
  | nil => cases record <;> simp [safetyStepOneFast] at step
  | cons top stack =>
    cases top with
    | node a0 a1 b0 b1 mask =>
      cases record with
      | pair _ _ _ => simp [safetyStepOneFast] at step
      | node a0' a1' b0' b1' inMask pruned kind cut =>
        simp only [safetyStepOneFast] at step
        simp only [safetyStepOne]
        split at step
        · rename_i guard
          rw [ite_eq_left guard]
          revert step
          rcases lookA : tableA.lookup a0 a1 with _ | boxA <;>
            rcases lookB : tableB.lookup b0 b1 with _ | boxB <;> intro step
          · simp at step
          · simp at step
          · simp at step
          · rw [BoxTree.lookup_sound fam tableA passA a0 a1 boxA lookA,
              BoxTree.lookup_sound fam' tableB passB b0 b1 boxB lookB]
            exact step
        · simp at step
    | pair a1 b0 b1 mask aPos bPos =>
      cases record with
      | node _ _ _ _ _ _ _ _ => simp [safetyStepOneFast] at step
      | pair aPos' bPos' mask' =>
        simp only [safetyStepOneFast, WireFamily.siteAtFast_eq] at step
        simp only [safetyStepOne]
        exact step

/-- An accepted fast replay is an accepted replay of `safetyStep` when both trees are checked. -/
theorem safetyStepFast_sound (fam fam' : WireFamily) (tableA tableB : BoxTree)
    (passA : tableA.check fam = true) (passB : tableB.check fam' = true)
    (records : List SafetyRecord) :
    ∀ state state' : SafetyState, safetyStepFast fam fam' tableA tableB state records = some state' →
      safetyStep fam fam' state records = some state' := by
  induction records with
  | nil =>
      intro state state' run
      simp only [safetyStepFast, Option.some.injEq] at run
      rw [run]
      rfl
  | cons record rest ih =>
      intro state state' run
      simp only [safetyStepFast] at run
      simp only [safetyStep]
      revert run
      rcases step : safetyStepOneFast fam fam' tableA tableB state record with _ | middle <;>
        intro run
      · simp at run
      · rw [safetyStepOneFast_sound fam fam' tableA tableB passA passB state record middle step]
        exact ih middle state' run

/-! ## Assembly -/

/-- A passing replay of the root task over well-shaped families with surjective permutations
makes every stored left site cross-safe against every stored right site at all nine lifts. -/
theorem safetyPieces_sound (fam fam' : WireFamily) (records : List SafetyRecord)
    (shapeL : fam.sites.shapeCheck fam.depth fam.count = true)
    (shapeR : fam'.sites.shapeCheck fam'.depth fam'.count = true)
    (surjL : ∀ o, o < fam.count → ∃ p, p < fam.count ∧ fam.perm.get? fam.depth p = some o)
    (surjR : ∀ o, o < fam'.count → ∃ p, p < fam'.count ∧ fam'.perm.get? fam'.depth p = some o)
    (leftValid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (rightValid : ∀ w ∈ fam'.sites.toList, w.valid = true)
    (run : safetyStep fam fam' [.node 0 fam.count 0 fam'.count 511] records = some []) :
    ∀ q ∈ wireSet fam.sites.toList, ∀ q' ∈ wireSet fam'.sites.toList, ∀ lift : ℤ × ℤ,
      NineLift lift → CrossSafe (closedDisk q) (closedDisk (shiftSite q' lift)) := by
  have rootSafe := safetyStep_sound fam fam' leftValid rightValid records
    [.node 0 fam.count 0 fam'.count 511] run (.node 0 fam.count 0 fam'.count 511)
    (List.mem_cons.2 (Or.inl rfl))
  have allBits : ∀ i, i < 9 → Nat.testBit 511 i = true := by decide
  rintro q ⟨w, wMem, rfl⟩ q' ⟨w', w'Mem, rfl⟩ lift nine
  obtain ⟨ordinal, ordinalLt, found⟩ :=
    fam.sites.shapeCheck_get? fam.depth fam.count shapeL w wMem
  obtain ⟨p, pLt, permEq⟩ := surjL ordinal ordinalLt
  obtain ⟨ordinal', ordinalLt', found'⟩ :=
    fam'.sites.shapeCheck_get? fam'.depth fam'.count shapeR w' w'Mem
  obtain ⟨p', pLt', permEq'⟩ := surjR ordinal' ordinalLt'
  have wEq : fam.siteAt p = some w := by
    simp only [WireFamily.siteAt, permEq]
    exact found
  have w'Eq : fam'.siteAt p' = some w' := by
    simp only [WireFamily.siteAt, permEq']
    exact found'
  obtain ⟨i, iLt, liftEq⟩ := exists_checkLift lift nine
  rw [← liftEq]
  exact rootSafe p p' (Nat.zero_le p) pLt (Nat.zero_le p') pLt' i iLt (allBits i iLt) w w' wEq w'Eq

/-- Cross-safety of the two periodic unions from the chunked pieces. -/
theorem crossSafe_U_of_safetyPieces (fam fam' : WireFamily) (records : List SafetyRecord)
    (shapeL : fam.sites.shapeCheck fam.depth fam.count = true)
    (shapeR : fam'.sites.shapeCheck fam'.depth fam'.count = true)
    (surjL : ∀ o, o < fam.count → ∃ p, p < fam.count ∧ fam.perm.get? fam.depth p = some o)
    (surjR : ∀ o, o < fam'.count → ∃ p, p < fam'.count ∧ fam'.perm.get? fam'.depth p = some o)
    (leftValid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (rightValid : ∀ w ∈ fam'.sites.toList, w.valid = true)
    (run : safetyStep fam fam' [.node 0 fam.count 0 fam'.count 511] records = some []) :
    CrossSafe (U (wireSet fam.sites.toList)) (U (wireSet fam'.sites.toList)) :=
  crossSafe_U_of_nine_lifts (wireSet fam.sites.toList) (wireSet fam'.sites.toList)
    (wireSet_valid fam.sites.toList leftValid) (wireSet_valid fam'.sites.toList rightValid)
    (safetyPieces_sound fam fam' records shapeL shapeR surjL surjR leftValid rightValid run)

/-- Unit independence of one periodic union from the chunked pieces of its self-product. -/
theorem unitIndependent_U_of_safetyPieces (fam : WireFamily) (records : List SafetyRecord)
    (shape : fam.sites.shapeCheck fam.depth fam.count = true)
    (surj : ∀ o, o < fam.count → ∃ p, p < fam.count ∧ fam.perm.get? fam.depth p = some o)
    (valid : ∀ w ∈ fam.sites.toList, w.valid = true)
    (run : safetyStep fam fam [.node 0 fam.count 0 fam.count 511] records = some []) :
    UnitIndependent (U (wireSet fam.sites.toList)) :=
  unitIndependent_U_of_nine_lifts (wireSet fam.sites.toList) (wireSet_valid fam.sites.toList valid)
    (safetyPieces_sound fam fam records shape shape surj surj valid valid run)

/-! ## Examples -/

/-- The example permutation passes the range check through itself as inverse. -/
example : surjCheck examplePerm examplePerm 1 2 0 2 = true := by decide

/-- A constant map fails the range check. -/
example : surjCheck (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 1)) 1 2 0 2 = false := by
  decide

/-- The example tree of claimed boxes: the root interval split into two minimal intervals. -/
noncomputable def exampleBoxTree : BoxTree :=
  .split 0 1 2 ((siteBox exampleSiteA).union (siteBox exampleSiteB))
    (.leaf 0 1 (siteBox exampleSiteA)) (.leaf 1 2 (siteBox exampleSiteB))

/-- The example tree is accepted. -/
example : exampleBoxTree.check exampleFamily = true := by decide +kernel

/-- A wrong claimed box is rejected. -/
example : (BoxTree.leaf 0 1 (siteBox exampleSiteB)).check exampleFamily = false := by
  decide +kernel

/-- The fast replay accepts the example certificate. -/
example : safetyStepFast exampleFamily exampleFamily exampleBoxTree exampleBoxTree
    [.node 0 2 0 2 511] exampleRecords = some [] := by
  decide +kernel

/-- The example box of both positions is the union of the two singleton boxes. -/
example : exampleFamily.rangeBox 0 2 =
    (exampleFamily.rangeBox 0 1).bind fun box => (exampleFamily.rangeBox 1 2).map box.union :=
  exampleFamily.rangeBox_split 0 1 2 (by decide) (by decide)

end Erdos188.UpperBound
