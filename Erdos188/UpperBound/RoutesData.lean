module

public import Erdos188.UpperBound.SafetyData

/-!
# Kernel checker for route certificates

The computable replay of the route obligations of the certificate:
containment routes, which place every disk of a source family inside a
period-shifted disk of one of two target families, and exact rotation routes,
which match the rotated center of every site of a family with a period-shifted
site of the same family. Sites are stored in ordinal-addressed index trees; a
route stream names one record per source ordinal in increasing order, each
replayed with `containCheck` or `rotateMatchCheck` at the negated wire lift.
Acceptance is proved to give inclusion of the periodic unions, respectively
rotation invariance of the periodic union. Every definition consumed by
`decide` is computable and structurally recursive so that the kernel can
reduce it; the step forms are chunkable through append lemmas. No finite
family or certificate appears here.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-! ## Route records

A wire lift `n` places the target at `a' + 59 n`, while `shiftSite q' l` has center `a' - 59 l`,
so every record is checked at the Lean lift `(-nS, -nT)`. An identity record routes the source
disk into a target disk; `tgtRole = false` names the first target table and `tgtRole = true` the
second. A rho record matches the rotated source center with a site of the same table. -/

/-- One route record of the wire, without the obligation and role names. -/
inductive RouteRecord where
  /-- `identity source_index target_role target_index ns nt`: a containment route. -/
  | identity (srcPos : ℕ) (tgtRole : Bool) (tgtPos : ℕ) (nS nT : ℤ)
  /-- `rho source_index target_index ns nt`: an exact rotation route within one table. -/
  | rho (srcPos tgtPos : ℕ) (nS nT : ℤ)

/-! ## Containment routes -/

/-- The target site named by a role and a position: the first table for `false`, the second for
`true`. -/
def targetSite (tgtA tgtB : IndexTree SiteWire) (da db : ℕ) : Bool → ℕ → Option SiteWire
  | false, pos => tgtA.get? da pos
  | true, pos => tgtB.get? db pos

/-- A found target site is stored in one of the two target tables. -/
theorem targetSite_mem (tgtA tgtB : IndexTree SiteWire) (da db : ℕ) (role : Bool) (pos : ℕ)
    (q' : SiteWire) (found : targetSite tgtA tgtB da db role pos = some q') :
    q' ∈ tgtA.toList ∨ q' ∈ tgtB.toList := by
  cases role with
  | false => exact Or.inl (tgtA.get?_mem da pos q' found)
  | true => exact Or.inr (tgtB.get?_mem db pos q' found)

/-- Replay one containment record against the running source counter: the record must name the
counter as its source, find its source and target sites, and pass `containCheck` at the negated
wire lift; a rotation record is rejected. -/
def containRouteOne (src tgtA tgtB : IndexTree SiteWire) (ds da db counter : ℕ) :
    RouteRecord → Option ℕ
  | .identity srcPos tgtRole tgtPos nS nT =>
      if srcPos = counter then
        match src.get? ds srcPos, targetSite tgtA tgtB da db tgtRole tgtPos with
        | some q, some q' => if containCheck q q' (-nS) (-nT) then some (counter + 1) else none
        | _, _ => none
      else none
  | .rho _ _ _ _ => none

/-- Replay a chunk of containment records from a counter; the boundary counter is explicit so that
a stream can be split into chunks. -/
def containRoutesStep (src tgtA tgtB : IndexTree SiteWire) (ds da db : ℕ) :
    ℕ → List RouteRecord → Option ℕ
  | counter, [] => some counter
  | counter, record :: rest =>
      match containRouteOne src tgtA tgtB ds da db counter record with
      | none => none
      | some counter' => containRoutesStep src tgtA tgtB ds da db counter' rest

/-- Chunks chain: replaying a concatenation is replaying the first chunk and then the second. -/
theorem containRoutesStep_append (src tgtA tgtB : IndexTree SiteWire) (ds da db counter : ℕ)
    (first second : List RouteRecord) :
    containRoutesStep src tgtA tgtB ds da db counter (first ++ second) =
      (containRoutesStep src tgtA tgtB ds da db counter first).bind fun counter' =>
        containRoutesStep src tgtA tgtB ds da db counter' second := by
  induction first generalizing counter with
  | nil => simp [containRoutesStep]
  | cons record rest ih =>
      simp only [List.cons_append, containRoutesStep]
      cases containRouteOne src tgtA tgtB ds da db counter record with
      | none => rfl
      | some counter' => exact ih counter'

/-- Two replayed chunks with a shared boundary counter replay as one chunk. -/
theorem containRoutesStep_chain {src tgtA tgtB : IndexTree SiteWire} {ds da db : ℕ}
    {counter middle final : ℕ} {first second : List RouteRecord}
    (hfirst : containRoutesStep src tgtA tgtB ds da db counter first = some middle)
    (hsecond : containRoutesStep src tgtA tgtB ds da db middle second = some final) :
    containRoutesStep src tgtA tgtB ds da db counter (first ++ second) = some final := by
  rw [containRoutesStep_append, hfirst]
  exact hsecond

/-- The whole containment obligation: the source tree has the shape of the ordinals `[0, n)` and
the record stream replays from counter `0` to exactly `n`. -/
def containRoutesCheck (src tgtA tgtB : IndexTree SiteWire) (ds da db n : ℕ)
    (records : List RouteRecord) : Bool :=
  src.shapeCheck ds n && decide (containRoutesStep src tgtA tgtB ds da db 0 records = some n)

/-- The obligation from its two conjuncts. -/
theorem containRoutesCheck_of_step (src tgtA tgtB : IndexTree SiteWire) (ds da db n : ℕ)
    (records : List RouteRecord) (shape : src.shapeCheck ds n = true)
    (run : containRoutesStep src tgtA tgtB ds da db 0 records = some n) :
    containRoutesCheck src tgtA tgtB ds da db n records = true := by
  simp [containRoutesCheck, shape, run]

/-! ## Rotation routes -/

/-- Replay one rotation record against the running source counter: the record must name the
counter as its source, find both sites in the table, and pass `rotateMatchCheck` at the negated
wire lift; a containment record is rejected. -/
def rotationRouteOne (fam : IndexTree SiteWire) (depth counter : ℕ) : RouteRecord → Option ℕ
  | .rho srcPos tgtPos nS nT =>
      if srcPos = counter then
        match fam.get? depth srcPos, fam.get? depth tgtPos with
        | some q, some q' => if rotateMatchCheck q q' (-nS) (-nT) then some (counter + 1) else none
        | _, _ => none
      else none
  | .identity _ _ _ _ _ => none

/-- Replay a chunk of rotation records from a counter, with an explicit boundary counter. -/
def rotationRoutesStep (fam : IndexTree SiteWire) (depth : ℕ) : ℕ → List RouteRecord → Option ℕ
  | counter, [] => some counter
  | counter, record :: rest =>
      match rotationRouteOne fam depth counter record with
      | none => none
      | some counter' => rotationRoutesStep fam depth counter' rest

/-- Chunks chain: replaying a concatenation is replaying the first chunk and then the second. -/
theorem rotationRoutesStep_append (fam : IndexTree SiteWire) (depth counter : ℕ)
    (first second : List RouteRecord) :
    rotationRoutesStep fam depth counter (first ++ second) =
      (rotationRoutesStep fam depth counter first).bind fun counter' =>
        rotationRoutesStep fam depth counter' second := by
  induction first generalizing counter with
  | nil => simp [rotationRoutesStep]
  | cons record rest ih =>
      simp only [List.cons_append, rotationRoutesStep]
      cases rotationRouteOne fam depth counter record with
      | none => rfl
      | some counter' => exact ih counter'

/-- Two replayed chunks with a shared boundary counter replay as one chunk. -/
theorem rotationRoutesStep_chain {fam : IndexTree SiteWire} {depth counter middle final : ℕ}
    {first second : List RouteRecord}
    (hfirst : rotationRoutesStep fam depth counter first = some middle)
    (hsecond : rotationRoutesStep fam depth middle second = some final) :
    rotationRoutesStep fam depth counter (first ++ second) = some final := by
  rw [rotationRoutesStep_append, hfirst]
  exact hsecond

/-- The whole rotation obligation: the table has the shape of the ordinals `[0, n)` and the record
stream replays from counter `0` to exactly `n`. -/
def rotationRoutesCheck (fam : IndexTree SiteWire) (depth n : ℕ) (records : List RouteRecord) :
    Bool :=
  fam.shapeCheck depth n && decide (rotationRoutesStep fam depth 0 records = some n)

/-- The obligation from its two conjuncts. -/
theorem rotationRoutesCheck_of_step (fam : IndexTree SiteWire) (depth n : ℕ)
    (records : List RouteRecord) (shape : fam.shapeCheck depth n = true)
    (run : rotationRoutesStep fam depth 0 records = some n) :
    rotationRoutesCheck fam depth n records = true := by
  simp [rotationRoutesCheck, shape, run]

/-! ## Soundness -/

/-- The site at a source position passes `containCheck` into some stored target site at some
lift. -/
def ContainRouted (src tgtA tgtB : IndexTree SiteWire) (ds p : ℕ) : Prop :=
  ∀ q, src.get? ds p = some q → ∃ q', (q' ∈ tgtA.toList ∨ q' ∈ tgtB.toList) ∧
    ∃ lift : ℤ × ℤ, containCheck q q' lift.1 lift.2 = true

/-- The site at a position passes `rotateMatchCheck` against some stored site at some lift. -/
def RotationRouted (fam : IndexTree SiteWire) (depth p : ℕ) : Prop :=
  ∀ q, fam.get? depth p = some q → ∃ q' ∈ fam.toList, ∃ lift : ℤ × ℤ,
    rotateMatchCheck q q' lift.1 lift.2 = true

/-- One accepted containment record advances the counter by one and routes its position. -/
theorem containRouteOne_sound (src tgtA tgtB : IndexTree SiteWire) (ds da db counter : ℕ)
    (record : RouteRecord) (counter' : ℕ)
    (step : containRouteOne src tgtA tgtB ds da db counter record = some counter') :
    counter' = counter + 1 ∧ ContainRouted src tgtA tgtB ds counter := by
  cases record with
  | rho _ _ _ _ => simp [containRouteOne] at step
  | identity srcPos tgtRole tgtPos nS nT =>
      simp only [containRouteOne] at step
      split at step
      · rename_i eq
        subst eq
        revert step
        rcases qEq : src.get? ds srcPos with _ | q <;>
          rcases q'Eq : targetSite tgtA tgtB da db tgtRole tgtPos with _ | q' <;> intro step
        · simp at step
        · simp at step
        · simp at step
        · dsimp only at step
          split at step
          · rename_i check
            simp only [Option.some.injEq] at step
            refine ⟨step.symm, fun q₀ q₀Eq => ?_⟩
            rw [qEq] at q₀Eq
            cases q₀Eq
            exact ⟨q', targetSite_mem tgtA tgtB da db tgtRole tgtPos q' q'Eq, (-nS, -nT), check⟩
          · simp at step
      · simp at step

/-- One accepted rotation record advances the counter by one and routes its position. -/
theorem rotationRouteOne_sound (fam : IndexTree SiteWire) (depth counter : ℕ)
    (record : RouteRecord) (counter' : ℕ)
    (step : rotationRouteOne fam depth counter record = some counter') :
    counter' = counter + 1 ∧ RotationRouted fam depth counter := by
  cases record with
  | identity _ _ _ _ _ => simp [rotationRouteOne] at step
  | rho srcPos tgtPos nS nT =>
      simp only [rotationRouteOne] at step
      split at step
      · rename_i eq
        subst eq
        revert step
        rcases qEq : fam.get? depth srcPos with _ | q <;>
          rcases q'Eq : fam.get? depth tgtPos with _ | q' <;> intro step
        · simp at step
        · simp at step
        · simp at step
        · dsimp only at step
          split at step
          · rename_i check
            simp only [Option.some.injEq] at step
            refine ⟨step.symm, fun q₀ q₀Eq => ?_⟩
            rw [qEq] at q₀Eq
            cases q₀Eq
            exact ⟨q', fam.get?_mem depth tgtPos q' q'Eq, (-nS, -nT), check⟩
          · simp at step
      · simp at step

/-- A replayed containment chunk routes every position from its start to its end counter. -/
theorem containRoutesStep_sound (src tgtA tgtB : IndexTree SiteWire) (ds da db : ℕ)
    (records : List RouteRecord) :
    ∀ counter final : ℕ, containRoutesStep src tgtA tgtB ds da db counter records = some final →
      ∀ p, counter ≤ p → p < final → ContainRouted src tgtA tgtB ds p := by
  induction records with
  | nil =>
      intro counter final run p le lt
      simp only [containRoutesStep, Option.some.injEq] at run
      subst run
      exact absurd lt (Nat.not_lt.2 le)
  | cons record rest ih =>
      intro counter final run p le lt
      simp only [containRoutesStep] at run
      revert run
      rcases step : containRouteOne src tgtA tgtB ds da db counter record with _ | counter' <;>
        intro run
      · simp at run
      · obtain ⟨rfl, routed⟩ :=
          containRouteOne_sound src tgtA tgtB ds da db counter record counter' step
        rcases Nat.eq_or_lt_of_le le with rfl | lt'
        · exact routed
        · exact ih (counter + 1) final run p lt' lt

/-- A replayed rotation chunk routes every position from its start to its end counter. -/
theorem rotationRoutesStep_sound (fam : IndexTree SiteWire) (depth : ℕ)
    (records : List RouteRecord) :
    ∀ counter final : ℕ, rotationRoutesStep fam depth counter records = some final →
      ∀ p, counter ≤ p → p < final → RotationRouted fam depth p := by
  induction records with
  | nil =>
      intro counter final run p le lt
      simp only [rotationRoutesStep, Option.some.injEq] at run
      subst run
      exact absurd lt (Nat.not_lt.2 le)
  | cons record rest ih =>
      intro counter final run p le lt
      simp only [rotationRoutesStep] at run
      revert run
      rcases step : rotationRouteOne fam depth counter record with _ | counter' <;> intro run
      · simp at run
      · obtain ⟨rfl, routed⟩ := rotationRouteOne_sound fam depth counter record counter' step
        rcases Nat.eq_or_lt_of_le le with rfl | lt'
        · exact routed
        · exact ih (counter + 1) final run p lt' lt

/-- A passing containment obligation places every source disk inside a period-shifted disk of one
of the two target tables; all three trees must hold valid wires. -/
theorem containRoutesCheck_sound (src tgtA tgtB : IndexTree SiteWire) (ds da db n : ℕ)
    (records : List RouteRecord) (srcValid : ∀ w ∈ src.toList, w.valid = true)
    (tgtAValid : ∀ w ∈ tgtA.toList, w.valid = true)
    (tgtBValid : ∀ w ∈ tgtB.toList, w.valid = true)
    (pass : containRoutesCheck src tgtA tgtB ds da db n records = true) :
    ∀ q ∈ wireSet src.toList, ∃ q' ∈ wireSet tgtA.toList ∪ wireSet tgtB.toList,
      ∃ lift : ℤ × ℤ, closedDisk q ⊆ closedDisk (shiftSite q' lift) := by
  simp only [containRoutesCheck, Bool.and_eq_true, decide_eq_true_eq] at pass
  obtain ⟨shape, run⟩ := pass
  rintro q ⟨w, wMem, rfl⟩
  obtain ⟨p, pLt, found⟩ := src.shapeCheck_get? ds n shape w wMem
  obtain ⟨w', w'Mem, lift, check⟩ :=
    containRoutesStep_sound src tgtA tgtB ds da db records 0 n run p (Nat.zero_le p) pLt w found
  have w'Valid : w'.valid = true := by
    rcases w'Mem with mem | mem
    · exact tgtAValid w' mem
    · exact tgtBValid w' mem
  refine ⟨w'.toSite, ?_, lift, containCheck_sound w w' lift (srcValid w wMem) w'Valid check⟩
  rcases w'Mem with mem | mem
  · exact Or.inl ⟨w', mem, rfl⟩
  · exact Or.inr ⟨w', mem, rfl⟩

/-- Inclusion of the periodic unions from a passing containment obligation. -/
theorem U_subset_of_containRoutes (src tgtA tgtB : IndexTree SiteWire) (ds da db n : ℕ)
    (records : List RouteRecord) (srcValid : ∀ w ∈ src.toList, w.valid = true)
    (tgtAValid : ∀ w ∈ tgtA.toList, w.valid = true)
    (tgtBValid : ∀ w ∈ tgtB.toList, w.valid = true)
    (pass : containRoutesCheck src tgtA tgtB ds da db n records = true) :
    U (wireSet src.toList) ⊆ U (wireSet tgtA.toList) ∪ U (wireSet tgtB.toList) := by
  rw [← U_union]
  exact U_subset_U_of_routes _ _
    (containRoutesCheck_sound src tgtA tgtB ds da db n records srcValid tgtAValid tgtBValid pass)

/-- The wire set of no sites is empty. -/
theorem wireSet_nil : wireSet ([] : List SiteWire) = ∅ := by
  ext site
  simp [wireSet]

/-- The periodic union of no sites is empty. -/
theorem U_empty : U (∅ : Set Site) = ∅ := by
  ext point
  simp [U]

/-- Inclusion of the periodic unions when the second target table is empty. -/
theorem U_subset_of_containRoutes_empty (src tgtA : IndexTree SiteWire) (ds da db n : ℕ)
    (records : List RouteRecord) (srcValid : ∀ w ∈ src.toList, w.valid = true)
    (tgtAValid : ∀ w ∈ tgtA.toList, w.valid = true)
    (pass : containRoutesCheck src tgtA .empty ds da db n records = true) :
    U (wireSet src.toList) ⊆ U (wireSet tgtA.toList) := by
  have inclusion := U_subset_of_containRoutes src tgtA .empty ds da db n records srcValid tgtAValid
    (by simp [IndexTree.toList]) pass
  rwa [IndexTree.toList, wireSet_nil, U_empty, Set.union_empty] at inclusion

/-- A passing rotation obligation matches every rotated site with a period-shifted site of the
table, hence the periodic union is rotation invariant; the table must hold valid wires. -/
theorem rotationRoutesCheck_sound (fam : IndexTree SiteWire) (depth n : ℕ)
    (records : List RouteRecord) (valid : ∀ w ∈ fam.toList, w.valid = true)
    (pass : rotationRoutesCheck fam depth n records = true) :
    RotationInvariant (U (wireSet fam.toList)) := by
  simp only [rotationRoutesCheck, Bool.and_eq_true, decide_eq_true_eq] at pass
  obtain ⟨shape, run⟩ := pass
  apply rotationInvariant_U_of_exact_rotation_routes
  rintro site ⟨w, wMem, rfl⟩
  obtain ⟨p, pLt, found⟩ := fam.shapeCheck_get? depth n shape w wMem
  obtain ⟨w', w'Mem, lift, check⟩ :=
    rotationRoutesStep_sound fam depth records 0 n run p (Nat.zero_le p) pLt w found
  exact ⟨w'.toSite, ⟨w', w'Mem, rfl⟩, lift,
    rotateMatchCheck_sound w w' lift (valid w wMem) (valid w' w'Mem) check⟩

/-! ## Site tables

A generated table is a balanced top tree of block subtrees. The kernel checks validity and shape
one block at a time, and these lemmas combine the block results along the top tree, so that no
single kernel check visits more than one block. -/

/-- Validity of every stored site from the Boolean list check. -/
theorem IndexTree.valid_of_all (tree : IndexTree SiteWire)
    (pass : tree.toList.all SiteWire.valid = true) : ∀ w ∈ tree.toList, w.valid = true :=
  fun w mem => List.all_eq_true.1 pass w mem

/-- The empty tree passes every list check. -/
theorem IndexTree.all_empty {α : Type} (p : α → Bool) :
    (IndexTree.empty : IndexTree α).toList.all p = true := rfl

/-- A node passes a list check when both children do. -/
theorem IndexTree.all_node_of {α : Type} (p : α → Bool) (left right : IndexTree α)
    (leftAll : left.toList.all p = true) (rightAll : right.toList.all p = true) :
    (IndexTree.node left right).toList.all p = true := by
  simp [IndexTree.toList, List.all_append, leftAll, rightAll]

/-- The empty tree has the shape of no positions at every depth. -/
theorem IndexTree.shapeCheck_empty {α : Type} (depth : ℕ) :
    (IndexTree.empty : IndexTree α).shapeCheck depth 0 = true := by
  simp [IndexTree.shapeCheck]

/-- A node has the shape of `count` positions when its children have the shapes of the lower and
upper halves. -/
theorem IndexTree.shapeCheck_node_of {α : Type} (left right : IndexTree α) (depth count : ℕ)
    (leftShape : left.shapeCheck depth (min count (2 ^ depth)) = true)
    (rightShape : right.shapeCheck depth (count - 2 ^ depth) = true) :
    (IndexTree.node left right).shapeCheck (depth + 1) count = true := by
  simp [IndexTree.shapeCheck, leftShape, rightShape]

/-! ## Examples

Containment: the sources `(1 / 2, 0)` and `(117 / 2, 0)` of radius `1 / 10` route into the first
target `(0, 0)` of radius `1 / 4`, the second at wire lift `(1, 0)` since `117 / 2 = 59 - 1 / 2`,
and the source `(30, 0)` routes into the second table's `(30, 0)` of radius `1 / 4`. Rotation:
two disks at the origin are fixed by the rotation, and `(1, 2)` rotates to `(-2, 3)`, which is
`(57, 3)` at wire lift `(-1, 0)`. -/

/-- Three containment sources in a depth-two tree. -/
def exampleContainSources : IndexTree SiteWire :=
  .node (.node (.leaf ⟨1, 2, 0, 1, 1, 10⟩) (.leaf ⟨117, 2, 0, 1, 1, 10⟩))
    (.node (.leaf ⟨30, 1, 0, 1, 1, 10⟩) .empty)

/-- The first target table: one site at the origin of radius `1 / 4`. -/
def exampleContainTargetsA : IndexTree SiteWire := .node (.leaf ⟨0, 1, 0, 1, 1, 4⟩) .empty

/-- The second target table: one site at `(30, 0)` of radius `1 / 4`. -/
def exampleContainTargetsB : IndexTree SiteWire := .leaf ⟨30, 1, 0, 1, 1, 4⟩

/-- One accepted containment route per source, in order. -/
def exampleContainRoutes : List RouteRecord :=
  [.identity 0 false 0 0 0, .identity 1 false 0 1 0, .identity 2 true 0 0 0]

/-- The containment obligation is accepted. -/
example : containRoutesCheck exampleContainSources exampleContainTargetsA exampleContainTargetsB
    2 1 0 3 exampleContainRoutes = true := by
  decide

/-- The same stream in two chunks through the explicit boundary counter. -/
example : containRoutesStep exampleContainSources exampleContainTargetsA exampleContainTargetsB
    2 1 0 0 (exampleContainRoutes.take 2) = some 2 := by
  decide
example : containRoutesStep exampleContainSources exampleContainTargetsA exampleContainTargetsB
    2 1 0 2 (exampleContainRoutes.drop 2) = some 3 := by
  decide

/-- A wrong lift is rejected: without the lift the second source is `58 1/2` units away. -/
example : containRoutesCheck exampleContainSources exampleContainTargetsA exampleContainTargetsB
    2 1 0 3 [.identity 0 false 0 0 0, .identity 1 false 0 0 0, .identity 2 true 0 0 0] = false := by
  decide

/-- A missing source is rejected: the counter ends at `2`, not `3`. -/
example : containRoutesCheck exampleContainSources exampleContainTargetsA exampleContainTargetsB
    2 1 0 3 [.identity 0 false 0 0 0, .identity 2 true 0 0 0] = false := by
  decide

/-- The radius order is rejected: the radius-`1 / 4` target does not fit into a radius-`1 / 10`
source. -/
example : containRoutesCheck exampleContainTargetsA exampleContainSources exampleContainTargetsB
    1 2 0 1 [.identity 0 false 0 0 0] = false := by
  decide

/-- A rotation record in a containment stream is rejected. -/
example : containRoutesStep exampleContainSources exampleContainTargetsA exampleContainTargetsB
    2 1 0 0 [.rho 0 0 0 0] = none := by
  decide

/-- Two disks at the origin, of radii `1 / 10` and `1 / 4`. -/
def exampleRotationFamily : IndexTree SiteWire :=
  .node (.leaf ⟨0, 1, 0, 1, 1, 10⟩) (.leaf ⟨0, 1, 0, 1, 1, 4⟩)

/-- The rotation obligation is accepted: each origin disk is its own rotation. -/
example : rotationRoutesCheck exampleRotationFamily 1 2 [.rho 0 0 0 0, .rho 1 1 0 0] = true := by
  decide

/-- A radius mismatch is rejected. -/
example : rotationRoutesCheck exampleRotationFamily 1 2 [.rho 0 1 0 0, .rho 1 0 0 0] = false := by
  decide

/-- A wrong lift is rejected. -/
example : rotationRoutesCheck exampleRotationFamily 1 2 [.rho 0 0 1 0, .rho 1 1 0 0] = false := by
  decide

/-- The sites `(1, 2)` and `(57, 3)` of radius `1 / 10`. -/
def exampleRotationPair : IndexTree SiteWire :=
  .node (.leaf ⟨1, 1, 2, 1, 1, 10⟩) (.leaf ⟨57, 1, 3, 1, 1, 10⟩)

/-- The rotated `(1, 2)` is `(57, 3)` at wire lift `(-1, 0)`. -/
example : rotationRoutesStep exampleRotationPair 1 0 [.rho 0 1 (-1) 0] = some 1 := by decide

/-- The opposite lift sign is rejected. -/
example : rotationRoutesStep exampleRotationPair 1 0 [.rho 0 1 1 0] = none := by decide

/-- The rotated `(57, 3)` is not in the pair, so the whole obligation fails. -/
example : rotationRoutesCheck exampleRotationPair 1 2 [.rho 0 1 (-1) 0, .rho 1 0 (-1) 1] =
    false := by
  decide

/-- A containment record in a rotation stream is rejected. -/
example : rotationRoutesStep exampleRotationPair 1 0 [.identity 0 false 1 0 0] = none := by decide

end Erdos188.UpperBound
