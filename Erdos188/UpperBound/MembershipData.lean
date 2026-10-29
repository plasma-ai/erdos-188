module

public import Erdos188.UpperBound.CoverData
public import Erdos188.UpperBound.RoutesData

/-!
# Membership of the cover sites in the base and micro tables

The bridge between the covering certificate and the route certificates. The
covering certificate certifies the root cell for the family listed by the
cover site tree, and the route certificates prove containment and rotation
facts about the families listed by the base and micro tables. The red set is
built from the base and micro tables, so the covering conclusion transfers to
it once every cover site is a base site or a micro site. This module supplies
the chunkable kernel check of that inclusion. The three tables are strictly
increasing in one order and the cover table is the merge of the other two, so
a walk along the cover sites with one cursor into each of the base and micro
tables matches every cover site against the site stored at one of the two
cursors and advances that cursor; the walk never compares sites by order, so
no validity or ordering hypothesis is needed. The step function returns the
residual cursor pair, so a walk cut into consecutive chunks is checked chunk
by chunk and the chunk theorems chain through list concatenation. Soundness
reduces to `IndexTree.get?_mem`. No finite table is supplied here; the
generated modules under `Data/` and `Checks/` instantiate this interface.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

/-- A cursor pair: the next unmatched positions of the base and micro tables. -/
abbrev MembershipState := ℕ × ℕ

/-- Match one cover site against the site at the base cursor, else against the site at the micro
cursor, and advance the matching cursor; an unmatched site fails. -/
def membershipStepOne (bTree mTree : IndexTree SiteWire) (db dm : ℕ) (state : MembershipState)
    (site : SiteWire) : Option MembershipState :=
  if bTree.get? db state.1 = some site then some (state.1 + 1, state.2)
  else if mTree.get? dm state.2 = some site then some (state.1, state.2 + 1)
  else none

/-- Walk a chunk of cover sites from a cursor pair; the residual cursor pair survives, failure
does not. -/
def membershipStep (bTree mTree : IndexTree SiteWire) (db dm : ℕ) :
    MembershipState → List SiteWire → Option MembershipState
  | state, [] => some state
  | state, site :: rest =>
      match membershipStepOne bTree mTree db dm state site with
      | none => none
      | some next => membershipStep bTree mTree db dm next rest

/-- Walking a concatenation walks the first part and then the second from its residual. -/
theorem membershipStep_append (bTree mTree : IndexTree SiteWire) (db dm : ℕ)
    (first second : List SiteWire) :
    ∀ state : MembershipState, membershipStep bTree mTree db dm state (first ++ second) =
      (membershipStep bTree mTree db dm state first).bind
        (fun residual => membershipStep bTree mTree db dm residual second) := by
  induction first with
  | nil =>
      intro state
      simp [membershipStep]
  | cons site rest ih =>
      intro state
      simp only [List.cons_append, membershipStep]
      rcases hstep : membershipStepOne bTree mTree db dm state site with _ | next
      · simp
      · simp [ih]

/-- Two consecutive passing chunks pass as one chunk. -/
theorem membershipStep_chain {bTree mTree : IndexTree SiteWire} {db dm : ℕ}
    {state middle final : MembershipState} {first second : List SiteWire}
    (hfirst : membershipStep bTree mTree db dm state first = some middle)
    (hsecond : membershipStep bTree mTree db dm middle second = some final) :
    membershipStep bTree mTree db dm state (first ++ second) = some final := by
  rw [membershipStep_append, hfirst]
  exact hsecond

/-- A matched site is stored in the base table or in the micro table. -/
theorem membershipStepOne_sound (bTree mTree : IndexTree SiteWire) (db dm : ℕ)
    (state next : MembershipState) (site : SiteWire)
    (hstep : membershipStepOne bTree mTree db dm state site = some next) :
    site ∈ bTree.toList ∨ site ∈ mTree.toList := by
  unfold membershipStepOne at hstep
  split at hstep
  · next hbase => exact Or.inl (IndexTree.get?_mem bTree db state.1 site hbase)
  · split at hstep
    · next hmicro => exact Or.inr (IndexTree.get?_mem mTree dm state.2 site hmicro)
    · simp at hstep

/-- Every site of a passing chunk is stored in the base table or in the micro table. -/
theorem membershipStep_sound (bTree mTree : IndexTree SiteWire) (db dm : ℕ)
    (chunk : List SiteWire) :
    ∀ state final : MembershipState, membershipStep bTree mTree db dm state chunk = some final →
      ∀ site ∈ chunk, site ∈ bTree.toList ∨ site ∈ mTree.toList := by
  induction chunk with
  | nil =>
      intro state final _ site hsite
      simp at hsite
  | cons head rest ih =>
      intro state final hcheck site hsite
      simp only [membershipStep] at hcheck
      rcases hstep : membershipStepOne bTree mTree db dm state head with _ | next
      · simp [hstep] at hcheck
      · simp only [hstep] at hcheck
        rcases List.mem_cons.mp hsite with heq | hmem
        · rw [heq]
          exact membershipStepOne_sound bTree mTree db dm state next head hstep
        · exact ih next final hcheck site hmem

/-- A tree family lies in the union of two wire families once every tree site is stored in one
of the two tables. -/
theorem coverSiteSet_subset_wireSet_union (tree : SiteTree) (bTree mTree : IndexTree SiteWire)
    (hmem : ∀ site ∈ tree.toList, site ∈ bTree.toList ∨ site ∈ mTree.toList) :
    coverSiteSet tree ⊆ wireSet bTree.toList ∪ wireSet mTree.toList := by
  rintro q ⟨site, hsite, rfl⟩
  rcases hmem site hsite with hbase | hmicro
  · exact Or.inl ⟨site, hbase, rfl⟩
  · exact Or.inr ⟨site, hmicro, rfl⟩

/-- A passing walk over the whole flattened tree places the tree family in the union of the two
wire families. -/
theorem coverSiteSet_subset_of_membershipStep (tree : SiteTree) (bTree mTree : IndexTree SiteWire)
    (db dm : ℕ) (state final : MembershipState)
    (hwalk : membershipStep bTree mTree db dm state tree.toList = some final) :
    coverSiteSet tree ⊆ wireSet bTree.toList ∪ wireSet mTree.toList :=
  coverSiteSet_subset_wireSet_union tree bTree mTree
    (membershipStep_sound bTree mTree db dm tree.toList state final hwalk)

/-! ## Examples

The base table holds `(1, 1)` and `(30, 30)`, the micro table holds `(2, 2)` alone, and the
cover list is their merge `(1, 1)`, `(2, 2)`, `(30, 30)`: the walk ends with both cursors past
their tables, a foreign site fails, and a repeated site fails because its cursor has moved on. -/

/-- The site at base ordinal `0`. -/
def membershipExampleA : SiteWire := ⟨1, 1, 1, 1, 1, 10⟩

/-- The site at base ordinal `1`. -/
def membershipExampleB : SiteWire := ⟨30, 1, 30, 1, 1, 10⟩

/-- The site at micro ordinal `0`. -/
def membershipExampleC : SiteWire := ⟨2, 1, 2, 1, 1, 10⟩

/-- The two-site base table of depth one. -/
def membershipExampleBase : IndexTree SiteWire :=
  .node (.leaf membershipExampleA) (.leaf membershipExampleB)

/-- The one-site micro table of depth one. -/
def membershipExampleMicro : IndexTree SiteWire := .node (.leaf membershipExampleC) .empty

example : membershipStep membershipExampleBase membershipExampleMicro 1 1 (0, 0)
    [membershipExampleA, membershipExampleC, membershipExampleB] = some (2, 1) := by
  decide

example : membershipStep membershipExampleBase membershipExampleMicro 1 1 (0, 0)
    [membershipExampleA, membershipExampleC] = some (1, 1) := by
  decide

example : membershipStep membershipExampleBase membershipExampleMicro 1 1 (1, 1)
    [membershipExampleB] = some (2, 1) := by
  decide

example : membershipStep membershipExampleBase membershipExampleMicro 1 1 (0, 0)
    [membershipExampleA, ⟨3, 1, 3, 1, 1, 10⟩] = none := by
  decide

example : membershipStep membershipExampleBase membershipExampleMicro 1 1 (0, 0)
    [membershipExampleA, membershipExampleA] = none := by
  decide

end Erdos188.UpperBound
