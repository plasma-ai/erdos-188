module

public import Erdos188.UpperBound.ExactCover

/-!
# Tree-indexed site tables and chunked certificate replay

The data layer of the covering interface. The list checker of `ExactCover`
indexes its site table linearly, which the kernel cannot afford on a table of
hundreds of thousands of sites, and it replays the whole certificate in one
Boolean, which cannot be split across build jobs. This module replaces the
table with a binary tree indexed by the bits of an ordinal, so a lookup costs
one step per bit, and replaces the Boolean with a step function that returns
the residual cell stack, so a certificate cut into consecutive chunks is
checked chunk by chunk and the chunk theorems chain through list
concatenation. Soundness reduces to the leaf soundness of `ExactCover`. No
finite table or certificate is supplied here; the generated modules under
`Data/` and `Checks/` instantiate this interface.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos188.UpperBound

-- Residual stacks and looked-up sites are compared field by field by `decide`.
deriving instance DecidableEq for Cell
deriving instance DecidableEq for SiteWire

/-- A binary tree of wire sites; missing ordinals are `empty` subtrees. -/
inductive SiteTree where
  /-- One site at a full-depth position. -/
  | leaf (site : SiteWire)
  /-- Two subtrees; the current bit of the ordinal selects the left or the right one. -/
  | node (left right : SiteTree)
  /-- No site below this position. -/
  | empty

/-- Look up ordinal `n` in a tree with `depth` levels below the root: at a node with `k + 1`
levels left, `n < 2 ^ k` selects the left child with the same ordinal and otherwise the right
child with `n - 2 ^ k`, so the path of `n` reads its binary digits from bit `depth - 1` down to
bit `0`; a leaf answers only when no level is left, and `empty` never answers. -/
def SiteTree.get? : SiteTree → ℕ → ℕ → Option SiteWire
  | leaf site, 0, _ => some site
  | leaf _, _ + 1, _ => none
  | node _ _, 0, _ => none
  | node left right, k + 1, n =>
      if n < 2 ^ k then left.get? k n else right.get? k (n - 2 ^ k)
  | empty, _, _ => none

/-- The sites of a tree in left-to-right order. -/
def SiteTree.toList : SiteTree → List SiteWire
  | leaf site => [site]
  | node left right => left.toList ++ right.toList
  | empty => []

/-- A site occurs at some leaf of the tree. -/
def SiteTree.Mem : SiteTree → SiteWire → Prop
  | leaf site', site => site = site'
  | node left right, site => left.Mem site ∨ right.Mem site
  | empty, _ => False

instance : Membership SiteWire SiteTree := ⟨SiteTree.Mem⟩

/-- Tree membership is the leaf occurrence predicate. -/
theorem SiteTree.mem_def (tree : SiteTree) (site : SiteWire) : site ∈ tree ↔ tree.Mem site :=
  Iff.rfl

/-- Tree membership is list membership of the flattened tree. -/
theorem SiteTree.mem_toList :
    ∀ (tree : SiteTree) (site : SiteWire), site ∈ tree.toList ↔ site ∈ tree
  | leaf site', site => by simp [toList, mem_def, Mem]
  | node left right, site => by
      rw [toList, List.mem_append, mem_toList left, mem_toList right]
      rfl
  | empty, site => by simp [toList, mem_def, Mem]

/-- A successful lookup returns a site of the flattened tree. -/
theorem SiteTree.get?_mem :
    ∀ (tree : SiteTree) (depth n : ℕ) (site : SiteWire),
      tree.get? depth n = some site → site ∈ tree.toList
  | leaf site', 0, _, site, hget => by
      simp only [get?, Option.some.injEq] at hget
      simp [toList, hget]
  | leaf _, _ + 1, _, _, hget => by simp [get?] at hget
  | node _ _, 0, _, _, hget => by simp [get?] at hget
  | node left right, k + 1, n, site, hget => by
      simp only [get?] at hget
      split at hget
      · exact List.mem_append_left _ (get?_mem left k n site hget)
      · exact List.mem_append_right _ (get?_mem right k (n - 2 ^ k) site hget)
  | empty, _, _, _, hget => by simp [get?] at hget

/-- The leaf test against the site at a tree ordinal; a missing ordinal fails. -/
def treeLeafCheck (tree : SiteTree) (depth ordinal : ℕ) (cell : Cell) (j liftS liftT : ℤ) :
    Bool :=
  match tree.get? depth ordinal with
  | none => false
  | some site => leafCheck cell j site liftS liftT

/-- Replay records against an explicit cell stack; the residual stack survives, failure does
not, and the records must run out before the stack does. -/
def coverStreamStep (tree : SiteTree) (depth : ℕ) :
    List Cell → List CoverRecord → Option (List Cell)
  | stack, [] => some stack
  | [], _ :: _ => none
  | cell :: stack, CoverRecord.direction d i e h k :: rest =>
      if cell.hasAddress d i e h k then
        coverStreamStep tree depth (cell.directionChild 0 :: cell.directionChild 1 :: stack) rest
      else none
  | cell :: stack, CoverRecord.translation d i e h k :: rest =>
      if cell.hasAddress d i e h k then
        coverStreamStep tree depth (cell.translationChild 0 0 :: cell.translationChild 0 1 ::
          cell.translationChild 1 0 :: cell.translationChild 1 1 :: stack) rest
      else none
  | cell :: stack, CoverRecord.leaf d i e h k j ordinal liftS liftT :: rest =>
      if cell.hasAddress d i e h k && treeLeafCheck tree depth ordinal cell j liftS liftT then
        coverStreamStep tree depth stack rest
      else none

/-- The semantic family listing exactly the sites of a tree. -/
def coverSiteSet (tree : SiteTree) : Set Site :=
  {q | ∃ site ∈ tree.toList, site.toSite = q}

/-- A passing tree leaf test names a tree site that passes the leaf test. -/
theorem treeLeafCheck_sound (tree : SiteTree) (depth ordinal : ℕ) (cell : Cell)
    (j liftS liftT : ℤ) (hcheck : treeLeafCheck tree depth ordinal cell j liftS liftT = true) :
    ∃ site ∈ tree.toList, leafCheck cell j site liftS liftT = true := by
  rcases hget : tree.get? depth ordinal with _ | site
  · simp [treeLeafCheck, hget] at hcheck
  · simp only [treeLeafCheck, hget] at hcheck
    exact ⟨site, SiteTree.get?_mem tree depth ordinal site hget, hcheck⟩

/-- Replaying a concatenation replays the first part and then the second from its residual. -/
theorem coverStreamStep_append (tree : SiteTree) (depth : ℕ) (first second : List CoverRecord) :
    ∀ stack : List Cell, coverStreamStep tree depth stack (first ++ second) =
      (coverStreamStep tree depth stack first).bind
        (fun residual => coverStreamStep tree depth residual second) := by
  induction first with
  | nil =>
      intro stack
      simp [coverStreamStep]
  | cons record rest ih =>
      intro stack
      cases stack with
      | nil => simp [coverStreamStep]
      | cons top stack =>
          cases record with
          | direction d i e h k =>
              simp only [List.cons_append, coverStreamStep]
              cases top.hasAddress d i e h k
              · simp
              · simp [ih]
          | translation d i e h k =>
              simp only [List.cons_append, coverStreamStep]
              cases top.hasAddress d i e h k
              · simp
              · simp [ih]
          | leaf d i e h k j ordinal liftS liftT =>
              simp only [List.cons_append, coverStreamStep]
              cases top.hasAddress d i e h k && treeLeafCheck tree depth ordinal top j liftS liftT
              · simp
              · simp [ih]

/-- Two consecutive passing chunks pass as one chunk. -/
theorem coverStreamStep_chain {tree : SiteTree} {depth : ℕ} {stack middle final : List Cell}
    {first second : List CoverRecord}
    (hfirst : coverStreamStep tree depth stack first = some middle)
    (hsecond : coverStreamStep tree depth middle second = some final) :
    coverStreamStep tree depth stack (first ++ second) = some final := by
  rw [coverStreamStep_append, hfirst]
  exact hsecond

/-- A replay from any stack that ends with the empty stack certifies every cell on the stack. -/
theorem coverStreamStep_sound (siteSet : Set Site) (tree : SiteTree) (depth : ℕ)
    (hsites : ∀ site ∈ tree.toList, site.toSite ∈ siteSet) (records : List CoverRecord) :
    ∀ stack : List Cell, coverStreamStep tree depth stack records = some [] →
      ∀ cell ∈ stack, Certified siteSet cell := by
  induction records with
  | nil =>
      intro stack hcheck cell hcell
      simp only [coverStreamStep, Option.some.injEq] at hcheck
      rw [hcheck] at hcell
      simp at hcell
  | cons record rest ih =>
      intro stack hcheck cell hcell
      cases stack with
      | nil => simp [coverStreamStep] at hcheck
      | cons top stack =>
          cases record with
          | direction d i e h k =>
              simp only [coverStreamStep] at hcheck
              split at hcheck
              · have children := ih _ hcheck
                rcases List.mem_cons.mp hcell with heq | hmem
                · rw [heq]
                  exact Certified.directionSplit top (children _ (by simp)) (children _ (by simp))
                · exact children cell (by simp [hmem])
              · simp at hcheck
          | translation d i e h k =>
              simp only [coverStreamStep] at hcheck
              split at hcheck
              · have children := ih _ hcheck
                rcases List.mem_cons.mp hcell with heq | hmem
                · rw [heq]
                  refine Certified.translationSplit top ?_
                  simp only [Fin.forall_fin_two]
                  exact ⟨⟨children _ (by simp), children _ (by simp)⟩,
                    ⟨children _ (by simp), children _ (by simp)⟩⟩
                · exact children cell (by simp [hmem])
              · simp at hcheck
          | leaf d i e h k j ordinal liftS liftT =>
              simp only [coverStreamStep] at hcheck
              split at hcheck
              · next hguard =>
                  simp only [Bool.and_eq_true] at hguard
                  rcases List.mem_cons.mp hcell with heq | hmem
                  · rw [heq]
                    obtain ⟨site, hsite, hpass⟩ :=
                      treeLeafCheck_sound tree depth ordinal top j liftS liftT hguard.2
                    exact Certified.leaf top ⟨j, site.toSite, (liftS, liftT)⟩
                      (leafCheck_sound siteSet top j site (liftS, liftT) (hsites site hsite) hpass)
                  · exact ih stack hcheck cell hmem
              · simp at hcheck

/-- A replay from the root cell alone that ends with the empty stack certifies the root. -/
theorem coverStreamStep_root (siteSet : Set Site) (tree : SiteTree) (depth : ℕ)
    (hsites : ∀ site ∈ tree.toList, site.toSite ∈ siteSet) (records : List CoverRecord)
    (hcheck : coverStreamStep tree depth [rootCell] records = some []) :
    Certified siteSet rootCell :=
  coverStreamStep_sound siteSet tree depth hsites records [rootCell] hcheck rootCell
    (List.mem_singleton_self rootCell)

/-- Every tree site belongs to the family of the tree. -/
theorem toSite_mem_coverSiteSet (tree : SiteTree) :
    ∀ site ∈ tree.toList, site.toSite ∈ coverSiteSet tree :=
  fun site hsite => ⟨site, hsite, rfl⟩

/-- A passing root replay certifies the root for the family of the tree. -/
theorem coverStreamStep_certified (tree : SiteTree) (depth : ℕ) (records : List CoverRecord)
    (hcheck : coverStreamStep tree depth [rootCell] records = some []) :
    Certified (coverSiteSet tree) rootCell :=
  coverStreamStep_root (coverSiteSet tree) tree depth (toSite_mem_coverSiteSet tree) records hcheck

example : (SiteTree.node (.node (.leaf wideSite) .empty) (.leaf ⟨1, 1, 1, 1, 1, 1⟩)).get? 2 0 =
    some wideSite := by
  decide

example : (SiteTree.node (.node (.leaf wideSite) .empty) (.leaf ⟨1, 1, 1, 1, 1, 1⟩)).get? 2 1 =
    none := by
  decide

example : (SiteTree.node (.node (.leaf wideSite) .empty) (.leaf ⟨1, 1, 1, 1, 1, 1⟩)).get? 2 2 =
    none := by
  decide

example : coverStreamStep (.node (.leaf wideSite) .empty) 1 [rootCell]
    [.direction 0 0 0 0 0, .translation 1 0 0 0 0,
      .leaf 1 0 1 0 0 0 0 0 0, .leaf 1 0 1 0 1 0 0 0 0,
      .leaf 1 0 1 1 0 0 0 0 0, .leaf 1 0 1 1 1 0 0 0 0,
      .leaf 1 1 0 0 0 1 0 0 0] = some [] := by
  decide

example : coverStreamStep (.node (.leaf wideSite) .empty) 1 [rootCell]
    [.direction 0 0 0 0 0, .translation 1 0 0 0 0, .leaf 1 0 1 0 0 0 0 0 0] =
      some [⟨1, 0, 1, 0, 1⟩, ⟨1, 0, 1, 1, 0⟩, ⟨1, 0, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0⟩] :=
  by decide

example : coverStreamStep (.node (.leaf wideSite) .empty) 1 [rootCell]
    [.leaf 0 0 0 0 0 0 1 0 0] = none := by
  decide

example : coverStreamStep (.node (.leaf wideSite) .empty) 1 [rootCell]
    [.leaf 0 0 0 0 0 0 0 0 0, .leaf 0 0 0 0 0 0 0 0 0] = none := by
  decide

end Erdos188.UpperBound
