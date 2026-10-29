module

public import Erdos188.LowerBound.Coefficients

/-!
# The fourteen-point pattern inequality

The points `je + yv` (`0 ≤ j ≤ 6`, `y ∈ {0, 1}`, `e = 1`, `v = e^{iπ/3}`) form two
rows of seven. A red/blue labeling of them with no red unit pair and a red point in
each row is an admissible word. For every admissible word `w`,

`P(w₀, …, w₅) - P(w₁, …, w₆) ≤ C(w) + C(σw)`,

where `C` is the cost, `σ` is the half-turn of the patch, and `P` is an integer
potential on six-column states specified by sixty integers.
-/

@[expose] public section

namespace Erdos188.LowerBound.Pattern

/-- A column `{je, je + v}`: `0` has no red point, `1` has `je` red, and `2` has
`je + v` red. Both points are at unit distance, so they are not both red. -/
abbrev Column := Fin 3

/-- The red indicator of the lower point of a column. -/
def lower (c : Column) : Int := if c = 1 then 1 else 0

/-- The red indicator of the upper point of a column. -/
def upper (c : Column) : Int := if c = 2 then 1 else 0

/-- Consecutive columns have no red unit pair: neither row has adjacent red points,
and the upper point `je + v` and the next lower point `(j + 1)e` are not both red. -/
def compatible (s t : Column) : Bool :=
  !(s == t && s != 0) && !(s == 2 && t == 1)

/-- Every pair of consecutive columns is compatible. -/
def chain : List Column → Bool
  | s :: t :: rest => compatible s t && chain (t :: rest)
  | _ => true

/-- Exchange the two rows of a column. -/
def swapRows (c : Column) : Column := if c = 1 then 2 else if c = 2 then 1 else 0

/-- The half-turn of a list of columns: reverse the columns and exchange the rows. -/
def halfTurn (s : List Column) : List Column := (s.map swapRows).reverse

/-- All lists of `n` columns, in lexicographic order. -/
def allLists : Nat → List (List Column)
  | 0 => [[]]
  | n + 1 => (List.finRange 3).flatMap fun c => (allLists n).map (c :: ·)

/-- The nonzero compatible six-column states, in lexicographic order. -/
def states : List (List Column) :=
  (allLists 6).filter fun s => s.any (· != 0) && chain s

/-- The states preceding their half-turn, one from each non-fixed pair. -/
def representatives : List (List Column) :=
  states.filter fun s => decide (s < halfTurn s)

/-- The sixty potential values on `representatives`. -/
def values : List Int :=
  [1, 6, 1, -2, 0, 0, 4, -1, -2, 0,
   -1, 12, 4, 0, 3, -6, -1, 0, 6, 0,
   14, -1, 0, 0, 0, 0, 2, -8, 4, -6,
   -6, -2, 6, 2, 8, 0, 0, 0, 9, -2,
   4, 2, -4, 14, -4, -3, -10, -5, -4, 3,
   -10, -12, -4, 0, 0, 2, 5, 0, 6, -8]

/-- The potential value of a representative state. -/
def lookup (s : List Column) : Int :=
  (((representatives.zip values).find? (·.1 == s)).map (·.2)).getD 0

/-- The potential, extended to all states so that `P(σs) = -P(s)`. -/
def potential (s : List Column) : Int :=
  if s < halfTurn s then lookup s
  else if halfTurn s < s then -lookup (halfTurn s)
  else 0

/-- A labeling of the fourteen points, column by column. -/
abbrev Word := Fin 7 → Column

/-- The labeling has no red unit pair and a red point in each row. -/
def admissible (w : Word) : Bool :=
  chain (List.ofFn w) && (List.ofFn w).any (· == 1) && (List.ofFn w).any (· == 2)

/-- The cost `C(w) = -3(w₀₀ + w₀₁) - ∑ⱼ [Hⱼ(w₀₀wⱼ₀ + w₀₁wⱼ₁) + Uⱼw₀₀wⱼ₁ + Dⱼw₀₁wⱼ₀]`. -/
def cost (w : Word) : Int :=
  -3 * (lower (w 0) + upper (w 0)) -
    ((List.finRange 6).map fun j =>
      let (H, U, D) := rowTable j
      H * (lower (w 0) * lower (w j.succ) + upper (w 0) * upper (w j.succ)) +
        U * lower (w 0) * upper (w j.succ) + D * upper (w 0) * lower (w j.succ)).sum

/-- The half-turn of a word. -/
def halfTurnWord (w : Word) : Word := fun j => swapRows (w j.rev)

/-- The first six columns of a word. -/
def window₀ (w : Word) : List Column := List.ofFn fun i : Fin 6 => w i.castSucc

/-- The last six columns of a word. -/
def window₁ (w : Word) : List Column := List.ofFn fun i : Fin 6 => w i.succ

/-- The pattern inequality on one word, as a Boolean test. -/
def check (w : Word) : Bool :=
  !admissible w || decide (potential (window₀ w) - potential (window₁ w) ≤
    cost w + cost (halfTurnWord w))

/-- The word with columns read from a list, padded with empty columns. -/
def ofList (l : List Column) : Word := fun i => l.getD i 0

/-- The test passes on every seven-column list. -/
theorem check_allLists : (allLists 7).all (fun l => check (ofList l)) = true := by
  decide +kernel

/-- Every list of `n` columns appears in `allLists n`. -/
theorem mem_allLists : ∀ {n : Nat} (l : List Column), l.length = n → l ∈ allLists n
  | 0, [], _ => by simp [allLists]
  | n + 1, c :: l, h => by
    simp only [allLists, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨c, l, mem_allLists l (by simpa using h), rfl⟩

/-- Reading a word's columns into a list and back recovers the word. -/
theorem ofList_ofFn (w : Word) : ofList (List.ofFn w) = w := by
  funext i
  simp [ofList, List.getD_eq_getElem?_getD, -List.ofFn_succ]

/-- The finite certificate: the potential difference is bounded by the symmetrized cost on
every admissible word. -/
theorem pattern_inequality (w : Word) (hw : admissible w = true) :
    potential (window₀ w) - potential (window₁ w) ≤ cost w + cost (halfTurnWord w) := by
  have h := List.all_eq_true.mp check_allLists (List.ofFn w)
    (mem_allLists _ (List.length_ofFn ..))
  rw [ofList_ofFn] at h
  simpa [check, hw] using h

end Erdos188.LowerBound.Pattern
