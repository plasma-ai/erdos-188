module

public import Erdos188.LowerBound.Certificate.Run.Part1
public import Erdos188.LowerBound.Certificate.Run.Part2
public import Erdos188.LowerBound.Certificate.Run.Part3
public import Erdos188.LowerBound.Certificate.Run.Part4

/-!
# Kernel evaluation of the certificate

The interval checks `checkInterval_k` are proved by kernel evaluation in
`Erdos188.LowerBound.Certificate.Run.Part1`–`Part4`; here they are collected, and the error budget
is checked.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

theorem checkErrorBudget_eq_true : checkErrorBudget = true := by decide +kernel

/-- Every interval check passes. -/
theorem checkInterval_eq_true : ∀ k, k < numIntervals → checkInterval k = true
  | 0, _ => checkInterval_0
  | 1, _ => checkInterval_1
  | 2, _ => checkInterval_2
  | 3, _ => checkInterval_3
  | 4, _ => checkInterval_4
  | 5, _ => checkInterval_5
  | 6, _ => checkInterval_6
  | 7, _ => checkInterval_7
  | 8, _ => checkInterval_8
  | 9, _ => checkInterval_9
  | 10, _ => checkInterval_10
  | 11, _ => checkInterval_11
  | 12, _ => checkInterval_12
  | 13, _ => checkInterval_13
  | 14, _ => checkInterval_14
  | 15, _ => checkInterval_15
  | 16, _ => checkInterval_16
  | 17, _ => checkInterval_17
  | 18, _ => checkInterval_18
  | 19, _ => checkInterval_19
  | 20, _ => checkInterval_20
  | 21, _ => checkInterval_21
  | 22, _ => checkInterval_22
  | 23, _ => checkInterval_23
  | 24, _ => checkInterval_24
  | 25, _ => checkInterval_25
  | 26, _ => checkInterval_26
  | 27, _ => checkInterval_27
  | 28, _ => checkInterval_28
  | 29, _ => checkInterval_29
  | 30, _ => checkInterval_30
  | 31, _ => checkInterval_31
  | 32, _ => checkInterval_32
  | 33, _ => checkInterval_33
  | 34, _ => checkInterval_34
  | 35, _ => checkInterval_35
  | 36, _ => checkInterval_36
  | 37, _ => checkInterval_37
  | 38, _ => checkInterval_38
  | 39, _ => checkInterval_39
  | 40, _ => checkInterval_40
  | _ + 41, h => absurd h (Nat.not_lt_of_le (Nat.le_add_left 41 _))

theorem check_eq_true : check = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, checkErrorBudget_eq_true,
    and_true]
  exact checkInterval_eq_true

end Erdos188.LowerBound.Certificate
