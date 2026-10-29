module

/-!
# Coefficient tables

The two integer tables of the fourteen-point proof: the row coefficients
`(H_j, U_j, D_j)` of the cost `C`, and the radial kernel coefficients `C_n` of
`F(t) = 191 + ∑ₙ Cₙ J₀(√n t)`.
-/

@[expose] public section

namespace Erdos188.LowerBound

/-- The coefficients `(H_j, U_j, D_j)` for `j = 1, …, 6`, indexed by `j - 1`. -/
def rowTable : Fin 6 → Int × Int × Int
  | 0 => (0, -10, 0)
  | 1 => (5, -7, -7)
  | 2 => (6, -4, -4)
  | 3 => (3, -5, -3)
  | 4 => (0, -5, -2)
  | 5 => (1, 3, -2)

/-- The radii squared `n` appearing in the kernel `F`. -/
def kernelRadius : Fin 11 → Nat
  | 0 => 1
  | 1 => 3
  | 2 => 4
  | 3 => 7
  | 4 => 9
  | 5 => 13
  | 6 => 16
  | 7 => 21
  | 8 => 31
  | 9 => 36
  | 10 => 43

/-- The kernel coefficients `C_n`: `322` at `n = 1`, and `32 c_n` otherwise. -/
def kernelCoeff : Fin 11 → Int
  | 0 => 322
  | 1 => -544
  | 2 => 320
  | 3 => -352
  | 4 => 384
  | 5 => -224
  | 6 => 192
  | 7 => -224
  | 8 => -224
  | 9 => 64
  | 10 => 96

end Erdos188.LowerBound
