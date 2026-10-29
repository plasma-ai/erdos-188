module

public import Erdos188.LowerBound.Coefficients
public import Erdos188.LowerBound.Certificate.Data

/-!
# The rational certificate checker

A computable checker for `F(t) ≥ 0` on `[0, 81]`, following
`kernel_certificate_method.md`. For each `n` in `kernelRadius` it builds degree-44
rational polynomial approximations of `J₀(√n t)` on the intervals
`[0,2], [2,4], …, [78,80], [80,81]` from the recurrence for Bessel's equation, bounds
their residual integrals and join discrepancies, and checks positivity of
`191 + ∑ₙ Cₙ pₙ` minus the weighted error budget by Bernstein coefficients, with the
fixed subdivision of `[2,4]` and `[4,6]`.

Everything here is computable rational arithmetic, evaluated by the kernel in
`Erdos188.LowerBound.Certificate.Run`.

## Soundness outline

Fix the `i`-th radius `n = kernelRadius i` and write `y(t) = J₀(√n t)`. Interval `k` is
`[aₖ, aₖ + hₖ]` with `aₖ = intervalStart k`, `hₖ = intervalWidth k`, and carries the
polynomial `Pₖ(t) = evalPoly (approxPoly k i) (t - aₖ)`. `checkInterval k = true` gives:

* `k = 0`: `startValue 0 i = (1, 0)`, so `P₀(0) = y(0)` and `P₀'(0) = y'(0)`.
* The residual `R` with `t R(t) = t Pₖ'' + Pₖ' + n t Pₖ` (whose numerator is
  `evalPoly (residualNum n aₖ (approxPoly k i)) (t - aₖ)`) has `∫ |R| ≤ r`, where
  `residualBound … = some r`, and `r + join ≤ errorBound k i`, where `join` is
  `joinBound n hₖ (approxPoly k i) (startValue (k+1) i)` for `k + 1 < numIntervals` (the
  energy jump from `Pₖ` to `Pₖ₊₁` at `aₖ + hₖ = aₖ₊₁`, since `Pₖ₊₁(aₖ₊₁)` and
  `Pₖ₊₁'(aₖ₊₁)` are the components of `startValue (k+1) i`) and `0` otherwise.
* `errorBudget ≤ evalPoly (combinedPoly k) z` for `z ∈ [0, hₖ]`, by `checkPieces`.

By the energy estimate, `|y(t) - Pₖ(t)| ≤ ∑_{j ≤ k} errorBound j i` on interval `k`, and
`checkErrorBudget = true` gives `∑ᵢ |Cᵢ| ∑ₖ errorBound k i ≤ errorBudget`. Hence
`kernelF t ≥ evalPoly (combinedPoly k) (t - aₖ) - errorBudget ≥ 0`.
-/

@[expose] public section

namespace Erdos188.LowerBound.Certificate

/-! ### Polynomials as coefficient lists

A list `[c₀, c₁, …, c_d]` represents the polynomial `∑ₖ cₖ xᵏ`. -/

/-- `evalPoly c x = ∑ₖ c[k] * x ^ k`, by Horner's rule. -/
def evalPoly : List Rat → Rat → Rat
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

/-- The coefficientwise sum: `evalPoly (addPoly p q) x = evalPoly p x + evalPoly q x`. -/
def addPoly : List Rat → List Rat → List Rat
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addPoly p q

/-- `evalPoly (scalePoly r p) x = r * evalPoly p x`. -/
def scalePoly (r : Rat) (p : List Rat) : List Rat :=
  p.map (r * ·)

/-- Multiplication by a linear polynomial:
`evalPoly (mulLinear u w p) x = (u + w * x) * evalPoly p x`. -/
def mulLinear (u w : Rat) : List Rat → List Rat
  | [] => []
  | c :: cs => (u * c) :: addPoly [w * c] (mulLinear u w cs)

/-- `(derivAux k c)[j] = (k + j) * c[j]`. -/
def derivAux : Nat → List Rat → List Rat
  | _, [] => []
  | k, c :: cs => ((k : Rat) * c) :: derivAux (k + 1) cs

/-- The derivative: `(derivPoly c)[k] = (k + 1) * c[k + 1]`, so
`evalPoly (derivPoly c)` is the derivative of `evalPoly c`. -/
def derivPoly : List Rat → List Rat
  | [] => []
  | _ :: cs => derivAux 1 cs

/-- Affine substitution: `evalPoly (shiftPoly u w p) s = evalPoly p (u + w * s)`. -/
def shiftPoly (u w : Rat) : List Rat → List Rat
  | [] => []
  | c :: cs => addPoly [c] (mulLinear u w (shiftPoly u w cs))

/-- `(bernsteinAux a N j bs)[l] = a + (j + l + 1) / N * bs[l]`. -/
def bernsteinAux (a : Rat) (N : Nat) : Nat → List Rat → List Rat
  | _, [] => []
  | j, b :: bs => (a + ((j + 1 : Nat) : Rat) / (N : Rat) * b) :: bernsteinAux a N (j + 1) bs

/-- The Bernstein coefficients on `[0, 1]`. For `c` of length `N + 1`, `bernstein c` has
length `N + 1` and
`evalPoly c s = ∑ⱼ (bernstein c)[j] * (N choose j) * s ^ j * (1 - s) ^ (N - j)`.
So `evalPoly c s ≥ β` for `s ∈ [0, 1]` whenever every entry of `bernstein c` is `≥ β`.

The recursion: if `c = a :: cs` with `cs` of length `N` and Bernstein coefficients `β`
(degree `N - 1`), then `evalPoly c s = a + s * evalPoly cs s`, `a = a * ∑ⱼ B_{N,j}(s)`,
and `s * B_{N-1,j}(s) = (j + 1) / N * B_{N,j+1}(s)`, giving `b₀ = a` and
`b_{j+1} = a + (j + 1) / N * βⱼ`. -/
def bernstein : List Rat → List Rat
  | [] => []
  | a :: cs => a :: bernsteinAux a cs.length 0 (bernstein cs)

/-! ### Error bounds -/

/-- `absIntAux h hp k c = ∑ⱼ |c[j]| * hp * h ^ j / (k + j + 1)`. -/
def absIntAux (h : Rat) : Rat → Nat → List Rat → Rat
  | _, _, [] => 0
  | hp, k, c :: cs => Rat.abs c * hp / ((k + 1 : Nat) : Rat) + absIntAux h (hp * h) (k + 1) cs

/-- `absIntBound h c = ∑ₖ |c[k]| * h ^ (k + 1) / (k + 1)`, which bounds
`∫₀ʰ |evalPoly c z| dz` for `0 ≤ h`. -/
def absIntBound (h : Rat) (c : List Rat) : Rat :=
  absIntAux h h 0 c

/-- The residual numerator in the local variable `z = t - a`:
`evalPoly (residualNum n a p) z = (a + z) * p''(z) + p'(z) + n * (a + z) * p(z)`,
where `p(z) = evalPoly p z` and `p'`, `p''` are `evalPoly` of `derivPoly p` and
`derivPoly (derivPoly p)`. -/
def residualNum (n a : Rat) (p : List Rat) : List Rat :=
  addPoly (mulLinear a 1 (derivPoly (derivPoly p)))
    (addPoly (derivPoly p) (scalePoly n (mulLinear a 1 p)))

/-- A bound on `∫ₐ^{a+h} |R(t)| dt` for the residual `R(t) = Q(t - a) / t` of `p` on
`[a, a + h]`, where `Q = residualNum n a p`.

* `a > 0`: `some (absIntBound h Q / a)`, since `t ≥ a` there.
* `a = 0`: `some (absIntBound h Q.tail)` if `Q.headD 0 = 0` (then `R(t) = evalPoly Q.tail t`
  is a polynomial), and `none` otherwise. -/
def residualBound (n a : Nat) (h : Rat) (p : List Rat) : Option Rat :=
  let q := residualNum n a p
  if a = 0 then
    if q.headD 0 = 0 then some (absIntBound h q.tail) else none
  else
    some (absIntBound h q / a)

/-- `joinWeightAux n fuel q` is the least `q' ∈ (q, q + fuel]` with `n < q' * q'`, or
`q + fuel` if there is none. -/
def joinWeightAux (n : Nat) : Nat → Nat → Nat
  | 0, q => q
  | fuel + 1, q => if n < (q + 1) * (q + 1) then q + 1 else joinWeightAux n fuel (q + 1)

/-- The weight `q_n = ⌊√n⌋ + 1` of the value jump at a join. Soundness only uses
`n ≤ q_n * q_n`, which `checkRadius` checks. -/
def joinWeight (n : Nat) : Nat :=
  joinWeightAux n n 0

/-- The energy jump `|p'(h) - c₁| + q_n * |p(h) - c₀|` when passing from `p` on `[0, h]`
to the next polynomial with value `c₀` and derivative `c₁` at the join, `c = (c₀, c₁)`. -/
def joinBound (n : Nat) (h : Rat) (p : List Rat) (c : Rat × Rat) : Rat :=
  Rat.abs (evalPoly (derivPoly p) h - c.2) + (joinWeight n : Rat) * Rat.abs (evalPoly p h - c.1)

/-! ### The polynomial approximations -/

/-- The degree of the polynomial approximations. -/
def degree : Nat := 44

/-- `recurAux n a fuel k c₋ c c'`, with `(c₋, c, c') = (c_{k-1}, c_k, c_{k+1})`, lists the
next `fuel` coefficients `c_{k+2}, c_{k+3}, …` of the recurrence (15) of the method note,
which makes the coefficients of `z^k` in `residualNum n a` vanish:
`c_{k+2} = -((k+1)² c_{k+1} + n a c_k + n c_{k-1}) / (a (k+1)(k+2))` for `a ≠ 0`, and
`c_{k+2} = -n c_k / (k+2)²` for `a = 0`. Soundness does not depend on this
construction. -/
def recurAux (n a : Rat) : Nat → Nat → Rat → Rat → Rat → List Rat
  | 0, _, _, _, _ => []
  | fuel + 1, k, cm, c, c' =>
    let c'' :=
      if a = 0 then -(n * c) / (((k + 2) * (k + 2) : Nat) : Rat)
      else
        -((((k + 1) * (k + 1) : Nat) : Rat) * c' + n * a * c + n * cm) /
          (a * (((k + 1) * (k + 2) : Nat) : Rat))
    c'' :: recurAux n a fuel (k + 1) c c' c''

/-- The degree-`44` approximation of `J₀(√n t)` on `[a, a + h]` in the local variable
`z = t - a`, with starting values `p(0) = c₀` and `p'(0) = c₁`. Its first two
coefficients are `c₀` and `c₁` by definition. -/
def buildPoly (n a : Nat) (c₀ c₁ : Rat) : List Rat :=
  c₀ :: c₁ :: recurAux n a (degree - 1) 0 0 c₀ c₁

/-! ### Intervals and certificate data -/

/-- The number of polynomial intervals. -/
def numIntervals : Nat := 41

/-- Interval `k` starts at `2k`. -/
def intervalStart (k : Nat) : Nat := 2 * k

/-- Interval `k` has width `2`, except the last one, `[80, 81]`. -/
def intervalWidth (k : Nat) : Nat := if k + 1 < numIntervals then 2 else 1

/-- The certificate data of interval `k`. -/
def cert (k : Nat) : IntervalCert := certificate.getD k default

/-- The starting values `(c₀, c₁) = (m₀ / 2^32, m₁ / 2^32)` of the `i`-th approximation on
interval `k`. -/
def startValue (k : Nat) (i : Fin 11) : Rat × Rat :=
  let m := (cert k).start.getD i (0, 0)
  (mkRat m.1 4294967296, mkRat m.2 4294967296)

/-- The error bound `e / 2^64` of the `i`-th approximation on interval `k`. -/
def errorBound (k : Nat) (i : Fin 11) : Rat :=
  mkRat ((cert k).err.getD i 0) 18446744073709551616

/-- The approximation of `J₀(√n t)` for `n = kernelRadius i` on interval `k`, in the local
variable `z = t - intervalStart k`. -/
def approxPoly (k : Nat) (i : Fin 11) : List Rat :=
  buildPoly (kernelRadius i) (intervalStart k) (startValue k i).1 (startValue k i).2

/-- The approximation of `F` on interval `k`:
`evalPoly (combinedPoly k) z = 191 + ∑ᵢ Cᵢ * evalPoly (approxPoly k i) z`. -/
def combinedPoly (k : Nat) : List Rat :=
  (List.finRange 11).foldr (fun i acc => addPoly (scalePoly (kernelCoeff i) (approxPoly k i)) acc)
    [191]

/-- The budget for the weighted approximation error. -/
def errorBudget : Rat := 1 / 100

/-! ### The checks -/

/-- The error checks of the `i`-th approximation on interval `k`: exact starting values on
the first interval, `n ≤ q_n²`, and residual plus join error at most `errorBound k i`. -/
def checkRadius (k : Nat) (i : Fin 11) : Bool :=
  let n := kernelRadius i
  let p := approxPoly k i
  let h : Rat := intervalWidth k
  let join := if k + 1 < numIntervals then joinBound n h p (startValue (k + 1) i) else 0
  (if k = 0 then startValue k i = (1, 0) else true) &&
    decide (n ≤ joinWeight n * joinWeight n) &&
    match residualBound n (intervalStart k) h p with
    | some r => decide (r + join ≤ errorBound k i)
    | none => false

/-- `checkPiece P u v = true` implies `errorBudget ≤ evalPoly P z` for all `z ∈ [u, v]`:
`u < v`, and the Bernstein coefficients of `s ↦ P(u + (v - u) s)` on `[0, 1]` are all
`≥ errorBudget`. -/
def checkPiece (P : List Rat) (u v : Rat) : Bool :=
  decide (u < v) && (bernstein (shiftPoly u (v - u) P)).all (fun b => decide (errorBudget ≤ b))

/-- `checkPieces P h u vs = true` implies `errorBudget ≤ evalPoly P z` for all
`z ∈ [u, h]`: the breakpoints `vs = [v₁, …, v_m]` (`m ≥ 1`, `v_m = h`) split `[u, h]`
into the pieces `[u, v₁], [v₁, v₂], …, [v_{m-1}, v_m]`, each passing `checkPiece`. -/
def checkPieces (P : List Rat) (h : Rat) : Rat → List Rat → Bool
  | _, [] => false
  | u, [v] => checkPiece P u v && decide (v = h)
  | u, v :: w :: vs => checkPiece P u v && checkPieces P h v (w :: vs)

/-- The check of interval `k`: all error checks, and positivity of the combined polynomial
on `[0, intervalWidth k]` with the breakpoints `(cert k).breaks`. -/
def checkInterval (k : Nat) : Bool :=
  (List.finRange 11).all (checkRadius k) &&
    checkPieces (combinedPoly k) (intervalWidth k) 0 (cert k).breaks

/-- The weighted error `∑ᵢ |Cᵢ| * ∑_{k < numIntervals} errorBound k i`. -/
def totalError : Rat :=
  (List.finRange 11).foldr
    (fun i acc =>
      Rat.abs (kernelCoeff i) * (List.range numIntervals).foldr (fun k s => errorBound k i + s) 0
        + acc)
    0

/-- The weighted error is within the budget. -/
def checkErrorBudget : Bool :=
  decide (totalError ≤ errorBudget)

/-- The certificate check: every interval passes and the weighted error is within the
budget. -/
def check : Bool :=
  (List.range numIntervals).all checkInterval && checkErrorBudget

end Erdos188.LowerBound.Certificate
