/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.SinCosBracket

/-!
## The bracket of the digamma function `ψ(x)`

**`x > 0`.**  The asymptotic series (DLMF 5.11.2) with the argument shifted to where it
converges fast, as for `ln Γ` (`AzFloat/LnGammaBracket.lean`, whose shift and number of terms
are reused):

  `ψ(x) = ψ(y) − ∑_{i<δ} 1/(x + i)`,   `y = x + δ`,
  `ψ(y) = ln y − 1/(2y) + ∑_{k=1}^{n−1} (−1)^k c_k / y^(2k) + r`,

`c_k = T_k / (4^(2k) − 2^(2k))` with the tangent numbers `T_k`, and the remainder `r` between
`0` and the first omitted term (`psiNu_eq_sum_add`, `Transcendental/DigammaStirling.lean`).
The loop `psiSumLoop` sums the series of `−ν(y) = ln y − 1/(2y) − ψ(y)`, whose signs are those
of Stirling's series, and closes it by the term it stops at.
The shift sum (`harmonicEncl`) takes one division for two terms, rounded down at the upper end
of the enclosure of `x`; the upper end of the sum is the same sum times a factor just above `1`.

**`x < 0`** (not an integer): the reflection formula (DLMF 5.5.4)
`ψ(x) = ψ(1 − x) − π cot (π x)`.  With an integer `k` next to `x` and `a = |x − k|`,
`cot (π x) = ± cot (π a)`; sine and cosine of `π a` come from one `sinCosBracket` at the lower
end of the enclosure of `π a`, widened by its width (`digammaCot`), the sine with the extra
bits that keep it relatively accurate next to a pole.  The cosine changes sign at the
half-integers, so the quotient and the product by `π` are taken with the signed operations
`Encl.divPos`, `Encl.mulPos`.

**Tiny arguments** (`digammaTiny?`): `ψ(x) = −1/x − γ + O(x)` lies within `2` of `−1/x`, which
can be a float, so the loop would need about `|e|` bits; the inequalities
`−1/x − 2 < ψ(x) < −1/x` (`psiR_near_zero`) settle the rounding by one test.

Nothing is assumed about the widths: `ψ` has a zero at `1.4616…` and one between any two
consecutive poles, where the terms cancel and Ziv's loop supplies the bits.  The proofs are in
`Equiv/DigammaBracket.lean`.
-/

namespace Azurite.AzFloat

/-! ### Signed products and quotients of enclosures -/

/-- `[a] · [b]` for an enclosure `[a]` of any sign and a nonnegative `[b]`. -/
def Encl.mulPos (W : Nat) (a b : Encl) : Encl :=
  ((mulPrecRound a.1 (if lt a.1 zero then b.2 else b.1) W .Floor).1,
    (mulPrecRound a.2 (if lt zero a.2 then b.2 else b.1) W .Ceiling).1)

/-- `[a] / [b]` for an enclosure `[a]` of any sign and a positive `[b]`. -/
def Encl.divPos (W : Nat) (a b : Encl) : Encl :=
  ((divPrecRound a.1 (if lt a.1 zero then b.1 else b.2) W .Floor).1,
    (divPrecRound a.2 (if lt zero a.2 then b.1 else b.2) W .Ceiling).1)

/-! ### The series for `x > 0` -/

/-- The enclosure of `c_k / y^(2k)` from the tangent number table `T` (`T_k` at index `k − 1`)
and an enclosure `p` of `y^(−2k)`. -/
def psiTermEncl (V : Nat) (T : Array AzNat) (k : Nat) (p : Encl) : Encl :=
  Encl.mul V
    (Encl.div V (Encl.exact (ofAzNat (T.getD (k - 1) 0)))
      (Encl.exact (ofAzNat (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k))))))
    p

/-- The sum of the series of `−ν(y)` from the term `k` on: `p` encloses `y^(−2k)`, `acc` the
terms before `k`, `inv2` encloses `y^(−2)`.  A term below `tol`, or the last one of the table,
is not added: the remainder lies between `0` and it, with its sign `(−1)^(k+1)`. -/
def psiSumLoop (V : Nat) (T : Array AzNat) (inv2 : Encl) (tol : AzFloat) :
    Nat → Nat → Encl → Encl → Encl
  | 0, k, p, acc =>
    let τ := psiTermEncl V T k p
    if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
    else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)
  | fuel + 1, k, p, acc =>
    let τ := psiTermEncl V T k p
    if le τ.2 tol then
      if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
      else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)
    else
      psiSumLoop V T inv2 tol fuel (k + 1) (Encl.mul V p inv2)
        (if k % 2 = 1 then Encl.add V acc τ else Encl.sub V acc τ)

/-- The enclosure of `ψ(y)` for `y > 0` from an enclosure `Y` of `y` with a positive lower
end, with `M ≥ 1` tangent numbers: `ln y − 1/(2y) − (−ν(y))`. -/
def digammaStirlingEncl (V M : Nat) (Y : Encl) (tol : AzFloat) : Encl :=
  let inv := Encl.div V (Encl.exact one) Y
  let inv2 := Encl.mul V inv inv
  let N := psiSumLoop V (AzNat.tangentNumbers M) inv2 tol (M - 1) 1 inv2 (Encl.exact zero)
  Encl.sub V (Encl.sub V (lnOfEncl Y V) (Encl.half inv)) N

/-- The lower sums of `∑_{i ≤ j < i+m} 1/(x + j)` from a float `b ≥ x`: `lo` and `up` are the
sum of the quotients below rounded down and up.  Two consecutive terms take one division,
`1/y + 1/(y + 1) = (2y + 1)/(y (y + 1))` at `y = ⌈b + i⌉`, with the numerator rounded down and
the denominator up; a last single term is `⌊1/y⌋`. -/
def harmonicLoop (V : Nat) (b : AzFloat) : Nat → Nat → AzFloat → AzFloat → AzFloat × AzFloat
  | 0, _, lo, up => (lo, up)
  | 1, i, lo, up =>
    let y := (addPrecRound b (ofAzNat (AzNat.ofNat i)) V .Ceiling).1
    let q := (divPrecRound one y V .Floor).1
    ((addPrecRound lo q V .Floor).1, (addPrecRound up q V .Ceiling).1)
  | m + 2, i, lo, up =>
    let y := (addPrecRound b (ofAzNat (AzNat.ofNat i)) V .Ceiling).1
    let N := (addPrecRound y (addPrecRound y one V .Floor).1 V .Floor).1
    let D := (mulPrecRound y (addPrecRound y one V .Ceiling).1 V .Ceiling).1
    let q := (divPrecRound N D V .Floor).1
    harmonicLoop V b m (i + 2) (addPrecRound lo q V .Floor).1 (addPrecRound up q V .Ceiling).1

/-- The sum `∑_{j<i} 1/(x + j)` from an enclosure `X = [a, b]` of `x > 0`.  Every quotient is
taken once, rounded down, at the upper end `b` (`harmonicLoop`): each is a lower bound of its
terms, and within the factor `(b/a) ((1 + ε)/(1 − ε))³`, `ε = 2^(1−V)`, of them — so the upper
end is the sum of the quotients times `⌈b/a⌉ (1 + 2^(6−V))`, and the sum costs one division
for two terms instead of four. -/
def harmonicEncl (V : Nat) (X : Encl) (i : Nat) : Encl :=
  let s := harmonicLoop V X.2 i 0 zero zero
  let K := (mulPrecRound (divPrecRound X.2 X.1 V .Ceiling).1
    (addPrecRound one (powerOf2 (AzInt.ofInt 6 - (AzNat.ofNat V).toAzInt)) V .Ceiling).1 V
    .Ceiling).1
  (s.1, (mulPrecRound s.2 K V .Ceiling).1)

/-- The bracket of `ψ(x)` at Ziv level `w` from an enclosure `X` of `x > 0` (positive lower
end) with `x < 2^e`: the shift, the number of terms and the working precision of
`lnGammaBracketEncl`. -/
def digammaPosEncl (X : Encl) (e : AzInt) (w : Nat) : Encl :=
  let L := lnGammaShiftExp w
  let V := w + 2 * L + 8 + 2 * w.log2
  let δ := lnGammaShift X.1 e L
  let E := max (L + 1) (if e.sign then e.abs.toNat else 0)
  let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
  if δ = 0 then digammaStirlingEncl V (lnGammaTerms w E) X tol
  else
    Encl.sub V (digammaStirlingEncl V (lnGammaTerms w E) (Encl.add V X (Encl.nat δ)) tol)
      (harmonicEncl V X δ)

/-! ### The reflection formula for `x < 0` -/

/-- The enclosure of `π cot (π a)` from a positive enclosure `A` of `a`; `none` when the
enclosure of `sin (π a)` is not positive. -/
def digammaCot (A : Encl) (W w : Nat) : Option Encl :=
  let Y := Encl.mul W A (Encl.pi W)
  let B := sinCosBracket Y.1 (expOf Y.1) (w + sinLostBits Y.1)
  let d := Encl.exact (subPrecRound Y.2 Y.1 W .Ceiling).1
  let S := Encl.widen W B.1 d
  let C := Encl.widen W B.2 d
  if lt zero S.1 then some (Encl.mulPos W (Encl.divPos W C S) (Encl.pi W)) else none

/-- The reflection formula on enclosures: from the sign `σ` of `x − k` (`true`: negative) with
a positive enclosure `A` of `|x − k|`, `k` an integer, and an enclosure `P` of `ψ(1 − x)`, the
enclosure of `ψ(x) = ψ(1 − x) ∓ π cot (π |x − k|)`. -/
def digammaReflect (F : Option (Bool × Encl)) (P : Encl) (w : Nat) : Option Encl :=
  match F with
  | none => none
  | some (σ, A) =>
    (digammaCot A (w + 16) w).map fun T =>
      if σ then Encl.add (w + 16) P T else Encl.sub (w + 16) P T

/-- An enclosure of `ψ(x)` at Ziv level `w` for a finite `x < 0` of exponent `e` that is not an
integer; `none` when the pieces do not give one at this level. -/
def digammaNegEncl (x : AzFloat) (e : AzInt) (w : Nat) : Option Encl :=
  let e' := (if e.sign then e else 0) + 1
  let X₁ := Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one)
  digammaReflect (gammaFracEncl x (gammaNearInt x) (w + 16)) (digammaPosEncl X₁ e' w) w

/-- An enclosure of `ψ(x)` at Ziv level `w` for a finite `x < 2^e` that is positive (`pos`) or
negative and not an integer. -/
def digammaEncl (x : AzFloat) (e : AzInt) (pos : Bool) (w : Nat) : Option Encl :=
  if pos then some (digammaPosEncl (Encl.exact x) e w) else digammaNegEncl x e w

/-! ### Tiny arguments -/

/-- **The tiny-argument path of `ψ`** for a finite `x` of exponent `e`: when
`e ≤ −(p + 72)`, `−ψ(x)` lies in `(1/x, 1/x + 2)`, so it is rounded (in the negated mode, the
result negated) by one test of `roundingPossible` on `[⌊1/x⌋, ⌈⌈1/x⌉ + 2⌉]` at `p + 72` bits.
The negation puts `1/x`, which is a float when `x` is a power of two, at the open side of the
half-open test.  `none` when the argument is not tiny or the test fails. -/
def digammaTiny? (x : AzFloat) (e : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat then
    let W := p + zivGuardBits + 8
    let lo := (divPrecRound one x W .Floor).1
    let hi := (addPrecRound (divPrecRound one x W .Ceiling).1 (ofAzNat (AzNat.ofNat 2)) W
      .Ceiling).1
    (roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

end Azurite.AzFloat
