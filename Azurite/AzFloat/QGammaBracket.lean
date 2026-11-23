/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesGBracket

/-!
## The bracket of the `q`-gamma function

`qGammaCoreOf A w` is the sign of `Γ_q(x)` and a positive enclosure of `|Γ_q(x)|` at Ziv level
`w`, for a base `q > 0`, `q ≠ 1`, and an argument `x` that is no pole; `none` when the level
gives nothing.  The base and the argument enter as a `QGammaIn` (enclosures at every working
precision), so that floats and rationals use the same bracket.

* **The base below `1`.**  For `q > 1` the bracket works with `p = 1/q`:
  `Γ_q(x) = Γ_p(x) q^((x−1)(x−2)/2)`.  For `0 < p < 1` (DLMF 5.18.4)

    `Γ_p(x) = (1 − p)^(1−x) ∏_{k ≥ 0} (1 − p^(k+1)) / (1 − p^(x+k))`.

* **The product.**  `K` factors are multiplied as enclosures (`qProdLoop`): the powers
  `t ← t p` from `p` and `r ← r p` from `p^x = exp(x ln p)`, the numerator `∏ (1 − t)`, the
  absolute value of the denominator `∏ |1 − r|`, and the parity of its negative factors — the
  sign of `Γ_q(x)` (the factors with `x + k < 0`).
* **The tails.**  `1 − a/(1 − p) ≤ (a; p)_∞ ≤ 1` for `0 ≤ a ≤ 1`, at `a = p^(K+1)` and
  `a = p^(x+K)`.  `K` (`qGammaTerms`) is taken with `K ln(1/p) ≥ 0.7 (w + 64) − ln(1 − p)`
  beyond the shift of the argument, so that both tails are within `2^(−w−64)` of `1`.
* **The logarithm.**  `ln |Γ_q(x)| = (x − 1) (−ln(1 − p)) + ln (the quotient)`, and for
  `q > 1` the term `((x − 1)(x − 2)/2) ln q` more; the core is its exponential
  (`gammaExpEncl`), as for `Γ` and the Barnes `G`-function.
* **Precision.**  `V = w + eb + 2 log₂ w + 64`, `eb` from the sizes of `x`, of `1/(1 − p)` and
  of `ln(1/p)` (`QGammaIn.eb`).

**Cost.**  `K ≈ 0.7 w / ln(1/p)` steps of six multiplications: the bracket is fast for a base
away from `1` and slow near it (`K` grows like `1/|q − 1|`), and for a negative `x` the shift
adds `|x|` steps.

The proofs: `Equiv/QGammaBracket.lean` (the enclosure, at every level) and
`Equiv/QGammaWidth.lean` (the width tends to `0`).  The functions are in `AzFloat/QGamma.lean`.
-/

namespace Azurite.AzFloat

/-- **The base and the argument of the bracket**, as they enter: `inv` (the base is `q > 1`
and `P` encloses `p = 1/q`; else `P` encloses `p = q < 1`), `P V` an enclosure of `p` of
relative width `6 · 2^(−V)`, `X V` and `absX V` enclosures of `x` and `|x|` of width
`O(2^(−V))`, `shift` a number with `x + shift ≥ 0` or so, and the padding `eb` of the
precision. -/
structure QGammaIn where
  inv : Bool
  P : Nat → Encl
  X : Nat → Encl
  absX : Nat → Encl
  shift : Nat
  eb : Nat

/-- `k` steps from `(t, r, n, d, neg)`: the powers `t ← t p`, `r ← r p`, the products
`n ← n (1 − t)`, `d ← d |1 − r|`, and the parity of the negative factors `1 − r`.  `none` when
a sign is not decided. -/
def qProdLoop (V : Nat) (P : Encl) : Nat → Encl → Encl → Encl → Encl → Bool →
    Option (Bool × Encl × Encl × Encl × Encl)
  | 0, t, r, n, d, neg => some (neg, t, r, n, d)
  | k + 1, t, r, n, d, neg =>
    match fracOfEncl (Encl.sub V (Encl.exact one) t),
      fracOfEncl (Encl.sub V (Encl.exact one) r) with
    | some (_, f), some (σ, g) =>
      qProdLoop V P k (Encl.mul V t P) (Encl.mul V r P) (Encl.mul V n f) (Encl.mul V d g)
        (neg != σ)
    | _, _ => none

/-- The number of factors at level `w`: beyond `shift`, with
`K ln(1/p) ≥ 0.7 (w + 64) − ln(1 − p)` (`lam` encloses `ln(1/p)`, `mu` encloses
`−ln(1 − p)`). -/
def qGammaTerms (V w : Nat) (lam mu : Encl) (shift : Nat) : Nat :=
  let Kq := Encl.div V (Encl.add V (Encl.nat ((w + 64) * 7 / 10 + 1)) mu) lam
  shift + azIntPos (truncToAzInt Kq.2) + 2

/-- The lower end of `1 − a/(1 − p)`, the lower bound of the tail `(a; p)_∞`. -/
def qGammaTailLo (V : Nat) (Q1 a : Encl) : AzFloat :=
  (Encl.sub V (Encl.exact one) (Encl.div V a Q1)).1

/-- The enclosure of `ln |Γ_q(x)|` from the output `o` of the loop: the two products with
their tails, the power of `1 − p`, and for `inv` the power of `q = 1/p`. -/
def qGammaFinL (V : Nat) (inv : Bool) (X aX Q1 lamc muc : Encl)
    (o : Bool × Encl × Encl × Encl × Encl) : Encl :=
  let R := Encl.div V (Encl.mul V o.2.2.2.1 (qGammaTailLo V Q1 o.2.1, one))
    (Encl.mul V o.2.2.2.2 (qGammaTailLo V Q1 o.2.2.1, one))
  let L0 := Encl.add V (Encl.mulPos V (Encl.sub V X (Encl.exact one)) muc) (lnOfEncl R V)
  if inv then
    let c2 := Encl.half (Encl.add V (Encl.sub V (Encl.mul V aX aX)
      (Encl.add V X (Encl.add V X X))) (Encl.nat 2))
    Encl.add V L0 (Encl.mulPos V c2 lamc)
  else L0

/-- `(neg, L)`: the sign of `Γ_q(x)` and an enclosure of `ln |Γ_q(x)|` at level `w`. -/
def qGammaLnEnclOf (A : QGammaIn) (w : Nat) : Option (Bool × Encl) :=
  let V := w + A.eb + 2 * w.log2 + 64
  let P := A.P V
  let X := A.X V
  let I := Encl.exact one
  let Q1 := Encl.sub V I P
  if lt zero Q1.1 then
    let lam := Encl.neg (lnOfEncl P V)
    let lamc : Encl := (clampNonneg lam.1, lam.2)
    let mu := Encl.neg (lnOfEncl Q1 V)
    let muc : Encl := (clampNonneg mu.1, mu.2)
    let K := qGammaTerms V w lam mu A.shift
    (gammaExpEncl false (Encl.mulPos V (Encl.neg X) lamc) V).bind fun r0 =>
      (qProdLoop V P K P r0 I I false).bind fun o =>
        if lt zero (qGammaTailLo V Q1 o.2.1) && lt zero (qGammaTailLo V Q1 o.2.2.1) then
          some (o.1, qGammaFinL V A.inv X (A.absX V) Q1 lamc muc o)
        else none
  else none

/-- The sign of `Γ_q(x)` and a positive enclosure of `|Γ_q(x)|` at Ziv level `w`. -/
def qGammaCoreOf (A : QGammaIn) (w : Nat) : Option (Bool × Encl) :=
  (qGammaLnEnclOf A w).bind fun r => (gammaExpEncl false r.2 w).map fun g => (r.1, g)

/-- The bracket of `Γ_q(x)` as a pair of `Roundable`s. -/
def qGammaApproxOf (A : QGammaIn) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf (qGammaCoreOf A w) w

end Azurite.AzFloat
