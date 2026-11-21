/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GlaisherKinkelin
import Azurite.AzFloat.BetaBracket
import Azurite.AzFloat.RoundToInteger

/-!
## The bracket of the Barnes `G`-function

`barnesGCore x w` is the sign of `G(x)` and a positive enclosure of `|G(x)|` at Ziv level `w`,
for a finite float `x` that is no zero of `G`; `none` when the level gives nothing.  It is the
exponential of `barnesGLnEncl`, an enclosure of `ln |G(x)|`:

* **The shift.**  `G(x + 1) = Γ(x) G(x)` gives
  `G(x) = G(Y) ∏_{j<N} (x + j)^(j+1) / Γ(Y)^N` for `Y = x + N`.  `N` (`barnesShift`) is taken
  with `Y > n + 1`, `n = glaisherArg w = 8 j`, `j = glaisherTerms w` — the argument and the
  number of terms of the Glaisher–Kinkelin constant.  A level whose shift exceeds `64 w` gives
  nothing (an astronomically negative `x` then ends with the fuel instead of running).
* **The expansion** (DLMF 5.17.5) at `y = Y − 1`:
  `ln G(y + 1) = y²/4 + y ln Γ(y + 1) − (y (y + 1)/2 + 1/12) ln y − ln A − μ(y)`, with
  `μ(y) = τ₁ − τ₂ + ⋯`, `τ_k = |B_{2k+2}| / (2k (2k + 1) (2k + 2) y^{2k})` — the terms of the
  constant (`glaisherTermEncl`), summed by `altSumLoop`; they envelop the remainder at every
  real `y > 0` (`Transcendental/BarnesG.lean`).  So

    `ln |G(x)| = y²/4 + (x − 1) ln Γ(Y) − (y (y + 1)/2 + 1/12) ln y − ln A − μ(y) + ln P`,

  `P = ∏_{j<N} |x + j|^(j+1)`.
* **The pieces.**  `ln Γ(Y)` by Stirling's series (`stirlingEnclWith`) and `½ ln (2π)`; `ln A`
  by `glaisherKinkelinLnEnclWith`; the three series share one table of tangent numbers.  `P`
  by `barnesProdLo`: lower bounds of the suffix products `S ← S |x + j|`, `W ← W S` for
  `j = N − 1, …, 0`, every product rounded down — `|x + j|` is formed exactly when it has at
  most `2V` bits (`barnesFrac`), so that `S |x + j|` is a short multiplication and `W S` the one
  full multiplication of a step — with the parity of the negative factors, which is the sign of
  `G(x)`; the upper bound of `P` comes from the count of the roundings (`glaisherUpper`, as for
  the products of the constant).
* **Precision.**  `V = w + 3 eb + 64`, `eb` the bits of `|x|` and of `N + n + 3`: the terms
  are of size `Y² ln Y`.

The proofs: `Equiv/BarnesGBracket.lean` (the enclosure, at every level) and
`Equiv/BarnesGWidth.lean` (the width tends to `0`).  The function is in `AzFloat/BarnesG.lean`.
-/

namespace Azurite.AzFloat

/-- The non-negative part of an integer, as a natural. -/
def azIntPos (e : AzInt) : Nat := if e.sign then e.abs.toNat else 0

/-- The shift `N` at `n` terms' argument: `x + N > n + 1`. -/
def barnesShift (x : AzFloat) (n : Nat) : Nat :=
  azIntPos ((AzNat.ofNat (n + 2)).toAzInt - truncToAzInt x)

/-- The sign of `x + k` (`true`: negative) and a lower bound of `|x + k|` within the factor
`e^(8u)`, `u = 2^(−V)`: the exact sum when it has at most `2V` bits, else the lower end of its
enclosure at `V` bits.  `none` when the sign is not decided. -/
def barnesFrac (V : Nat) (x : AzFloat) (k : Nat) : Option (Bool × AzFloat) :=
  let K := ofAzNat (AzNat.ofNat k)
  if exactSumPrec x K ≤ 2 * V then
    let d := exactAdd x K
    if lt zero d then some (false, d) else if lt d zero then some (true, -d) else none
  else (fracOfEncl (Encl.add V (Encl.exact x) (Encl.nat k))).map fun t => (t.1, t.2.1)

/-- From `(s, w, neg)` and `k`: the factors `|x + j|`, `j = k − 1, …, 0`, taken into lower
bounds of the suffix products `S ← S |x + j|`, `W ← W S`, every product rounded down, with
the parity of the negative factors of `∏ (x + j)^(j + 1)`.  `none` when a sign is not
decided. -/
def barnesProdLo (V : Nat) (x : AzFloat) : Nat → AzFloat → AzFloat → Bool →
    Option (Bool × AzFloat)
  | 0, _, w, neg => some (neg, w)
  | k + 1, s, w, neg =>
    match barnesFrac V x k with
    | none => none
    | some (σ, f) =>
      let s' := (mulPrecRound s f V .Floor).1
      barnesProdLo V x k s' (mulPrecRound w s' V .Floor).1 (neg != (σ && k % 2 == 0))

/-- `(neg, L)`: the sign of `G(x)` and an enclosure of `ln |G(x)|` at level `w`, for a finite
`x` that is not an integer `≤ 0`. -/
def barnesGLnEncl (x : AzFloat) (w : Nat) : Option (Bool × Encl) :=
  let j := glaisherTerms w
  let n := glaisherArg w
  let N := barnesShift x n
  let eb := max (azIntPos (expOf x)) ((N + n + 3).log2 + 1)
  let V := w + 3 * eb + 64
  let X := Encl.exact x
  let Y := Encl.add V X (Encl.nat N)
  let y := Encl.sub V Y (Encl.exact one)
  match barnesProdLo V x N one one false with
  | none => none
  | some (neg, wlo) =>
    let lnP := lnOfEncl (wlo, glaisherUpper V wlo (14 * N * N)) V
    let lny := lnOfEncl y V
    let T := AzNat.tangentNumbers (j + 1)
    let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
    let St := stirlingEnclWith V (j + 1) T Y tol
    let ln2pi := lnOfEncl (Encl.mul V (Encl.nat 2) (Encl.pi V)) V
    let lnGam := Encl.add V St (Encl.half ln2pi)
    let y2 := Encl.mul V y y
    let inv2 := Encl.div V (Encl.exact one) y2
    let S := altSumLoop V (glaisherTermEncl V T y2) inv2 tol (j - 1) 1 (Encl.mul V inv2 inv2)
      (Encl.exact zero)
    let lnA := glaisherKinkelinLnEnclWith w T
    let c := Encl.add V (Encl.half (Encl.mul V y Y)) (Encl.div V (Encl.exact one) (Encl.nat 12))
    let t2 := Encl.mulPos V (Encl.sub V X (Encl.exact one)) (clampNonneg lnGam.1, lnGam.2)
    let t3 := Encl.mulPos V c (clampNonneg lny.1, lny.2)
    some (neg, Encl.add V (Encl.sub V (Encl.sub V (Encl.sub V
      (Encl.add V (Encl.half (Encl.half y2)) t2) t3) lnA) S) lnP)

/-- The sign of `G(x)` and a positive enclosure of `|G(x)|` at Ziv level `w`. -/
def barnesGCore (x : AzFloat) (w : Nat) : Option (Bool × Encl) :=
  (barnesGLnEncl x w).bind fun r => (gammaExpEncl false r.2 w).map fun g => (r.1, g)

/-- The bracket of `G(x)` as a pair of `Roundable`s. -/
def barnesGApprox (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf (barnesGCore x w) w

end Azurite.AzFloat
