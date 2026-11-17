/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaBracket
import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.TanBracket
import Azurite.AzFloat.Compare
import Azurite.AzFloat.Sum
import Azurite.AzFloat.Ziv
import Azurite.AzFloat.Div
import Azurite.AzFloat.RoundToInteger
import Azurite.AzInt.Parity

/-!
## The brackets of `Γ(x)` and `1/Γ(x)`

Both functions come from the bracket of `ln Γ` (`AzFloat/LnGammaBracket.lean`).

* **`x > 0`**: `Γ(x) = exp (ln Γ(x))`, `1/Γ(x) = exp (−ln Γ(x))`.  The bracket of `ln Γ(x)` is
  taken at `gammaLnBits` more bits than the Ziv level, the size of `|ln Γ(x)|`, since the
  exponential turns its absolute error into a relative one.
* **`x < 0`** (not an integer): the reflection formula (DLMF 5.5.3)
  `Γ(x) Γ(1 − x) = π / sin (π x)`, so with `T = |sin (π x)| Γ(1 − x)`,
  `|Γ(x)| = π / T` and `|1/Γ(x)| = T / π`, the sign that of `sin (π x)`.
  - `Γ(1 − x)` is the exponential of `lnGammaBracketEncl` at the enclosure of `1 − x`.
  - **The sine** (`gammaSinEncl`) keeps its relative accuracy next to the integers and next to
    `0`: with an integer `k` near `x` and `d = x − k` (an exact difference rounded once),
    `sin (π x) = (−1)^k sin (π d)`, and `sin (π |d|)` is `sinBracket` at the lower end of the
    enclosure of `π |d|`, widened by the width of that enclosure (the sine is 1-Lipschitz).

Nothing here is assumed about the size of the errors.  Each piece returns `none` when it cannot
deliver a positive enclosure (a bracket of `ln Γ` wider than `1`, a sine whose lower end is not
positive), and `gammaApprox` then hands the Ziv loop the dummy bracket `[−1, 1]`, which is
never accepted.  Otherwise the enclosure is made strict on both sides (`gammaStrict`) and
negated when the value is negative.

**Tiny arguments** (`gammaTiny?`, `reciprocalGammaTiny?`): `Γ(x) = 1/x − γ + O(x)` and
`1/Γ(x) = x + γ x² + O(x³)` lie within a relative `|x|` of `1/x` and of `x`, which can be
floats, so the loop would need about `|e|` bits; the inequalities `1/x − 2 < Γ(x) < 1/x` and
`x < 1/Γ(x) < x + x²` (`Transcendental/GammaNearZero.lean`) settle the rounding by one test.

The proofs are in `Equiv/GammaBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The bits of `|ln Γ(y)|` for `y < 2^e`: about `e + lg e` for a large `y`, `lg |e|` for a
tiny one. -/
def gammaLnBits (e : AzInt) : Nat :=
  if e.sign then e.abs.toNat + e.abs.toNat.log2 + 2 else e.abs.toNat.log2 + 2

/-- The enclosure of `exp v` from an enclosure `M` of `v`; `none` when `M` is wider than `1` or
the result has no positive lower end. -/
def expEnclPos? (M : Encl) (w : Nat) : Option Encl :=
  if le (subPrecRound M.2 M.1 64 .Ceiling).1 one then
    if lt zero (expOfBracket M w).1 then some (expOfBracket M w) else none
  else none

/-- The enclosure of `exp v` (`neg = false`) or `exp (−v)` from an enclosure `L` of `v`. -/
def gammaExpEncl (neg : Bool) (L : Encl) (w : Nat) : Option Encl :=
  expEnclPos? (if neg then Encl.neg L else L) w

/-- An integer next to `x`: the truncation, or one less when `x` is more than `1/2` below
it. -/
def gammaNearInt (x : AzFloat) : AzInt :=
  let k := truncToAzInt x
  if lt (subPrecRound x (ofAzInt k) 64 .Nearest).1 (-(one <<< AzInt.ofInt (-1))) then k - 1
  else k

/-- The sign of `x − k` and the enclosure of `|x − k|`, for an integer `k`; `none` when the
sign is not decided (`x = k`). -/
def gammaFracEncl (x : AzFloat) (k : AzInt) (W : Nat) : Option (Bool × Encl) :=
  let D := Encl.sub W (Encl.exact x) (Encl.exact (ofAzInt k))
  if lt zero D.1 then some (false, D)
  else if lt D.2 zero then some (true, Encl.neg D)
  else none

/-- The enclosure of `sin y` from an enclosure `Y` of `y ≥ 0`: `sinBracket` at the lower end,
widened by the width of `Y`. -/
def sinOfEncl (Y : Encl) (W w : Nat) : Encl :=
  Encl.widen W (sinBracket Y.1 (expOf Y.1) w)
    (Encl.exact (subPrecRound Y.2 Y.1 W .Ceiling).1)

/-- The bits by which `y` is below `1`: the sine bracket is taken that much finer, since its
width is absolute and `sin y ≈ y` (next to a pole of `Γ`). -/
def sinLostBits (y : AzFloat) : Nat :=
  if (expOf y).sign then 0 else (expOf y).abs.toNat

/-- `(neg, S)` from the sign `σ` of `x − k` (`true`: negative), the integer `k` and a positive
enclosure `A` of `|x − k|`: `S` a positive enclosure of `|sin (π x)|` and `neg` the sign of
`sin (π x)` (`true`: negative); `none` when the enclosure of the sine is not positive. -/
def gammaSinOfFrac (σ : Bool) (k : AzInt) (A : Encl) (W w : Nat) : Option (Bool × Encl) :=
  let Y := Encl.mul W A (Encl.pi W)
  let S := sinOfEncl Y W (w + sinLostBits Y.1)
  if lt zero S.1 then some (σ != k.isOdd, S) else none

/-- `(neg, S)` with `S` a positive enclosure of `|sin (π x)|` and `neg` the sign of
`sin (π x)` (`true`: negative); `none` when no positive enclosure is found (`x` an integer, or
too few bits). -/
def gammaSinEncl (x : AzFloat) (W w : Nat) : Option (Bool × Encl) :=
  let k := gammaNearInt x
  match gammaFracEncl x k W with
  | none => none
  | some (σ, A) => gammaSinOfFrac σ k A W w

/-- The reflection formula on enclosures: from a positive enclosure `G` of `Γ(1 − x)` and the
sign and a positive enclosure `S` of `|sin (π x)|`, the sign and a positive enclosure of
`|Γ(x)| = π / (|sin πx| Γ(1 − x))` (`recip = false`) or of its reciprocal. -/
def gammaReflect (recip : Bool) (G : Option Encl) (S : Option (Bool × Encl)) (w : Nat) :
    Option (Bool × Encl) :=
  match G, S with
  | some G, some (neg, S) =>
    let T := Encl.mul (w + 16) S G
    some (neg, if recip then Encl.div (w + 16) T (Encl.pi (w + 16))
      else Encl.div (w + 16) (Encl.pi (w + 16)) T)
  | _, _ => none

/-- `(neg, b)`: the sign of `Γ(x)` and a positive enclosure `b` of `|Γ(x)|` (`recip = false`)
or `|1/Γ(x)|` (`recip = true`), for a finite `x < 2^e` that is positive (`pos`) or negative and
not an integer; `none` when the pieces do not give one at this level. -/
def gammaCore (recip : Bool) (x : AzFloat) (e : AzInt) (pos : Bool) (w : Nat) :
    Option (Bool × Encl) :=
  if pos then
    (gammaExpEncl recip (lnGammaBracket x e (w + gammaLnBits e)) w).map fun b => (false, b)
  else
    let e' := (if e.sign then e else 0) + 1
    let wL := w + gammaLnBits e'
    let X₁ := Encl.add (wL + 32) (Encl.exact (-x)) (Encl.exact one)
    gammaReflect recip (gammaExpEncl false (lnGammaBracketEncl X₁ e' wL) w)
      (gammaSinEncl x (w + 16) w) w

/-- A positive enclosure made strict: the lower end lowered and the upper end raised by a
`2^(−2w)`-th of themselves. -/
def gammaStrict (b : Encl) (w : Nat) : Encl :=
  ((subPrecRound b.1 (b.1 <<< (-(AzNat.ofNat (2 * w)).toAzInt)) (2 * w + 64) .Floor).1,
    (addPrecRound b.2 (b.2 <<< (-(AzNat.ofNat (2 * w)).toAzInt)) (2 * w + 64) .Ceiling).1)

/-- The bracket of `gammaApprox` from the answer of the core: strict on both sides, or the
dummy bracket `[−1, 1]` when there is none. -/
def gammaApproxOf (c : Option (Bool × Encl)) (w : Nat) : Roundable × Roundable :=
  match c with
  | none => negSwapApprox false (-one, one)
  | some (neg, b) => negSwapApprox neg (gammaStrict b w)

/-- The bracket of `Γ(x)` or `1/Γ(x)` as a pair of `Roundable`s, strict on both sides; the
dummy bracket `[−1, 1]` when `gammaCore` gives nothing. -/
def gammaApprox (recip : Bool) (x : AzFloat) (e : AzInt) (pos : Bool) (w : Nat) :
    Roundable × Roundable :=
  gammaApproxOf (gammaCore recip x e pos w) w

/-- The fuel of the Ziv loops for `Γ` and `1/Γ`: ten doublings of the working precision. -/
def gammaFuel : Nat := 10

/-- **The tiny-argument path of `Γ`** for a finite `x` of exponent `e` and precision `q`: when
`e ≤ −(p + 72)`, `−Γ(x)` lies in `(−1/x, −1/x + 2)`, so it is rounded (in the negated mode, the
result negated) by one test of `roundingPossible` on `[⌊−1/x⌋, ⌈⌈−1/x⌉ + 2⌉]` at `p + q + 72`
bits.  The negation puts `−1/x`, which is a float when `x` is a power of two, at the open side
of the half-open test: the Ziv loop would need about `|e|` bits to see on which side of it the
value lies.  `none` when the argument is not tiny or the test fails. -/
def gammaTiny? (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat then
    let W := p + q + zivGuardBits + 8
    let lo := (divPrecRound (-one) x W .Floor).1
    let hi := (addPrecRound (divPrecRound (-one) x W .Ceiling).1 (ofAzNat (AzNat.ofNat 2)) W
      .Ceiling).1
    (roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

/-- **The tiny-argument path of `1/Γ`** for a finite `x` of exponent `e` and precision `q`:
when `e ≤ −(max p q + 72)`, `1/Γ(x)` lies in `(x, x + x²)`, so it is rounded by one test of
`roundingPossible` on `[x, ⌈x + |x| 2^e⌉]`, the exact end `x` at the open side.  `none` when
the argument is not tiny or the test fails. -/
def reciprocalGammaTiny? (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let w := max p q + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let hi := (addPrecRound x (x.abs <<< e) (w + 8) .Ceiling).1
    roundingPossible (fun P M => setPrecRound x P M) (fun P M => setPrecRound hi P M) p mode
  else none

/-- Is `x` a positive integer at most `bound`? -/
def gammaSmallInt (x : AzFloat) (bound : Nat) : Bool :=
  isInteger x && lt zero x && le x (ofAzNat (AzNat.ofNat bound))

end Azurite.AzFloat
