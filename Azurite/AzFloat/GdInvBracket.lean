/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosRat
import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.PiConstants
import Azurite.AzFloat.SinCosRatBracket
import Azurite.AzFloat.TanBracket

/-!
## The bracket of the inverse Gudermannian `gd⁻¹ x`

`gd⁻¹ x = ∫₀ˣ sec t dt` (DLMF 4.23.41) for `|x| < π/2`; it is odd, increasing, and tends to
`+∞` at `π/2`.  For `0 < a = |x| < π/2`,

  `gd⁻¹ a = ln ((1 + sin a) / cos a)`,

one joint sine–cosine evaluation and one logarithm.

* **The argument of the logarithm** `V = (1 + sin a)/cos a ≥ 1`: `gdInvNum` encloses
  `(1 + sin a)/2 ∈ [1/2, 1]` and the quotient step of the tangent, `tanOfSinCos`, divides by
  the enclosure of `cos a` — or returns its dummy bracket `[−1, 1]` when that enclosure
  contains `0`, which happens next to `π/2` until the working precision exceeds the number of
  leading zero bits of `π/2 − a`.  The result is doubled.
* **The logarithm of an enclosure** (`lnOfEncl`): `lnBracket` at the lower end `lo`, the upper
  end raised by `⌈(hi − lo)/lo⌉ ≥ ln (V/lo)`; the dummy bracket `[−1, 1]` (never accepted by
  `roundingPossible`) when `lo` is not a positive float.
* `gdInvBracket x ex w` is the composition and `gdInvApprox` the pair of `Roundable`s for the
  Ziv loop of `AzFloat/GdInv.lean` (negated and swapped for `x < 0`).  The logarithm has
  absolute accuracy and `gd⁻¹ a ≈ a` for a small `a`, so the loop starts with
  `leadingZeroBits` more bits.
* **The domain** (`gdInvInDomain`): a float of precision `q` is below `π/2` exactly when it is
  at most `⌊π/2⌋` rounded down to `q` bits, the largest `q`-bit float below `π/2` (which is
  irrational); floats below `1` need no test.

`gdInvRatBracket q w` is the same step `gdInvOfSinCos` on the rational bracket
`sinCosRatBracket`; the domain test `gdInvRatInDomain` reads the sign of `cos q` for
`1 < |q| < 2`.

The tiny-argument path is that of the tangent (`tanTiny?`): `|x| < gd⁻¹ |x| ≤ |x| + |x|³`.

The proofs are in `Equiv/GdInvBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `(1 + s)/2` from an enclosure of `s`, at precision `V`. -/
def gdInvNum (s : Encl) (V : Nat) : Encl :=
  ((addPrecRound one s.1 V .Floor).1 <<< AzInt.ofInt (-1),
    (addPrecRound one s.2 V .Ceiling).1 <<< AzInt.ofInt (-1))

/-- The logarithm of an enclosure `[lo, hi]` with a positive lower end, at Ziv level `w`:
`lnBracket` at `lo`, the upper end raised by `⌈(hi − lo)/lo⌉`; the dummy bracket `[−1, 1]` when
`lo` is not a positive float. -/
def lnOfEncl (y : Encl) (w : Nat) : Encl :=
  match y.1 with
  | finite true e q m hv =>
    let L := lnBracket (finite true e q m hv) e w
    let d := (divPrecRound (subPrecRound y.2 (finite true e q m hv) w .Ceiling).1
      (finite true e q m hv) w .Ceiling).1
    (L.1, (addPrecRound L.2 d w .Ceiling).1)
  | _ => (-one, one)

/-- The bracket of `ln ((1 + s)/c)` at Ziv level `w` from enclosures `b = ([s], [c])` of a
sine in `[0, 1]` and of a positive cosine, or the dummy bracket `[−1, 1]` when `[c]` contains
`0`. -/
def gdInvOfSinCos (b : Encl × Encl) (w : Nat) : Encl :=
  let Q := tanOfSinCos (gdInvNum b.1 (w + 12), b.2) (w + 12)
  lnOfEncl (Q.1 <<< AzInt.ofInt 1, Q.2 <<< AzInt.ofInt 1) w

/-- The bracket of `gd⁻¹ |x|` at Ziv level `w` for a finite `x` of exponent `ex` with
`|x| < π/2`, or the dummy bracket `[−1, 1]` when the enclosure of `cos x` contains `0`. -/
def gdInvBracket (x : AzFloat) (ex : AzInt) (w : Nat) : Encl :=
  gdInvOfSinCos (sinCosBracket x ex w) w

/-- The bracket of `gd⁻¹ x` as a pair of `Roundable`s: that of `gd⁻¹ |x|`, negated and swapped
when `neg` (`x < 0`). -/
def gdInvApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  negSwapApprox neg (gdInvBracket x ex w)

/-- `|x| < π/2` for a finite float `x` of exponent `e` and precision `q`: true for `e ≤ 0`;
otherwise `|x| ≤ ⌊π/2⌋` at `q` bits. -/
def gdInvInDomain (x : AzFloat) (e : AzInt) (q : Nat) : Bool :=
  if e.sign = false ∨ e.abs.toNat = 0 then true
  else le x.abs (piDiv2PrecRound q .Floor).1

/-! ### A rational argument -/

/-- The bracket of `gd⁻¹ |q|` at Ziv level `w` for a rational `q` with `|q| < π/2`, or the dummy
bracket: `gdInvOfSinCos` on the joint rational bracket `sinCosRatBracket`. -/
def gdInvRatBracket (q : AzRat) (w : Nat) : Encl := gdInvOfSinCos (sinCosRatBracket q w) w

/-- The bracket of `gd⁻¹ q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def gdInvRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  negSwapApprox (!q.sign) (gdInvRatBracket q w)

/-- `|q| < π/2` for a rational `q`: true for `|q| ≤ 1`, false for `|q| ≥ 2`, and in between
the sign of `cos q`, read off its correctly rounded value at one bit, rounded down (`cos q`
is irrational, hence not `0`, and rounding down keeps a positive number nonnegative). -/
def gdInvRatInDomain (q : AzRat) : Bool :=
  if q.num ≤ q.den then true
  else if (q >>> (1 : Nat)).den ≤ (q >>> (1 : Nat)).num then false
  else !(cosRatPrecRound q 1 .Floor).1.isNegative

end Azurite.AzFloat
