/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pochhammer
import Azurite.AzFloat.GammaRat
import Azurite.AzNat.Compare
import Azurite.AzNat.Pow2

/-!
## The bracket of Pochhammer's symbol of a rational

The pieces of `pochhammerRatPrecRound` (`AzFloat/PochhammerRat.lean`) that its Ziv certificate
(`Equiv/PochhammerRatCertificate.lean`) is about: the test for a vanishing factor, the exact
path, the split and the bracket `pochRatApprox`; and `pochRatSpecial`, the test for the
arguments at which the value is known not to be dyadic.
-/

namespace Azurite.AzFloat


/-- Does a factor of `(q)ₙ` vanish: is `q` an integer with `−n < q ≤ 0`? -/
def pochRatHasZero (q : AzRat) (n : Nat) : Bool :=
  decide (q.den = 1) && (decide (q.num = 0) || !q.sign)
    && (AzNat.compare q.num (AzNat.ofNat n) == .lt)

/-- **The exact path**: `pochIntQuot` for `n ≤ 128` and a short `q`, or a cheap product
(`pochExactCheap`); `none` otherwise. -/
def pochRatExact? (q : AzRat) (n p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if (n ≤ 128 ∧ q.num.size + q.den.size ≤ 2 * p + 1024)
      ∨ pochExactCheap (q.num.size + q.den.size) n p = true then
    some (pochIntQuot (AzInt.mkNorm q.sign q.num) q.den.toAzInt n p mode)
  else none

/-- The number of negative factors of `(q)ₙ`: `0` for `q ≥ 0`, `n` for `q ≤ −n`, and `⌈−q⌉`
in between. -/
def pochRatSplit (q : AzRat) (n : Nat) : Nat :=
  if q.sign then 0
  else if AzNat.ofNat n * q.den ≤ q.num then n
  else min n ((q.num / q.den).toNat + (if q.den = 1 then 0 else 1))

/-- `pochCoreOf` for a rational `q`: the sign of `(q)ₙ` and a positive enclosure of
`|(q)ₙ|`. -/
def pochRatCore (q : AzRat) (n w : Nat) : Option (Bool × Encl) :=
  pochCoreOf (lnGammaRatEncl q) (pochRatSplit q n) n
    (gammaLnBits (expOf (addPrecRound (ofAzRatRound q.abs 64 .Ceiling).1
      (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1)) w

/-- The bracket of `(q)ₙ` as a pair of `Roundable`s. -/
def pochRatApprox (q : AzRat) (n w : Nat) : Roundable × Roundable :=
  gammaApproxOf (pochRatCore q n w) w

/-- Is the denominator of `q` not a power of two?  Then `(q)ₙ`, a reduced fraction with the
denominator `denⁿ`, is not dyadic for `n ≥ 1` (`not_isDyadic_prod_rat`), so it is no rounding
boundary and Ziv's loop terminates on it (`pochRatApprox_cert`). -/
def pochRatSpecial (q : AzRat) : Bool := !q.den.isPowerOfTwo

end Azurite.AzFloat
