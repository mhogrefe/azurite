/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammer
import Azurite.AzFloat.PochhammerRatBracket
import Azurite.AzFloat.BetaRatBracket
import Azurite.AzFloat.GammaRatBracket

/-!
## The brackets of the generalized Pochhammer symbol of two rationals

The pieces of `genPochhammerRatPrecRound` (`AzFloat/GenPochhammerRat.lean`) that its Ziv
certificate (`Equiv/GenPochhammerRatCertificate.lean`) is about: the pole test and the
bracket of the reciprocal branch, the bracket of the quotient, and `recipPochRatSpecial`, the
test for the arguments at which `1/((x − n)ₙ)` is known not to be dyadic.
-/

namespace Azurite.AzFloat

/-- Is `x` an integer with `1 ≤ x ≤ n`? -/
def genPochRatPole (x : AzRat) (n : Nat) : Bool :=
  decide (x.den = 1) && x.sign && decide (x.num ≠ 0)
    && !(AzNat.compare x.num (AzNat.ofNat n) == .gt)

/-- The bracket of `1/((x − n)ₙ)` as a pair of `Roundable`s (`s = x − n`). -/
def recipPochRatApprox (s : AzRat) (n w : Nat) : Roundable × Roundable :=
  gammaApproxOf
    (recipPochCoreOf (lnGammaRatEncl s) (pochRatSplit s n) n
      (gammaLnBits (expOf (addPrecRound (ofAzRatRound s.abs 64 .Ceiling).1
        (ofAzNat (AzNat.ofNat n)) 64 .Ceiling).1)) w) w

/-- The bracket of `Γ(s)/Γ(x)` as a pair of `Roundable`s (`s = x + y`). -/
def genPochRatApprox (x s : AzRat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf
    (gammaQuotEnclOf (lnGammaRatEncl x) (lnGammaRatEncl s) (gammaRatExp x) (gammaRatExp s)
      (gammaRatFrac x) (gammaRatFrac s) w) w

/-- Is the denominator of `x` not a power of two, and `n ≥ 4`?  Then `1/((x − n)ₙ)` is not
dyadic (`not_isDyadic_inv_prod_rat`): one of the first four numerators has an odd prime
factor.  (For `n = 3` it can be: `1/((−2/3)(1/3)(4/3)) = −27/8`.) -/
def recipPochRatSpecial (x : AzRat) (n : Nat) : Bool := pochRatSpecial x && decide (4 ≤ n)

end Azurite.AzFloat
