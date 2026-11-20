/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.LnGammaBracket
import Azurite.AzFloat.Equiv.GammaExtremumCertificate

/-!
## The local extrema of the Gamma function

`gammaExtremumPrecRound n p mode` is `Γ(xₙ)`, the value of `Γ` at the `n`-th real zero `xₙ` of
`ψ = Γ′/Γ` (`AzFloat/PsiZero.lean`; DLMF §5.4(iii)), rounded to precision `p` in `mode`, with
the comparison against the exact value; `gammaExtremum n p` rounds to nearest.

* `Γ(x₀) = 0.8856…` is the minimum of `Γ` on `(0, ∞)`, at `x₀ = 1.4616…`.
* For `n ≥ 1`, `Γ(xₙ)` is the extremum of `Γ` between the poles `−n` and `−n + 1`: a local
  maximum (negative) for odd `n`, a local minimum (positive) for even `n`.
  `Γ(x₁) = −3.5446…`, `Γ(x₂) = 2.3024…`, `Γ(x₃) = −0.8881…`.

**Method.**  `Γ` on an enclosure of `xₙ`:

* `psiZeroEnclAt n V` is an enclosure of `xₙ` of width at most `2^(−V)`: the enclosure
  `psiZeroEncl` at the first of the Ziv levels `V, 2V, 4V, …` that is narrow enough.  The
  search has a certificate (`searchCertified`, `psiZeroTightAt_exists`), no fuel: the
  enclosures of the zeros converge.  The first level is the one in practice, with more than
  ten bits to spare.
* `gammaExtremumCore`: for `n = 0` the exponential of `lnGammaBracketEncl` on that enclosure;
  for `n ≥ 1` the reflection formula (`gammaReflect`), with `ln Γ` on the enclosure of
  `1 − xₙ ∈ (n, n + 1)` and the sine from the enclosure of `xₙ + n ∈ (0, 1)`
  (`gammaSinOfFrac`).  These are the pieces of `Γ` at a rational (`AzFloat/GammaRatBracket`).
* Ziv's loop with fuel on `gammaApproxOf`: nothing is known about the arithmetic nature of
  the extrema.

The enclosure of `xₙ` is carried to the full working precision.  (At an extremum the value
depends on the argument only to second order, so half the precision would do — but interval
arithmetic does not see that, and a proof would need a bound on `Γ″`.)

**Contract** (`Equiv/GammaExtremum.lean`): `gammaExtremumPrecRoundFuel_zivSpec` — sound at
every fuel, complete in the limit of the fuel wherever the value is no rounding boundary.
-/

namespace Azurite.AzFloat

/-- An enclosure of the `n`-th zero of `ψ` of width at most `2^(−V)`: `psiZeroEncl` at the
first of the levels `max 64 V · 2^f` where it is that narrow. -/
def psiZeroEnclAt (n V : Nat) : Encl :=
  searchCertified (psiZeroTightAt n V) (max 64 V)
    (psiZeroTightAt_exists n V _ (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 V)))

/-- `(neg, b)`: the sign of `Γ(xₙ)` and a positive enclosure `b` of `|Γ(xₙ)|` at Ziv level
`w`; `none` when the pieces do not give one at this level. -/
def gammaExtremumCore (n w : Nat) : Option (Bool × Encl) :=
  if n = 0 then
    let e := AzInt.ofInt 1
    let wL := w + gammaLnBits e
    (gammaExpEncl false (lnGammaBracketEncl (psiZeroEnclAt n (wL + 32)) e wL) w).map
      fun b => (false, b)
  else
    let e' := AzInt.ofInt ((n.log2 + 2 : Nat) : Int)
    let wL := w + gammaLnBits e'
    let Z := psiZeroEnclAt n (wL + 34)
    let A := Encl.add (wL + 36) Z (Encl.nat n)
    gammaReflect false
      (gammaExpEncl false
        (lnGammaBracketEncl (Encl.sub (wL + 36) (Encl.exact one) Z) e' wL) w)
      (if lt zero A.1 then gammaSinOfFrac false (AzInt.ofInt (-(n : Int))) A (w + 16) w
        else none) w

/-- The bracket of `Γ(xₙ)` as a pair of `Roundable`s. -/
def gammaExtremumApprox (n w : Nat) : Roundable × Roundable :=
  gammaApproxOf (gammaExtremumCore n w) w

/-- `Γ(xₙ)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`, or if the fuel runs out), with the fuel of the Ziv loop
explicit. -/
def gammaExtremumPrecRoundFuel (fuel n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop (gammaExtremumApprox n) p mode fuel (max 64 (p + 32))

/-- `Γ(xₙ)` rounded to precision `p` with `mode`, and the comparison with the exact value:
`gammaExtremumPrecRoundFuel` at the fuel `gammaFuel p`. -/
def gammaExtremumPrecRound (n p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  gammaExtremumPrecRoundFuel (gammaFuel p) n p mode

/-- `Γ(xₙ)`, the `n`-th local extremum of `Γ`, rounded to nearest at precision `p`. -/
def gammaExtremum (n p : Nat) : AzFloat := (gammaExtremumPrecRound n p .Nearest).1

end Azurite.AzFloat
