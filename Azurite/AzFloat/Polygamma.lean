/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaBracket
import Azurite.AzFloat.Digamma

/-!
## The polygamma functions `ψ⁽ⁿ⁾(x)`

`polygammaPrecRound n x p mode` is the `n`-th derivative of the digamma function at a float
`x` (DLMF §5.15), rounded to precision `p` in `mode`, with the comparison against the exact
value; `polygamma n x` rounds to nearest at the precision of `x`.  `trigammaPrecRound` and
`trigamma` are the case `n = 1`: there is one algorithm for every `n ≥ 1`
(`AzFloat/PolygammaBracket.lean`), in which `n` only enters the terms of the series.

* **`n = 0`**: `digammaPrecRound`.
* **Special values, `n ≥ 1`.**  `ψ⁽ⁿ⁾(+∞) = 0`; `NaN` at `−∞` and at `NaN`.  At `x = 0`:
  `(−1)ⁿ⁺¹ ∞`, the limit from the right (there is no negative zero).  At the negative
  integers, where `ψ⁽ⁿ⁾(x) ∼ (−1)ⁿ⁺¹ n! / (x + m)ⁿ⁺¹`: `+∞` for an odd `n`, the limit from
  both sides, and `NaN` for an even `n`, where the sides disagree.
* **Tiny arguments** (`polygammaTiny?`): `ψ⁽ⁿ⁾(x) = (−1)ⁿ⁺¹ n!/xⁿ⁺¹ + ψ⁽ⁿ⁾(x + 1)`, and the
  leading term can be a float, so the loop would need about `(n + 1) |e|` bits; one test of
  `roundingPossible` on an enclosure of the leading term, widened by the bound
  `2ⁿ⁺² (n + 1)!` of the rest, settles the rounding at a cost independent of the exponent.
* **Everything else.**  Ziv's loop with fuel on `polygammaEncl`, from `polygammaStart` bits:
  `p + 32`, and for `|x| < 1` the `(n + 1) |e|` bits by which the leading term exceeds the
  rest (for the arguments, tiny but not tiny enough, that the test above leaves).
* **Contract** (`Equiv/Polygamma.lean`): `polygammaPrecRound_eq_or` — correctly rounded, or
  `(nan, .eq)` when the fuel runs out.
-/

namespace Azurite.AzFloat

/-- The bracket of `ψ⁽ⁿ⁾(x)` as a pair of `Roundable`s, the lower end strictly below the value;
the dummy bracket `[−1, 1]` when there is no enclosure at this level. -/
def polygammaApprox (n : Nat) (x : AzFloat) (pos : Bool) (p w : Nat) :
    Roundable × Roundable :=
  lnAbsGammaApproxOf (polygammaEnclFor n x pos p w) w

/-- **The one test of the tiny-argument path**, `n ≥ 1`, from a positive enclosure `Xa` of `|x|`
and the sign `s` of `x`, for `0 < |x| ≤ 1/4`: `H = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)` lies in
`(A, A + 2ⁿ⁺² (n + 1)!]` with `A = n!/xⁿ⁺¹` (`polygammaR_near_zero`), so it is rounded by one
test of `roundingPossible` on an enclosure of `A` widened upwards.  For an even `n` the result
is the negation of the rounding of `H` in the negated mode.  `none` when the test fails. -/
def polygammaTinyOf (n : Nat) (Xa : Encl) (s : Bool) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let W := p + zivGuardBits + 8
  let Q := Encl.div W (Encl.exact (ofAzNat (AzNat.factorial n))) (Encl.powBin W Xa (n + 1))
  let B := ofAzNat (AzNat.factorial (n + 1) <<< (n + 2))
  let neg := !s && n % 2 == 0
  let lo := if neg then -Q.2 else Q.1
  let hi := (addPrecRound (if neg then -Q.1 else Q.2) B W .Ceiling).1
  if n % 2 = 1 then
    roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p mode
  else
    (roundingPossible (fun P M => setPrecRound lo P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)

/-- **The tiny-argument path of `ψ⁽ⁿ⁾`**, `n ≥ 1`, for a finite `x` of sign `s` and exponent
`e ≤ −2`: `polygammaTinyOf` on `|x|`, which is exact — `A`, which can be a float, at the open
side.  Tried when the widening is below the last bit:
`(n + 1)(|e| − 2) ≥ p + 72 + lg (n + 1) + 2`.  `none` when the argument is not tiny or the test
fails. -/
def polygammaTiny? (n : Nat) (x : AzFloat) (s : Bool) (e : AzInt) (p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if e.sign = false ∧ 2 ≤ e.abs.toNat
      ∧ p + zivGuardBits + 10 + (n + 1).log2 ≤ (n + 1) * (e.abs.toNat - 2) then
    polygammaTinyOf n (Encl.exact x.abs) s p mode
  else none

/-- The first working precision of the loop for an argument of exponent `e`. -/
def polygammaStart (n : Nat) (e : AzInt) (p : Nat) : Nat :=
  max 64 (p + 32 + (if e.sign then 0 else (n + 1) * e.abs.toNat))

/-- `ψ⁽ⁿ⁾(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` where the function has no value, for `p = 0` unless the value is `0` or
infinite, or if the fuel runs out). -/
def polygammaPrecRound (n : Nat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if n = 0 then digammaPrecRound x p mode
  else
    match x with
    | nan => (nan, .eq)
    | infinity s => if s then (zero, .eq) else (nan, .eq)
    | zero => (infinity (n % 2 == 1), .eq)
    | finite s e q m hv =>
      if !s && isInteger (finite s e q m hv) then
        (if n % 2 = 1 then (infinity true, .eq) else (nan, .eq))
      else if p = 0 then (nan, .eq)
      else
        match polygammaTiny? n (finite s e q m hv) s e p mode with
        | some r => r
        | none =>
          zivLoop (polygammaApprox n (finite s e q m hv) s p) p mode lnGammaFuel
            (polygammaStart n e p)

/-- `ψ⁽ⁿ⁾(x)` rounded to nearest at the precision of `x`. -/
def polygamma (n : Nat) (x : AzFloat) : AzFloat :=
  (polygammaPrecRound n x (x.precision?.getD 1) .Nearest).1

/-- The trigamma function `ψ′(x)` rounded to precision `p` with `mode`. -/
def trigammaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  polygammaPrecRound 1 x p mode

/-- `ψ′(x)` rounded to nearest at the precision of `x`. -/
def trigamma (x : AzFloat) : AzFloat := polygamma 1 x

end Azurite.AzFloat
