/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaConstants
import Azurite.AzFloat.GammaBracket
import Azurite.AzNat.SumProduct
import Azurite.AzNat.Pow

/-!
## `Γ` at the rationals with denominator `2, 3, 4, 6`, through the constants

For `0 < r < d`, `d ∈ {2, 3, 4, 6}`, the value `Γ(r/d)` is a closed form in `π`, `Γ(1/4)` and
`Γ(1/3)` (`gammaBaseEncl`):

  `Γ(1/2) = √π`,  `Γ(3/4) = π √2 / Γ(1/4)`,  `Γ(2/3) = 2π / (√3 Γ(1/3))`,
  `Γ(1/6) = √3 Γ(1/3)² / (∛2 √π)`,  `Γ(5/6) = 2π / Γ(1/6)`

(reflection and duplication), the two constants by the AGM (`AzFloat/GammaConstants.lean`).
The integer shifts are exact rational factors, by the recurrence:

  `Γ(n + r/d) = Γ(r/d) · ∏_{j<n} (r + j d) / d^n`,
  `Γ(−(n + r/d)) = (−1)^(n+1) Γ(1 − r/d) · d^(n+1) / ∏_{j≤n} (r + j d)`,

the products by a balanced tree (`AzNat.product`), once per call.  This is several times
faster than Stirling's series at 53 bits and a hundred times at 5000 bits.

`gammaSpecialFast?` runs Ziv's loop with fuel on these brackets (the widths of the interval
AGM are not proven) when the shift is at most `gammaIntBound p`; the callers
(`gammaPrecRound`, `gammaRatPrecRound` and the reciprocals) hand a `NaN` over to the certified
loop on Stirling's series, so their results stay unconditionally correct.

The proofs are in `Equiv/GammaSpecial.lean`.
-/

namespace Azurite.AzFloat

/-- `∏_{j<m} (r + j d)`. -/
def gammaAP (r d m : Nat) : AzNat :=
  AzNat.product ((List.range m).map fun j => AzNat.ofNat (r + j * d))

/-- An enclosure of `Γ(1/6) = √3 Γ(1/3)² / (∛2 √π)` at Ziv level `w`. -/
def gammaOneSixthEncl (w : Nat) : Encl :=
  let W := w + 32
  let B := gammaOneThirdEncl w
  Encl.div W (Encl.mul W (Encl.sqrt W (Encl.nat 3)) (Encl.mul W B B))
    (Encl.mul W (Encl.cbrt W (Encl.nat 2)) (Encl.sqrt W (Encl.pi W)))

/-- An enclosure of `Γ(r/d)` at Ziv level `w`, for `0 < r < d`, `d ∈ {2, 3, 4, 6}` and `r/d`
in lowest terms or equal to `1/2`. -/
def gammaBaseEncl (r d w : Nat) : Encl :=
  let W := w + 32
  if 2 * r = d then Encl.sqrt W (Encl.pi W)
  else if d = 4 then
    if r = 1 then gammaOneQuarterEncl w
    else Encl.div W (Encl.mul W (Encl.pi W) (Encl.sqrt W (Encl.nat 2))) (gammaOneQuarterEncl w)
  else if d = 3 then
    if r = 1 then gammaOneThirdEncl w
    else Encl.div W (Encl.mul W (Encl.nat 2) (Encl.pi W))
      (Encl.mul W (Encl.sqrt W (Encl.nat 3)) (gammaOneThirdEncl w))
  else if r = 1 then gammaOneSixthEncl w
  else Encl.div W (Encl.mul W (Encl.nat 2) (Encl.pi W)) (gammaOneSixthEncl w)

/-- An enclosure of `Γ(r/d) · num / den`, or of its reciprocal, for positive floats `num`,
`den` (exact integers). -/
def gammaSpecialEncl (recip : Bool) (r d : Nat) (num den : AzFloat) (w : Nat) : Encl :=
  let W := w + 32
  let N := Encl.mul W (gammaBaseEncl r d w) (Encl.exact num)
  if recip then Encl.div W (Encl.exact den) N else Encl.div W N (Encl.exact den)

/-- The bracket of `± Γ(r/d) · num / den` or of its reciprocal as a pair of `Roundable`s. -/
def gammaSpecialApprox (recip neg : Bool) (r d : Nat) (num den : AzFloat) (w : Nat) :
    Roundable × Roundable :=
  gammaApproxOf (some (neg, gammaSpecialEncl recip r d num den w)) w

/-- **`Γ(± n/d)` (`recip = false`) or its reciprocal through the constants**, for a numerator
`n` not a multiple of `d ∈ {2, 3, 4, 6}` (`pos`: the sign), rounded to precision `p` with
`mode`.  `none` when the integer part exceeds `gammaIntBound p`; `(nan, .eq)` if the fuel runs
out. -/
def gammaSpecialFast? (recip pos : Bool) (n : AzNat) (d : Nat) (p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let Q := n / AzNat.ofNat d
  if Q ≤ AzNat.ofNat (gammaIntBound p) then
    let qu := Q.toNat
    let r := (n % AzNat.ofNat d).toNat
    some (
      if pos then
        zivLoop (gammaSpecialApprox recip false r d (ofAzNat (gammaAP r d qu))
          (ofAzNat ((AzNat.ofNat d).pow qu))) p mode (gammaFuel p) (max 64 (p + 32))
      else
        zivLoop (gammaSpecialApprox recip ((qu + 1) % 2 == 1) (d - r) d
          (ofAzNat ((AzNat.ofNat d).pow (qu + 1))) (ofAzNat (gammaAP r d (qu + 1)))) p mode
          (gammaFuel p) (max 64 (p + 32)))
  else none

end Azurite.AzFloat
