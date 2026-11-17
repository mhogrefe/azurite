/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnEncl
import Azurite.AzNat.TangentNumbers

/-!
## The bracket of `ln Γ(x)` for `x > 0`

Stirling's series (DLMF 5.11.1) with the argument shifted to where it converges fast:

  `ln Γ(x) = ln Γ(y) − ln (x (x+1) ⋯ (x+δ−1))`,   `y = x + δ`,
  `ln Γ(y) = (y − ½) ln y − y + ½ ln (2π) + ∑_{k=1}^{n−1} (−1)^(k+1) a_k / y^(2k−1) + r`,

`a_k = T_k / ((2k−1) (4^(2k) − 2^(2k)))` with the tangent numbers `T_k`
(`AzNat.tangentNumbers`), and the remainder `r` between `0` and the first omitted term
(`stirlingMu_eq_sum_add`, `Transcendental/LogGammaStirling.lean`).

* **The shift** (`lnGammaShift`): `y ≥ 2^L` with `2^L` between a quarter and half of the working precision
  (`lnGammaShiftExp`).  For `2^(E−1) ≤ x < 2^E`: nothing when `E > L`, `2^L − 2^(E−1)` when
  `1 ≤ E ≤ L`, `2^L` when `x < 1`.  The rising product is `δ` multiplications of enclosures
  (`risingEncl`), followed by one logarithm.
* **The series** (`stirlingSumLoop`): the terms are added, on enclosures, until one is below
  the tolerance or the table of tangent numbers ends; that term is not added but bounds the
  remainder, on its own side.  So the enclosure is valid whatever the number of terms is, and
  nothing about the speed of convergence enters the proof.
* Everything is evaluated on enclosures (`Encl`) at `V = w + 2L + 8 + 2⌊lg w⌋` bits (the
  last term for what the general logarithm loses beyond 2048 bits).  There are two logarithms
  (`lnOfEncl`): `ln y`, and `½ ln (2π / P²) = ½ ln (2π) − ln P` for the constant and the rising
  product `P` together.

`lnGammaBracket x e w` encloses `ln Γ(x)` for every positive float `x`, whatever `e` and `w ≥ 64`
are (`Equiv/LnGammaBracket.lean`); the exponent only chooses the shift.  Its width is not
bounded by a theorem: near the zeros `x = 1` and `x = 2` the terms cancel, and the caller
(`AzFloat/LnGamma.lean`) adds the bits that are lost there to the working precision.
-/

namespace Azurite.AzFloat

/-- The exponent `L` of the threshold `2^L` from which Stirling's series is used at Ziv level
`w`: `2^L ∈ (w/4, w/2]` (measured: a larger shift costs more in the rising product than it
saves in the series). -/
def lnGammaShiftExp (w : Nat) : Nat := (w / 4).log2 + 1

/-- The shift `δ` for a positive float `x` with `2^(e−1) ≤ x < 2^e`: `x + δ ≥ 2^L`, and `δ = 0`
only when `x ≥ 1`. -/
def lnGammaShift (x : AzFloat) (e : AzInt) (L : Nat) : Nat :=
  let s :=
    if e.sign then
      if L < e.abs.toNat then 0
      else if e.abs.toNat = 0 then 2 ^ L
      else 2 ^ L - 2 ^ (e.abs.toNat - 1)
    else 2 ^ L
  max s (if le one x then 0 else 1)

/-- The least `m ≥ m₀` (among `fuel` candidates) with `2 (w + 24) ≤ m (4E + 7 − ⌊lg m⁴⌋)`. -/
def lnGammaTermsGo (w E : Nat) : Nat → Nat → Nat
  | 0, m => m
  | fuel + 1, m =>
    if 2 * (w + 24) ≤ m * (4 * E + 7 - (m * m * m * m).log2) then m
    else lnGammaTermsGo w E fuel (m + 1)

/-- The number of tangent numbers at Ziv level `w` for an argument `2^(E−1) ≤ y < 2^E`.  The
term of index `m` of Stirling's series is about `(m / (π e y))^(2m)`, i.e. `m` times
`2 lg (π e 2^(E−1) / m) ≥ (4E + 7 − ⌊lg m⁴⌋) / 2` bits; the least `m` that reaches `w + 24`
bits, plus three.  (Too few only costs a wider bracket: the series is closed by its last
term whatever it is.) -/
def lnGammaTerms (w E : Nat) : Nat := lnGammaTermsGo w E (w / 2) 1 + 3

/-- The rising product `x (x+1) ⋯ (x+i−1)` on enclosures. -/
def risingEncl (V : Nat) (X : Encl) : Nat → Encl
  | 0 => Encl.exact one
  | i + 1 => Encl.mul V (risingEncl V X i) (Encl.add V X (Encl.nat i))

/-- The enclosure of `a_k / y^(2k−1)` from the tangent number table `T` (`T_k` at index
`k − 1`) and an enclosure `p` of `y^(−(2k−1))`. -/
def stirlingTermEncl (V : Nat) (T : Array AzNat) (k : Nat) (p : Encl) : Encl :=
  Encl.mul V
    (Encl.div V (Encl.exact (ofAzNat (T.getD (k - 1) 0)))
      (Encl.exact (ofAzNat
        (AzNat.mulNat (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k))) (2 * k - 1)))))
    p

/-- The sum of Stirling's series from the term `k` on: `p` encloses `y^(−(2k−1))`, `acc` the
terms before `k`, `inv2` encloses `y^(−2)`.  A term below `tol`, or the last one of the table,
is not added: the remainder lies between `0` and it, with its sign `(−1)^(k+1)`. -/
def stirlingSumLoop (V : Nat) (T : Array AzNat) (inv2 : Encl) (tol : AzFloat) :
    Nat → Nat → Encl → Encl → Encl
  | 0, k, p, acc =>
    let τ := stirlingTermEncl V T k p
    if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
    else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)
  | fuel + 1, k, p, acc =>
    let τ := stirlingTermEncl V T k p
    if le τ.2 tol then
      if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
      else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)
    else
      stirlingSumLoop V T inv2 tol fuel (k + 1) (Encl.mul V p inv2)
        (if k % 2 = 1 then Encl.add V acc τ else Encl.sub V acc τ)

/-- The enclosure of `μ(y) = ln Γ(y) − (y − ½) ln y + y − ½ ln (2π)` from an enclosure `Y` of
`y`, with `M ≥ 1` tangent numbers. -/
def stirlingMuEncl (V M : Nat) (Y : Encl) (tol : AzFloat) : Encl :=
  let T := AzNat.tangentNumbers M
  let inv := Encl.div V (Encl.exact one) Y
  stirlingSumLoop V T (Encl.mul V inv inv) tol (M - 1) 1 inv (Encl.exact zero)

/-- The enclosure of `ln Γ(y) − ½ ln (2π)` for `y ≥ 1` from an enclosure `Y` of `y`:
`(y − ½) ln y − y + μ(y)`. -/
def lnGammaStirlingEncl (V M : Nat) (Y : Encl) (tol : AzFloat) : Encl :=
  let lnY := lnOfEncl Y V
  let half := Encl.div V (Encl.exact one) (Encl.nat 2)
  let A := Encl.mul V (Encl.subNonneg V Y half) (clampNonneg lnY.1, lnY.2)
  Encl.add V (Encl.sub V A Y) (stirlingMuEncl V M Y tol)

/-- Half an enclosure (exact). -/
def Encl.half (a : Encl) : Encl := (a.1 <<< AzInt.ofInt (-1), a.2 <<< AzInt.ofInt (-1))

/-- The bracket of `ln Γ(x)` at Ziv level `w` for a positive finite float `x < 2^e`.  The
constant and the rising product `P` share one logarithm: `½ ln (2π) − ln P = ½ ln (2π / P²)`. -/
def lnGammaBracket (x : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  let L := lnGammaShiftExp w
  let V := w + 2 * L + 8 + 2 * w.log2
  let δ := lnGammaShift x e L
  let X := Encl.exact x
  let E := max (L + 1) (if e.sign then e.abs.toNat else 0)
  let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
  let twoPi := Encl.mul V (Encl.nat 2) (Encl.pi V)
  if δ = 0 then
    Encl.add V (lnGammaStirlingEncl V (lnGammaTerms w E) X tol) (Encl.half (lnOfEncl twoPi V))
  else
    let P := risingEncl V X δ
    Encl.add V (lnGammaStirlingEncl V (lnGammaTerms w E) (Encl.add V X (Encl.nat δ)) tol)
      (Encl.half (lnOfEncl (Encl.div V twoPi (Encl.mul V P P)) V))

end Azurite.AzFloat
