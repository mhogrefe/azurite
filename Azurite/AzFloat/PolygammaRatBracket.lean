/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaBracket
import Azurite.AzFloat.GammaRatBracket
import Azurite.AzFloat.LnGamma

/-!
## The bracket of the polygamma functions of a rational

The enclosures of `ψ⁽ⁿ⁾(q)` for an `AzRat` `q` (the pieces of the float function,
`AzFloat/PolygammaBracket.lean`, on the roundings of rationals), and `polygammaRatSpecial`,
the arguments with a known irrational value.  The functions are in
`AzFloat/PolygammaRat.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `H(q) = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(q)` at Ziv level `w` for a rational `q < 0` that is not
an integer, as `polygammaNegEncl`: with `m = −⌊q⌋`, so that `u = q + m` and `1 − u` lie in
`(0, 1)`, the recurrence in positive terms for `m ≤ 2^L`, and three positive arguments
beyond.  `u`, `1 − u` and `1 − q` are exact rationals, rounded once.  (`none` only if the
signs are not those of such a `q`.) -/
def polygammaRatNegEncl (n : Nat) (q : AzRat) (w : Nat) : Option Encl :=
  let k := (q.round .Floor).1
  let m := k.abs.toNat
  let u := q - k.toAzRat
  let a₂ := 1 - u
  if k.sign = false ∧ u.num ≠ 0 ∧ u.sign = true ∧ a₂.num ≠ 0 ∧ a₂.sign = true then
    let V := polyWork n w
    let W := w + 32
    let U := lnGammaRatEncl u V
    let A₂ := lnGammaRatEncl a₂ V
    if m ≤ 2 ^ lnGammaShiftExp w then
      let T := Encl.mul V (Encl.exact (ofAzNat (AzNat.factorial n))) (polyShiftSum V A₂ n m)
      some (if n % 2 = 1 then Encl.add W (polygammaPosEncl n U w) T
        else Encl.sub W (polygammaPosEncl n U w) T)
    else
      let A₁ := lnGammaRatEncl (1 - q) V
      let D := Encl.sub W (polygammaPosEncl n A₁ w) (polygammaPosEncl n A₂ w)
      some (if n % 2 = 0 then Encl.add W (polygammaPosEncl n U w) D
        else Encl.sub W (polygammaPosEncl n U w) D)
  else none

/-- An enclosure of `ψ⁽ⁿ⁾(q)` at Ziv level `w` for a rational `q` that is positive (`pos`) or
negative and not an integer. -/
def polygammaRatEncl (n : Nat) (q : AzRat) (pos : Bool) (w : Nat) : Option Encl :=
  (if pos then some (polygammaPosEncl n (lnGammaRatEncl q (polyWork n w)) w)
    else polygammaRatNegEncl n q w).map fun H => if n % 2 = 1 then H else Encl.neg H

/-- The bracket of `ψ⁽ⁿ⁾(q)` as a pair of `Roundable`s, with the second evaluation of
`enclRefine` where digits cancel. -/
def polygammaRatApprox (n : Nat) (q : AzRat) (pos : Bool) (p w : Nat) :
    Roundable × Roundable :=
  lnAbsGammaApproxOf (enclRefine (polygammaRatEncl n q pos) p w) w

/-- Arguments where `ψ⁽ⁿ⁾(q)` is known to be irrational: `n` odd and the denominator of `q`
is `1` or `2`.  To be used off the poles and off `0`: `q` is then a positive integer or a
half-integer (`polygammaRatApprox_cert`, `Equiv/PolygammaRatCertificate.lean`). -/
def polygammaRatSpecial (n : Nat) (q : AzRat) : Bool :=
  n % 2 == 1 && (decide (q.den = 1) || decide (q.den = AzNat.ofNat 2))

end Azurite.AzFloat
