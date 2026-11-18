/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowRatBracket
import Azurite.AzFloat.Equiv.WrightOmegaBracket

/-!
## The Wright `ω` function on the real line

`wrightOmegaPrecRound x p mode` is `ω(x) = W₀(eˣ)`, the positive root of `y + ln y = x` (DLMF
4.13.1_2), correctly rounded to precision `p` in `mode` with the comparison against the exact
value; `wrightOmegaFloat x` rounds to nearest at the precision of `x` (the name `wrightOmega`
is the complex function of `DLMF/Chapter4/Section13Omega.lean`).  The rational versions
`wrightOmegaRatPrecRound q p mode` and `wrightOmegaRat q p` take an `AzRat`: the same pipeline
with the target entering through its `Floor`/`Ceiling` roundings.

* **Special values.**  `ω(+∞) = +∞`, `ω(−∞) = 0`, and `ω(1) = 1` is the only rational argument
  with a rational value; `ω` is defined on the whole real line.
* **Rounding.**  Ziv's loop (`zivLoopCertified`, no fuel) on the brackets of
  `AzFloat/WrightOmegaBracket.lean`: an unverified Newton candidate for `y + ln y = x` with half
  the bits wanted, verified and refined by one enclosure of its residual; the certificate is
  the irrationality of `ω(x)` for a rational `x ≠ 1` (`Transcendental/WrightOmega.lean`).  The
  exponential `eˣ` is never formed, so the cost for a large `x` is that of a logarithm; for a
  very negative `x`, where `ω(x) ≈ eˣ`, it is that of the exponential.
* **Large arguments** go through `wrightOmegaHuge?` (`x − ln x < ω(x) < x`).

The specifications `wrightOmegaPrecRound_eq`, `wrightOmegaRatPrecRound_eq` are in
`Equiv/WrightOmega.lean`.
-/

namespace Azurite.AzFloat

/-- Ziv's loop for `ω` of a rational target other than `1`. -/
def wrightOmegaLoop (xAt eAt : Nat → AzFloat × AzFloat) (h : OmegaTarget xAt eAt) (p : Nat)
    [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  zivLoopCertified (wrightApprox xAt eAt (omegaSideCert h)) p mode (p + zivGuardBits)
    (omegaZivCert p mode h _)

/-- `ω(x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`). -/
def wrightOmegaPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (zero, .eq)
  | zero =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      wrightOmegaLoop (floatAt zero) (expAt zero)
        ⟨0, floatAt_encl toVal_zero', expAt_encl toVal_zero', ⟨0, by rw [Rat.cast_zero]⟩,
          zero_ne_one⟩ p mode
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      if h1 : isOne (finite s e q m hv) = true then setPrecRound one p mode
      else
        match wrightOmegaHuge? (fun P M => setPrecRound (-(finite s e q m hv)) P M)
          (-(finite s e q m hv)) (finite s e q m hv) e (p + zivGuardBits) p mode with
        | some r => r
        | none =>
          wrightOmegaLoop (floatAt (finite s e q m hv)) (expAt (finite s e q m hv))
            ⟨_, floatAt_encl (toVal_finite s e q m hv), expAt_encl (toVal_finite s e q m hv),
              finiteVal_rat s e hv, fun h => h1 ((isOne_iff (toVal_finite s e q m hv)).mpr h)⟩
            p mode

/-- `ω(q)` for an `AzRat`, rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0`). -/
def wrightOmegaRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    if h1 : q.sign = true ∧ q.num = q.den then setPrecRound one p mode
    else
      match guardedBy ((ratExpBound q).sign
          && decide (p + zivGuardBits + 8 ≤ (ratExpBound q).abs.toNat)) fun _ =>
          wrightOmegaHuge? (fun P M => ofAzRatRound (-q) P M)
            (ofAzRatRound (-q) (p + zivGuardBits + 8) .Ceiling).1 (ofAzRatRound q 64 .Floor).1
            (ratExpBound q) (p + zivGuardBits) p mode with
      | some r => r
      | none =>
        wrightOmegaLoop (ratAt q) (expRatAt q)
          ⟨_, ratAt_encl q, expRatAt_encl q, ⟨_, rfl⟩, fun h =>
            h1 ((coe_toRat_eq_one_iff q).mp (by rw [h, EReal.coe_one]))⟩ p mode

/-- `ω(x)` rounded to nearest at the precision of `x`. -/
def wrightOmegaFloat (x : AzFloat) : AzFloat :=
  (wrightOmegaPrecRound x (x.precision?.getD 1) .Nearest).1

/-- `ω(q)` rounded to nearest at precision `p`. -/
def wrightOmegaRat (q : AzRat) (p : Nat) : AzFloat := (wrightOmegaRatPrecRound q p .Nearest).1

end Azurite.AzFloat
