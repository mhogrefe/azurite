/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowRatBracket
import Azurite.AzFloat.Equiv.LambertWBracket

/-!
## The real branches of the Lambert `W` function

`lambertW0PrecRound x p mode` is the principal branch `W₀ x` (`x ≥ −e⁻¹`) and
`lambertWm1PrecRound x p mode` the branch `W₋₁ x` (`−e⁻¹ ≤ x < 0`), DLMF §4.13, correctly rounded
to precision `p` in `mode` with the comparison against the exact value; `lambertW0Float x` and
`lambertWm1Float x` round to nearest at the precision of `x` (the names `lambertW0`,
`lambertWm1` are the real functions of `DLMF/Chapter4/Section13Real.lean`).  The rational
versions `lambertW0RatPrecRound q p mode`, `lambertWm1RatPrecRound q p mode` (and
`lambertW0Rat q p`, `lambertWm1Rat q p`) take an `AzRat`: the same pipeline with the target
entering through its `Floor`/`Ceiling` roundings (`ratAt`).

* **Domain.**  A float or rational is never `−e⁻¹` (irrational), so the certified search `qEncl`
  decides the sign of `q = 1 + e x` for `x < 0`: `NaN` below the branch point.  `x = 0` gives
  `W₀ 0 = 0` and `W₋₁ (0⁻) = −∞`; `W₀ (+∞) = +∞`; everything else outside the domain is `NaN`.
* **Rounding.**  Ziv's loop (`zivLoopCertified`, no fuel) on the brackets of
  `AzFloat/LambertWBracket.lean`: an unverified Halley candidate, verified by the mean value
  theorem around it, with a bisection fallback; the certificate is the irrationality of the
  roots for rational `x ≠ 0` (`Transcendental/LambertW.lean`).  The specifications
  `lambertW0PrecRound_eq`, `lambertWm1PrecRound_eq`, `lambertW0RatPrecRound_eq`,
  `lambertWm1RatPrecRound_eq` are in `Equiv/LambertW.lean`.
-/

namespace Azurite.AzFloat

/-- Ziv's loop for `W₀` of a positive rational target. -/
def lambertW0Pos (xAt : Nat → AzFloat × AzFloat) (h : PosTarget xAt) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  zivLoopCertified (lambertApprox true xAt none (aprioriW0Pos xAt 64) (sideCert_pos' h)) p mode
    (p + zivGuardBits) (zivCert_W0_pos' p mode h _)

/-- Ziv's loop for `W₀` of a negative rational target (`NaN` below `−e⁻¹`). -/
def lambertW0Neg (xAt : Nat → AzFloat × AzFloat) (h : NegTarget xAt) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  match hq : qEncl xAt (qCert' h) with
  | none => (nan, .eq)
  | some (lo, hi) =>
    zivLoopCertified (lambertApprox true xAt (some (qTight xAt (lo, hi)))
      (aprioriW0Neg (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
        (64 + 2 * compBits (some (qTight xAt (lo, hi))))) (sideCert_neg' h hq))
      p mode (p + zivGuardBits) (zivCert_W0_neg' p mode h hq _)

/-- Ziv's loop for `W₋₁` of a negative rational target (`NaN` below `−e⁻¹`). -/
def lambertWm1Neg (xAt : Nat → AzFloat × AzFloat) (h : NegTarget xAt) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  match hq : qEncl xAt (qCert' h) with
  | none => (nan, .eq)
  | some (lo, hi) =>
    zivLoopCertified (lambertApprox false xAt (some (qTight xAt (lo, hi)))
      (aprioriWm1 xAt (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
        (64 + 2 * compBits (some (qTight xAt (lo, hi))))) (sideCert_neg' h hq))
      p mode (p + zivGuardBits) (zivCert_Wm1' p mode h hq _)

/-- `W₀ x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or `+∞`). -/
def lambertW0PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match lambertW0Tiny? (fun P M => setPrecRound (-(finite s e q m hv)) P M)
        (-(finite s e q m hv)) e (max p q + zivGuardBits) p mode with
      | some r => r
      | none =>
      if hs : s = true then
        lambertW0Pos (floatAt (finite s e q m hv)) ⟨_, floatAt_encl (toVal_finite s e q m hv),
          finiteVal_rat s e hv, by subst hs; exact finiteVal_true_pos e hv⟩ p mode
      else
        lambertW0Neg (floatAt (finite s e q m hv)) ⟨_, floatAt_encl (toVal_finite s e q m hv),
          finiteVal_rat s e hv,
          by rw [Bool.eq_false_iff.mpr hs]; exact finiteVal_false_neg e hv⟩ p mode

/-- `W₋₁ x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `−∞`). -/
def lambertWm1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (nan, .eq)
  | zero => (infinity false, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      if hs : s = true then (nan, .eq)
      else
        lambertWm1Neg (floatAt (finite s e q m hv)) ⟨_, floatAt_encl (toVal_finite s e q m hv),
          finiteVal_rat s e hv,
          by rw [Bool.eq_false_iff.mpr hs]; exact finiteVal_false_neg e hv⟩ p mode

/-- `W₀ q` for an `AzRat`, rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def lambertW0RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (zero, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    match lambertW0Tiny? (fun P M => ofAzRatRound (-q) P M)
      (ofAzRatRound (-q) (p + zivGuardBits + 8) .Ceiling).1 (ratExpBound q) (p + zivGuardBits)
      p mode with
    | some r => r
    | none =>
    if hs : q.sign = true then
      lambertW0Pos (ratAt q) ⟨_, ratAt_encl q, ⟨_, rfl⟩, toRat_pos_real q hs h0⟩ p mode
    else
      lambertW0Neg (ratAt q)
        ⟨_, ratAt_encl q, ⟨_, rfl⟩, toRat_neg_real q (Bool.eq_false_iff.mpr hs) h0⟩ p mode

/-- `W₋₁ q` for an `AzRat`, rounded to precision `p` with `mode`, and the comparison with the
exact value (`(nan, .eq)` for `p = 0` unless `q = 0`). -/
def lambertWm1RatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if h0 : q.num = 0 then (infinity false, .eq)
  else if hp : p = 0 then (nan, .eq)
  else
    haveI : NeZero p := ⟨hp⟩
    if hs : q.sign = true then (nan, .eq)
    else
      lambertWm1Neg (ratAt q)
        ⟨_, ratAt_encl q, ⟨_, rfl⟩, toRat_neg_real q (Bool.eq_false_iff.mpr hs) h0⟩ p mode

/-- `W₀ x` rounded to nearest at the precision of `x`. -/
def lambertW0Float (x : AzFloat) : AzFloat :=
  (lambertW0PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `W₋₁ x` rounded to nearest at the precision of `x`. -/
def lambertWm1Float (x : AzFloat) : AzFloat :=
  (lambertWm1PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `W₀ q` rounded to nearest at precision `p`. -/
def lambertW0Rat (q : AzRat) (p : Nat) : AzFloat := (lambertW0RatPrecRound q p .Nearest).1

/-- `W₋₁ q` rounded to nearest at precision `p`. -/
def lambertWm1Rat (q : AzRat) (p : Nat) : AzFloat := (lambertWm1RatPrecRound q p .Nearest).1

end Azurite.AzFloat
