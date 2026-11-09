/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LambertWBracket

/-!
## The real branches of the Lambert `W` function

`lambertW0PrecRound x p mode` is the principal branch `W₀ x` (`x ≥ −e⁻¹`) and
`lambertWm1PrecRound x p mode` the branch `W₋₁ x` (`−e⁻¹ ≤ x < 0`), DLMF §4.13, correctly rounded
to precision `p` in `mode` with the comparison against the exact value; `lambertW0Float x` and
`lambertWm1Float x` round to nearest at the precision of `x` (the names `lambertW0`,
`lambertWm1` are the real functions of `DLMF/Chapter4/Section13Real.lean`).

* **Domain.**  A float is never `−e⁻¹` (irrational), so the certified search `qEncl` decides the
  sign of `q = 1 + e x` for `x < 0`: `NaN` below the branch point.  `x = 0` gives `W₀ 0 = 0` and
  `W₋₁ (0⁻) = −∞`; `W₀ (+∞) = +∞`; everything else outside the domain is `NaN`.
* **Rounding.**  Ziv's loop (`zivLoopCertified`, no fuel) on the brackets of
  `AzFloat/LambertWBracket.lean`: an unverified Halley candidate, verified by the mean value
  theorem around it, with a bisection fallback; the certificate is the irrationality of the
  roots for rational `x ≠ 0` (`Transcendental/LambertW.lean`).  The specifications
  `lambertW0PrecRound_eq`, `lambertWm1PrecRound_eq` are in `Equiv/LambertW.lean`.
-/

namespace Azurite.AzFloat

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
      if hs : s = true then
        zivLoopCertified (lambertApprox true (finite s e q m hv) none
          (aprioriW0Pos (finite s e q m hv) 64) (sideCert_pos s e q m hv hs)) p mode
          (p + zivGuardBits) (zivCert_W0_pos p mode s e q m hv hs)
      else
        have hs' : s = false := Bool.eq_false_iff.mpr hs
        match hq : qEncl (finite s e q m hv) (qCert s e q m hv hs') with
        | none => (nan, .eq)
        | some (lo, hi) =>
          zivLoopCertified (lambertApprox true (finite s e q m hv)
            (some (qTight (finite s e q m hv) (lo, hi)))
            (aprioriW0Neg (qTight (finite s e q m hv) (lo, hi)).1
              (qTight (finite s e q m hv) (lo, hi)).2
              (64 + 2 * compBits (some (qTight (finite s e q m hv) (lo, hi)))))
            (sideCert_neg s e q m hv hs' hq)) p mode (p + zivGuardBits)
            (zivCert_W0_neg p mode s e q m hv hs' hq)

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
        have hs' : s = false := Bool.eq_false_iff.mpr hs
        match hq : qEncl (finite s e q m hv) (qCert s e q m hv hs') with
        | none => (nan, .eq)
        | some (lo, hi) =>
          zivLoopCertified (lambertApprox false (finite s e q m hv)
            (some (qTight (finite s e q m hv) (lo, hi)))
            (aprioriWm1 (finite s e q m hv) (qTight (finite s e q m hv) (lo, hi)).1
              (qTight (finite s e q m hv) (lo, hi)).2
              (64 + 2 * compBits (some (qTight (finite s e q m hv) (lo, hi)))))
            (sideCert_neg s e q m hv hs' hq)) p mode (p + zivGuardBits)
            (zivCert_Wm1 p mode s e q m hv hs' hq)

/-- `W₀ x` rounded to nearest at the precision of `x`. -/
def lambertW0Float (x : AzFloat) : AzFloat :=
  (lambertW0PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `W₋₁ x` rounded to nearest at the precision of `x`. -/
def lambertWm1Float (x : AzFloat) : AzFloat :=
  (lambertWm1PrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
