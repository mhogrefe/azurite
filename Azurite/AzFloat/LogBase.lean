/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBaseBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzFloat.LogBasePow2
import Azurite.AzNat.LogBase2

/-!
## The logarithm in a natural base

`logBasePrecRound x b p mode` is `log_b x = ln x / ln b` for a 64-bit natural base `b ≥ 2`,
correctly rounded to precision `p` in `mode`, with the comparison against the exact value.  A
base that is a power of two, `b = 2^k`, delegates to `logBasePow2PrecRound x k`.  Otherwise
`log_b x` is rational exactly when `x` is a positive integer power of the primitive root of `b`
(`logBaseExact?`), and that rational is rounded once (`ofAzRatRound`); every other positive
float has an irrational `log_b x`, computed by the certified Ziv loop from the bracket
`logBaseApprox`.  Special values: `NaN` for `NaN`, `−∞`, negatives and the bases `0` and `1`;
`log_b (+∞) = +∞` and `log_b 0 = −∞`.  The specification `logBasePrecRound_eq_liftVal` is in
`Equiv/LogBase.lean`.
-/

namespace Azurite.AzFloat

/-- `logBasePrecRound` for the base `b`, built on the power-of-two driver `P2` (for `b = 2^k`)
and a bracket function `A` of `log_b x` with its Ziv certificate `hA` (`logBasePow2PrecRound`
and `logBaseApprox`, or their `With` versions). -/
def logBasePrecRoundCore (b : UInt64)
    (P2 : AzFloat → AzInt → Nat → RoundingMode → AzFloat × Ordering)
    (A : AzFloat → AzInt → Nat → Roundable × Roundable)
    (hA : ∀ (p : Nat) [NeZero p] (mode : RoundingMode) (e : AzInt) {q : ℕ} {m : AzNat}
      (hv : FiniteValid q m), 2 ≤ b.toNat →
      Irrational (Real.log (finiteVal true e m) / Real.log b.toNat) → ∀ w₀ : Nat, 0 < w₀ →
      ∃ f : Nat, (roundingPossible (A (finite true e q m hv) e (w₀ * 2 ^ f)).1
        (A (finite true e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hb : b.toNat < 2 then (nan, .eq)
  else
    match hk : (AzNat.ofNat b.toNat).checkedLogBase2 with
    | some k => P2 x (AzNat.ofNat k).toAzInt p mode
    | none =>
      match x with
      | nan => (nan, .eq)
      | infinity s => if s then (infinity true, .eq) else (nan, .eq)
      | zero => (infinity false, .eq)
      | finite false _ _ _ _ => (nan, .eq)
      | finite true e q m hv =>
        if hp : p = 0 then (nan, .eq)
        else
          haveI : NeZero p := ⟨hp⟩
          match hx : logBaseExact? (finite true e q m hv) (AzNat.ofNat b.toNat) with
          | some r => ofAzRatRound r p mode
          | none =>
            zivLoopCertified (A (finite true e q m hv) e) p mode (p + zivGuardBits)
              (hA p mode e hv (not_lt.mp hb)
                (AzNat.toNat_ofNat b.toNat ▸
                  irrational_of_logBaseExact?_none e hv (AzNat.ofNat b.toNat)
                  (by rw [AzNat.toNat_ofNat]; exact not_lt.mp hb)
                  (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt)
                  ((AzNat.checkedLogBase2_eq_none_iff _).mp hk) hx)
                (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log_b x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `b < 2`). -/
def logBasePrecRound (x : AzFloat) (b : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  logBasePrecRoundCore b logBasePow2PrecRound (fun x e w => logBaseApprox x e b w)
    (@fun p _ mode e _ _ hv hb hirr w₀ hw₀ =>
      logBaseApprox_isSome_exists p mode e hv b hb hirr w₀ hw₀)
    x p mode

/-- `log_b x` rounded to nearest at the precision of `x`. -/
def logBase (x : AzFloat) (b : UInt64) : AzFloat :=
  (logBasePrecRound x b (x.precision?.getD 1) .Nearest).1

/-- The constants for `log_b` at precision `p` (the first Ziv level `p + zivGuardBits`). -/
def LogBaseConsts.forPrecision (b : UInt64) (p : Nat) : LogBaseConsts :=
  LogBaseConsts.make b (p + zivGuardBits)

/-- `logBasePrecRound x cb.base p mode` with the constants `cb`; the same result
(`logBasePrecRoundWith_eq_logBasePrecRound`). -/
def logBasePrecRoundWith (cb : LogBaseConsts) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  logBasePrecRoundCore cb.base (logBasePow2PrecRoundWith cb.ln) (logBaseApproxWith cb)
    (@fun p _ mode e _ _ hv hb hirr w₀ hw₀ =>
      logBaseApproxWith_isSome_exists cb p mode e hv hb hirr w₀ hw₀)
    x p mode

/-- `log_{cb.base} x` rounded to nearest at the precision of `x`, with the constants `cb`. -/
def logBaseWith (cb : LogBaseConsts) (x : AzFloat) : AzFloat :=
  (logBasePrecRoundWith cb x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
