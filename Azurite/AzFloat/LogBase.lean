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

/-- `log_b x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `b < 2`). -/
def logBasePrecRound (x : AzFloat) (b : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hb : b.toNat < 2 then (nan, .eq)
  else
    match hk : (AzNat.ofNat b.toNat).checkedLogBase2 with
    | some k => logBasePow2PrecRound x (AzNat.ofNat k).toAzInt p mode
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
            zivLoopCertified (logBaseApprox (finite true e q m hv) e b) p mode
              (p + zivGuardBits)
              (logBaseApprox_isSome_exists p mode e hv b (not_lt.mp hb)
                (AzNat.toNat_ofNat b.toNat ▸
                  irrational_of_logBaseExact?_none e hv (AzNat.ofNat b.toNat)
                  (by rw [AzNat.toNat_ofNat]; exact not_lt.mp hb)
                  (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt)
                  ((AzNat.checkedLogBase2_eq_none_iff _).mp hk) hx)
                (p + zivGuardBits) (by unfold zivGuardBits; omega))

/-- `log_b x` rounded to nearest at the precision of `x`. -/
def logBase (x : AzFloat) (b : UInt64) : AzFloat :=
  (logBasePrecRound x b (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
