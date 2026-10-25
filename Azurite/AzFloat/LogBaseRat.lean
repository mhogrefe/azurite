/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBaseBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzFloat.LogBasePow2Rat
import Azurite.AzNat.LogBase2

/-!
## The logarithm of a rational in a natural base

`logBaseRatPrecRound q b p mode` is `log_b q = ln q / ln b` for a rational `q` and a 64-bit
natural base `b ≥ 2`, correctly rounded to precision `p` in `mode`, with the comparison against
the exact value.  A base that is a power of two, `b = 2^k`, delegates to
`logBasePow2RatPrecRound q k`.  Otherwise `log_b q` is rational exactly when `q` is an integer
power (possibly negative) of the primitive root of `b` (`logBaseExactRat?`), and that rational is
rounded once (`ofAzRatRound`); every other positive rational has an irrational `log_b q`,
computed by the certified Ziv loop from the bracket `logBaseRatApprox`.  Special values: `NaN`
for `q < 0` and the bases `0` and `1`; `log_b 0 = −∞`.  The specification
`logBaseRatPrecRound_eq` is in `Equiv/LogBaseRat.lean`.
-/

namespace Azurite.AzFloat

/-- `log_b q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `b < 2`). -/
def logBaseRatPrecRound (q : AzRat) (b : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hb : b.toNat < 2 then (nan, .eq)
  else
    match (AzNat.ofNat b.toNat).checkedLogBase2 with
    | some k => logBasePow2RatPrecRound q (AzNat.ofNat k).toAzInt p mode
    | none =>
      if h0 : q.num = 0 then (infinity false, .eq)
      else if hs : q.sign = true then
        if hp : p = 0 then (nan, .eq)
        else
          haveI : NeZero p := ⟨hp⟩
          match hx : logBaseExactRat? q (AzNat.ofNat b.toNat) with
          | some r => ofAzRatRound r p mode
          | none =>
            zivLoopCertified (logBaseRatApprox q b) p mode (p + zivGuardBits)
              (logBaseRatApprox_isSome_exists p mode q (toRat_pos_of_sign q hs h0) b
                (not_lt.mp hb)
                (AzNat.toNat_ofNat b.toNat ▸
                  irrational_of_logBaseExactRat?_none q (toRat_pos_of_sign q hs h0)
                    (AzNat.ofNat b.toNat) (by rw [AzNat.toNat_ofNat]; exact not_lt.mp hb)
                    (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt) hx)
                (p + zivGuardBits) (by unfold zivGuardBits; omega))
      else (nan, .eq)

/-- `log_b q` rounded to nearest at precision `p`. -/
def logBaseRat (q : AzRat) (b : UInt64) (p : Nat) : AzFloat :=
  (logBaseRatPrecRound q b p .Nearest).1

end Azurite.AzFloat
