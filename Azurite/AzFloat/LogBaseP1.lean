/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBaseBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzFloat.Ln1p
import Azurite.AzNat.LogBase2

/-!
## `log_b (1 + x)`

`logBaseP1PrecRound x b p mode` is `log_b (1 + x)` for a 64-bit natural base `b ≥ 2` (the
natural-base analogue of C23's `log2p1`), correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `logBaseP1 x b` rounds to nearest.  The working precision
starts at `p + 64 + leadingZeroBits e` as `ln1p` does, so that tiny `x` are resolved.  Exact
cases first: for a power-of-two base `b = 2^k`, `1 + x = 2^j` (`onePlusPow2Exponent?`) gives the
rational `j / k`; otherwise `1 + x = c^r` for the primitive root `c` of `b = c^s` and a positive
integer `x` (`logBaseP1Exact?`) gives `r / s`; both are rounded once (`ofAzRatRound`).  Every
other `x > −1` has an irrational `log_b (1 + x)` and the certified Ziv loop runs on
`logBaseP1Approx`, the `ln (1 + x)` bracket of `ln1p` divided by the bracket of `ln b`.  Special
values as for `ln1p`: `NaN ↦ NaN`, `+∞ ↦ +∞`, `−∞ ↦ NaN`, `0 ↦ 0` exactly, `−1 ↦ −∞`, `NaN`
below `−1` and for the bases `0` and `1`.  The specification `logBaseP1PrecRound_eq_liftVal` is
in `Equiv/LogBaseP1.lean`.
-/

namespace Azurite.AzFloat

/-- The finite case of `logBaseP1PrecRound` for `x > −1`: the exact branches or the Ziv loop. -/
def logBaseP1Finite (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (b : UInt64) (hb : 2 ≤ b.toNat) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  match hk : (AzNat.ofNat b.toNat).checkedLogBase2 with
  | some k =>
    match h : onePlusPow2Exponent? (finite s e q m hv) (p + zivGuardBits + leadingZeroBits e)
      with
    | some j => ofAzRatRound (AzRat.ofAzInts j (AzNat.ofNat k).toAzInt) p mode
    | none =>
      zivLoopCertified (logBaseP1Approx (finite s e q m hv) b) p mode
        (p + zivGuardBits + leadingZeroBits e)
        (logBaseP1Approx_isSome_exists p mode (toVal_finite s e q m hv) hgt b hb
          (irrational_log_div_log_one_add_of_pow2 s e hv hgt b hb hk
            (by unfold zivGuardBits; omega) h)
          _ (by unfold zivGuardBits; omega))
  | none =>
    match hx : logBaseP1Exact? (finite s e q m hv) (AzNat.ofNat b.toNat) with
    | some r => ofAzRatRound r p mode
    | none =>
      zivLoopCertified (logBaseP1Approx (finite s e q m hv) b) p mode
        (p + zivGuardBits + leadingZeroBits e)
        (logBaseP1Approx_isSome_exists p mode (toVal_finite s e q m hv) hgt b hb
          (AzNat.toNat_ofNat b.toNat ▸
            irrational_of_logBaseP1Exact?_none s e hv (AzNat.ofNat b.toNat)
              (by rw [AzNat.toNat_ofNat]; exact hb)
              (by rw [AzNat.toNat_ofNat]; exact b.toBitVec.isLt)
              ((AzNat.checkedLogBase2_eq_none_iff _).mp hk) hgt hx)
          _ (by unfold zivGuardBits; omega))

/-- `log_b (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `b < 2`). -/
def logBaseP1PrecRound (x : AzFloat) (b : UInt64) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hb : b.toNat < 2 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity s => if s then (infinity true, .eq) else (nan, .eq)
    | zero => (zero, .eq)
    | finite true e q m hv =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        logBaseP1Finite true e hv (by linarith [finiteVal_true_pos e hv]) b (not_lt.mp hb) p mode
    | finite false e q m hv =>
      if hneg : e.sign = true ∧ e.abs ≠ 0 then
        if eqIEEE (finite false e q m hv) (-one) then (infinity false, .eq) else (nan, .eq)
      else if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        logBaseP1Finite false e hv (finiteVal_false_gt_neg_one e hv hneg) b (not_lt.mp hb) p mode

/-- `log_b (1 + x)` rounded to nearest at the precision of `x`. -/
def logBaseP1 (x : AzFloat) (b : UInt64) : AzFloat :=
  (logBaseP1PrecRound x b (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
