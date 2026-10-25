/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBasePow2Bracket
import Azurite.AzFloat.Ln1p
import Azurite.AzRat.Construct

/-!
## `log_{2^k} (1 + x)`

`logBasePow2P1PrecRound x k p mode` is `log_{2^k} (1 + x) = log₂ (1 + x) / k` for an integer
`k ≠ 0` (possibly negative), correctly rounded to precision `p` in `mode`, with the comparison
against the exact value; `logBasePow2P1 x k` rounds to nearest.  The working precision starts
at `p + 64 + leadingZeroBits e` as `ln1p` does.  If `1 + x = 2^j` (`onePlusPow2Exponent?`) the
result is the rational `j / k`, rounded once (`ofAzRatRound`); otherwise `log₂ (1 + x) / k` is
irrational and the certified Ziv loop runs on `logBasePow2P1Approx`, the `ln (1 + x)` bracket of
`ln1p` turned into a `log₂` bracket and divided by `|k|`.  Special values: `NaN` for `NaN`, `−∞`,
`x < −1` and `k = 0`; `0 ↦ 0` exactly; `+∞ ↦ ±∞` and `−1 ↦ ∓∞` by the sign of `k`.  The
specification `logBasePow2P1PrecRound_eq_liftVal` is in `Equiv/LogBasePow2P1.lean`.
-/

namespace Azurite.AzFloat

/-- The finite case of `logBasePow2P1PrecRound` for `x > −1`: the exact branch or the Ziv
loop. -/
def logBasePow2P1Finite (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) (k : AzInt) (hk : k ≠ 0) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  match h : onePlusPow2Exponent? (finite s e q m hv) (p + zivGuardBits + leadingZeroBits e) with
  | some j => ofAzRatRound (AzRat.ofAzInts j k) p mode
  | none =>
    zivLoopCertified (logBasePow2P1Approx (finite s e q m hv) k) p mode
      (p + zivGuardBits + leadingZeroBits e)
      (logBasePow2P1Approx_isSome_exists p mode (toVal_finite s e q m hv) hgt k hk
        (Irrational.div_intCast
          (irrational_logb_two_one_add_of_none (toVal_finite s e q m hv)
            (by unfold zivGuardBits; omega) (by linarith) h)
          (toInt_ne_zero_of_ne_zero hk))
        _ (by unfold zivGuardBits; omega))

/-- `log_{2^k} (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact
value (`(nan, .eq)` for `p = 0` or `k = 0`). -/
def logBasePow2P1PrecRound (x : AzFloat) (k : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hk : k = 0 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity s => if s then (infinity k.sign, .eq) else (nan, .eq)
    | zero => (zero, .eq)
    | finite true e q m hv =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        logBasePow2P1Finite true e hv (by linarith [finiteVal_true_pos e hv]) k hk p mode
    | finite false e q m hv =>
      if hneg : e.sign = true ∧ e.abs ≠ 0 then
        if eqIEEE (finite false e q m hv) (-one) then (infinity (!k.sign), .eq) else (nan, .eq)
      else if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        logBasePow2P1Finite false e hv (finiteVal_false_gt_neg_one e hv hneg) k hk p mode

/-- `log_{2^k} (1 + x)` rounded to nearest at the precision of `x`. -/
def logBasePow2P1 (x : AzFloat) (k : AzInt) : AzFloat :=
  (logBasePow2P1PrecRound x k (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
