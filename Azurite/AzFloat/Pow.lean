/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PowBracket
import Azurite.AzFloat.PowInt
import Azurite.AzFloat.RoundToInteger

/-!
## `x^y` for floats `x` and `y`

`powPrecRound x y p mode` is `x^y`, correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `pow x y` rounds to nearest at the precision of `x`.

* **Integer exponents** `y = n` (`isInteger`, `truncToAzInt`): the exact dyadic power
  `x^n = ±m^n 2^(E n)` through `powIntPrecRound` (one rounding) when it is cheap and may be a
  float — `|n| (size m' − 1) ≤ p + 1` for the odd part `m'` of the significand
  (`powIntCheap`) — and otherwise Ziv's loop on the bracket `exp (n ln |x|)` (`powApprox`), with
  the sign `(−1)^n` for `x < 0`; the loop is certified because such a power is never a rounding
  boundary (`not_mem_floatSet_of_not_cheap`).
* **Non-integer exponents**, `x > 0`: `powExact?` decides whether `x^y` is rational — exactly
  when `x = m 2^t` with `m = u^(2^J)` and `2^J ∣ t` for `y = N/2^J` — and gives `x^y = z^N` for
  the float `z = u 2^(t/2^J)`, handled as an integer power; otherwise `x^y` is irrational and
  Ziv's loop on `powApprox` is certified.  `x < 0` gives `NaN`.
* **Special values** (IEEE 754 / MPFR / Malachite, without negative zero): `x^0 = 1` and
  `1^y = 1` for every `x`, `y`, even `NaN`; otherwise `NaN` propagates; `x^(+∞) = +∞`,
  `x^(−∞) = 0` for `|x| > 1` and the other way round for `|x| < 1`, `(±1)^(±∞) = 1`;
  `(+∞)^y = +∞` for `y > 0`, `0` for `y < 0`; `(−∞)^y = −∞` for a positive odd integer `y`,
  `+∞` for every other `y > 0`, `0` for `y < 0`; `0^y = 0` for `y > 0`, `+∞` for `y < 0`; `x^y
  = NaN` for `x < 0` and a non-integer `y`.  The specification `powPrecRound_eq` is in
  `Equiv/Pow.lean` (`Spec.pow`).
-/

namespace Azurite.AzFloat

/-- `|n| < 2^(size |n|)`: the exponent of the exact float `ofAzInt n`. -/
theorem abs_toInt_lt_two_pow_size (n : AzInt) :
    |(n.toInt : ℝ)| < (2 : ℝ) ^ ((AzNat.ofNat n.abs.size).toAzInt).toInt := by
  rw [AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_natCast, ← Int.cast_abs, Int.abs_eq_natAbs,
    ← toNat_abs_eq_natAbs]
  have := Nat.lt_size_self n.abs.toNat
  rw [AzNat.size_toNat] at this
  exact_mod_cast this

/-- `(±m 2^E)^n` for `n ≠ 0`: `powIntPrecRound` when the exact power is cheap (and possibly a
float), Ziv's loop on the bracket of `exp (n ln |x|)`, with the sign `(−1)^n`, otherwise. -/
def powIntOrZiv (sx : Bool) (ex : AzInt) (qx : Nat) (mx : AzNat) (hvx : FiniteValid qx mx)
    (n : AzInt) (hn : n ≠ 0) (p : Nat) [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  if hc : powIntCheap mx n p = true then powIntPrecRound (finite sx ex qx mx hvx) n p mode
  else
    let neg := !sx && n.abs.isOdd
    let en := (AzNat.ofNat n.abs.size).toAzInt
    zivLoopCertified (powApprox neg (finite true ex qx mx hvx) ex (ofAzInt n) en) p mode
      (powStart en ex p)
      (powApprox_isSome_exists p mode neg ex hvx (toVal_ofAzInt n) en (abs_toInt_lt_two_pow_size n)
        (by
          rw [Real.rpow_intCast]
          exact not_mem_floatSet_of_not_cheap p ex hvx hn (Bool.eq_false_iff.mpr hc)
            (abs_powSign neg))
        (powStart en ex p) (by unfold powStart zivGuardBits; omega))

/-- `r^n` for a natural `r ≥ 1` (as the exact float `ofAzNat r`) through `powIntOrZiv`: exact
when cheap, Ziv's loop otherwise; `1` for `n = 0`.  Used by the natural-base powers whose exact
case `u^x = r^n` has an arbitrarily large `n`. -/
def natPowOrZiv (r : AzNat) (n : AzInt) (p : Nat) [NeZero p] (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hn : n = 0 then setPrecRound one p mode
  else
    match ofAzNat r with
    | finite true ez qz mz hvz => powIntOrZiv true ez qz mz hvz n hn p mode
    | _ => (nan, .eq)

/-- `truncToAzInt` of a nonzero integer float is nonzero. -/
theorem truncToAzInt_ne_zero_of_isInteger (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hi : isInteger (finite s e q m hv) = true) :
    truncToAzInt (finite s e q m hv) ≠ 0 := by
  intro h0
  have h := truncToAzInt_of_isInteger s e hv hi
  rw [h0, AzInt.toInt_zero, Int.cast_zero] at h
  exact finiteVal_ne_zero s e hv h.symm

/-- `x^y` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or an infinity). -/
def powPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match y with
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | nan =>
    if eqIEEE x one then (if p = 0 then (nan, .eq) else setPrecRound one p mode) else (nan, .eq)
  | infinity sy =>
    match x with
    | nan => (nan, .eq)
    | zero => if sy then (zero, .eq) else (infinity true, .eq)
    | infinity _ => if sy then (infinity true, .eq) else (zero, .eq)
    | finite _ ex _ _ _ =>
      if eqIEEE x.abs one then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
      else if ex.sign && ex != 0 then (if sy then (infinity true, .eq) else (zero, .eq))
      else (if sy then (zero, .eq) else (infinity true, .eq))
  | finite sy ey qy my hvy =>
    match x with
    | nan => (nan, .eq)
    | zero => if sy then (zero, .eq) else (infinity true, .eq)
    | infinity sx =>
      if sx then (if sy then (infinity true, .eq) else (zero, .eq))
      else if sy then
        (if isInteger (finite sy ey qy my hvy) && (truncToAzInt (finite sy ey qy my hvy)).abs.isOdd
          then (infinity false, .eq) else (infinity true, .eq))
      else (zero, .eq)
    | finite sx ex qx mx hvx =>
      if hp : p = 0 then (nan, .eq)
      else if eqIEEE (finite sx ex qx mx hvx) one then setPrecRound one p mode
      else
        haveI : NeZero p := ⟨hp⟩
        if hi : isInteger (finite sy ey qy my hvy) = true then
          powIntOrZiv sx ex qx mx hvx (truncToAzInt (finite sy ey qy my hvy))
            (truncToAzInt_ne_zero_of_isInteger sy ey hvy hi) p mode
        else if hsx : sx = false then (nan, .eq)
        else
          match hex : powExact? ex mx sy ey my with
          | some (z, N) =>
            match z with
            | finite true ez qz mz hvz =>
              if hN : N = 0 then (nan, .eq)
              else powIntOrZiv true ez qz mz hvz N hN p mode
            | _ => (nan, .eq)
          | none =>
            zivLoopCertified
              (powApprox false (finite true ex qx mx hvx) ex (finite sy ey qy my hvy) ey) p mode
              (powStart ey ex p)
              (powApprox_isSome_exists p mode false ex hvx (toVal_finite sy ey qy my hvy) ey
                (abs_finiteVal_bounds sy ey hvy).2
                (by
                  simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul]
                  exact not_mem_floatSet_of_irrational p
                    (irrational_of_powExact?_none ex hvx sy ey hvy (Bool.eq_false_iff.mpr hi) hex))
                (powStart ey ex p) (by unfold powStart zivGuardBits; omega))

/-- `x^y` rounded to nearest at the precision of `x`. -/
def pow (x y : AzFloat) : AzFloat := (powPrecRound x y (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
