/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBaseFloatBracket
import Azurite.AzFloat.Equiv.LogBaseExact

/-!
## The logarithm in a float base

`logBaseFloatPrecRound x b p mode` is `log_b x = ln x / ln b` for floats `x` and `b`, correctly
rounded to precision `p` in `mode`, with the comparison against the exact value; `logBaseFloat x
b` rounds to nearest at the precision of `x`.  For positive finite `x ≠ 1` and `b ≠ 1`,
`log_b x` is rational exactly when `x` and `b` are integer powers of a common rational
(`logBaseFloatExact?` on the odd parts and dyadic exponents), and that rational is rounded once
(`ofAzRatRound`); otherwise the certified Ziv loop runs on `logBaseFloatApprox`, the `ln x`
bracket divided by the sign-clamped `ln b` bracket.  Special cases (with `b` the base): `NaN` for
`NaN`, for `x < 0` or `b < 0` (including `−∞`), for `x ∈ {∞, 0}` with `b ∈ {∞, 0}`, and for
`x = 1` with `b = 1`; `log_b x = 0` for finite `x > 0` with `b ∈ {∞, 0}`, and for `x = 1` with
`b ∉ {1}`; `log_1 x = ∞` for `x > 1` (including `∞`) and `−∞` for `0 ≤ x < 1`; `log_b ∞ = ∞`
for `b ≥ 1` and `−∞` for `0 < b < 1`; `log_b 0 = −∞` for `b ≥ 1` and `∞` for `0 < b < 1`.  The
specification `logBaseFloatPrecRound_eq_liftVal₂` is in `Equiv/LogBaseFloat.lean`.
-/

namespace Azurite.AzFloat

/-- The general case: `x, b > 0` finite, `x ≠ 1`, `b ≠ 1`: the exact branch or the Ziv loop. -/
def logBaseFloatFinite (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (hx1 : finiteVal true ex mx ≠ 1) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  match hx : logBaseFloatExact? (dyadicExp ex mx) (oddPart mx) (dyadicExp eb mb) (oddPart mb)
    with
  | some r => ofAzRatRound r p mode
  | none =>
    zivLoopCertified
      (logBaseFloatApprox (finite true ex qx mx hvx) ex (finite true eb qb mb hvb) eb) p mode
      (p + zivGuardBits)
      (logBaseFloatApprox_isSome_exists p mode ex hvx eb hvb hb1
        (irrational_logBaseFloat_of_none ex hvx eb hvb hb1 hx1 hx)
        _ (by unfold zivGuardBits; omega))

/-- `log_b x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def logBaseFloatPrecRound (x b : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity false => (nan, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | infinity true =>
    match b with
    | finite true eb _ _ _ =>
      if eb.sign = true ∧ eb.abs ≠ 0 then (infinity true, .eq) else (infinity false, .eq)
    | _ => (nan, .eq)
  | zero =>
    match b with
    | finite true eb _ _ _ =>
      if eb.sign = true ∧ eb.abs ≠ 0 then (infinity false, .eq) else (infinity true, .eq)
    | _ => (nan, .eq)
  | finite true ex qx mx hvx =>
    match b with
    | nan => (nan, .eq)
    | infinity false => (nan, .eq)
    | finite false _ _ _ _ => (nan, .eq)
    | infinity true => (zero, .eq)
    | zero => (zero, .eq)
    | finite true eb qb mb hvb =>
      if hb1 : eqIEEE (finite true eb qb mb hvb) one = true then
        if eqIEEE (finite true ex qx mx hvx) one then (nan, .eq)
        else if ex.sign = true ∧ ex.abs ≠ 0 then (infinity true, .eq) else (infinity false, .eq)
      else if hx1 : eqIEEE (finite true ex qx mx hvx) one = true then (zero, .eq)
      else if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        logBaseFloatFinite ex hvx eb hvb (finiteVal_ne_one_of_not_eqIEEE eb hvb hb1)
          (finiteVal_ne_one_of_not_eqIEEE ex hvx hx1) p mode

/-- `log_b x` rounded to nearest at the precision of `x`. -/
def logBaseFloat (x b : AzFloat) : AzFloat :=
  (logBaseFloatPrecRound x b (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
