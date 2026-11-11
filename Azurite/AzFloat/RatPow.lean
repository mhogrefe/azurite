/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.RatPowBracket
import Azurite.AzFloat.Pow

/-!
## `q^y` for a rational `q` and a float `y`

`ratPowPrecRound q y p mode` is `q^y` for an `AzRat` `q` and a float `y`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `ratPowFloat q y p` rounds
to nearest.  The structure is that of `powPrecRound` (`AzFloat/Pow.lean`) with the base `q = ±a/b`
in lowest terms:

* **Integer exponents** `y = n`: the exact `(a/b)^n = ± a'^n 2^(c n) / b'^n` through one
  correctly rounded division of exact floats when both `a^n` and `b^n` pass `powIntCheap`
  (`ratPowIntCheap`), and otherwise Ziv's loop on the bracket `exp (n ln (a/b))`
  (`ratPowApprox`), with the sign `(−1)^n` for `q < 0`; such a power is never a rounding
  boundary (`not_mem_floatSet_ratPow_of_not_cheap`).
* **Non-integer exponents**, `q > 0`: `ratPowExact?` decides whether `q^y` is rational — exactly
  when `a` and `b` are both `2^J`-th powers for `y = N/2^J` — and gives `q^y = (u/v)^N`, handled
  as an integer power; otherwise `q^y` is irrational and Ziv's loop is certified.  `q < 0` gives
  `NaN`.
* **Special values** as for `powPrecRound`: `q^0 = 1` and `1^y = 1` even for `NaN`; `q^(±∞)` by
  `|q|` against `1`; `0^y = 0` for `y > 0`, `+∞` for `y < 0`.  The specification
  `ratPowPrecRound_eq` is in `Equiv/RatPow.lean`: `roundVal p mode (Spec.pow (some q) y.toVal)`.
-/

namespace Azurite.AzFloat

/-- The positive rational `a/b` for coprime `a`, `b` with `b ≠ 0`. -/
def mkPosRat (a b : AzNat) (hb : b ≠ 0) (hcop : Nat.Coprime a.toNat b.toNat) : AzRat :=
  ⟨true, a, b, hb, fun _ => rfl, (AzNat.coprime_iff a b).mpr hcop⟩

/-- `± (a/b)^n` for coprime `a`, `b ≠ 0` and `n ≠ 0`: one correctly rounded division of the exact
floats `a'^|n| 2^(c_a |n| − c_b |n|)` and `b'^|n|` (odd parts `a'`, `b'`) when the power is cheap,
Ziv's loop on the bracket of `exp (n ln (a/b))` otherwise. -/
def ratPowIntOrZiv (neg : Bool) (a b : AzNat) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : Nat.Coprime a.toNat b.toNat) (n : AzInt) (hn : n ≠ 0) (p : Nat) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  if hc : ratPowIntCheap a b n p = true then
    let A := if n.sign then a else b
    let B := if n.sign then b else a
    let ac := splitOdd A
    let bc := splitOdd B
    let numF := ofAzNat (powOdd ac.1 n.abs) <<<
      ((AzNat.ofNat ac.2).toAzInt * n.abs.toAzInt - (AzNat.ofNat bc.2).toAzInt * n.abs.toAzInt)
    divPrecRound (if neg then -numF else numF) (ofAzNat (powOdd bc.1 n.abs)) p mode
  else
    let en := (AzNat.ofNat n.abs.size).toAzInt
    let q := mkPosRat a b hb hcop
    zivLoopCertified (ratPowApprox neg q (ofAzInt n) en) p mode (ratPowStart en q p)
      (ratPowApprox_isSome_exists p mode neg q rfl ha (toVal_ofAzInt n) en
        (abs_toInt_lt_two_pow_size n)
        (by
          rw [Real.rpow_intCast, coe_toRat_eq_div_pos q rfl]
          exact not_mem_floatSet_ratPow_of_not_cheap p ha hb hcop hn (Bool.eq_false_iff.mpr hc)
            (abs_powSign neg))
        (ratPowStart en q p) (by unfold ratPowStart zivGuardBits; omega))

/-- `q^y` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or an infinity). -/
def ratPowPrecRound (q : AzRat) (y : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match y with
  | zero => if p = 0 then (nan, .eq) else setPrecRound one p mode
  | nan =>
    if q.sign ∧ q.num = q.den then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else (nan, .eq)
  | infinity sy =>
    if q.num = q.den then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else if q.den < q.num then (if sy then (infinity true, .eq) else (zero, .eq))
    else (if sy then (zero, .eq) else (infinity true, .eq))
  | finite sy ey qy my hvy =>
    if hq0 : q.num = 0 then (if sy then (zero, .eq) else (infinity true, .eq))
    else if hp : p = 0 then (nan, .eq)
    else if q.sign ∧ q.num = q.den then setPrecRound one p mode
    else
      haveI : NeZero p := ⟨hp⟩
      have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
      if hi : isInteger (finite sy ey qy my hvy) = true then
        -- `q = −1`: `±1` by the parity of `y`, without converting a huge `y`
        if q.num = q.den then negOnePow (finite sy ey qy my hvy) p mode
        else
        ratPowIntOrZiv (!q.sign && (truncToAzInt (finite sy ey qy my hvy)).abs.isOdd) q.num q.den
          hq0 q.den_nz hcop (truncToAzInt (finite sy ey qy my hvy))
          (truncToAzInt_ne_zero_of_isInteger sy ey hvy hi) p mode
      else if hsq : q.sign = false then (nan, .eq)
      else
        have hs : q.sign = true := by revert hsq; cases q.sign <;> simp
        match expNearOne? (sy == decide (q.den.toNat < q.num.toNat))
          (nearOneExp ey (q.num.size + q.den.size)) p mode with
        | some r => r
        | none =>
        match hex : ratPowExact? q.num q.den sy ey my with
        | some (u, v, N) =>
          have h := ratPowExact?_some hq0 q.den_nz hcop sy ey hvy (Bool.eq_false_iff.mpr hi) hex
          ratPowIntOrZiv false u v h.1 h.2.1 h.2.2.1 N
            (fun h0 => h.2.2.2.1 (by rw [h0, AzInt.toInt_zero])) p mode
        | none =>
          zivLoopCertified (ratPowApprox false q (finite sy ey qy my hvy) ey) p mode
            (ratPowStart ey q p)
            (ratPowApprox_isSome_exists p mode false q hs hq0 (toVal_finite sy ey qy my hvy) ey
              (abs_finiteVal_bounds sy ey hvy).2
              (by
                simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul]
                rw [coe_toRat_eq_div_pos q hs]
                exact not_mem_floatSet_of_irrational p
                  (irrational_of_ratPowExact?_none hq0 q.den_nz hcop sy ey hvy
                    (Bool.eq_false_iff.mpr hi) hex))
              (ratPowStart ey q p) (by unfold ratPowStart zivGuardBits; omega))

/-- `q^y` rounded to nearest at precision `p`. -/
def ratPowFloat (q : AzRat) (y : AzFloat) (p : Nat) : AzFloat :=
  (ratPowPrecRound q y p .Nearest).1

end Azurite.AzFloat
