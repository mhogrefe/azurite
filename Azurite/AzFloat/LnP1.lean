/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.NegRound

/-!
## `ln (1 + x)`

`lnP1PrecRound x p mode` is `ln (1 + x)` (MCA's `log1p`, §4.4.2 and Exercise 4.9) correctly
rounded to precision `p` in `mode`, with the comparison against the exact value; `lnP1 x p` rounds
to nearest.  MCA evaluates `log1p` by argument reduction and a power series in `O(√n M(n))`; the
AGM logarithm of `LnBracket.lean` is `O(log n · M(n))`, so the bracket here is `ln` of the float
`y = ⌊1 + x⌋_w` (one rounded addition, one AGM run), the upper end widened by
`2^(2−w) ≥ ln ((1 + x)/y)` (`lnP1Approx`).  The point of `log1p` is small `|x|`: there `1 + x` loses
the leading zero bits of `x`, so for `|x| < 1` with exponent `e ≤ 0` the certified Ziv loop starts
at `p + 64 − e` instead of `p + 64`, and the first level already determines the rounding; the loop
needs no fuel since `ln (1 + x)` is irrational for every float `x ≠ 0` (`irrational_log_rat`).
**Tiny arguments** (`e ≤ −(max p q + 72)`, `q` the precision of `x`) never reach the loop:
`lnP1Tiny?` rounds from `x − 2x² ≤ ln (1 + x) < x` directly, at a cost independent of `e`
(so `lnP1 (2^(−2^30))` is immediate; the loop would need `2^30` bits).
Special values: `lnP1 NaN = NaN`, `lnP1 (+∞) = +∞`, `lnP1 (−∞) = NaN`, `lnP1 0 = 0` exactly,
`lnP1 (−1) = −∞`, `lnP1 x = NaN` for `x < −1`.  The specification `lnP1PrecRound_eq_liftVal` is in
`Equiv/LnP1.lean`.
-/

namespace Azurite.AzFloat

/-- The number of leading zero bits of a float of exponent `e` with `|x| < 1`: `−e` for `e ≤ 0`,
else `0` (only the start of the working precision depends on it). -/
def leadingZeroBits (e : AzInt) : Nat := if e.sign then 0 else e.abs.toUInt64.toNat

/-- The first working precision of the `log_b (1 + x)` Ziv loops for an argument of exponent
`e` at target precision `p`: `p + 64` when the argument is tiny enough for the cheap bracket of
`lnP1BracketOf` at that precision (`e ≤ −(p + 72)`), else `p + 64 + leadingZeroBits e`. -/
def lnP1Start (e : AzInt) (p : Nat) : Nat :=
  if e.sign = false ∧ p + zivGuardBits + 8 ≤ e.abs.toNat then p + zivGuardBits
  else p + zivGuardBits + leadingZeroBits e

theorem lnP1Start_ge (e : AzInt) (p : Nat) : 64 ≤ lnP1Start e p := by
  unfold lnP1Start zivGuardBits
  split_ifs <;> omega

theorem lnP1Start_pos (e : AzInt) (p : Nat) : 0 < lnP1Start e p :=
  lt_of_lt_of_le (by norm_num) (lnP1Start_ge e p)

/-- **The tiny-argument path of `ln (1 + x)`** for a finite `x` of exponent `e` and precision
`q`: when `e ≤ −(w + 8)` with `w = max p q + 64`, `−ln (1 + x)` lies in `(−x, −x + 2x²]`, so it
is rounded (in the negated mode) from the bracket `[−x, ⌈−x + 2|x| 2^e⌉_{w+8}]` by the test of
`roundingPossible`, and the result is negated.  (The negation puts the exact end `x` at the
open side of the half-open test; the bracket contains no boundary since `x` has at most `w`
bits.)  No logarithm is computed and the cost is independent of `e`.  `none` when the argument
is not tiny or the test fails. -/
def lnP1Tiny? (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let w := max p q + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let nx := -x
    let hi := (addPrecRound nx ((x.abs <<< e) <<< AzInt.ofInt 1) (w + 8) .Ceiling).1
    (roundingPossible (fun P M => setPrecRound nx P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

/-- `lnP1PrecRound` built on a bracket function `A` of `ln (1 + x)` with its Ziv
certificate `hA` (`lnP1Approx`, or `lnP1ApproxWith c` with precomputed constants). -/
def lnP1PrecRoundCore (A : AzFloat → Nat → Roundable × Roundable)
    (hA : ∀ (p : Nat) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ},
      x.toVal = some (xv : EReal) → -1 < xv → xv ≠ 0 → ∀ w₀ : Nat, 0 < w₀ →
      ∃ f : Nat, (roundingPossible (A x (w₀ * 2 ^ f)).1 (A x (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (zero, .eq)
  | finite true e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match lnP1Tiny? (finite true e q m hv) e q p mode with
      | some r => r
      | none =>
        zivLoopCertified (A (finite true e q m hv)) p mode
          (p + zivGuardBits + leadingZeroBits e)
          (hA p mode (toVal_finite true e q m hv)
            (by linarith [finiteVal_true_pos e hv]) (finiteVal_true_pos e hv).ne' _
            (by unfold zivGuardBits; omega))
  | finite false e q m hv =>
    if hneg : e.sign = true ∧ e.abs ≠ 0 then
      if eqIEEE (finite false e q m hv) (-one) then (infinity false, .eq) else (nan, .eq)
    else if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      match lnP1Tiny? (finite false e q m hv) e q p mode with
      | some r => r
      | none =>
        zivLoopCertified (A (finite false e q m hv)) p mode
          (p + zivGuardBits + leadingZeroBits e)
          (hA p mode (toVal_finite false e q m hv)
            (finiteVal_false_gt_neg_one e hv hneg) (finiteVal_false_ne_zero e hv) _
            (by unfold zivGuardBits; omega))

/-- `ln (1 + x)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def lnP1PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  lnP1PrecRoundCore lnP1Approx @lnP1Approx_isSome_exists x p mode

/-- `ln (1 + x)` rounded to nearest at the precision of `x`. -/
def lnP1 (x : AzFloat) : AzFloat := (lnP1PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `lnP1PrecRound` with the constants `c`; the same result (`lnP1PrecRoundWith_eq_lnP1PrecRound`).
(The Ziv loop starts at `p + 64 + leadingZeroBits e`, so for small `|x|` the constants need a
correspondingly finer `W` to be used.) -/
def lnP1PrecRoundWith (c : LnConsts) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  lnP1PrecRoundCore (lnP1ApproxWith c) (@lnP1ApproxWith_isSome_exists c) x p mode

/-- `ln (1 + x)` rounded to nearest at the precision of `x`, with the constants `c`. -/
def lnP1With (c : LnConsts) (x : AzFloat) : AzFloat :=
  (lnP1PrecRoundWith c x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
