/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Log2Bracket
import Azurite.AzNat.Pow2

/-!
## The base-2 logarithm

`log2PrecRound x p mode` is `log₂ x` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value; `log2 x` rounds to nearest.  A float whose significand is a
power of two is `2^(e−1)` exactly, and its logarithm is the integer `e − 1`, returned exactly
(`setPrecRound (ofAzInt (e − 1))`, which also rounds integers of more than `p` bits).  Every other
positive float has an irrational `log₂ x` (`irrational_logb_two_finiteVal`), computed as
`ln x / ln 2` from the brackets of `ln x` and `ln 2` with directed rounding (`log2Approx`) by the
certified Ziv loop, without fuel.  Special values: `log₂ NaN = NaN`, `log₂ (+∞) = +∞`,
`log₂ (−∞) = NaN`, `log₂ 0 = −∞`, `log₂ x = NaN` for `x < 0`.  The specification
`log2PrecRound_eq_liftVal` is in `Equiv/Log2.lean`.
-/

namespace Azurite.AzFloat

/-- `log2PrecRound` built on a bracket function `A` of `log₂ x` with its Ziv certificate `hA`
(`log2Approx`, or `log2ApproxWith c` with precomputed constants). -/
def log2PrecRoundCore (A : AzFloat → AzInt → Nat → Roundable × Roundable)
    (hA : ∀ (p : Nat) [NeZero p] (mode : RoundingMode) (e : AzInt) {q : ℕ} {m : AzNat}
      (hv : FiniteValid q m), m.isPowerOfTwo = false → ∀ w₀ : Nat, 0 < w₀ →
      ∃ f : Nat, (roundingPossible (A (finite true e q m hv) e (w₀ * 2 ^ f)).1
        (A (finite true e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if s then (infinity true, .eq) else (nan, .eq)
  | zero => (infinity false, .eq)
  | finite false _ _ _ _ => (nan, .eq)
  | finite true e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      if h2 : m.isPowerOfTwo = true then setPrecRound (ofAzInt (e - 1)) p mode
      else
        zivLoopCertified (A (finite true e q m hv) e) p mode (p + zivGuardBits)
          (hA p mode e hv (Bool.eq_false_iff.mpr h2) (p + zivGuardBits)
            (by unfold zivGuardBits; omega))

/-- `log₂ x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0`). -/
def log2PrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  log2PrecRoundCore log2Approx @log2Approx_isSome_exists x p mode

/-- `log₂ x` rounded to nearest at the precision of `x`. -/
def log2 (x : AzFloat) : AzFloat := (log2PrecRound x (x.precision?.getD 1) .Nearest).1

/-- `log2PrecRound` with the constants `c` (`LnConsts.forPrecision p`); the same result
(`log2PrecRoundWith_eq_log2PrecRound`). -/
def log2PrecRoundWith (c : LnConsts) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  log2PrecRoundCore (log2ApproxWith c) (@log2ApproxWith_isSome_exists c) x p mode

/-- `log₂ x` rounded to nearest at the precision of `x`, with the constants `c`. -/
def log2With (c : LnConsts) (x : AzFloat) : AzFloat :=
  (log2PrecRoundWith c x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
