/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LogBasePow2Bracket
import Azurite.AzRat.Construct

/-!
## The logarithm in a power-of-two base

`logBasePow2PrecRound x k p mode` is `log_{2^k} x = log₂ x / k` for an integer `k ≠ 0`
(possibly negative), correctly rounded to precision `p` in `mode`, with the comparison against
the exact value.  A float whose significand is a power of two is `2^(e−1)`, and its logarithm
is the rational `(e − 1) / k`, rounded exactly once (`ofAzRatRound`).  Every other positive
float has an irrational `log₂ x / k`, computed by the certified Ziv loop from the bracket
`logBasePow2Approx`.  Special values: `NaN` for `NaN`, `−∞`, negatives and the base `1`
(`k = 0`); `log_{2^k} (+∞) = ±∞` and `log_{2^k} 0 = ∓∞` with the sign of `k`.  The
specification `logBasePow2PrecRound_eq_liftVal` is in `Equiv/LogBasePow2.lean`.
-/

namespace Azurite.AzFloat

/-- `logBasePow2PrecRound` built on a bracket function `A` of `log_{2^k} x` with its Ziv
certificate `hA` (`logBasePow2Approx`, or `logBasePow2ApproxWith c`). -/
def logBasePow2PrecRoundCore (A : AzFloat → AzInt → AzInt → Nat → Roundable × Roundable)
    (hA : ∀ (p : Nat) [NeZero p] (mode : RoundingMode) (e : AzInt) {q : ℕ} {m : AzNat}
      (hv : FiniteValid q m), m.isPowerOfTwo = false → ∀ k : AzInt, k ≠ 0 → ∀ w₀ : Nat, 0 < w₀ →
      ∃ f : Nat, (roundingPossible (A (finite true e q m hv) e k (w₀ * 2 ^ f)).1
        (A (finite true e q m hv) e k (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (x : AzFloat) (k : AzInt) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if hk : k = 0 then (nan, .eq)
  else
    match x with
    | nan => (nan, .eq)
    | infinity s => if s then (infinity k.sign, .eq) else (nan, .eq)
    | zero => (infinity (!k.sign), .eq)
    | finite false _ _ _ _ => (nan, .eq)
    | finite true e q m hv =>
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        if h2 : m.isPowerOfTwo = true then ofAzRatRound (AzRat.ofAzInts (e - 1) k) p mode
        else
          zivLoopCertified (A (finite true e q m hv) e k) p mode (p + zivGuardBits)
            (hA p mode e hv (Bool.eq_false_iff.mpr h2) k hk (p + zivGuardBits)
              (by unfold zivGuardBits; omega))

/-- `log_{2^k} x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` or `k = 0`). -/
def logBasePow2PrecRound (x : AzFloat) (k : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  logBasePow2PrecRoundCore logBasePow2Approx @logBasePow2Approx_isSome_exists x k p mode

/-- `log_{2^k} x` rounded to nearest at the precision of `x`. -/
def logBasePow2 (x : AzFloat) (k : AzInt) : AzFloat :=
  (logBasePow2PrecRound x k (x.precision?.getD 1) .Nearest).1

/-- `logBasePow2PrecRound` with the constants `c`; the same result
(`logBasePow2PrecRoundWith_eq_logBasePow2PrecRound`). -/
def logBasePow2PrecRoundWith (c : LnConsts) (x : AzFloat) (k : AzInt) (p : Nat)
    (mode : RoundingMode) : AzFloat × Ordering :=
  logBasePow2PrecRoundCore (logBasePow2ApproxWith c) (@logBasePow2ApproxWith_isSome_exists c)
    x k p mode

/-- `log_{2^k} x` rounded to nearest at the precision of `x`, with the constants `c`. -/
def logBasePow2With (c : LnConsts) (x : AzFloat) (k : AzInt) : AzFloat :=
  (logBasePow2PrecRoundWith c x k (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
