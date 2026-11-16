/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcscBracket
import Azurite.AzFloat.Equiv.AsecBracket
import Azurite.AzFloat.Atan2

/-!
## The arccosecant

`acscPrecRound x p mode` is `arccsc x = arcsin (1/x)` — the inverse of the cosecant on
`[−π/2, π/2]`, defined for `|x| ≥ 1`, an odd function — correctly rounded to precision `p` in
`mode`, with the comparison against the exact value; `acsc x` rounds to nearest at the precision
of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `acscApprox` (`AzFloat/AcscBracket.lean`):
`arccsc |x| = 2 arctan (1/(|x| + √(x² − 1)))`.  The loop terminates because `arcsin q` is
irrational for every rational `q ≠ 0` in `[−1, 1]`.

**Oddness.**  The loop always runs on `arccsc |x|`; for `x < 0` the mode is negated and the
result is negated, so `acscPrecRound (−x) p mode` is the negation of
`acscPrecRound x p (−mode)`.

**Extreme arguments.**  For a huge `x` the result is `≈ 1/x`, enclosed with relative accuracy
by two divisions, at a cost that does not grow with the exponent.  When `x` is a power of two
the value `1/x + 1/(6x³) + …` is exponentially close to the float `1/x`; that float is the
exact lower end of the enclosure — this is why the loop runs on the absolute value.

Special values: `acsc NaN = NaN`; `acsc x = NaN` for `|x| < 1`, including `0`;
`acsc (±∞) = 0` (there is no negative zero); `acsc (±1) = ±π/2`, correctly rounded.
-/

namespace Azurite.AzFloat

/-- `arccsc x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `|x| < 1`, and for `p = 0` unless `x = ±∞`). -/
def acscPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => (nan, .eq)
  | finite s e q m hv =>
    if h1 : eqIEEE (finite s e q m hv).abs one = true then signedRound s piDiv2PrecRound p mode
    else if he : e.sign = true ∧ e.abs.toNat ≠ 0 then
      if hp : p = 0 then (nan, .eq)
      else
        haveI : NeZero p := ⟨hp⟩
        let o := !s
        let r := zivLoopCertified (acscApprox (finite s e q m hv) e.abs.toNat) p
          (if o then -mode else mode) (p + zivGuardBits)
          (acscApprox_isSome_exists p _ (toVal_finite s e q m hv)
            (one_lt_abs_of_exponent (abs_finiteVal_bounds s e hv).1 he (fun h => by
              have habs : (finite s e q m hv).abs.toVal
                  = some ((|finiteVal s e m| : ℝ) : EReal) := by
                rw [toVal_abs, toVal_finite, Option.map_some, ← EReal.coe_neg]
                congr 1
              exact h1 ((eqIEEE_iff _ _).mpr ⟨_, habs, by rw [h]; exact toVal_one'⟩)))
            (two_pow_le_of_exponent (abs_finiteVal_bounds s e hv).1 he) (p + zivGuardBits)
            (by unfold zivGuardBits; omega))
        if o then (-r.1, r.2.swap) else r
    else (nan, .eq)

/-- `arccsc x` rounded to nearest at the precision of `x` (`0` for `x = ±∞`). -/
def acsc (x : AzFloat) : AzFloat := (acscPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
