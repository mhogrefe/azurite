/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AcschBracket

/-!
## The inverse hyperbolic cosecant

`acschPrecRound x p mode` is `acsch x = asinh (1/x) = ln (1/x + √(1/x² + 1))` correctly rounded
to precision `p` in `mode`, with the comparison against the exact value; `acsch x` rounds to
nearest at the precision of `x`.

A certified Ziv loop (`zivLoopCertified`, no fuel) on `acschApprox`
(`AzFloat/AcschBracket.lean`).  The loop terminates because `asinh q` is irrational for every
rational `q ≠ 0` (`irrational_arsinh_rat`), here `q = 1/x`.

**Oddness.**  The loop always runs on `−acsch |x|`; for `x > 0` the mode is negated and the
result is negated, so `acschPrecRound (−x) p mode` is the negation of
`acschPrecRound x p (−mode)`.

**Extreme arguments.**  For a huge `x` the result is `≈ 1/x`, enclosed with relative accuracy
by two divisions, at a cost that does not grow with the exponent.  When `x` is a power of two
the value `1/x − 1/(6x³) + …` is exponentially close to the float `1/x`, from below; that float
is the exact upper end of the enclosure of `acsch |x|`, hence the exact lower end of the
negated one — this is why the loop runs on the negated absolute value.  A tiny `x` gives
`≈ ±ln (2/|x|)` and costs one logarithm.

Special values: `acsch NaN = NaN`; `acsch (±∞) = 0` (there is no negative zero);
`acsch 0 = +∞` (there is one zero only).
-/

namespace Azurite.AzFloat

/-- `acsch x` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` and a finite `x ≠ 0`). -/
def acschPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => (infinity true, .eq)
  | finite s e q m hv =>
    if hp : p = 0 then (nan, .eq)
    else
      haveI : NeZero p := ⟨hp⟩
      let r := zivLoopCertified (acschApprox (finite s e q m hv) e) p
        (if s then -mode else mode) (p + zivGuardBits + acschExtra e p)
        (acschApprox_isSome_exists p _ (toVal_finite s e q m hv) (finiteVal_ne_zero s e hv)
          (abs_finiteVal_bounds s e hv).1 _ (by unfold zivGuardBits; omega))
      if s then (-r.1, r.2.swap) else r

/-- `acsch x` rounded to nearest at the precision of `x`. -/
def acsch (x : AzFloat) : AzFloat := (acschPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
