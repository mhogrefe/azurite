/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinhCoshBracket
import Azurite.AzFloat.Sinh
import Azurite.AzFloat.Cosh

/-!
## The hyperbolic sine and cosine together

`sinhCoshPrecRound x p mode` is the pair of `sinh x` and `cosh x`, each correctly rounded to
precision `p` in `mode` with the comparison against the exact value:
`sinhCoshPrecRound x p mode = (sinhPrecRound x p mode, coshPrecRound x p mode)`
(`sinhCoshPrecRound_eq`, `Equiv/SinhCosh.lean`), from **one** exponential.  `sinhCosh x` rounds
both to nearest at the precision of `x`.

A certified joint Ziv loop (`zivLoopCertified₂`, no fuel) on `sinhCoshApprox`
(`AzFloat/SinhCoshBracket.lean`), total because `sinh q` and `cosh q` are both irrational for
every rational `q ≠ 0`.  The exponential dominates, so the pair costs about half of the two
separate calls.

Tiny arguments (where the tiny-argument test of `sinh` or of `cosh` answers), zero, `NaN`, the
infinities and `p = 0` are delegated to `sinhPrecRound` and `coshPrecRound`.
-/

namespace Azurite.AzFloat

/-- `(sinh x, cosh x)`, each rounded to precision `p` with `mode` and paired with the
comparison with the exact value (as `sinhPrecRound` and `coshPrecRound`), from one
computation. -/
def sinhCoshPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  match x with
  | finite s e q m hv =>
    if hp : p = 0 then ((nan, .eq), (nan, .eq))
    else
      haveI : NeZero p := ⟨hp⟩
      match tanTiny? s (finite s e q m hv) e q p mode, expNearOne? true (coshTinyExp e) p mode with
      | none, none =>
        zivLoopCertified₂ (sinhCoshApprox (!s) (finite s e q m hv) e) p mode (p + zivGuardBits)
          (sinhCoshApprox_isSome_exists p mode (toVal_finite s e q m hv)
            (finiteVal_ne_zero s e hv) (abs_finiteVal_bounds s e hv).2
            (finiteVal_neg_iff s e hv) (p + zivGuardBits) (by unfold zivGuardBits; omega))
      | _, _ =>
        (sinhPrecRound (finite s e q m hv) p mode, coshPrecRound (finite s e q m hv) p mode)
  | _ => (sinhPrecRound x p mode, coshPrecRound x p mode)

/-- `(sinh x, cosh x)`, both rounded to nearest at the precision of `x`. -/
def sinhCosh (x : AzFloat) : AzFloat × AzFloat :=
  let r := sinhCoshPrecRound x (x.precision?.getD 1) .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
