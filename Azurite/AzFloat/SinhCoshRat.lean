/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.SinhCoshBracket
import Azurite.AzFloat.SinhRat
import Azurite.AzFloat.CoshRat

/-!
## The hyperbolic sine and cosine of a rational together

`sinhCoshRatPrecRound q p mode` is the pair of `sinh q` and `cosh q` for an `AzRat` `q`, each
correctly rounded to precision `p` in `mode` with the comparison against the exact value:
`sinhCoshRatPrecRound q p mode = (sinhRatPrecRound q p mode, coshRatPrecRound q p mode)`
(`sinhCoshRatPrecRound_eq`, `Equiv/SinhCosh.lean`), from **one** exponential.
`sinhCoshRat q p` rounds both to nearest.

A certified joint Ziv loop (`zivLoopCertified₂`, no fuel) on `sinhCoshRatApprox`
(`AzFloat/SinhCoshBracket.lean`).  `q = 0`, `p = 0` and tiny arguments (where the tiny-argument
test of `sinhRat` or of `coshRat` answers) are delegated to `sinhRatPrecRound` and
`coshRatPrecRound`.
-/

namespace Azurite.AzFloat

/-- `(sinh q, cosh q)` for a rational `q`, each rounded to precision `p` with `mode` and
paired with the comparison with the exact value (as `sinhRatPrecRound` and
`coshRatPrecRound`), from one computation. -/
def sinhCoshRatPrecRound (q : AzRat) (p : Nat) (mode : RoundingMode) :
    (AzFloat × Ordering) × (AzFloat × Ordering) :=
  if h0 : q.num = 0 then (sinhRatPrecRound q p mode, coshRatPrecRound q p mode)
  else if hp : p = 0 then (sinhRatPrecRound q p mode, coshRatPrecRound q p mode)
  else
    haveI : NeZero p := ⟨hp⟩
    match tanTinyRat? q p mode, expNearOne? true (coshRatTinyExp q) p mode with
    | none, none =>
      zivLoopCertified₂ (sinhCoshRatApprox q) p mode (p + zivGuardBits)
        (sinhCoshRatApprox_isSome_exists p mode q h0 (p + zivGuardBits)
          (by unfold zivGuardBits; omega))
    | _, _ => (sinhRatPrecRound q p mode, coshRatPrecRound q p mode)

/-- `(sinh q, cosh q)`, both rounded to nearest at precision `p`. -/
def sinhCoshRat (q : AzRat) (p : Nat) : AzFloat × AzFloat :=
  let r := sinhCoshRatPrecRound q p .Nearest
  (r.1.1, r.2.1)

end Azurite.AzFloat
