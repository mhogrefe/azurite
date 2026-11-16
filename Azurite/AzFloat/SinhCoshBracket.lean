/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhRatBracket
import Azurite.AzFloat.CoshBracket

/-!
## The joint brackets of `sinh x` and `cosh x`

Both functions from **one** exponential: with the enclosure `u` of `exp |x| − 1`
(`expM1Bracket`, relative accuracy for a small `x`),

* `sinh |x| = (u + u/(1 + u))/2` by `sinhOfExpM1 u` — this is `sinhBracket` itself, and
* `cosh x = (E + 1/E)/2` by `coshOfExp` on `E = 1 + u`, rounded outwards (`expOfExpM1`).

`sinhCoshApprox neg x e w` is the pair of pairs of `Roundable`s for the joint Ziv loop of
`AzFloat/SinhCosh.lean` (the sine part negated and swapped for `x < 0`), and
`sinhCoshRatApprox q w` the same from `expM1RatBracket |q|` for a rational
(`AzFloat/SinhCoshRat.lean`).  The exponential being by far the dominant cost, the pair costs
about half of the two separate computations.

The proofs are in `Equiv/SinhCoshBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `E = 1 + u` from an enclosure of `u ≥ 0`, rounded outwards at precision
`W`. -/
def expOfExpM1 (u : Encl) (W : Nat) : Encl :=
  ((addPrecRound one (clampNonneg u.1) W .Floor).1, (addPrecRound one u.2 W .Ceiling).1)

/-- The brackets of `sinh` and `cosh` from an enclosure of `exp a − 1`, `a ≥ 0`. -/
def sinhCoshOfExpM1 (u : Encl) (w : Nat) : Encl × Encl :=
  (sinhOfExpM1 u (w + 16), coshOfExp (expOfExpM1 u (w + 16)) (w + 16))

/-- The joint bracket of `sinh x` and `cosh x` as pairs of `Roundable`s (`neg`: `x < 0`), for a
finite `x` with `|x| < 2^e`. -/
def sinhCoshApprox (neg : Bool) (x : AzFloat) (e : AzInt) (w : Nat) :
    (Roundable × Roundable) × (Roundable × Roundable) :=
  let b := sinhCoshOfExpM1 (expM1Bracket x.abs e w) w
  (enclApprox neg b.1, enclApprox false b.2)

/-- The joint bracket of `sinh q` and `cosh q` as pairs of `Roundable`s, for a rational
`q ≠ 0`. -/
def sinhCoshRatApprox (q : AzRat) (w : Nat) :
    (Roundable × Roundable) × (Roundable × Roundable) :=
  let b := sinhCoshOfExpM1 (expM1RatBracket q.abs w) w
  (enclApprox (!q.sign) b.1, enclApprox false b.2)

end Azurite.AzFloat
