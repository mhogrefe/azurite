/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.AtanRatBracket

/-!
## The bracket of `arccot x`

`arccot x = arctan (1/x)`, the odd arccotangent with range `(−π/2, π/2]` (not the continuous
branch `π/2 − arctan x`).  `acotBracket x e w` encloses `arccot |x| = arctan (1/|x|) ∈ (0, π/2)`
for a finite float `x ≠ 0` of exponent `e`, with width at most `2^(−w)`:

* `|x| < 1` (`e ≤ 0`): `π/2 − arctan |x|`, the arctangent by `atanLoop` at the level `w + 8`
  — absolute accuracy is enough next to `π/2`, so a tiny `x` costs nothing extra.
* `|x| ≥ 1` (`e ≥ 1`), `2e < w + 16`: `atanWiden` of the two directed quotients `1/|x|`, at the
  level `w + 8 + e` (relative accuracy: the result is about `2^(−e)`).
* `|x| ≥ 1`, `2e ≥ w + 16`: `acotTinyEncl`, from `(1/a)(1 − 1/a²) ≤ arctan (1/a) < 1/a`: two
  directed divisions and a factor `1 − 2^(−w−14)`.  Its **upper** end is the correctly rounded
  `1/a` — exactly `1/a` when `a` is a power of two, the case in which `arccot a` is
  exponentially close to a float, from below.

`acotApprox` is the pair of `Roundable`s of the **negated** enclosure: the Ziv loop of
`AzFloat/Acot.lean` always runs on `−arccot |x|`, so that the exact end is the lower one.

The proofs are in `Equiv/AcotBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The enclosure `[(1/a)(1 − 2^(−w−14)), 1/a]` (rounded outwards at `w + 16` bits) of
`arctan (1/a)` for a float `a` with `1/a² ≤ 2^(−w−14)`. -/
def acotTinyEncl (a : AzFloat) (w : Nat) : Encl :=
  let W := w + 16
  let c := (subPrecRound one (one <<< AzInt.ofInt (-((w : Int) + 14))) W .Floor).1
  ((mulPrecRound (divPrecRound one a W .Floor).1 c W .Floor).1,
    (divPrecRound one a W .Ceiling).1)

/-- The bracket of `arccot |x| = arctan (1/|x|)` at Ziv level `w` for a finite `x ≠ 0` of
exponent `e`. -/
def acotBracket (x : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  let a := x.abs
  if e.sign = true ∧ e.abs.toNat ≠ 0 then
    if w + 16 ≤ 2 * e.abs.toNat then acotTinyEncl a w
    else
      let K := w + 8 + e.abs.toNat
      atanWiden (divPrecRound one a (K + 64) .Floor).1 (divPrecRound one a (K + 64) .Ceiling).1
        K (K + 64)
  else piShiftEncl true false (atanLoop a (w + 8) (w + 8)) (w + 72)

/-- The bracket of `−arccot |x|` as a pair of `Roundable`s. -/
def acotApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox true (acotBracket x e w)

end Azurite.AzFloat
