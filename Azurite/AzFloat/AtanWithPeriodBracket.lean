/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanBracket

/-!
## The bracket of `arctan (x) u / (2π)`

The arctangent measured in `u`ths of a turn.

* `atanAbsEncl x ex w` is an enclosure of `arctan |x|` with a nonnegative lower end and width at
  most `2^(−w)`: `atanBracket x ex w` with the lower end clamped at `0`, except for a **tiny**
  argument (`|x| < 2^ex`, `2 ex ≤ −(w + 8)`), where it is `[|x| − |x| 2^(2 ex), |x|]` — from
  `x − x³ ≤ arctan x ≤ x` — at a cost independent of the exponent.
* `atanPeriodScale A u V` multiplies an enclosure `A` of an angle `0 ≤ θ ≤ 2` by `u/(2π)`: one
  interval division by `piBracket V`, then the exact float `u/2` with directed roundings.
* `atanPeriodApprox neg x ex u w` is the pair of `Roundable`s for the Ziv loop of
  `AzFloat/AtanWithPeriod.lean` (negated and swapped for `x < 0`).

The proofs are in `Equiv/AtanWithPeriodBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `arctan |x|` with a nonnegative lower end, for a finite `x` of exponent `ex`
at level `w`: `[|x| − |x| 2^(2 ex), |x|]` for a tiny argument, `atanBracket` otherwise. -/
def atanAbsEncl (x : AzFloat) (ex : AzInt) (w : Nat) : Encl :=
  if ex.sign = false ∧ w + 8 ≤ 2 * ex.abs.toNat then
    let xa := x.abs
    (clampNonneg (subPrecRound xa ((xa <<< ex) <<< ex) (w + 64) .Floor).1, xa)
  else
    let a := atanBracket x ex w
    (clampNonneg a.1, a.2)

/-- `A u / (2π)` for a nonnegative enclosure `A` and a natural `u`, at precision `V`. -/
def atanPeriodScale (A : Encl) (u : AzNat) (V : Nat) : Encl :=
  let d := Encl.div V A (piBracket V)
  let uf := ofAzNat u <<< AzInt.ofInt (-1)
  ((mulPrecRound d.1 uf V .Floor).1, (mulPrecRound d.2 uf V .Ceiling).1)

/-- The bracket of `arctan (x) u / (2π)` as a pair of `Roundable`s: that of
`arctan |x| u / (2π)`, negated and swapped when `neg` (`x < 0`). -/
def atanPeriodApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (u : AzNat) (w : Nat) :
    Roundable × Roundable :=
  let b := atanPeriodScale (atanAbsEncl x ex w) u (w + 64)
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
