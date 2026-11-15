/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanBracket
import Azurite.AzFloat.SinRatBracket

/-!
## The bracket of `arctan q` for a rational `q`

`atanRatBracket q w` encloses `arctan |q|` for an `AzRat` `q` at Ziv level `w`, by the levels of
`AzFloat/AtanBracket.lean` at a float next to the argument:

* **The widening** (`atanWiden`).  For floats `0 ≤ r_lo ≤ t ≤ r_hi`, `r_lo ≤ 1`: `atanLoop` at
  `r_lo`, the upper end widened by `r_hi − r_lo` (`arctan` is `1`-Lipschitz).
* `|q| ≤ 1` (`num ≤ den`): the widening at `⌊|q|⌋_V`, `⌈|q|⌉_V`, at the level
  `K = atanWork (ratExpBound q) w` (`w + 8` plus the number of leading zero bits of `|q|`, so
  with relative accuracy) and `V = K + 64`.
* `|q| > 1`: `arctan |q| = π/2 − arctan (1/|q|)` with the reciprocal **rational** `1/|q|` (no
  division), the widening at level `K = w + 8`, `π` from `piBracket`.

`atanRatApprox` negates and swaps the ends for `q < 0`; `atanTinyRat?` is the tiny-argument
path, the test of `sinTinyRat?` (`−arctan |q| ∈ (−|q|, −|q| + |q|³]`).

The proofs are in `Equiv/AtanRatBracket.lean`.
-/

namespace Azurite.AzFloat

/-- An enclosure of `arctan t` from floats `0 ≤ rl ≤ t ≤ rh`, `rl ≤ 1`: the level `K` of
`atanLoop` at `rl`, the upper end widened by `rh − rl`, at precision `V`. -/
def atanWiden (rl rh : AzFloat) (K V : Nat) : Encl :=
  let b := atanLoop rl K K
  (b.1, (addPrecRound b.2 (subPrecRound rh rl 64 .Ceiling).1 V .Ceiling).1)

/-- The bracket of `arctan |q|` at Ziv level `w` for a rational `q`. -/
def atanRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  if q.num ≤ q.den then
    let K := atanWork (ratExpBound q) w
    let V := K + 64
    atanWiden (ofAzRatRound q.abs V .Floor).1 (ofAzRatRound q.abs V .Ceiling).1 K V
  else
    let K := w + 8
    let V := K + 64
    let r := q.abs⁻¹
    let b := atanWiden (ofAzRatRound r V .Floor).1 (ofAzRatRound r V .Ceiling).1 K V
    let P := piBracket V
    ((subPrecRound (P.1 <<< AzInt.ofInt (-1)) b.2 V .Floor).1,
      (subPrecRound (P.2 <<< AzInt.ofInt (-1)) b.1 V .Ceiling).1)

/-- The bracket of `arctan q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def atanRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := atanRatBracket q w
  if q.sign then (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)
  else (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)

/-- The tiny-argument path of `arctan q`: the test of `sinTinyRat?` (`|q| < 2^e`,
`e ≤ −(p + 72)`), valid because `|q| − |q|³ ≤ arctan |q| < |q|`. -/
def atanTinyRat? (q : AzRat) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  sinTinyRat? q p mode

end Azurite.AzFloat
