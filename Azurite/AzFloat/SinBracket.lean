/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosBracket

/-!
## The bracket of `sin x`

`sinBracket x ex w` encloses `sin |x|` for a finite float `x` of exponent `ex` at Ziv level `w`
(reduction precision `W = cosWork ex w`, series precision `V = w + 12`), by the machinery of
`cosBracket` at a shifted centre:
with `[lo, hi]` the bracket of `π` and the exact reduction `r' = remExact |x| (2 lo)`,
`sin |x| = sin r = cos (r − π/2)` for the true reduction `r ∈ [r' − E, r']`, and
`t = r − π/2` lies within `E₂ = E + ⌈hi − lo⌉ + 2^(4−V)` below the float
`s = ⌈r' − lo/2⌉_V`.  `cosTail s E₂ V` (`CosBracket.lean`) is the series of `cos (s/8)`, the
Lipschitz widening by `E₂/8`, and three double-angle steps (valid since
`t/8, t/4 ∈ [−π/2, π/2]`).  `sinApprox neg` gives the `Roundable`s, negated and swapped for
`x < 0` (`sin` is odd).

**Tiny arguments** (`sinTiny?`): for `|x| < 2^e`, `e ≤ −(max p q + 72)`, `−sin |x|` lies in
`(−|x|, −|x| + |x|³]`, so it is rounded by one test of `roundingPossible` with the exact end
`−|x|` at the open side (in the negated mode, the result negated, for `x > 0`); the Ziv loop
would need about `2|e|` bits to see the side of `x`.
-/

namespace Azurite.AzFloat

/-- The bracket of `sin |x|` at Ziv level `w` for a finite `x` of exponent `ex` (reduction
precision `W = cosWork ex w`, series precision `V = w + 12`). -/
def sinBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let W := cosWork ex w
  let V := w + 12
  let P := piBracket W
  let y := P.1 <<< AzInt.ofInt 1
  let r := remExact x.abs y
  let d := (subPrecRound P.2 P.1 64 .Ceiling).1
  let E := (mulPrecRound x.abs d 64 .Ceiling).1
  let s := (subPrecRound r (P.1 <<< AzInt.ofInt (-1)) V .Ceiling).1
  let E₂ := (addPrecRound (addPrecRound E d 64 .Ceiling).1 (one <<< AzInt.ofInt (4 - (V : Int)))
    64 .Ceiling).1
  cosTail s E₂ V

/-- The bracket of `sin x` as a pair of `Roundable`s: that of `sin |x|`, negated and swapped
when `neg` (`x < 0`). -/
def sinApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := sinBracket x ex w
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- **The tiny-argument path of `sin`** for a finite `x` of sign `s`, exponent `e` and precision
`q` (see the module documentation).  `none` when the argument is not tiny or the test fails. -/
def sinTiny? (s : Bool) (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let w := max p q + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let nx := -x.abs
    let hi := (addPrecRound nx ((x.abs <<< e) <<< e) (w + 8) .Ceiling).1
    let r := roundingPossible (fun P M => setPrecRound nx P M) (fun P M => setPrecRound hi P M) p
      (if s then -mode else mode)
    if s then r.map fun r => (-r.1, r.2.swap) else r
  else none

end Azurite.AzFloat
