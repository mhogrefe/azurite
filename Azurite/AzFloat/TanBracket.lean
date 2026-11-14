/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosBracket

/-!
## The bracket of `tan x`

`tanBracket x ex w` encloses `tan |x|` for a finite float `x` of exponent `ex` at Ziv level `w`
as the quotient of the two components of the joint bracket `sinCosBracket x ex w` (Brent and
Zimmermann, *Modern Computer Arithmetic*, §4.9.1: "the simultaneous computation of `sin x` and
`cos x` might be useful to compute `tan x`"; `tan` has no hypergeometric series of its own,
§4.4): with `[sin |x|] = [sl, sh]` and `[|cos x|] = [b₁, b₂]` (`enclAbs`),

* if `b₁ = 0` — the bracket of `cos x` contains `0`, the working precision does not yet separate
  `x` from a pole — the **dummy bracket** `[−1, 1]` is returned: it is not an enclosure, but
  `roundingPossible` never accepts it (the floors of its ends differ at every precision), so the
  Ziv loop just moves on to the next level;
* otherwise `enclDivSignedPos` divides: the lower end is `⌊sl/b₁⌋` for `sl < 0` and `⌊sl/b₂⌋`
  for `sl ≥ 0`, the upper end `⌈sh/b₂⌉` for `sh < 0` and `⌈sh/b₁⌉` for `sh ≥ 0` (two divisions at
  `V = w + 12` bits; the version with four divisions and no sign test was measured 2 % slower),
  and the result is negated when `cos x < 0`.

`tanApprox neg` gives the `Roundable`s, negated and swapped for `x < 0` (`tan` is odd).

**Tiny arguments** (`tanTiny?`): for `|x| < 2^e`, `e ≤ −(max p q + 72)`, `tan |x|` lies in
`(|x|, |x| + |x|³]`, so it is rounded by one test of `roundingPossible` with the exact end `|x|`
at the open side (in the negated mode, the result negated, for `x < 0`); the Ziv loop would need
about `2|e|` bits to see the side of `x`.
-/

namespace Azurite.AzFloat

/-- `[s] / [b]` for an enclosure `[s]` of any sign and a positive enclosure `[b]`, with two
directed divisions: a negative end is divided by the end of `[b]` that makes the quotient larger
in magnitude in the right direction (`s.1 < 0` by `b.1`, `s.1 ≥ 0` by `b.2` for the lower end,
and the other way round for the upper end). -/
def enclDivSignedPos (w : Nat) (s b : Encl) : Encl :=
  ((divPrecRound s.1 (if s.1.isNegative then b.1 else b.2) w .Floor).1,
    (divPrecRound s.2 (if s.2.isNegative then b.2 else b.1) w .Ceiling).1)

/-- The bracket of `tan |x|` at Ziv level `w` for a finite `x` of exponent `ex`, or the dummy
bracket `[−1, 1]` (never accepted by `roundingPossible`) when the bracket of `cos x` contains
`0`. -/
def tanBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let b := sinCosBracket x ex w
  let B := enclAbs b.2
  match B.1 with
  | zero => (-one, one)
  | _ =>
    let T := enclDivSignedPos (w + 12) b.1 B
    if b.2.2.isNegative then Encl.neg T else T

/-- The bracket of `tan x` as a pair of `Roundable`s: that of `tan |x|`, negated and swapped
when `neg` (`x < 0`). -/
def tanApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := tanBracket x ex w
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- **The tiny-argument path of `tan`** for a finite `x` of sign `s`, exponent `e` and precision
`q` (see the module documentation).  `none` when the argument is not tiny or the test fails. -/
def tanTiny? (s : Bool) (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let w := max p q + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let ax := x.abs
    let hi := (addPrecRound ax ((ax <<< e) <<< e) (w + 8) .Ceiling).1
    let r := roundingPossible (fun P M => setPrecRound ax P M) (fun P M => setPrecRound hi P M) p
      (if s then mode else -mode)
    if s then r else r.map fun r => (-r.1, r.2.swap)
  else none

end Azurite.AzFloat
