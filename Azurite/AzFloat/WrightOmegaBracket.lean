/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LambertWBracket
import Azurite.AzFloat.LnEncl
import Azurite.AzFloat.ExpRat

/-!
## Brackets of the real Wright `ω` function

`ω(x) = W₀(eˣ)` is the positive root of `y + ln y = x` (DLMF 4.13.1_2; `wrightOmegaReal` of
`DLMF/Chapter4/Section13Real.lean`).  The bracket is taken from that equation, not from `eˣ`:
for a large `x` the exponential is astronomically larger than `ω(x) ≈ x − ln x`.

* **The candidate** (`omegaCandidate`, unverified): a seed (`Float` Newton steps, or `eˣ` and
  `x − ln x` outside the `Float` range) refined by Newton's iteration for `y + ln y = x`
  (`logSeedStep`) at doubling precisions, up to **half** the bits wanted.
* **The enclosure** (`omegaEncl`): with the residual `d = n + ln n − x` of the candidate `n`
  enclosed at full precision (one logarithm), `n − ω = d c` where `c` lies between `t/(1 + t)`
  at `t = min(n, ω)` and at `t = max(n, ω)` (`Transcendental/WrightOmega.lean`).  The crude
  bounds `n − d⁺ min(1, n) ≤ ω ≤ n + d⁻ k` (`d⁺ = max(d, 0)`, `d⁻ = max(−d, 0)`, `k = min(1, 2n)`
  when `d⁻ ≤ 1/2` and `1` otherwise) enclose `c`, and `ω ∈ n − [d]·[c]` then has a width of the
  order `d²`: the verification is also the last Newton step.  The cost is about two
  logarithms.
* **The fallback.**  The candidate is never trusted: if the enclosure is not narrower than
  `2^(−w)` relative, the bracket is that of `W₀` at `eˣ` (`lambertBracket`, with `eˣ` entering
  through its `Floor`/`Ceiling` roundings `expAt`, `expRatAt`), whose width is proven to tend
  to zero.  It only serves the termination proof.
* **Large arguments** (`wrightOmegaHuge?`): `x − ln x < ω(x) < x`, and `x` can be a float, so
  the loop would need about as many bits as the exponent of `x` to see on which side of it the
  value lies; the inequalities settle the rounding by one test.

The proofs are in `Equiv/WrightOmegaBracket.lean`.
-/

namespace Azurite.AzFloat

/-! ### The target -/

/-- The enclosure function of `eˣ` for a float `x`: its `Floor` and `Ceiling` roundings. -/
def expAt (x : AzFloat) : Nat → AzFloat × AzFloat :=
  fun P => ((expPrecRound x P .Floor).1, (expPrecRound x P .Ceiling).1)

/-- The enclosure function of `e^q` for a rational `q`: its `Floor` and `Ceiling` roundings. -/
def expRatAt (q : AzRat) : Nat → AzFloat × AzFloat :=
  fun P => ((expRatPrecRound q P .Floor).1, (expRatPrecRound q P .Ceiling).1)

/-- Is the value of `x` equal to `1`? -/
def isOne (x : AzFloat) : Bool := le x one && le one x

/-! ### The candidate (unverified) -/

/-- Newton's iteration for `y + ln y = x` in `Float`. -/
def omegaFloat (x : Float) : Nat → Float → Float
  | 0, y => y
  | k + 1, y => omegaFloat x k (y - (y + Float.log y - x) * y / (1 + y))

/-- A seed for the candidate, with about `48` bits: eight Newton steps in `Float` from `eˣ`
(`x < −1`), from the tangent of `ω` at `0` (`−1 ≤ x ≤ 2`) or from `x − ln x` (`x > 2`), all
below `e^(1+x)`, where a Newton step stays positive.  Outside the `Float` range (and below
`−700`, where `eˣ` leaves the normal range) the same start values at 64 bits: they are within a
relative `eˣ`, respectively `ln x / x`, of `ω(x)`. -/
def omegaSeed (x : AzFloat) : AzFloat :=
  let big : Unit → AzFloat := fun _ =>
    if lt x one then (expPrecRound x 64 .Nearest).1
    else (subPrecRound x (lnPrecRound x 64 .Nearest).1 64 .Nearest).1
  let xf := toFloat64 x
  if xf.isFinite && xf ≥ -700 then
    let y₀ := if xf < -1 then Float.exp xf
      else if xf ≤ 2 then 0.5671432904097838 + 0.36 * xf
      else xf - Float.log xf
    let y := omegaFloat xf 8 y₀
    if y.isFinite && y > 0 then ofFloat64 y else big ()
  else big ()

/-- Newton steps (`logSeedStep`) from a seed with about `48` bits up to `target` bits, planned
backwards: the step to `target` bits starts from `target/2 + 8`, so every step is limited by
its precision and not by the accuracy of its start (a forward schedule `a ↦ 2a − c` doubles
its deficit at every step).  A step is taken at `8` bits beyond the target and the bit length
of the exponent of the iterate (`|ln n|` for a tiny `n`). -/
def omegaRefine (x seed : AzFloat) : Nat → Nat → AzFloat
  | 0, _ => seed
  | fuel + 1, target =>
    if target ≤ 40 then seed
    else
      let n := omegaRefine x seed fuel (target / 2 + 8)
      logSeedStep x n (target + expSize n + 8)

/-- The unverified candidate for `ω(x)` with about `target` correct bits. -/
def omegaCandidate (xAt : Nat → AzFloat × AzFloat) (target : Nat) : AzFloat :=
  let x := (xAt (target + expSize (xAt 64).1 + 80)).1
  omegaRefine x (omegaSeed x) (target.log2 + 2) target

/-! ### The enclosure around a candidate -/

/-- The enclosure of `ω(x)` from an enclosure `X` of `x` and a positive float `n`, at
precision `P`: `n − [D]·[c₁, c₂]` with `D` the enclosure of `n + ln n − x`. -/
def omegaEncl (X : Encl) (n : AzFloat) (P : Nat) : Encl :=
  let D := Encl.sub P (Encl.add P (Encl.exact n) (lnOfEncl (Encl.exact n) P)) X
  let dp := maxOf zero D.2
  let dm := maxOf zero (-D.1)
  let m := maxOf zero (subPrecRound n (mulPrecRound dp (minOf one n) P .Ceiling).1 P .Floor).1
  let k := if le dm oneHalf then minOf one (n <<< AzInt.ofInt 1) else one
  let M := (addPrecRound n (mulPrecRound dm k P .Ceiling).1 P .Ceiling).1
  let c₁ := (divPrecRound m (addPrecRound one m P .Ceiling).1 P .Floor).1
  let c₂ := (divPrecRound M (addPrecRound one M P .Floor).1 P .Ceiling).1
  let U := if lt zero D.2 then (mulPrecRound D.2 c₂ P .Ceiling).1
    else (mulPrecRound D.2 c₁ P .Ceiling).1
  let L := if lt D.1 zero then (mulPrecRound D.1 c₂ P .Floor).1
    else (mulPrecRound D.1 c₁ P .Floor).1
  ((subPrecRound n U P .Floor).1, (subPrecRound n L P .Ceiling).1)

/-- The working precision at Ziv level `w` for a candidate `n`: `w + 24 + 2 lg w` bits (the
bracket of the logarithm at level `P` is about `2 lg P` bits wider than `2^(−P)`) beyond the
bit length of the exponent of `n`, at least `64`. -/
def omegaWork (n : AzFloat) (w : Nat) : Nat := max 64 (w + 24 + 2 * w.log2 + expSize n)

/-- The bracket of `ω(x)` at Ziv level `w`: the enclosure around the candidate when it is
narrower than `2^(−w)` relative, otherwise the bracket of `W₀` at `eˣ`. -/
def wrightBracket (xAt eAt : Nat → AzFloat × AzFloat)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt eAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    (w : Nat) : AzFloat × AzFloat :=
  let n := omegaCandidate xAt (w / 2 + 8)
  let I := omegaEncl (xAt (omegaWork n w)) n (omegaWork n w)
  if n.isFinite && lt zero n
    && le (subPrecRound I.2 I.1 64 .Ceiling).1 (I.1 <<< (-(AzNat.ofNat w).toAzInt))
  then I
  else lambertBracket true eAt none (aprioriW0Pos eAt 64) hs w

/-- The bracket as a pair of `Roundable`s. -/
def wrightApprox (xAt eAt : Nat → AzFloat × AzFloat)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt eAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    (w : Nat) : Roundable × Roundable :=
  let b := wrightBracket xAt eAt hs w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-! ### Large arguments -/

/-- **The large-argument path of `ω`** for an argument `1 < x < 2^e`, given by the rounding
procedure `nx` of `−x`, a float `nxHi ≥ −x` and a float `xLo ≤ x`: `−ω(x)` lies in
`(−x, −x + ln x)`, so it is rounded in the negated mode by the test of `roundingPossible` on
`(−x, ⌈nxHi + e⌉_{w+8}]`, and the result is negated.  (The exact end `x`, often a rounding
boundary, must be at the open side, and the Ziv loop would need about `e` bits to see the
side.)  `none` when `e` is too small for the test to succeed, when `xLo ≤ 1`, or when the test
fails. -/
def wrightOmegaHuge? (nx : Roundable) (nxHi xLo : AzFloat) (e : AzInt) (w p : Nat)
    (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  if e.sign = true ∧ w + 8 + e.abs.size ≤ e.abs.toNat ∧ lt one xLo = true then
    let hi := (addPrecRound nxHi (ofAzInt e) (w + 8) .Ceiling).1
    (roundingPossible nx (fun P M => setPrecRound hi P M) p (-mode)).map
      fun r => (-r.1, r.2.swap)
  else none

end Azurite.AzFloat
