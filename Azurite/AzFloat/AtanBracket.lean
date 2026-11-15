/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosBracket

/-!
## The bracket of `arctan x`

`atanBracket x ex w` encloses `arctan |x|` for a finite float `x` of exponent `ex` at Ziv level
`w`.  The arctangent is computed from the sine and the cosine, by a certified Newton-like
iteration of order five on `tan y = t`:

* **The step** (`atanStepAt`, `atanStep`).  For `0 ≤ t ≤ 1` and a fixed-point number
  `0 ≤ y ≤ arctan t`,

    `arctan t = y + arctan δ`,  `δ = tan (arctan t − y) = (t cos y − sin y) / (cos y + t sin y)`,

  and `δ − δ³/3 ≤ arctan δ ≤ δ − δ³/3 + δ⁵/5` for `δ ≥ 0`.  `sin y` and `cos y` are the
  enclosures of `sinCosFix` (Algorithm 4.4 of *Modern Computer Arithmetic*), `δ` is one interval
  division, and the width of the result is `δ⁵/5` plus the rounding errors, so an approximation
  `y` good to `K/5` bits gives `K` bits.
* **The levels** (`atanLoop`).  The level of accuracy `K` (width at most `(3/4) 2^(−K)`) takes
  `y` from the lower end of level `⌈K/5⌉`, truncated to `⌈K/5⌉ + 3` fraction bits, and works at
  `K + lg K + 64` bits; level `K ≤ 1` is `atanBase`, `[t − t³/3, t]` (width at most `3/8`).
* **The seed** (`atanSeed`, `atanSeeded?`; tuning of 2026-11-15).  The levels up to `256` do
  not recurse: `y` is a 62-bit fixed-point approximation of `arctan t` computed in machine
  words (Euler's series), some `2^(−54)` below `arctan t`, and one step from it gives up to
  `256` bits.  The seed is **not proven**: the step certifies `y ≤ arctan t` by the sign of the
  lower end of `t cos y − sin y`, the width of the result is measured, and the proven recursion
  is the fallback.  So a level `K ≤ 256` costs one step, `K ≤ 1280` two, and so on; the whole
  costs little more than one `sinCosFix` at the top precision with a fifth of the argument
  bits.
* **The reduction** (`atanBracket`).  `|x| < 1` (`ex ≤ 0`): the loop at `K = w + 8 − ex`, i.e.
  with relative accuracy.  `|x| ≥ 1`: `arctan |x| = π/2 − arctan (1/|x|)`, the reciprocal
  enclosed by two divisions, the loop at its lower end and the upper end widened by the width of
  the reciprocal (`arctan` is `1`-Lipschitz), `π` from `piBracket`.

`atanApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Atan.lean` (negated and
swapped for `x < 0`), and `atanTiny?` the tiny-argument path: `−arctan |x|` lies in
`(−|x|, −|x| + |x|³]` just as `−sin |x|` does, so it is the test of `sinTiny?`.

The proofs are in `Equiv/AtanBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The base enclosure `[t − t³/3, t]` of `arctan t` for a float `0 ≤ t ≤ 1`, at precision
`V`. -/
def atanBase (t : AzFloat) (V : Nat) : Encl :=
  let c := (mulPrecRound (mulPrecRound t t V .Ceiling).1 t V .Ceiling).1
  let third := (divPrecRound c (ofAzNat (AzNat.ofNat 3)) V .Ceiling).1
  (clampNonneg (subPrecRound t third V .Floor).1, t)

/-- One step of the iteration for `arctan t`, `0 ≤ t ≤ 1`, from `y = M 2^(−T)`: the enclosure
`[y + δ_lo − (δ³/3)_hi, y + δ_hi − (δ³/3)_lo + (δ⁵/5)_hi]` with
`δ = (t cos y − sin y) / (cos y + t sin y)`, at the working precision `K + lg K + 64`, valid
when `0 ≤ y ≤ arctan t`.  The flag says that the lower end of the enclosure of
`t cos y − sin y` is not negative, which certifies `y ≤ arctan t`. -/
def atanStepAt (t : AzFloat) (M : AzNat) (T K : Nat) : Bool × Encl :=
  let V := K + (AzNat.ofNat K).size + 64
  let y := ofAzNat M <<< AzInt.ofInt (-(T : Int))
  let sc := sinCosFix M T V
  let te := Encl.exact t
  let raw := Encl.sub V (Encl.mul V te sc.2) sc.1
  let num := enclClamp0 raw
  let den := Encl.add V sc.2 (Encl.mul V te sc.1)
  let d := Encl.div V num den
  let d2 := Encl.mul V d d
  let c := Encl.mul V d2 d
  let third := Encl.div V c (Encl.nat 3)
  let fifth := Encl.div V (Encl.mul V c d2) (Encl.nat 5)
  (!raw.1.isNegative,
    (clampNonneg (addPrecRound y (subPrecRound d.1 third.2 V .Floor).1 V .Floor).1,
      (addPrecRound y (addPrecRound (subPrecRound d.2 third.1 V .Ceiling).1 fifth.2 V
        .Ceiling).1 V .Ceiling).1))

/-- One step of the iteration from an enclosure `b` whose lower end is in `[0, arctan t]`: `y` is
the lower end truncated to `K' + 3` fraction bits. -/
def atanStep (t : AzFloat) (b : Encl) (K' K : Nat) : Encl :=
  (atanStepAt t (floorScaled b.1 (K' + 3)) (K' + 3) K).2

/-- `⌊a b / 2^62⌋` for fixed-point numbers with 62 fraction bits (`a b < 2^126`). -/
@[inline] def atanSeedMul (a b : UInt64) : UInt64 :=
  let p := UInt64.wideMul a b
  (p.1 <<< 2) ||| (p.2 >>> 62)

/-- The tail `∑_{n ≥ 1} a_n` of the series of `atanSeedFix`, `a_n = a_{n−1} z (1 − 1/(2n+1))`,
until a term vanishes: `d = 2n + 1`, `a = a_{n−1}`, `s` the sum so far. -/
def atanSeedSum (z : UInt64) : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, s => s
  | fuel + 1, d, a, s =>
    let a1 := atanSeedMul a z
    let a2 := a1 - a1 / d
    if a2 == 0 then s else atanSeedSum z fuel (d + 2) a2 (s + a2)

/-- An **unverified** approximation from below of `arctan t` in fixed point with 62 fraction
bits, for `0 ≤ t ≤ 2^62` (i.e. `t ≤ 1`), in machine words: Euler's series

  `arctan t = (t/D) ∑_{n≥0} (2·4·…·2n)/(3·5·…·(2n+1)) z^n`,  `D = 1 + t²`,  `z = t²/D ≤ 1/2`,

with `1/D` by one machine division and two Newton steps from below.  The rounding errors are
some `150` units of `2^(−62)`; `256` units are subtracted so that the result is below
`arctan t`, by about `2^(−54)`.  Nothing is proven about it: `atanSeeded?` checks what it
needs. -/
def atanSeedFix (t : UInt64) : UInt64 :=
  let one : UInt64 := 4611686018427387904
  let t2 := atanSeedMul t t
  let D := one + t2
  let r0 := ((9223372036854775808 : UInt64) / ((D >>> 31) + 1)) <<< 30
  let r1 := r0 + atanSeedMul r0 (one - atanSeedMul D r0)
  let r := r1 + atanSeedMul r1 (one - atanSeedMul D r1)
  let s := atanSeedSum (atanSeedMul t2 r) 64 3 one one
  let y := atanSeedMul (atanSeedMul t r) s
  if y ≤ 256 then 0 else y - 256

/-- The seed of `arctan t` for a float `0 ≤ t ≤ 1`: `M` with `M 2^(−62) ≈ arctan t − 2^(−54)`
(unverified). -/
def atanSeed (t : AzFloat) : AzNat := (atanSeedFix (floorScaled t 62).toUInt64).toAzNat

/-- The enclosure of `arctan t` of width at most `(3/4) 2^(−K)` by **one** step from the seed,
for `K ≤ 256`: the step runs at level `max K 59` (so that its precision covers the 62 fraction
bits of the seed) and is accepted when the seed is certified to be at most `arctan t` (the flag
of `atanStepAt`) and the width of the result is small enough, both checked here; `none`
otherwise (in practice only for `t < 2^(−54)`, where the seed is `0`). -/
def atanSeeded? (t : AzFloat) (K : Nat) : Option Encl :=
  if 256 < K then none
  else
    let M := atanSeed t
    if M.size = 0 ∨ 62 < M.size then none
    else
      let Ke := max K 59
      let r := atanStepAt t M 62 Ke
      let wd := (subPrecRound r.2.2 r.2.1 64 .Ceiling).1
      if r.1 = true ∧
          le wd (ofAzNat (AzNat.ofNat 3) <<< AzInt.ofInt (-((Ke : Int) + 2))) = true then
        some r.2
      else none

/-- The enclosure of `arctan t` (`0 ≤ t ≤ 1`) of width at most `(3/4) 2^(−K)` when the fuel is
at least `K − 1`: level `K ≤ 256` is one step from the seed (`atanSeeded?`); otherwise, and as
the proven fallback, level `K ≥ 2` is a step from level `⌈K/5⌉`. -/
def atanLoop (t : AzFloat) : Nat → Nat → Encl
  | 0, K => atanBase t (K + 64)
  | fuel + 1, K =>
    if K ≤ 1 then atanBase t (K + 64)
    else
      match atanSeeded? t K with
      | some r => r
      | none => atanStep t (atanLoop t fuel ((K + 4) / 5)) ((K + 4) / 5) K

/-- The level of accuracy for an argument of exponent `ex ≤ 0` at Ziv level `w`. -/
def atanWork (ex : AzInt) (w : Nat) : Nat := w + 8 + (if ex.sign then 0 else ex.abs.toNat)

/-- The bracket of `arctan |x|` at Ziv level `w` for a finite `x` of exponent `ex`. -/
def atanBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  if ex.sign = false ∨ ex.abs.toNat = 0 then
    let K := atanWork ex w
    atanLoop x.abs K K
  else
    let K := w + 8
    let V := K + 64
    let rl := (divPrecRound one x.abs V .Floor).1
    let rh := (divPrecRound one x.abs V .Ceiling).1
    let b := atanLoop rl K K
    let up := (addPrecRound b.2 (subPrecRound rh rl 64 .Ceiling).1 V .Ceiling).1
    let P := piBracket V
    ((subPrecRound (P.1 <<< AzInt.ofInt (-1)) up V .Floor).1,
      (subPrecRound (P.2 <<< AzInt.ofInt (-1)) b.1 V .Ceiling).1)

/-- The bracket of `arctan x` as a pair of `Roundable`s: that of `arctan |x|`, negated and
swapped when `neg` (`x < 0`). -/
def atanApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := atanBracket x ex w
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- **The tiny-argument path of `arctan`** for a finite `x` of sign `s`, exponent `e` and
precision `q`: the test of `sinTiny?` (`|x| < 2^e`, `e ≤ −(max p q + 72)`), valid because
`|x| − |x|³ ≤ arctan |x| < |x|`. -/
def atanTiny? (s : Bool) (x : AzFloat) (e : AzInt) (q p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  sinTiny? s x e q p mode

end Azurite.AzFloat
