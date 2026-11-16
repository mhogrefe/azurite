/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatBracket
import Azurite.AzFloat.TanhBracket

/-!
## The bracket of the Gudermannian `gd x`

`gd x = ∫₀ˣ sech t dt` (DLMF 4.23.39) is odd, increasing, and tends to `π/2`.  For `a = |x| > 0`
the bracket `gdBracket a e w` at Ziv level `w` uses two identities:

  `gd a = 2 arctan (tanh (a/2))`,        `gd a = π/2 − 2 arctan (e^(−a))`,

the first with a small arctangent argument for a small `a`, the second for a large one (the
two arguments agree at `a = ln (1 + √2)`, where both are `√2 − 1`).  One exponential is
needed in either case; what differs is the arctangent.

* **Huge arguments** (`gdHuge`): when `a ≥ N ≥ w + 8`, `0 < π/2 − gd a < 2 e^(−a) ≤ 2^(1−N)`,
  so the bracket is that of `π/2` with the lower end lowered by `2^(1−N)`: no exponential, and
  a cost independent of `a`.
* **The alternating series** (`atanAlt`): for an enclosure of `z ∈ [0, 1]`,

    `arctan z = z − z³/3 + z⁵/5 − ⋯`,

  with the partial sums alternately below and above, so the sum of `k` terms and the next term
  enclose `arctan z` whatever `k` is.  The loop runs on enclosures (`Encl`) until a term
  drops below `2^(−K−2)` or the fuel `gdSeriesTerms` is spent.  It is tried when few terms
  are expected — `gdSmallSeries?` for `a < 1` with `z = tanh (a/2)` when `64 (1 − e) ≥ K`,
  `gdLargeSeries?` for `a ≥ 1` with `z = e^(−a)` when `92 ⌊a⌋ ≥ K` (thresholds measured:
  about 32 terms cost what the general arctangent does, at every precision tried) — and it
  is **accepted only if its measured width is small enough** (`enclNarrow?`).  So nothing has
  to be proven about its convergence: a result that is too wide falls back to the next path.
  In the large case `e^(−a)` is only needed to `K − ⌊a⌋` bits.
* **The general path** (`gdCore`): `2 arctan (tanh (a/2))` with the hyperbolic tangent from
  `tanhBracket` (one `expm1`, relative accuracy for a small `a`) and the arctangent by the
  certified iteration of `AzFloat/AtanBracket.lean` (`atanWiden`), at the level
  `K = atanWork e w`, i.e. with relative accuracy.

`gdApprox` is the pair of `Roundable`s for the Ziv loop of `AzFloat/Gd.lean` (negated and
swapped for `x < 0`).  The tiny-argument path is that of the sine (`sinTiny?`):
`|x| − |x|³ ≤ gd |x| < |x|`.

`gdRatBracket q w` is the same on the rational brackets (`tanhRatBracket`, `expRatBracket`),
through the shared steps `gdSmallOf`, `gdLargeOf`, `gdCoreOf`.

The proofs are in `Equiv/GdBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The end of the alternating series after `k` terms: the sum `acc` of the first `k` terms and
the next term enclose the value, from below for an even `k` and from above for an odd one. -/
def atanAltClose (V k : Nat) (acc term : Encl) : Encl :=
  if k % 2 = 0 then (acc.1, (addPrecRound acc.2 term.2 V .Ceiling).1)
  else ((subPrecRound acc.1 term.2 V .Floor).1, acc.2)

/-- The alternating series `∑ (−1)^k z^(2k+1)/(2k+1)` on enclosures, at precision `V`: `z2`
encloses `z²`, `p` encloses `z^(2k+1)`, `acc` the sum of the first `k` terms.  It stops when
the upper end of a term is below `tau` or the fuel is spent. -/
def atanAltLoop (V : Nat) (z2 : Encl) (tau : AzFloat) : Nat → Nat → Encl → Encl → Encl
  | 0, k, p, acc => atanAltClose V k acc (Encl.div V p (Encl.nat (2 * k + 1)))
  | fuel + 1, k, p, acc =>
    if lt (Encl.div V p (Encl.nat (2 * k + 1))).2 tau = true then
      atanAltClose V k acc (Encl.div V p (Encl.nat (2 * k + 1)))
    else
      atanAltLoop V z2 tau fuel (k + 1) (Encl.mul V p z2)
        (if k % 2 = 0 then Encl.add V acc (Encl.div V p (Encl.nat (2 * k + 1)))
          else Encl.sub V acc (Encl.div V p (Encl.nat (2 * k + 1))))

/-- An enclosure of `arctan z` for an enclosure `z` of a number in `[0, 1]`, by the alternating
series at precision `V`, stopped at terms below `2^(−K−2)` or after `fuel` terms.  Valid for
every `fuel`; narrow only when the series has converged. -/
def atanAlt (z : Encl) (K V fuel : Nat) : Encl :=
  let zz : Encl := (clampNonneg z.1, z.2)
  atanAltLoop V (Encl.mul V zz zz) (one <<< AzInt.ofInt (-((K : Int) + 2))) fuel 0 zz
    (Encl.exact zero)

/-- The number of terms after which the alternating series gives up. -/
def gdSeriesTerms : Nat := 40

/-- `some b` when the width of `b` is at most `2^(−j)` (measured: one subtraction rounded up),
`none` otherwise. -/
def enclNarrow? (b : Encl) (j : Int) : Option Encl :=
  if le (subPrecRound b.2 b.1 64 .Ceiling).1 (one <<< AzInt.ofInt (-j)) = true then some b
  else none

/-- The series path for a small argument, from an enclosure `t` of `tanh (a/2)` at the level
`K`: `2 arctan t` by the alternating series, accepted when its width is at most `2^(8−K)`. -/
def gdSmallOf (t : Encl) (K : Nat) : Option Encl :=
  let A := atanAlt t K (K + 32) gdSeriesTerms
  enclNarrow? (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1) ((K : Int) - 8)

/-- The series path for a large argument, from an enclosure `z` of `e^(−a)` at Ziv level `w`:
`π/2 − 2 arctan z` by the alternating series, accepted when its width is at most `2^(−w)`. -/
def gdLargeOf (z : Encl) (w : Nat) : Option Encl :=
  let K := w + 8
  let V := K + 56
  let A := atanAlt z K V gdSeriesTerms
  let P := piBracket V
  enclNarrow?
    ((subPrecRound (P.1 <<< AzInt.ofInt (-1)) (A.2 <<< AzInt.ofInt 1) V .Floor).1,
      (subPrecRound (P.2 <<< AzInt.ofInt (-1)) (A.1 <<< AzInt.ofInt 1) V .Ceiling).1)
    ((K : Int) - 8)

/-- The general path, from an enclosure `t` of `tanh (a/2)` (clamped to `[0, 1]`) at the level
`K`: `2 arctan t` with the arctangent of `atanWiden`. -/
def gdCoreOf (t : Encl) (K : Nat) : Encl :=
  let A := atanWiden (clampNonneg t.1) (minOf t.2 one) K (K + 64)
  (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1)

/-- The series path for a small `a` (exponent `e ≤ 0`): `gdSmallOf` with `tanh (a/2)` from
`tanhBracket`, tried when `64 (1 − e) ≥ K`. -/
def gdSmallSeries? (a : AzFloat) (e : AzInt) (w : Nat) : Option Encl :=
  let K := atanWork e w
  if 64 * (K - (w + 8) + 1) < K then none
  else gdSmallOf (tanhBracket (a <<< AzInt.ofInt (-1)) (e + AzInt.ofInt (-1)) (w + 64)) K

/-- The series path for a large `a` (`1 ≤ a < 2^e`, not huge): `gdLargeOf`, tried when
`92 ⌊a⌋ ≥ K = w + 8`.  `e^(−a) ≤ 2^(−⌊a⌋)` is computed to `K + 24 − ⌊a⌋` bits. -/
def gdLargeSeries? (a : AzFloat) (e : AzInt) (w : Nat) : Option Encl :=
  let fl := (truncToAzInt a).abs.toNat
  if 92 * fl < w + 8 then none
  else gdLargeOf (expBracket (-a) e (max 64 (w + 8 + 24 - fl))) w

/-- The bracket of `gd a` for a huge `a ≥ N`: `[⌊π/2⌋ − 2^(1−N), ⌈π/2⌉]`. -/
def gdHuge (N w : Nat) : Encl :=
  let V := w + 72
  let P := piBracket V
  ((subPrecRound (P.1 <<< AzInt.ofInt (-1)) (one <<< AzInt.ofInt (1 - (N : Int))) V .Floor).1,
    P.2 <<< AzInt.ofInt (-1))

/-- The general path: `gdCoreOf` with `tanh (a/2)` from `tanhBracket`, at the level
`K = atanWork e w`. -/
def gdCore (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  gdCoreOf (tanhBracket (a <<< AzInt.ofInt (-1)) (e + AzInt.ofInt (-1)) (w + 96))
    (atanWork e w)

/-- The bracket of `gd a` at Ziv level `w` for a positive finite float `a < 2^e`. -/
def gdBracket (a : AzFloat) (e : AzInt) (w : Nat) : Encl :=
  if w + 8 ≤ floatAbsFloorN e then gdHuge (floatAbsFloorN e) w
  else
    match (if e.sign = true ∧ e.abs.toNat ≠ 0 then gdLargeSeries? a e w
      else gdSmallSeries? a e w) with
    | some b => b
    | none => gdCore a e w

/-- The bracket of `gd x` as a pair of `Roundable`s: that of `gd |x|`, negated and swapped when
`neg` (`x < 0`). -/
def gdApprox (neg : Bool) (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  enclApprox neg (gdBracket x.abs e w)

/-! ### A rational argument -/

/-- The bracket of `gd |q|` at Ziv level `w` for a rational `q ≠ 0`: the paths of `gdBracket`
on the rational brackets — `gdHuge` when `⌊|q|⌋ ≥ w + 8`; the alternating series of
`e^(−|q|)` (`expRatBracket`) for `|q| ≥ 1` or of `tanh (|q|/2)` (`tanhRatBracket`) for
`|q| < 1`, under the same thresholds; and `gdCoreOf` on `tanhRatBracket`.  The level is
`atanWork (ratExpBound q) w`, i.e. with relative accuracy for a small `q`. -/
def gdRatBracket (q : AzRat) (w : Nat) : Encl :=
  let N := ratAbsFloorN q
  if w + 8 ≤ N then gdHuge N w
  else
    let K := atanWork (ratExpBound q) w
    match (if q.den ≤ q.num then
        (if 92 * N < w + 8 then none
          else gdLargeOf (expRatBracket (-q.abs) (max 64 (w + 8 + 24 - N))) w)
      else
        (if 64 * (K - (w + 8) + 1) < K then none
          else gdSmallOf (tanhRatBracket (q >>> (1 : Nat)) (w + 64)) K)) with
    | some b => b
    | none => gdCoreOf (tanhRatBracket (q >>> (1 : Nat)) (w + 96)) K

/-- The bracket of `gd q` as a pair of `Roundable`s (negated and swapped for `q < 0`). -/
def gdRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox (!q.sign) (gdRatBracket q w)

end Azurite.AzFloat
