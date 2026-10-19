/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Div
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Ziv
import Azurite.AzNat.AtanhSplit
import Azurite.AzNat.Pow

/-!
## The bracket of `ln 2`

`ln 2 = 18 atanh(1/26) − 2 atanh(1/4801) + 8 atanh(1/8749)`, each `atanh(1/q) = ∑_k
1/((2k+1) q^(2k+1))` summed exactly by binary splitting (`AzNat.atanhNumDen`).  Truncating the
three series after `N₁, N₂, N₃` terms and adding the tail bounds `(4/3) t_N` on the appropriate
side gives exact rationals `lo ≤ ln 2 ≤ hi` of width below `2^(−w)` when
`(2N_q+1)⌊lg q⌋ ≥ w + 6` (`ln2N₁`, `ln2N₂`, `ln2N₃`, with `⌊lg 26⌋ = 4`, `⌊lg 4801⌋ = 12`,
`⌊lg 8749⌋ = 13`).  Each exact series fraction is turned into a pair of floats by one directed
division of its numerator and denominator rounded to `w + 8` bits (`seriesBracket`; no GCD, no
large products — the reductions of `AzRat` arithmetic on these fractions, and later the exact
products of a common-denominator combination, used to cost more than the series), the tail
bounds are replaced by the power of two `2^(−w−5) ≥ (4/3) t_N`, and the Machin combination is
evaluated on floats with directed rounding at `w + 8` bits: `ln2Bracket w = (lo, hi)` encloses
`ln 2` with width below `8 · 2^(−w)` (in fact below `2 · 2^(−w)`).  `ln2Approx w` is the bracket
as `Roundable`s — what Ziv's loop tests (`Azurite/AzFloat/Ln2.lean`); one evaluation of the
three series per level.  The reciprocal
bracket `log2EBracket w = (⌊1/hi⌋_w, ⌈1/lo⌉_w)` encloses `log₂ e = 1/ln 2` at the cost of two
divisions (`log2EApprox`).

The theory is `Azurite/BrentZimmermann/Chapter4/Ln2BinarySplitting.lean`; the proofs are in
`Azurite/AzFloat/Equiv/Ln2Bracket.lean`.
-/

namespace Azurite.AzFloat

/-- Terms for `atanh(1/26)` at working precision `w`: `(2N+1)·4 ≥ w + 6`. -/
def ln2N₁ (w : Nat) : Nat := (w + 6) / 8 + 1

/-- Terms for `atanh(1/4801)`: `(2N+1)·12 ≥ w + 6`. -/
def ln2N₂ (w : Nat) : Nat := (w + 6) / 24 + 1

/-- Terms for `atanh(1/8749)`: `(2N+1)·13 ≥ w + 6`. -/
def ln2N₃ (w : Nat) : Nat := (w + 6) / 26 + 1

/-- Floats below and above a truncated series `S = n/d` (`AzNat.atanhNumDen`) at precision `k`:
numerator and denominator are rounded to `k` bits (down/up for the lower end, up/down for the
upper end) and divided once with directed rounding, so the cost is `O(M(k))` whatever the size of
the exact fraction. -/
def seriesBracket (s : AzNat × AzNat) (k : Nat) : AzFloat × AzFloat :=
  ((divPrecRound (setPrecRound (ofAzNat s.1) k .Floor).1 (setPrecRound (ofAzNat s.2) k .Ceiling).1
      k .Floor).1,
    (divPrecRound (setPrecRound (ofAzNat s.1) k .Ceiling).1 (setPrecRound (ofAzNat s.2) k .Floor).1
      k .Ceiling).1)

/-- The bracket `lo ≤ ln 2 ≤ hi` at working precision `w`, as floats of precision `k = w + 8`:
the three series bracketed by `seriesBracket`, the tail bounds `(4/3) t_N ≤ 2^(−w−5)` replaced by
that power of two, and the Machin combination `18 S₁ − 2 (S₂ + t) + 8 S₃` (lower end, every
operation rounded down, the subtracted part rounded up) and `18 (S₁ + t) − 2 S₂ + 8 (S₃ + t)`
(upper end, the other way round) evaluated at precision `k`. -/
def ln2Bracket (w : Nat) : AzFloat × AzFloat :=
  let k := w + 8
  let b₁ := seriesBracket (AzNat.atanhNumDen 26 (ln2N₁ w)) k
  let b₂ := seriesBracket (AzNat.atanhNumDen 4801 (ln2N₂ w)) k
  let b₃ := seriesBracket (AzNat.atanhNumDen 8749 (ln2N₃ w)) k
  let t := powerOf2 (-(AzNat.ofNat (w + 5)).toAzInt)
  let c18 := ofAzNat (AzNat.ofNat 18)
  let c8 := ofAzNat (AzNat.ofNat 8)
  let c2 := ofAzNat (AzNat.ofNat 2)
  let lo := (subPrecRound
    (addPrecRound (mulPrecRound c18 b₁.1 k .Floor).1 (mulPrecRound c8 b₃.1 k .Floor).1 k .Floor).1
    (mulPrecRound c2 (addPrecRound b₂.2 t k .Ceiling).1 k .Ceiling).1 k .Floor).1
  let hi := (subPrecRound
    (addPrecRound (mulPrecRound c18 (addPrecRound b₁.2 t k .Ceiling).1 k .Ceiling).1
      (mulPrecRound c8 (addPrecRound b₃.2 t k .Ceiling).1 k .Ceiling).1 k .Ceiling).1
    (mulPrecRound c2 b₂.1 k .Floor).1 k .Ceiling).1
  (lo, hi)

/-- The two ends of the bracket, rounded at any requested precision. -/
def ln2Approx (w : Nat) : Roundable × Roundable :=
  let b := ln2Bracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket `⌊1/hi⌋_w ≤ log₂ e = 1/ln 2 ≤ ⌈1/lo⌉_w`: the reciprocals of the ends of the
bracket of `ln 2`, with directed rounding (`w ≥ 2`, so that `lo > 0`). -/
def log2EBracket (w : Nat) : AzFloat × AzFloat :=
  let b := ln2Bracket w
  ((divPrecRound one b.2 w .Floor).1, (divPrecRound one b.1 w .Ceiling).1)

/-- The two ends of the `log₂ e` bracket, rounded at any requested precision. -/
def log2EApprox (w : Nat) : Roundable × Roundable :=
  let b := log2EBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
