/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.Sqrt
import Azurite.AzNat.HypSplit

/-!
## The bracket of Catalan's constant

`G = ∑_{j≥0} (−1)^j/(2j+1)² = 0.9159655941772190150546035149323841107741493742816721342664…`.

The defining series converges like `1/j`, so `G` is computed from Ramanujan's formula
`G = (π/8) ln(2 + √3) + (3/8) ∑_{k≥0} 1/((2k+1)² C(2k,k))` with the logarithm expanded as
`ln(2 + √3) = 2 artanh(1/√3) = 2√3 ∑_{k≥0} 1/((2k+1) 3^{k+1})`:

  `G = √3 · π · (A/4) + 3S/8`,  `A = ∑ 1/((2k+1) 3^{k+1})`,  `S = ∑ 1/((2k+1)² C(2k,k))`

(`catalanConstant_eq`, `Azurite/Transcendental/Catalan.lean`).  Both series have positive
rational terms with ratios at most `1/3` and `1/4`, so the partial sums are lower bounds and the
tails are at most `(1/2) 3^{−N}` and `(4/3) 4^{−N}`.  At working precision `w`:

* `catalanTerms w = ⌊(w+10)/2⌋ + 1` terms of `S` (tail of `3S/8` at most `2^(−w−12)`) and
  `atanhSqrtThreeTerms w = 2(⌊(w+10)/3⌋ + 1)` terms of `A` (tail of `√3 π A/4` at most
  `2^(−w−11)`, from `9^m ≥ 8^m`), each summed **exactly** by binary splitting
  (`AzNat.catalanNumDen`, `AzNat.atanhSqrtThreeNumDen`) and bracketed by floats of `k = w + 16`
  bits (`seriesBracket`);
* `√3` by its floor and ceiling at `k` bits, `π` by `piBracket k`;
* the bracket is `[⌊⌊⌊√3_lo π_lo⌋ a_lo⌋ + s_lo⌋, ⌈⌈⌈⌈√3_hi π_hi⌉ a_hi⌉ + s_hi⌉ + 2^(−w−10)⌉]`.

The cost is the binary splitting of `≈ w/2` terms with ratios of `≈ 2 lg k` bits each and of
`≈ 2w/3` terms with odd denominators, `O(M(w) log² w)`, plus `π` and one square root.

The specification, the width `≤ 2^(−w)` and the termination certificate (from the
irrationality of `G`) are in `Equiv/CatalanBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The number of terms of `S = ∑ 1/((2k+1)² C(2k,k))` at working precision `w`:
`4^N ≥ 2^(w+11)`. -/
def catalanTerms (w : Nat) : Nat := (w + 10) / 2 + 1

/-- The number of terms of `A = ∑ 1/((2k+1) 3^{k+1})` at working precision `w`: `N = 2m` with
`3m ≥ w + 11`, so that `3^N = 9^m ≥ 2^(w+11)`. -/
def atanhSqrtThreeTerms (w : Nat) : Nat := 2 * ((w + 10) / 3 + 1)

/-- The precision of the floats of the bracket at working precision `w`. -/
def catalanBits (w : Nat) : Nat := w + 16

/-- The bracket `lo ≤ G ≤ hi` of Catalan's constant at working precision `w`. -/
def catalanBracket (w : Nat) : AzFloat × AzFloat :=
  let k := catalanBits w
  let a := seriesBracket (AzNat.atanhSqrtThreeNumDen (atanhSqrtThreeTerms w)) k
  let s := seriesBracket (AzNat.catalanNumDen (catalanTerms w)) k
  let three := ofAzNat (AzNat.ofNat 3)
  let rl := (sqrtPrecRound three k .Floor).1
  let rh := (sqrtPrecRound three k .Ceiling).1
  let pi := piBracket k
  let t := powerOf2 (-(AzNat.ofNat (w + 10)).toAzInt)
  ((addPrecRound (mulPrecRound (mulPrecRound rl pi.1 k .Floor).1 a.1 k .Floor).1 s.1 k .Floor).1,
    (addPrecRound (addPrecRound (mulPrecRound (mulPrecRound rh pi.2 k .Ceiling).1 a.2 k
      .Ceiling).1 s.2 k .Ceiling).1 t k .Ceiling).1)

/-- The two ends of the bracket of Catalan's constant, rounded at any requested precision. -/
def catalanApprox (w : Nat) : Roundable × Roundable :=
  let b := catalanBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
