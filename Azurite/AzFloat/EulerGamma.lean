/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket
import Azurite.AzInt.SignedSplit

/-!
## Euler's constant `γ`

**Sweeney's method** (1963): for every `n ≥ 1`,

  `γ = ∑_{k≥0} (−1)^k n^(k+1) / ((k+1) (k+1)!) − ln n − E₁(n)`,  `0 ≤ E₁(n) ≤ e^(−n)/n`

(`eulerMascheroni_eq_sweeney`, `Azurite/Transcendental/EulerGamma.lean`, from Mathlib's
`γ = −∫₀^∞ ln t e^(−t) dt`).  At working precision `w` we take `n = eulerGammaN w`, so that
`E₁(n) ≤ 2^(−w−5)`, and `N = eulerGammaTerms w = 37 q − 1` terms with `q = ⌈n/10⌉`, so that
the tail of the series is at most `2 · 2^(−16q) ≤ 2^(−w−8)`
(`abs_tsum_sweeneyTerm_sub_sum_le_of_le`: the first omitted term is at most
`(e n/(N+1))^(N+1) ≤ (10e/37)^(37q)` and `(10e/37)^37 ≤ 2^(−16)`).  The partial sum is computed
exactly by signed binary splitting (`AzInt.sweeneyNumDen`), bracketed by floats of `k` bits
(`seriesBracket`), `ln n` by `lnBracket` at `k` bits, and the bracket of `γ` is

  `[⌊⌊S_lo − L_hi⌋ − 2^(−w−4)⌋, ⌈⌈S_hi + 2^(−w−4)⌉ − L_lo⌉]`,

the lower end covering `E₁(n) + tail ≤ 2^(−w−5) + 2^(−w−8)`, the upper end the tail.  The cost
is the binary splitting of `≈ 2.6 w` terms of size `O(w)` bits each, `O(M(w) log² w)`, plus one
logarithm of a small integer at `≈ w` bits; the alternative of Brent and McMillan (1980; `≈ 2.1
w` terms of two series, no logarithm beyond `ln n`) would need the theory of the modified Bessel
functions `I₀`, `K₀` (DLMF Chapter 10), not yet available.

The Ziv loop (`zivLoop`) has fuel `eulerGammaFuel p` and the specification is "correctly rounded
or `NaN`" (`Equiv/EulerGamma.lean`): the termination certificate would need the irrationality of
`γ`, an open problem.  The fuel is exhausted only if `γ` lies within about `2^(−16p)` of a
rounding boundary.
-/

namespace Azurite.AzFloat

/-- The bracket of `ln x` for an arbitrary float (`(NaN, NaN)` unless `x` is finite and
positive): `lnBracket` with the exponent of `x`. -/
def lnBracketOf (x : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  match x with
  | finite true e q m hv => lnBracket (finite true e q m hv) e w
  | _ => (nan, nan)

/-- The argument `n` of Sweeney's formula at working precision `w`: `n ≥ 0.7 (w + 5)`, so that
`E₁(n) ≤ e^(−n) ≤ 2^(−w−5)`. -/
def eulerGammaN (w : Nat) : Nat := 7 * (w + 5) / 10 + 1

/-- `q = ⌈n/10⌉` for `n = eulerGammaN w`: the number of terms is `37 q − 1 ≈ 3.7 n`. -/
def eulerGammaQ (w : Nat) : Nat := (eulerGammaN w + 9) / 10

/-- The number of terms of Sweeney's series at working precision `w`: `37 q − 1`, so that the
tail is at most `2 · 2^(−16 q) ≤ 2^(−w−8)`. -/
def eulerGammaTerms (w : Nat) : Nat := 37 * eulerGammaQ w - 1

/-- The precision of the floats of the bracket at working precision `w`: `w + 12 + ⌊lg n⌋`, so
that the relative error of the bracket of the partial sum (at most `ln n + 2`) is absolutely at
most `2^(−w−8)`. -/
def eulerGammaBits (w : Nat) : Nat := w + 12 + Nat.log 2 (eulerGammaN w)

/-- The bracket `lo < γ ≤ hi` at working precision `w`. -/
def eulerGammaBracket (w : Nat) : AzFloat × AzFloat :=
  let n := eulerGammaN w
  let k := eulerGammaBits w
  let s := AzInt.sweeneyNumDen n (eulerGammaTerms w)
  let b := seriesBracket (s.1.natAbs, s.2) k
  let l := lnBracketOf (ofAzNat (AzNat.ofNat n)) k
  let t := powerOf2 (-(AzNat.ofNat (w + 4)).toAzInt)
  ((subPrecRound (subPrecRound b.1 l.2 k .Floor).1 t k .Floor).1,
    (subPrecRound (addPrecRound b.2 t k .Ceiling).1 l.1 k .Ceiling).1)

/-- The two ends of the `γ` bracket, rounded at any requested precision. -/
def eulerGammaApprox (w : Nat) : Roundable × Roundable :=
  let b := eulerGammaBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The fuel of the Ziv loop for `γ`: enough doublings to reach `16 (p + 64)` bits. -/
def eulerGammaFuel (p : Nat) : Nat := zivFuel (16 * (p + zivGuardBits))

/-- `γ` rounded to precision `p` with `mode`, and the comparison with the exact value (`NaN` at
precision `0` or if the fuel runs out). -/
def eulerGammaPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop eulerGammaApprox p mode (eulerGammaFuel p) (p + zivGuardBits)

/-- Euler's constant `γ` rounded to nearest at precision `p`. -/
def eulerGamma (p : Nat) : AzFloat := (eulerGammaPrecRound p .Nearest).1

end Azurite.AzFloat
