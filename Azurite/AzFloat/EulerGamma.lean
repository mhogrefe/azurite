/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.LnSmooth
import Azurite.AzInt.SweeneyHorner

/-!
## Euler's constant `γ`

**Sweeney's method** (1963): for every `n ≥ 1`,

  `γ = ∑_{k≥0} (−1)^k n^(k+1) / ((k+1) (k+1)!) − ln n − E₁(n)`,  `0 ≤ E₁(n) ≤ e^(−n)/n`

(`eulerMascheroni_eq_sweeney`, `Azurite/Transcendental/EulerGamma.lean`, from Mathlib's
`γ = −∫₀^∞ ln t e^(−t) dt`).  At working precision `w` the argument is `n = eulerGammaArg w`,
barely above `eulerGammaN w ≥ 0.7 (w + 5)`, so that `E₁(n) ≤ 2^(−w−5)`, and
`N = eulerGammaTermsOf n = 37 q − 1` terms with `q = ⌈n/10⌉`, so that the tail of the series
is at most `2 · 2^(−16q) ≤ 2^(−w−8)` (`abs_tsum_sweeneyTerm_sub_sum_le_of_le`: the first omitted
term is at most `(e n/(N+1))^(N+1) ≤ (10e/37)^(37q)` and `(10e/37)^37 ≤ 2^(−16)`).

**The partial sum** is enclosed by the truncated backward recurrence of
`AzInt/SweeneyHorner.lean` (`AzInt.sweeneyHornerEncl`): machine-word blocks of the recurrence
matrices applied to a numerator and a denominator that are cut back to
`V = eulerGammaWork w n ≈ w + 1.45 n` bits, with the truncation error carried as an exact
radius.  The terms of the series reach `e^n ≈ 2^(1.44 n)` before they cancel, hence the extra
`1.45 n` bits.  The exact fraction of the partial sum, which the first version of this file
computed by binary splitting, has about `N log₂ N` bits — forty times the precision at
`20000` bits; the recurrence never multiplies anything longer than `V + 256` bits by more than
a block (`eulerGammaBlockBits`: one word below `V = 1024`, about `V / 16` bits above).

**The logarithm**: the argument is the least integer `n ≥ eulerGammaN w` with no prime factor
above `7` (`nextSmooth`; about `1 %` above at most), and `ln n` is then an integer combination
of four fast `atanh` series (`lnNatBracket`, `AzFloat/LnSmooth.lean`), at about the cost of
`ln 2` — a fifth of the general logarithm at `20000` bits.

The bracket of `γ` is

  `[⌊⌊S_lo − L_hi⌋ − 2^(−w−4)⌋, ⌈⌈S_hi + 2^(−w−4)⌉ − L_lo⌉]`,

the lower end covering `E₁(n) + tail ≤ 2^(−w−5) + 2^(−w−8)`, the upper end the tail.  The
alternative of Brent and McMillan (1980; a quarter of the terms, no cancellation) would need
the theory of the modified Bessel functions `I₀`, `K₀` (DLMF Chapter 10), not yet available.

The Ziv loop (`zivLoop`) starts at `max (p + 16) 64` bits and has fuel (`eulerGammaFuel p`;
`eulerGammaPrecRoundFuel` takes it as an argument): a termination certificate would need the
irrationality of `γ`, an open problem.  The specification (`Equiv/EulerGamma.lean`,
`Equiv/EulerGammaWidth.lean`) is that of a fuel-bound function: correctly rounded or `NaN`,
and — the bracket has width at most `1000 · 2^(−w)` — correctly rounded for every large enough
fuel if `γ` is no rounding boundary of the precision.
-/

namespace Azurite.AzFloat

/-- The bracket of `ln x` for an arbitrary float (`(NaN, NaN)` unless `x` is finite and
positive): `lnBracket` with the exponent of `x`. -/
def lnBracketOf (x : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  match x with
  | finite true e q m hv => lnBracket (finite true e q m hv) e w
  | _ => (nan, nan)

/-- The bracket of `ln n` for a natural `n ≥ 1` at `k` bits: the four-series combination of
`AzFloat/LnSmooth.lean` when `n = 2^a 3^b 5^c 7^d`, the general logarithm otherwise. -/
def lnNatBracket (n k : Nat) : AzFloat × AzFloat :=
  let e := smoothExps n
  if n = 2 ^ e.1 * 3 ^ e.2.1 * 5 ^ e.2.2.1 * 7 ^ e.2.2.2.1 then
    lnSmoothBracket e.1 e.2.1 e.2.2.1 e.2.2.2.1 k
  else lnBracketOf (ofAzNat (AzNat.ofNat n)) k

/-- The least argument of Sweeney's formula at working precision `w`: `n ≥ 0.7 (w + 5)`, so
that `E₁(n) ≤ e^(−n) ≤ 2^(−w−5)`. -/
def eulerGammaN (w : Nat) : Nat := 7 * (w + 5) / 10 + 1

/-- The argument `n` of Sweeney's formula at working precision `w`: the least integer from
`eulerGammaN w` on with no prime factor above `7`, whose logarithm is cheap. -/
def eulerGammaArg (w : Nat) : Nat := nextSmooth (eulerGammaN w)

/-- The number of terms of Sweeney's series with argument `n`: `37 q − 1` with `q = ⌈n/10⌉`,
so that the tail is at most `2 · 2^(−16 q)`. -/
def eulerGammaTermsOf (n : Nat) : Nat := 37 * ((n + 9) / 10) - 1

/-- The precision of the floats of the bracket: `w + 12 + ⌊lg n⌋ + 2 ⌊lg w⌋` (at least `64`);
the last term covers what the general logarithm loses at high precision. -/
def eulerGammaBits (w n : Nat) : Nat := max 64 (w + 12 + n.log2 + 2 * w.log2)

/-- The bits kept by the truncated recurrence: `w + 16 + ⌊13 n / 9⌋ + 2 ⌊lg n⌋`
(`13/9 > log₂ e`: the terms of the series reach `e^n`). -/
def eulerGammaWork (w n : Nat) : Nat := w + 16 + 13 * n / 9 + 2 * n.log2

/-- The size of the long blocks of the recurrence at `V` bits: none (machine words only) below
`1024` bits, `max 256 (V / 16)` bits above (measured). -/
def eulerGammaBlockBits (V : Nat) : Nat := if V < 1024 then 0 else max 256 (V / 16)

/-- The float below `a / d` at `k` bits: `a` rounded down, `d` rounded up, one division rounded
down (the lower end of `seriesBracket`). -/
def fracFloor (a d : AzNat) (k : Nat) : AzFloat :=
  (divPrecRound (setPrecRound (ofAzNat a) k .Floor).1 (setPrecRound (ofAzNat d) k .Ceiling).1
    k .Floor).1

/-- The float above `a / d` at `k` bits (the upper end of `seriesBracket`). -/
def fracCeil (a d : AzNat) (k : Nat) : AzFloat :=
  (divPrecRound (setPrecRound (ofAzNat a) k .Ceiling).1 (setPrecRound (ofAzNat d) k .Floor).1
    k .Ceiling).1

/-- The bracket `lo < γ ≤ hi` at working precision `w` from Sweeney's formula with the
argument `n ≥ eulerGammaN w`. -/
def eulerGammaBracketAt (w n : Nat) : AzFloat × AzFloat :=
  let k := eulerGammaBits w n
  let V := eulerGammaWork w n
  let e := AzInt.sweeneyHornerEncl n (eulerGammaTermsOf n) V (eulerGammaBlockBits V)
  let l := lnNatBracket n k
  let t := powerOf2 (-(AzNat.ofNat (w + 4)).toAzInt)
  ((subPrecRound (subPrecRound (fracFloor e.1 e.2.2 k) l.2 k .Floor).1 t k .Floor).1,
    (subPrecRound (addPrecRound (fracCeil e.2.1 e.2.2 k) t k .Ceiling).1 l.1 k .Ceiling).1)

/-- The bracket `lo < γ ≤ hi` at working precision `w`. -/
def eulerGammaBracket (w : Nat) : AzFloat × AzFloat := eulerGammaBracketAt w (eulerGammaArg w)

/-- The two ends of the `γ` bracket, rounded at any requested precision. -/
def eulerGammaApprox (w : Nat) : Roundable × Roundable :=
  let b := eulerGammaBracket w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The fuel of the Ziv loop for `γ`: enough doublings to reach `16 (p + 64)` bits. -/
def eulerGammaFuel (p : Nat) : Nat := zivDefaultFuel p

/-- **`γ` with the fuel of its Ziv loop as an argument**: rounded to precision `p` with `mode`,
and the comparison with the exact value (`NaN` at precision `0` or if the fuel runs out).  The
loop starts at `max (p + 16) 64` bits: the enclosure is a few bits narrower than `2^(−w)`, so
sixteen guard bits fail about once in `2^19` precisions, and a failure only doubles the
working precision.  The specification is `eulerGammaPrecRoundFuel_zivSpec`
(`Equiv/EulerGammaWidth.lean`). -/
def eulerGammaPrecRoundFuel (fuel p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop eulerGammaApprox p mode fuel (max (p + 16) 64)

/-- `γ` rounded to precision `p` with `mode`, and the comparison with the exact value (`NaN` at
precision `0` or if the fuel runs out): `eulerGammaPrecRoundFuel` at the fuel
`eulerGammaFuel p`. -/
def eulerGammaPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  eulerGammaPrecRoundFuel (eulerGammaFuel p) p mode

/-- Euler's constant `γ` rounded to nearest at precision `p`. -/
def eulerGamma (p : Nat) : AzFloat := (eulerGammaPrecRound p .Nearest).1

end Azurite.AzFloat
