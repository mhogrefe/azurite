/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.PolygammaBracket
import Azurite.AzFloat.LnEncl
import Azurite.AzFloat.Equiv.AltSeriesWidth

/-!
## The Glaisher–Kinkelin constant

`glaisherKinkelinPrecRound p mode` is the Glaisher–Kinkelin constant

  `A = 1.28242 71291 00622 63687 …`,  `ln A = 1/12 − ζ′(−1)`

(DLMF 5.17.6–5.17.7, where it is Glaisher's constant), rounded to precision `p` in `mode`, with
the comparison against the exact value; `glaisherKinkelin p` rounds to nearest.

**Method**: the Euler–Maclaurin expansion behind the definition.  With

  `ln A = lim (∑_{k ≤ n} k ln k − (n²/2 + n/2 + 1/12) ln n + n²/4)`,

for every `n ≥ 1` and `j ≥ 1`

  `ln A = ∑_{k ≤ n} k ln k − (n²/2 + n/2 + 1/12) ln n + n²/4 + ∑_{k=1}^{j} t_k + θ`,
  `t_k = B_{2k+2} / (2k (2k + 1) (2k + 2) n^{2k})`,  `|θ| ≤ |t_j|`

(`DLMF.abs_glaisherC_sub_le`, from the expansion 5.17.5 of Barnes's `G` with its remainder as
an integral of a periodic Bernoulli function, and `|B̃_{2m}| ≤ |B_{2m}|`); and `θ` has the
sign of the next term (`DLMF.glaisherSeq_sub_eq`, `DLMF.dlmf_2_10_5_bound`).

* **The sum of `k ln k`** is the logarithm of the hyperfactorial `∏ k^k = (n!)ⁿ / ∏_{k<n} k!`:
  one loop for `n!` and `∏_{k<n} k!` — `n` full multiplications, rounded down, with the upper
  bounds from the count of the roundings (`glaisherProdLo`, `glaisherProd`) —, one power, one
  division, **one** logarithm.
* **The terms** alternate in sign and envelop the remainder (DLMF 2.10.4–2.10.5), so they
  are summed on enclosures by the loop of Stirling's series (`altSumLoop`), straight from
  the tangent numbers — `|t_k| = T_{k+1} / ((4^{2k+2} − 2^{2k+2}) · 2k (2k + 1) n^{2k})` —
  one division and three multiplications a term, closed by the first term below `2^(−w−16)`
  or the last one.  (Until 2026-11-20 this was an exact rational sum over reduced Bernoulli
  numbers, a third of the time at 1000 bits.)
* **The parameters**: at most `j = ⌊w/12⌋ + 3` terms at `n = 8j`.  The terms decrease like
  `(π e n / j)^(−2j)`, twelve bits a term at this ratio.
* `A = exp (ln A)` by the exponential of an enclosure (`gammaExpEncl`), and Ziv's loop with
  fuel: whether `A` is irrational is not known.

**Contract** (`Equiv/GlaisherKinkelin.lean`): `glaisherKinkelinPrecRoundFuel_zivSpec` — sound
at every fuel, complete in the limit of the fuel wherever `A` is no rounding boundary.
-/

namespace Azurite.AzFloat

/-- The number of terms of the expansion at Ziv level `w`. -/
def glaisherTerms (w : Nat) : Nat := w / 12 + 3

/-- The argument `n` of the expansion at Ziv level `w`. -/
def glaisherArg (w : Nat) : Nat := 8 * glaisherTerms w

/-- `(f, w)` after `k` more steps from lower bounds of `(i!, ∏_{l<i} l!)`: lower bounds of
`(i + k)!` and `∏_{l<i+k} l!`, every product rounded down.  One full multiplication a
step. -/
def glaisherProdLo (V : Nat) : Nat → Nat → AzFloat → AzFloat → AzFloat × AzFloat
  | 0, _, f, w => (f, w)
  | k + 1, i, f, w =>
    glaisherProdLo V k (i + 1) (mulPrecRound f (ofAzNat (AzNat.ofNat (i + 1))) V .Floor).1
      (mulPrecRound w f V .Floor).1

/-- An upper bound of a positive number from a lower bound `f` that `K` roundings down made:
`⌈f · ⌈1 + 2K · 2^(−V)⌉⌉`.  (Each rounding loses a factor of at most `e^(3u)`, `u = 2^(−V)`,
and `e^(3Ku)… ≤ 1 + 2 · 3Ku`; `K` counts three units a rounding.) -/
def glaisherUpper (V : Nat) (f : AzFloat) (K : Nat) : AzFloat :=
  (mulPrecRound f
    (addPrecRound one (ofAzNat (AzNat.ofNat (2 * K)) <<< AzInt.ofInt (-(V : Int))) V
      .Ceiling).1 V .Ceiling).1

/-- Enclosures of `n!` and of `∏_{k<n} k!`: the lower bounds of `glaisherProdLo` and the upper
bounds they imply (`n` roundings behind the first, at most `n²` behind the second). -/
def glaisherProd (V n : Nat) : Encl × Encl :=
  let fw := glaisherProdLo V n 0 one one
  ((fw.1, glaisherUpper V fw.1 (3 * n)), (fw.2, glaisherUpper V fw.2 (3 * n * n)))

/-- The enclosure of `τ_k = |t_k| = c_{k+1} / (2k (2k + 1) n^{2k})` from the tangent number
table `T`, an enclosure `p` of `n^(−2k−2)` and the enclosure `n2` of `n²`: the term
`c_{k+1} n^(−2k−2)` of the series of `ψ` (`psiTermEncl`) times `n² / (2k (2k + 1))`. -/
def glaisherTermEncl (V : Nat) (T : Array AzNat) (n2 : Encl) (k : Nat) (p : Encl) : Encl :=
  Encl.div V (Encl.mul V (psiTermEncl V T (k + 1) p) n2) (Encl.nat (2 * k * (2 * k + 1)))

/-- An enclosure of `ln A` at Ziv level `w`. -/
def glaisherKinkelinLnEncl (w : Nat) : Encl :=
  let j := glaisherTerms w
  let n := glaisherArg w
  let V := w + 2 * n.log2 + 64
  let FW := glaisherProd V n
  let lnH := lnOfEncl (Encl.div V (Encl.powBin V FW.1 n) FW.2) V
  let L := lnOfEncl (Encl.nat n) V
  let c := Encl.div V (Encl.nat (6 * n * n + 6 * n + 1)) (Encl.nat 12)
  let n2 := Encl.nat (n * n)
  let inv2 := Encl.div V (Encl.exact one) n2
  let p₁ := Encl.div V (Encl.exact one) (Encl.nat (n * n * (n * n)))
  let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
  let S := altSumLoop V (glaisherTermEncl V (AzNat.tangentNumbers (j + 1)) n2) inv2 tol (j - 1)
    1 p₁ (Encl.exact zero)
  Encl.sub V (Encl.add V (Encl.sub V lnH (Encl.mulPos V L c)) (Encl.nat (n * n / 4))) S

/-- The sign (positive) and a positive enclosure of `A` at Ziv level `w`. -/
def glaisherKinkelinCore (w : Nat) : Option (Bool × Encl) :=
  (gammaExpEncl false (glaisherKinkelinLnEncl w) w).map fun g => (false, g)

/-- The bracket of `A` as a pair of `Roundable`s. -/
def glaisherKinkelinApprox (w : Nat) : Roundable × Roundable :=
  gammaApproxOf (glaisherKinkelinCore w) w

/-- The Glaisher–Kinkelin constant rounded to precision `p` with `mode`, and the comparison
with the exact value (`(nan, .eq)` for `p = 0`, or if the fuel runs out), with the fuel of
the Ziv loop explicit. -/
def glaisherKinkelinPrecRoundFuel (fuel p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else zivLoop glaisherKinkelinApprox p mode fuel (max 64 (p + 32))

/-- The Glaisher–Kinkelin constant rounded to precision `p` with `mode`, and the comparison
with the exact value: `glaisherKinkelinPrecRoundFuel` at the fuel `gammaFuel p`. -/
def glaisherKinkelinPrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  glaisherKinkelinPrecRoundFuel (gammaFuel p) p mode

/-- The Glaisher–Kinkelin constant rounded to nearest at precision `p`. -/
def glaisherKinkelin (p : Nat) : AzFloat := (glaisherKinkelinPrecRound p .Nearest).1

end Azurite.AzFloat
