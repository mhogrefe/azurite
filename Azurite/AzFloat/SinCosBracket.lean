/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinBracket
import Azurite.AzFloat.ZivPair
import Azurite.AzInt.SinCosSplit
import Azurite.AzNat.ModPow2
import Azurite.AzNat.ShiftRight

/-!
## The joint bracket of `sin x` and `cos x`

`sinCosBracket x ex w` encloses `sin |x|` and `cos x` together for a finite float `x` of
exponent `ex` at Ziv level `w`, by Algorithm 4.4 (SinCos) of Brent and Zimmermann, *Modern
Computer Arithmetic*, §4.9.1: the sine and the cosine of a fixed-point number are assembled from
those of its bit blocks by the addition formulae, each block by binary splitting.

* **Reduction.**  `r' = remExact |x| (2 lo)` against the lower end of the
  bracket `[lo, hi]` of `π` at `W = cosWork ex w` bits; the true reduction `r = |x| − 2kπ` lies in
  `[r' − E, r']`.
* **Fixed point.**  `M = ⌊r' · 2^(T−3)⌋` with `T = V + 4` fraction bits at the series precision
  `V = w + 12`, so that `θ = M / 2^T ≤ r'/8 < π/4`.
* **Blocks.**  The fraction bits of `θ` are cut at the positions `sinCosCut T i =
  min(g (2^i − 1), T)` (`g = sinCosBlockBase`): the blocks have `g, 2g, 4g, …` bits, and block `i`
  is the dyadic rational `y_i = d_i / 2^(c_{i+1})` with `d_i < 2^(c_{i+1} − c_i)`
  (`sinCosDigit`), `θ = ∑ y_i`, `y_i < 2^(−c_i)`.
* **Binary splitting.**  `sinCosBlock` encloses `sin y_i` and `cos y_i`: the partial sums
  through index `N` of both Taylor series are exact fractions (`AzInt.altSplit`) within the term
  of index `N` of the values (alternating series), and `enclFraction` turns each into an
  enclosure with one division at `V + 8` bits.  `N = sinCosTerms c_i V` is the first index whose
  term is certified below `2^(−V)` by counting bits (`2 c_i` for `y²` and `⌊lg⌋` of each
  denominator factor).
* **Rotation.**  `sinCosRotate`: `sin (y + x) = sin y cos x + cos y sin x`,
  `cos (y + x) = cos y cos x − sin y sin x` in interval arithmetic at `V` bits, from the lowest
  block up (`sinCosFixLoop`; a zero block is skipped).  All the angles lie in `[0, π/4)`.
* **Doubling.**  Three double-angle steps `(s, c) ↦ (2sc, 2c² − 1)` take `θ` to `8θ = M/2^(T−3)`
  (the last sine through the signed product `enclMulNonnegSigned`, the last cosine through
  `|cos 4θ|`), and both results are widened by `E₂ ≥ E + 2^(3−T)`, which covers `|r − 8θ|`
  (`sin` and `cos` are `1`-Lipschitz).

`sinCosApprox` is the pair of pairs of `Roundable`s for the joint Ziv loop
(`AzFloat/SinCos.lean`); the sine bracket is negated and swapped for `x < 0`.

`sinBracket` and `cosBracket` are the two components computed alone (`sinCosTailSin`,
`sinCosTailCos`: the doublings the other component needs are skipped), with `sinApprox` and
`cosApprox` for the Ziv loops of `AzFloat/Sin.lean` and `AzFloat/Cos.lean`; the rational,
with-period and `π x` families and the Dottie number use them too.
-/

namespace Azurite.AzFloat

/-- The number of bits of the first block of `sinCosFix` (the later blocks double). -/
def sinCosBlockBase : Nat := 4

/-- The cut positions of the blocks among the `T` fraction bits: `min(g (2^i − 1), T)`. -/
def sinCosCut (T i : Nat) : Nat := min (sinCosBlockBase * (2 ^ i - 1)) T

/-- The digit of block `i` of the fixed-point number `M / 2^T`: the bits of `M` between the cut
positions `i` and `i + 1` (counted from the top). -/
def sinCosDigit (M : AzNat) (T i : Nat) : AzNat :=
  (M >>> (T - sinCosCut T (i + 1))).modPow2 (sinCosCut T (i + 1) - sinCosCut T i)

/-- The search for the number of terms: from the index `n` with `acc` certified bits
(`y^(2n)/(2n)! ≤ 2^(−acc)` for `y ≤ 2^(−c)`), stop when `V ≤ acc`. -/
def sinCosTermsLoop (c V : Nat) : Nat → Nat → Nat → Nat
  | 0, n, _ => n
  | fuel + 1, n, acc =>
    if V ≤ acc then n
    else sinCosTermsLoop c V fuel (n + 1)
      (acc + 2 * c + ((AzNat.ofNat ((2 * n + 1) * (2 * n + 2))).size - 1))

/-- An index `N` with `y^(2N)/(2N)! ≤ 2^(−V)` for every `0 ≤ y ≤ 2^(−c)`. -/
def sinCosTerms (c V : Nat) : Nat := sinCosTermsLoop c V V 0 0

/-- An enclosure at precision `V` of a value `v ≥ 0` within `|P| / D` of the fraction `a / D`
(`a ≥ 0`, `D > 0`): **one** division, of the numerator and the denominator truncated to
`V + 8` bits, gives `q ≤ a / D ≤ q (1 + 2^(−V−5))`, and `|P| / D` is bounded by a 64-bit
quotient `t`; the result is `[q − t, q + q 2^(−V−5) + t]`, clamped at `0`. -/
def enclFraction (V : Nat) (a P D : AzInt) : Encl :=
  let V' := V + 8
  let q := (divPrecRound (setPrecRound (ofAzInt a) V' .Floor).1
    (setPrecRound (ofAzInt D) V' .Ceiling).1 V' .Floor).1
  let t := (divPrecRound (setPrecRound (ofAzInt P).abs 64 .Ceiling).1
    (setPrecRound (ofAzInt D) 64 .Floor).1 64 .Ceiling).1
  let e := (addPrecRound (q <<< AzInt.ofInt (3 - (V' : Int))) t 64 .Ceiling).1
  enclClamp0 ((subPrecRound q t V .Floor).1, (addPrecRound q e V .Ceiling).1)

/-- Enclosures of `sin y` and `cos y` for the dyadic rational `y = d / 2^c ≤ 1` at precision
`V`: the partial sums through index `N` of the two Taylor series, exact by binary splitting,
are within the term of index `N` of the values (`enclFraction`). -/
def sinCosBlock (d : AzNat) (c N V : Nat) : Encl × Encl :=
  let d2 := d * d
  let s := 2 * c
  let sc := AzInt.altSplit d2 s 0 0 N
  let ss := AzInt.altSplit d2 s 1 0 N
  let Dc := sc.2.1.toAzInt <<< (s * N)
  let Ds := ss.2.1.toAzInt <<< (s * N)
  (enclFraction V (d.toAzInt * (Ds + ss.2.2)) (d.toAzInt * ss.1) (Ds <<< c),
    enclFraction V (Dc + sc.2.2) sc.1 Dc)

/-- The rotation by a block: from `b = ([sin y], [cos y])` and `r = ([sin x], [cos x])`
(nonnegative enclosures, `y + x ≤ π/2`) to `([sin (y + x)], [cos (y + x)])`. -/
def sinCosRotate (V : Nat) (b r : Encl × Encl) : Encl × Encl :=
  (enclClamp0 (Encl.add V (Encl.mul V b.1 r.2) (Encl.mul V b.2 r.1)),
    enclClamp0 (Encl.sub V (Encl.mul V b.2 r.2) (Encl.mul V b.1 r.1)))

/-- The blocks `j, …, j + n − 1` of `M / 2^T`: enclosures of the sine and the cosine of their
sum, from the lowest block up. -/
def sinCosFixLoop (M : AzNat) (T V : Nat) : Nat → Nat → Encl × Encl
  | 0, _ => (Encl.exact zero, Encl.exact one)
  | n + 1, j =>
    let rest := sinCosFixLoop M T V n (j + 1)
    let d := sinCosDigit M T j
    if d = AzNat.ofNat 0 then rest
    else sinCosRotate V
      (sinCosBlock d (sinCosCut T (j + 1)) (sinCosTerms (sinCosCut T j) V) V) rest

/-- Enclosures of `sin θ` and `cos θ` for the fixed-point number `θ = M / 2^T ≤ 1` at precision
`V` (MCA Algorithm 4.4). -/
def sinCosFix (M : AzNat) (T V : Nat) : Encl × Encl :=
  sinCosFixLoop M T V (AzNat.ofNat T).size 0

/-- The exact doubling of an enclosure. -/
def enclDouble (a : Encl) : Encl := (a.1 <<< AzInt.ofInt 1, a.2 <<< AzInt.ofInt 1)

/-- `[a] · [b]` for a nonnegative enclosure `[a]` and an enclosure `[b]` of any sign. -/
def enclMulNonnegSigned (w : Nat) (a b : Encl) : Encl :=
  (minOf (mulPrecRound a.1 b.1 w .Floor).1 (mulPrecRound a.2 b.1 w .Floor).1,
    maxOf (mulPrecRound a.1 b.2 w .Ceiling).1 (mulPrecRound a.2 b.2 w .Ceiling).1)

/-- The tail of the joint bracket: from the enclosures of `sin θ`, `cos θ` (`0 ≤ θ ≤ π/4`) to
those of `sin t`, `cos t` for every `t` within `E` of `8θ`: three double-angle steps and the
Lipschitz widening. -/
def sinCosTail (sc : Encl × Encl) (E : AzFloat) (V : Nat) : Encl × Encl :=
  let s2 := enclClamp0 (enclDouble (Encl.mul V sc.1 sc.2))
  let c2 := enclClamp0 (cosDouble V sc.2)
  let s4 := enclClamp0 (enclDouble (Encl.mul V s2 c2))
  let c4 := cosDouble V c2
  let s8 := enclDouble (enclMulNonnegSigned V s4 c4)
  let c8 := cosDouble V (enclAbs c4)
  (Encl.widen V s8 (Encl.exact E), Encl.widen V c8 (Encl.exact E))

/-- The sine half of `sinCosTail`, computed alone (the last cosine doubling is skipped). -/
def sinCosTailSin (sc : Encl × Encl) (E : AzFloat) (V : Nat) : Encl :=
  let s2 := enclClamp0 (enclDouble (Encl.mul V sc.1 sc.2))
  let c2 := enclClamp0 (cosDouble V sc.2)
  let s4 := enclClamp0 (enclDouble (Encl.mul V s2 c2))
  let c4 := cosDouble V c2
  Encl.widen V (enclDouble (enclMulNonnegSigned V s4 c4)) (Encl.exact E)

/-- The cosine half of `sinCosTail`, computed alone (no sine doubling at all). -/
def sinCosTailCos (sc : Encl × Encl) (E : AzFloat) (V : Nat) : Encl :=
  Encl.widen V (cosDouble V (enclAbs (cosDouble V (enclClamp0 (cosDouble V sc.2)))))
    (Encl.exact E)

/-- The common part of the brackets at Ziv level `w` for a finite `x` of exponent `ex`
(reduction precision `W = cosWork ex w`, series precision `V = w + 12`): the enclosures of
`sin θ`, `cos θ` for the fixed-point number `θ ≤ r'/8`, and the slack `E₂` of the tail. -/
def sinCosReduce (x : AzFloat) (ex : AzInt) (w : Nat) : (Encl × Encl) × AzFloat :=
  let W := cosWork ex w
  let V := w + 12
  let T := V + 4
  let P := piBracket W
  let y := P.1 <<< AzInt.ofInt 1
  let r := remExact x.abs y
  let E := (mulPrecRound x.abs (subPrecRound P.2 P.1 64 .Ceiling).1 64 .Ceiling).1
  let M := floorScaled r (T - 3)
  let E₂ := (addPrecRound E (one <<< AzInt.ofInt (3 - (T : Int))) 64 .Ceiling).1
  (sinCosFix M T V, E₂)

/-- The joint bracket `([sin |x|], [cos x])` at Ziv level `w` for a finite `x` of exponent
`ex`. -/
def sinCosBracket (x : AzFloat) (ex : AzInt) (w : Nat) : Encl × Encl :=
  let r := sinCosReduce x ex w
  sinCosTail r.1 r.2 (w + 12)

/-- The bracket of `sin |x|` at Ziv level `w` for a finite `x` of exponent `ex`: the first
component of `sinCosBracket` (`sinBracket_eq`), without the last cosine doubling. -/
def sinBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let r := sinCosReduce x ex w
  sinCosTailSin r.1 r.2 (w + 12)

/-- The bracket of `cos x` at Ziv level `w` for a finite `x` of exponent `ex`: the second
component of `sinCosBracket` (`cosBracket_eq`), without the sine doublings. -/
def cosBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let r := sinCosReduce x ex w
  sinCosTailCos r.1 r.2 (w + 12)

theorem sinBracket_eq (x : AzFloat) (ex : AzInt) (w : Nat) :
    sinBracket x ex w = (sinCosBracket x ex w).1 := rfl

theorem cosBracket_eq (x : AzFloat) (ex : AzInt) (w : Nat) :
    cosBracket x ex w = (sinCosBracket x ex w).2 := rfl

/-- `sinCosBracket` as `Roundable`s for the joint Ziv loop: the bracket of `sin x` (that of
`sin |x|`, negated and swapped when `neg`, i.e. `x < 0`) and the bracket of `cos x`. -/
def sinCosApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) :
    (Roundable × Roundable) × (Roundable × Roundable) :=
  let b := sinCosBracket x ex w
  (if neg then
      (fun p mode => setPrecRound (-b.1.2) p mode, fun p mode => setPrecRound (-b.1.1) p mode)
    else (fun p mode => setPrecRound b.1.1 p mode, fun p mode => setPrecRound b.1.2 p mode),
    (fun p mode => setPrecRound b.2.1 p mode, fun p mode => setPrecRound b.2.2 p mode))

/-- The bracket of `sin x` as a pair of `Roundable`s: that of `sin |x|`, negated and swapped
when `neg` (`x < 0`). -/
def sinApprox (neg : Bool) (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := sinBracket x ex w
  if neg then (fun p mode => setPrecRound (-b.2) p mode, fun p mode => setPrecRound (-b.1) p mode)
  else (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- `cosBracket` as a pair of `Roundable`s for the Ziv loop. -/
def cosApprox (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := cosBracket x ex w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
