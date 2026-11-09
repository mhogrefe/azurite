/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Interval
import Azurite.AzFloat.Rem
import Azurite.AzFloat.Ziv

/-!
## The bracket of `cos x`

`cosBracket x ex w` encloses `cos x` for a finite float `x` of exponent `ex` at Ziv level `w`,
working at `W = cosWork ex w = w + 12 + max(ex, 0)` bits:

* **Reduction.**  With `[lo, hi]` the bracket of `π` at `W` bits and `y = 2 lo` (a float, so the
  remainder is exact), `r' = remExact |x| y = |x| − k y ∈ [0, y)`, `k = ⌊|x|/y⌋`.  The true
  reduction `r = |x| − 2kπ = r' − 2k(π − lo)` lies in `[r' − E, r']` with
  `E = ⌈|x| (hi − lo)⌉ ≥ 2k(π − lo)` (`k ≤ |x|/(2 lo)`, `lo ≥ 1`), and `cos x = cos r`.
* **Series.**  `cosSeries m W` encloses `cos m` for `|m| ≤ 1` by the alternating Taylor series in
  interval arithmetic (`Encl`), `cosTerms W = W/4 + 2` terms beyond the first, the tail bounded by
  the last term computed (the terms decrease).  Here `m = r'/8 ∈ [0, π/4)`.
* **Doubling.**  `cos (r/8)` is widened by the Lipschitz bound `E/8` (`|cos a − cos b| ≤ |a − b|`)
  to enclose `cos (r/8)`, then `cos (2θ) = 2 cos² θ − 1` three times (`cosDouble`); the first
  two inputs are nonnegative (`θ < π/2`), the last goes through `|cos (r/2)|` (`enclAbs`).

`cosApprox` is the pair of `Roundable`s for the Ziv loop (`AzFloat/Cos.lean`).
-/

namespace Azurite.AzFloat

/-- The working precision of `cos` at Ziv level `w` for an argument of exponent `ex`. -/
def cosWork (ex : AzInt) (w : Nat) : Nat := w + 12 + (if ex.sign then ex.abs.toNat else 0)

/-- The number of series terms beyond the first at precision `W`. -/
def cosTerms (W : Nat) : Nat := W / 4 + 2

/-- The enclosure with its lower end clamped at `0` (for a value known to be nonnegative). -/
def enclClamp0 (a : Encl) : Encl := (clampNonneg a.1, a.2)

/-- The absolute value of an enclosure `[lo, hi]`: `[max(0, lo, −hi), max(hi, −lo)]`. -/
def enclAbs (a : Encl) : Encl := (clampNonneg (maxOf a.1 (-a.2)), maxOf a.2 (-a.1))

/-- The double-angle step `2[a]² − 1` for a nonnegative enclosure `a` of `cos θ`. -/
def cosDouble (W : Nat) (a : Encl) : Encl :=
  Encl.sub W (Encl.mul W (Encl.nat 2) (Encl.mul W a a)) (Encl.exact one)

/-- The series loop: `j` further terms from the current index `i`, the current term `t`
(enclosing `m^{2i}/(2i)!`), the partial sum `S` and the sign flag `pos` (`i` even: the next term
is subtracted).  Returns the final partial sum and the last term. -/
def cosSeriesLoop (W : Nat) (u : Encl) : Nat → Nat → Bool → Encl → Encl → Encl × Encl
  | 0, _, _, S, t => (S, t)
  | j + 1, i, pos, S, t =>
    let t' := Encl.div W (Encl.mul W t u) (Encl.nat ((2 * i + 1) * (2 * i + 2)))
    let S' := if pos then Encl.sub W S t' else Encl.add W S t'
    cosSeriesLoop W u j (i + 1) (!pos) S' t'

/-- An enclosure of `cos m` for a float `m` with `|m| ≤ 1`: the Taylor series with `cosTerms W`
terms beyond the first, widened by the last term (which bounds the tail). -/
def cosSeries (m : AzFloat) (W : Nat) : Encl :=
  let am := Encl.exact m.abs
  let u := Encl.mul W am am
  let St := cosSeriesLoop W u (cosTerms W) 0 true (Encl.exact one) (Encl.exact one)
  Encl.widen W St.1 St.2

/-- The bracket of `cos x` at Ziv level `w` for a finite `x` of exponent `ex`. -/
def cosBracket (x : AzFloat) (ex : AzInt) (w : Nat) : AzFloat × AzFloat :=
  let W := cosWork ex w
  let P := piBracket W
  let y := P.1 <<< AzInt.ofInt 1
  let r := remExact x.abs y
  let E := (mulPrecRound x.abs (subPrecRound P.2 P.1 64 .Ceiling).1 64 .Ceiling).1
  let m := r <<< AzInt.ofInt (-3)
  let C := Encl.widen W (cosSeries m W) (Encl.exact (E <<< AzInt.ofInt (-3)))
  let C2 := cosDouble W (enclClamp0 C)
  let C4 := cosDouble W (enclClamp0 C2)
  cosDouble W (enclAbs C4)

/-- **The tiny-argument path of `cos`** for an argument below `2^e` in magnitude: when
`e ≤ −(p + 72)`, `−cos x` lies in `(−1, −1 + 2^(2e)]` (from `cos x ≥ 1 − x²/2`), so it is rounded
in the negated mode from the bracket `[−1, ⌈−1 + 2^(2e)⌉_{p+72}]` by the test of
`roundingPossible`, and the result is negated.  (The negation puts the exact end `1`, a rounding
boundary, at the open side of the half-open test.)  Nothing is computed from the argument, so the
cost is independent of `e`; the Ziv loop would need about `2|e|` bits.  `none` when the argument
is not tiny or the test fails. -/
def cosTiny? (e : AzInt) (p : Nat) (mode : RoundingMode) : Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits
  if e.sign = false ∧ w + 8 ≤ e.abs.toNat then
    let hi := (addPrecRound (-one) ((one <<< e) <<< e) (w + 8) .Ceiling).1
    (roundingPossible (fun P M => setPrecRound (-one) P M) (fun P M => setPrecRound hi P M) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

/-- `cosBracket` as a pair of `Roundable`s for the Ziv loop. -/
def cosApprox (x : AzFloat) (ex : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := cosBracket x ex w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

end Azurite.AzFloat
