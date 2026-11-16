/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpBracket

/-!
## Brackets of `exp x` for finite floats

The argument reduction (MCA §4.3.1): with `k = ⌊⌊x / ln 2⌋⌋` (a floor division against the
lower end of the `ln 2` bracket, truncated to an integer) the remainder `r = x − k ln 2` has
`|r| < 7/10`, and `exp x = 2^k · exp r`.  The working precision `expWork e w` of the reduction
grows with the exponent of `x`, so that the bracket of `r` (`expReduce`) has width at most
`2^(−w−10)`.  The small argument is handled by `expDyadicBracket` on the dyadic truncation
`M / 2^(2^K)` of the lower end (`floorScaled`), the upper end widened by `exp d ≤ 1 + 2d` for
the distance `d` to the upper end; a negative `r` goes through `exp (−r)` and a reciprocal,
and a bracket straddling `0` (width `≤ 2^(−w−10)`) uses `1 + r ≤ exp r ≤ 1 + 2r` directly.
Finally the shift by `k` is exact, and `expApprox` is the pair of `Roundable`s for the Ziv loop.
`expRatBracket` handles a rational argument through the float `⌊q⌋_W` below it, the upper end
widened by `exp (q − ⌊q⌋_W) ≤ 1 + 2^(−w−14)`.  `expM1Bracket` brackets `exp x − 1`: the
working precision is raised by `max(−e, 0)` against the cancellation, and a tiny `x`
(`|x| < 2^(−w)`) is enclosed by `[x, x + |x| 2^e]` without any series.  `expM1RatBracket` is the
rational version: `expM1Bracket` at `⌊q⌋_W`, the upper end widened by `⌈exp y⌉ · 2^(e + 2 − W)`.
`expOfBracket X w` encloses `exp v` for a bracket `X` of `v` of width at most `1`: `expBracketAt`
at the lower end, the upper end widened by `exp (hi − lo) ≤ 1 + 2 (hi − lo)`.
-/

namespace Azurite.AzFloat

/-- `⌊|x| · 2^N⌋` as a natural (`0` for `NaN` and the infinities). -/
def floorScaled (x : AzFloat) (N : Nat) : AzNat :=
  match x with
  | finite _ e _ m _ =>
    let sh : AzInt := e + (AzNat.ofNat N).toAzInt - (AzNat.ofNat m.size).toAzInt
    if sh.sign then m <<< sh.abs.toNat else m >>> sh.abs.toNat
  | _ => AzNat.ofNat 0

/-- `x` truncated toward zero to an integer (`0` for `NaN` and the infinities). -/
def truncToAzInt (x : AzFloat) : AzInt :=
  match x with
  | y@(finite s _ _ _ _) => let n := (floorScaled y 0).toAzInt; if s then n else -n
  | _ => 0

/-- The working precision of the reduction for a float of exponent `e`. -/
def expWork (e : AzInt) (w : Nat) : Nat := w + 16 + (if e.sign then e.abs.toNat else 0)

/-- The working precision from which a bracket of `y ln b` computed at `expWork ey w` bits has
width below `1/256`, for `n = max(ey, 0) + |exponent of b|`: `88 + n`, or `110 + 6 size (n + 24)`
when that is smaller.  The width bound is a polynomial in `w + n` times `2^(−w)`, so the
threshold is only logarithmic in `n`: a huge exponent `ey` raises the precision of the bracket
of `y ln b` through `expWork` once, not a second time through the starting precision of Ziv's
loop (which would also be the precision of the final exponential). -/
def lnMulW₀ (n : Nat) : Nat := min (88 + n) (110 + 6 * (n + 24).size)

/-- The integer `k` and a bracket of `r = x − k ln 2` at working precision `W`, from a bracket
`L` of `ln 2` computed at precision `W` or finer. -/
def expReduceBy (L : AzFloat × AzFloat) (x : AzFloat) (W : Nat) : AzInt × AzFloat × AzFloat :=
  let k := truncToAzInt (divPrecRound x L.1 W .Floor).1
  let ka := ofAzNat k.abs
  let plo := (mulPrecRound ka L.1 W .Floor).1
  let phi := (mulPrecRound ka L.2 W .Ceiling).1
  if k.sign then
    (k, (subPrecRound x phi W .Floor).1, (subPrecRound x plo W .Ceiling).1)
  else
    (k, (addPrecRound x plo W .Floor).1, (addPrecRound x phi W .Ceiling).1)

/-- The integer `k` and a bracket of `r = x − k ln 2` at working precision `W`. -/
def expReduce (x : AzFloat) (W : Nat) : AzInt × AzFloat × AzFloat :=
  expReduceBy (ln2Bracket W) x W

/-- A supplier of brackets of `ln 2` that reuses a bracket `L` already computed at precision
`W₀`: `L` for every `W ≤ W₀`, `ln2Bracket W` above.  A power `b^y = exp (y ln b)` computes
`ln 2` for the logarithm and passes it on to the reduction of the exponential, which needs it at
(nearly) the same precision. -/
def ln2Reuse (W₀ : Nat) (L : AzFloat × AzFloat) (W : Nat) : AzFloat × AzFloat :=
  if W ≤ W₀ then L else ln2Bracket W

/-- The number of bit-burst levels: `2^(expK w) > w + 8`. -/
def expK (w : Nat) : Nat := (AzNat.ofNat (w + 8)).size

/-- The bracket of `exp` over `[rl, rh]` for `0 ≤ rl ≤ rh ≤ 3/4`: the lower end is the lower end
of `expDyadicBracket` at the truncation `t = M / 2^(2^K)` of `rl`, the upper end is the upper
end at `t` times `⌈1 + 2 ⌈rh − t⌉⌉`. -/
def expSmallBracket (rl rh : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  let K := expK w
  let N := 2 ^ K
  let M := floorScaled rl N
  let E := expDyadicBracket M K w
  let t := ofAzNat M >>> N
  let d := (subPrecRound rh t (w + 8) .Ceiling).1
  let f := (addPrecRound one (d <<< (1 : Nat)) (w + 8) .Ceiling).1
  (E.1, (mulPrecRound E.2 f (w + 8) .Ceiling).1)

/-- The bracket of `exp r` from a bracket `[rl, rh]` of `r`, `|r| < 7/10`, by the sign of `r`. -/
def expSignedBracket (rl rh : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  if rl.isNegative then
    if rh.isPositive then
      ((addPrecRound one rl (w + 8) .Floor).1,
        (addPrecRound one (rh <<< (1 : Nat)) (w + 8) .Ceiling).1)
    else
      let S := expSmallBracket (-rh) (-rl) w
      ((divPrecRound one S.2 (w + 8) .Floor).1, (divPrecRound one S.1 (w + 8) .Ceiling).1)
  else expSmallBracket rl rh w

/-- The bracket of `exp x` for a finite float `x` of exponent `e`, at working precision `w`, from
a bracket `L` of `ln 2` computed at precision `expWork e w` or finer. -/
def expBracketBy (L : AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let R := expReduceBy L x (expWork e w)
  let b := expSignedBracket R.2.1 R.2.2 w
  (b.1 <<< R.1, b.2 <<< R.1)

/-- The bracket of `exp x` for a finite float `x` of exponent `e`, at working precision `w`. -/
def expBracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  expBracketBy (ln2Bracket (expWork e w)) x e w

/-- `expBracket` as a pair of `Roundable`s for the Ziv loop. -/
def expApprox (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := expBracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- `expBracket` at the float's own exponent (`(one, one)` at zero; the callers never ask for
`NaN` or the infinities). -/
def expBracketAt (x : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  match x with
  | x@(finite _ e _ _ _) => expBracket x e w
  | zero => (one, one)
  | _ => (nan, nan)

/-- `expBracketAt` with the brackets of `ln 2` taken from a supplier `F` (`ln2Bracket`, or
`ln2Reuse W₀ L`). -/
def expBracketAtBy (F : Nat → AzFloat × AzFloat) (x : AzFloat) (w : Nat) : AzFloat × AzFloat :=
  match x with
  | x@(finite _ e _ _ _) => expBracketBy (F (expWork e w)) x e w
  | zero => (one, one)
  | _ => (nan, nan)

/-- The bracket of `exp q` for a rational `q`: `exp` of the float `y = ⌊q⌋_W` below `q` at
`W = w + 16 + size (num q)` (so `q − y ≤ 2^(−w−15)`), the upper end widened by the factor
`1 + 2^(−w−14) ≥ exp (q − y)`. -/
def expRatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let W := w + 16 + q.num.size
  let b := expBracketAt (ofAzRatRound q W .Floor).1 w
  (b.1, (addPrecRound b.2 (b.2 >>> (w + 14 : Nat)) (w + 8) .Ceiling).1)

/-- `expRatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def expRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := expRatBracket q w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The compensation `max(−e, 0)` for the cancellation in `exp x − 1` at exponent `e`. -/
def expM1Comp (e : AzInt) : Nat := if e.sign then 0 else e.abs.toNat

/-- The bracket of `exp x − 1` for a finite float `x` of exponent `e`: when `w ≤ max(−e, 0)`
(so `|x| < 2^e ≤ 2^(−w)`) the bracket `[x, ⌈x + |x| · 2^e⌉]` from `x ≤ exp x − 1 ≤ x + x²`;
otherwise `expBracket` at the compensated working precision `w + max(−e, 0)` with `1`
subtracted outward.  The brackets of `ln 2` come from a supplier `F`. -/
def expM1BracketBy (F : Nat → AzFloat × AzFloat) (x : AzFloat) (e : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let c := expM1Comp e
  if w ≤ c then (x, (addPrecRound x (x.abs <<< e) (w + 8) .Ceiling).1)
  else
    let b := expBracketBy (F (expWork e (w + c))) x e (w + c)
    ((subPrecRound b.1 one (w + c + 8) .Floor).1, (subPrecRound b.2 one (w + c + 8) .Ceiling).1)

/-- `expM1BracketBy` with the brackets of `ln 2` computed at the precision of the reduction. -/
def expM1Bracket (x : AzFloat) (e : AzInt) (w : Nat) : AzFloat × AzFloat :=
  expM1BracketBy ln2Bracket x e w

/-- `expM1Bracket` as a pair of `Roundable`s for the Ziv loop. -/
def expM1Approx (x : AzFloat) (e : AzInt) (w : Nat) : Roundable × Roundable :=
  let b := expM1Bracket x e w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `exp q − 1` for a rational `q`: `expM1Bracket` at the float `y = ⌊q⌋_W` below
`q` (`W = w + 16 + size (num q)`) with the exponent `e = ⌊log₂ |q|⌋ + 2` of `q` itself, the
upper end widened by `E · 2^(e + 2 − W) ≥ 2 (q − y) exp y` where `E = ⌈hi + 1⌉ ≥ exp y`. -/
def expM1RatBracket (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  let e : AzInt := AzInt.ofInt (AzRat.floorLogBaseAbs 2 q + 2)
  let W := w + 16 + q.num.size
  let b := expM1Bracket (ofAzRatRound q W .Floor).1 e w
  let E := (addPrecRound b.2 one (w + 8) .Ceiling).1
  let corr := E <<< (e - (AzNat.ofNat (W - 2)).toAzInt)
  (b.1, (addPrecRound b.2 corr (w + 8) .Ceiling).1)

/-- `expM1RatBracket` as a pair of `Roundable`s for the Ziv loop. -/
def expM1RatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := expM1RatBracket q w
  (fun p mode => setPrecRound b.1 p mode, fun p mode => setPrecRound b.2 p mode)

/-- The bracket of `exp v` from a bracket `X` of `v` (of width at most `1`): `expBracketAt` at
the lower end `lo` gives `[a, b] ∋ exp lo`, and the upper end is widened to `b + ⌈b · 2d⌉` for
`d = ⌈hi − lo⌉`, since `exp v ≤ exp lo · exp (v − lo) ≤ exp lo · (1 + 2d)`.  The brackets of
`ln 2` come from a supplier `F`. -/
def expOfBracketBy (F : Nat → AzFloat × AzFloat) (X : AzFloat × AzFloat) (w : Nat) :
    AzFloat × AzFloat :=
  let b := expBracketAtBy F X.1 w
  let d := (subPrecRound X.2 X.1 (w + 8) .Ceiling).1
  let corr := (mulPrecRound b.2 (d <<< AzInt.ofInt 1) (w + 8) .Ceiling).1
  (b.1, (addPrecRound b.2 corr (w + 8) .Ceiling).1)

/-- `expOfBracketBy` with the brackets of `ln 2` computed at the precision of the reduction. -/
def expOfBracket (X : AzFloat × AzFloat) (w : Nat) : AzFloat × AzFloat :=
  expOfBracketBy ln2Bracket X w


/-- **The tiny-exponent path of the exponential family**: the rounding of `exp v` for a real
`v ≠ 0` with `|v| < 2^E` and known sign (`pos`: `v > 0`), when `E ≤ −(p + 72)`.  Then
`exp v ∈ (1, 1 + 2^(E+1)]` for `v > 0` and `−exp v ∈ (−1, −1 + 2^(E+1)]` for `v < 0`; one test
of `roundingPossible` (in the negated mode for `v < 0`, the result negated) with the exact end
`±1` — a rounding boundary — at the open side.  Nothing is computed from `v`, so the cost is
independent of `E`; a Ziv loop on a two-sided bracket of `exp v` would need about `|E|` bits.
`none` when `E` is not small enough or the test fails.  Used by `exp`, `2^x`, `b^x`, `x^y`
and their rational variants (`v = x`, `x ln 2`, `x ln b`, `y ln x`). -/
def expNearOne? (pos : Bool) (E : AzInt) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  let w := p + zivGuardBits + 8
  if E.sign = false ∧ w ≤ E.abs.toNat then
    let d := one <<< (E + AzInt.ofInt 1)
    if pos then
      roundingPossible (fun P M => setPrecRound one P M)
        (fun P M => setPrecRound (addPrecRound one d w .Ceiling).1 P M) p mode
    else
      (roundingPossible (fun P M => setPrecRound (-one) P M)
        (fun P M => setPrecRound (addPrecRound (-one) d w .Ceiling).1 P M) p (-mode)).map
        fun r => (-r.1, r.2.swap)
  else none

/-- **The large-negative path of `exp v − 1`**: the rounding of `exp v − 1` for a real `v < 0`
(`neg`) with `N ≤ |v|`.  Then `exp v − 1 ∈ (−1, −1 + 2^(−N)]`, the mirror image of
`exp v' ∈ [1 − 2^(−N), 1)` for `v' = ln (1 − exp v)`, `|v'| < 2^(2 − N)`: one test of
`expNearOne?` at the exponent `2 − min N 2^62` in the negated mode, the result negated.
Nothing is computed from `v`; a Ziv loop would bracket `exp v` to about `|v|` bits only to
learn that it is negligible.  `none` when `v > 0`, `N` is not large enough (about `p + 74`)
or the test fails. -/
def expM1NearNegOne? (neg : Bool) (N : Nat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if neg then
    (expNearOne? false (AzInt.ofInt (2 - ((min N 4611686018427387904 : Nat) : Int))) p
      (-mode)).map fun r => (-r.1, r.2.swap)
  else none

/-- A natural `N ≤ |x|` for a finite float `x` of exponent `e` (`|x| ≥ 2^(e−1)`): `2^(e−1)`
capped at `2^61` for `e ≥ 1`, and `0` otherwise. -/
def floatAbsFloorN (e : AzInt) : Nat := if e.sign then 2 ^ (min e.abs.toNat 62) / 2 else 0

/-- A natural `N ≤ |q|` for a rational `q`: `⌊num / den⌋`. -/
def ratAbsFloorN (q : AzRat) : Nat := (q.num / q.den).toNat

/-- An exponent bound for a rational: `|q| < 2^(size num − size den + 1)`. -/
def ratTinyExp (q : AzRat) : AzInt :=
  (AzNat.ofNat (q.num.size + 1)).toAzInt - (AzNat.ofNat q.den.size).toAzInt

/-- The exponent bound of `y ln B` for `|y| < 2^Ey` and `|ln B| ≤ N`: `Ey + size N`. -/
def nearOneExp (Ey : AzInt) (N : Nat) : AzInt := Ey + (AzNat.ofNat N.size).toAzInt

/-- `expNearOne?` for a rational exponent `q` and a base with `|ln B| ≤ N` (`none` for
`q = 0`). -/
def ratNearOne? (q : AzRat) (N : Nat) (p : Nat) (mode : RoundingMode) :
    Option (AzFloat × Ordering) :=
  if q.num = 0 then none else expNearOne? q.sign (nearOneExp (ratTinyExp q) N) p mode

end Azurite.AzFloat
