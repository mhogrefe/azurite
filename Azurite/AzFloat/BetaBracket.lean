/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket

/-!
## The bracket of the Beta function `B(a, b) = Γ(a) Γ(b) / Γ(a + b)`

`betaCore a b w` is the sign of `B(a, b)` and a positive enclosure of `|B(a, b)|` at Ziv level
`w`, for finite floats `a`, `b`; `none` when the pieces do not give one at this level.  It is
the exponential of `lnAbsBetaCore`, an enclosure of

  `ln |B(a, b)| = ln |Γ(a)| + ln |Γ(b)| − ln |Γ(a + b)|`,

in which the three logarithms of `|Γ|` are taken together.  Each argument `v` contributes a
**piece** (`lnGammaPiece`): `ln |Γ(v)| = t + ½ ln q` with

* `v > 0`: `t = ln Γ(y) − ½ ln (2π)` by Stirling's series at the shifted argument `y = v + δ`
  (`stirlingEnclWith`), and `q = 2π / P²` for the rising product `P = v (v + 1) ⋯ (v + δ − 1)`;
* `v < 0`: the reflection formula `Γ(v) Γ(1 − v) = π / sin (π v)`: `t` is minus the Stirling
  value at the shifted `1 − v`, and `q = π P² / (2 sin² (π v))`.  The sine needs the distance
  of `v` to an integer `k` with its sign: `gammaFracEncl` for `a` and `b`, `(a − k) + b` on
  enclosures for the sum (`betaSumFrac`).  The sign of the sine is the sign of `Γ(v)`.

So one table of tangent numbers serves the three series, `π` is computed once, and the
constants, rising products and sines share **one logarithm**, `½ ln (q_a q_b / q_s)`; one
exponential follows.  The sum `a + b` enters by an enclosure: it need not be a float at the
working precision.

The pieces are evaluated at `betaBits` more bits than the Ziv level, the size of `|ln Γ|` at
the three arguments.  Nothing is assumed about the widths: where `B` is small against its
factors (near a pole of `Γ(a + b)`, where `B` vanishes; large `a`, `b`) Ziv's loop supplies
the bits.  The proofs are in `Equiv/BetaBracket.lean`.
-/

namespace Azurite.AzFloat

/-- The sign of a number (`true`: negative) and a positive enclosure of its absolute value,
from an enclosure `D`; `none` when `D` contains `0`. -/
def fracOfEncl (D : Encl) : Option (Bool × Encl) :=
  if lt zero D.1 then some (false, D)
  else if lt D.2 zero then some (true, Encl.neg D)
  else none

/-- The integer next to a float `x`, the sign of `x − k` and a positive enclosure of
`|x − k|`. -/
def gammaFloatFrac (x : AzFloat) (W : Nat) : Option (Bool × AzInt × Encl) :=
  let k := gammaNearInt x
  (gammaFracEncl x k W).map fun t => (t.1, k, t.2)

/-- The precision at which `a + b` is rounded to find the integer next to it: `66` bits beyond
the binary point, so that the rounded sum is within `2^(−65)` of the sum whatever the sizes of
`a` and `b`. -/
def betaSumPrec (a b : AzFloat) : Nat :=
  let ea := expOf a
  let eb := expOf b
  let es := (if ea ≤ eb then eb else ea) + 1
  66 + (if es.sign then es.abs.toNat else 0)

/-- The same for the sum `a + b`: `k` next to the sum rounded at `betaSumPrec` bits (a
negative sum is then less than `1` away from `k`, as the sine needs), and `(a − k) + b` on
enclosures. -/
def betaSumFrac (a b : AzFloat) (W : Nat) : Option (Bool × AzInt × Encl) :=
  let k := gammaNearInt (addPrecRound a b (betaSumPrec a b) .Nearest).1
  (fracOfEncl (Encl.add W (Encl.sub W (Encl.exact a) (Encl.exact (ofAzInt k)))
    (Encl.exact b))).map fun t => (t.1, k, t.2)

/-- `lnGammaStirlingEncl` on a given table `T` of tangent numbers (`T = tangentNumbers M`):
the enclosure of `ln Γ(y) − ½ ln (2π)` for `y ≥ 1`. -/
def stirlingEnclWith (V M : Nat) (T : Array AzNat) (Y : Encl) (tol : AzFloat) : Encl :=
  let lnY := lnOfEncl Y V
  let half := Encl.div V (Encl.exact one) (Encl.nat 2)
  let A := Encl.mul V (Encl.subNonneg V Y half) (clampNonneg lnY.1, lnY.2)
  let inv := Encl.div V (Encl.exact one) Y
  Encl.add V (Encl.sub V A Y)
    (stirlingSumLoop V T (Encl.mul V inv inv) tol (M - 1) 1 inv (Encl.exact zero))

/-- The Stirling value and the rising product of a positive argument given by an enclosure `X`
below `2^e`: `(St, P)` with `St` enclosing `ln Γ(x + δ) − ½ ln (2π)` and `P` enclosing
`x (x + 1) ⋯ (x + δ − 1)`, `δ` the shift of `ln Γ`. -/
def stirlingShifted (X : Encl) (e : AzInt) (L V M : Nat) (T : Array AzNat) (tol : AzFloat) :
    Encl × Encl :=
  let δ := lnGammaShift X.1 e L
  (stirlingEnclWith V M T (Encl.add V X (Encl.nat δ)) tol, risingEncl V X δ)

/-- **A piece of `ln |Γ(v)|`** from an enclosure `X` of `v < 2^e` that does not contain `0`:
`(neg, t, q)` with `neg` the sign of `Γ(v)` (`true`: negative), and enclosures `t`, `q` (the
latter positive) such that `ln |Γ(v)| = t + ½ ln q`.  For a negative `v`, `F ()` gives an
integer `k`, the sign of `v − k` and a positive enclosure of `|v − k|`.  `Pi` encloses `π`;
`w` is the level of the sine. -/
def lnGammaPiece (X : Encl) (e : AzInt) (F : Unit → Option (Bool × AzInt × Encl)) (Pi : Encl)
    (L V M : Nat) (T : Array AzNat) (tol : AzFloat) (w : Nat) : Option (Bool × Encl × Encl) :=
  if lt zero X.1 then
    let r := stirlingShifted X e L V M T tol
    some (false, r.1, Encl.div V (Encl.mul V (Encl.nat 2) Pi) (Encl.mul V r.2 r.2))
  else if lt X.2 zero then
    let X₁ := Encl.sub V (Encl.exact one) X
    if lt zero X₁.1 then
      match (F ()).bind fun t => gammaSinOfFrac t.1 t.2.1 t.2.2 (w + 16) w with
      | some (neg, Sn) =>
        let r := stirlingShifted X₁ ((if e.sign then e else 0) + 1) L V M T tol
        some (neg, Encl.neg r.1,
          Encl.div V (Encl.mul V Pi (Encl.mul V r.2 r.2))
            (Encl.mul V (Encl.nat 2) (Encl.mul V Sn Sn)))
      | none => none
    else none
  else none

/-- The bits of `|ln Γ|` at arguments below `2^ea`, `2^eb` and `2^es`. -/
def betaBits (ea eb es : AzInt) : Nat :=
  max (max (gammaLnBits ea) (gammaLnBits eb)) (gammaLnBits es)

/-- `(neg, b)`: the sign of `B(a, b)` and an enclosure `b` of `ln |B(a, b)|` at level `w` (with
the sines at level `ws`), for arguments given by enclosures: `A V`, `B V`, `S V` enclose `a`,
`b`, `a + b` (below `2^ea`, `2^eb`, `2^es`) at the working precision `V`, and `Fa W`, `Fb W`,
`Fs W` give their distances to an integer.  `none` when a piece is missing. -/
def lnAbsBetaEncl (A B S : Nat → Encl) (ea eb es : AzInt)
    (Fa Fb Fs : Nat → Option (Bool × AzInt × Encl)) (w ws : Nat) : Option (Bool × Encl) :=
  let L := lnGammaShiftExp w
  let V := w + 2 * L + 8 + 2 * w.log2
  let pe := fun (e : AzInt) => max (L + 1) (if e.sign then e.abs.toNat else 0)
  let M := max (max (lnGammaTerms w (pe ea)) (lnGammaTerms w (pe eb))) (lnGammaTerms w (pe es))
  let T := AzNat.tangentNumbers M
  let tol := powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)
  let Pi := Encl.pi V
  match lnGammaPiece (A V) ea (fun _ => Fa (ws + 16)) Pi L V M T tol ws,
    lnGammaPiece (B V) eb (fun _ => Fb (ws + 16)) Pi L V M T tol ws,
    lnGammaPiece (S V) es (fun _ => Fs (ws + 16)) Pi L V M T tol ws with
  | some (na, ta, qa), some (nb, tb, qb), some (ns, ts, qs) =>
    some ((na != nb) != ns,
      Encl.add V (Encl.sub V (Encl.add V ta tb) ts)
        (Encl.half (lnOfEncl (Encl.div V (Encl.mul V qa qb) qs) V)))
  | _, _, _ => none

/-- The exponential of `lnAbsBetaEncl` at Ziv level `w`: the sign of `B(a, b)` and a positive
enclosure of `|B(a, b)|`. -/
def betaEnclOf (A B S : Nat → Encl) (ea eb es : AzInt)
    (Fa Fb Fs : Nat → Option (Bool × AzInt × Encl)) (w : Nat) : Option (Bool × Encl) :=
  (lnAbsBetaEncl A B S ea eb es Fa Fb Fs (w + betaBits ea eb es) w).bind fun r =>
    (gammaExpEncl false r.2 w).map fun g => (r.1, g)

/-- `lnAbsBetaEncl` for floats `a`, `b`: the sign of `B(a, b)` and an enclosure of
`ln |B(a, b)|`. -/
def lnAbsBetaCore (a b : AzFloat) (w ws : Nat) : Option (Bool × Encl) :=
  let ea := expOf a
  let eb := expOf b
  lnAbsBetaEncl (fun _ => Encl.exact a) (fun _ => Encl.exact b)
    (fun V => Encl.add V (Encl.exact a) (Encl.exact b)) ea eb ((if ea ≤ eb then eb else ea) + 1)
    (gammaFloatFrac a) (gammaFloatFrac b) (betaSumFrac a b) w ws

/-- `(neg, b)`: the sign of `B(a, b)` and a positive enclosure `b` of `|B(a, b)|` at Ziv level
`w`; `none` when the pieces do not give one at this level. -/
def betaCore (a b : AzFloat) (w : Nat) : Option (Bool × Encl) :=
  let ea := expOf a
  let eb := expOf b
  let es := (if ea ≤ eb then eb else ea) + 1
  (lnAbsBetaCore a b (w + betaBits ea eb es) w).bind fun r =>
    (gammaExpEncl false r.2 w).map fun g => (r.1, g)

/-- The bracket of `B(a, b)` as a pair of `Roundable`s, strict on both sides; the dummy bracket
`[−1, 1]` when `betaCore` gives nothing. -/
def betaApprox (a b : AzFloat) (w : Nat) : Roundable × Roundable :=
  gammaApproxOf (betaCore a b w) w

/-- Is `a + b` a non-positive integer?  For finite `a`, `b`.  When both are integers the sign of
the sum is one comparison.  When neither is, both are below `2` to their precision in absolute
value, so an integer sum is representable at `qa + qb + 2` bits: the sum is an integer exactly
when the addition at that precision is exact and gives one.  (The exact sum itself can be
astronomically long — `2^(−10⁹) + 3/2` — and is never formed.) -/
def sumIsNonposInt (a b : AzFloat) : Bool :=
  if isInteger a then isInteger b && le a (-b)
  else if isInteger b then false
  else
    let r := addPrecRound a b (a.precision?.getD 1 + b.precision?.getD 1 + 2) .Nearest
    if r.2 = .eq then isInteger r.1 && le r.1 zero else false

/-- Is `a + b` a positive integer, for `a`, `b` that are not integers?  As in
`sumIsNonposInt`: the sum is an integer exactly when the addition at `qa + qb + 2` bits is
exact and gives one. -/
def sumIsPosInt (a b : AzFloat) : Bool :=
  let r := addPrecRound a b (a.precision?.getD 1 + b.precision?.getD 1 + 2) .Nearest
  if r.2 = .eq then isInteger r.1 && lt zero r.1 else false

/-- Arguments where `B(a, b)` is known to be irrational, so that Ziv's loop needs no fuel
(`betaApprox_cert`, `Equiv/BetaCertificate.lean`): `a` and `b` are not integers, and either
`a + b` is a positive integer — `B(a, b)` is then a rational multiple of `π / sin (π a)` — or
both are quarter-integers, where `B(a, b)` is `Γ(1/4)^(±2)` times a number algebraic over
`ℤ[π]` (Chudnovsky's theorem; `Azurite.Chudnovsky.irrational_beta_of_den`).  To be used off
the zeros of `B` (`sumIsNonposInt`). -/
def betaSpecial (a b : AzFloat) : Bool :=
  a.isFinite && b.isFinite && !isInteger a && !isInteger b
    && (sumIsPosInt a b || (gammaSpecial a && gammaSpecial b))

end Azurite.AzFloat
