/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Forms
import Azurite.AzComplexFloat.Arith
import Azurite.AzFloat.Pi
import Azurite.AzFloat.Exp
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.RoundToInteger
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Compare

/-!
# Hilbert class polynomials by complex floating point (generator side)

`hilbertClassPoly D` is the list of the integer coefficients (constant term first) of
`H_{−D}(X) = ∏ (X − j(τ))` over the reduced forms `(A, B, C)` of discriminant `−D`,
`τ = (−B + √−D)/(2A)`.  Nothing here is proven: the generator's output is checked by
`ECPP.check`, and a wrong polynomial only makes the search fail.

* `q = e^(2πiτ) = e^(−π√D/A) · e^(−πiB/A)`;
* `P(q) = ∏ (1 − qⁿ) = ∑ (−1)^k q^(k(3k−1)/2)` (Euler's pentagonal number theorem);
* `f = Δ(2τ)/Δ(τ) = q (P(q²)/P(q))^24` and `j = (256 f + 1)³ / f`;
* the forms `(A, ±B, C)` give conjugate values, so the product is formed over the reals
  from the factors `X − j` and `X² − 2 Re(j) X + |j|²`;
* the working precision is the size `π√D ∑ 1/A` of the largest coefficient in bits plus a
  margin, and the result is accepted only if every coefficient is within `2^(−8)` of an
  integer; otherwise the precision is doubled.
-/

namespace Azurite.ECPP

open AzComplexFloat

private def N' : RoundingMode := .Nearest

private def fmul (x y : AzFloat) (p : Nat) : AzFloat := (AzFloat.mulPrecRound x y p N').1
private def fadd (x y : AzFloat) (p : Nat) : AzFloat := (AzFloat.addPrecRound x y p N').1
private def fsub (x y : AzFloat) (p : Nat) : AzFloat := (AzFloat.subPrecRound x y p N').1
private def fdiv (x y : AzFloat) (p : Nat) : AzFloat := (AzFloat.divPrecRound x y p N').1
private def fnat (n : Nat) : AzFloat := AzFloat.ofAzNat (AzNat.ofNat n)

private def cmul (z w : AzComplexFloat) (p : Nat) : AzComplexFloat := (mulPrecRound z w p p N' N').1
private def csqr (z : AzComplexFloat) (p : Nat) : AzComplexFloat := (sqrPrecRound z p p N' N').1
private def cadd (z w : AzComplexFloat) (p : Nat) : AzComplexFloat := (addPrecRound z w p p N' N').1
private def csub (z w : AzComplexFloat) (p : Nat) : AzComplexFloat := (subPrecRound z w p p N' N').1
private def cdiv (z w : AzComplexFloat) (p : Nat) : AzComplexFloat := (divPrecRound z w p p N' N').1

/-- `z^n` by binary powering at precision `p`. -/
def cpow (z : AzComplexFloat) (n p : Nat) : AzComplexFloat := Id.run do
  let mut acc := AzComplexFloat.one
  let mut b := z
  let mut e := n
  for _ in [0:n.size] do
    if e % 2 == 1 then acc := cmul acc b p
    b := csqr b p
    e := e / 2
  return acc

/-- `∏ (1 − qⁿ)` by the pentagonal number series, for `|q| ≤ 2^(−bitsPerPower)`. -/
def eulerProduct (q : AzComplexFloat) (bitsPerPower p : Nat) : AzComplexFloat := Id.run do
  let mut s := AzComplexFloat.one
  for k in [1:p + 2] do
    let e₁ := k * (3 * k - 1) / 2
    if e₁ * bitsPerPower > p + 8 then break
    let t := cadd (cpow q e₁ p) (cpow q (e₁ + k) p) p
    s := if k % 2 == 1 then csub s t p else cadd s t p
  return s

/-- `j(τ)` for the form `(A, B, ·)` of discriminant `−D`, at precision `p`. -/
def jOfForm (D A B p : Nat) : AzComplexFloat :=
  let pi := AzFloat.pi p
  let sqrtD := (AzFloat.sqrtPrecRound (fnat D) p N').1
  let r := (AzFloat.expPrecRound (-(fdiv (fmul pi sqrtD p) (fnat A) p)) p N').1
  let θ := -(fdiv (fmul pi (fnat B) p) (fnat A) p)
  let q := (mulFloatPrecRound (cisPrecRound θ p p N' N').1 r p p N' N').1
  let bits := 4 * Nat.sqrt D / A
  let q2 := csqr q p
  let ratio := cdiv (eulerProduct q2 (2 * bits) p) (eulerProduct q bits p) p
  let f := cmul q (cpow ratio 24 p) p
  let g := cadd ((mulFloatPrecRound f (fnat 256) p p N' N').1) AzComplexFloat.one p
  cdiv (cmul g (csqr g p) p) f p

/-- Multiply a real polynomial (constant term first) by `X² + s X + t`. -/
def mulQuadratic (c : List AzFloat) (s t : AzFloat) (p : Nat) : List AzFloat :=
  let n := c.length
  let get (i : Int) : AzFloat := if i < 0 then AzFloat.zero else c.getD i.toNat AzFloat.zero
  (List.range (n + 2)).map fun i =>
    fadd (get ((i : Int) - 2)) (fadd (fmul s (get ((i : Int) - 1)) p) (fmul t (get i) p) p) p

/-- Multiply a real polynomial (constant term first) by `X − r`. -/
def mulLinear (c : List AzFloat) (r : AzFloat) (p : Nat) : List AzFloat :=
  let n := c.length
  let get (i : Int) : AzFloat := if i < 0 then AzFloat.zero else c.getD i.toNat AzFloat.zero
  (List.range (n + 1)).map fun i => fsub (get ((i : Int) - 1)) (fmul r (get i) p) p

/-- A float that is within `2^(−8)` of an integer, as that integer. -/
def nearInteger? (x : AzFloat) : Option AzInt :=
  let r := AzFloat.roundToInteger x
  let d := (AzFloat.subPrecRound x r 64 N').1.abs
  if AzFloat.partialCompare d (AzFloat.powerOf2 (AzInt.ofInt (-8))) == some .lt then
    r.toAzRat?.map fun v => AzInt.mkNorm v.sign v.num
  else none

/-- The coefficients of `H_{−D}` at precision `p`, if they all come out near integers. -/
def hilbertClassPolyAt (D p : Nat) : Option (List AzInt) :=
  let coeffs := (reducedForms D).foldl (fun c f =>
    let j := jOfForm D f.a f.b p
    if f.paired then
      mulQuadratic c (-(j.re <<< AzInt.ofInt 1)) (normSqrPrecRound j p N').1 p
    else mulLinear c j.re p) [AzFloat.one]
  coeffs.mapM nearInteger?

/-- An estimate of the bit size of the largest coefficient of `H_{−D}`. -/
def classPolyBits (D : Nat) : Nat :=
  (reducedForms D).foldl (fun s f =>
    s + (if f.paired then 2 else 1) * ((46 * (Nat.sqrt D + 1)) / (10 * f.a) + 1)) 0

/-- **The Hilbert class polynomial `H_{−D}`**: its integer coefficients, constant term first
(`none` if three precisions fail). -/
def hilbertClassPoly (D : Nat) : Option (List AzInt) :=
  let p₀ := classPolyBits D + 4 * classNumber D + 64
  (hilbertClassPolyAt D p₀).orElse fun _ =>
    (hilbertClassPolyAt D (2 * p₀)).orElse fun _ => hilbertClassPolyAt D (4 * p₀)

end Azurite.ECPP
