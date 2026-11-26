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
`ECPP.check`, and a wrong polynomial only makes the search fail.  `genusClassPoly D` is one
of the factors of `H_{−D}` over the genus field (see the last section).  For
`D ≡ 7 (mod 8)`, `weberClassPoly D` and `genusWeberPoly D` are the same for Weber's class
invariants, with much smaller coefficients (see the section on them).

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

/-- The real polynomial `∏ (X − inv f)` over the forms, a form `(A, B, C)` marked `paired`
standing for `(A, ±B, C)` with conjugate values. -/
def formsPoly (forms : List RedForm) (inv : RedForm → AzComplexFloat) (p : Nat) :
    List AzFloat :=
  forms.foldl (fun c f =>
    let j := inv f
    if f.paired then
      mulQuadratic c (-(j.re <<< AzInt.ofInt 1)) (normSqrPrecRound j p N').1 p
    else mulLinear c j.re p) [AzFloat.one]

/-- `g` at the precisions `p₀`, `2p₀`, `4p₀`, until it gives a result. -/
def retry3 {α : Type} (p₀ : Nat) (g : Nat → Option α) : Option α :=
  (g p₀).orElse fun _ => (g (2 * p₀)).orElse fun _ => g (4 * p₀)

/-- The coefficients of `H_{−D}` at precision `p`, if they all come out near integers. -/
def hilbertClassPolyAt (D p : Nat) : Option (List AzInt) :=
  (formsPoly (reducedForms D) (fun f => jOfForm D f.a f.b p) p).mapM nearInteger?

/-- An estimate of the bit size of the largest coefficient of `H_{−D}`. -/
def classPolyBits (D : Nat) : Nat :=
  (reducedForms D).foldl (fun s f =>
    s + (if f.paired then 2 else 1) * ((46 * (Nat.sqrt D + 1)) / (10 * f.a) + 1)) 0

/-- **The Hilbert class polynomial `H_{−D}`**: its integer coefficients, constant term first
(`none` if three precisions fail). -/
def hilbertClassPoly (D : Nat) : Option (List AzInt) :=
  retry3 (classPolyBits D + 4 * classNumber D + 64) (hilbertClassPolyAt D)

/-! ### Weber's class invariants

For `D ≡ 7 (mod 8)` the class field is generated by much smaller numbers than `j`: values of
the Weber functions

  `𝔣(τ) = q^(−1/48) P(−q^(1/2)) / P(q)`,  `𝔣₁(τ) = q^(−1/48) P(q^(1/2)) / P(q)`,
  `𝔣₂(τ) = √2 q^(1/24) P(q²) / P(q)`

(`q^s = e^(2πisτ)`), with `j = (x − 16)³ / x` for each of `x = 𝔣^24, −𝔣₁^24, −𝔣₂^24`.  To the
form `(a, b, c)` with `τ = (−b + √−D)/(2a)`, `ζ = e^(2πi/48)` and `ε = (−1)^((D+1)/8)`,
attach (N. Yui, D. Zagier, *On the singular values of Weber modular functions*, Math. Comp.
66 (1997), 1645–1662, §3)

* `ζ^(b(a − c − ac²)) 𝔣(τ)` if `a` and `c` are even,
* `ε ζ^(b(a − c − ac²)) 𝔣₁(τ)` if `a` is even and `c` is odd,
* `ε ζ^(b(a − c + a²c)) 𝔣₂(τ)` if `a` is odd and `c` is even.

For `3 ∤ D` these `h` numbers are the roots of a polynomial `W_D` with integer coefficients,
and a root `u` gives the root `(u^24 − 16)³ / u^24` of `H_{−D}`; for `3 ∣ D` their cubes are,
with `(v^8 − 16)³ / v^8`.  The coefficients have about `1/72` (`1/24` for the cubes) of the
digits of those of `H_{−D}`.  The forms `(a, ±b, c)` give conjugate values, and the classes
act on the values as on the forms, so the product over the reals and the factor over the
genus field are formed as for `j`.

As everything in this file, the recipe is not proven: the result is accepted only when the
coefficients come out near integers, and what the search builds on it is checked by
`ECPP.check`.  The tests compare the roots modulo primes with those of `H_{−D}`. -/

/-- The kind of Weber invariant for `−D`: `1` (the invariant itself, `3 ∤ D`) or `3` (its
cube, `3 ∣ D`) for `D ≡ 7 (mod 8)`, none otherwise. -/
def weberKind (D : Nat) : Option Nat :=
  if D % 8 = 7 then (if D % 3 = 0 then some 3 else some 1) else none

/-- `ζ₄₈^k = e^(2πik/48)`. -/
def zeta48 (k : Int) (p : Nat) : AzComplexFloat :=
  let θ := fdiv (fmul (AzFloat.pi p) (fnat (k % 48).toNat) p) (fnat 24) p
  (cisPrecRound θ p p N' N').1

/-- A Weber function at `τ = (−B + √−D)/(2A)`: `𝔣`, `𝔣₁`, `𝔣₂` for `which = 0, 1, 2`.  All
the powers of `q` come from `w = e^(2πiτ/48)`. -/
def weberFn (which D A B p : Nat) : AzComplexFloat :=
  let pi := AzFloat.pi p
  let sqrtD := (AzFloat.sqrtPrecRound (fnat D) p N').1
  let den := fnat (48 * A)
  let r := (AzFloat.expPrecRound (-(fdiv (fmul pi sqrtD p) den p)) p N').1
  let θ := -(fdiv (fmul pi (fnat B) p) den p)
  let w := (mulFloatPrecRound (cisPrecRound θ p p N' N').1 r p p N' N').1
  let h := cpow w 24 p
  let q := csqr h p
  let bits := 4 * Nat.sqrt D / A
  let Pq := eulerProduct q bits p
  if which = 2 then
    let v := cmul (csqr w p) (cdiv (eulerProduct (csqr q p) (2 * bits) p) Pq p) p
    (mulFloatPrecRound v (AzFloat.sqrtPrecRound (fnat 2) p N').1 p p N' N').1
  else
    cdiv (cdiv (eulerProduct (if which = 0 then -h else h) (bits / 2) p) Pq p) w p

/-- The Weber invariant of the form `f` of discriminant `−D` (`D ≡ 7 (mod 8)`), cubed when
`cube`. -/
def weberValue (D : Nat) (cube : Bool) (f : RedForm) (p : Nat) : AzComplexFloat :=
  let a : Int := f.a
  let b : Int := f.b
  let c : Int := f.c
  let neg := (D + 1) / 8 % 2 == 1
  let u :=
    if f.a % 2 == 0 && f.c % 2 == 0 then
      cmul (zeta48 (b * (a - c - a * c * c)) p) (weberFn 0 D f.a f.b p) p
    else if f.a % 2 == 0 then
      let v := cmul (zeta48 (b * (a - c - a * c * c)) p) (weberFn 1 D f.a f.b p) p
      if neg then -v else v
    else
      let v := cmul (zeta48 (b * (a - c + a * a * c)) p) (weberFn 2 D f.a f.b p) p
      if neg then -v else v
  if cube then cmul u (csqr u p) p else u

/-- The precision to start from for the Weber polynomial of `−D`. -/
def weberBits (D : Nat) : Nat :=
  classPolyBits D / (if D % 3 = 0 then 16 else 48) + 4 * classNumber D + 64

/-- **The Weber class polynomial** of `−D`, `D ≡ 7 (mod 8)`: the integer coefficients,
constant term first, of the polynomial whose roots are the Weber invariants of the forms
(their cubes when `3 ∣ D`).  `none` for other `D`, or if three precisions fail. -/
def weberClassPoly (D : Nat) : Option (List AzInt) :=
  (weberKind D).bind fun k =>
    retry3 (weberBits D) fun p =>
      (formsPoly (reducedForms D) (fun f => weberValue D (k == 3) f p) p).mapM nearInteger?

/-! ### The factor of `H_{−D}` over the genus field

Let `−D = d₁ ⋯ d_t` be the factorization into prime discriminants.  The classes of forms fall
into `2^(t−1)` genera (the values of the characters `χ_{dᵢ}`), and the product of `X − j` over
one genus has its coefficients in the real subfield of the genus field
`ℚ(√d₁, …, √d_t)`: `H_{−D}` splits there into `2^(t−1)` conjugate factors of degree
`h / 2^(t−1)`.  A coefficient is `2^(−t) ∑_S A_S ρ_S` with integers `A_S`, over the sets `S`
of prime discriminants with positive product, `ρ_S = ∏_{i ∈ S} √dᵢ`; the class of a genus `σ`
acts on `ρ_S` by the sign `χ_S(σ) = ∏_{i ∈ S} χ_{dᵢ}(σ)`, so the `A_S` are recovered from the
`2^(t−1)` real factors: `A_S ρ_S = 2 ∑_σ χ_S(σ) c_σ`.  Modulo an `n` that splits in the class
field, the square roots of the `dᵢ` modulo `n` give the factor modulo `n`, and a root of it
is a root of `H_{−D}` — found in a ring of a `2^(t−1)` times smaller degree. -/

/-- The value `±1` of the genus character of the prime discriminant `d` on a form of
discriminant `−D` (`d` one of the prime discriminants of `−D`). -/
def genusChar (d : Int) (f : RedForm) : Int :=
  if d % 2 != 0 then
    let p := d.natAbs
    let m := if f.a % p != 0 then f.a else f.c
    if (List.range p).any fun x => x * x % p == m % p then 1 else -1
  else
    let m := if f.a % 2 == 1 then f.a else f.c
    if d == -4 then (if m % 4 == 1 then 1 else -1)
    else if d == 8 then (if m % 8 == 1 || m % 8 == 7 then 1 else -1)
    else (if m % 8 == 1 || m % 8 == 3 then 1 else -1)

/-- The subsets (as lists of flags) of the prime discriminants whose product is positive,
the empty one first. -/
def positiveSubsets (ds : List Int) : List (List Bool) :=
  let t := ds.length
  ((List.range (2 ^ t)).map fun mask => (List.range t).map fun i => mask / 2 ^ i % 2 == 1).filter
    fun S => ((ds.zip S).filter fun x => x.2 && x.1 < 0).length % 2 == 0

/-- **A factor of `H_{−D}` over the genus field**: the prime discriminants `dᵢ`, and for
every set `S` of them with positive product the integers `A_S(k)` (constant term first);
coefficient `k` of the factor is `2^(−t) ∑_S A_S(k) ∏_{i ∈ S} √dᵢ`. -/
structure GenusPoly where
  ds : List Int
  terms : List (List Bool × List AzInt)

/-- The genus factor for the invariant `inv` at precision `p`, if every `A_S(k)` comes out
near an integer. -/
def genusPolyAt (inv : RedForm → AzComplexFloat) (D p : Nat) : Option GenusPoly := do
  let ds := primeDiscriminants D
  let forms := reducedForms D
  let keyOf (f : RedForm) : List Int := ds.map fun d => genusChar d f
  let keys := (forms.map keyOf).eraseDups
  -- the real factor of every genus
  let factors : List (List Int × List AzFloat) := keys.map fun key =>
    (key, formsPoly (forms.filter fun f => keyOf f == key) inv p)
  let len := (factors.headD ([], [])).2.length
  if factors.any fun x => x.2.length != len then none
  let terms ← (positiveSubsets ds).mapM fun S => do
    let sel := (ds.zip S).filter (·.2)
    let dS : Nat := sel.foldl (fun acc x => acc * x.1.natAbs) 1
    let negs := (sel.filter fun x => x.1 < 0).length
    let root := (AzFloat.sqrtPrecRound (fnat dS) p N').1
    let coeffs ← (List.range len).mapM fun k =>
      let sum := factors.foldl (fun acc x =>
        let chi := (x.1.zip S).foldl (fun s y => if y.2 then s * y.1 else s) (1 : Int)
        let c := x.2.getD k AzFloat.zero
        if chi == 1 then fadd acc c p else fsub acc c p) AzFloat.zero
      let v := fdiv (sum <<< AzInt.ofInt 1) root p
      nearInteger? (if negs / 2 % 2 == 1 then -v else v)
    pure (S, coeffs)
  pure ⟨ds, terms⟩

/-- **The factor of `H_{−D}` over the genus field** (`none` if three precisions fail, or if
`−D` is a prime discriminant: then the factor is `H_{−D}` itself). -/
def genusClassPoly (D : Nat) : Option GenusPoly :=
  if (primeDiscriminants D).length < 2 then none
  else
    retry3 (classPolyBits D + 4 * classNumber D + 64 + 8 * (primeDiscriminants D).length)
      fun p => genusPolyAt (fun f => jOfForm D f.a f.b p) D p

/-- **The factor of the Weber class polynomial over the genus field** (`none` as for
`genusClassPoly`, or when `−D` has no Weber polynomial here). -/
def genusWeberPoly (D : Nat) : Option GenusPoly :=
  if (primeDiscriminants D).length < 2 then none
  else
    (weberKind D).bind fun k =>
      retry3 (weberBits D + 8 * (primeDiscriminants D).length)
        fun p => genusPolyAt (fun f => weberValue D (k == 3) f p) D p

end Azurite.ECPP
