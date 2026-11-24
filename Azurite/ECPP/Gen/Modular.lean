/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Sqrt
import Azurite.AzZMod.Conversion
import Azurite.AzNat.JacobiSym
import Azurite.AzNat.SqrtRem
import Azurite.AzInt.ExtendedGcd
import Azurite.AzPolynomial.GcdOrFactor
import Azurite.AzPolyMod.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzNat.Kronecker

/-!
# Modular tools of the certificate generator

Unproven helpers (`docs/ecpp_plan.md`, layer 3) for a modulus `n` that is only a probable
prime.

* `AzZMod.inv?`: the inverse of a residue, or `none` when it is not a unit.
* `sqrtSmall? n d`: a square root of a small integer `d` modulo `n` (Jacobi symbol first).
* `cornacchia4 n D r`: a solution `(x, y)` of `x² + D y² = 4n` from a square root `r` of `−D`
  modulo `n` (the modified Cornacchia algorithm, Cohen, *A Course in Computational Algebraic
  Number Theory*, Algorithm 1.5.3).
* `trialDivide m primes`: the cofactor of `m` after removing the listed primes.
* `rootOfSplitPoly n h`: a root modulo `n` of a monic polynomial that splits into distinct
  linear factors, by the splitting `gcd((X + r)^((n−1)/2) − 1, ·)`.
-/

namespace Azurite

/-- The inverse of a residue modulo `m`, or `none` when it is not a unit. -/
def AzZMod.inv? {m : AzNat} [NeZero m.toNat] (a : AzZMod m) : Option (AzZMod m) :=
  let g := AzInt.egcd a.val m
  if g.1 = 1 then some (AzZMod.ofAzInt m g.2.1) else none

namespace ECPP

open AzZMod

variable {n : AzNat} [NeZero n.toNat]

/-- A small integer as a residue. -/
def resOfInt (n : AzNat) [NeZero n.toNat] (d : Int) : AzZMod n := ofAzInt n (AzInt.ofInt d)

/-- A square root of the small integer `d` modulo `n`, if the Jacobi symbol is `1` and the
root extraction succeeds. -/
def sqrtSmall? (n : AzNat) [NeZero n.toNat] (d : Int) : Option (AzZMod n) :=
  let r := resOfInt n d
  if AzNat.jacobi r.val n = 1 then AzZMod.sqrt? r else none

/-- **Cornacchia for `x² + D y² = 4n`** (`n` odd), from `r` with `r² ≡ −D (mod n)`. -/
def cornacchia4 (n : AzNat) (D : Nat) (r : AzNat) : Option (AzNat × AzNat) := Id.run do
  let x₀ := if r.testBit 0 == (D % 2 == 1) then r else n - r
  let n4 := n.shiftLeft 2
  let l := AzNat.sqrt n4
  let mut a := n.shiftLeft 1
  let mut b := x₀
  for _ in [0:2 * n.size + 4] do
    if b ≤ l then break
    let t := a % b
    a := b
    b := t
  let t := n4 - b * b
  let d := AzNat.ofNat D
  if t % d ≠ 0 then return none
  let c := t / d
  let s := AzNat.sqrt c
  if s * s = c then return some (b, s) else return none

/-- The primes below `B` (a small sieve). -/
def smallPrimes (B : Nat) : List Nat := Id.run do
  let mut sieve := Array.replicate (B + 1) true
  let mut out : Array Nat := #[]
  for p in [2:B] do
    if sieve[p]! then
      out := out.push p
      for k in [1:B / p + 1] do
        sieve := sieve.set! (k * p) false
  return out.toList

/-- Remove from `m` all the factors in `primes`: `(cofactor, removed part)`. -/
def trialDivide (m : AzNat) (primes : List Nat) : AzNat × AzNat := Id.run do
  let mut q := m
  let mut c : AzNat := 1
  for p in primes do
    let pa := AzNat.ofNat p
    for _ in [0:m.size] do
      if q % pa ≠ 0 then break
      q := q / pa
      c := c * pa
  return (q, c)

/-- A polynomial over `ℤ/n` from integer coefficients (constant term first). -/
def polyOfInts (n : AzNat) [NeZero n.toNat] (c : List AzInt) : AzPolynomial (AzZMod n) :=
  AzPolynomial.normalize (c.map (ofAzInt n)).toArray

/-! ### Powers modulo a polynomial by packed multiplication

The splitting needs `(X + r)^((n − 1)/2)` modulo a monic `g` of degree `d` over `ℤ/n`.  A
product of two residues of degree below `d` is one multiplication of large numbers (the
coefficients packed `w` limbs apart, `AzNat.kroneckerPack`), and so is each of the two
products of the reduction modulo `g` (the quotient from the precomputed inverse of the
reversed `g` as a power series, then `q · g`). -/

/-- The first `k` coefficients of a packed number (`AzNat.kroneckerPack`), each reduced
modulo `n`. -/
def unpackCoeffs (n : AzNat) (w k : Nat) (x : AzNat) : Array AzNat :=
  (Array.range k).map fun i => AzNat.kroneckerCoeff w x i % n

/-- The data for arithmetic modulo `n` and a monic `g` of degree `d ≥ 2`: the low
coefficients of `g`, `g` packed, and the packed inverse of the reversed `g` modulo
`X^(d − 1)`. -/
structure PackedMod where
  n : AzNat
  d : Nat
  w : Nat
  g : Array AzNat
  gPacked : AzNat
  invPacked : AzNat

/-- Set up `PackedMod` from the low coefficients `g₀, …, g_(d−1)` of a monic `g`. -/
def PackedMod.make (n : AzNat) (g : Array AzNat) : PackedMod := Id.run do
  let d := g.size
  let w := (2 * n.size + d.log2 + 1 + 63) / 64
  -- reversed `g`: coefficient `i` is `g_(d − i)`
  let rev (i : Nat) : AzNat := if i = 0 then (1 : AzNat) else g[d - i]!
  let mut inv : Array AzNat := #[1]
  for k in [1:d - 1] do
    let mut s : AzNat := 0
    for i in [1:k + 1] do
      s := s + rev i * inv[k - i]!
    inv := inv.push ((n - s % n) % n)
  return ⟨n, d, w, g, AzNat.kroneckerPack w (g.push 1), AzNat.kroneckerPack w inv⟩

/-- Reduce a packed product of two residues (degree at most `2d − 2`) modulo `g`. -/
def PackedMod.reduce (M : PackedMod) (prod : AzNat) : Array AzNat :=
  let d := M.d
  let p := unpackCoeffs M.n M.w (2 * d - 1) prod
  let hi := (Array.range (d - 1)).map fun i => p[2 * d - 2 - i]!
  let qr := unpackCoeffs M.n M.w (d - 1) (AzNat.kroneckerPack M.w hi * M.invPacked)
  let qg := unpackCoeffs M.n M.w d (AzNat.kroneckerPack M.w qr.reverse * M.gPacked)
  (Array.range d).map fun i =>
    let a := p[i]!
    let b := qg[i]!
    if b ≤ a then a - b else a + M.n - b

def PackedMod.sqr (M : PackedMod) (a : Array AzNat) : Array AzNat :=
  M.reduce (AzNat.square (AzNat.kroneckerPack M.w a))

/-- Multiply a residue by `X + r`. -/
def PackedMod.mulLinear (M : PackedMod) (r : AzNat) (a : Array AzNat) : Array AzNat :=
  let top := a[M.d - 1]!
  (Array.range M.d).map fun i =>
    let lo : AzNat := if i = 0 then 0 else a[i - 1]!
    (lo + r * a[i]! + top * (M.n - M.g[i]!)) % M.n

/-- `(X + r)^e` modulo `g`, for `e ≥ 1`. -/
def PackedMod.powLinear (M : PackedMod) (r e : AzNat) : Array AzNat := Id.run do
  let one : Array AzNat := (Array.range M.d).map fun i => if i = 0 then (1 : AzNat) else 0
  let mut acc := M.mulLinear r one
  let bits := e.size
  for j in [1:bits] do
    acc := M.sqr acc
    if e.testBit (bits - 1 - j) then acc := M.mulLinear r acc
  return acc

/-- **A root modulo `n`** of a monic polynomial that splits into distinct linear factors
(as a class polynomial does modulo a prime that splits completely): repeated splitting by
`gcd((X + r)^((n − 1)/2) − 1, ·)`. -/
def rootOfSplitPoly (n : AzNat) [NeZero n.toNat] (h : AzPolynomial (AzZMod n)) :
    Option (AzZMod n) := Id.run do
  let e := (n - 1).shiftRight 1
  let mut g := h
  let mut r : Nat := 0
  for _ in [0:64 + 8 * h.natDegree] do
    if g.natDegree ≤ 1 then break
    r := r + 1
    let dg := g.natDegree
    let M := PackedMod.make n ((Array.range dg).map fun i => (g.coeff i).val)
    let pw := M.powLinear (AzNat.ofNat r) e
    let t : AzPolynomial (AzZMod n) := AzPolynomial.normalize (pw.map (ofAzNat n)) - 1
    match AzPolynomial.gcdOrFactor n t g with
    | .inl _ => return none
    | .inr d =>
      if 0 < d.natDegree ∧ d.natDegree < g.natDegree then
        g := if 2 * d.natDegree ≤ g.natDegree then d else AzPolynomial.divByMonic g d
  if g.natDegree = 1 then
    -- `g = X + c₀` up to its leading coefficient
    match (g.coeff 1).inv? with
    | some li => return some (-(g.coeff 0 * li))
    | none => return none
  else return none

end ECPP

end Azurite
