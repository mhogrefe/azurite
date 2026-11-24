/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Mul
import Azurite.AzZMod.Instances
import Azurite.AzNat.Kronecker
import Azurite.AzNat.LogBase2
import Azurite.AzNat.Instances
import Azurite.AzNat.Pow2
import Azurite.AzInt.Instances
import Azurite.AzInt.Conversion

/-!
# Polynomial multiplication over `ℤ/m` by Kronecker substitution

`mulKronecker p q` packs the residues of each factor into one number, `w` limbs apart
(`AzNat.kroneckerPack`), multiplies the two numbers with `AzNat`'s multiplication and reads
the coefficients of the product back, reducing each modulo `m`.  The width `w` is chosen so
that a coefficient of the product of the lifts — a sum of at most `min (len p) (len q)`
products of residues — stays below `2^(64 w)`.  One large product instead of
`len p · len q` modular ones; correctness is `Equiv/Kronecker.lean`.
-/

namespace Azurite.AzPolynomial

/-- Limbs per coefficient for a product with `n` coefficients in all in the two factors:
`2^(64 w) > n · m²`. -/
def kroneckerWidth (m : AzNat) (n : Nat) : Nat :=
  (2 * m.size + n.log2 + 1 + 63) / 64

/-- **Multiplication over `ℤ/m` by Kronecker substitution.** -/
def mulKronecker {m : AzNat} [NeZero m.toNat] (p q : AzPolynomial (AzZMod m)) :
    AzPolynomial (AzZMod m) :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else
    let w := kroneckerWidth m (p.coeffs.size + q.coeffs.size)
    let x := AzNat.kroneckerPack w (p.coeffs.map (·.val)) *
      AzNat.kroneckerPack w (q.coeffs.map (·.val))
    normalize <| Array.ofFn fun (k : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      AzZMod.ofAzNat m (AzNat.kroneckerCoeff w x k.val)

/-! ### Natural-number coefficients

The width comes from the data: with `s₁`, `s₂` the largest limb counts of the coefficients, a
coefficient of the product is below `n · 2^(64 (s₁ + s₂))`. -/

/-- **Multiplication over `AzNat` by Kronecker substitution.** -/
def mulKroneckerNat (p q : AzPolynomial AzNat) : AzPolynomial AzNat :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else
    let w := AzNat.maxLimbs p.coeffs + AzNat.maxLimbs q.coeffs +
      ((p.coeffs.size + q.coeffs.size).log2 + 1 + 63) / 64
    let x := AzNat.kroneckerPack w p.coeffs * AzNat.kroneckerPack w q.coeffs
    normalize <| Array.ofFn fun (k : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      AzNat.kroneckerCoeff w x k.val

/-! ### Integer coefficients

A polynomial with signed coefficients is packed as the difference of two packed numbers (its
positive and its negative coefficients), so that the product of the two signed numbers is
the value of the product at `2^(64 w)`.  Adding `∑ₖ 2^(64 w − 1) · 2^(64 w k)` makes every
block nonnegative; each coefficient is its block minus `2^(64 w − 1)`. -/

/-- The nonnegative coefficients (zero in place of the others). -/
def posParts (a : Array AzInt) : Array AzNat :=
  a.map fun c => if c.sign then c.abs else 0

/-- The absolute values of the negative coefficients (zero in place of the others). -/
def negParts (a : Array AzInt) : Array AzNat :=
  a.map fun c => if c.sign then 0 else c.abs

/-- `∑ aᵢ · 2^(64 w i)` for signed coefficients of absolute value below `2^(64 w)`. -/
def kroneckerPackInt (w : Nat) (a : Array AzInt) : AzInt :=
  (AzNat.kroneckerPack w (posParts a)).toAzInt - (AzNat.kroneckerPack w (negParts a)).toAzInt

/-- **Multiplication over `AzInt` by Kronecker substitution.** -/
def mulKroneckerInt (p q : AzPolynomial AzInt) : AzPolynomial AzInt :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else
    let w := AzNat.maxLimbs (p.coeffs.map (·.abs)) + AzNat.maxLimbs (q.coeffs.map (·.abs)) +
      ((p.coeffs.size + q.coeffs.size).log2 + 2 + 63) / 64
    let half := AzNat.pow2 (64 * w - 1)
    let off := AzNat.kroneckerPack w (Array.replicate (p.coeffs.size + q.coeffs.size - 1) half)
    let y := (kroneckerPackInt w p.coeffs * kroneckerPackInt w q.coeffs + off.toAzInt).abs
    normalize <| Array.ofFn fun (k : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      (AzNat.kroneckerCoeff w y k.val).toAzInt - half.toAzInt

/-! ### When to use it

Measured with `benchmark poly_kronecker` (2026-11-23).  Over `AzZMod m` the reductions of
the schoolbook product dominate and Kronecker wins from three coefficients on at every
modulus size.  Over `AzInt` and `AzNat` there is nothing to save but the multiplications,
so it wins only when the factors are long compared with their coefficients, and only when
the coefficients are of similar size (the width is set by the largest). -/

/-- Half of the blocks or more are filled: `2 · (total limbs) ≥ len · s`. -/
def kroneckerDense (a : Array AzNat) (s : Nat) : Bool :=
  decide (a.size * s ≤ 2 * AzNat.sumLimbs a)

/-- Use Kronecker substitution over `AzNat`: the shorter factor has at least `4 s + 4`
coefficients, for `s` the largest limb count, and both factors are dense. -/
def useKroneckerNat (p q : AzPolynomial AzNat) : Bool :=
  let s := max (AzNat.maxLimbs p.coeffs) (AzNat.maxLimbs q.coeffs)
  decide (4 * s + 4 ≤ min p.coeffs.size q.coeffs.size) &&
    kroneckerDense p.coeffs s && kroneckerDense q.coeffs s

/-- Use Kronecker substitution over `AzInt`: coefficients of at most four limbs, the shorter
factor has at least `8 s` coefficients, and both factors are dense. -/
def useKroneckerInt (p q : AzPolynomial AzInt) : Bool :=
  let a := p.coeffs.map (·.abs)
  let b := q.coeffs.map (·.abs)
  let s := max (AzNat.maxLimbs a) (AzNat.maxLimbs b)
  decide (1 ≤ s) && decide (s ≤ 4) && decide (8 * s ≤ min a.size b.size) &&
    kroneckerDense a s && kroneckerDense b s

-- ── Tests ───────────────────────────────────────────────────────────────────

/-- A polynomial with `len` coefficients modulo `m` (test data). -/
private def testPoly (m : AzNat) [NeZero m.toNat] (len seed : Nat) : AzPolynomial (AzZMod m) :=
  normalize <| (Array.range len).map fun i =>
    AzZMod.ofAzNat m (AzNat.ofNat ((1000003 + seed) ^ (i + 3) + i * i + seed))

/-- `mulKronecker` against the schoolbook product on factors of `a` and `b` coefficients. -/
private def agrees (m a b : Nat) : Bool :=
  if h : m ≠ 0 then
    haveI : NeZero m := ⟨h⟩
    let p := testPoly (AzNat.ofNat m) a 1
    let q := testPoly (AzNat.ofNat m) b 2
    decide (mulKronecker p q = mulBasecaseFold p q)
  else false

#guard agrees 7 5 9
#guard agrees 2 6 6
#guard agrees 1 3 4
#guard agrees 65537 1 12
#guard agrees 65537 12 12
#guard agrees (2 ^ 64 - 59) 7 20
#guard agrees (2 ^ 64) 9 9
#guard agrees (2 ^ 127 - 1) 16 5
#guard agrees (2 ^ 521 - 1) 10 10
#guard mulKronecker (0 : AzPolynomial (AzZMod (AzNat.ofNat 7))) (testPoly _ 4 1) = 0
-- the largest residues: every coefficient of the product of the lifts is `len · (m − 1)²`
#guard
  let m := AzNat.ofNat (2 ^ 64)
  let p : AzPolynomial (AzZMod m) :=
    normalize ((Array.range 40).map fun _ => AzZMod.ofAzNat m (AzNat.ofNat (2 ^ 64 - 1)))
  decide (mulKronecker p p = mulBasecaseFold p p)

/-- Test data over `AzNat` and `AzInt`. -/
private def testNat (len seed : Nat) : AzPolynomial AzNat :=
  normalize <| (Array.range len).map fun i =>
    AzNat.ofNat (((1000003 + seed) ^ (i % 7 + 1) + i * i + seed) % (10 ^ (3 + 5 * (i % 9))))

private def testInt (len seed : Nat) : AzPolynomial AzInt :=
  normalize <| (Array.range len).map fun i =>
    let c := (AzNat.ofNat (((1000003 + seed) ^ (i % 7 + 1) + i * i + seed) %
      (10 ^ (3 + 5 * (i % 9))))).toAzInt
    if (i + seed) % 3 == 0 then -c else c

#guard mulKroneckerNat (testNat 5 1) (testNat 9 2) = mulBasecaseFold (testNat 5 1) (testNat 9 2)
#guard mulKroneckerNat (testNat 1 1) (testNat 30 2) = mulBasecaseFold (testNat 1 1) (testNat 30 2)
#guard mulKroneckerNat (testNat 40 3) (testNat 40 4) =
  mulBasecaseFold (testNat 40 3) (testNat 40 4)
#guard mulKroneckerNat 0 (testNat 4 1) = 0
#guard mulKroneckerInt (testInt 5 1) (testInt 9 2) = mulBasecaseFold (testInt 5 1) (testInt 9 2)
#guard mulKroneckerInt (testInt 1 1) (testInt 30 2) = mulBasecaseFold (testInt 1 1) (testInt 30 2)
#guard mulKroneckerInt (testInt 40 3) (testInt 40 4) =
  mulBasecaseFold (testInt 40 3) (testInt 40 4)
#guard mulKroneckerInt (testInt 12 5) (testInt 12 5) =
  mulBasecaseFold (testInt 12 5) (testInt 12 5)
#guard mulKroneckerInt (testInt 4 1) 0 = 0
-- extreme coefficients `±(2^64 − 1)`: the blocks reach both ends of their range
#guard
  let c := (AzNat.ofNat (2 ^ 64 - 1)).toAzInt
  let p : AzPolynomial AzInt := normalize ((Array.range 33).map fun _ => c)
  let q : AzPolynomial AzInt := normalize ((Array.range 33).map fun _ => -c)
  mulKroneckerInt p q = mulBasecaseFold p q && mulKroneckerInt p p = mulBasecaseFold p p &&
    mulKroneckerInt q q = mulBasecaseFold q q

end Azurite.AzPolynomial
