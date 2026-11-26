/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.Karatsuba
import Azurite.AzPolynomial.Equiv.Kronecker
import Azurite.AzPolynomial.Equiv.KroneckerInt
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Pow

/-!
# The multiplications of `AzPolynomial`, by coefficient type

The instances of `AzPolynomialMulConfig`: for each coefficient type the algorithm that `*`
on `AzPolynomial` uses, with the proof that it is the schoolbook product (the class's law
`dmul_eq`).  A file that multiplies polynomials over one of these types imports this file.

* `AzInt`: Kronecker substitution for long factors with small coefficients
  (`useKroneckerInt`), else Karatsuba with threshold 29;
* `AzNat`: Kronecker substitution for long factors (`useKroneckerNat`), else schoolbook;
* `AzRat`: Karatsuba with threshold 14;
* `AzZMod m`: Kronecker substitution from `kroneckerThreshold` coefficients on;
* `ℤ`, `ℚ`: Karatsuba with the default threshold.

Only `AzZMod m` sets `invThreshold` (powers in `AzPolyMod` reducing by a precomputed inverse).
Over `AzInt` and `AzRat` the coefficients of a power are not reduced and the inverse has large
coefficients of its own; measured 2026-11-24 (`benchmark poly_default 1 "inv:1"`, degrees 8–64,
exponents 8 and 64), the inverse-based power is 1.1–1.7 times slower over `AzInt` and 1.2–1.4
times slower over `AzRat`, so they keep the default `none`.

Every instance starts with a test on the sizes alone and takes the schoolbook product for
short factors, so that the kernel can still evaluate small products (`decide`, `rfl`): the
other algorithms are defined by well-founded recursion.

For another coefficient type, `instance : AzPolynomialMulConfig T := .basecase` or
`.karatsuba`.
-/

namespace Azurite.AzPolynomial

/-- An array-backed polynomial with the product's value is the schoolbook product. -/
theorem eq_mulBasecaseFold_of_toPoly {R : Type _} [Semiring R] [DecidableEq R]
    {x p q : AzPolynomial R}
    (h : AzPolynomial.toPoly x = AzPolynomial.toPoly p * AzPolynomial.toPoly q) :
    x = mulBasecaseFold p q :=
  toPoly_inj.mp (by rw [h, toPoly_mulBasecaseFold])

/-- Karatsuba multiplication with threshold `t` (schoolbook when both factors are shorter
than `t`) as a multiplication config, for any `CommRing`. -/
@[reducible] def AzPolynomialMulConfig.karatsubaWith {R : Type _} [CommRing R] [DecidableEq R]
    (t : Nat) : AzPolynomialMulConfig R where
  dmul p q :=
    if p.coeffs.size < t ∧ q.coeffs.size < t then mulBasecaseFold p q
    else mulKaratsubaWithThreshold t p q
  dmul_eq p q := by
    split
    · rfl
    · exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKaratsubaWithThreshold _ _ _)

/-- Karatsuba multiplication with the default threshold as a multiplication config. -/
@[reducible] def AzPolynomialMulConfig.karatsuba {R : Type _} [CommRing R] [DecidableEq R] :
    AzPolynomialMulConfig R := .karatsubaWith karatsubaThreshold

/-- Multiplication for `AzInt`: Kronecker substitution for long factors with small
coefficients of similar size (`useKroneckerInt`), else Karatsuba with threshold 29;
schoolbook when a factor has fewer than 8 coefficients. -/
instance : AzPolynomialMulConfig AzInt where
  dmul p q :=
    if p.coeffs.size < 8 ∨ q.coeffs.size < 8 then mulBasecaseFold p q
    else if useKroneckerInt p q then mulKroneckerInt p q
    else mulKaratsubaWithThreshold 29 p q
  dmul_eq p q := by
    split
    · rfl
    · split
      · exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKroneckerInt p q)
      · exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKaratsubaWithThreshold _ p q)

/-- Multiplication for `AzNat`: Kronecker substitution for long factors with coefficients of
similar size (`useKroneckerNat`), else the schoolbook product. -/
instance : AzPolynomialMulConfig AzNat where
  dmul p q :=
    if p.coeffs.size < 8 ∨ q.coeffs.size < 8 then mulBasecaseFold p q
    else if useKroneckerNat p q then mulKroneckerNat p q
    else mulBasecaseFold p q
  dmul_eq p q := by
    split
    · rfl
    · split
      · exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKroneckerNat p q)
      · rfl

/-- Karatsuba multiplication for `AzRat`, threshold tuned to 14. -/
instance : AzPolynomialMulConfig AzRat := .karatsubaWith 14

/-- Below this many coefficients in the shorter factor, multiplication over `AzZMod m` is
the schoolbook product; from it on it is Kronecker substitution. -/
def kroneckerThreshold : Nat := 3

/-- Multiplication for `AzZMod m`: Kronecker substitution when both factors have at least
`kroneckerThreshold` coefficients — at two points (two `AzNat` products of half the size)
when `useKronecker2`, else at one point (one large `AzNat` product) — else the schoolbook
product.  Both Kronecker products square the packed numbers when the factors are equal. -/
instance {m : AzNat} [NeZero m.toNat] : AzPolynomialMulConfig (AzZMod m) where
  dmul p q :=
    if p.coeffs.size < kroneckerThreshold ∨ q.coeffs.size < kroneckerThreshold then
      mulBasecaseFold p q
    else if useKronecker2 p q then mulKronecker2 p q
    else mulKronecker p q
  dmul_eq p q := by
    split
    · rfl
    · split
      · exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKronecker2 p q)
      · exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKronecker p q)
  -- measured 2026-11-24 (`benchmark poly_default 1 "parts:1"`): slower at degree 4, 1.2 times
  -- faster at degree 8, 1.4–1.7 at 16, 3.2–3.4 at 128
  invThreshold := some 9

/-- Karatsuba multiplication for Mathlib's `ℤ` and `ℚ`. -/
instance : AzPolynomialMulConfig ℤ := .karatsuba
instance : AzPolynomialMulConfig ℚ := .karatsuba

-- ── Tests ───────────────────────────────────────────────────────────────────

-- Testing the implementation using Integer polynomials
#guard toChars ((parseAzPolynomial (R := AzInt) "x+1").get! * (parseAzPolynomial (R := AzInt) "x+2").get!) == "x^2+3*x+2"
#guard toChars ((parseAzPolynomial (R := AzInt) "2*x^2+x").get! * (parseAzPolynomial (R := AzInt) "x-1").get!) == "2*x^3-x^2-x"
#guard toChars ((0 : AzPolynomial AzInt) * (parseAzPolynomial (R := AzInt) "x^2+1").get!) == "0"
#guard toChars ((parseAzPolynomial (R := AzInt) "3").get! * (parseAzPolynomial (R := AzInt) "4").get!) == "12"

-- (relocated from `Mul.lean`)
#guard ((· * ·) <$>
    (parseAzPolynomial "x-1/2" : Option (AzPolynomial AzRat)) <*>
    (parseAzPolynomial "x+1/2" : Option (AzPolynomial AzRat))).map
    toChars == some "x^2-1/4"

section PowTests

#guard toChars ((parseAzPolynomial (R := AzInt) "x+1").get!.pow 0) == "1"
#guard toChars ((parseAzPolynomial (R := AzInt) "x+1").get!.pow 1) == "x+1"
#guard toChars ((parseAzPolynomial (R := AzInt) "x+1").get!.pow 2) == "x^2+2*x+1"
#guard toChars ((parseAzPolynomial (R := AzInt) "x+1").get!.pow 3) == "x^3+3*x^2+3*x+1"
#guard toChars ((parseAzPolynomial (R := AzInt) "2*x").get!.pow 4) == "16*x^4"
#guard toChars ((0 : AzPolynomial AzInt).pow 5) == "0"
#guard toChars ((1 : AzPolynomial AzInt).pow 100) == "1"

end PowTests

#guard
  let p : AzPolynomial AzInt :=
    normalize ((Array.range 40).map fun (i : Nat) => AzInt.ofInt ((i : Int) * 37 - 500))
  useKroneckerInt p p && p * p = mulBasecaseFold p p && p ^ 3 = mulBasecaseFold p (p * p)
#guard
  let p : AzPolynomial AzInt :=
    normalize ((Array.range 5).map fun (i : Nat) => AzInt.ofInt ((i : Int) * 37 - 50))
  p * p = mulBasecaseFold p p
#guard
  let p : AzPolynomial AzNat :=
    normalize ((Array.range 40).map fun i => AzNat.ofNat (i * 37 + 5))
  useKroneckerNat p p && p * p = mulBasecaseFold p p
#guard
  let p : AzPolynomial (AzZMod (AzNat.ofNat 1000003)) :=
    normalize ((Array.range 20).map fun i => AzZMod.ofAzNat _ (AzNat.ofNat (i * i * 977 + 5)))
  p * p = mulBasecaseFold p p && p ^ 3 = mulBasecaseFold p (p * p)

end Azurite.AzPolynomial
