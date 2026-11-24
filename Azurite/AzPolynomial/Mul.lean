/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

import Mathlib.Algebra.Polynomial.Coeff
open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Original O(n^2) multiplication using List.range.map.sum.
    Allocates an intermediate list per output coefficient.
    Kept for comparison with the optimized version. -/
def mulBasecaseList (p q : AzPolynomial R) : AzPolynomial R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    (List.range (n.val + 1)).map (fun i => p.coeff i * q.coeff (n.val - i)) |>.sum
  )

/-- Optimized O(n^2) multiplication using Finset.sum over range.
    Avoids allocating intermediate lists per output coefficient. -/
def mulBasecase (p q : AzPolynomial R) : AzPolynomial R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    ∑ i ∈ Finset.range (n.val + 1), p.coeff i * q.coeff (n.val - i)
  )

/-- O(n^2) basecase convolution on raw coefficient arrays using Fin.foldl.
    Produces an un-normalized array of product coefficients.
    Shared by `mulBasecaseFold` and `mulKaratsuba`. -/
def mulBasecaseCoeffs (a b : Array R) : Array R :=
  if a.size == 0 || b.size == 0 then #[]
  else Array.ofFn (fun (n : Fin (a.size + b.size - 1)) =>
    Fin.foldl (n.val + 1) (fun acc i =>
      acc + ((a[i.val]?).getD 0) * ((b[n.val - i.val]?).getD 0)) 0)

/-- O(n^2) multiplication using Fin.foldl — a direct accumulating fold with
    no intermediate data structures (no List, no Finset/Multiset wrapper). -/
def mulBasecaseFold (p q : AzPolynomial R) : AzPolynomial R :=
  normalize (mulBasecaseCoeffs p.coeffs q.coeffs)

-- ── Multiplication config typeclass ─────────────────────────────────────────

/-- **The multiplication of `AzPolynomial R`**: an implementation `dmul` together with the
    proof that it is the schoolbook product (`dmul_eq`).  The `*` of `AzPolynomial R` — and
    with it the ring structure — is `dmul`, so the algorithm is chosen by the coefficient
    type, and every statement about `*` holds for whichever algorithm that is.

    Each coefficient type has exactly one instance (there is no generic default, so that
    code generic in `R` cannot silently fix an algorithm): the tuned ones for `AzInt`,
    `AzNat`, `AzRat`, `AzZMod m` are in `FastMul.lean`; `basecase` and (in `FastMul.lean`)
    `karatsuba` are ready-made values for other types.

    Code and statements generic in `R` take `[AzPolynomialMulConfig R]`. -/
class AzPolynomialMulConfig (R : Type _) [Semiring R] [DecidableEq R] where
  /-- The multiplication implementation. -/
  dmul : AzPolynomial R → AzPolynomial R → AzPolynomial R
  /-- It is the schoolbook product. -/
  dmul_eq : ∀ p q, dmul p q = mulBasecaseFold p q

/-- The schoolbook product as a multiplication config, for coefficient types without a tuned
    one: `instance : AzPolynomialMulConfig T := .basecase`. -/
@[reducible] def AzPolynomialMulConfig.basecase : AzPolynomialMulConfig R where
  dmul := mulBasecaseFold
  dmul_eq _ _ := rfl

/-- Multiplies two `AzPolynomial`s by the algorithm of the coefficient type `R`
    (`AzPolynomialMulConfig`). -/
def mul [AzPolynomialMulConfig R] (p q : AzPolynomial R) : AzPolynomial R :=
  AzPolynomialMulConfig.dmul p q

instance [AzPolynomialMulConfig R] : Mul (AzPolynomial R) := ⟨mul⟩

/-- `*` is the schoolbook product, whatever the algorithm. -/
theorem mul_eq_mulBasecaseFold [AzPolynomialMulConfig R] (p q : AzPolynomial R) :
    p * q = mulBasecaseFold p q :=
  AzPolynomialMulConfig.dmul_eq p q

/-- Polynomials over polynomials: the schoolbook product. -/
instance [Semiring (AzPolynomial R)] : AzPolynomialMulConfig (AzPolynomial R) := .basecase

-- Verify old implementation still works
#guard toChars (mulBasecaseList (parseAzPolynomial (R := AzInt) "x+1").get! (parseAzPolynomial (R := AzInt) "x+2").get!) == "x^2+3*x+2"

-- Verify fold implementation works
#guard toChars (mulBasecaseFold (parseAzPolynomial (R := AzInt) "x+1").get! (parseAzPolynomial (R := AzInt) "x+2").get!) == "x^2+3*x+2"

-- `AzPolynomial AzRat` round-trips through strings (rational coefficients render
-- as `"3/2"`, `-1` coefficients as `"-x"`).  (Relocated from `ParsableCoeff/AzRat`.)
#guard (parseAzPolynomial "3/2*x^2-1/3*x+5" :
    Option (AzPolynomial AzRat)).map toChars == some "3/2*x^2-1/3*x+5"
#guard (parseAzPolynomial "x^2-x-1/2" :
    Option (AzPolynomial AzRat)).map toChars == some "x^2-x-1/2"

end Azurite.AzPolynomial
