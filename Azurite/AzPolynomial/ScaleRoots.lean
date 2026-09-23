/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

/-!
# Root Scaling

Multiplies the roots of `P ∈ R[X]` by a fraction `b / c` of ring elements without
leaving `R[X]`: the coefficient of `X^i` becomes `aᵢ · c^i · b^(deg P − i)`, so
that (over the fraction field, for `b, c ≠ 0`) the result is
`b^(deg P) · P(c·X / b)`, whose roots are `(b/c)·r` for the roots `r` of `P`.

The one-element scalings are the special cases: `scaleRoots p b 1` multiplies the
roots by `b` (Mathlib's `Polynomial.scaleRoots` direction), and
`scaleRoots p 1 c` divides them by `c` (the substitution `X ↦ c·X`).

Implemented by two O(n) passes of a single carried-power map
(`scaleRootsAux`, applied once forward for `c^i` and once reversed for
`b^(deg P − i)`), so every power is computed exactly once; a final `normalize`
strips trailing zeros (the leading coefficient becomes `aₚ·c^p`, which can vanish
when `c = 0` or `c` is a zero divisor).

## Main definitions

- `AzPolynomial.scaleRoots p b c` — multiplies the roots by `b / c`

The coefficient formula `coeff_scaleRoots` is proved here; the `toPoly` bridge,
the root-scaling property, and the degree data live in `Equiv/ScaleRoots.lean`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Multiply the `i`-th element of a list by `k · c^i`, carrying the power (one
ring multiplication per element for the power, one for the coefficient). -/
def scaleRootsAux (c : R) : R → List R → List R
  | _, [] => []
  | k, a :: t => a * k :: scaleRootsAux c (k * c) t

omit [DecidableEq R] in
theorem scaleRootsAux_length (c : R) : ∀ (k : R) (l : List R),
    (scaleRootsAux c k l).length = l.length
  | _, [] => rfl
  | k, a :: t => by simp [scaleRootsAux, scaleRootsAux_length c (k * c) t]

omit [DecidableEq R] in
theorem scaleRootsAux_getD (c : R) : ∀ (l : List R) (k : R) (i : ℕ),
    (scaleRootsAux c k l).getD i 0 = l.getD i 0 * (k * c ^ i)
  | [], k, i => by simp [scaleRootsAux]
  | a :: t, k, 0 => by simp [scaleRootsAux]
  | a :: t, k, (i + 1) => by
    simp only [scaleRootsAux, List.getD_cons_succ]
    rw [scaleRootsAux_getD c t (k * c) i, pow_succ', mul_assoc]

/-- **Root scaling.** Multiplies the roots by `b / c`: the coefficient of `X^i`
becomes `aᵢ · c^i · b^(deg P − i)`. The `c`-powers are applied by a forward pass
and the `b`-powers by a reversed pass of `scaleRootsAux`. -/
def scaleRoots (p : AzPolynomial R) (b c : R) : AzPolynomial R :=
  normalize (((scaleRootsAux b 1 ((scaleRootsAux c 1 p.coeffs.toList).reverse)).reverse).toArray)

/-- The coefficient formula: `(scaleRoots p b c).coeff i = aᵢ · c^i · b^(deg P − i)`. -/
@[simp] theorem coeff_scaleRoots (p : AzPolynomial R) (b c : R) (i : ℕ) :
    (p.scaleRoots b c).coeff i = p.coeff i * c ^ i * b ^ (p.natDegree - i) := by
  rw [scaleRoots, coeff_normalize]
  set L := p.coeffs.toList with hL
  set M := (scaleRootsAux c 1 L).reverse with hM
  have hlenM : M.length = L.length := by rw [hM, List.length_reverse, scaleRootsAux_length]
  rw [List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  by_cases hi : i < L.length
  · have h1 : ((scaleRootsAux b 1 M).reverse).getD i 0
        = (scaleRootsAux b 1 M).getD (L.length - 1 - i) 0 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_reverse (by rw [scaleRootsAux_length, hlenM]; exact hi),
        scaleRootsAux_length, hlenM, ← List.getD_eq_getElem?_getD]
    rw [h1, scaleRootsAux_getD, one_mul]
    have h2 : M.getD (L.length - 1 - i) 0 = (scaleRootsAux c 1 L).getD i 0 := by
      rw [hM, List.getD_eq_getElem?_getD,
        List.getElem?_reverse (by rw [scaleRootsAux_length]; omega),
        scaleRootsAux_length, show L.length - 1 - (L.length - 1 - i) = i by omega,
        ← List.getD_eq_getElem?_getD]
    rw [h2, scaleRootsAux_getD, one_mul]
    have h3 : L.getD i 0 = p.coeff i := by
      rw [hL, List.getD_eq_getElem?_getD, Array.getElem?_toList]; rfl
    have h4 : L.length - 1 - i = p.natDegree - i := by
      rw [hL, Array.length_toList]; rfl
    rw [h3, h4]
  · have h1 : ((scaleRootsAux b 1 M).reverse).getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [List.length_reverse, scaleRootsAux_length, hlenM]; omega)]
      rfl
    have h2 : p.coeff i = 0 := by
      show (p.coeffs[i]?).getD 0 = 0
      rw [Array.getElem?_eq_none (by rw [← Array.length_toList, ← hL]; omega)]; rfl
    rw [h1, h2, zero_mul, zero_mul]

@[simp] theorem scaleRoots_zero (b c : R) : (0 : AzPolynomial R).scaleRoots b c = 0 := by
  apply AzPolynomial.ext
  show (normalize _).coeffs = #[]
  simp [scaleRootsAux, coeffs_zero, normalize]

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- roots ±1 scaled by 2: x² − 1 ↦ x² − 4 (b-powers keep the result monic)
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2-1").get!.scaleRoots 2 1)
    == "x^2-4"

-- roots ±1 scaled by 1/2: x² − 1 ↦ 4x² − 1 (roots ±1/2)
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2-1").get!.scaleRoots 1 2)
    == "4*x^2-1"

-- root 2 scaled by 3/2: x − 2 ↦ 2x − 6 (root 3)
#guard toChars ((parseAzPolynomial (R := AzInt) "x-2").get!.scaleRoots 3 2)
    == "2*x-6"

-- roots scaled by 0: all roots collapse to 0, degree preserved
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2-1").get!.scaleRoots 0 1)
    == "x^2"

-- denominator 0 (degenerate): only the constant term survives; normalize
-- strips the vanished leading coefficients
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2-1").get!.scaleRoots 1 0)
    == "-1"

-- scaling by 1/1 is the identity
#guard toChars ((parseAzPolynomial (R := AzInt) "x^3-2*x+7").get!.scaleRoots 1 1)
    == "x^3-2*x+7"

-- zero polynomial
#guard toChars ((0 : AzPolynomial AzInt).scaleRoots 5 3) == "0"

end Tests

end Azurite.AzPolynomial
