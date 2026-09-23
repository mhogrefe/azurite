/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.IntContent
import Azurite.AzMvPolynomial.Equiv.MonomialOrder
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.Gcd

/-!
# Content and leading-coefficient multiplicativity for `AzMvPolynomial` over `AzInt`

The multivariate content Gauss layer. Two multiplicativity results are
established here:

* `leadingCoeff_mul` — the leading coefficient (of the `ord`-largest
  monomial) is multiplicative on nonzero polynomials. No Gauss: the leading
  term of a product is the product of the leading terms since `ord` is a
  monomial order (Mathlib `MonomialOrder.leadingCoeff_mul`).

* `Azurite.AzPolynomial.contentGen_mul` (in `AzPolynomial/Equiv/GcdTower.lean`)
  — the **Gauss** multiplicativity of the concrete `contentGen` fold, one
  tower level at a time, via `map_contentGen` + Mathlib `Polynomial.content_mul`
  over the `NormalizedGCDMonoid` model ring. This is the substantive Gauss
  content, absent from Mathlib for the multivariate case.

The flat `intContent` multiplicativity (`intContent_mul`) then reduces to
`contentGen_mul` through the tower correspondence; see the note at the end of
this file for the remaining "flatten coefficients" bridge.
-/

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- A nonzero polynomial has a nonempty term array. -/
theorem size_pos_of_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    0 < P.terms.size := by
  by_contra h
  push Not at h
  apply hP
  have hE : P.terms = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_zero.mp h)
  obtain ⟨t, s⟩ := P
  simp only at hE
  subst hE
  rfl

/-- For nonzero `P`, `leadingCoeff P` is Mathlib's `MonomialOrder.leadingCoeff`
of the represented polynomial. -/
theorem leadingCoeff_toMvPoly {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    (toMathlibMonomialOrder ord).leadingCoeff P.toMvPoly = leadingCoeff P := by
  rw [Azurite.leadingCoeff_eq_terms_zero P (size_pos_of_ne_zero hP)]
  unfold leadingCoeff AzMvPolynomial.leadCoeff AzMvPolynomial.leadTerm
  rw [Array.getElem?_eq_getElem (size_pos_of_ne_zero hP)]
  rfl

/-- **Leading-coefficient multiplicativity** (no Gauss): the coefficient of
the `ord`-largest monomial is multiplicative on nonzero polynomials. -/
theorem leadingCoeff_mul {P Q : AzMvPolynomial n AzInt ord}
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    leadingCoeff (P * Q) = leadingCoeff P * leadingCoeff Q := by
  have hPQ : P * Q ≠ 0 := by
    intro h
    have h0 : toMvPoly (P * Q) = 0 := by rw [h, toMvPoly_zero]
    rw [toMvPoly_mul] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hP (toMvPoly_injective (by rw [h1, toMvPoly_zero]))
    · exact hQ (toMvPoly_injective (by rw [h1, toMvPoly_zero]))
  rw [← leadingCoeff_toMvPoly hPQ, ← leadingCoeff_toMvPoly hP,
    ← leadingCoeff_toMvPoly hQ, toMvPoly_mul, MonomialOrder.leadingCoeff_mul]

/-! ### Multiplicativity of `intContent`

`intContent_mul` (and Gauss's lemma `intContent_mul_primitive`) are proven in
`Azurite.AzMvPolynomial.Equiv.IntContentMul` by the textbook
**reduction-mod-`p`** argument — no `NormalizedGCDMonoid` on
`MvPolynomial (Fin n) ℤ` is needed. See that file for the `primPos`
factorization, primitivity of the primitive part, and the positive
leading-coefficient fact. -/

end Azurite.AzMvPolynomial
