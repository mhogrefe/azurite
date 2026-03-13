import Mathlib
import Mathlib.Algebra.Polynomial.Basic

/-!
# Computational Univariate Polynomials

This module defines `DensePoly`, a computational representation of univariate
polynomials over an arbitrary Semiring/Ring `R`.

Unlike `Polynomial R` in Mathlib (which represents polynomials as finitely
supported functions `Finsupp`), `DensePoly R` focuses on a dense representation
using a list of coefficients.

The representation maintains the invariant that the last element of the
list (the leading coefficient) is always non-zero, unless the polynomial is the
zero polynomial (represented by the empty list).
-/

namespace Azurite

/-- A univariate polynomial represented as a dense list of coefficients
`[a_0, a_1, ..., a_n]`. The last element `a_n` is guaranteed to be non-zero
(unless the list is empty, representing the zero polynomial). -/
structure DensePoly (R : Type _) [Semiring R] where
  coeffs : List R
  -- If the list is non-empty, the last element is not 0
  last_ne_zero : coeffs.getLast? ≠ some 0
deriving Repr

@[ext] lemma DensePoly.ext {R : Type _} [Semiring R] {p q : Azurite.DensePoly R} (h : p.coeffs = q.coeffs) : p = q := by
  cases p
  cases q
  simp at h
  congr

end Azurite

namespace Azurite.DensePoly

/-- The zero polynomial is represented by the empty list. -/
def zero {R : Type _} [Semiring R] : DensePoly R :=
  ⟨[], by simp⟩

instance {R : Type _} [Semiring R] : Inhabited (DensePoly R) := ⟨zero⟩
instance {R : Type _} [Semiring R] : Zero (DensePoly R) := ⟨zero⟩

@[simp] lemma coeffs_zero {R : Type _} [Semiring R] : (0 : DensePoly R).coeffs = [] := rfl

end Azurite.DensePoly
