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

/-- 
The polynomial 1. 

In an arbitrary Semiring, `1` might equal `0` (the trivial ring). 
If `1 = 0`, then returning `[1]` violates our invariant because the last element is `0`. 
Therefore, we require `[DecidableEq R]` to return `[]` (the zero polynomial) if `1 = 0`.
-/
def one {R : Type _} [Semiring R] [DecidableEq R] : DensePoly R :=
  if h : (1 : R) = 0 then
    zero
  else
    ⟨[(1 : R)], by simp [h]⟩

instance {R : Type _} [Semiring R] : Inhabited (DensePoly R) := ⟨zero⟩
instance {R : Type _} [Semiring R] : Zero (DensePoly R) := ⟨zero⟩
instance {R : Type _} [Semiring R] [DecidableEq R] : One (DensePoly R) := ⟨one⟩

@[simp] lemma coeffs_zero {R : Type _} [Semiring R] : (0 : DensePoly R).coeffs = [] := rfl

/-- The natural degree of a `DensePoly`. Expected behavior: 0 for the zero polynomial. -/
def natDegree {R : Type _} [Semiring R] (p : DensePoly R) : ℕ :=
  p.coeffs.length - 1

/-- The degree of a `DensePoly`, returning `WithBot ℕ`. Expected behavior: ⊥ for the zero polynomial. -/
def degree {R : Type _} [Semiring R] (p : DensePoly R) : WithBot ℕ :=
  if p.coeffs = [] then ⊥ else ↑p.natDegree

end Azurite.DensePoly
