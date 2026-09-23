/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# BPR Definition 4.73: quasi-monic polynomials

A nonzero polynomial `P ∈ K[X₁, …, X_{k-1}][X_k]` is *quasi-monic with respect to `X_k`* if its
leading coefficient with respect to `X_k` is an element of `K`. We model
`K[X₁, …, X_{k-1}][X_k]` as `Polynomial (MvPolynomial (Fin n) K)` (`n = k - 1`), the distinguished
variable `X_k` being the `Polynomial` indeterminate; the leading coefficient with respect to `X_k`
is `Polynomial.leadingCoeff`, an element of `K[X₁, …, X_{k-1}] = MvPolynomial (Fin n) K`, and "is an
element of `K`" means it is a constant `MvPolynomial.C c`.

A set of polynomials `𝒫` is quasi-monic with respect to `X_k` if each of its members is.
-/

namespace Azurite.BPR.Chapter4

variable {n : ℕ} {K : Type*} [Field K]

/-- **BPR Definition 4.73.** A nonzero polynomial `P ∈ K[X₁, …, X_{k-1}][X_k]` is *quasi-monic
with respect to `X_k`* if its leading coefficient with respect to `X_k` is an element of `K`,
i.e. a constant `MvPolynomial.C c`. -/
def IsQuasiMonic (P : Polynomial (MvPolynomial (Fin n) K)) : Prop :=
  P ≠ 0 ∧ ∃ c : K, P.leadingCoeff = MvPolynomial.C c

/-- A quasi-monic polynomial is nonzero. -/
theorem IsQuasiMonic.ne_zero {P : Polynomial (MvPolynomial (Fin n) K)} (hP : IsQuasiMonic P) :
    P ≠ 0 :=
  hP.1

/-- The constant value of the leading coefficient of a quasi-monic polynomial is nonzero. -/
theorem IsQuasiMonic.leadingCoeff_const_ne_zero {P : Polynomial (MvPolynomial (Fin n) K)}
    (hP : IsQuasiMonic P) : ∀ c : K, P.leadingCoeff = MvPolynomial.C c → c ≠ 0 := by
  rintro c hc rfl
  exact hP.1 (Polynomial.leadingCoeff_eq_zero.mp (by simpa using hc))

/-- **BPR Definition 4.73 (for a set).** A set of polynomials `𝒫 ⊆ K[X₁, …, X_{k-1}][X_k]` is
*quasi-monic with respect to `X_k`* if each polynomial in `𝒫` is quasi-monic with respect to
`X_k`. -/
def IsQuasiMonicSet (S : Set (Polynomial (MvPolynomial (Fin n) K))) : Prop :=
  ∀ P ∈ S, IsQuasiMonic P

end Azurite.BPR.Chapter4
