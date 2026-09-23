/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # BPR Section 2.1 — Proposition 2.13: Fundamental Theorem of Symmetric Polynomials

> Let `K` be a field. Every symmetric polynomial `Q(X₁,…,Xₖ) ∈ K[X₁,…,Xₖ]`
> can be written as `R(E₁,…,Eₖ)` for some polynomial `R(T₁,…,Tₖ) ∈ K[T₁,…,Tₖ]`,
> where `Eᵢ` is the `i`-th elementary symmetric function.

**Proof sketch (BPR).** The leading monomial of a symmetric polynomial `Q`
in the graded lexicographic ordering satisfies `α₁ ≥ α₂ ≥ ⋯ ≥ αₖ`.
Subtracting the matching product `c_α E₁^{α₁−α₂} ⋯ Eₖ^{αₖ}` yields a symmetric
polynomial `Q₁` with strictly smaller leading monomial; iterating and using
well-foundedness of the grlex ordering closes the descent.

In Mathlib this is `MvPolynomial.esymmAlgHom_surjective`, which states that the
`R`-algebra homomorphism sending `Tᵢ ↦ Eᵢ` is surjective onto the symmetric
subalgebra.
-/

namespace Azurite.BPR

variable {K : Type*} [CommRing K]

open MvPolynomial in
/-- **BPR Proposition 2.13** (Fundamental Theorem of Symmetric Polynomials).
    Let `K` be a field. Every symmetric polynomial `Q(X₁,…,Xₖ) ∈ K[X₁,…,Xₖ]`
    can be written as `R(E₁,…,Eₖ)` for some polynomial `R(T₁,…,Tₖ) ∈ K[T₁,…,Tₖ]`,
    where `Eᵢ` is the `i`-th elementary symmetric function.

    **Proof sketch (BPR):** The leading monomial of a symmetric polynomial `Q`
    in the graded lexicographic ordering satisfies `α₁ ≥ α₂ ≥ ⋯ ≥ αₖ`.
    Subtracting the matching product `c_α E₁^{α₁−α₂} ⋯ Eₖ^{αₖ}` yields a symmetric
    polynomial `Q₁` with strictly smaller leading monomial. Iterating and using
    well-foundedness of the grlex ordering (no infinite descending sequences) gives
    the result.

    In Mathlib this is `MvPolynomial.esymmAlgHom_surjective`, which states that the
    `R`-algebra homomorphism sending `Tᵢ ↦ Eᵢ` is surjective onto the symmetric
    subalgebra. -/
theorem proposition_2_13 {k : ℕ} (Q : MvPolynomial (Fin k) K)
    (hQ : Q.IsSymmetric) :
    ∃ R : MvPolynomial (Fin k) K,
      MvPolynomial.aeval (fun i : Fin k => MvPolynomial.esymm (Fin k) K (↑i + 1)) R = Q := by
  have hsurj := MvPolynomial.esymmAlgHom_surjective K (show Fintype.card (Fin k) ≤ k by simp)
  obtain ⟨R, hR⟩ := hsurj ⟨Q, hQ⟩
  exact ⟨R, by rw [← MvPolynomial.esymmAlgHom_apply, hR]⟩

end Azurite.BPR
