/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! # BPR Section 2.1 — Symmetric polynomials

**Definition (BPR p.38).** Let `K` be a field. A polynomial
`Q(X₁, …, Xₖ) ∈ K[X₁, …, Xₖ]` is *symmetric* if for every permutation `σ`
of `{1, …, k}`, `Q(X_{σ(1)}, …, X_{σ(k)}) = Q(X₁, …, Xₖ)`.

**Mathlib correspondence.** This is exactly `MvPolynomial.IsSymmetric`
from `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs`, defined as
`∀ e : Equiv.Perm σ, MvPolynomial.rename e φ = φ`.

The *i*-th elementary symmetric function `E_i` is `MvPolynomial.esymm`.
-/

namespace Azurite.BPR

open MvPolynomial

variable {K : Type*} [Field K]

/-- **BPR Definition (p.38).** A polynomial `Q ∈ K[X₁, …, Xₖ]` is *symmetric* if it is
    invariant under every permutation of its variables.

    This is `MvPolynomial.IsSymmetric` in Mathlib: `∀ e : Perm (Fin k), rename e Q = Q`. -/
def IsSymmetricPolynomial (k : ℕ) (Q : MvPolynomial (Fin k) K) : Prop :=
  Q.IsSymmetric

/-- **BPR Definition (p.38).** The `i`-th *elementary symmetric function*
    `E_i = ∑_{1 ≤ j₁ < ⋯ < jᵢ ≤ k} X_{j₁} ⋯ X_{jᵢ}`,
    i.e., the sum of all squarefree degree-`i` monomials.

    This is `MvPolynomial.esymm` in Mathlib. -/
noncomputable def elementarySymmetric (k : ℕ) (i : ℕ) : MvPolynomial (Fin k) K :=
  esymm (Fin k) K i

end Azurite.BPR
