/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_1.SymmetricPolynomials
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! # BPR Section 2.1 — Exercise 2.7: Orbit sums span symmetric polynomials

> For a multi-index `α`, define `M_α = ∑_{σ ∈ S_k} X_σ^α`. Prove that
> every symmetric polynomial can be written as a finite sum
> `∑ c_α M_α`.

The proof uses averaging: since `rename σ Q = Q` for symmetric `Q`,
`k! • Q = ∑_σ rename σ Q`. Expanding `Q` as a sum of monomials and
swapping sums gives `k! • Q = ∑_α coeff_α(Q) • M_α`. Dividing by `k!`
(nonzero in characteristic 0) yields the result.

**Characteristic restriction.** BPR does not mention a characteristic
restriction, but the `CharZero K` hypothesis is necessary for this
formulation. In characteristic `p`, `M_α` sums over *all* permutations
(including those that fix `α`), so the stabilizer multiplicity
`|Stab(α)|` appears as a factor. When `p ∣ |Stab(α)|`, `M_α` vanishes.
For example, `X₁X₂ ∈ F₂[X₁,X₂]` is symmetric but `M_{(1,1)} = 2X₁X₂ = 0`
in char 2, and no other `M_α` contains the monomial `X₁X₂`.

The statement *does* hold over arbitrary fields if one uses the proper
monomial symmetric polynomials `m_α = ∑_{β ∈ orbit(α)} X^β` (each
distinct monomial counted once), which is Mathlib's
`MvPolynomial.msymm`. If a future application needs the result in
positive characteristic, this proof should be refactored to use
`msymm`.
-/

namespace Azurite.BPR

open MvPolynomial Equiv

variable {K : Type*} [Field K]

/-- **BPR Notation.** `M_α = ∑_{σ ∈ S_k} X_σ^α`: the sum of the monomial `X^α` over
    all permutations of the variables. `X_σ^α = rename σ (monomial α 1)`. -/
noncomputable def monomialOrbitSum (k : ℕ) (α : Fin k →₀ ℕ) : MvPolynomial (Fin k) K :=
  ∑ σ : Perm (Fin k), rename (σ : Fin k → Fin k) (monomial α 1)

/-- **BPR Exercise 2.7.** Every symmetric polynomial can be written as a finite
    sum `∑ cα • M_α`. -/
theorem exercise_2_7 [CharZero K] {k : ℕ} {Q : MvPolynomial (Fin k) K}
    (hQ : Q.IsSymmetric) :
    ∃ (S : Finset (Fin k →₀ ℕ)) (c : (Fin k →₀ ℕ) → K),
      Q = ∑ α ∈ S, c α • monomialOrbitSum k α := by
  refine ⟨Q.support, fun α => Q.coeff α / (k.factorial : K), ?_⟩
  have hk_ne : (↑k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  -- Step 1: k! • Q = ∑ σ, rename σ Q
  have h1 : (↑k.factorial : K) • Q = ∑ σ : Perm (Fin k), rename ↑σ Q := by
    conv_rhs => arg 2; ext σ; rw [hQ σ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    norm_cast
  -- Step 2: ∑ σ, rename σ Q = ∑ α ∈ support, coeff α Q • M_α
  have h2 : ∑ σ : Perm (Fin k), rename (↑σ) Q =
      ∑ α ∈ Q.support, Q.coeff α • (monomialOrbitSum k α : MvPolynomial (Fin k) K) := by
    calc ∑ σ : Perm (Fin k), rename (⇑σ) Q
        = ∑ σ : Perm (Fin k), ∑ α ∈ Q.support,
            MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α) (Q.coeff α) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          conv_lhs => rw [Q.as_sum, map_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          exact rename_monomial _ _ _
      _ = ∑ α ∈ Q.support, ∑ σ : Perm (Fin k),
            MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α) (Q.coeff α) :=
          Finset.sum_comm
      _ = ∑ α ∈ Q.support, Q.coeff α • monomialOrbitSum k α := by
          refine Finset.sum_congr rfl fun α _ => ?_
          unfold monomialOrbitSum; simp_rw [rename_monomial]
          have hfactor : ∀ σ : Perm (Fin k),
            (MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α)) (Q.coeff α) =
            Q.coeff α • (MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α)) (1 : K) :=
            fun σ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          simp_rw [hfactor, ← Finset.smul_sum]
  -- Combine: Q = (1/k!) • k! • Q = ∑ (coeff/k!) • M_α
  have hmain := h1.trans h2
  have hinv : Q = (↑k.factorial : K)⁻¹ • ((↑k.factorial : K) • Q) :=
    (inv_smul_smul₀ hk_ne Q).symm
  conv_lhs => rw [hinv, hmain, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [smul_comm (↑k.factorial : K)⁻¹, div_eq_mul_inv, mul_smul]

end Azurite.BPR
