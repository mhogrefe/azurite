/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Lemma_2_74
import Azurite.BasuPollackRoy.Chapter2.Section2_2.SturmTarskiTransfer

/-! # Sign-condition root counts transfer along order-preserving embeddings

The number of roots of `P ∈ F[X]` realizing a given sign condition on a family
`𝒬` of `F`-polynomials is the **same** in any two order-preserving extensions of
the ordered field `F` (with the intermediate value property).

This is the joint refinement of `card_roots_transfer`, and the engine behind the
uniqueness of the real closure. The proof is pure reuse: BPR's sign determination
(`card_eq_inv_mulVec`, Lemma 2.74) writes each count `c(σ, Z)` as a *field-independent*
rational matrix `(signMatrixQ s)⁻¹` applied to the Tarski-query vector
`TaQ(𝒬^A, P)`; that vector transfers entrywise by `tarskiQuery_transfer` (Stage 1),
since `𝒬^α` is a product of `F`-polynomials and `familyPow` commutes with `map`.
-/

open scoped Polynomial Matrix

namespace Azurite.BPR

open _root_.Polynomial

variable {ι : Type*} [Fintype ι]

/-- `𝒬^α` commutes with `map φ`: it is a product of powers, and ring homs preserve
both. -/
theorem familyPow_map {R R' : Type*} [Field R] [Field R'] (φ : R →+* R')
    (Q : ι → R[X]) (α : ι → ℕ) :
    (familyPow Q α).map φ = familyPow (fun i => (Q i).map φ) α := by
  simp [familyPow, Polynomial.map_prod, Polynomial.map_pow]

/-- **Sign-condition root counts transfer.** For `P ∈ F[X]` (`P ≠ 0`), a family
`Q : Fin s → F[X]`, and two order-preserving embeddings `ι : F → R`, `τ : F → R'`
into fields with the intermediate value property, the number of roots of `P`
realizing the `j`-th sign condition is the same downstream of `ι` and of `τ`.

Both counts equal the `j`-th coordinate of the field-independent vector
`(signMatrixQ s)⁻¹ ·ᵥ TaQ(𝒬^A, P)` (`card_eq_inv_mulVec`), and the Tarski-query
vector agrees by `tarskiQuery_transfer`. -/
theorem realizationOverFinset_card_transfer
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (ι : F →+* R) (hι : StrictMono ι) (τ : F →+* R') (hτ : StrictMono τ)
    (s : Nat) (P : F[X]) (hP : P ≠ 0) (Q : Fin s → F[X]) (j : Fin (3 ^ s)) :
    (SignCondition.realizationOverFinset (signFn s j) (P.map ι) (fun i => (Q i).map ι)).card
      = (SignCondition.realizationOverFinset (signFn s j) (P.map τ) (fun i => (Q i).map τ)).card := by
  have hR_card := congrFun (card_eq_inv_mulVec s (P.map ι) (fun i => (Q i).map ι)) j
  have hR'_card := congrFun (card_eq_inv_mulVec s (P.map τ) (fun i => (Q i).map τ)) j
  have hTaQ : (fun i => (tarskiQuery (familyPow (fun i => (Q i).map ι) (expFn s i)) (P.map ι) : ℚ))
            = (fun i => (tarskiQuery (familyPow (fun i => (Q i).map τ) (expFn s i)) (P.map τ) : ℚ)) := by
    funext i
    rw [← familyPow_map ι Q (expFn s i), ← familyPow_map τ Q (expFn s i)]
    have h := tarskiQuery_transfer hR hR' ι hι τ hτ P (familyPow Q (expFn s i)) hP
    exact_mod_cast h
  have hcardℚ :
      ((SignCondition.realizationOverFinset (signFn s j) (P.map ι) (fun i => (Q i).map ι)).card : ℚ)
    = ((SignCondition.realizationOverFinset (signFn s j) (P.map τ) (fun i => (Q i).map τ)).card : ℚ) := by
    rw [hR_card, hR'_card, hTaQ]
  exact_mod_cast hcardℚ

/-- The count transfer for an *arbitrary* sign condition `σ` (not just the
enumerated `signFn s j`); `signFn` is surjective onto all sign conditions. -/
theorem realizationOverFinset_card_transfer'
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (ι : F →+* R) (hι : StrictMono ι) (τ : F →+* R') (hτ : StrictMono τ)
    (s : Nat) (P : F[X]) (hP : P ≠ 0) (Q : Fin s → F[X]) (σ : SignCondition (Fin s)) :
    (SignCondition.realizationOverFinset σ (P.map ι) (fun i => (Q i).map ι)).card
      = (SignCondition.realizationOverFinset σ (P.map τ) (fun i => (Q i).map τ)).card := by
  obtain ⟨j, rfl⟩ := signFn_surjective s σ
  exact realizationOverFinset_card_transfer hR hR' ι hι τ hτ s P hP Q j

/-- **A sign condition is realized in `R` iff realized in `R'`.** Immediate from
the count transfer (a condition is realized exactly when its count is positive). -/
theorem realizationOver_nonempty_transfer
    {F R R' : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Field R'] [LinearOrder R'] [IsStrictOrderedRing R']
    (hR : HasIntermediateValueProperty R) (hR' : HasIntermediateValueProperty R')
    (ι : F →+* R) (hι : StrictMono ι) (τ : F →+* R') (hτ : StrictMono τ)
    (s : Nat) (P : F[X]) (hP : P ≠ 0) (Q : Fin s → F[X]) (σ : SignCondition (Fin s)) :
    (SignCondition.realizationOver σ (P.map ι) (fun i => (Q i).map ι)).Nonempty
      ↔ (SignCondition.realizationOver σ (P.map τ) (fun i => (Q i).map τ)).Nonempty := by
  rw [SignCondition.realizationOver_nonempty_iff_card_pos
        (by simpa [Polynomial.map_eq_zero_iff ι.injective] using hP),
      SignCondition.realizationOver_nonempty_iff_card_pos
        (by simpa [Polynomial.map_eq_zero_iff τ.injective] using hP),
      realizationOverFinset_card_transfer' hR hR' ι hι τ hτ s P hP Q σ]

end Azurite.BPR
