/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_2.Proposition_8_15
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Nat.Choose.Bounds

/-!
# BPR §8.2.3 Proposition 8.16: characteristic polynomial of a polynomial matrix

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.

**Proposition 8.16.** Let `M` be an `n × n` matrix with entries that are
polynomials in `Y₁, …, Y_k` of degrees `≤ d` and integer coefficients of bitsize
`≤ τ`. Then the coefficients of the characteristic polynomial of `M`, considered
as polynomials in `Y₁, …, Y_k`, have degrees `≤ d·n` and integer coefficients of
bitsize `≤ n (τ + bit(n) + k·bit(d+1) + 1)`.

The proof uses Proposition 8.15 and the fact that the coefficients of the
characteristic polynomial are signed sums of at most `2ⁿ` principal minors of `M`
(`Matrix.charpoly_coeff_eq_sum_minors`): each `c × c` principal minor is a
determinant bounded by Proposition 8.15 (after reindexing its `↥s`-index to
`Fin c`), and summing the `C(n,c) ≤ 2ⁿ` minors adds `bit(C(n,c) − 1) ≤ n` to the
bitsize.

Here `bit(N) = Int.size N` (BPR Definition 8.4).
-/

namespace Azurite.BPR

open _root_.Azurite.BPR.MvPolynomial

variable {n k : ℕ}

/-- **BPR Proposition 8.16.** For an `n × n` matrix (`n ≥ 1`) of polynomials in
`Y₁, …, Y_k` of total degree `≤ d` with integer coefficients of bitsize `≤ τ`,
every coefficient of the characteristic polynomial has total degree `≤ d·n` and
integer coefficients of bitsize `≤ n (τ + bit(n) + k·bit(d+1) + 1)`. -/
theorem proposition_8_16 (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) ℤ)) {d τ : ℕ}
    (hn : 0 < n)
    (hd : ∀ i j, (M i j).totalDegree ≤ d)
    (hτ : ∀ i j r, Int.size ((M i j).coeff r) ≤ τ) :
    ∀ i, (M.charpoly.coeff i).totalDegree ≤ d * n ∧
      ∀ r, Int.size ((M.charpoly.coeff i).coeff r) ≤
        n * (τ + Nat.size n + k * Nat.size (d + 1) + 1) := by
  set B := n * (τ + Nat.size n + k * Nat.size (d + 1)) with hB
  -- `1 ≤ B`, used for the empty principal minor (det = 1).
  have hone_le : 1 ≤ B := by
    rw [hB]
    have h2 : 1 ≤ τ + Nat.size n + k * Nat.size (d + 1) := by
      have := Nat.size_pos.mpr hn; omega
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ n * (τ + Nat.size n + k * Nat.size (d + 1)) := Nat.mul_le_mul hn h2
  -- Each principal minor (det of a `↥s`-submatrix) is bounded by Proposition 8.15.
  have minor_bound : ∀ s : Finset (Fin n),
      (M.submatrix (Subtype.val : {x // x ∈ s} → Fin n) Subtype.val).det.totalDegree ≤ d * n ∧
      ∀ rr, ((M.submatrix (Subtype.val : {x // x ∈ s} → Fin n)
                Subtype.val).det.coeff rr).natAbs.size ≤ B := by
    intro s
    have hcard_le : s.card ≤ n := by
      calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ s)
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    -- Reindex the `↥s`-submatrix to a `Fin s.card` matrix `N`.
    let e : Fin s.card ≃ {x // x ∈ s} := s.equivFin.symm
    let N : Matrix (Fin s.card) (Fin s.card) (MvPolynomial (Fin k) ℤ) :=
      (M.submatrix Subtype.val Subtype.val).submatrix e e
    have hNdet : (M.submatrix (Subtype.val : {x // x ∈ s} → Fin n) Subtype.val).det = N.det :=
      (Matrix.det_submatrix_equiv_self e _).symm
    have hdN : ∀ a b, (N a b).totalDegree ≤ d := by
      intro a b; show (M _ _).totalDegree ≤ d; exact hd _ _
    have hτN : ∀ a b rr, Int.size ((N a b).coeff rr) ≤ τ := by
      intro a b rr; show Int.size ((M _ _).coeff rr) ≤ τ; exact hτ _ _ rr
    refine ⟨?_, ?_⟩
    · rw [hNdet]
      exact (proposition_8_14 N hdN).trans (Nat.mul_le_mul_left d hcard_le)
    · intro rr
      rw [hNdet]
      rcases Nat.eq_zero_or_pos s.card with hc0 | hcpos
      · -- empty minor: `N.det = 1`.
        have : IsEmpty (Fin s.card) := hc0 ▸ inferInstanceAs (IsEmpty (Fin 0))
        rw [Matrix.det_isEmpty]
        refine le_trans ?_ hone_le
        rw [MvPolynomial.coeff_one]
        split <;> simp
      · obtain ⟨_, hsize⟩ := proposition_8_15 N hcpos hdN hτN
        refine (hsize rr).trans ?_
        rw [hB]
        exact Nat.mul_le_mul hcard_le (by gcongr; exact Nat.size_le_size hcard_le)
  intro i
  by_cases hi : i ≤ n
  · -- `i ≤ n`: the coefficient is `±` a sum of `(n − i)`-minors.
    set c := n - i with hc
    have hcn : c ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
    have hcoeff : M.charpoly.coeff i
        = (-1) ^ c * ∑ s ∈ Finset.powersetCard c (Finset.univ : Finset (Fin n)),
            (M.submatrix (Subtype.val : {x // x ∈ s} → Fin n) Subtype.val).det := by
      have h := Matrix.charpoly_coeff_eq_sum_minors M c hcn
      rw [Fintype.card_fin, show n - c = i from by omega] at h
      exact h
    rw [hcoeff]
    refine ⟨?_, fun r => ?_⟩
    · -- degree
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have hsign : ((-1 : MvPolynomial (Fin k) ℤ) ^ c).totalDegree = 0 := by
        refine Nat.le_zero.mp ((MvPolynomial.totalDegree_pow _ _).trans ?_)
        rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_one, Nat.mul_zero]
      rw [hsign, Nat.zero_add]
      exact MvPolynomial.totalDegree_finsetSum_le (fun s _ => (minor_bound s).1)
    · -- bitsize
      show (((-1 : MvPolynomial (Fin k) ℤ) ^ c *
        ∑ s ∈ Finset.powersetCard c (Finset.univ : Finset (Fin n)),
          (M.submatrix Subtype.val Subtype.val).det).coeff r).natAbs.size ≤ _
      have hCpow : (-1 : MvPolynomial (Fin k) ℤ) ^ c = MvPolynomial.C ((-1 : ℤ) ^ c) := by
        simp [map_pow]
      rw [hCpow, MvPolynomial.coeff_C_mul, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_neg, Int.natAbs_one, one_pow, Nat.one_mul, MvPolynomial.coeff_sum]
      refine (Int.size_finset_sum_le' (B := B) (fun s _ => (minor_bound s).2 r)).trans ?_
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      have hchoose : Nat.size (n.choose c - 1) ≤ n := by
        apply Nat.size_le.mpr
        calc n.choose c - 1 < n.choose c := Nat.sub_lt (Nat.choose_pos (by omega)) Nat.one_pos
          _ ≤ 2 ^ n := Nat.choose_le_two_pow n c
      calc B + Nat.size (n.choose c - 1) ≤ B + n := Nat.add_le_add_left hchoose _
        _ = n * (τ + Nat.size n + k * Nat.size (d + 1) + 1) := by rw [hB]; ring
  · -- `i > n`: the coefficient is zero.
    have hzero : M.charpoly.coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact not_le.mp hi
    rw [hzero]
    refine ⟨by rw [MvPolynomial.totalDegree_zero]; exact Nat.zero_le _, fun r => ?_⟩
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]; exact Nat.zero_le _

end Azurite.BPR
