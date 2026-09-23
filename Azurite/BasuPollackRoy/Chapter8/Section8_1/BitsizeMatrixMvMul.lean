/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvMul
import Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMatrixMvAdd
import Mathlib.Data.Matrix.Mul

/-!
# BPR §8.1: Total degree and coefficient bitsize of a product of two matrices
            over `ℤ[Y₁, …, Y_k]`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if `M : Matrix l m (MvPolynomial (Fin k) ℤ)` and
`N : Matrix m n (MvPolynomial (Fin k) ℤ)` have entry degrees in `Y` bounded
by `p` and `q` and coefficient bitsizes bounded by `τ` and `σ` respectively,
then the entries of `M * N` have degree in `Y` bounded by `p + q` and
coefficient bitsizes bounded by

  `τ + σ + k · bit(p + q) + bit(card m)`

— matching BPR's stated bound exactly.

The degree claim composes `MvPolynomial.totalDegree_mul` and
`MvPolynomial.totalDegree_finsetSum`. The bitsize claim flattens the
matrix-entry expansion into a single Finset sum over middle-index ×
antidiagonal pairs, bounds each integer product by `τ + σ`, and bounds
the total summand count by `(Fintype.card m) · (p + q + 1)^k`. The
critical slack — `bit(p + q + 1)` reducing to `bit(p + q)` once
multiplied by `card m` — comes from a `Nat.size` product inequality.
-/

namespace Azurite.BPR

/-! ### Arithmetic helpers -/

/-- For `c ≥ 1`, `c ≤ 2 ^ Nat.size (c - 1)`. -/
private lemma le_two_pow_size_pred {c : ℕ} (hc : 1 ≤ c) :
    c ≤ 2 ^ Nat.size (c - 1) := by
  have h : c - 1 < 2 ^ Nat.size (c - 1) := Nat.lt_size_self _
  omega

/-- For `c ≥ 1` and any `k`, `c ^ k ≤ 2 ^ (k * Nat.size (c - 1))`. -/
private lemma pow_le_two_pow_mul_size_pred {c : ℕ} (hc : 1 ≤ c) (k : ℕ) :
    c ^ k ≤ 2 ^ (k * Nat.size (c - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc c ^ (k + 1)
        = c ^ k * c := pow_succ c k
      _ ≤ 2 ^ (k * Nat.size (c - 1)) * 2 ^ Nat.size (c - 1) :=
          Nat.mul_le_mul ih (le_two_pow_size_pred hc)
      _ = 2 ^ ((k + 1) * Nat.size (c - 1)) := by
          rw [← pow_add]; congr 1; ring

/-- For `c ≥ 1`,
    `Nat.size (a * c ^ k) ≤ Nat.size a + k * Nat.size (c - 1)`. -/
private lemma size_mul_pow_le {a c k : ℕ} (hc : 1 ≤ c) :
    Nat.size (a * c ^ k) ≤ Nat.size a + k * Nat.size (c - 1) := by
  rw [Nat.size_le]
  calc a * c ^ k
      ≤ a * 2 ^ (k * Nat.size (c - 1)) :=
        Nat.mul_le_mul_left _ (pow_le_two_pow_mul_size_pred hc k)
    _ < 2 ^ Nat.size a * 2 ^ (k * Nat.size (c - 1)) :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.size a + k * Nat.size (c - 1)) := by rw [← pow_add]

/-! ### Antidiagonal cardinality bound -/

/-- The cardinality of the antidiagonal of `r : Fin k →₀ ℕ` is bounded by
    `(|r| + 1) ^ k`, where `|r| = r.sum`. -/
private lemma antidiagonal_card_le_pow_sum {k : ℕ} (r : Fin k →₀ ℕ) :
    (Finset.antidiagonal r).card ≤ (r.sum (fun _ x => x) + 1) ^ k := by
  set d := r.sum (fun _ x => x) with hd_def
  -- Each pair `(α, β) ∈ antidiag r` has `α i ≤ r i ≤ d`, so the function
  -- `(α, β) ↦ (i ↦ min (α i) d)` injects `antidiag r` into `Fin k → Fin (d + 1)`.
  let φ : (Fin k →₀ ℕ) × (Fin k →₀ ℕ) → (Fin k → Fin (d + 1)) :=
    fun p i => ⟨min (p.1 i) d, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have h_bnd : ∀ {α β : Fin k →₀ ℕ}, α + β = r → ∀ i, α i ≤ d := by
    intros α β hαβ i
    have h₁ : α i ≤ r i := by
      have : (α + β) i = r i := by rw [hαβ]
      simp [Finsupp.add_apply] at this; omega
    have h₂ : r i ≤ d := by
      by_cases hi : i ∈ r.support
      · rw [hd_def, Finsupp.sum, ← Finset.sum_erase_add _ _ hi]
        exact Nat.le_add_left _ _
      · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
    exact h₁.trans h₂
  have h_inj : Set.InjOn φ (Finset.antidiagonal r) := by
    intros p hp p' hp' hφ
    rw [Finset.mem_coe, Finset.mem_antidiagonal] at hp hp'
    have h_fst : p.1 = p'.1 := by
      apply Finsupp.ext
      intro i
      have heq : (φ p i).val = (φ p' i).val := by rw [hφ]
      simp only [φ] at heq
      rw [Nat.min_eq_left (h_bnd hp i), Nat.min_eq_left (h_bnd hp' i)] at heq
      exact heq
    have h_snd : p.2 = p'.2 := by
      have : p.1 + p.2 = p'.1 + p'.2 := by rw [hp, hp']
      rw [h_fst] at this
      exact add_left_cancel this
    exact Prod.ext h_fst h_snd
  have h_card := Finset.card_le_card_of_injOn φ
    (fun _ _ => Finset.mem_univ _) h_inj
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h_card

/-! ### Matrix-product bounds -/

/-- **BPR §8.1 (unnumbered lemma, degree part).** Entrywise total degrees
    of a product of two matrices over `MvPolynomial (Fin k) ℤ` are bounded
    by the sum of the entrywise total-degree bounds on the factors. -/
theorem Matrix.totalDegree_mvMul_le {k : ℕ} {l m n : Type _} [Fintype m]
    {M : Matrix l m (MvPolynomial (Fin k) ℤ)}
    {N : Matrix m n (MvPolynomial (Fin k) ℤ)}
    {p q : ℕ}
    (hM : ∀ i j, (M i j).totalDegree ≤ p)
    (hN : ∀ i j, (N i j).totalDegree ≤ q) :
    ∀ i j, ((M * N) i j).totalDegree ≤ p + q := by
  intro i j
  rw [_root_.Matrix.mul_apply]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro s _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hM i s) (hN s j))

/-- **BPR §8.1 (unnumbered lemma, bitsize part).** Entrywise coefficient
    bitsizes of a product of two matrices over `MvPolynomial (Fin k) ℤ`
    are bounded by `τ + σ + k * Nat.size (p + q) + Nat.size (Fintype.card m)`
    when the entrywise coefficient bitsizes are bounded by `τ` and `σ`
    and the entrywise total degrees are bounded by `p` and `q`. -/
theorem Matrix.bitsize_coeff_mvMul_le {k : ℕ} {l m n : Type _} [Fintype m]
    {M : Matrix l m (MvPolynomial (Fin k) ℤ)}
    {N : Matrix m n (MvPolynomial (Fin k) ℤ)}
    {τ σ p q : ℕ}
    (hM_size : ∀ i j r, ((M i j).coeff r).natAbs.size ≤ τ)
    (hN_size : ∀ i j r, ((N i j).coeff r).natAbs.size ≤ σ)
    (hM_deg : ∀ i j, (M i j).totalDegree ≤ p)
    (hN_deg : ∀ i j, (N i j).totalDegree ≤ q) :
    ∀ i j r, (((M * N) i j).coeff r).natAbs.size ≤
      τ + σ + k * Nat.size (p + q) + Nat.size (Fintype.card m) := by
  intro i j r
  by_cases hr : r.sum (fun _ x => x) ≤ p + q
  case neg =>
    -- `|r| > p + q` ⟹ `(M * N) i j` has totalDegree ≤ p + q < |r|, so the coeff is 0.
    push Not at hr
    have hcoeff : ((M * N) i j).coeff r = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      exact lt_of_le_of_lt (Matrix.totalDegree_mvMul_le hM_deg hN_deg i j) hr
    simp [hcoeff]
  case pos =>
    -- `|r| ≤ p + q`. Express the matrix entry's coefficient at `r` as a flat
    -- sum over `(s, (α, β)) ∈ univ ×ˢ antidiagonal r`, each summand bounded
    -- by `τ + σ`. Then bound `Nat.size` of the total summand count using
    -- `size_mul_pow_le` and the antidiagonal-cardinality bound.
    rw [_root_.Matrix.mul_apply, _root_.MvPolynomial.coeff_sum]
    simp_rw [_root_.MvPolynomial.coeff_mul]
    rw [← Finset.sum_product']
    set T := (Finset.univ : Finset m) ×ˢ Finset.antidiagonal r with hT_def
    have h_each : ∀ sp ∈ T,
        ((M i sp.1).coeff sp.2.1 * (N sp.1 j).coeff sp.2.2).natAbs.size ≤
          τ + σ :=
      fun sp _ => Int.size_mul_le _ _ τ σ (hM_size i sp.1 sp.2.1) (hN_size sp.1 j sp.2.2)
    have h_sum_size := Int.size_finset_sum_le (s := T)
      (f := fun sp => (M i sp.1).coeff sp.2.1 * (N sp.1 j).coeff sp.2.2)
      (B := τ + σ) h_each
    have h_card : T.card ≤ Fintype.card m * (p + q + 1) ^ k := by
      rw [hT_def, Finset.card_product, Finset.card_univ]
      exact Nat.mul_le_mul_left _ <|
        (antidiagonal_card_le_pow_sum r).trans <|
          Nat.pow_le_pow_left (by omega) k
    have h_card_size : Nat.size T.card ≤
        Nat.size (Fintype.card m) + k * Nat.size (p + q) := by
      have := size_mul_pow_le (a := Fintype.card m) (c := p + q + 1) (k := k)
        (by omega)
      simp only [Nat.add_sub_cancel] at this
      exact (Nat.size_le_size h_card).trans this
    calc _ ≤ (τ + σ) + Nat.size T.card := h_sum_size
      _ ≤ (τ + σ) + (Nat.size (Fintype.card m) + k * Nat.size (p + q)) :=
        Nat.add_le_add_left h_card_size _
      _ = τ + σ + k * Nat.size (p + q) + Nat.size (Fintype.card m) := by ring

end Azurite.BPR
