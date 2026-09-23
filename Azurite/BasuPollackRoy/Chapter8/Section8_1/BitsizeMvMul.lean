/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Size
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# BPR §8.1: Bitsize of a product of two multivariate polynomials

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if `P, Q : MvPolynomial (Fin k) ℤ` have
coefficient bitsizes bounded by `τ` and `σ` respectively, and
`totalDegree Q ≤ q`, then the coefficient bitsizes of `P * Q` are
bounded by `τ + σ + k * bit(q + 1)`.

Proved by induction on `k` using `MvPolynomial.finSuccEquiv` to view a
`(k+1)`-variable polynomial as a univariate polynomial over the
`k`-variable coefficient ring.
-/

namespace Azurite.BPR

/-- `bitsize(a * b) ≤ τ + σ` when `bitsize a ≤ τ` and `bitsize b ≤ σ`. -/
theorem Int.size_mul_le (a b : ℤ) (τ σ : ℕ)
    (ha : a.natAbs.size ≤ τ) (hb : b.natAbs.size ≤ σ) :
    (a * b).natAbs.size ≤ τ + σ := by
  rw [Nat.size_le] at ha hb ⊢
  rw [Int.natAbs_mul, show 2 ^ (τ + σ) = 2 ^ τ * 2 ^ σ from pow_add 2 τ σ]
  exact Nat.mul_lt_mul_of_lt_of_lt ha hb

/-- Triangle inequality for `Finset` sums of integers (`natAbs`). -/
theorem Int.natAbs_finset_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ihs _)

/-- Bitsize of a `Finset` sum of integers, bounded by element bound + `Nat.size` of card. -/
theorem Int.size_finset_sum_le {ι : Type _} {s : Finset ι} {f : ι → ℤ} {B : ℕ}
    (hB : ∀ i ∈ s, (f i).natAbs.size ≤ B) :
    (∑ i ∈ s, f i).natAbs.size ≤ B + Nat.size s.card := by
  rw [Nat.size_le]
  calc (∑ i ∈ s, f i).natAbs
      ≤ ∑ i ∈ s, (f i).natAbs := Int.natAbs_finset_sum_le s f
    _ ≤ ∑ _i ∈ s, (2 ^ B : ℕ) :=
        Finset.sum_le_sum fun i hi => Nat.le_of_lt (Nat.size_le.mp (hB i hi))
    _ = s.card * 2 ^ B := by simp [Finset.sum_const, smul_eq_mul]
    _ < 2 ^ s.card.size * 2 ^ B :=
        Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (Nat.two_pow_pos _)
    _ = 2 ^ (B + s.card.size) := by rw [← pow_add]; congr 1; omega

/-- Sharper variant of `Int.size_finset_sum_le` using `Nat.size (s.card - 1)`
    instead of `Nat.size s.card`. Saves one bit when `s.card` is a power of two
    (e.g., for `s.card = 1` we get `B + 0` instead of `B + 1`). -/
theorem Int.size_finset_sum_le' {ι : Type _} {s : Finset ι} {f : ι → ℤ} {B : ℕ}
    (hB : ∀ i ∈ s, (f i).natAbs.size ≤ B) :
    (∑ i ∈ s, f i).natAbs.size ≤ B + Nat.size (s.card - 1) := by
  by_cases h_card : s.card = 0
  · rw [Finset.card_eq_zero] at h_card
    subst h_card
    simp
  have h_pos : 0 < s.card := Nat.pos_of_ne_zero h_card
  rcases Nat.eq_zero_or_pos B with hB_zero | hB_pos
  · subst hB_zero
    have h_all_zero : ∀ i ∈ s, f i = 0 := by
      intro i hi
      have h := hB i hi
      rw [Nat.size_le] at h
      have : (f i).natAbs = 0 := by omega
      exact Int.natAbs_eq_zero.mp this
    simp [Finset.sum_eq_zero h_all_zero]
  rw [Nat.size_le]
  have h_card_le : s.card ≤ 2 ^ Nat.size (s.card - 1) := by
    have : s.card - 1 < 2 ^ Nat.size (s.card - 1) := Nat.lt_size_self _
    omega
  have h_2N_pos : 0 < 2 ^ Nat.size (s.card - 1) := Nat.two_pow_pos _
  have h_2B_pos : 0 < 2 ^ B := Nat.two_pow_pos _
  calc (∑ i ∈ s, f i).natAbs
      ≤ ∑ i ∈ s, (f i).natAbs := Int.natAbs_finset_sum_le s f
    _ ≤ ∑ _i ∈ s, (2 ^ B - 1 : ℕ) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have := hB i hi
        rw [Nat.size_le] at this
        omega
    _ = s.card * (2 ^ B - 1) := by simp [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ Nat.size (s.card - 1) * (2 ^ B - 1) :=
        Nat.mul_le_mul_right _ h_card_le
    _ < 2 ^ Nat.size (s.card - 1) * 2 ^ B :=
        Nat.mul_lt_mul_of_pos_left (by omega) h_2N_pos
    _ = 2 ^ (B + Nat.size (s.card - 1)) := by rw [← pow_add]; ring_nf

private theorem Finsupp.antidiag_fin0 :
    Finset.antidiagonal (0 : Fin 0 →₀ ℕ) = {(0, 0)} := by
  ext ⟨a, b⟩; simp only [Finset.mem_antidiagonal, Finset.mem_singleton, Prod.mk.injEq]
  exact ⟨fun _ => ⟨Finsupp.ext (fun i => i.elim0), Finsupp.ext (fun i => i.elim0)⟩,
         fun ⟨ha, hb⟩ => by subst ha; subst hb; simp⟩

private theorem Finset.antidiag_filter_snd_le (l q : ℕ) :
    ((Finset.antidiagonal l).filter (fun x : ℕ × ℕ => x.2 ≤ q)).card ≤ q + 1 := by
  have h := Finset.card_le_card_of_injOn (f := Prod.snd)
    (s := ((Finset.antidiagonal l).filter (fun x : ℕ × ℕ => x.2 ≤ q) : Finset _))
    (t := Finset.range (q + 1))
    (fun x hx => by
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_range]; omega)
    (fun x₁ hx₁ x₂ hx₂ heq => by
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
      ext <;> [omega; exact heq])
  rwa [Finset.card_range] at h

/-- **BPR §8.1 (unnumbered lemma).** If `P, Q : MvPolynomial (Fin k) ℤ` with
    coefficient bitsizes bounded by `τ` and `σ` respectively, and
    `totalDegree Q ≤ q`, then the coefficient bitsizes of `P * Q` are
    bounded by `τ + σ + k * Nat.size (q + 1)`. Proved by induction on `k`
    using `MvPolynomial.finSuccEquiv`. -/
theorem MvPolynomial.bitsize_coeff_mul_le :
    ∀ (k : ℕ) (P Q : MvPolynomial (Fin k) ℤ) (τ σ q : ℕ),
    (∀ m, (P.coeff m).natAbs.size ≤ τ) →
    (∀ m, (Q.coeff m).natAbs.size ≤ σ) →
    MvPolynomial.totalDegree Q ≤ q →
    ∀ m, ((P * Q).coeff m).natAbs.size ≤ τ + σ + k * Nat.size (q + 1) := by
  intro k; induction k with
  | zero =>
    intro P Q τ σ q hP hQ _hq m
    have : m = 0 := Finsupp.ext (fun i => i.elim0)
    subst this; simp only [Nat.zero_mul, Nat.add_zero]
    rw [MvPolynomial.coeff_mul, Finsupp.antidiag_fin0, Finset.sum_singleton]
    exact Int.size_mul_le _ _ τ σ (hP 0) (hQ 0)
  | succ k ih =>
    intro P Q τ σ q hP hQ hq m
    rw [show m = Finsupp.cons (m 0) (Finsupp.tail m) from by
      ext i; cases i using Fin.cases <;> simp [Finsupp.cons, Finsupp.tail]]
    rw [← MvPolynomial.finSuccEquiv_coeff_coeff,
        show (MvPolynomial.finSuccEquiv ℤ k) (P * Q) =
            (MvPolynomial.finSuccEquiv ℤ k) P * (MvPolynomial.finSuccEquiv ℤ k) Q
          from map_mul _ P Q,
        Polynomial.coeff_mul, MvPolynomial.coeff_sum]
    set l := m 0; set m' := Finsupp.tail m
    have hndQ : ((MvPolynomial.finSuccEquiv ℤ k) Q).natDegree ≤ q := by
      rw [MvPolynomial.natDegree_finSuccEquiv]
      exact le_trans (MvPolynomial.degreeOf_le_totalDegree Q 0) hq
    -- Filter sum to x.2 ≤ q: terms with x.2 > q have Q-coeff = 0
    rw [show ∑ x ∈ Finset.antidiagonal l,
          (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
            ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2).coeff m'
        = ∑ x ∈ (Finset.antidiagonal l).filter (fun x => x.2 ≤ q),
          (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
            ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2).coeff m' from by
      symm; apply Finset.sum_filter_of_ne
      intro x _ hne; by_contra hgt; push Not at hgt
      have : ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      exact hne (by simp [this])]
    set s := (Finset.antidiagonal l).filter (fun x : ℕ × ℕ => x.2 ≤ q)
    -- Each term bounded by IH
    have hB : ∀ x ∈ s, ((((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
         ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2).coeff m').natAbs.size
        ≤ τ + σ + k * Nat.size (q + 1) := by
      intro x _hx
      apply ih _ _ τ σ q
      · intro m''; rw [MvPolynomial.finSuccEquiv_coeff_coeff]; exact hP _
      · intro m''; rw [MvPolynomial.finSuccEquiv_coeff_coeff]; exact hQ _
      · by_cases hne : ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2 = 0
        · simp [hne]
        · have := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le Q x.2 hne; omega
    calc (∑ x ∈ s, (((MvPolynomial.finSuccEquiv ℤ k) P).coeff x.1 *
             ((MvPolynomial.finSuccEquiv ℤ k) Q).coeff x.2).coeff m').natAbs.size
        ≤ (τ + σ + k * Nat.size (q + 1)) + Nat.size s.card :=
          Int.size_finset_sum_le hB
      _ ≤ (τ + σ + k * Nat.size (q + 1)) + Nat.size (q + 1) :=
          Nat.add_le_add_left (Nat.size_le_size (Finset.antidiag_filter_snd_le l q)) _
      _ = τ + σ + (k + 1) * Nat.size (q + 1) := by ring

end Azurite.BPR
