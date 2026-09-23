/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Fin
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.CompareEmbed

/-!
# BPR §8.1 Lemma 8.6: Counting monomials by degree

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

The number of monomials of degree `≤ d` in `k` variables is
`(d + k).choose k`.

We construct the actual `Finset` of exponent tuples `Fin k → ℕ` with
sum `≤ d`, prove a membership characterisation, and compute its
cardinality via the hockey-stick identity
(`Nat.sum_range_add_choose`). The result is then lifted to
`MonicMonomial`, Azurite's concrete monomial type.

As a corollary, the bound `(d + k).choose k ≤ (d + 1) ^ k` is
established.
-/

namespace Azurite.BPR

open Matrix MonomialOrder

/-- The finite set of exponent tuples `Fin k → ℕ` whose sum is `≤ d`.
    These are the exponent vectors of monic monomials of degree `≤ d`
    in `k` variables. -/
def monicMonomials : (k : ℕ) → (d : ℕ) → Finset (Fin k → ℕ)
  | 0, _ => {Fin.elim0}
  | k + 1, d => (Finset.range (d + 1)).biUnion fun j =>
      (monicMonomials k (d - j)).image (vecCons j)

/-- An exponent tuple belongs to `monicMonomials k d` iff its sum is `≤ d`. -/
theorem mem_monicMonomials {k d : ℕ} {f : Fin k → ℕ} :
    f ∈ monicMonomials k d ↔ ∑ i, f i ≤ d := by
  induction k generalizing d with
  | zero =>
    simp only [monicMonomials, Finset.mem_singleton, Fintype.sum_empty]
    exact ⟨fun _ => Nat.zero_le _, fun _ => Subsingleton.elim _ _⟩
  | succ k ih =>
    simp only [monicMonomials, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, g, hg, rfl⟩
      simp only [vecCons, Fin.sum_cons]; rw [ih] at hg; omega
    · intro hle
      have hsum : ∑ i, f i = f 0 + ∑ i, Fin.tail f i := by
        conv_lhs => rw [← Fin.cons_self_tail f]; rw [Fin.sum_cons]
      refine ⟨f 0, ?_, Fin.tail f, ?_, Fin.cons_self_tail f⟩
      · omega
      · rw [ih]; omega

private theorem vecCons_injective_right {n : ℕ} (j : ℕ) :
    Function.Injective (vecCons j : (Fin n → ℕ) → Fin (n + 1) → ℕ) := by
  intro a b h; ext i; have := congr_fun h i.succ
  simp [vecCons, Fin.cons] at this; exact this

private theorem monicMonomials_pairwiseDisjoint (k d : ℕ) :
    Set.PairwiseDisjoint (Finset.range (d + 1) : Set ℕ)
      (fun j => (monicMonomials k (d - j)).image (vecCons j)) := by
  intro j₁ _ j₂ _ hne
  simp only [Finset.disjoint_left, Finset.mem_image]
  rintro _ ⟨_, _, rfl⟩ ⟨_, _, h⟩
  exact hne (by have := congr_fun h 0; simp [vecCons, Fin.cons] at this; exact this.symm)

/-- **BPR Lemma 8.6.** The number of monic monomials of degree `≤ d` in `k`
    variables is `(d + k).choose k`. -/
theorem card_monicMonomials (k d : ℕ) :
    (monicMonomials k d).card = (d + k).choose k := by
  induction k generalizing d with
  | zero => simp [monicMonomials]
  | succ k ih =>
    rw [monicMonomials, Finset.card_biUnion (monicMonomials_pairwiseDisjoint k d)]
    simp only [Finset.card_image_of_injective _ (vecCons_injective_right _), ih]
    rw [show d + (k + 1) = d + k + 1 from by omega, ← Nat.sum_range_add_choose d k]
    apply Finset.sum_bij' (fun i _ => d - i) (fun i _ => d - i)
    · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_range] at ha; omega
    · intro a ha; simp only [Finset.mem_range] at ha; omega
    · intros; rfl

-- Sanity checks
#guard (monicMonomials 0 5).card = 1
#guard (monicMonomials 1 3).card = 4
#guard (monicMonomials 2 2).card = 6   -- 1, x₀, x₁, x₀², x₀x₁, x₁²
#guard (monicMonomials 3 1).card = 4
#guard (monicMonomials 3 3).card = 20

/-! ### MonicMonomial bridge -/

variable {n : ℕ} (ord : MonomialOrder)

private theorem ofFn_mk_injective :
    Function.Injective (fun f : Fin n → ℕ => (⟨Vector.ofFn f⟩ : MonicMonomial n ord)) := by
  intro a b h
  simp only [MonicMonomial.mk.injEq] at h
  exact funext (fun i => by
    have : (Vector.ofFn a)[i] = (Vector.ofFn b)[i] := by rw [h]
    simpa using this)

/-- The finite set of `MonicMonomial`s of total degree `≤ d`. -/
def MonicMonomial.finsetLeD (d : ℕ) : Finset (MonicMonomial n ord) :=
  (monicMonomials n d).image (fun f => ⟨Vector.ofFn f⟩)

/-- A `MonicMonomial` belongs to `finsetLeD` iff its total degree is `≤ d`. -/
theorem MonicMonomial.mem_finsetLeD {d : ℕ} {m : MonicMonomial n ord} :
    m ∈ MonicMonomial.finsetLeD ord d ↔ m.totalDegree ≤ d := by
  simp only [finsetLeD, Finset.mem_image, mem_monicMonomials]
  constructor
  · rintro ⟨f, hf, hm⟩
    rw [MonicMonomial.totalDegree, ← hm, totalDeg_eq_finsum]
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]; exact hf
  · intro hle
    refine ⟨fun i => m.exponents[i], ?_, ?_⟩
    · rw [MonicMonomial.totalDegree, totalDeg_eq_finsum] at hle
      convert hle using 1
    · ext : 1; ext i : 1; simp

/-- **BPR Lemma 8.6 (MonicMonomial form).** The number of monic monomials
    of total degree `≤ d` in `n` variables is `(d + n).choose n`. -/
theorem MonicMonomial.card_finsetLeD (d : ℕ) :
    (MonicMonomial.finsetLeD ord d : Finset (MonicMonomial n ord)).card =
    (d + n).choose n := by
  rw [finsetLeD, Finset.card_image_of_injective _ (ofFn_mk_injective (ord := ord)),
      card_monicMonomials]

/-! ### Upper bound on binomial coefficient -/

/-- `(d + n).choose n ≤ (d + 1) ^ n`.
    Proof: by induction on `n`, using the hockey-stick identity to decompose
    `(d + n + 1).choose (n + 1) = ∑ i ≤ d, (i + n).choose n ≤ (d + 1) · (d + n).choose n`. -/
theorem choose_add_le_pow (d n : ℕ) : (d + n).choose n ≤ (d + 1) ^ n := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
    rw [show d + (n + 1) = d + n + 1 from by omega, ← Nat.sum_range_add_choose d n]
    calc ∑ i ∈ Finset.range (d + 1), (i + n).choose n
        ≤ ∑ _i ∈ Finset.range (d + 1), (d + n).choose n := by
          apply Finset.sum_le_sum
          intro i hi; apply Nat.choose_le_choose
          simp only [Finset.mem_range] at hi; omega
      _ = (d + 1) * (d + n).choose n := by
          simp [Finset.sum_const, Finset.card_range]
      _ ≤ (d + 1) * (d + 1) ^ n := Nat.mul_le_mul_left _ (ih d)
      _ = (d + 1) ^ (n + 1) := by ring

/-- Corollary: the number of monic monomials of degree `≤ d` in `k` variables
    is at most `(d + 1) ^ k`. -/
theorem card_monicMonomials_le_pow (k d : ℕ) :
    (monicMonomials k d).card ≤ (d + 1) ^ k :=
  card_monicMonomials k d ▸ choose_add_le_pow d k

/-- Corollary (MonicMonomial form): the number of monic monomials of total
    degree `≤ d` in `n` variables is at most `(d + 1) ^ n`. -/
theorem MonicMonomial.card_finsetLeD_le_pow (d : ℕ) :
    (MonicMonomial.finsetLeD ord d : Finset (MonicMonomial n ord)).card ≤
      (d + 1) ^ n := by
  rw [MonicMonomial.card_finsetLeD]; exact choose_add_le_pow d n

end Azurite.BPR
