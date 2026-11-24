/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.ModByMonicInv
import Azurite.AzPolynomial.Equiv.DivModByMonic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The remainder by a precomputed inverse is the remainder

* `divByMonic_coeff_of_inverse` (Mathlib polynomials): for monic `F` of degree `d`, `P` of
  degree at most `2d − 2` and `G` with `rev_d(F) · G ≡ 1 (mod X^(d−1))`, the coefficients of
  `P /ₘ F` are those of `rev_(2d−2)(P) · G` below `X^(d−1)`, reversed.
* `invRev_spec`: `invRev f` is such a `G` for monic `f`.
* **`modByMonicInv_eq`**: `modByMonicInv f (invRev f) P = modByMonic P f` for monic `f`.
-/

open Polynomial

namespace Azurite.AzPolynomial

section Theory

variable {R : Type _} [CommRing R]

/-- Products agree below `Xⁿ` when the left factors do. -/
theorem coeff_mul_congr_left {a b c : R[X]} {n : ℕ} (h : ∀ i, i < n → a.coeff i = b.coeff i) :
    ∀ i, i < n → (a * c).coeff i = (b * c).coeff i := by
  intro i hi
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.mem_antidiagonal.mp hx
  rw [h x.1 (by omega)]

/-- **The quotient from the inverse of the reversed divisor.** -/
theorem divByMonic_coeff_of_inverse {F G P : R[X]} {d : ℕ} (hF : F.Monic)
    (hd : F.natDegree = d) (hP : P.natDegree ≤ 2 * d - 2)
    (hG : ∀ j, j < d - 1 → (reflect d F * G).coeff j = (1 : R[X]).coeff j)
    (i : ℕ) (hi : i < d - 1) :
    (P /ₘ F).coeff i = (reflect (2 * d - 2) P * G).coeff (d - 2 - i) := by
  have hd2 : 2 ≤ d := by omega
  have hF1 : F ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hd
    omega
  have hq : (P /ₘ F).natDegree ≤ d - 2 := by
    rw [natDegree_divByMonic P hF, hd]
    omega
  have hr : ∀ k, d ≤ k → (P %ₘ F).coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (natDegree_modByMonic_lt P hF hF1) (hd ▸ hk))
  have hsplit : reflect (2 * d - 2) P =
      reflect (2 * d - 2) (P %ₘ F) + reflect d F * reflect (d - 2) (P /ₘ F) := by
    conv_lhs => rw [← modByMonic_add_div P F]
    rw [reflect_add, show 2 * d - 2 = d + (d - 2) by omega,
      reflect_mul F (P /ₘ F) (le_of_eq hd) hq]
  have hj : d - 2 - i < d - 1 := by omega
  rw [hsplit, add_mul, Polynomial.coeff_add]
  have h1 : (reflect (2 * d - 2) (P %ₘ F) * G).coeff (d - 2 - i) = 0 := by
    have := coeff_mul_congr_left (a := reflect (2 * d - 2) (P %ₘ F)) (b := 0) (c := G)
      (n := d - 1) (fun k hk => by
        rw [coeff_reflect, revAt_le (by omega), coeff_zero]
        exact hr _ (by omega)) (d - 2 - i) hj
    rw [this, zero_mul, coeff_zero]
  have h2 : (reflect d F * reflect (d - 2) (P /ₘ F) * G).coeff (d - 2 - i) =
      (P /ₘ F).coeff i := by
    rw [show reflect d F * reflect (d - 2) (P /ₘ F) * G =
      reflect d F * G * reflect (d - 2) (P /ₘ F) by ring,
      coeff_mul_congr_left (b := 1) hG (d - 2 - i) hj, one_mul, coeff_reflect,
      revAt_le (by omega)]
    congr 1
    omega
  rw [h1, h2, zero_add]

end Theory

variable {R : Type _} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
theorem sumTo_eq (h : ℕ → R) (n : ℕ) : sumTo h n = ∑ i ∈ Finset.range n, h i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih, Finset.sum_range_succ]

omit [DecidableEq R] in
theorem invRevCoeffs_size (f : AzPolynomial R) (d : ℕ) :
    ∀ (n : ℕ) (g : Array R), (invRevCoeffs f d n g).size = g.size + n := by
  intro n
  induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g
    rw [invRevCoeffs, ih, Array.size_push]
    omega

/-- The recurrence that the entries satisfy. -/
def InvRevInv (f : AzPolynomial R) (d : ℕ) (g : Array R) : Prop :=
  (g[0]?).getD 0 = 1 ∧ ∀ k, 1 ≤ k → k < g.size →
    (g[k]?).getD 0 = -∑ i ∈ Finset.range k, f.coeff (d - (i + 1)) * (g[k - (i + 1)]?).getD 0

omit [DecidableEq R] in
theorem invRevCoeffs_inv (f : AzPolynomial R) (d : ℕ) :
    ∀ (n : ℕ) (g : Array R), 1 ≤ g.size → InvRevInv f d g →
      InvRevInv f d (invRevCoeffs f d n g) := by
  intro n
  induction n with
  | zero => intro g _ h; exact h
  | succ n ih =>
    intro g hg h
    rw [invRevCoeffs]
    refine ih _ (by rw [Array.size_push]; omega) ⟨?_, ?_⟩
    · rw [Array.getElem?_push_lt hg]
      have := h.1
      rwa [Array.getElem?_eq_getElem hg] at this
    · intro k hk1 hk
      rw [Array.size_push] at hk
      have hpre : ∀ i, i ∈ Finset.range k →
          ((g.push (-(sumTo (fun i => f.coeff (d - (i + 1)) *
            (g[g.size - (i + 1)]?).getD 0) g.size)))[k - (i + 1)]?) = g[k - (i + 1)]? := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Array.getElem?_push]
        have : ¬(k - (i + 1) = g.size) := by omega
        simp only [this, ↓reduceIte]
      rw [Finset.sum_congr rfl fun i hi => by rw [hpre i hi]]
      by_cases hlt : k < g.size
      · rw [Array.getElem?_push]
        have : ¬(k = g.size) := by omega
        simp only [this, ↓reduceIte]
        exact h.2 k hk1 hlt
      · have hkeq : k = g.size := by omega
        subst hkeq
        rw [Array.getElem?_push]
        simp only [↓reduceIte, Option.getD_some, sumTo_eq]

/-- **`invRev f` inverts the reversed `f` modulo `X^(d−1)`**, for monic `f` of degree `d`. -/
theorem invRev_spec (f : AzPolynomial R) (hmon : f.leadingCoeff = 1) :
    ∀ j, j < f.natDegree - 1 →
      (reflect f.natDegree (AzPolynomial.toPoly f) * AzPolynomial.toPoly (invRev f)).coeff j =
        (1 : R[X]).coeff j := by
  intro j hj
  obtain ⟨d, hd⟩ : ∃ d, d = f.natDegree := ⟨_, rfl⟩
  rw [← hd] at hj ⊢
  have hinv : InvRevInv f d (invRevCoeffs f d (d - 2) #[1]) :=
    invRevCoeffs_inv f d (d - 2) #[1] (by simp) ⟨by simp, fun k hk1 hk => by simp at hk; omega⟩
  have hsize : (invRevCoeffs f d (d - 2) #[1]).size = d - 1 := by
    rw [invRevCoeffs_size]
    simp
    omega
  have hcoeff : ∀ k, (AzPolynomial.toPoly (invRev f)).coeff k =
      ((invRevCoeffs f d (d - 2) #[1])[k]?).getD 0 := by
    intro k
    rw [coeff_toPoly_eq, invRev, ← hd, coeff_normalize]
  have ha : ∀ i, i ≤ d → (reflect d (AzPolynomial.toPoly f)).coeff i = f.coeff (d - i) := by
    intro i hi
    rw [coeff_reflect, revAt_le hi, coeff_toPoly_eq]
  have ha0 : f.coeff d = 1 := by rw [hd]; exact hmon
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (reflect d (AzPolynomial.toPoly f)).coeff a *
      (AzPolynomial.toPoly (invRev f)).coeff b), Finset.sum_range_succ']
  simp only [Nat.sub_zero, hcoeff]
  rw [ha 0 (by omega), Nat.sub_zero, ha0, one_mul,
    Finset.sum_congr rfl fun i hi => by
      rw [ha (i + 1) (by rw [Finset.mem_range] at hi; omega)]]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp only [Finset.range_zero, Finset.sum_empty, zero_add, coeff_one_zero]
    exact hinv.1
  · have hj0 : ¬(j = 0) := by omega
    rw [hinv.2 j hjpos (by omega), coeff_one]
    simp only [hj0, ↓reduceIte]
    simp

variable [AzPolynomialMulConfig R]

omit [DecidableEq R] in
theorem ofFn_getElem?_getD {n : ℕ} (h : Fin n → R) (k : ℕ) :
    ((Array.ofFn h)[k]?).getD 0 = if hk : k < n then h ⟨k, hk⟩ else 0 := by
  rw [Array.getElem?_ofFn]
  split <;> rfl

/-- The quotient computed from the inverse is the quotient. -/
theorem toPoly_quotByInv (f g P : AzPolynomial R) (hmon : f.leadingCoeff = 1)
    (hg : ∀ j, j < f.natDegree - 1 →
      (reflect f.natDegree (AzPolynomial.toPoly f) * AzPolynomial.toPoly g).coeff j =
        (1 : R[X]).coeff j)
    (hP : P.coeffs.size ≤ 2 * f.natDegree - 1) (hPf : f.coeffs.size ≤ P.coeffs.size)
    (hf2 : 2 ≤ f.coeffs.size) :
    AzPolynomial.toPoly (quotByInv g P f.natDegree) =
      AzPolynomial.toPoly P /ₘ AzPolynomial.toPoly f := by
  obtain ⟨d, hd⟩ : ∃ d, d = f.natDegree := ⟨_, rfl⟩
  rw [← hd] at hg hP ⊢
  have hd2 : 2 ≤ d := by
    have : d = f.coeffs.size - 1 := hd
    omega
  have hF : (AzPolynomial.toPoly f).Monic := by
    unfold Polynomial.Monic
    rw [leadingCoeff_toPoly]
    exact hmon
  have hFd : (AzPolynomial.toPoly f).natDegree = d := by
    rw [AzPolynomial.natDegree_toPoly, hd]
  have hPd : (AzPolynomial.toPoly P).natDegree ≤ 2 * d - 2 := by
    rw [AzPolynomial.natDegree_toPoly]
    unfold natDegree
    omega
  ext i
  unfold quotByInv
  rw [coeff_toPoly_eq, coeff_normalize, ofFn_getElem?_getD]
  split
  · next hi =>
    rw [divByMonic_coeff_of_inverse hF hFd hPd hg i hi, ← coeff_toPoly_eq, toPoly_mul]
    refine coeff_mul_congr_left (n := d - 1) (fun k hk => ?_) _ (by omega)
    rw [coeff_toPoly_eq, coeff_normalize, ofFn_getElem?_getD, coeff_reflect,
      revAt_le (by omega), coeff_toPoly_eq]
    simp only [hk, ↓reduceDIte]
  · next hi =>
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_divByMonic _ hF, hFd]
    omega

/-- **The remainder by the precomputed inverse is the remainder.** -/
theorem modByMonicInv_eq (f P : AzPolynomial R) (hmon : f.leadingCoeff = 1) :
    modByMonicInv f (invRev f) P = modByMonic P f := by
  unfold modByMonicInv
  split
  · rfl
  · next hne =>
    have hf2 : 2 ≤ f.coeffs.size := by omega
    have hP : P.coeffs.size ≤ 2 * f.natDegree - 1 := by omega
    have hF : (AzPolynomial.toPoly f).Monic := by
      unfold Polynomial.Monic
      rw [leadingCoeff_toPoly]
      exact hmon
    have hf0 : AzPolynomial.toPoly f ≠ 0 := by
      intro h0
      have : f = 0 := by rwa [← toPoly_inj, toPoly_zero]
      rw [this] at hf2
      simp at hf2
    apply toPoly_inj.mp
    rw [toPoly_sub, toPoly_mul,
      toPoly_quotByInv f (invRev f) P hmon (invRev_spec f hmon) hP (by omega) hf2,
      toPoly_modByMonic hF hf0]
    have := modByMonic_add_div (AzPolynomial.toPoly P) (AzPolynomial.toPoly f)
    linear_combination -this

end Azurite.AzPolynomial
