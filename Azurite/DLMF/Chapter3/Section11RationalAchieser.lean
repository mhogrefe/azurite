/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11RationalExist
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain

/-!
# DLMF §3.11(iii): Achieser's theorem — characterization and uniqueness

The corrected form of "There exists a unique solution of this minimax problem and there are at
least `k + ℓ + 2` values `x_j` … such that `m_j = (−1)^j ε(x_j)` … and `±m` is the maximum".

For `R = P/Q` in lowest terms (`IsCoprime P Q`) let `D = max(k + deg Q, ℓ + deg P)` (`D = k` for
`P = 0`), so that `N = D + 2 = k + ℓ + 2 − d` with the defect `d = k + ℓ − D` (`ratD`,
`ratDefect`). Then:

* `dlmf_3_11_iii_characterization`: `R` is minimax iff `ε` equioscillates (3.11.18) at `N`
  points;
* `dlmf_3_11_iii_unique`: the minimax approximation is unique (as a function on `[a, b]`);
* `dlmf_3_11_iii_alternation`: the minimax approximation in lowest terms equioscillates at
  `k + ℓ + 2 − d` points, and at `k + ℓ + 2` points when it is nondegenerate (`d = 0`).

Ingredients:

* `eq_zero_of_weak_alternates`: a polynomial of degree `≤ n` with `(−1)^j V(x_j) ≥ 0` at `n + 2`
  points vanishes (the top divided difference, Mathlib's `Lagrange.coeff_eq_sum`);
* `natDegree_cross_le_ratD` and `exists_cross_eq` (Bezout): `{pQ − Pq}` is exactly the
  polynomials of degree `≤ D`;
* `exists_poly_sign`: if two disjoint compact sets admit no alternating sequence of length
  `n + 2`, some polynomial of degree `≤ n` is positive on one and negative on the other;
* `alternation_of_minimax`: perturbing `P/Q` to `(P − tp)/(Q − tq)` with `pQ − Pq` of the sign of
  `ε` on the extremal set lowers the error unless the error equioscillates at `N` points;
* `exists_coprime_rep`: reduction to lowest terms.
-/

open Polynomial Set Filter Topology

namespace Azurite.DLMF

/-! ### Weak alternation -/

theorem prod_sub_sign {n : ℕ} {x : Fin (n + 2) → ℝ} (hx : StrictMono x) (i : Fin (n + 2)) :
    0 < (-1) ^ (n + 1 - (i : ℕ)) * ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  have hsplit : Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => by
      rcases h with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h⟩
  have hdisj : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_Iio, Finset.mem_Ioi] at h1 h2
    exact absurd (h1.trans h2) (lt_irrefl _)
  have hcard : (Finset.Ioi i).card = n + 1 - (i : ℕ) := by
    simp [Fin.card_Ioi]
  rw [hsplit, Finset.prod_union hdisj, ← hcard, ← Finset.prod_const, mul_comm, mul_assoc,
    ← Finset.prod_mul_distrib]
  apply mul_pos
  · exact Finset.prod_pos fun j hj => sub_pos.mpr (hx (Finset.mem_Iio.mp hj))
  · exact Finset.prod_pos fun j hj => by
      have := hx (Finset.mem_Ioi.mp hj); linarith

/-- A polynomial of degree `≤ n` with `(−1)^j V(x_j) ≥ 0` at `n + 2` increasing points
vanishes. -/
theorem eq_zero_of_weak_alternates {n : ℕ} {V : ℝ[X]} (hV : V.natDegree ≤ n)
    {x : Fin (n + 2) → ℝ} (hx : StrictMono x)
    (h : ∀ j : Fin (n + 2), 0 ≤ (-1) ^ (j : ℕ) * V.eval (x j)) :
    V = 0 := by
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin (n + 2))) := fun i _ j _ hij =>
    hx.injective hij
  have hdeg : V.degree < (Finset.univ : Finset (Fin (n + 2))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (show V.natDegree < n + 2 by omega))
  have hsum := Lagrange.coeff_eq_sum hinj hdeg
  rw [Finset.card_univ, Fintype.card_fin, show n + 2 - 1 = n + 1 by omega,
    coeff_eq_zero_of_natDegree_lt (by omega)] at hsum
  -- every term has the sign of `(−1)^{n+1}`
  have hterm : ∀ i : Fin (n + 2), 0 ≤ (-1) ^ (n + 1) *
      (V.eval (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)) := fun i => by
    have hp := prod_sub_sign hx i
    have hi := h i
    have e : (-1 : ℝ) ^ (n + 1) = (-1) ^ (i : ℕ) * (-1) ^ (n + 1 - (i : ℕ)) := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    rcases neg_one_pow_eq_or ℝ (n + 1 - (i : ℕ)) with hm | hm <;> rw [hm] at hp ⊢
    · rw [one_mul] at hp
      rw [mul_one, mul_div_assoc']
      exact div_nonneg hi hp.le
    · have hp' : 0 < -∏ j ∈ Finset.univ.erase i, (x i - x j) := by linarith
      rw [show (-1 : ℝ) ^ (i : ℕ) * -1 * (V.eval (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)) =
        ((-1) ^ (i : ℕ) * V.eval (x i)) / -∏ j ∈ Finset.univ.erase i, (x i - x j) by
          rw [div_neg]; ring]
      exact div_nonneg hi hp'.le
  have hzero : ∀ i : Fin (n + 2), V.eval (x i) = 0 := by
    have hs : ∑ i, (-1) ^ (n + 1) * (V.eval (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j)) =
        0 := by
      rw [← Finset.mul_sum, ← hsum, mul_zero]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hs i (Finset.mem_univ i)
    have hp := (prod_sub_sign hx i).ne'
    have hp' : ∏ j ∈ Finset.univ.erase i, (x i - x j) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hp; exact hp rfl
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hp'
  exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero V hx.injective hzero (by simp; omega)

/-! ### The degree `D` and the space `{pQ − Pq}` -/

/-- `D = max(k + deg Q, ℓ + deg P)` (`= k` for `P = 0`); `N = D + 2` alternation points. -/
noncomputable def ratD (k ℓ : ℕ) (P Q : ℝ[X]) : ℕ :=
  if P = 0 then k else max (k + Q.natDegree) (ℓ + P.natDegree)

/-- The defect `d = k + ℓ − D` (`= min(k − deg P, ℓ − deg Q)` for `P ≠ 0`). -/
noncomputable def ratDefect (k ℓ : ℕ) (P Q : ℝ[X]) : ℕ := k + ℓ - ratD k ℓ P Q

theorem ratD_le {k ℓ : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ ℓ) :
    ratD k ℓ P Q ≤ k + ℓ := by
  unfold ratD; split_ifs <;> omega

theorem natDegree_eq_zero_of_coprime_zero {Q : ℝ[X]} (h : IsCoprime (0 : ℝ[X]) Q) :
    Q.natDegree = 0 :=
  natDegree_eq_zero_of_isUnit (isCoprime_zero_left.mp h)

/-- Competitors differ by numerators of degree `≤ D`. -/
theorem natDegree_cross_le_ratD {k ℓ : ℕ} {P Q P' Q' : ℝ[X]} (hcop : IsCoprime P Q)
    (hP' : P'.natDegree ≤ k) (hQ' : Q'.natDegree ≤ ℓ) :
    (P' * Q - P * Q').natDegree ≤ ratD k ℓ P Q := by
  unfold ratD
  split_ifs with hP0
  · subst hP0
    rw [zero_mul, sub_zero]
    exact natDegree_mul_le.trans (by rw [natDegree_eq_zero_of_coprime_zero hcop]; omega)
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_mul_le.trans (le_max_of_le_left (by omega))
    · exact natDegree_mul_le.trans (le_max_of_le_right (by omega))

/-- **Bezout**: every polynomial of degree `≤ D` is `pQ − Pq` with `deg p ≤ k`, `deg q ≤ ℓ`. -/
theorem exists_cross_eq {k ℓ : ℕ} {P Q : ℝ[X]} (hcop : IsCoprime P Q) (hQ0 : Q ≠ 0)
    (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ ℓ) {u : ℝ[X]} (hu : u.natDegree ≤ ratD k ℓ P Q) :
    ∃ p q : ℝ[X], p.natDegree ≤ k ∧ q.natDegree ≤ ℓ ∧ p * Q - P * q = u := by
  by_cases hP0 : P = 0
  · subst hP0
    have hQc := natDegree_eq_zero_of_coprime_zero hcop
    simp only [ratD, ↓reduceIte] at hu
    set c := Q.coeff 0
    have hQC : Q = C c := eq_C_of_natDegree_eq_zero hQc
    have hc : c ≠ 0 := fun h0 => hQ0 (by rw [hQC, h0, C_0])
    refine ⟨u * C c⁻¹, 0, (natDegree_mul_le.trans (by simp; omega)), by simp, ?_⟩
    rw [hQC, zero_mul, sub_zero, mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, mul_one]
  obtain ⟨A, B, hAB⟩ := hcop
  simp only [ratD, hP0, ↓reduceIte] at hu
  -- `u = (uB)Q − P(−uA)`
  set p0 := u * B
  set q0 := -(u * A)
  have h0 : p0 * Q - P * q0 = u := by
    simp only [p0, q0]; linear_combination u * hAB
  by_cases hcase : ℓ + P.natDegree ≤ k + Q.natDegree
  · -- reduce `q₀` modulo `Q`
    set s := q0 / Q
    set q := q0 % Q
    have hq0 : q0 = Q * s + q := (EuclideanDomain.div_add_mod q0 Q).symm
    refine ⟨p0 - P * s, q, ?_, ?_, ?_⟩
    · -- `(p₀ − Ps)Q = u + Pq` has degree `≤ D`
      have hkey : (p0 - P * s) * Q = u + P * q := by
        rw [← h0, hq0]; ring
      by_cases hpz : p0 - P * s = 0
      · rw [hpz]; simp
      have hdeg := congrArg natDegree hkey
      rw [natDegree_mul hpz hQ0] at hdeg
      have hPq : (P * q).natDegree ≤ k + Q.natDegree := by
        by_cases hq : q = 0
        · rw [hq, mul_zero, natDegree_zero]; exact Nat.zero_le _
        · have hqd : q.natDegree < Q.natDegree :=
            natDegree_lt_natDegree hq (EuclideanDomain.mod_lt q0 hQ0)
          exact natDegree_mul_le.trans (by omega)
      have : (u + P * q).natDegree ≤ k + Q.natDegree :=
        (natDegree_add_le _ _).trans (max_le (hu.trans (by omega)) hPq)
      omega
    · by_cases hq : q = 0
      · rw [hq, natDegree_zero]; exact Nat.zero_le _
      · exact (natDegree_lt_natDegree hq (EuclideanDomain.mod_lt q0 hQ0)).le.trans hQ
    · rw [← h0, hq0]; ring
  · -- reduce `p₀` modulo `P`
    push Not at hcase
    set s := p0 / P
    set p := p0 % P
    have hp0 : p0 = P * s + p := (EuclideanDomain.div_add_mod p0 P).symm
    refine ⟨p, q0 - Q * s, ?_, ?_, ?_⟩
    · by_cases hp : p = 0
      · rw [hp, natDegree_zero]; exact Nat.zero_le _
      · exact (natDegree_lt_natDegree hp (EuclideanDomain.mod_lt p0 hP0)).le.trans hP
    · have hkey : P * (q0 - Q * s) = p * Q - u := by
        rw [← h0, hp0]; ring
      by_cases hqz : q0 - Q * s = 0
      · rw [hqz]; simp
      have hdeg := congrArg natDegree hkey
      rw [natDegree_mul hP0 hqz] at hdeg
      have hpQ : (p * Q).natDegree ≤ ℓ + P.natDegree := by
        by_cases hp : p = 0
        · rw [hp, zero_mul, natDegree_zero]; exact Nat.zero_le _
        · have hpd : p.natDegree < P.natDegree :=
            natDegree_lt_natDegree hp (EuclideanDomain.mod_lt p0 hP0)
          exact natDegree_mul_le.trans (by omega)
      have : (p * Q - u).natDegree ≤ ℓ + P.natDegree :=
        (natDegree_sub_le _ _).trans (max_le hpQ (hu.trans (by omega)))
      omega
    · rw [← h0, hp0]; ring

/-! ### Reduction to lowest terms -/

/-- Every admissible `P/Q` has an admissible representative in lowest terms with the same values
on `[a, b]`. -/
theorem exists_coprime_rep {a b : ℝ} (hab : a ≤ b) {k ℓ : ℕ} {P Q : ℝ[X]}
    (hPQ : RatAdmissible a b k ℓ P Q) :
    ∃ P' Q' : ℝ[X], RatAdmissible a b k ℓ P' Q' ∧ IsCoprime P' Q' ∧
      ∀ x ∈ Icc a b, P'.eval x / Q'.eval x = P.eval x / Q.eval x := by
  have hQ0 : Q ≠ 0 := fun h0 => by
    have := hPQ.2.2 a (left_mem_Icc.mpr hab); rw [h0, eval_zero] at this; exact lt_irrefl _ this
  classical
  let _ : GCDMonoid ℝ[X] := EuclideanDomain.gcdMonoid ℝ[X]
  set g := GCDMonoid.gcd P Q
  have hg0 : g ≠ 0 := gcd_ne_zero_of_right hQ0
  have hgP : g * (P / g) = P := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left P Q)
  have hgQ : g * (Q / g) = Q := EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right P Q)
  have hcop : IsCoprime (P / g) (Q / g) := isCoprime_div_gcd_div_gcd hQ0
  have hQg0 : Q / g ≠ 0 := fun h0 => hQ0 (by rw [← hgQ, h0, mul_zero])
  have hgx : ∀ x ∈ Icc a b, g.eval x ≠ 0 := fun x hx h0 => by
    have := hPQ.2.2 x hx; rw [← hgQ, eval_mul, h0, zero_mul] at this; exact lt_irrefl _ this
  -- `g` has constant sign
  set σ : ℝ := if 0 < g.eval a then 1 else -1
  have hσ : ∀ x ∈ Icc a b, 0 < σ * g.eval x := fun x hx => by
    have h1 := weight_mul_pos g.continuous.continuousOn hgx hx (left_mem_Icc.mpr hab)
    have ha := hgx a (left_mem_Icc.mpr hab)
    simp only [σ]
    split_ifs with h
    · rw [one_mul]; exact pos_of_mul_pos_left h1 h.le
    · push Not at h
      have : g.eval a < 0 := lt_of_le_of_ne h ha
      nlinarith
  have hσ2 : σ = 1 ∨ σ = -1 := by simp only [σ]; split_ifs <;> simp
  have hσ0 : σ ≠ 0 := by rcases hσ2 with h | h <;> rw [h] <;> norm_num
  have hdegP : (P / g).natDegree ≤ P.natDegree := by
    by_cases hP0 : P / g = 0
    · rw [hP0, natDegree_zero]; exact Nat.zero_le _
    · conv_rhs => rw [← hgP]
      rw [natDegree_mul hg0 hP0]; omega
  have hdegQ : (Q / g).natDegree ≤ Q.natDegree := by
    conv_rhs => rw [← hgQ]
    rw [natDegree_mul hg0 hQg0]; omega
  refine ⟨C σ * (P / g), C σ * (Q / g), ⟨(natDegree_C_mul_le _ _).trans (hdegP.trans hPQ.1),
    (natDegree_C_mul_le _ _).trans (hdegQ.trans hPQ.2.1), fun x hx => ?_⟩, ?_, fun x hx => ?_⟩
  · simp only [eval_mul, eval_C]
    have h1 := hPQ.2.2 x hx
    rw [← hgQ, eval_mul] at h1
    have h2 := hσ x hx
    -- `σ (Q/g)(x) = (σ g(x))⁻¹ Q(x) ... > 0`
    have : 0 < (σ * g.eval x) * (σ * (Q / g).eval x) := by
      have e : (σ * g.eval x) * (σ * (Q / g).eval x) = (σ * σ) * (g.eval x * (Q / g).eval x) := by
        ring
      rw [e, show σ * σ = 1 by rcases hσ2 with h | h <;> rw [h] <;> norm_num, one_mul]
      exact h1
    exact pos_of_mul_pos_right this h2.le
  · obtain ⟨u, v, huv⟩ := hcop
    have hc : C σ⁻¹ * C σ = 1 := by rw [← C_mul, inv_mul_cancel₀ hσ0, C_1]
    exact ⟨C σ⁻¹ * u, C σ⁻¹ * v, by linear_combination (u * (P / g) + v * (Q / g)) * hc + huv⟩
  · simp only [eval_mul, eval_C]
    conv_rhs => rw [← hgP, ← hgQ]
    simp only [eval_mul]
    rw [mul_div_mul_left _ _ hσ0, mul_div_mul_left _ _ (hgx x hx)]

/-! ### Alternation lower bound with a general degree -/

variable {a b : ℝ}

theorem ratMaxErr_congr {f w : ℝ → ℝ} {P Q P' Q' : ℝ[X]}
    (h : ∀ x ∈ Icc a b, ratErr f w P Q x = ratErr f w P' Q' x) :
    ratMaxErr a b f w P Q = ratMaxErr a b f w P' Q' := by
  unfold ratMaxErr
  congr 1
  exact Set.image_congr fun x hx => by rw [h x hx]

/-- de la Vallée-Poussin with numerators of degree `≤ n`: an alternation of `n + 2` points with
magnitude `≥ μ` forces every competitor to have error `≥ μ`. -/
theorem vallee_poussin_deg {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {n k ℓ : ℕ} {P Q : ℝ[X]}
    (hPQ : RatAdmissible a b k ℓ P Q) {x : Fin (n + 2) → ℝ} (hx : StrictMono x)
    (hxI : ∀ j, x j ∈ Icc a b) {s μ : ℝ} (hs : s = 1 ∨ s = -1)
    (hμ : ∀ j : Fin (n + 2), μ ≤ s * (-1) ^ (j : ℕ) * ratErr f w P Q (x j)) {P' Q' : ℝ[X]}
    (hPQ' : RatAdmissible a b k ℓ P' Q') (hdeg : (P' * Q - P * Q').natDegree ≤ n) :
    μ ≤ ratMaxErr a b f w P' Q' := by
  by_contra hlt
  push Not at hlt
  have hQ' : ∀ y ∈ Icc a b, Q'.eval y ≠ 0 := fun y hy => (hPQ'.2.2 y hy).ne'
  have hlt' : ∀ j, |ratErr f w P' Q' (x j)| < μ := fun j =>
    lt_of_le_of_lt (abs_ratErr_le hf hw hw0 hQ' (hxI j)) hlt
  refine not_alternates hdeg hx fun j => ?_
  have hj1 := hxI j.castSucc
  have hj2 := hxI j.succ
  rw [cross_eval_eq (f := f) (w := w) (hPQ.2.2 _ hj1).ne' (hQ' _ hj1) (hw0 _ hj1),
    cross_eval_eq (f := f) (w := w) (hPQ.2.2 _ hj2).ne' (hQ' _ hj2) (hw0 _ hj2)]
  set t : ℝ := s * (-1) ^ (j : ℕ) with ht
  have habs : |t| = 1 := by rcases hs with rfl | rfl <;> simp [ht, abs_pow]
  have ht2 : t * t = 1 := by
    rcases hs with rfl | rfl <;> simp [ht, ← pow_add, ← two_mul, pow_mul]
  set e1 := ratErr f w P' Q' (x j.castSucc)
  set e2 := ratErr f w P' Q' (x j.succ)
  set c1 := ratErr f w P Q (x j.castSucc)
  set c2 := ratErr f w P Q (x j.succ)
  have h1 : μ ≤ t * c1 := by have := hμ j.castSucc; simpa [Fin.val_castSucc, ← ht] using this
  have h2' : μ ≤ -(t * c2) := by
    have := hμ j.succ
    have e : s * (-1) ^ ((j.succ : Fin (n + 2)) : ℕ) * c2 = -(t * c2) := by
      rw [Fin.val_succ, pow_succ, ht]; ring
    linarith
  have key : (e1 - c1) * (e2 - c2) < 0 := by
    have hte1 : |t * e1| < μ := by rw [abs_mul, habs, one_mul]; exact hlt' j.castSucc
    have hte2 : |t * e2| < μ := by rw [abs_mul, habs, one_mul]; exact hlt' j.succ
    have k1 : t * (e1 - c1) < 0 := by have := (abs_lt.mp hte1).2; nlinarith
    have k2 : 0 < t * (e2 - c2) := by have := (abs_lt.mp hte2).1; nlinarith
    have := mul_neg_of_neg_of_pos k1 k2
    have e : (t * (e1 - c1)) * (t * (e2 - c2)) = (t * t) * ((e1 - c1) * (e2 - c2)) := by ring
    rw [e, ht2, one_mul] at this
    exact this
  have hww := weight_mul_pos hw hw0 hj1 hj2
  have hpos : 0 < (w (x j.castSucc) * w (x j.succ)) *
      (Q'.eval (x j.castSucc) * Q.eval (x j.castSucc)) *
        (Q'.eval (x j.succ) * Q.eval (x j.succ)) := by
    have := hPQ'.2.2 _ hj1; have := hPQ'.2.2 _ hj2; have := hPQ.2.2 _ hj1; have := hPQ.2.2 _ hj2
    positivity
  have e : (e1 - c1) * w (x j.castSucc) * Q'.eval (x j.castSucc) * Q.eval (x j.castSucc) *
      ((e2 - c2) * w (x j.succ) * Q'.eval (x j.succ) * Q.eval (x j.succ)) =
      ((e1 - c1) * (e2 - c2)) * ((w (x j.castSucc) * w (x j.succ)) *
        (Q'.eval (x j.castSucc) * Q.eval (x j.castSucc)) *
          (Q'.eval (x j.succ) * Q.eval (x j.succ))) := by ring
  rw [e]
  exact mul_neg_of_neg_of_pos key hpos

/-! ### Separating the extremal sets by a polynomial -/

/-- An alternating sequence of length `m`: increasing points, in `A` at even and `B` at odd
indices. -/
def AltSeq (A B : Set ℝ) (m : ℕ) : Prop :=
  ∃ x : ℕ → ℝ, (∀ i j, i < j → j < m → x i < x j) ∧ ∀ j < m, x j ∈ (if Even j then A else B)

theorem AltSeq.of_succ {A B : Set ℝ} {m : ℕ} (h : AltSeq A B (m + 1)) : AltSeq A B m := by
  obtain ⟨x, hx, hm⟩ := h
  exact ⟨x, fun i j hij hj => hx i j hij (by omega), fun j hj => hm j (by omega)⟩

theorem AltSeq.snoc' {A B : Set ℝ} {m : ℕ} {x : ℕ → ℝ} (hx : ∀ i j, i < j → j < m → x i < x j)
    (hm : ∀ j < m, x j ∈ (if Even j then A else B)) {y : ℝ} (hy : ∀ j < m, x j < y)
    (hyA : y ∈ (if Even m then A else B)) :
    ∃ x' : ℕ → ℝ, (∀ i j, i < j → j < m + 1 → x' i < x' j) ∧
      (∀ j < m + 1, x' j ∈ (if Even j then A else B)) ∧ ∀ j < m + 1, x' j ≤ y := by
  refine ⟨fun j => if j < m then x j else y, fun i j hij hj => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · have hi : i < m := by omega
    by_cases hjm : j < m
    · simp only [hi, hjm, ↓reduceIte]; exact hx i j hij hjm
    · simp only [hi, hjm, ↓reduceIte]; exact hy i hi
  · by_cases hjm : j < m
    · simp only [hjm, ↓reduceIte]; exact hm j hjm
    · have : j = m := by omega
      subst this; simp only [lt_irrefl, ↓reduceIte]; exact hyA
  · by_cases hjm : j < m
    · simp only [hjm, ↓reduceIte]; exact (hy j hjm).le
    · simp only [hjm, ↓reduceIte]; exact le_rfl

/-- Appending a point and then another. -/
theorem AltSeq.snoc2 {A B : Set ℝ} {m : ℕ} {x : ℕ → ℝ} (hx : ∀ i j, i < j → j < m → x i < x j)
    (hm : ∀ j < m, x j ∈ (if Even j then A else B)) {y y' : ℝ} (hy : ∀ j < m, x j < y)
    (hyy : y < y') (hyA : y ∈ (if Even m then A else B))
    (hyA' : y' ∈ (if Even (m + 1) then A else B)) : AltSeq A B (m + 2) := by
  obtain ⟨x', hx', hm', hle⟩ := AltSeq.snoc' hx hm hy hyA
  obtain ⟨x'', hx'', hm'', -⟩ := AltSeq.snoc' hx' hm' (fun j hj => (hle j hj).trans_lt hyy) hyA'
  exact ⟨x'', hx'', hm''⟩

theorem AltSeq.snoc1 {A B : Set ℝ} {m : ℕ} {x : ℕ → ℝ} (hx : ∀ i j, i < j → j < m → x i < x j)
    (hm : ∀ j < m, x j ∈ (if Even j then A else B)) {y : ℝ} (hy : ∀ j < m, x j < y)
    (hyA : y ∈ (if Even m then A else B)) : AltSeq A B (m + 1) := by
  obtain ⟨x', hx', hm', -⟩ := AltSeq.snoc' hx hm hy hyA
  exact ⟨x', hx', hm'⟩

/-- The induction step: the maximum of `A ∪ B` lies in `A`. -/
theorem exists_poly_sign_step {n : ℕ}
    (ih : ∀ A B : Set ℝ, IsCompact A → IsCompact B → Disjoint A B → ¬ AltSeq A B (n + 2) →
      ¬ AltSeq B A (n + 2) → ∃ u : ℝ[X], u.natDegree ≤ n ∧ (∀ x ∈ A, 0 < u.eval x) ∧
        (∀ x ∈ B, u.eval x < 0) ∧ ∀ y, (∀ x ∈ A ∪ B, x ≤ y) → u.eval y ≠ 0)
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B) (hd : Disjoint A B)
    (hAB : ¬ AltSeq A B (n + 3)) (hBA : ¬ AltSeq B A (n + 3)) (hBne : B.Nonempty)
    {M : ℝ} (hMA : M ∈ A) (hMmax : ∀ x ∈ A ∪ B, x ≤ M) :
    ∃ u : ℝ[X], u.natDegree ≤ n + 1 ∧ (∀ x ∈ A, 0 < u.eval x) ∧ (∀ x ∈ B, u.eval x < 0) ∧
      ∀ y, (∀ x ∈ A ∪ B, x ≤ y) → u.eval y ≠ 0 := by
  have hdisj : ∀ x ∈ A, x ∉ B := fun x hx hxB => Set.disjoint_left.mp hd hx hxB
  set m' := sSup B
  have hm'B : m' ∈ B := hB.sSup_mem hBne
  have hBle : ∀ x ∈ B, x ≤ m' := fun x hx => le_csSup hB.bddAbove hx
  have hm'M : m' < M := lt_of_le_of_ne (hMmax m' (Or.inr hm'B)) fun h => hdisj M hMA (h ▸ hm'B)
  set T := A ∩ Icc m' M
  have hT : IsCompact T := hA.inter_right isClosed_Icc
  have hTne : T.Nonempty := ⟨M, hMA, hm'M.le, le_rfl⟩
  set r := sInf T
  have hrT : r ∈ T := hT.sInf_mem hTne
  have hr : m' < r := lt_of_le_of_ne hrT.2.1 fun h => hdisj r hrT.1 (h ▸ hm'B)
  set z := (m' + r) / 2
  have hz1 : m' < z := by simp only [z]; linarith
  have hz2 : z < r := by simp only [z]; linarith
  -- points of `A` not beyond `z` lie below `m′`
  have hF1 : ∀ x ∈ A, x ≤ z → x < m' := fun x hx hxz => by
    by_contra hge
    push Not at hge
    have hxT : x ∈ T := ⟨hx, hge, hMmax x (Or.inl hx)⟩
    have := csInf_le hT.bddBelow hxT
    linarith
  set A' := A ∩ Iic z
  have hA' : IsCompact A' := hA.inter_right isClosed_Iic
  have hA'A : A' ⊆ A := Set.inter_subset_left
  have hd' : Disjoint A' B := hd.mono_left hA'A
  have hlt_m : ∀ x ∈ A' ∪ B, x ≤ m' := fun x hx => by
    rcases hx with hx | hx
    · exact (hF1 x hx.1 hx.2).le
    · exact hBle x hx
  -- a sequence on the left part, lifted to `A, B` and bounded by its last point
  have hlift : ∀ {P1 P2 : Set ℝ}, P1 ⊆ P2 → ∀ {y : ℕ → ℝ} {L : ℕ},
      (∀ j < L, y j ∈ (if Even j then P1 else B)) → ∀ j < L, y j ∈ (if Even j then P2 else B) :=
    fun hsub y L h j hj => by have := h j hj; split_ifs at this ⊢; exacts [hsub this, this]
  have hlift' : ∀ {P1 P2 : Set ℝ}, P1 ⊆ P2 → ∀ {y : ℕ → ℝ} {L : ℕ},
      (∀ j < L, y j ∈ (if Even j then B else P1)) → ∀ j < L, y j ∈ (if Even j then B else P2) :=
    fun hsub y L h j hj => by have := h j hj; split_ifs at this ⊢; exacts [this, hsub this]
  have hbelow : ∀ {y : ℕ → ℝ} {L : ℕ}, (∀ i j, i < j → j < L → y i < y j) →
      (∀ j < L, y j ∈ A' ∪ B) → ∀ j < L, y j ≤ m' := fun _ hy j hj => hlt_m _ (hy j hj)
  have hno1 : ¬ AltSeq A' B (n + 2) := by
    rintro ⟨y, hy, hym⟩
    have hmem := hlift hA'A hym
    have hin : ∀ j < n + 2, y j ∈ A' ∪ B := fun j hj => by
      have := hym j hj; split_ifs at this; exacts [Or.inl this, Or.inr this]
    by_cases hev : Even (n + 1)
    · have hlast : y (n + 1) ∈ A' := by have := hym (n + 1) (by omega); simpa [hev] using this
      have hlt : y (n + 1) < m' := hF1 _ hlast.1 hlast.2
      have hall : ∀ j < n + 2, y j < m' := fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact (hy j (n + 1) h (by omega)).trans hlt
        · rw [h]; exact hlt
      have hodd : ¬ Even (n + 2) := by rw [Nat.even_add_one]; exact not_not.mpr hev
      have heven : Even (n + 2 + 1) := by
        rw [show n + 2 + 1 = (n + 1) + 2 by ring]; exact hev.add even_two
      exact hAB ((AltSeq.snoc2 hy hmem hall hm'M (by simpa [hodd] using hm'B)
        (by simpa [heven] using hMA)).of_succ)
    · have hlast : y (n + 1) ∈ B := by have := hym (n + 1) (by omega); simpa [hev] using this
      have heven : Even (n + 2) := by rw [Nat.even_add_one]; exact hev
      exact hAB (AltSeq.snoc1 hy hmem (fun j hj => (hbelow hy hin j hj).trans_lt hm'M)
        (by simpa [heven] using hMA))
  have hno2 : ¬ AltSeq B A' (n + 2) := by
    rintro ⟨y, hy, hym⟩
    have hmem := hlift' hA'A hym
    have hin : ∀ j < n + 2, y j ∈ A' ∪ B := fun j hj => by
      have := hym j hj; split_ifs at this; exacts [Or.inr this, Or.inl this]
    by_cases hev : Even (n + 1)
    · have hlast : y (n + 1) ∈ B := by have := hym (n + 1) (by omega); simpa [hev] using this
      have hodd : ¬ Even (n + 2) := by rw [Nat.even_add_one]; exact not_not.mpr hev
      exact hBA (AltSeq.snoc1 hy hmem (fun j hj => (hbelow hy hin j hj).trans_lt hm'M)
        (by simpa [hodd] using hMA))
    · have hlast : y (n + 1) ∈ A' := by have := hym (n + 1) (by omega); simpa [hev] using this
      have hlt : y (n + 1) < m' := hF1 _ hlast.1 hlast.2
      have hall : ∀ j < n + 2, y j < m' := fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact (hy j (n + 1) h (by omega)).trans hlt
        · rw [h]; exact hlt
      have heven : Even (n + 2) := by rw [Nat.even_add_one]; exact hev
      have hodd : ¬ Even (n + 2 + 1) := by rw [Nat.even_add_one]; exact not_not.mpr heven
      exact hBA ((AltSeq.snoc2 hy hmem hall hm'M (by simpa [heven] using hm'B)
        (by simpa [hodd] using hMA)).of_succ)
  obtain ⟨u0, hu0d, hu0A, hu0B, hu0r⟩ := ih A' B hA' hB hd' hno1 hno2
  -- `u₀ < 0` from `m′` on
  have hneg : ∀ y, m' ≤ y → u0.eval y < 0 := by
    intro y hy
    by_contra hge
    push Not at hge
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hy u0.continuous.continuousOn
      (show (0 : ℝ) ∈ Icc (u0.eval m') (u0.eval y) from ⟨(hu0B m' hm'B).le, hge⟩)
    exact hu0r c (fun x hx => (hlt_m x hx).trans hc.1) hc0
  refine ⟨u0 * (C z - X), ?_, fun x hx => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · refine natDegree_mul_le.trans ?_
    have : (C z - X).natDegree ≤ 1 := by
      rw [show C z - X = -(X - C z) by ring, natDegree_neg, natDegree_X_sub_C]
    omega
  · simp only [eval_mul, eval_sub, eval_C, eval_X]
    by_cases hxz : x ≤ z
    · have h1 := hu0A x ⟨hx, hxz⟩
      have h2 := hF1 x hx hxz
      exact mul_pos h1 (by linarith)
    · push Not at hxz
      have h1 := hneg x (by linarith)
      exact mul_pos_of_neg_of_neg h1 (by linarith)
  · simp only [eval_mul, eval_sub, eval_C, eval_X]
    have h1 := hu0B x hx
    have h2 := hBle x hx
    exact mul_neg_of_neg_of_pos h1 (by linarith)
  · simp only [eval_mul, eval_sub, eval_C, eval_X]
    have hyM := hy M (Or.inl hMA)
    have hrM := hrT.2.2
    exact mul_ne_zero (hneg y (by linarith)).ne (sub_neg.mpr (by linarith)).ne

/-- **Separation**: if two disjoint compact sets admit no alternating sequence of length
`n + 2` (in either order), some polynomial of degree `≤ n` is positive on the first and negative
on the second (and has no zero to the right of both). -/
theorem exists_poly_sign (n : ℕ) : ∀ A B : Set ℝ, IsCompact A → IsCompact B → Disjoint A B →
    ¬ AltSeq A B (n + 2) → ¬ AltSeq B A (n + 2) → ∃ u : ℝ[X], u.natDegree ≤ n ∧
      (∀ x ∈ A, 0 < u.eval x) ∧ (∀ x ∈ B, u.eval x < 0) ∧
        ∀ y, (∀ x ∈ A ∪ B, x ≤ y) → u.eval y ≠ 0 := by
  -- if one set is empty, a constant works
  have hconst : ∀ A B : Set ℝ, (A = ∅ ∨ B = ∅) → ∃ u : ℝ[X], u.natDegree ≤ 0 ∧
      (∀ x ∈ A, 0 < u.eval x) ∧ (∀ x ∈ B, u.eval x < 0) ∧
        ∀ y, (∀ x ∈ A ∪ B, x ≤ y) → u.eval y ≠ 0 := by
    intro A B h
    rcases h with h | h
    · exact ⟨C (-1), by simp, by simp [h], fun _ _ => by simp, fun _ _ => by simp⟩
    · exact ⟨C 1, by simp, fun _ _ => by simp, by simp [h], fun _ _ => by simp⟩
  induction n with
  | zero =>
    intro A B hA hB hd hAB hBA
    refine hconst A B ?_
    by_contra hne
    push Not at hne
    obtain ⟨p, hp⟩ := hne.1
    obtain ⟨q, hq⟩ := hne.2
    have hpq : p ≠ q := fun h => Set.disjoint_left.mp hd hp (h ▸ hq)
    rcases lt_or_gt_of_ne hpq with h | h
    · exact hAB ⟨fun j => if j = 0 then p else q, fun i j hij hj => by
        have : i = 0 := by omega
        have : j = 1 := by omega
        subst_vars; simpa using h, fun j hj => by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [hp, hq]⟩
    · exact hBA ⟨fun j => if j = 0 then q else p, fun i j hij hj => by
        have : i = 0 := by omega
        have : j = 1 := by omega
        subst_vars; simpa using h, fun j hj => by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [hp, hq]⟩
  | succ n ih =>
    intro A B hA hB hd hAB hBA
    by_cases hemp : A = ∅ ∨ B = ∅
    · obtain ⟨u, hu, h1, h2, h3⟩ := hconst A B hemp
      exact ⟨u, hu.trans (Nat.zero_le _), h1, h2, h3⟩
    push Not at hemp
    have hAne := hemp.1
    have hBne := hemp.2
    have hU : IsCompact (A ∪ B) := hA.union hB
    have hUne : (A ∪ B).Nonempty := hAne.mono Set.subset_union_left
    set M := sSup (A ∪ B)
    have hMU : M ∈ A ∪ B := hU.sSup_mem hUne
    have hMmax : ∀ x ∈ A ∪ B, x ≤ M := fun x hx => le_csSup hU.bddAbove hx
    rcases hMU with hMA | hMB
    · exact exists_poly_sign_step ih hA hB hd hAB hBA hBne hMA hMmax
    · obtain ⟨u, hu, h1, h2, h3⟩ := exists_poly_sign_step ih hB hA hd.symm hBA hAB hAne hMB
        (fun x hx => hMmax x (Set.union_comm A B ▸ hx))
      refine ⟨-u, by rwa [natDegree_neg], fun x hx => ?_, fun x hx => ?_, fun y hy => ?_⟩
      · simp only [eval_neg]; linarith [h2 x hx]
      · simp only [eval_neg]; linarith [h1 x hx]
      · simp only [eval_neg, neg_ne_zero]
        exact h3 y fun x hx => hy x (Set.union_comm A B ▸ hx)

/-! ### Necessity: a minimax approximation equioscillates at `D + 2` points -/

theorem abs_sub_le_max_of_mul_nonneg {e h : ℝ} (heh : 0 ≤ e * h) :
    |e - h| ≤ max (|e| - |h|) |h| := by
  rcases le_total 0 e with he | he <;> rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg he, abs_of_nonneg hh]
    rcases le_total h e with h1 | h1
    · rw [abs_of_nonneg (by linarith)]; exact le_max_of_le_left le_rfl
    · rw [abs_of_nonpos (by linarith)]; exact le_max_of_le_right (by linarith)
  · have hz : e * h = 0 := le_antisymm (mul_nonpos_of_nonneg_of_nonpos he hh) heh
    rcases mul_eq_zero.mp hz with h0 | h0 <;> subst h0 <;> simp
  · have hz : e * h = 0 := le_antisymm (mul_nonpos_of_nonpos_of_nonneg he hh) heh
    rcases mul_eq_zero.mp hz with h0 | h0 <;> subst h0 <;> simp
  · rw [abs_of_nonpos he, abs_of_nonpos hh]
    rcases le_total h e with h1 | h1
    · rw [abs_of_nonneg (by linarith)]; exact le_max_of_le_right (by linarith)
    · rw [abs_of_nonpos (by linarith)]; exact le_max_of_le_left (by linarith)

/-- Equally spaced nodes in `[a, b]`. -/
theorem exists_strictMono_nodes (hab : a < b) (N : ℕ) :
    ∃ x : Fin (N + 1) → ℝ, StrictMono x ∧ ∀ j, x j ∈ Icc a b := by
  refine ⟨fun j => a + (b - a) * (j : ℝ) / N, fun i j hij => ?_, fun j => ?_⟩
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      exact absurd hij (by rw [Fin.lt_def]; have := i.isLt; have := j.isLt; omega)
    · have : ((i : ℕ) : ℝ) < j := by exact_mod_cast hij
      have hba : 0 < b - a := sub_pos.mpr hab
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      simp only
      rw [add_lt_add_iff_left, div_lt_div_iff_of_pos_right hN']
      exact mul_lt_mul_of_pos_left this hba
  · have hba : 0 ≤ b - a := (sub_pos.mpr hab).le
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [hab.le]
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hj : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
      constructor
      · have : 0 ≤ (b - a) * (j : ℝ) / N := by positivity
        linarith
      · have : (b - a) * (j : ℝ) / N ≤ b - a := by
          rw [div_le_iff₀ hN']; nlinarith
        linarith

/-- **Necessity**: a minimax approximation in lowest terms equioscillates (3.11.18) at
`D + 2 = k + ℓ + 2 − d` points. -/
theorem alternation_of_minimax (hab : a < b) {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {k ℓ : ℕ} {P Q : ℝ[X]}
    (hmin : IsRatMinimax a b f w k ℓ P Q) (hcop : IsCoprime P Q) :
    ∃ x : Fin (ratD k ℓ P Q + 2) → ℝ, StrictMono x ∧ (∀ j, x j ∈ Icc a b) ∧
      ∃ m, |m| = ratMaxErr a b f w P Q ∧
        ∀ j : Fin (ratD k ℓ P Q + 2), (-1) ^ (j : ℕ) * ratErr f w P Q (x j) = m := by
  set D := ratD k ℓ P Q
  set E := ratMaxErr a b f w P Q with hEdef
  set ε := ratErr f w P Q
  have hQ : ∀ x ∈ Icc a b, 0 < Q.eval x := hmin.1.2.2
  have hQne : ∀ x ∈ Icc a b, Q.eval x ≠ 0 := fun x hx => (hQ x hx).ne'
  have hεc : ContinuousOn ε (Icc a b) := continuousOn_ratErr hf hw hw0 hQne
  have hεE : ∀ x ∈ Icc a b, |ε x| ≤ E := fun x hx => abs_ratErr_le hf hw hw0 hQne hx
  have hE0 : 0 ≤ E := ratMaxErr_nonneg hab.le hf hw hw0 hQne
  rcases hE0.eq_or_lt with hE | hE
  · -- `E = 0`: any nodes
    obtain ⟨x, hx, hxI⟩ := exists_strictMono_nodes hab (D + 1)
    refine ⟨x, hx, hxI, 0, by rw [abs_zero, hE], fun j => ?_⟩
    have := hεE _ (hxI j)
    rw [← hE] at this
    rw [abs_nonpos_iff.mp this, mul_zero]
  -- the extremal sets
  set A := Icc a b ∩ ε ⁻¹' {E}
  set B := Icc a b ∩ ε ⁻¹' {-E}
  have hAc : IsCompact A := isCompact_Icc.of_isClosed_subset
    (hεc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) Set.inter_subset_left
  have hBc : IsCompact B := isCompact_Icc.of_isClosed_subset
    (hεc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) Set.inter_subset_left
  have hd : Disjoint A B := Set.disjoint_left.mpr fun x hA hB => by
    have h1 : ε x = E := hA.2
    have h2 : ε x = -E := hB.2
    linarith
  have hAI : A ⊆ Icc a b := Set.inter_subset_left
  have hBI : B ⊆ Icc a b := Set.inter_subset_left
  by_cases hAB : AltSeq A B (D + 2)
  · obtain ⟨y, hy, hym⟩ := hAB
    refine ⟨fun j => y j, fun i j hij => hy i j hij j.isLt, fun j => ?_, E, abs_of_pos hE,
      fun j => ?_⟩
    · have := hym j j.isLt; split_ifs at this; exacts [hAI this, hBI this]
    · have := hym j j.isLt
      split_ifs at this with hev
      · have h1 : ε (y j) = E := this.2
        simp only [h1, hev.neg_one_pow, one_mul]
      · have h1 : ε (y j) = -E := this.2
        rw [Nat.not_even_iff_odd] at hev
        simp only [h1, hev.neg_one_pow]; ring
  by_cases hBA : AltSeq B A (D + 2)
  · obtain ⟨y, hy, hym⟩ := hBA
    refine ⟨fun j => y j, fun i j hij => hy i j hij j.isLt, fun j => ?_, -E, by
      rw [abs_neg, abs_of_pos hE], fun j => ?_⟩
    · have := hym j j.isLt; split_ifs at this; exacts [hBI this, hAI this]
    · have := hym j j.isLt
      split_ifs at this with hev
      · have h1 : ε (y j) = -E := this.2
        simp only [h1, hev.neg_one_pow, one_mul]
      · have h1 : ε (y j) = E := this.2
        rw [Nat.not_even_iff_odd] at hev
        simp only [h1, hev.neg_one_pow]; ring
  -- otherwise a perturbation lowers the error
  exfalso
  obtain ⟨u, hud, huA, huB, -⟩ := exists_poly_sign D A B hAc hBc hd hAB hBA
  set σ : ℝ := if 0 < w a then 1 else -1
  have hσ2 : σ = 1 ∨ σ = -1 := by simp only [σ]; split_ifs <;> simp
  have hσw : ∀ x ∈ Icc a b, 0 < σ * w x := fun x hx => by
    have h1 := weight_mul_pos hw hw0 hx (left_mem_Icc.mpr hab.le)
    have ha := hw0 a (left_mem_Icc.mpr hab.le)
    simp only [σ]
    split_ifs with h
    · rw [one_mul]; exact pos_of_mul_pos_left h1 h.le
    · push Not at h
      have : w a < 0 := lt_of_le_of_ne h ha
      nlinarith
  have habsw : ∀ x ∈ Icc a b, |w x| = σ * w x := fun x hx => by
    rw [← abs_of_pos (hσw x hx), abs_mul]
    rcases hσ2 with h | h <;> simp [h]
  have hQ0 : Q ≠ 0 := fun h0 => by
    have := hQ a (left_mem_Icc.mpr hab.le); rw [h0, eval_zero] at this; exact lt_irrefl _ this
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_cross_eq hcop hQ0 hmin.1.1 hmin.1.2.1
    (u := C σ * u) ((natDegree_C_mul_le _ _).trans hud)
  -- compactness bounds
  obtain ⟨x0, hx0, hx0min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le)
    Q.continuous.continuousOn
  set Qmin := Q.eval x0
  have hQmin : 0 < Qmin := hQ x0 hx0
  have hQge : ∀ x ∈ Icc a b, Qmin ≤ Q.eval x := fun x hx => hx0min hx
  obtain ⟨qM, hqM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b)
    q.continuous.continuousOn
  obtain ⟨uM, huM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b)
    u.continuous.continuousOn
  obtain ⟨x1, hx1, hx1min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le)
    hw.abs
  set wmin := |w x1|
  have hwmin : 0 < wmin := abs_pos.mpr (hw0 x1 hx1)
  have hwge : ∀ x ∈ Icc a b, wmin ≤ |w x| := fun x hx => hx1min hx
  have hqM0 : 0 ≤ qM := (norm_nonneg _).trans (hqM a (left_mem_Icc.mpr hab.le))
  have huM0 : 0 ≤ uM := (norm_nonneg _).trans (huM a (left_mem_Icc.mpr hab.le))
  -- the extremal set has `ε u > 0`; its minimum `c > 0`
  set φ : ℝ → ℝ := fun x => ε x * u.eval x
  have hφc : ContinuousOn φ (Icc a b) := hεc.mul u.continuous.continuousOn
  set K := A ∪ B
  have hK : IsCompact K := hAc.union hBc
  have hKI : K ⊆ Icc a b := Set.union_subset hAI hBI
  have hKne : K.Nonempty := by
    obtain ⟨x, hx, hxE⟩ := exists_ratMaxErr hab.le hf hw hw0 hQne (P := P)
    rcases abs_eq hE0 |>.mp hxE with h | h
    · exact ⟨x, Or.inl ⟨hx, h⟩⟩
    · exact ⟨x, Or.inr ⟨hx, h⟩⟩
  have hφK : ∀ x ∈ K, 0 < φ x := fun x hx => by
    rcases hx with hx | hx
    · have h1 : ε x = E := hx.2
      simp only [φ, h1]; exact mul_pos hE (huA x hx)
    · have h1 : ε x = -E := hx.2
      simp only [φ, h1]; exact mul_pos_of_neg_of_neg (by linarith) (huB x hx)
  obtain ⟨x2, hx2, hx2min⟩ := hK.exists_isMinOn hKne (hφc.mono hKI)
  set c := φ x2
  have hc : 0 < c := hφK x2 hx2
  -- away from the extremal set the error is smaller by `η`
  set W := Icc a b ∩ φ ⁻¹' Iic (c / 2)
  have hW : IsCompact W := isCompact_Icc.of_isClosed_subset
    (hφc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic) Set.inter_subset_left
  have hWlt : ∀ x ∈ W, |ε x| < E := fun x hx => by
    refine lt_of_le_of_ne (hεE x hx.1) fun heq => ?_
    have hxK : x ∈ K := by
      rcases abs_eq hE0 |>.mp heq with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨hx.1, h⟩
    have h1 := hx2min hxK
    have h2 : φ x ≤ c / 2 := hx.2
    simp only [Set.mem_ofPred_eq] at h1
    linarith
  obtain ⟨η, hη, hηW⟩ : ∃ η > 0, ∀ x ∈ W, |ε x| ≤ E - η := by
    rcases W.eq_empty_or_nonempty with hWe | hWne
    · exact ⟨E, hE, fun x hx => by rw [hWe] at hx; exact hx.elim⟩
    · obtain ⟨x3, hx3, hx3max⟩ := hW.exists_isMaxOn hWne ((hεc.mono Set.inter_subset_left).abs)
      refine ⟨E - |ε x3|, by linarith [hWlt x3 hx3], fun x hx => ?_⟩
      have := hx3max hx
      simp only [Set.mem_ofPred_eq] at this
      linarith
  -- the step size
  set dmax : ℝ := 2 / (wmin * Qmin * Qmin)
  set G : ℝ := uM * dmax + 1
  have hdmax : 0 < dmax := by positivity
  have hG : 0 < G := by positivity
  set t : ℝ := min (Qmin / (2 * (qM + 1))) (min (E / (2 * G)) (η / (2 * G)))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have ht1 : t * qM ≤ Qmin / 2 := by
    have : t ≤ Qmin / (2 * (qM + 1)) := min_le_left _ _
    calc t * qM ≤ Qmin / (2 * (qM + 1)) * qM := by gcongr
      _ ≤ Qmin / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have htE : t * G ≤ E / 2 := by
    have : t ≤ E / (2 * G) := (min_le_right _ _).trans (min_le_left _ _)
    calc t * G ≤ E / (2 * G) * G := by gcongr
      _ = E / 2 := by field_simp
  have htη : t * G ≤ η / 2 := by
    have : t ≤ η / (2 * G) := (min_le_right _ _).trans (min_le_right _ _)
    calc t * G ≤ η / (2 * G) * G := by gcongr
      _ = η / 2 := by field_simp
  set Pt := P - C t * p
  set Qt := Q - C t * q
  have hQt : ∀ x ∈ Icc a b, Qmin / 2 ≤ Qt.eval x := fun x hx => by
    simp only [Qt, eval_sub, eval_mul, eval_C]
    have h1 := hqM x hx
    rw [Real.norm_eq_abs] at h1
    have h2 : t * q.eval x ≤ t * qM := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans h1) ht.le
    linarith [hQge x hx]
  have hQtpos : ∀ x ∈ Icc a b, 0 < Qt.eval x := fun x hx => by linarith [hQt x hx]
  -- the perturbed error
  have hεt : ∀ x ∈ Icc a b, ratErr f w Pt Qt x =
      ε x - t * u.eval x * (1 / (|w x| * Q.eval x * Qt.eval x)) := fun x hx => by
    have hpqx := congrArg (eval x) hpq
    simp only [eval_sub, eval_mul, eval_C] at hpqx
    have hw' := hw0 x hx
    have hQx := hQne x hx
    have hQtx := (hQtpos x hx).ne'
    have e1 : Pt.eval x * Q.eval x - P.eval x * Qt.eval x = -(t * (σ * u.eval x)) := by
      simp only [Pt, Qt, eval_sub, eval_mul, eval_C]
      rw [← hpqx]; ring
    have e2 : ratErr f w Pt Qt x =
        ε x + (Pt.eval x * Q.eval x - P.eval x * Qt.eval x) / (Qt.eval x * Q.eval x) / w x := by
      simp only [ε, ratErr]
      field_simp
      ring
    rw [e2, e1, habsw x hx]
    rcases hσ2 with h | h <;> rw [h] <;> field_simp <;> ring
  -- the error drops strictly everywhere
  have hlt : ∀ x ∈ Icc a b, |ratErr f w Pt Qt x| < E := fun x hx => by
    rw [hεt x hx]
    set d := 1 / (|w x| * Q.eval x * Qt.eval x)
    have hd0 : 0 < d := by
      have := hQ x hx; have := hQtpos x hx; have := abs_pos.mpr (hw0 x hx); positivity
    have hden : 0 < |w x| * Q.eval x * Qt.eval x := by
      have := hQ x hx; have := hQtpos x hx; have := abs_pos.mpr (hw0 x hx); positivity
    have hdle : d ≤ dmax := by
      simp only [d, dmax]
      rw [div_le_div_iff₀ hden (mul_pos (mul_pos hwmin hQmin) hQmin)]
      have h1 := hwge x hx
      have h2 := hQge x hx
      have h3 := hQt x hx
      have : wmin * Qmin * (Qmin / 2) ≤ |w x| * Q.eval x * Qt.eval x := by
        have := mul_le_mul h1 h2 hQmin.le (abs_nonneg _)
        exact mul_le_mul this h3 (by linarith) (mul_nonneg (abs_nonneg _) (hQ x hx).le)
      nlinarith
    have hux := huM x hx
    rw [Real.norm_eq_abs] at hux
    have hh : |t * u.eval x * d| ≤ t * G := by
      rw [abs_mul, abs_mul, abs_of_pos ht, abs_of_pos hd0]
      calc t * |u.eval x| * d ≤ t * uM * dmax := by gcongr
        _ ≤ t * G := by
            rw [mul_assoc]; gcongr; simp only [G]; linarith
    by_cases hxW : φ x ≤ c / 2
    · calc |ε x - t * u.eval x * d| ≤ |ε x| + |t * u.eval x * d| := abs_sub _ _
        _ ≤ E - η + t * G := add_le_add (hηW x ⟨hx, hxW⟩) hh
        _ < E := by linarith
    · push Not at hxW
      have hφpos : 0 < ε x * u.eval x := by have := hc; simp only [φ] at hxW; linarith
      have hmn : 0 ≤ ε x * (t * u.eval x * d) := by
        have : ε x * (t * u.eval x * d) = (ε x * u.eval x) * (t * d) := by ring
        rw [this]; exact mul_nonneg hφpos.le (mul_pos ht hd0).le
      have hhpos : 0 < |t * u.eval x * d| := by
        apply abs_pos.mpr
        have : u.eval x ≠ 0 := fun h0 => by rw [h0, mul_zero] at hφpos; exact lt_irrefl _ hφpos
        exact mul_ne_zero (mul_ne_zero ht.ne' this) hd0.ne'
      calc |ε x - t * u.eval x * d| ≤ max (|ε x| - |t * u.eval x * d|) |t * u.eval x * d| :=
            abs_sub_le_max_of_mul_nonneg hmn
        _ < E := max_lt (by linarith [hεE x hx]) (by linarith)
  -- contradiction with minimality
  have hadm : RatAdmissible a b k ℓ Pt Qt :=
    ⟨(natDegree_sub_le _ _).trans (max_le hmin.1.1 ((natDegree_C_mul_le _ _).trans hp)),
      (natDegree_sub_le _ _).trans (max_le hmin.1.2.1 ((natDegree_C_mul_le _ _).trans hq)),
      hQtpos⟩
  obtain ⟨x4, hx4, hx4eq⟩ := exists_ratMaxErr hab.le hf hw hw0 (fun x hx => (hQtpos x hx).ne')
    (P := Pt)
  have := hmin.2 Pt Qt hadm
  have := hlt x4 hx4
  linarith

/-! ### Achieser's theorem -/

/-- **DLMF §3.11(iii)** (characterization, corrected): for `R = P/Q` admissible and in lowest
terms, `R` is minimax iff `m_j = (−1)^j ε(x_j)` (3.11.18) is constant `= m`, `|m| = max |ε|`, at
`D + 2 = k + ℓ + 2 − d` points. -/
theorem dlmf_3_11_iii_characterization (hab : a < b) {f w : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {k ℓ : ℕ} {P Q : ℝ[X]} (hPQ : RatAdmissible a b k ℓ P Q)
    (hcop : IsCoprime P Q) :
    IsRatMinimax a b f w k ℓ P Q ↔
      ∃ x : Fin (ratD k ℓ P Q + 2) → ℝ, StrictMono x ∧ (∀ j, x j ∈ Icc a b) ∧
        ∃ m, |m| = ratMaxErr a b f w P Q ∧
          ∀ j : Fin (ratD k ℓ P Q + 2), (-1) ^ (j : ℕ) * ratErr f w P Q (x j) = m := by
  refine ⟨fun h => alternation_of_minimax hab hf hw hw0 h hcop, ?_⟩
  rintro ⟨x, hx, hxI, m, hm, h18⟩
  refine ⟨hPQ, fun P' Q' hPQ' => ?_⟩
  rw [← hm]
  have hs : (if 0 ≤ m then (1 : ℝ) else -1) = 1 ∨ (if 0 ≤ m then (1 : ℝ) else -1) = -1 := by
    split_ifs <;> simp
  refine vallee_poussin_deg hf hw hw0 hPQ hx hxI hs (fun j => ?_) hPQ'
    (natDegree_cross_le_ratD hcop hPQ'.1 hPQ'.2.1)
  rw [mul_assoc, h18 j]
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · rw [abs_of_neg (not_le.mp h)]; ring_nf; rfl

/-- **DLMF §3.11(iii)** (uniqueness): two minimax approximations agree on `[a, b]`. -/
theorem dlmf_3_11_iii_unique (hab : a < b) {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {k ℓ : ℕ}
    {P₁ Q₁ P₂ Q₂ : ℝ[X]} (h₁ : IsRatMinimax a b f w k ℓ P₁ Q₁)
    (h₂ : IsRatMinimax a b f w k ℓ P₂ Q₂) :
    ∀ x ∈ Icc a b, P₁.eval x / Q₁.eval x = P₂.eval x / Q₂.eval x := by
  obtain ⟨P, Q, hPQ, hcop, hval⟩ := exists_coprime_rep hab.le h₁.1
  have hrr : ∀ x ∈ Icc a b, ratErr f w P Q x = ratErr f w P₁ Q₁ x := fun x hx => by
    simp only [ratErr, hval x hx]
  have hEeq : ratMaxErr a b f w P Q = ratMaxErr a b f w P₁ Q₁ := ratMaxErr_congr hrr
  have hmin : IsRatMinimax a b f w k ℓ P Q := ⟨hPQ, fun P' Q' h => hEeq ▸ h₁.2 P' Q' h⟩
  obtain ⟨x, hx, hxI, m, hm, h18⟩ := alternation_of_minimax hab hf hw hw0 hmin hcop
  have hE2 : ratMaxErr a b f w P₂ Q₂ = ratMaxErr a b f w P Q :=
    le_antisymm (h₂.2 P Q hPQ) (hEeq ▸ h₁.2 P₂ Q₂ h₂.1)
  -- `V = P₂Q − PQ₂` weakly alternates at `D + 2` points
  set s : ℝ := if 0 ≤ m then 1 else -1
  have hs2 : s = 1 ∨ s = -1 := by simp only [s]; split_ifs <;> simp
  have hsm : s * m = |m| := by
    simp only [s]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set σ : ℝ := if 0 < w a then 1 else -1
  have hσ2 : σ = 1 ∨ σ = -1 := by simp only [σ]; split_ifs <;> simp
  have hσw : ∀ y ∈ Icc a b, 0 < σ * w y := fun y hy => by
    have h1 := weight_mul_pos hw hw0 hy (left_mem_Icc.mpr hab.le)
    have ha := hw0 a (left_mem_Icc.mpr hab.le)
    simp only [σ]
    split_ifs with h
    · rw [one_mul]; exact pos_of_mul_pos_left h1 h.le
    · push Not at h
      have : w a < 0 := lt_of_le_of_ne h ha
      nlinarith
  set V := C (-(s * σ)) * (P₂ * Q - P * Q₂)
  have hV : V.natDegree ≤ ratD k ℓ P Q :=
    (natDegree_C_mul_le _ _).trans (natDegree_cross_le_ratD hcop h₂.1.1 h₂.1.2.1)
  have hV0 := eq_zero_of_weak_alternates hV hx fun j => by
    have hj := hxI j
    have hQj := hPQ.2.2 _ hj
    have hQ2j := h₂.1.2.2 _ hj
    have hwj := hσw _ hj
    simp only [V, eval_mul, eval_C]
    rw [cross_eval_eq (f := f) (w := w) hQj.ne' hQ2j.ne' (hw0 _ hj)]
    have h2 := abs_ratErr_le hf hw hw0 (fun y hy => (h₂.1.2.2 y hy).ne') (P := P₂) hj
    rw [hE2, ← hm] at h2
    have h1 := h18 j
    -- `(−1)^j s ε(x_j) = |m| ≥ |ε₂(x_j)|`
    set t : ℝ := (-1) ^ (j : ℕ)
    have ht2 : t * t = 1 := by simp [t, ← pow_add, ← two_mul, pow_mul]
    have hs22 : s * s = 1 := by rcases hs2 with h | h <;> rw [h] <;> norm_num
    have key : 0 ≤ t * s * (ratErr f w P Q (x j) - ratErr f w P₂ Q₂ (x j)) := by
      have e1 : t * s * ratErr f w P Q (x j) = |m| := by rw [← hsm, ← h1]; ring
      have e2 : |t * s * ratErr f w P₂ Q₂ (x j)| ≤ |m| := by
        rw [abs_mul, abs_mul, show |t| = 1 by simp [t, abs_pow], show |s| = 1 by
          rcases hs2 with h | h <;> rw [h] <;> norm_num, one_mul, one_mul]
        exact h2
      have := (abs_le.mp e2).2
      linarith
    have hpos : 0 < (σ * w (x j)) * Q₂.eval (x j) * Q.eval (x j) := by positivity
    have e : t * (-(s * σ) * ((ratErr f w P₂ Q₂ (x j) - ratErr f w P Q (x j)) * w (x j) *
        Q₂.eval (x j) * Q.eval (x j))) =
        (t * s * (ratErr f w P Q (x j) - ratErr f w P₂ Q₂ (x j))) *
          ((σ * w (x j)) * Q₂.eval (x j) * Q.eval (x j)) := by ring
    rw [e]
    exact mul_nonneg key hpos.le
  have hzero : P₂ * Q - P * Q₂ = 0 := by
    have hsσ : -(s * σ) ≠ 0 := by
      rcases hs2 with h | h <;> rcases hσ2 with h' | h' <;> rw [h, h'] <;> norm_num
    have := hV0
    simp only [V] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (C_eq_zero.mp h) hsσ
    · exact h
  intro y hy
  have hy' := congrArg (eval y) hzero
  simp only [eval_sub, eval_mul, eval_zero] at hy'
  rw [← hval y hy, div_eq_div_iff (hPQ.2.2 y hy).ne' (h₂.1.2.2 y hy).ne']
  linarith

/-- **DLMF §3.11(iii)** (alternation, corrected): the minimax approximation exists, is unique,
and in lowest terms equioscillates at `k + ℓ + 2 − d` points (`d` the defect), hence at
`k + ℓ + 2` points when it is nondegenerate. -/
theorem dlmf_3_11_iii_alternation (hab : a < b) {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) (k ℓ : ℕ) :
    ∃ P Q, IsRatMinimax a b f w k ℓ P Q ∧ IsCoprime P Q ∧
      ∃ x : Fin (k + ℓ + 2 - ratDefect k ℓ P Q) → ℝ, StrictMono x ∧ (∀ j, x j ∈ Icc a b) ∧
        ∃ m, |m| = ratMaxErr a b f w P Q ∧
          ∀ j : Fin (k + ℓ + 2 - ratDefect k ℓ P Q), (-1) ^ (j : ℕ) * ratErr f w P Q (x j) = m := by
  obtain ⟨P₀, Q₀, h₀⟩ := dlmf_3_11_iii_exists hab hf hw hw0 k ℓ
  obtain ⟨P, Q, hPQ, hcop, hval⟩ := exists_coprime_rep hab.le h₀.1
  have hrr : ∀ x ∈ Icc a b, ratErr f w P Q x = ratErr f w P₀ Q₀ x := fun x hx => by
    simp only [ratErr, hval x hx]
  have hmin : IsRatMinimax a b f w k ℓ P Q :=
    ⟨hPQ, fun P' Q' h => (ratMaxErr_congr hrr) ▸ h₀.2 P' Q' h⟩
  have hN : k + ℓ + 2 - ratDefect k ℓ P Q = ratD k ℓ P Q + 2 := by
    have := ratD_le hPQ.1 hPQ.2.1
    unfold ratDefect; omega
  refine ⟨P, Q, hmin, hcop, ?_⟩
  rw [hN]
  exact alternation_of_minimax hab hf hw hw0 hmin hcop

theorem ratDefect_eq_zero_iff {k ℓ : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ ℓ) :
    ratDefect k ℓ P Q = 0 ↔ ratD k ℓ P Q = k + ℓ := by
  have := ratD_le hP hQ
  unfold ratDefect; omega

end Azurite.DLMF
