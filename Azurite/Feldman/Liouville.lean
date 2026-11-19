/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Fel'dman, Lemmas 2–5: roots of integer polynomials and Liouville's inequality

N. I. Fel'dman, *Approximation of certain transcendental numbers. I*, Izv. Akad. Nauk SSSR
Ser. Mat. 15 (1951), 53–74, §1.  The height of a polynomial is the largest absolute value of
its coefficients; `n` is its degree.

* **Lemmas 2, 3** (`norm_leadingCoeff_mul_prod_le`, `norm_leadingCoeff_mul_prod_one_add_le`).
  For `P = a₀ ∏ (z − ξ_ν)` of height `≤ H`: `|a₀| |ξ_{ν₁} ⋯ ξ_{ν_s}| ≤ (n + 1) H` for distinct
  indices, and `|a₀| ∏ (1 + |ξ_ν|) ≤ 2ⁿ (n + 1) H`.  Both are bounds for the Mahler measure
  `|a₀| ∏ max(1, |ξ_ν|) ≤ (n + 1) H` (`mahlerMeasure_le_of_coeff_le`), and are sharper than
  Fel'dman's `(n + 1) 2ⁿ H` and `(n + 1) 4ⁿ H`, which he gets from the maximum principle.
* **Lemma 4 (Liouville's inequality).**  Fel'dman states it for `β = ∑ a_{k,l} α₁^k ξ^l` with
  a fixed algebraic `α₁`; the approximation of `π` uses `α₁ = i` only, and that is what is
  proven here.  `liouville_int`: for `ξ` a root of an irreducible `p ∈ ℤ[z]` of degree `n` and
  height `≤ H`, and `R ∈ ℤ[z]` of degree `≤ M` and height `≤ A` with `R(ξ) ≠ 0`,

    `|R(ξ)| ≥ ((M + 1) A)^(−(n−1)) ((n + 1) H)^(−M)`:

  the resultant `a₀^M ∏_j R(ξ_j)` is a nonzero integer, and the other factors are bounded
  by the Mahler measure.  `liouville_gaussian`: the same for `β = Q₁(ξ) + i Q₂(ξ) ≠ 0`, from
  `β β′ = (Q₁² + Q₂²)(ξ)` with `β′ = Q₁(ξ) − i Q₂(ξ)` (or `β = 2 Q₁(ξ)` when `β′ = 0`).
* **Lemma 5** (`norm_aeval_ge_dist_root`).  If `ξ` is a root of `p` nearest to `ζ`, then
  `|p(ζ)| ≥ |ζ − ξ| 2^(1−n) |p′(ξ)|`, since `|ζ − ξ_j| ≥ |ξ − ξ_j|/2` for the other roots; and
  `p′(ξ) ≠ 0` is bounded below by Liouville's inequality.  Fel'dman's version, for any `P`
  without multiple roots, uses the discriminant and has `e^(−2n²) H^(−n)`; this one, for an
  irreducible `p` (the only case used), has `(2n²(n + 1)H²)^(−(n−1))`.
-/

namespace Azurite.Feldman

open Polynomial

/-! ### Products over multisets -/

theorem one_le_prod_map {α : Type*} (s : Multiset α) (f : α → ℝ) (hf : ∀ a, 1 ≤ f a) :
    1 ≤ (s.map f).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (hf a) ih

theorem prod_map_nonneg {α : Type*} (s : Multiset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ (s.map f).prod :=
  Multiset.prod_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hf a

theorem prod_map_le_prod_map {α : Type*} (s : Multiset α) (f g : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hfg : ∀ a, f a ≤ g a) : (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul (hfg a) ih (prod_map_nonneg s f hf) ((hf a).trans (hfg a))

theorem prod_map_le_of_le {α : Type*} {s t : Multiset α} (h : s ≤ t) (f : α → ℝ)
    (hf : ∀ a, 1 ≤ f a) : (s.map f).prod ≤ (t.map f).prod := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [Multiset.map_add, Multiset.prod_add]
  exact le_mul_of_one_le_right (prod_map_nonneg s f fun a => zero_le_one.trans (hf a))
    (one_le_prod_map u f hf)

theorem prod_map_const_mul_pow {α : Type*} (s : Multiset α) (c : ℝ) (f : α → ℝ) (M : ℕ) :
    (s.map fun a => c * f a ^ M).prod = c ^ Multiset.card s * (s.map f).prod ^ M := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.card_cons, Multiset.map_cons,
      Multiset.prod_cons]
    ring

theorem norm_prod_map {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ‖(s.map f).prod‖ = (s.map fun a => ‖f a‖).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-! ### Lemmas 2 and 3 -/

/-- The Mahler measure of a polynomial of height `≤ H` is at most `(n + 1) H`. -/
theorem mahlerMeasure_le_of_coeff_le (P : ℂ[X]) {H : ℝ} (hH : ∀ i, ‖P.coeff i‖ ≤ H) :
    P.mahlerMeasure ≤ (P.natDegree + 1) * H := by
  refine (mahlerMeasure_le_sum_norm_coeff P).trans ?_
  rw [Polynomial.sum_def]
  have h0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  calc ∑ i ∈ P.support, ‖P.coeff i‖ ≤ ∑ _i ∈ P.support, H := Finset.sum_le_sum fun i _ => hH i
    _ = P.support.card * H := by simp
    _ ≤ (P.natDegree + 1) * H := by
      have : (P.support.card : ℝ) ≤ P.natDegree + 1 := by
        exact_mod_cast P.card_supp_le_succ_natDegree
      gcongr

/-- **Fel'dman, Lemma 2**: `|a₀| |ξ_{ν₁} ⋯ ξ_{ν_s}| ≤ (n + 1) H` for any part of the roots. -/
theorem norm_leadingCoeff_mul_prod_le (P : ℂ[X]) {H : ℝ} (hH : ∀ i, ‖P.coeff i‖ ≤ H)
    {s : Multiset ℂ} (hs : s ≤ P.roots) :
    ‖P.leadingCoeff‖ * (s.map fun a => ‖a‖).prod ≤ (P.natDegree + 1) * H := by
  refine le_trans ?_ (mahlerMeasure_le_of_coeff_le P hH)
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (prod_map_le_prod_map s _ _ (fun a => norm_nonneg a) fun a => le_max_right _ _).trans
    (prod_map_le_of_le hs _ fun a => le_max_left _ _)

/-- **Fel'dman, Lemma 3**: `|a₀| ∏ (1 + |ξ_ν|) ≤ 2ⁿ (n + 1) H`. -/
theorem norm_leadingCoeff_mul_prod_one_add_le (P : ℂ[X]) {H : ℝ} (hH : ∀ i, ‖P.coeff i‖ ≤ H) :
    ‖P.leadingCoeff‖ * (P.roots.map fun a => 1 + ‖a‖).prod
      ≤ 2 ^ P.natDegree * ((P.natDegree + 1) * H) := by
  have h1 : (P.roots.map fun a => 1 + ‖a‖).prod
      ≤ (P.roots.map fun a => 2 * max 1 ‖a‖ ^ 1).prod :=
    prod_map_le_prod_map _ _ _ (fun a => by positivity) fun a => by
      rw [pow_one]
      rcases le_total 1 ‖a‖ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
  rw [prod_map_const_mul_pow, pow_one] at h1
  have h2 : (2 : ℝ) ^ Multiset.card P.roots ≤ 2 ^ P.natDegree :=
    pow_le_pow_right₀ (by norm_num) P.card_roots'
  have h3 := mahlerMeasure_le_of_coeff_le P hH
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots] at h3
  have h4 : 0 ≤ (P.roots.map fun a => max 1 ‖a‖).prod :=
    prod_map_nonneg _ _ fun a => by positivity
  calc ‖P.leadingCoeff‖ * (P.roots.map fun a => 1 + ‖a‖).prod
      ≤ ‖P.leadingCoeff‖
          * (2 ^ Multiset.card P.roots * (P.roots.map fun a => max 1 ‖a‖).prod) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = 2 ^ Multiset.card P.roots
          * (‖P.leadingCoeff‖ * (P.roots.map fun a => max 1 ‖a‖).prod) := by ring
    _ ≤ 2 ^ P.natDegree * ((P.natDegree + 1) * H) :=
        mul_le_mul h2 h3 (mul_nonneg (norm_nonneg _) h4) (by positivity)

/-! ### Integer polynomials at complex points -/

/-- The image in `ℂ[X]` of an integer polynomial. -/
noncomputable abbrev toC (p : ℤ[X]) : ℂ[X] := p.map (Int.castRingHom ℂ)

theorem aeval_eq_eval_toC (p : ℤ[X]) (z : ℂ) : aeval z p = (toC p).eval z := by
  rw [aeval_def, eval₂_eq_eval_map]
  rfl

theorem natDegree_toC (p : ℤ[X]) : (toC p).natDegree = p.natDegree :=
  natDegree_map_eq_of_injective Int.cast_injective p

theorem norm_coeff_toC (p : ℤ[X]) (i : ℕ) : ‖(toC p).coeff i‖ = |(p.coeff i : ℝ)| := by
  rw [coeff_map, eq_intCast, Complex.norm_intCast]

/-- `|R(z)| ≤ (M + 1) A max(1, |z|)^M` for `R` of degree `≤ M` and height `≤ A`. -/
theorem norm_aeval_le (R : ℤ[X]) {M : ℕ} (hM : R.natDegree ≤ M) {A : ℝ}
    (hA : ∀ i, |(R.coeff i : ℝ)| ≤ A) (z : ℂ) :
    ‖aeval z R‖ ≤ (M + 1) * A * max 1 ‖z‖ ^ M := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hM)]
  calc ‖∑ i ∈ Finset.range (M + 1), R.coeff i • z ^ i‖
      ≤ ∑ _i ∈ Finset.range (M + 1), A * max 1 ‖z‖ ^ M := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [zsmul_eq_mul, norm_mul, Complex.norm_intCast, norm_pow]
        have hi' : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : ‖z‖ ^ i ≤ max 1 ‖z‖ ^ M :=
          (pow_le_pow_left₀ (norm_nonneg z) (le_max_right _ _) i).trans
            (pow_le_pow_right₀ (le_max_left _ _) hi')
        exact mul_le_mul (hA i) h1 (by positivity) ((abs_nonneg _).trans (hA i))
    _ = (M + 1) * A * max 1 ‖z‖ ^ M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- An integer polynomial that does not vanish at one root of an irreducible `p` does not
vanish at any. -/
theorem aeval_ne_zero_of_root {p R : ℤ[X]} (hp : Irreducible p) (hn : p.natDegree ≠ 0) {ξ : ℂ}
    (hξ : aeval ξ p = 0) (hR : aeval ξ R ≠ 0) {η : ℂ} (hη : aeval η p = 0) :
    aeval η R ≠ 0 := by
  have hprim : p.IsPrimitive := hp.isPrimitive hn
  have hq : Irreducible (p.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hp
  have hev : ∀ (q : ℤ[X]) (z : ℂ), aeval z (q.map (Int.castRingHom ℚ)) = aeval z q := fun q z =>
    aeval_map_algebraMap ℚ z q
  have hcop : IsCoprime (p.map (Int.castRingHom ℚ)) (R.map (Int.castRingHom ℚ)) := by
    rw [hq.coprime_iff_not_dvd]
    rintro ⟨c, hc⟩
    apply hR
    rw [← hev R ξ, hc, map_mul, hev p ξ, hξ, zero_mul]
  obtain ⟨u, v, huv⟩ := hcop
  intro h0
  have := congrArg (aeval η) huv
  rw [map_add, map_mul, map_mul, hev p η, hev R η, hη, h0, mul_zero, mul_zero, add_zero,
    map_one] at this
  exact zero_ne_one this

/-! ### Lemma 4: Liouville's inequality -/

/-- **Liouville's inequality** (Fel'dman, Lemma 4, for integer coefficients): for a root `ξ` of
an irreducible `p ∈ ℤ[z]` of degree `n` and height `≤ H`, and `R ∈ ℤ[z]` of degree `≤ M` and
height `≤ A` with `R(ξ) ≠ 0`: `1 ≤ |R(ξ)| ((M + 1) A)^(n−1) ((n + 1) H)^M`. -/
theorem liouville_int {p R : ℤ[X]} (hp : Irreducible p) (hn : p.natDegree ≠ 0) {ξ : ℂ}
    (hξ : aeval ξ p = 0) (hR : aeval ξ R ≠ 0) {M : ℕ} (hM : R.natDegree ≤ M) {A H : ℝ}
    (hA : ∀ i, |(R.coeff i : ℝ)| ≤ A) (hH : ∀ i, |(p.coeff i : ℝ)| ≤ H) :
    1 ≤ ‖aeval ξ R‖ * (((M + 1) * A) ^ (p.natDegree - 1) * ((p.natDegree + 1) * H) ^ M) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  have hsplit : (toC p).Splits := IsAlgClosed.splits _
  have hp0 : toC p ≠ 0 := fun h => hn (by rw [← natDegree_toC, h, natDegree_zero])
  -- the resultant is a nonzero integer
  have hres := resultant_eq_prod_eval (toC p) (toC R) M (natDegree_map_le.trans hM) hsplit
  rw [natDegree_toC, resultant_map_map] at hres
  have hne : ((p.resultant R p.natDegree M : ℤ) : ℂ) ≠ 0 := by
    rw [eq_intCast] at hres
    rw [hres]
    refine mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hp0)) (Multiset.prod_ne_zero ?_)
    intro h0
    obtain ⟨η, hη, hη0⟩ := Multiset.mem_map.mp h0
    have hη' : aeval η p = 0 := by
      rw [aeval_eq_eval_toC]
      exact (mem_roots hp0).mp hη
    exact aeval_ne_zero_of_root hp hn hξ hR hη' (by rw [aeval_eq_eval_toC]; exact hη0)
  have hge : (1 : ℝ) ≤ ‖((p.resultant R p.natDegree M : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have : (p.resultant R p.natDegree M : ℤ) ≠ 0 := fun h => hne (by rw [h, Int.cast_zero])
    exact_mod_cast Int.one_le_abs this
  rw [eq_intCast] at hres
  rw [hres, norm_mul, norm_pow] at hge
  -- split off the root `ξ`
  have hmem : ξ ∈ (toC p).roots := by
    rw [mem_roots hp0, IsRoot, ← aeval_eq_eval_toC]
    exact hξ
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem
  have hcard : Multiset.card t = p.natDegree - 1 := by
    have := hsplit.natDegree_eq_card_roots
    rw [natDegree_toC, ht, Multiset.card_cons] at this
    omega
  have hnorm : ‖((toC p).roots.map (toC R).eval).prod‖
      = ‖aeval ξ R‖ * (t.map fun η => ‖aeval η R‖).prod := by
    rw [ht, Multiset.map_cons, Multiset.prod_cons, norm_mul, ← aeval_eq_eval_toC, norm_prod_map]
    simp only [aeval_eq_eval_toC]
  rw [hnorm] at hge
  -- the other roots
  have hrest : (t.map fun η => ‖aeval η R‖).prod
      ≤ ((M + 1) * A) ^ (p.natDegree - 1) * (t.map fun η => max 1 ‖η‖).prod ^ M := by
    rw [← hcard, ← prod_map_const_mul_pow]
    exact prod_map_le_prod_map _ _ _ (fun η => norm_nonneg _) fun η => norm_aeval_le R hM hA η
  have hmahler : ‖(toC p).leadingCoeff‖ * (t.map fun η => max 1 ‖η‖).prod
      ≤ (p.natDegree + 1) * H := by
    have h1 := mahlerMeasure_le_of_coeff_le (toC p) (H := H)
      (fun i => by rw [norm_coeff_toC]; exact hH i)
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, natDegree_toC] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h1
    exact prod_map_le_of_le (by rw [ht]; exact Multiset.le_cons_self t ξ) _
      fun a => le_max_left _ _
  have ht0 : 0 ≤ (t.map fun η => max 1 ‖η‖).prod := prod_map_nonneg _ _ fun a => by positivity
  calc (1 : ℝ) ≤ ‖(toC p).leadingCoeff‖ ^ M
        * (‖aeval ξ R‖ * (t.map fun η => ‖aeval η R‖).prod) := hge
    _ ≤ ‖(toC p).leadingCoeff‖ ^ M * (‖aeval ξ R‖
        * (((M + 1) * A) ^ (p.natDegree - 1) * (t.map fun η => max 1 ‖η‖).prod ^ M)) := by
        gcongr
    _ = ‖aeval ξ R‖ * (((M + 1) * A) ^ (p.natDegree - 1)
        * (‖(toC p).leadingCoeff‖ * (t.map fun η => max 1 ‖η‖).prod) ^ M) := by
        rw [mul_pow]; ring
    _ ≤ ‖aeval ξ R‖ * (((M + 1) * A) ^ (p.natDegree - 1) * ((p.natDegree + 1) * H) ^ M) := by
        gcongr

/-- A root of a nonconstant integer polynomial of height `≤ H` has `max(1, |ξ|) ≤ (n + 1) H`. -/
theorem max_one_norm_root_le {p : ℤ[X]} (hn : p.natDegree ≠ 0) {ξ : ℂ} (hξ : aeval ξ p = 0)
    {H : ℝ} (hH : ∀ i, |(p.coeff i : ℝ)| ≤ H) : max 1 ‖ξ‖ ≤ (p.natDegree + 1) * H := by
  have hp0 : toC p ≠ 0 := fun h => hn (by rw [← natDegree_toC, h, natDegree_zero])
  have hmem : ξ ∈ (toC p).roots := by
    rw [mem_roots hp0, IsRoot, ← aeval_eq_eval_toC]
    exact hξ
  have hlc : 1 ≤ ‖(toC p).leadingCoeff‖ := by
    rw [leadingCoeff_map_of_injective Int.cast_injective, eq_intCast, Complex.norm_intCast]
    have : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fun h => hn (by rw [h, natDegree_zero])
    exact_mod_cast Int.one_le_abs this
  have h1 := prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff hlc
  have h2 := mahlerMeasure_le_of_coeff_le (toC p) (H := H)
    (fun i => by rw [norm_coeff_toC]; exact hH i)
  rw [natDegree_toC] at h2
  have h3 := prod_map_le_of_le (Multiset.singleton_le.mpr hmem) (fun a : ℂ => max 1 ‖a‖)
    fun a => le_max_left _ _
  rw [Multiset.map_singleton, Multiset.prod_singleton] at h3
  linarith

/-- The coefficients of a product: `(M + 1) A B` for factors of heights `≤ A`, `≤ B`, the first
of degree `≤ M`. -/
theorem abs_coeff_mul_le {P Q : ℤ[X]} {M : ℕ} (hP : P.natDegree ≤ M) {A B : ℝ}
    (hA : ∀ i, |(P.coeff i : ℝ)| ≤ A) (hB : ∀ i, |(Q.coeff i : ℝ)| ≤ B) (k : ℕ) :
    |((P * Q).coeff k : ℝ)| ≤ (M + 1) * A * B := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  calc |∑ i ∈ Finset.range (k + 1), (P.coeff i : ℝ) * (Q.coeff (k - i) : ℝ)|
      ≤ ∑ i ∈ Finset.range (k + 1), (if i ≤ M then A * B else 0) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        split_ifs with h
        · rw [abs_mul]
          exact mul_le_mul (hA i) (hB _) (abs_nonneg _) hA0
        · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          simp
    _ = ∑ i ∈ (Finset.range (k + 1)).filter (fun i => i ≤ M), A * B := by
        rw [Finset.sum_filter]
    _ ≤ ∑ _i ∈ Finset.range (M + 1), A * B :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
          rw [Finset.mem_filter] at hi
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi.2)) fun _ _ _ => by positivity
    _ = (M + 1) * A * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Liouville's inequality with Gaussian coefficients** (Fel'dman, Lemma 4 for `α₁ = i`):
for `β = Q₁(ξ) + i Q₂(ξ) ≠ 0` with `Q₁, Q₂ ∈ ℤ[z]` of degree `≤ M` and height `≤ A`,
`1 ≤ |β| · 2(M + 1)A · (2(2M + 1)(M + 1)A²)^(n−1) · ((n + 1)H)^(3M)`. -/
theorem liouville_gaussian {p Q₁ Q₂ : ℤ[X]} (hp : Irreducible p) (hn : p.natDegree ≠ 0)
    {ξ : ℂ} (hξ : aeval ξ p = 0) (hβ : aeval ξ Q₁ + Complex.I * aeval ξ Q₂ ≠ 0) {M : ℕ}
    (h₁ : Q₁.natDegree ≤ M) (h₂ : Q₂.natDegree ≤ M) {A H : ℝ} (hA1 : 1 ≤ A)
    (hA₁ : ∀ i, |(Q₁.coeff i : ℝ)| ≤ A) (hA₂ : ∀ i, |(Q₂.coeff i : ℝ)| ≤ A)
    (hH : ∀ i, |(p.coeff i : ℝ)| ≤ H) :
    1 ≤ ‖aeval ξ Q₁ + Complex.I * aeval ξ Q₂‖ * (2 * (M + 1) * A
      * ((2 * M + 1) * (2 * (M + 1) * A ^ 2)) ^ (p.natDegree - 1)
      * ((p.natDegree + 1) * H) ^ (3 * M)) := by
  set B : ℝ := (p.natDegree + 1) * H with hB
  have hroot := max_one_norm_root_le hn hξ hH
  have hB1 : 1 ≤ B := (le_max_left _ _).trans hroot
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set X : ℝ := ((2 * M + 1) * (2 * (M + 1) * A ^ 2)) ^ (p.natDegree - 1) with hX
  have hX0 : 0 ≤ X := by positivity
  by_cases hβ' : aeval ξ Q₁ - Complex.I * aeval ξ Q₂ = 0
  · -- `β = 2 Q₁(ξ)`
    have he : aeval ξ Q₁ + Complex.I * aeval ξ Q₂ = 2 * aeval ξ Q₁ := by
      linear_combination -hβ'
    rw [he] at hβ ⊢
    have hQ : aeval ξ Q₁ ≠ 0 := fun h => hβ (by rw [h, mul_zero])
    have hL := liouville_int hp hn hξ hQ h₁ hA₁ hH
    rw [← hB] at hL
    have hx : ((M + 1) * A) ^ (p.natDegree - 1) ≤ X := by
      apply pow_le_pow_left₀ (by positivity)
      have hAA : A ≤ A ^ 2 := by nlinarith
      calc (M + 1) * A ≤ 1 * (2 * (M + 1) * A ^ 2) := by nlinarith
        _ ≤ (2 * M + 1) * (2 * (M + 1) * A ^ 2) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hb : B ^ M ≤ B ^ (3 * M) := pow_le_pow_right₀ hB1 (by omega)
    rw [norm_mul, Complex.norm_ofNat]
    have hQn : 0 ≤ ‖aeval ξ Q₁‖ := norm_nonneg _
    have hbig : (1 : ℝ) ≤ 2 * (M + 1) * A := by nlinarith
    calc (1 : ℝ) ≤ ‖aeval ξ Q₁‖ * (((M + 1) * A) ^ (p.natDegree - 1) * B ^ M) := hL
      _ ≤ ‖aeval ξ Q₁‖ * (X * B ^ (3 * M)) := by gcongr
      _ ≤ 2 * ‖aeval ξ Q₁‖ * (2 * (M + 1) * A * X * B ^ (3 * M)) := by
        have h0 : 0 ≤ X * B ^ (3 * M) := by positivity
        have h1 : X * B ^ (3 * M) ≤ 2 * (M + 1) * A * X * B ^ (3 * M) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (M + 1) * A - 1) h0]
        nlinarith [mul_nonneg hQn h0, mul_le_mul_of_nonneg_left h1 hQn]
  · -- `β β′ = (Q₁² + Q₂²)(ξ)`
    have he : aeval ξ (Q₁ * Q₁ + Q₂ * Q₂)
        = (aeval ξ Q₁ + Complex.I * aeval ξ Q₂) * (aeval ξ Q₁ - Complex.I * aeval ξ Q₂) := by
      rw [map_add, map_mul, map_mul]
      linear_combination (aeval ξ Q₂) ^ 2 * Complex.I_sq
    have hR : aeval ξ (Q₁ * Q₁ + Q₂ * Q₂) ≠ 0 := by
      rw [he]
      exact mul_ne_zero hβ hβ'
    have hdeg : (Q₁ * Q₁ + Q₂ * Q₂).natDegree ≤ 2 * M :=
      (natDegree_add_le _ _).trans (max_le (natDegree_mul_le.trans (by omega))
        (natDegree_mul_le.trans (by omega)))
    have hcoeff : ∀ i, |((Q₁ * Q₁ + Q₂ * Q₂).coeff i : ℝ)| ≤ 2 * (M + 1) * A ^ 2 := fun i => by
      rw [coeff_add]
      push_cast
      have e1 := abs_coeff_mul_le h₁ hA₁ hA₁ i
      have e2 := abs_coeff_mul_le h₂ hA₂ hA₂ i
      have := abs_add_le ((Q₁ * Q₁).coeff i : ℝ) ((Q₂ * Q₂).coeff i : ℝ)
      nlinarith
    have hL := liouville_int hp hn hξ hR hdeg hcoeff hH
    rw [he, norm_mul, ← hB] at hL
    push_cast at hL
    rw [← hX] at hL
    -- `|β′| ≤ 2 (M + 1) A B^M`
    have hβn : ‖aeval ξ Q₁ - Complex.I * aeval ξ Q₂‖ ≤ 2 * (M + 1) * A * B ^ M := by
      have e1 := norm_aeval_le Q₁ h₁ hA₁ ξ
      have e2 := norm_aeval_le Q₂ h₂ hA₂ ξ
      have e3 : max 1 ‖ξ‖ ^ M ≤ B ^ M := pow_le_pow_left₀ (by positivity) hroot M
      have e4 : ‖aeval ξ Q₁ - Complex.I * aeval ξ Q₂‖ ≤ ‖aeval ξ Q₁‖ + ‖aeval ξ Q₂‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
      have e5 : (M + 1) * A * max 1 ‖ξ‖ ^ M ≤ (M + 1) * A * B ^ M := by gcongr
      linarith
    have hn0 : 0 ≤ ‖aeval ξ Q₁ + Complex.I * aeval ξ Q₂‖ := norm_nonneg _
    calc (1 : ℝ) ≤ ‖aeval ξ Q₁ + Complex.I * aeval ξ Q₂‖
          * ‖aeval ξ Q₁ - Complex.I * aeval ξ Q₂‖ * (X * B ^ (2 * M)) := hL
      _ ≤ ‖aeval ξ Q₁ + Complex.I * aeval ξ Q₂‖ * (2 * (M + 1) * A * B ^ M)
          * (X * B ^ (2 * M)) := by gcongr
      _ = ‖aeval ξ Q₁ + Complex.I * aeval ξ Q₂‖ * (2 * (M + 1) * A * X * B ^ (3 * M)) := by
        rw [show 3 * M = M + 2 * M by ring, pow_add]
        ring

/-! ### Lemma 5: the value of a polynomial near a root -/

theorem prod_map_le_prod_map_of_mem {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hfg : ∀ a ∈ s, f a ≤ g a) : (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul (hfg a (Multiset.mem_cons_self a s))
      (ih fun b hb => hfg b (Multiset.mem_cons_of_mem hb)) (prod_map_nonneg s f hf)
      ((hf a).trans (hfg a (Multiset.mem_cons_self a s)))

/-- The derivative of an integer polynomial of degree `n` and height `≤ H` has height
`≤ n H`. -/
theorem abs_coeff_derivative_le {p : ℤ[X]} {H : ℝ} (hH : ∀ i, |(p.coeff i : ℝ)| ≤ H) (i : ℕ) :
    |((derivative p).coeff i : ℝ)| ≤ p.natDegree * H := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  rw [coeff_derivative]
  by_cases hi : i + 1 ≤ p.natDegree
  · push_cast
    rw [abs_mul, mul_comm]
    have h1 : |((i : ℝ) + 1)| ≤ p.natDegree := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hi
    exact mul_le_mul h1 (hH _) (abs_nonneg _) (Nat.cast_nonneg _)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [zero_mul, Int.cast_zero, abs_zero]
    positivity

/-- **Fel'dman, Lemma 5** (for an irreducible polynomial): if `ξ` is a root of `p` nearest to
`ζ`, then `|ζ − ξ| ≤ |p(ζ)| · 2^(n−1) (n² H)^(n−1) ((n + 1) H)^(n−1)`. -/
theorem norm_aeval_ge_dist_root {p : ℤ[X]} (hp : Irreducible p) (hn : p.natDegree ≠ 0)
    {ξ ζ : ℂ} (hξ : aeval ξ p = 0) (hnear : ∀ η, aeval η p = 0 → ‖ζ - ξ‖ ≤ ‖ζ - η‖) {H : ℝ}
    (hH : ∀ i, |(p.coeff i : ℝ)| ≤ H) :
    ‖ζ - ξ‖ ≤ ‖aeval ζ p‖ * (2 ^ (p.natDegree - 1)
      * (p.natDegree * (p.natDegree * H)) ^ (p.natDegree - 1)
      * ((p.natDegree + 1) * H) ^ (p.natDegree - 1)) := by
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  have hsplit : (toC p).Splits := IsAlgClosed.splits _
  have hp0 : toC p ≠ 0 := fun h => hn (by rw [← natDegree_toC, h, natDegree_zero])
  have hmem : ξ ∈ (toC p).roots := by
    rw [mem_roots hp0, IsRoot, ← aeval_eq_eval_toC]
    exact hξ
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem
  have hcard : Multiset.card t = p.natDegree - 1 := by
    have := hsplit.natDegree_eq_card_roots
    rw [natDegree_toC, ht, Multiset.card_cons] at this
    omega
  -- `p = (X − ξ) q`
  set q : ℂ[X] := C (toC p).leadingCoeff * (t.map fun a => X - C a).prod with hq
  have hfac : toC p = (X - C ξ) * q := by
    conv_lhs => rw [hsplit.eq_prod_roots, ht, Multiset.map_cons, Multiset.prod_cons]
    rw [hq]
    ring
  have hqeval : ∀ z : ℂ, q.eval z = (toC p).leadingCoeff * (t.map fun a => z - a).prod := by
    intro z
    rw [hq, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  have hval : aeval ζ p = (ζ - ξ) * q.eval ζ := by
    rw [aeval_eq_eval_toC, hfac, eval_mul, eval_sub, eval_X, eval_C]
  have hder : aeval ξ (derivative p) = q.eval ξ := by
    have hfac' : map (Int.castRingHom ℂ) p = (X - C ξ) * q := hfac
    rw [aeval_eq_eval_toC, toC, ← derivative_map, hfac', derivative_mul]
    simp
  -- the other roots are at least half as far from `ζ` as from `ξ`
  have hhalf : ‖q.eval ξ‖ ≤ 2 ^ (p.natDegree - 1) * ‖q.eval ζ‖ := by
    rw [hqeval, hqeval, norm_mul, norm_mul, norm_prod_map, norm_prod_map]
    have h1 : (t.map fun a => ‖ξ - a‖).prod ≤ (t.map fun a => 2 * ‖ζ - a‖ ^ 1).prod :=
      prod_map_le_prod_map_of_mem _ _ _ (fun a => norm_nonneg _) fun a ha => by
        have hroot : aeval a p = 0 := by
          rw [aeval_eq_eval_toC]
          exact (mem_roots hp0).mp (by rw [ht]; exact Multiset.mem_cons_of_mem ha)
        have h2 := hnear a hroot
        have h3 : ‖ξ - a‖ ≤ ‖ζ - ξ‖ + ‖ζ - a‖ := by
          have := norm_sub_le (ζ - a) (ζ - ξ)
          rw [show ζ - a - (ζ - ξ) = ξ - a by ring] at this
          linarith
        rw [pow_one]
        linarith
    rw [prod_map_const_mul_pow, pow_one, hcard] at h1
    calc ‖(toC p).leadingCoeff‖ * (t.map fun a => ‖ξ - a‖).prod
        ≤ ‖(toC p).leadingCoeff‖ * (2 ^ (p.natDegree - 1) * (t.map fun a => ‖ζ - a‖).prod) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 2 ^ (p.natDegree - 1) * (‖(toC p).leadingCoeff‖ * (t.map fun a => ‖ζ - a‖).prod) := by
          ring
  -- `p′(ξ) ≠ 0`, bounded below by Liouville's inequality
  have hsep : aeval ξ (derivative p) ≠ 0 := by
    have hq' : Irreducible (p.map (Int.castRingHom ℚ)) :=
      (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hp.isPrimitive hn)).mp hp
    have h1 : aeval ξ (p.map (Int.castRingHom ℚ)) = 0 := by
      rw [show aeval ξ (p.map (Int.castRingHom ℚ)) = aeval ξ p from aeval_map_algebraMap ℚ ξ p]
      exact hξ
    have h2 := hq'.separable.aeval_derivative_ne_zero h1
    rwa [derivative_map,
      show aeval ξ ((derivative p).map (Int.castRingHom ℚ)) = aeval ξ (derivative p) from
        aeval_map_algebraMap ℚ ξ (derivative p)] at h2
  have hL := liouville_int hp hn hξ hsep (M := p.natDegree - 1) (natDegree_derivative_le p)
    (abs_coeff_derivative_le hH) hH
  have hcast : (((p.natDegree - 1 : ℕ) : ℝ) + 1) = p.natDegree := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast, hder] at hL
  set Lb : ℝ := (p.natDegree * (p.natDegree * H)) ^ (p.natDegree - 1)
    * ((p.natDegree + 1) * H) ^ (p.natDegree - 1) with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  rw [hval, norm_mul]
  have hd0 : 0 ≤ ‖ζ - ξ‖ := norm_nonneg _
  calc ‖ζ - ξ‖ = ‖ζ - ξ‖ * 1 := (mul_one _).symm
    _ ≤ ‖ζ - ξ‖ * (‖q.eval ξ‖ * Lb) := mul_le_mul_of_nonneg_left hL hd0
    _ ≤ ‖ζ - ξ‖ * (2 ^ (p.natDegree - 1) * ‖q.eval ζ‖ * Lb) := by gcongr
    _ = ‖ζ - ξ‖ * ‖q.eval ζ‖ * (2 ^ (p.natDegree - 1)
          * (p.natDegree * (p.natDegree * H)) ^ (p.natDegree - 1)
          * ((p.natDegree + 1) * H) ^ (p.natDegree - 1)) := by
        rw [hLb]; ring

end Azurite.Feldman
