/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Order.IntermediateValue

/-!
# DLMF §1.11: Zeros of Polynomials

Formalizations of <https://dlmf.nist.gov/1.11>, one theorem per equation, named `dlmf_1_11_N`;
statements made in the prose are named `dlmf_1_11_ii_<topic>`.  Polynomials are Mathlib's
`Polynomial`; zeros are counted with multiplicity through `Polynomial.roots`.

## §1.11(ii) Elementary properties

* `dlmf_1_11_ii_card_roots`, `dlmf_1_11_ii_card_roots_real`: exactly `n` complex zeros counting
  multiplicity.
* `dlmf_1_11_ii_odd` (monic, odd degree: a real zero of sign opposite to the constant term),
  `dlmf_1_11_ii_even` (monic, even degree, negative constant term: zeros of both signs);
  helpers `monic_tendsto_atTop`, `exists_root_Ioo_of_mul_neg`, `monic_exists_pos_root`.
* Descartes' rule of signs: `dlmf_1_11_ii_descartes` (bound from Mathlib, parity proven here via
  `neg_one_pow_countP_roots_pos` and `neg_one_pow_signVariations_poly`: both `(−1)^count` equal
  `sign aₙ · sign a₀`), `dlmf_1_11_ii_descartes_neg` (negative zeros via `f(−z)`),
  `signVariations_X_pow_mul`.
* 1.11.8 `exampleF`, `dlmf_1_11_8`, `dlmf_1_11_ii_example` (one positive, one negative and six
  non-real zeros).
* `dlmf_1_11_ii_reverse_coeff`, `dlmf_1_11_ii_reverse`: the zeros of `zⁿ f(1/z)` are the
  reciprocals of those of `f`.
* 1.11.9 `discriminantOfZeros`, `dlmf_1_11_9` (Mathlib's `Polynomial.discr` equals
  `aₙ^{2n−2} ∏_{j<k} (zⱼ − zₖ)²`; `prod_prod_erase_sub`, `sum_card_Ioi`), `dlmf_1_11_9_complex`.
* 1.11.10 `dlmf_1_11_10` (`k`-th elementary symmetric function `= (−1)ᵏ aₙ₋ₖ/aₙ`),
  `dlmf_1_11_10_sum`, `dlmf_1_11_10_pairs`, `dlmf_1_11_10_prod`.
-/

namespace Azurite.DLMF

open Polynomial Filter Topology

/-! ### Number of zeros -/

/-- **DLMF §1.11(ii)**: a polynomial of degree `n` with complex coefficients has exactly `n`
complex zeros counting multiplicity. -/
theorem dlmf_1_11_ii_card_roots (f : ℂ[X]) : f.roots.card = f.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

/-- **DLMF §1.11(ii)**: a polynomial of degree `n` with real coefficients has exactly `n` complex
zeros counting multiplicity. -/
theorem dlmf_1_11_ii_card_roots_real (f : ℝ[X]) :
    (f.map Complex.ofRealHom).roots.card = f.natDegree :=
  IsAlgClosed.card_roots_map_eq_natDegree_of_injective f Complex.ofRealHom.injective

/-! ### Real zeros of monic polynomials -/

/-- A monic real polynomial of positive degree tends to `+∞` at `+∞`. -/
theorem monic_tendsto_atTop {f : ℝ[X]} (hf : f.Monic) (hd : 0 < f.natDegree) :
    Tendsto (fun x => f.eval x) atTop atTop :=
  f.tendsto_atTop_of_leadingCoeff_nonneg (natDegree_pos_iff_degree_pos.mp hd)
    (by rw [hf.leadingCoeff]; exact zero_le_one)

/-- A real polynomial with `f(a) < 0 < f(b)` or `f(b) < 0 < f(a)` has a zero strictly between. -/
theorem exists_root_Ioo_of_mul_neg {f : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : f.eval a * f.eval b < 0) : ∃ x ∈ Set.Ioo a b, f.IsRoot x := by
  have hc : ContinuousOn (fun x => f.eval x) (Set.Icc a b) := f.continuous.continuousOn
  have ha : f.eval a ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h
  have hb : f.eval b ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hab hc ⟨h2.le, h1.le⟩
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hx0⟩
    · rintro rfl; exact ha hx0
    · rintro rfl; exact hb hx0
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hab hc ⟨h1.le, h2.le⟩
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hx0⟩
    · rintro rfl; exact ha hx0
    · rintro rfl; exact hb hx0

/-- A monic real polynomial of positive degree with `f(0) < 0` has a positive zero. -/
theorem monic_exists_pos_root {f : ℝ[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    (h0 : f.eval 0 < 0) : ∃ x, 0 < x ∧ f.IsRoot x := by
  obtain ⟨b, hfb, hb⟩ := (((monic_tendsto_atTop hf hd).eventually (eventually_gt_atTop 0)).and
    (eventually_gt_atTop 0)).exists
  obtain ⟨x, hx, hroot⟩ := exists_root_Ioo_of_mul_neg hb.le (mul_neg_of_neg_of_pos h0 hfb)
  exact ⟨x, hx.1, hroot⟩

/-- `f(−x)` for a polynomial `f`, as a polynomial. -/
theorem eval_comp_neg_X (f : ℝ[X]) (x : ℝ) : (f.comp (-X)).eval x = f.eval (-x) := by
  simp

/-- **DLMF §1.11(ii)**: every monic polynomial of odd degree with real coefficients has at least
one real zero with sign opposite to that of the constant term. -/
theorem dlmf_1_11_ii_odd {f : ℝ[X]} (hf : f.Monic) (hodd : Odd f.natDegree) :
    ∃ x, f.IsRoot x ∧ SignType.sign x = -SignType.sign (f.coeff 0) := by
  have hd : 0 < f.natDegree := hodd.pos
  rcases lt_trichotomy (f.coeff 0) 0 with h | h | h
  · obtain ⟨x, hx, hroot⟩ := monic_exists_pos_root hf hd (by rwa [← coeff_zero_eq_eval_zero])
    exact ⟨x, hroot, by rw [sign_pos hx, sign_neg h]; rfl⟩
  · refine ⟨0, ?_, by rw [h]; simp⟩
    rw [IsRoot, ← coeff_zero_eq_eval_zero, h]
  · -- `g(x) = −f(−x)` is monic of odd degree with `g(0) < 0`
    set g := -f.comp (-X) with hg
    have hgn : g.natDegree = f.natDegree := by
      rw [hg, natDegree_neg, natDegree_comp]; simp
    have hgm : g.Monic := by
      rw [Monic, hg, leadingCoeff_neg, comp_neg_X_leadingCoeff_eq, hf.leadingCoeff,
        hodd.neg_one_pow]
      norm_num
    obtain ⟨x, hx, hroot⟩ := monic_exists_pos_root hgm (hgn ▸ hd)
      (by rw [hg, eval_neg, eval_comp_neg_X, neg_zero, ← coeff_zero_eq_eval_zero]; linarith)
    refine ⟨-x, ?_, by rw [sign_neg (neg_neg_of_pos hx), sign_pos h]⟩
    have : (-f.comp (-X)).eval x = 0 := hroot
    rw [eval_neg, eval_comp_neg_X, neg_eq_zero] at this
    exact this

/-- **DLMF §1.11(ii)**: a monic polynomial of even degree with real coefficients has at least two
zeros of opposite signs when the constant term is negative. -/
theorem dlmf_1_11_ii_even {f : ℝ[X]} (hf : f.Monic) (heven : Even f.natDegree)
    (h0 : f.coeff 0 < 0) : ∃ x y, x < 0 ∧ 0 < y ∧ f.IsRoot x ∧ f.IsRoot y := by
  have hd : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h | h
    · rw [eq_C_of_natDegree_eq_zero h] at hf
      have := hf.leadingCoeff
      rw [leadingCoeff_C] at this
      rw [this] at h0
      exact absurd h0 (by norm_num)
    · exact h
  obtain ⟨y, hy, hry⟩ := monic_exists_pos_root hf hd (by rwa [← coeff_zero_eq_eval_zero])
  set g := f.comp (-X) with hg
  have hgn : g.natDegree = f.natDegree := by rw [hg, natDegree_comp]; simp
  have hgm : g.Monic := by
    rw [Monic, hg, comp_neg_X_leadingCoeff_eq, hf.leadingCoeff, heven.neg_one_pow]
    norm_num
  obtain ⟨x, hx, hrx⟩ := monic_exists_pos_root hgm (hgn ▸ hd)
    (by rw [hg, eval_comp_neg_X, neg_zero, ← coeff_zero_eq_eval_zero]; exact h0)
  refine ⟨-x, y, neg_neg_of_pos hx, hy, ?_, hry⟩
  rw [IsRoot, hg, eval_comp_neg_X] at hrx
  exact hrx

/-! ### Reciprocal zeros -/

/-- **DLMF §1.11(ii)**: `zⁿ f(1/z) = a₀ zⁿ + a₁ zⁿ⁻¹ + ⋯ + aₙ` is Mathlib's `reverse`, whose
coefficients are those of `f` in reverse order. -/
theorem dlmf_1_11_ii_reverse_coeff {K : Type*} [Field K] (f : K[X]) {k : ℕ}
    (hk : k ≤ f.natDegree) : f.reverse.coeff k = f.coeff (f.natDegree - k) := by
  rw [coeff_reverse, revAt_le hk]

/-- **DLMF §1.11(ii)**: the zeros of `zⁿ f(1/z)` are the reciprocals of the zeros of `f`. -/
theorem dlmf_1_11_ii_reverse {K : Type*} [Field K] (f : K[X]) {z : K} (hz : z ≠ 0) :
    f.reverse.IsRoot z⁻¹ ↔ f.IsRoot z := by
  let _ : Invertible z := invertibleOfNonzero hz
  have := eval₂_reverse_eq_zero_iff (RingHom.id K) z f
  rwa [invOf_eq_inv, eval₂_id, eval₂_id] at this

/-! ### Elementary symmetric functions of the zeros -/

/-- **DLMF 1.11.10**: for `f = aₙzⁿ + ⋯ + a₀` of degree `n` with zeros `z₁, …, zₙ` (counted with
multiplicity; over `ℂ` every polynomial has `n` of them), the `k`-th elementary symmetric function
of the zeros is `(−1)ᵏ aₙ₋ₖ/aₙ`. -/
theorem dlmf_1_11_10 {K : Type*} [Field K] {f : K[X]} (hf0 : f ≠ 0)
    (hf : f.roots.card = f.natDegree) {k : ℕ} (hk : k ≤ f.natDegree) :
    f.roots.esymm k = (-1) ^ k * f.coeff (f.natDegree - k) / f.leadingCoeff := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  rw [coeff_eq_esymm_roots_of_card hf (Nat.sub_le _ _), Nat.sub_sub_self hk]
  field_simp
  have h1 : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [h1, mul_one]

/-- **DLMF 1.11.10**: `z₁ + z₂ + ⋯ + zₙ = −aₙ₋₁/aₙ`. -/
theorem dlmf_1_11_10_sum {K : Type*} [Field K] {f : K[X]} (hf0 : f ≠ 0)
    (hf : f.roots.card = f.natDegree) (hn : 1 ≤ f.natDegree) :
    f.roots.sum = -f.coeff (f.natDegree - 1) / f.leadingCoeff := by
  have h := dlmf_1_11_10 hf0 hf hn
  simp only [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map,
    Function.comp_def, Multiset.prod_singleton, Multiset.map_id'] at h
  rw [h]
  ring

/-- **DLMF 1.11.10**: `∑_{j<k} zⱼ zₖ = aₙ₋₂/aₙ`. -/
theorem dlmf_1_11_10_pairs {K : Type*} [Field K] {f : K[X]} (hf0 : f ≠ 0)
    (hf : f.roots.card = f.natDegree) (hn : 2 ≤ f.natDegree) :
    f.roots.esymm 2 = f.coeff (f.natDegree - 2) / f.leadingCoeff := by
  rw [dlmf_1_11_10 hf0 hf hn]
  ring

/-- **DLMF 1.11.10**: `z₁ z₂ ⋯ zₙ = (−1)ⁿ a₀/aₙ`. -/
theorem dlmf_1_11_10_prod {K : Type*} [Field K] {f : K[X]} (hf0 : f ≠ 0)
    (hf : f.roots.card = f.natDegree) :
    f.roots.prod = (-1) ^ f.natDegree * f.coeff 0 / f.leadingCoeff := by
  have h := dlmf_1_11_10 hf0 hf le_rfl
  rw [Nat.sub_self, Multiset.esymm, ← hf, Multiset.powersetCard_self, Multiset.map_singleton,
    Multiset.sum_singleton] at h
  rw [h, hf]

/-! ### Descartes' rule of signs

Mathlib proves the bound `Polynomial.roots_countP_pos_le_signVariations`; the parity statement is
proven here: both numbers are even exactly when the leading coefficient and the lowest nonzero
coefficient have the same sign. -/

section Descartes

open SignType

theorem sign_mul_self_of_ne_zero {a : ℝ} (ha : a ≠ 0) : sign a * sign a = 1 := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [sign_neg h]; rfl
  · rw [sign_pos h]; rfl

theorem neg_one_pow_ite_sign {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (-1 : SignType) ^ (if sign a = sign b then 0 else 1) = sign a * sign b := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb <;>
    simp [sign_neg, sign_pos, ha, hb]

/-- For a list of reals with nonzero first and last entries, `(−1)^(sign changes)` is the
product of the signs of the first and last entries. -/
theorem neg_one_pow_signVariations :
    ∀ (l : List ℝ) (h : l ≠ []), l.head h ≠ 0 → l.getLast h ≠ 0 →
      (-1 : SignType) ^ l.signVariations = sign (l.head h) * sign (l.getLast h) := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  intro h hhead hlast
  match l, h, hhead, hlast, hn with
  | [a], _, ha, _, _ =>
    simp only [List.head_cons] at ha
    simp only [List.signVariations_singleton, pow_zero, List.head_cons, List.getLast_singleton]
    exact (sign_mul_self_of_ne_zero ha).symm
  | a :: b :: rest, _, ha, hl, hn =>
    simp only [List.head_cons] at ha ⊢
    by_cases hb : b = 0
    · subst hb
      have hrest : rest ≠ [] := by
        rintro rfl
        simp at hl
      have hlast' : (a :: rest).getLast (List.cons_ne_nil a rest) =
          (a :: 0 :: rest).getLast (List.cons_ne_nil _ _) := by
        simp [List.getLast_cons hrest]
      rw [List.signVariations_cons_zero_cons, ← hlast',
        ih (a :: rest).length (by simp at hn ⊢; omega) (a :: rest) rfl (List.cons_ne_nil _ _)
          ha (by rwa [hlast'])]
      rfl
    · have hlast' : (b :: rest).getLast (List.cons_ne_nil b rest) =
          (a :: b :: rest).getLast (List.cons_ne_nil _ _) := by
        simp
      rw [List.signVariations_cons_cons_of_ne_zero rest ha hb, pow_add, ← hlast',
        ih (b :: rest).length (by simp at hn ⊢; omega) (b :: rest) rfl (List.cons_ne_nil _ _)
          hb (by rwa [hlast']), neg_one_pow_ite_sign ha hb]
      simp only [List.head_cons]
      calc sign b * sign ((b :: rest).getLast _) * (sign a * sign b)
          = sign a * (sign b * sign b) * sign ((b :: rest).getLast _) := by ac_rfl
        _ = _ := by rw [sign_mul_self_of_ne_zero hb, mul_one]

theorem coeffList_getLast {P : ℝ[X]} (h : P.coeffList ≠ []) :
    P.coeffList.getLast h = P.coeff 0 := by
  simp only [coeffList]
  rw [List.getLast_map, List.getLast_reverse]
  simp

theorem coeffList_head {P : ℝ[X]} (hP : P ≠ 0) (h : P.coeffList ≠ []) :
    P.coeffList.head h = P.leadingCoeff := by
  have := head?_coeffList hP
  rw [List.head?_eq_some_head h] at this
  exact Option.some_injective _ this

/-- `(−1)^(sign changes of the coefficients) = sign(aₙ) sign(a₀)` when `a₀ ≠ 0`. -/
theorem neg_one_pow_signVariations_poly {P : ℝ[X]} (hP : P ≠ 0) (h0 : P.coeff 0 ≠ 0) :
    (-1 : SignType) ^ P.signVariations = sign P.leadingCoeff * sign (P.coeff 0) := by
  have hne : P.coeffList ≠ [] := by rwa [ne_eq, coeffList_eq_nil]
  rw [Polynomial.signVariations, neg_one_pow_signVariations P.coeffList hne
    (by rw [coeffList_head hP]; exact leadingCoeff_ne_zero.mpr hP)
    (by rwa [coeffList_getLast]), coeffList_head hP, coeffList_getLast]

/-- A real polynomial with no positive zero has `sign R(0) = sign(leading coefficient)`. -/
theorem sign_eval_zero_eq_sign_leadingCoeff {R : ℝ[X]} (hR : R ≠ 0) (h0 : R.eval 0 ≠ 0)
    (hpos : ∀ t ∈ R.roots, ¬ 0 < t) : sign (R.eval 0) = sign R.leadingCoeff := by
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  by_contra hne
  have hneg : R.eval 0 * R.leadingCoeff < 0 := by
    rcases lt_or_gt_of_ne h0 with h1 | h1 <;> rcases lt_or_gt_of_ne hlc with h2 | h2
    · exact absurd (by rw [sign_neg h1, sign_neg h2]) hne
    · exact mul_neg_of_neg_of_pos h1 h2
    · exact mul_neg_of_pos_of_neg h1 h2
    · exact absurd (by rw [sign_pos h1, sign_pos h2]) hne
  -- for large `x`, `R(x)` has the sign of the leading coefficient
  obtain ⟨x, hx, hxs⟩ : ∃ x, 0 < x ∧ 0 < R.eval x * R.leadingCoeff := by
    rcases Nat.eq_zero_or_pos R.natDegree with hd | hd
    · have hRC := eq_C_of_natDegree_eq_zero hd
      have : R.eval 0 = R.leadingCoeff := by
        rw [hRC, eval_C, leadingCoeff_C]
      rw [this] at hneg
      exact absurd hneg (not_lt.mpr (mul_self_nonneg _))
    · have hdeg : 0 < R.degree := natDegree_pos_iff_degree_pos.mp hd
      rcases lt_or_gt_of_ne hlc with h2 | h2
      · have ht := (-R).tendsto_atTop_of_leadingCoeff_nonneg (by rwa [degree_neg])
          (by rw [leadingCoeff_neg]; linarith)
        obtain ⟨x, hxR, hx⟩ := ((ht.eventually (eventually_gt_atTop 0)).and
          (eventually_gt_atTop 0)).exists
        rw [eval_neg] at hxR
        exact ⟨x, hx, mul_pos_of_neg_of_neg (by linarith) h2⟩
      · have ht := R.tendsto_atTop_of_leadingCoeff_nonneg hdeg h2.le
        obtain ⟨x, hxR, hx⟩ := ((ht.eventually (eventually_gt_atTop 0)).and
          (eventually_gt_atTop 0)).exists
        exact ⟨x, hx, mul_pos hxR h2⟩
  have hprod : R.eval 0 * R.eval x < 0 := by
    have h3 : 0 < R.leadingCoeff * R.leadingCoeff := mul_self_pos.mpr hlc
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨t, ht, hroot⟩ := exists_root_Ioo_of_mul_neg hx.le hprod
  exact hpos t ((mem_roots hR).mpr hroot) ht.1

/-- `(−1)^(number of positive zeros) = sign(aₙ) sign(a₀)` when `a₀ ≠ 0`. -/
theorem neg_one_pow_countP_roots_pos {P : ℝ[X]} (hP : P ≠ 0) (h0 : P.coeff 0 ≠ 0) :
    (-1 : SignType) ^ P.roots.countP (0 < ·) = sign P.leadingCoeff * sign (P.coeff 0) := by
  classical
  set s := P.roots.filter (0 < ·) with hs
  set Q := (s.map fun a => X - C a).prod with hQ
  obtain ⟨R, hPR⟩ : Q ∣ P := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP s).mpr
    (Multiset.filter_le _ _)
  have hR : R ≠ 0 := by rintro rfl; rw [mul_zero] at hPR; exact hP hPR
  have hQm : Q.Monic := monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hroots : P.roots = s + R.roots := by
    rw [hPR, roots_mul (hPR ▸ hP), roots_multiset_prod_X_sub_C]
  have hcount : P.roots.countP (0 < ·) = s.card := Multiset.countP_eq_card_filter _ _
  have hRpos : ∀ t ∈ R.roots, ¬ 0 < t := by
    have h2 : P.roots.countP (0 < ·) = s.card + R.roots.countP (0 < ·) := by
      rw [hroots, Multiset.countP_add, Multiset.countP_eq_card.mpr
        (fun a ha => (Multiset.mem_filter.mp ha).2)]
    exact Multiset.countP_eq_zero.mp (show R.roots.countP (0 < ·) = 0 by omega)
  -- the value at `0`
  have hQ0 : Q.eval 0 = (-1) ^ s.card * s.prod := by
    rw [hQ, eval_multiset_prod, Multiset.map_map]
    have : (eval 0 ∘ fun a => X - C a) = fun a : ℝ => -a := by
      funext a; simp
    rw [this, Multiset.prod_map_neg]
  have hsprod : 0 < s.prod := Multiset.prod_pos fun a ha => (Multiset.mem_filter.mp ha).2
  have hP0 : P.coeff 0 = Q.eval 0 * R.eval 0 := by
    rw [coeff_zero_eq_eval_zero, hPR, eval_mul]
  have hR0 : R.eval 0 ≠ 0 := by
    intro h; rw [h, mul_zero] at hP0; exact h0 hP0
  have hlc : P.leadingCoeff = R.leadingCoeff := by
    rw [hPR, leadingCoeff_mul, hQm.leadingCoeff, one_mul]
  have hsignR := sign_eval_zero_eq_sign_leadingCoeff hR hR0 hRpos
  rw [hcount, hlc, hP0, hQ0, sign_mul, sign_mul, sign_pos hsprod, mul_one, ← hsignR]
  have hpow : sign ((-1 : ℝ) ^ s.card) = (-1 : SignType) ^ s.card := by
    rw [sign_pow, sign_neg (by norm_num : (-1 : ℝ) < 0)]
  rw [hpow, mul_left_comm, sign_mul_self_of_ne_zero hR0, mul_one]

theorem nat_mod_two_eq_of_neg_one_pow_eq {a b : ℕ} (h : (-1 : SignType) ^ a = (-1) ^ b) :
    a % 2 = b % 2 := by
  rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd b with hb | hb
  · rw [Nat.even_iff.mp ha, Nat.even_iff.mp hb]
  · rw [ha.neg_one_pow, hb.neg_one_pow] at h; exact absurd h (by decide)
  · rw [ha.neg_one_pow, hb.neg_one_pow] at h; exact absurd h (by decide)
  · rw [Nat.odd_iff.mp ha, Nat.odd_iff.mp hb]

/-- Multiplying by a power of `X` does not change the sign changes of the coefficients. -/
theorem signVariations_X_pow_mul (Q : ℝ[X]) (k : ℕ) :
    (X ^ k * Q).signVariations = Q.signVariations := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  have hPk : X ^ k * Q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
  have hdeg : (X ^ k * Q).natDegree = Q.natDegree + k := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hQ, natDegree_X_pow, add_comm]
  have hcl : (X ^ k * Q).coeffList = Q.coeffList ++ List.replicate k 0 := by
    simp only [coeffList, withBotSucc_degree_eq_natDegree_add_one hPk,
      withBotSucc_degree_eq_natDegree_add_one hQ, hdeg]
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.length_map, List.length_reverse, List.length_range] at h1
    rw [List.getElem_map, List.getElem_reverse, List.getElem_range, coeff_X_pow_mul']
    simp only [List.length_range]
    by_cases hi : i < Q.natDegree + 1
    · have hc : k ≤ Q.natDegree + k + 1 - 1 - i := by omega
      rw [List.getElem_append_left (by simpa using hi), List.getElem_map, List.getElem_reverse,
        List.getElem_range]
      simp only [hc, ↓reduceIte, List.length_range]
      congr 1
      omega
    · have hc : ¬ k ≤ Q.natDegree + k + 1 - 1 - i := by omega
      rw [List.getElem_append_right (by simpa using hi), List.getElem_replicate]
      simp only [hc, ↓reduceIte]
  simp only [Polynomial.signVariations, hcl, List.signVariations, List.map_append,
    List.filter_append, List.map_replicate, sign_zero]
  simp

/-- **DLMF §1.11(ii)**, Descartes' rule of signs: the number of positive zeros (counted with
multiplicity) of a nonzero real polynomial cannot exceed the number of sign changes of its
coefficients, and the two numbers have the same parity. -/
theorem dlmf_1_11_ii_descartes {P : ℝ[X]} (hP : P ≠ 0) :
    P.roots.countP (0 < ·) ≤ P.signVariations ∧
      P.roots.countP (0 < ·) % 2 = P.signVariations % 2 := by
  refine ⟨roots_countP_pos_le_signVariations P, ?_⟩
  obtain ⟨q, hPq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  rw [map_zero, sub_zero] at hPq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (X_dvd_iff.mpr h)
  have hqne : q ≠ 0 := by rintro rfl; exact hq (dvd_zero _)
  have hcount : P.roots.countP (0 < ·) = q.roots.countP (0 < ·) := by
    rw [hPq, roots_mul (hPq ▸ hP), roots_X_pow, Multiset.countP_add, Multiset.countP_nsmul,
      Multiset.countP_eq_zero.mpr (by simp), mul_zero, zero_add]
  rw [hcount, hPq, signVariations_X_pow_mul]
  exact nat_mod_two_eq_of_neg_one_pow_eq (by
    rw [neg_one_pow_countP_roots_pos hqne hq0, neg_one_pow_signVariations_poly hqne hq0])

/-- **DLMF §1.11(ii)**: the same holds for `f(−z)`, hence for the negative zeros of `f(z)`. -/
theorem dlmf_1_11_ii_descartes_neg {P : ℝ[X]} (hP : P ≠ 0) :
    P.roots.countP (· < 0) = (P.comp (-X)).roots.countP (0 < ·) ∧
      P.roots.countP (· < 0) ≤ (P.comp (-X)).signVariations ∧
      P.roots.countP (· < 0) % 2 = (P.comp (-X)).signVariations % 2 := by
  have h : P.roots.countP (· < 0) = (P.comp (-X)).roots.countP (0 < ·) := by
    rw [roots_comp_neg_X, Multiset.countP_map, Multiset.countP_eq_card_filter]
    congr 1
    exact Multiset.filter_congr fun x _ => by simp
  have hP' : P.comp (-X) ≠ 0 := by
    intro h0
    have := congrArg (fun p => p.comp (-X)) h0
    simp only [comp_neg_X_comp_neg_X, zero_comp] at this
    exact hP this
  rw [h]
  exact ⟨rfl, dlmf_1_11_ii_descartes hP'⟩

end Descartes

/-! ### Example 1.11.8 -/

section Example

/-- The polynomial `f(z) = z⁸ + 10z³ + z − 4` of DLMF 1.11.8. -/
noncomputable def exampleF : ℝ[X] := X ^ 8 + 10 * X ^ 3 + X - 4

theorem exampleF_natDegree : exampleF.natDegree = 8 := by
  unfold exampleF; compute_degree!

theorem exampleF_ne_zero : exampleF ≠ 0 := by
  intro h; have := exampleF_natDegree; rw [h, natDegree_zero] at this; norm_num at this

/-- **DLMF 1.11.8**: `f(−z) = z⁸ − 10z³ − z − 4`. -/
theorem dlmf_1_11_8 : exampleF.comp (-X) = X ^ 8 - 10 * X ^ 3 - X - 4 := by
  simp only [exampleF, sub_comp, add_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
  ring

theorem exampleF_coeffList : exampleF.coeffList = [1, 0, 0, 0, 0, 10, 0, 1, -4] := by
  rw [coeffList, withBotSucc_degree_eq_natDegree_add_one exampleF_ne_zero, exampleF_natDegree]
  simp [List.range_succ, exampleF, coeff_X, coeff_X_pow]

theorem exampleF_neg_coeffList :
    (exampleF.comp (-X)).coeffList = [1, 0, 0, 0, 0, -10, 0, -1, -4] := by
  have hne : exampleF.comp (-X) ≠ 0 := by
    intro h
    have := congrArg (fun p => p.comp (-X)) h
    simp only [comp_neg_X_comp_neg_X, zero_comp] at this
    exact exampleF_ne_zero this
  have hdeg : (exampleF.comp (-X)).natDegree = 8 := by
    rw [natDegree_comp, exampleF_natDegree, natDegree_neg, natDegree_X]
  rw [coeffList, withBotSucc_degree_eq_natDegree_add_one hne, hdeg, dlmf_1_11_8]
  simp [List.range_succ, coeff_X, coeff_X_pow]

/-- **DLMF §1.11(ii)**, example 1.11.8: `f` and `f(−z)` each have one change of sign; hence `f` has
exactly one positive zero, one negative zero, and six non-real complex zeros (with
multiplicity). -/
theorem dlmf_1_11_ii_example :
    exampleF.signVariations = 1 ∧ (exampleF.comp (-X)).signVariations = 1 ∧
      exampleF.roots.countP (0 < ·) = 1 ∧ exampleF.roots.countP (· < 0) = 1 ∧
      exampleF.roots.card = 2 ∧
      (exampleF.map Complex.ofRealHom).roots.countP (fun z => z.im ≠ 0) = 6 := by
  classical
  have hs1 : exampleF.signVariations = 1 := by
    rw [Polynomial.signVariations, exampleF_coeffList]
    norm_num [List.signVariations_cons_zero_cons, List.signVariations_cons_cons_of_ne_zero,
      List.signVariations_singleton]
  have hs2 : (exampleF.comp (-X)).signVariations = 1 := by
    rw [Polynomial.signVariations, exampleF_neg_coeffList]
    norm_num [List.signVariations_cons_zero_cons, List.signVariations_cons_cons_of_ne_zero,
      List.signVariations_singleton]
  have hpos : exampleF.roots.countP (0 < ·) = 1 := by
    have := dlmf_1_11_ii_descartes exampleF_ne_zero
    rw [hs1] at this
    omega
  have hneg : exampleF.roots.countP (· < 0) = 1 := by
    have := dlmf_1_11_ii_descartes_neg exampleF_ne_zero
    rw [hs2] at this
    omega
  have h0 : ¬ exampleF.IsRoot 0 := by
    simp [exampleF]
  have hcard : exampleF.roots.card = 2 := by
    rw [Multiset.card_eq_countP_add_countP (fun x : ℝ => 0 < x), hpos]
    have : exampleF.roots.countP (fun x => ¬ 0 < x) = exampleF.roots.countP (· < 0) :=
      Multiset.countP_congr rfl fun x hx => by
        have hx0 : x ≠ 0 := fun h => h0 (h ▸ (mem_roots exampleF_ne_zero).mp hx)
        refine propext ⟨fun h => lt_of_le_of_ne (not_lt.mp h) hx0, fun h => not_lt.mpr h.le⟩
    rw [this, hneg]
  refine ⟨hs1, hs2, hpos, hneg, hcard, ?_⟩
  have hC := dlmf_1_11_ii_card_roots_real exampleF
  rw [exampleF_natDegree] at hC
  have hreal := filter_roots_map_range_eq_map_roots Complex.ofRealHom.injective exampleF
  have hrange : ∀ z : ℂ, z ∈ Complex.ofRealHom.range ↔ z.im = 0 := fun z =>
    ⟨fun ⟨x, hx⟩ => by rw [← hx]; simp, fun h => ⟨z.re, Complex.ext (by simp) (by simp [h])⟩⟩
  have hsplit := Multiset.card_eq_countP_add_countP (fun z : ℂ => z ∈ Complex.ofRealHom.range)
    (exampleF.map Complex.ofRealHom).roots
  rw [Multiset.countP_eq_card_filter, hreal, Multiset.card_map, hcard, hC] at hsplit
  have : (exampleF.map Complex.ofRealHom).roots.countP (fun z => z.im ≠ 0) =
      (exampleF.map Complex.ofRealHom).roots.countP (fun z => z ∉ Complex.ofRealHom.range) :=
    Multiset.countP_congr rfl fun z _ => by rw [hrange]
  rw [this]
  omega

end Example

/-! ### The discriminant -/

section Discriminant

open Finset

/-- **DLMF 1.11.9**: the discriminant `D = aₙ^{2n−2} ∏_{j<k} (zⱼ − zₖ)²` of a polynomial with
leading coefficient `aₙ` and zeros `z₁, …, zₙ`. -/
def discriminantOfZeros {K : Type*} [Field K] (a : K) {n : ℕ} (z : Fin n → K) : K :=
  a ^ (2 * n - 2) * ∏ j, ∏ k ∈ Ioi j, (z j - z k) ^ 2

/-- `∑ᵢ #{j > i} = n(n − 1)/2`. -/
theorem sum_card_Ioi (n : ℕ) : ∑ i : Fin n, #(Ioi i) = n * (n - 1) / 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n, sum_range_reflect (fun i => i) n,
    sum_range_id]

/-- `∏_{i ≠ j} (zᵢ − zⱼ) = (−1)^{n(n−1)/2} ∏_{i<j} (zᵢ − zⱼ)²`. -/
theorem prod_prod_erase_sub {K : Type*} [Field K] {n : ℕ} (z : Fin n → K) :
    ∏ i, ∏ j ∈ univ.erase i, (z i - z j) =
      (-1) ^ (n * (n - 1) / 2) * ∏ i, ∏ j ∈ Ioi i, (z i - z j) ^ 2 := by
  have hsplit : ∀ i : Fin n, univ.erase i = Ioi i ∪ Iio i := fun i => by
    ext j
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_Ioi, mem_Iio]
    exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim ne_of_gt ne_of_lt⟩
  have hdisj : ∀ i : Fin n, Disjoint (Ioi i) (Iio i) := fun i =>
    disjoint_left.mpr fun j h1 h2 => absurd (mem_Ioi.mp h1) (not_lt.mpr (mem_Iio.mp h2).le)
  have hswap : ∏ i, ∏ j ∈ Iio i, (z i - z j) = ∏ i, ∏ j ∈ Ioi i, (z j - z i) :=
    prod_comm' fun i j => by simp only [mem_univ, true_and, and_true, mem_Iio, mem_Ioi]
  simp_rw [hsplit, prod_union (hdisj _)]
  rw [prod_mul_distrib, hswap, ← prod_mul_distrib]
  have h1 : ∀ i : Fin n, (∏ j ∈ Ioi i, (z i - z j)) * ∏ j ∈ Ioi i, (z j - z i) =
      (-1) ^ #(Ioi i) * ∏ j ∈ Ioi i, (z i - z j) ^ 2 := fun i => by
    rw [← prod_mul_distrib, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by ring
  simp_rw [h1]
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, sum_card_Ioi]

/-- **DLMF 1.11.9**: for `f = aₙ ∏ⱼ (z − zⱼ)` with `aₙ ≠ 0`, Mathlib's discriminant (defined
through the Sylvester matrix of `f` and `f'`) is `aₙ^{2n−2} ∏_{j<k} (zⱼ − zₖ)²`.  Proof: by
Mathlib, `Res(f, f') = (−1)^{n(n−1)/2} aₙ D` and `Res(f, f') = aₙ^{n−1} ∏ᵢ f'(zᵢ)`, while
`f'(zᵢ) = aₙ ∏_{j≠i} (zᵢ − zⱼ)`. -/
theorem dlmf_1_11_9 {K : Type*} [Field K] {a : K} (ha : a ≠ 0) {n : ℕ} (z : Fin n → K) :
    (C a * ∏ j, (X - C (z j))).discr = discriminantOfZeros a z := by
  classical
  set g : K[X] := ∏ j, (X - C (z j)) with hgdef
  set S : Multiset K := univ.val.map z with hS
  have hg : g = (S.map fun r => X - C r).prod := by
    rw [hgdef, prod_eq_multiset_prod, hS, Multiset.map_map]
    rfl
  have hgm : g.Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (z j)
  have hgdeg : g.natDegree = n := by
    rw [hgdef, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (z j)]
    simp
  set f := C a * g with hfdef
  have hfdeg : f.natDegree = n := by rw [hfdef, natDegree_C_mul ha, hgdeg]
  have hflc : f.leadingCoeff = a := by
    rw [hfdef, leadingCoeff_mul, leadingCoeff_C, hgm.leadingCoeff, mul_one]
  have hfroots : f.roots = S := by
    rw [hfdef, roots_C_mul _ ha, hg, roots_multiset_prod_X_sub_C]
  have hsplit : f.Splits := splits_iff_card_roots.mpr (by rw [hfroots, hS]; simp [hfdeg])
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hg1 : g = 1 := by simp [hgdef]
    rw [hfdef, hg1, mul_one, discr_C, discriminantOfZeros]
    simp
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp (by rw [hfdeg]; exact hn)
  have H1 := resultant_deriv hdeg
  have H2 := resultant_eq_prod_eval f (derivative f) (f.natDegree - 1)
    (natDegree_derivative_le f) hsplit
  rw [H2, hflc, hfdeg, hfroots] at H1
  -- `f'(zᵢ) = a ∏_{j ≠ i} (zᵢ − zⱼ)`
  have hderiv : ∀ i, (derivative f).eval (z i) = a * ∏ j ∈ univ.erase i, (z i - z j) := by
    intro i
    have hmem : z i ∈ S := Multiset.mem_map_of_mem z (mem_univ_val i)
    rw [hfdef, derivative_C_mul, eval_mul, eval_C, hg,
      eval_multiset_prod_X_sub_C_derivative hmem]
    congr 1
    have hSi : S.erase (z i) = (univ.erase i).val.map z := by
      rw [hS, ← Multiset.cons_erase (mem_univ_val i), Multiset.map_cons,
        Multiset.erase_cons_head, erase_val]
    rw [hSi, Multiset.map_map]
    rfl
  have hprod : (S.map fun r => (derivative f).eval r).prod =
      a ^ n * ∏ i, ∏ j ∈ univ.erase i, (z i - z j) := by
    rw [hS, Multiset.map_map]
    rw [show ((univ.val.map ((fun r => (derivative f).eval r) ∘ z)).prod) =
        ∏ i, (derivative f).eval (z i) from rfl]
    simp_rw [hderiv]
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  rw [hprod, prod_prod_erase_sub] at H1
  rw [discriminantOfZeros]
  have hu : (-1 : K) ^ (n * (n - 1) / 2) * a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ha
  apply mul_left_cancel₀ hu
  rw [← H1]
  have hexp : a ^ (n - 1) * a ^ n = a * a ^ (2 * n - 2) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  calc a ^ (n - 1) * (a ^ n * ((-1) ^ (n * (n - 1) / 2) * ∏ i, ∏ j ∈ Ioi i, (z i - z j) ^ 2))
      = (a ^ (n - 1) * a ^ n) * ((-1) ^ (n * (n - 1) / 2) *
          ∏ i, ∏ j ∈ Ioi i, (z i - z j) ^ 2) := by ring
    _ = _ := by rw [hexp]; ring

/-- **DLMF 1.11.9** for complex polynomials: every `f ≠ 0` has its zeros `z₁, …, zₙ`, and its
discriminant is `aₙ^{2n−2} ∏_{j<k} (zⱼ − zₖ)²`. -/
theorem dlmf_1_11_9_complex {f : ℂ[X]} (hf : f ≠ 0) :
    ∃ z : Fin f.natDegree → ℂ, f.roots = univ.val.map z ∧
      f.discr = discriminantOfZeros f.leadingCoeff z := by
  have hcard : f.roots.toList.length = f.natDegree := by
    rw [Multiset.length_toList, dlmf_1_11_ii_card_roots]
  refine ⟨fun j => f.roots.toList.get (Fin.cast hcard.symm j), ?_, ?_⟩
  · conv_lhs => rw [← Multiset.coe_toList f.roots]
    rw [Fin.univ_val_map]
    congr 1
    refine List.ext_get (by simp [hcard]) fun i h1 h2 => ?_
    simp
  · have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
    rw [← dlmf_1_11_9 hlc]
    congr 1
    conv_lhs => rw [(IsAlgClosed.splits f).eq_prod_roots]
    congr 1
    conv_lhs => rw [← Multiset.coe_toList f.roots]
    rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    refine List.ext_get (by simp [hcard]) fun i h1 h2 => ?_
    simp

end Discriminant

end Azurite.DLMF
