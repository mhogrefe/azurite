/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fel'dman, Lemma 6: the coefficients of an exponential polynomial from its derivatives

N. I. Fel'dman, *Approximation of certain transcendental numbers. I*, Izv. Akad. Nauk SSSR
Ser. Mat. 15 (1951), 53–74, §1, Lemma 6, with the bounds (26)–(28) of its use.

For `f(z) = ∑_{l<q} P_l(z) e^{lz}` with polynomials `P_l` of degree `< q₀`, the coefficients are
determined by the `q q₀` numbers `f⁽ˢ⁾(2πix)`, `s < q`, `x < q₀`, and
(`l1_le_of_iteratedDeriv_le`)

  `|f⁽ˢ⁾(2πix)| ≤ ε` for all these `s`, `x`  ⟹  `‖P_l‖₁ ≤ 2^q (1 + q₀)^q q₀ 2^{q₀} ε`,

`‖·‖₁` (`l1`) being the sum of the absolute values of the coefficients.  Fel'dman writes the
inverse of the system explicitly with cofactors of two Vandermonde determinants (formula (2))
and bounds them ((27), (28)); here the same inversion is done in three steps on polynomials:

1. `f⁽ˢ⁾(z) = ∑_l e^{lz} ((D + l)^s P_l)(z)` (`iteratedDeriv_expPoly`), so `f⁽ˢ⁾(2πix)` is the
   value at `2πix` of the polynomial `A_s = ∑_l (D + l)^s P_l`;
2. a polynomial of degree `< m` with values `≤ ε` at `0, …, m − 1` has `‖·‖₁ ≤ m 2^m ε`
   (`l1_le_of_eval_le`), the Lagrange basis polynomials having `‖ℓ_x‖₁ ≤ C(m, x + 1)`
   (`l1_lagrange_basis_le`);
3. the moments `M_s = ∑_l l^s P_l` are `∑_t C(s, t) (−D)^t A_{s−t}` (`moment_eq`, the binomial
   theorem for the commuting operators `D + l` and `−D`), and `P_l = ∑_s [λ^s]ℓ_l · M_s`.
-/

namespace Azurite.Feldman

open Polynomial Finset

/-! ### The `ℓ¹` norm of a polynomial -/

/-- The sum of the absolute values of the coefficients. -/
noncomputable def l1 (P : ℂ[X]) : ℝ := ∑ i ∈ P.support, ‖P.coeff i‖

theorem l1_nonneg (P : ℂ[X]) : 0 ≤ l1 P := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem l1_eq_sum_range {P : ℂ[X]} {n : ℕ} (h : P.natDegree < n) :
    l1 P = ∑ i ∈ range n, ‖P.coeff i‖ := by
  unfold l1
  refine Finset.sum_subset (fun i hi => ?_) fun i _ hi => ?_
  · exact mem_range.mpr ((le_natDegree_of_mem_supp i hi).trans_lt h)
  · rw [notMem_support_iff.mp hi, norm_zero]

theorem norm_coeff_le_l1 (P : ℂ[X]) (i : ℕ) : ‖P.coeff i‖ ≤ l1 P := by
  by_cases hi : i ∈ P.support
  · exact Finset.single_le_sum (f := fun i => ‖P.coeff i‖) (fun _ _ => norm_nonneg _) hi
  · rw [notMem_support_iff.mp hi, norm_zero]
    exact l1_nonneg P

theorem l1_zero : l1 0 = 0 := by simp [l1]

theorem l1_add_le (P Q : ℂ[X]) : l1 (P + Q) ≤ l1 P + l1 Q := by
  set n := max P.natDegree Q.natDegree + 1 with hn
  have h1 : P.natDegree < n := by omega
  have h2 : Q.natDegree < n := by omega
  have h3 : (P + Q).natDegree < n := (natDegree_add_le P Q).trans_lt (by omega)
  rw [l1_eq_sum_range h1, l1_eq_sum_range h2, l1_eq_sum_range h3, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    rw [coeff_add]
    exact norm_add_le _ _

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add_le _ _).trans (by linarith)

theorem l1_C_mul (c : ℂ) (P : ℂ[X]) : l1 (C c * P) = ‖c‖ * l1 P := by
  have h1 : (C c * P).natDegree < P.natDegree + 1 :=
    (natDegree_C_mul_le c P).trans_lt (Nat.lt_succ_self _)
  rw [l1_eq_sum_range h1, l1_eq_sum_range (Nat.lt_succ_self _), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [coeff_C_mul, norm_mul]

theorem l1_smul (c : ℂ) (P : ℂ[X]) : l1 (c • P) = ‖c‖ * l1 P := by
  rw [smul_eq_C_mul, l1_C_mul]

theorem l1_X_pow_mul (n : ℕ) (P : ℂ[X]) : l1 (X ^ n * P) = l1 P := by
  have h1 : (X ^ n * P).natDegree < n + (P.natDegree + 1) := by
    refine natDegree_mul_le.trans_lt ?_
    rw [natDegree_X_pow]
    omega
  rw [l1_eq_sum_range h1, l1_eq_sum_range (Nat.lt_succ_self _), Finset.sum_range_add]
  have h0 : ∑ i ∈ range n, ‖(X ^ n * P).coeff i‖ = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [coeff_X_pow_mul', ite_eq_right (by have := mem_range.mp hi; omega), norm_zero]
  rw [h0, zero_add]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeff_X_pow_mul', ite_eq_left (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem l1_mul_le (P Q : ℂ[X]) : l1 (P * Q) ≤ l1 P * l1 Q := by
  conv_lhs => rw [P.as_sum_support, Finset.sum_mul]
  refine (l1_sum_le _ _).trans ?_
  unfold l1
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => le_of_eq ?_
  rw [← C_mul_X_pow_eq_monomial, mul_assoc]
  exact (l1_C_mul _ _).trans (by rw [l1_X_pow_mul]; rfl)

theorem l1_one : l1 (1 : ℂ[X]) = 1 := by
  rw [l1_eq_sum_range (n := 1) (by simp)]
  simp

theorem l1_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    l1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (l1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (l1_nonneg _))

theorem l1_X_sub_C_le (b : ℂ) : l1 (X - C b) ≤ 1 + ‖b‖ := by
  rw [l1_eq_sum_range (n := 2) (by rw [natDegree_X_sub_C]; omega)]
  simp [Finset.sum_range_succ, coeff_X, coeff_C]
  linarith

/-- `‖P′‖₁ ≤ n ‖P‖₁` for `deg P ≤ n`. -/
theorem l1_derivative_le {P : ℂ[X]} {n : ℕ} (h : P.natDegree ≤ n) :
    l1 (derivative P) ≤ n * l1 P := by
  have h1 : (derivative P).natDegree < n + 1 :=
    (natDegree_derivative_le P).trans_lt (by omega)
  rw [l1_eq_sum_range h1, l1_eq_sum_range (n := n + 1 + 1) (by omega), Finset.mul_sum,
    Finset.sum_range_succ' _ (n + 1)]
  have hstep : ∑ i ∈ range (n + 1), ‖(derivative P).coeff i‖
      ≤ ∑ i ∈ range (n + 1), (n : ℝ) * ‖P.coeff (i + 1)‖ := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [coeff_derivative, norm_mul, mul_comm]
    by_cases hi' : i + 1 ≤ n
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [show ((i : ℂ) + 1) = ((i + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast hi'
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have : 0 ≤ (n : ℝ) * ‖P.coeff 0‖ := by positivity
  linarith

/-- Rescaling the variable by `c`, `|c| ≥ 1`, does not decrease `‖·‖₁`. -/
theorem l1_le_l1_comp {P : ℂ[X]} {c : ℂ} (hc : 1 ≤ ‖c‖) : l1 P ≤ l1 (P.comp (C c * X)) := by
  have h1 : (P.comp (C c * X)).natDegree < P.natDegree + 1 := by
    refine natDegree_comp_le.trans_lt ?_
    have : (C c * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    calc P.natDegree * (C c * X).natDegree ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ this
      _ < P.natDegree + 1 := by omega
  rw [l1_eq_sum_range h1, l1_eq_sum_range (Nat.lt_succ_self _)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [comp_C_mul_X_coeff, norm_mul, norm_pow]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hc)

/-! ### Lagrange interpolation at `0, …, m − 1` -/

/-- `∏_{j < m, j ≠ x} (1 + j)/|x − j| = C(m, x + 1)`. -/
theorem prod_erase_weight (x : ℕ) : ∀ m, x + 1 ≤ m →
    ∏ j ∈ (range m).erase x, ((1 + j : ℝ) / |(x : ℝ) - j|) = (m.choose (x + 1) : ℝ) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have he : (range (x + 1)).erase x = range x := by
      rw [range_add_one, erase_insert (by simp)]
    rw [he, Nat.choose_self, Nat.cast_one, Finset.prod_div_distrib]
    have hnum : ∏ j ∈ range x, (1 + j : ℝ) = ∏ j ∈ range x, |(x : ℝ) - j| := by
      rw [← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [abs_of_nonneg (by
        have : (j : ℝ) ≤ x := by exact_mod_cast hj'.le
        linarith), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hnum]
    refine div_self (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
    have hj' := mem_range.mp hj
    have : (j : ℝ) < x := by exact_mod_cast hj'
    exact abs_ne_zero.mpr (by linarith)
  | succ m hm ih =>
    have he : (range (m + 1)).erase x = insert m ((range m).erase x) := by
      rw [range_add_one, erase_insert_of_ne (by omega)]
    rw [he, Finset.prod_insert (by simp), ih]
    have hxm : (x : ℝ) < m := by exact_mod_cast hm
    rw [abs_of_neg (by linarith)]
    have hid := Nat.choose_mul_succ_eq m (x + 1)
    have hid' : (m.choose (x + 1) : ℝ) * (m + 1) = ((m + 1).choose (x + 1) : ℝ) * (m - x) := by
      have := congrArg (fun k : ℕ => (k : ℝ)) hid
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
    linarith

/-- The Lagrange basis polynomials of the nodes `0, …, m − 1` have `‖ℓ_x‖₁ ≤ C(m, x + 1)`. -/
theorem l1_lagrange_basis_le {m x : ℕ} (hx : x < m) :
    l1 (Lagrange.basis (range m) (fun j : ℕ => (j : ℂ)) x) ≤ (m.choose (x + 1) : ℝ) := by
  rw [← prod_erase_weight x m hx]
  unfold Lagrange.basis
  refine (l1_prod_le _ _).trans (Finset.prod_le_prod₀ (fun _ _ => l1_nonneg _) fun j _ => ?_)
  unfold Lagrange.basisDivisor
  rw [l1_C_mul, norm_inv]
  dsimp only
  have hn : ‖(x : ℂ) - (j : ℂ)‖ = |(x : ℝ) - j| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hn, inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  refine (l1_X_sub_C_le _).trans (le_of_eq ?_)
  rw [Complex.norm_natCast]

/-- A polynomial of degree `< m` with `|A(x)| ≤ ε` at `x = 0, …, m − 1` has
`‖A‖₁ ≤ m 2^m ε`. -/
theorem l1_le_of_eval_le {A : ℂ[X]} {m : ℕ} (hdeg : A.natDegree < m) {ε : ℝ}
    (h : ∀ x < m, ‖A.eval (x : ℂ)‖ ≤ ε) : l1 A ≤ m * 2 ^ m * ε := by
  have hinj : Set.InjOn (fun j : ℕ => (j : ℂ)) (range m : Set ℕ) :=
    fun a _ b _ hab => Nat.cast_injective hab
  have hd : A.degree < (range m).card := by
    rw [card_range]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast hdeg)
  have hε : 0 ≤ ε := (norm_nonneg _).trans (h 0 (by omega))
  rw [Lagrange.eq_interpolate hinj hd, Lagrange.interpolate_apply]
  refine (l1_sum_le _ _).trans ?_
  calc ∑ i ∈ range m, l1 (C (A.eval (i : ℂ)) * Lagrange.basis (range m) (fun j : ℕ => (j : ℂ)) i)
      ≤ ∑ _i ∈ range m, ε * 2 ^ m := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [l1_C_mul]
        have hi' := mem_range.mp hi
        refine mul_le_mul (h i hi') ((l1_lagrange_basis_le hi').trans ?_) (l1_nonneg _) hε
        exact_mod_cast Nat.choose_le_two_pow m (i + 1)
    _ = m * 2 ^ m * ε := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]
        ring

/-! ### The operators `D + l` -/

/-- The operator `D + l` on polynomials: `e^{-lz} (d/dz) (e^{lz} P)`. -/
noncomputable def shiftD (l : ℂ) : Module.End ℂ ℂ[X] := derivative + l • (1 : Module.End ℂ ℂ[X])

theorem shiftD_apply (l : ℂ) (P : ℂ[X]) : shiftD l P = derivative P + l • P := rfl

theorem natDegree_shiftD_le (l : ℂ) {P : ℂ[X]} {d : ℕ} (h : P.natDegree ≤ d) :
    (shiftD l P).natDegree ≤ d := by
  rw [shiftD_apply]
  exact (natDegree_add_le _ _).trans (max_le ((natDegree_derivative_le P).trans (by omega))
    ((natDegree_smul_le l P).trans h))

theorem natDegree_shiftD_pow_le (l : ℂ) {P : ℂ[X]} {d : ℕ} (h : P.natDegree ≤ d) (s : ℕ) :
    ((shiftD l ^ s) P).natDegree ≤ d := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact natDegree_shiftD_le l ih

theorem l1_neg (P : ℂ[X]) : l1 (-P) = l1 P := by
  have : -P = (-1 : ℂ) • P := by simp
  rw [this, l1_smul]
  simp

/-- `‖(−D)^t A‖₁ ≤ d^t ‖A‖₁` for `deg A ≤ d`, and the degree does not grow. -/
theorem l1_negD_pow_le {A : ℂ[X]} {d : ℕ} (h : A.natDegree ≤ d) (t : ℕ) :
    (((-derivative : Module.End ℂ ℂ[X]) ^ t) A).natDegree ≤ d ∧
      l1 (((-derivative : Module.End ℂ ℂ[X]) ^ t) A) ≤ (d : ℝ) ^ t * l1 A := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
    refine ⟨?_, ?_⟩
    · rw [natDegree_neg]
      exact (natDegree_derivative_le _).trans (by omega)
    · rw [l1_neg, pow_succ]
      calc l1 (derivative (((-derivative : Module.End ℂ ℂ[X]) ^ t) A))
          ≤ d * l1 (((-derivative : Module.End ℂ ℂ[X]) ^ t) A) := l1_derivative_le ih.1
        _ ≤ d * ((d : ℝ) ^ t * l1 A) := mul_le_mul_of_nonneg_left ih.2 (Nat.cast_nonneg d)
        _ = (d : ℝ) ^ t * d * l1 A := by ring

/-- `l^s P = ∑_t C(s, t) (−D)^t (D + l)^(s−t) P`: the binomial theorem for the commuting
operators `−D` and `D + l`, whose sum is `l`. -/
theorem moment_eq (l : ℂ) (s : ℕ) (P : ℂ[X]) :
    l ^ s • P = ∑ t ∈ range (s + 1),
      s.choose t • (((-derivative : Module.End ℂ ℂ[X]) ^ t) ((shiftD l ^ (s - t)) P)) := by
  have hc : Commute (-derivative : Module.End ℂ ℂ[X]) (shiftD l) := by
    unfold shiftD
    have h1 : Commute (derivative : Module.End ℂ ℂ[X]) (l • (1 : Module.End ℂ ℂ[X])) :=
      (Commute.one_right _).smul_right l
    exact ((Commute.refl _).add_right h1).neg_left
  have h := hc.add_pow s
  have hsum : (-derivative : Module.End ℂ ℂ[X]) + shiftD l = l • (1 : Module.End ℂ ℂ[X]) := by
    unfold shiftD
    abel
  rw [hsum, smul_pow, one_pow] at h
  have h2 := LinearMap.congr_fun h P
  rw [LinearMap.smul_apply, Module.End.one_apply] at h2
  rw [h2, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Module.End.mul_apply, Module.End.natCast_apply, Module.End.mul_apply, map_nsmul,
    map_nsmul]

/-! ### The derivatives of an exponential polynomial -/

/-- `f⁽ˢ⁾(z) = ∑_l e^{lz} ((D + l)^s P_l)(z)` for `f(z) = ∑_l e^{lz} P_l(z)`. -/
theorem iteratedDeriv_expPoly (q : ℕ) (P : ℕ → ℂ[X]) (s : ℕ) :
    iteratedDeriv s (fun z : ℂ => ∑ l ∈ range q, Complex.exp (l * z) * (P l).eval z)
      = fun z => ∑ l ∈ range q,
          Complex.exp (l * z) * (((shiftD (l : ℂ)) ^ s) (P l)).eval z := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have hd : ∀ l ∈ range q, HasDerivAt
        (fun z : ℂ => Complex.exp (l * z) * (((shiftD (l : ℂ)) ^ s) (P l)).eval z)
        (Complex.exp (l * z) * (((shiftD (l : ℂ)) ^ (s + 1)) (P l)).eval z) z := by
      intro l _
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (l * z)) (Complex.exp (l * z) * (l * 1)) z :=
        ((hasDerivAt_id z).const_mul (l : ℂ)).cexp
      have h2 := h1.mul ((((shiftD (l : ℂ)) ^ s) (P l)).hasDerivAt z)
      refine h2.congr_deriv ?_
      rw [pow_succ', Module.End.mul_apply, shiftD_apply, eval_add, eval_smul, smul_eq_mul]
      ring
    exact (HasDerivAt.fun_sum hd).deriv

/-! ### Lemma 6 -/

/-- **Fel'dman, Lemma 6 with the bounds (26)–(28)**: if `f(z) = ∑_{l<q} P_l(z) e^{lz}` with
`deg P_l < q₀` has `|f⁽ˢ⁾(2πix)| ≤ ε` for `s < q`, `x < q₀`, then
`‖P_l‖₁ ≤ 2^q (1 + q₀)^q q₀ 2^{q₀} ε` for every `l < q`. -/
theorem l1_le_of_iteratedDeriv_le {q₀ q : ℕ} (P : ℕ → ℂ[X]) (hP : ∀ l, (P l).natDegree < q₀)
    {ε : ℝ}
    (hε : ∀ s < q, ∀ x < q₀, ‖iteratedDeriv s
      (fun z : ℂ => ∑ l ∈ range q, Complex.exp (l * z) * (P l).eval z)
      (2 * Real.pi * Complex.I * x)‖ ≤ ε) :
    ∀ l < q, l1 (P l) ≤ 2 ^ q * (1 + (q₀ : ℝ)) ^ q * (q₀ * 2 ^ q₀) * ε := by
  intro l hl
  have hq₀ : 0 < q₀ := Nat.pos_of_ne_zero fun h => by have := hP 0; omega
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε 0 (by omega) 0 hq₀)
  have hPd : ∀ l, (P l).natDegree ≤ q₀ - 1 := fun l => by have := hP l; omega
  -- the polynomials `A_s`
  set A : ℕ → ℂ[X] := fun s => ∑ l ∈ range q, ((shiftD (l : ℂ)) ^ s) (P l) with hA
  have hAd : ∀ s, (A s).natDegree ≤ q₀ - 1 := fun s =>
    natDegree_sum_le_of_forall_le _ _ fun l _ => natDegree_shiftD_pow_le _ (hPd l) s
  have hAval : ∀ s (x : ℕ), (A s).eval (2 * Real.pi * Complex.I * x)
      = iteratedDeriv s (fun z : ℂ => ∑ l ∈ range q, Complex.exp (l * z) * (P l).eval z)
        (2 * Real.pi * Complex.I * x) := by
    intro s x
    rw [iteratedDeriv_expPoly, hA, eval_finsetSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have : Complex.exp ((l : ℂ) * (2 * Real.pi * Complex.I * x)) = 1 := by
      have := Complex.exp_nat_mul_two_pi_mul_I (l * x)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [this, one_mul]
  -- `‖A_s‖₁ ≤ q₀ 2^{q₀} ε`
  set a : ℝ := q₀ * 2 ^ q₀ * ε with ha
  have ha0 : 0 ≤ a := by positivity
  have hAl1 : ∀ s < q, l1 (A s) ≤ a := by
    intro s hs
    have hc : (1 : ℝ) ≤ ‖(2 * Real.pi * Complex.I : ℂ)‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      nlinarith [Real.two_le_pi]
    refine (l1_le_l1_comp hc).trans ?_
    have hdeg : ((A s).comp (C (2 * Real.pi * Complex.I : ℂ) * X)).natDegree < q₀ := by
      refine natDegree_comp_le.trans_lt ?_
      have h1 : (C (2 * Real.pi * Complex.I : ℂ) * X).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans (by simp)
      have h2 := hAd s
      calc (A s).natDegree * (C (2 * Real.pi * Complex.I : ℂ) * X).natDegree
          ≤ (A s).natDegree * 1 := Nat.mul_le_mul_left _ h1
        _ < q₀ := by omega
    refine l1_le_of_eval_le hdeg fun x hx => ?_
    rw [eval_comp, eval_mul, eval_C, eval_X, hAval]
    exact hε s hs x hx
  -- the moments
  set Mo : ℕ → ℂ[X] := fun s => ∑ l ∈ range q, (l : ℂ) ^ s • P l with hMo
  set b : ℝ := (1 + (q₀ : ℝ)) ^ q * a with hb
  have hMl1 : ∀ s < q, l1 (Mo s) ≤ b := by
    intro s hs
    have hM : Mo s = ∑ t ∈ range (s + 1),
        s.choose t • (((-derivative : Module.End ℂ ℂ[X]) ^ t) (A (s - t))) := by
      rw [hMo, hA]
      simp only [moment_eq, map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.smul_sum]
    rw [hM]
    refine (l1_sum_le _ _).trans ?_
    have hterm : ∀ t ∈ range (s + 1),
        l1 (s.choose t • (((-derivative : Module.End ℂ ℂ[X]) ^ t) (A (s - t))))
          ≤ (q₀ : ℝ) ^ t * 1 ^ (s - t) * s.choose t * a := by
      intro t ht
      have ht' := mem_range.mp ht
      rw [← Nat.cast_smul_eq_nsmul ℂ, l1_smul, Complex.norm_natCast, one_pow, mul_one]
      have h1 := (l1_negD_pow_le (hAd (s - t)) t).2
      have h2 := hAl1 (s - t) (by omega)
      have h3 : ((q₀ - 1 : ℕ) : ℝ) ^ t ≤ (q₀ : ℝ) ^ t :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le q₀ 1) t
      calc (s.choose t : ℝ) * l1 (((-derivative : Module.End ℂ ℂ[X]) ^ t) (A (s - t)))
          ≤ (s.choose t : ℝ) * (((q₀ - 1 : ℕ) : ℝ) ^ t * l1 (A (s - t))) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ ≤ (s.choose t : ℝ) * ((q₀ : ℝ) ^ t * a) := by
            gcongr
            exact l1_nonneg _
        _ = (q₀ : ℝ) ^ t * s.choose t * a := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← add_pow, hb]
    refine mul_le_mul_of_nonneg_right ?_ ha0
    rw [add_comm]
    exact pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) q₀]) hs.le
  -- `P_l` from the moments
  have hinj : Set.InjOn (fun j : ℕ => (j : ℂ)) (range q : Set ℕ) :=
    fun a _ b _ hab => Nat.cast_injective hab
  set ℓ : ℂ[X] := Lagrange.basis (range q) (fun j : ℕ => (j : ℂ)) l with hℓ
  have hℓdeg : ℓ.natDegree < q := by
    rw [hℓ, Lagrange.natDegree_basis hinj (mem_range.mpr hl), card_range]
    omega
  have hPl : P l = ∑ s ∈ range q, ℓ.coeff s • Mo s := by
    rw [hMo]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hev : ∀ j : ℕ, ∑ s ∈ range q, ℓ.coeff s * (j : ℂ) ^ s = ℓ.eval (j : ℂ) := fun j =>
      (eval_eq_sum_range' hℓdeg _).symm
    simp only [hev]
    rw [Finset.sum_eq_single l]
    · rw [hℓ, Lagrange.eval_basis_self hinj (mem_range.mpr hl), one_smul]
    · intro j hj hjl
      rw [hℓ, Lagrange.eval_basis_of_ne (Ne.symm hjl) hj, zero_smul]
    · intro h
      exact absurd (mem_range.mpr hl) h
  have hb0 : 0 ≤ b := by positivity
  rw [hPl]
  refine (l1_sum_le _ _).trans ?_
  calc ∑ s ∈ range q, l1 (ℓ.coeff s • Mo s) ≤ ∑ s ∈ range q, ‖ℓ.coeff s‖ * b := by
        refine Finset.sum_le_sum fun s hs => ?_
        rw [l1_smul]
        exact mul_le_mul_of_nonneg_left (hMl1 s (mem_range.mp hs)) (norm_nonneg _)
    _ = l1 ℓ * b := by rw [← Finset.sum_mul, l1_eq_sum_range hℓdeg]
    _ ≤ 2 ^ q * b := by
        refine mul_le_mul_of_nonneg_right ((l1_lagrange_basis_le hl).trans ?_) hb0
        exact_mod_cast Nat.choose_le_two_pow q (l + 1)
    _ = 2 ^ q * (1 + (q₀ : ℝ)) ^ q * (q₀ * 2 ^ q₀) * ε := by rw [hb, ha]; ring

end Azurite.Feldman
