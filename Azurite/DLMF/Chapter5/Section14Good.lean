/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Selberg

/-!
# Good's identity (Dyson's constant-term identity) as a torus integral

For `a : Fin n → ℕ`,
`∫_{[−π,π]ⁿ} ∏_{i ≠ j} (1 − e^{i(θᵢ−θⱼ)})^{aᵢ} dθ = (2π)ⁿ (a₁ + ⋯ + aₙ)!/(a₁!⋯aₙ!)`
(Dyson's conjecture, proved by Gunson, Wilson and Good; we follow I. J. Good, *Short proof of a
conjecture by Dyson*, J. Math. Phys. 11 (1970)). Good's argument works directly with the
integrals: if some `aᵢ = 0`, the variable `θᵢ` only enters through a polynomial in `e^{−iθᵢ}` with
constant term `1`, so it integrates out to `2π`; if all `aᵢ ≥ 1`, Lagrange interpolation of the
constant `1` at the nodes `e^{iθ₁}, …, e^{iθₙ}` gives the recursion
`F(a) = Σₖ F(a − eₖ)`, which the multinomial coefficients also satisfy.
-/

open Finset MeasureTheory Filter Topology

namespace Azurite.DLMF

/-- The box `[−π, π]ⁿ`. -/
def torusBox (n : ℕ) : Set (Fin n → ℝ) := Set.Icc (fun _ => -Real.pi) (fun _ => Real.pi)

/-- `∏_{j ≠ i} (1 − e^{i(θᵢ−θⱼ)})`. -/
noncomputable def goodQ {n : ℕ} (θ : Fin n → ℝ) (i : Fin n) : ℂ :=
  ∏ j, if j = i then 1 else 1 - Complex.exp (((θ i - θ j : ℝ) : ℂ) * Complex.I)

/-- Good's integrand `∏ᵢ ∏_{j ≠ i} (1 − e^{i(θᵢ−θⱼ)})^{aᵢ}`. -/
noncomputable def goodF {n : ℕ} (a : Fin n → ℕ) (θ : Fin n → ℝ) : ℂ := ∏ i, goodQ θ i ^ a i

/-- The multinomial coefficient `(Σ aᵢ)!/∏ aᵢ!`. -/
noncomputable def multinomialC {n : ℕ} (a : Fin n → ℕ) : ℂ :=
  ((∑ i, a i).factorial : ℂ) / ∏ i, ((a i).factorial : ℂ)

theorem continuous_goodQ {n : ℕ} (i : Fin n) : Continuous fun θ : Fin n → ℝ => goodQ θ i := by
  unfold goodQ
  refine continuous_finsetProd _ fun j _ => ?_
  split_ifs
  · exact continuous_const
  · fun_prop

theorem continuous_goodF {n : ℕ} (a : Fin n → ℕ) : Continuous (goodF a) := by
  unfold goodF
  exact continuous_finsetProd _ fun i _ => (continuous_goodQ i).pow _

theorem isCompact_torusBox (n : ℕ) : IsCompact (torusBox n) := isCompact_Icc

theorem integrableOn_torusBox {n : ℕ} {g : (Fin n → ℝ) → ℂ} (hg : Continuous g) :
    IntegrableOn g (torusBox n) := hg.continuousOn.integrableOn_compact (isCompact_torusBox n)

/-! ### Splitting off one coordinate -/

theorem integral_torusBox_succ {m : ℕ} (i : Fin (m + 1)) {g : (Fin (m + 1) → ℝ) → ℂ}
    (hg : Continuous g) :
    ∫ θ in torusBox (m + 1), g θ =
      ∫ θ' in torusBox m, ∫ t in Set.Icc (-Real.pi) Real.pi, g (Fin.insertNth i t θ') := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _
  have he : ∀ p : ℝ × (Fin m → ℝ), e.symm p = Fin.insertNth i p.1 p.2 := fun p => rfl
  have hpre : e.symm ⁻¹' torusBox (m + 1) = Set.Icc (-Real.pi) Real.pi ×ˢ torusBox m := by
    ext ⟨t, s⟩
    simp only [Set.mem_preimage, he, torusBox, Set.mem_Icc, Set.mem_prod, Pi.le_def,
      Fin.forall_iff_succAbove i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    tauto
  have hint := integrableOn_torusBox (n := m + 1) hg
  have hint' := (hmp.integrableOn_comp_preimage e.symm.measurableEmbedding).mpr hint
  rw [hpre, IntegrableOn, ← Measure.prod_restrict] at hint'
  have hint'' : Integrable (fun p => g (e.symm p))
      ((volume.restrict (Set.Icc (-Real.pi) Real.pi)).prod (volume.restrict (torusBox m))) :=
    hint'
  rw [← hmp.setIntegral_preimage_emb e.symm.measurableEmbedding, hpre, ← Measure.prod_restrict,
    integral_prod_symm _ hint'']
  simp only [he]

/-! ### Integrating a polynomial in `e^{−it}` -/

theorem integral_exp_neg_pow (k : ℕ) :
    ∫ t in (-Real.pi)..Real.pi, Complex.exp (-(t : ℂ) * Complex.I) ^ k =
      if k = 0 then 2 * Real.pi else 0 := by
  split_ifs with hk
  · subst hk; simp; ring
  · have hc : -(k : ℂ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero, hk]
    have e : ∀ t : ℝ, Complex.exp (-(t : ℂ) * Complex.I) ^ k =
        Complex.exp (-(k : ℂ) * Complex.I * t) := fun t => by
      rw [← Complex.exp_nat_mul]; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (-(k : ℂ) * Complex.I * (-Real.pi : ℝ)) =
        Complex.exp (-(k : ℂ) * Complex.I * (Real.pi : ℝ)) *
          Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h2, Complex.exp_nat_mul_two_pi_mul_I, mul_one, sub_self, zero_div]
    simp

theorem integral_poly_exp_neg (P : Polynomial ℂ) :
    ∫ t in (-Real.pi)..Real.pi, P.eval (Complex.exp (-(t : ℂ) * Complex.I)) =
      2 * Real.pi * P.coeff 0 := by
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [intervalIntegral.integral_finsetSum (fun k _ => by
    exact (Continuous.intervalIntegrable (by fun_prop) _ _))]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_neg_pow]
  rw [Finset.sum_eq_single 0 (fun k _ hk => by simp [hk]) (fun h => by simp at h)]
  simp only [↓reduceIte]
  push_cast
  ring

/-! ### A variable with exponent `0` integrates out -/

theorem goodQ_succAbove {m : ℕ} (θ : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (j : Fin m) :
    goodQ θ (i.succAbove j) =
      (1 - Complex.exp (((θ (i.succAbove j) - θ i : ℝ) : ℂ) * Complex.I)) *
        goodQ (θ ∘ i.succAbove) j := by
  unfold goodQ
  rw [Fin.prod_univ_succAbove _ i,
    ite_eq_right_of_eq_false _ _ (eq_false (Fin.succAbove_ne i j).symm)]
  congr 1
  refine prod_congr rfl fun l _ => ?_
  simp only [Fin.succAbove_right_inj, Function.comp_apply]

theorem goodF_of_zero {m : ℕ} (a : Fin (m + 1) → ℕ) {i : Fin (m + 1)} (ha : a i = 0)
    (θ : Fin (m + 1) → ℝ) :
    goodF a θ = goodF (a ∘ i.succAbove) (θ ∘ i.succAbove) *
      ∏ j : Fin m, (1 - Complex.exp (((θ (i.succAbove j) - θ i : ℝ) : ℂ) * Complex.I)) ^
        a (i.succAbove j) := by
  unfold goodF
  rw [Fin.prod_univ_succAbove _ i, ha, pow_zero, one_mul]
  simp_rw [goodQ_succAbove, mul_pow, prod_mul_distrib, Function.comp_apply]
  ring

theorem integral_goodF_slice {m : ℕ} (a : Fin (m + 1) → ℕ) {i : Fin (m + 1)} (ha : a i = 0)
    (θ' : Fin m → ℝ) :
    ∫ t in Set.Icc (-Real.pi) Real.pi, goodF a (Fin.insertNth i t θ') =
      2 * Real.pi * goodF (a ∘ i.succAbove) θ' := by
  set P : Polynomial ℂ := ∏ j : Fin m,
    (1 - Polynomial.C (Complex.exp ((θ' j : ℂ) * Complex.I)) * Polynomial.X) ^ a (i.succAbove j)
  have hP : ∀ t : ℝ, ∏ j : Fin m,
      (1 - Complex.exp (((θ' j - t : ℝ) : ℂ) * Complex.I)) ^ a (i.succAbove j) =
      P.eval (Complex.exp (-(t : ℂ) * Complex.I)) := fun t => by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    refine prod_congr rfl fun j _ => ?_
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  have hP0 : P.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [P, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_mul]
  simp_rw [goodF_of_zero a ha]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp_rw [hP]
  have hcomp : ∀ t : ℝ, (Fin.insertNth i t θ') ∘ i.succAbove = θ' := fun t => by
    ext j; simp
  simp_rw [hcomp]
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_poly_exp_neg, hP0]
  ring

theorem integral_goodF_of_zero {m : ℕ} (a : Fin (m + 1) → ℕ) {i : Fin (m + 1)} (ha : a i = 0) :
    ∫ θ in torusBox (m + 1), goodF a θ =
      2 * Real.pi * ∫ θ' in torusBox m, goodF (a ∘ i.succAbove) θ' := by
  rw [integral_torusBox_succ i (continuous_goodF a)]
  simp_rw [integral_goodF_slice a ha]
  rw [integral_const_mul]

theorem multinomialC_of_zero {m : ℕ} (a : Fin (m + 1) → ℕ) {i : Fin (m + 1)} (ha : a i = 0) :
    multinomialC a = multinomialC (a ∘ i.succAbove) := by
  unfold multinomialC
  rw [Fin.sum_univ_succAbove _ i, Fin.prod_univ_succAbove _ i, ha]
  simp

/-! ### Lagrange interpolation -/

theorem one_sub_exp_eq (x y : ℝ) :
    1 - Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) =
      (Complex.exp ((y : ℂ) * Complex.I) - Complex.exp ((x : ℂ) * Complex.I)) /
        Complex.exp ((y : ℂ) * Complex.I) := by
  rw [sub_div, div_self (Complex.exp_ne_zero _), ← Complex.exp_sub]
  push_cast
  ring_nf

/-- `Σₖ ∏_{j ≠ k} xⱼ/(xⱼ − xₖ) = 1` (Lagrange interpolation of `1`, evaluated at `0`). -/
theorem sum_inv_goodQ {n : ℕ} (hn : 0 < n) {θ : Fin n → ℝ}
    (hθ : ∀ j k, j ≠ k →
      Complex.exp ((θ j : ℂ) * Complex.I) ≠ Complex.exp ((θ k : ℂ) * Complex.I)) :
    ∑ k, (goodQ θ k)⁻¹ = 1 := by
  set x : Fin n → ℂ := fun j => Complex.exp ((θ j : ℂ) * Complex.I)
  have hinj : Set.InjOn x (univ : Finset (Fin n)) := fun j _ k _ hjk => by
    by_contra h; exact hθ j k h hjk
  have hL := congrArg (Polynomial.eval 0) (Lagrange.sum_basis hinj (univ_nonempty_iff.mpr
    ⟨⟨0, hn⟩⟩))
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at hL
  rw [← hL]
  refine sum_congr rfl fun k _ => ?_
  rw [goodQ, ← prod_inv_distrib, Lagrange.basis, Polynomial.eval_prod,
    ← mul_prod_erase univ _ (mem_univ k), ite_eq_left_of_eq_true _ _ (eq_self k), inv_one, one_mul]
  refine prod_congr rfl fun j hj => ?_
  have hjk : j ≠ k := ne_of_mem_erase hj
  rw [ite_eq_right_of_eq_false _ _ (eq_false hjk), Lagrange.basisDivisor, Polynomial.eval_mul,
    Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, one_sub_exp_eq, inv_div]
  simp only [x]
  rw [show Complex.exp ((θ k : ℂ) * Complex.I) - Complex.exp ((θ j : ℂ) * Complex.I) =
    -(Complex.exp ((θ j : ℂ) * Complex.I) - Complex.exp ((θ k : ℂ) * Complex.I)) by ring,
    inv_neg, div_eq_mul_inv]
  ring

theorem goodF_eq_mul {n : ℕ} (a : Fin n → ℕ) {k : Fin n} (hk : 1 ≤ a k) (θ : Fin n → ℝ) :
    goodF a θ = goodQ θ k * goodF (Function.update a k (a k - 1)) θ := by
  unfold goodF
  rw [← mul_prod_erase univ _ (mem_univ k), ← mul_prod_erase univ _ (mem_univ k),
    Function.update_self]
  have : ∏ i ∈ univ.erase k, goodQ θ i ^ Function.update a k (a k - 1) i =
      ∏ i ∈ univ.erase k, goodQ θ i ^ a i :=
    prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [this, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]

theorem goodF_recursion {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) (ha : ∀ k, 1 ≤ a k)
    {θ : Fin n → ℝ}
    (hθ : ∀ j k, j ≠ k →
      Complex.exp ((θ j : ℂ) * Complex.I) ≠ Complex.exp ((θ k : ℂ) * Complex.I)) :
    goodF a θ = ∑ k, goodF (Function.update a k (a k - 1)) θ := by
  have hQ : ∀ k, goodQ θ k ≠ 0 := fun k => by
    unfold goodQ
    refine prod_ne_zero_iff.mpr fun j _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · rw [one_sub_exp_eq]
      exact div_ne_zero (sub_ne_zero.mpr (hθ j k h)) (Complex.exp_ne_zero _)
  calc goodF a θ = goodF a θ * ∑ k, (goodQ θ k)⁻¹ := by rw [sum_inv_goodQ hn hθ, mul_one]
    _ = ∑ k, goodF (Function.update a k (a k - 1)) θ := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [goodF_eq_mul a (ha k) θ]
      field_simp [hQ k]

theorem multinomialC_recursion {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ) (ha : ∀ k, 1 ≤ a k) :
    multinomialC a = ∑ k, multinomialC (Function.update a k (a k - 1)) := by
  set S := ∑ i, a i
  have hS : 1 ≤ S := (ha ⟨0, hn⟩).trans (single_le_sum (fun i _ => Nat.zero_le _) (mem_univ _))
  have hsum : ∀ k, ∑ i, Function.update a k (a k - 1) i = S - 1 := fun k => by
    rw [← add_sum_erase univ _ (mem_univ k), Function.update_self,
      sum_congr rfl fun i hi => Function.update_of_ne (ne_of_mem_erase hi) _ _,
      show S = a k + ∑ i ∈ univ.erase k, a i from (add_sum_erase univ a (mem_univ k)).symm]
    have := ha k; omega
  have hprod : ∀ k, (∏ i, ((Function.update a k (a k - 1) i).factorial : ℂ)) * a k =
      ∏ i, ((a i).factorial : ℂ) := fun k => by
    rw [← mul_prod_erase univ _ (mem_univ k), ← mul_prod_erase univ (fun i => ((a i).factorial : ℂ))
      (mem_univ k), Function.update_self,
      prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]]
    have h1 : ((a k).factorial : ℂ) = a k * ((a k - 1).factorial : ℂ) := by
      obtain ⟨c, hc⟩ : ∃ c, a k = c + 1 := ⟨a k - 1, by have := ha k; omega⟩
      rw [hc, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast; ring
    rw [h1]; ring
  have hfact : (S.factorial : ℂ) = S * ((S - 1).factorial : ℂ) := by
    obtain ⟨c, hc⟩ : ∃ c, S = c + 1 := ⟨S - 1, by omega⟩
    rw [hc, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast; ring
  have hS0 : (S : ℂ) ≠ 0 := by exact_mod_cast (by omega : S ≠ 0)
  have hP0 : ∏ i, ((a i).factorial : ℂ) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have hterm : ∀ k, multinomialC (Function.update a k (a k - 1)) = multinomialC a * a k / S :=
    fun k => by
      have hPk : ∏ i, ((Function.update a k (a k - 1) i).factorial : ℂ) ≠ 0 :=
        prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
      have hak : (a k : ℂ) ≠ 0 := by exact_mod_cast (by have := ha k; omega : a k ≠ 0)
      unfold multinomialC
      rw [hsum k, ← hprod k, hfact]
      field_simp
  simp_rw [hterm, ← sum_div, ← mul_sum]
  rw [show (∑ k, (a k : ℂ)) = S by push_cast [S]; rfl, mul_div_assoc, div_self hS0, mul_one]

/-! ### Distinct nodes almost everywhere -/

theorem ae_torus_distinct {n : ℕ} :
    ∀ᵐ θ ∂(volume.restrict (torusBox n)), ∀ j k : Fin n, j ≠ k →
      Complex.exp ((θ j : ℂ) * Complex.I) ≠ Complex.exp ((θ k : ℂ) * Complex.I) := by
  have h1 : ∀ᵐ θ ∂(volume : Measure (Fin n → ℝ)), ∀ j k : Fin n, j ≠ k → θ j ≠ θ k := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k
    by_cases hjk : j = k
    · exact ae_of_all _ fun _ h => absurd hjk h
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_coord_eq_null hjk)] with θ hθ _
      exact hθ
  have h2 : ∀ᵐ θ ∂(volume : Measure (Fin n → ℝ)), ∀ j, θ j ≠ -Real.pi ∧ θ j ≠ Real.pi := by
    rw [ae_all_iff]; intro j
    have e1 : volume {θ : Fin n → ℝ | θ j = -Real.pi} = 0 := by
      rw [volume_pi]; exact Measure.pi_hyperplane _ j _
    have e2 : volume {θ : Fin n → ℝ | θ j = Real.pi} = 0 := by
      rw [volume_pi]; exact Measure.pi_hyperplane _ j _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp e1, measure_eq_zero_iff_ae_notMem.mp e2]
      with θ h1 h2 using ⟨h1, h2⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1, ae_restrict_of_ae h2]
    with θ hθ hd hb j k hjk heq
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  have hre : θ j - θ k = 2 * Real.pi * m := by
    have := congrArg Complex.im hm
    simp at this
    linarith
  have hj := hθ.1 j; have hj' := hθ.2 j; have hk := hθ.1 k; have hk' := hθ.2 k
  have hj1 := lt_of_le_of_ne hj (hb j).1.symm
  have hj2 := lt_of_le_of_ne hj' (hb j).2
  have hk1 := lt_of_le_of_ne hk (hb k).1.symm
  have hk2 := lt_of_le_of_ne hk' (hb k).2
  have hπ := Real.pi_pos
  have hm0 : m = 0 := by
    have h1 : (m : ℝ) < 1 := by nlinarith
    have h2 : -1 < (m : ℝ) := by nlinarith
    have h1' : m < 1 := by exact_mod_cast h1
    have h2' : -1 < m := by exact_mod_cast h2
    omega
  rw [hm0] at hre
  exact hd j k hjk (sub_eq_zero.mp (by simpa using hre))

/-! ### Good's identity -/

theorem integral_const_torusBox_zero (c : ℂ) : ∫ _θ in torusBox 0, c = c := by
  rw [setIntegral_const, torusBox, Measure.real, Real.volume_Icc_pi]
  simp

/-- **Good's identity**: `∫_{[−π,π]ⁿ} ∏_{i≠j}(1 − e^{i(θᵢ−θⱼ)})^{aᵢ} dθ = (2π)ⁿ (Σaᵢ)!/∏aᵢ!`. -/
theorem good_identity : ∀ (n : ℕ) (a : Fin n → ℕ),
    ∫ θ in torusBox n, goodF a θ = (2 * Real.pi : ℂ) ^ n * multinomialC a := by
  suffices h : ∀ N, ∀ (n : ℕ) (a : Fin n → ℕ), n + ∑ i, a i = N →
      ∫ θ in torusBox n, goodF a θ = (2 * Real.pi : ℂ) ^ n * multinomialC a from
    fun n a => h _ n a rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro n a hN
  rcases n with _ | m
  · have hF : ∀ θ : Fin 0 → ℝ, goodF a θ = 1 := fun θ => by simp [goodF]
    simp_rw [hF]
    rw [integral_const_torusBox_zero]
    simp [multinomialC]
  · by_cases h0 : ∃ i, a i = 0
    · obtain ⟨i, hi⟩ := h0
      have hsum : ∑ j, (a ∘ i.succAbove) j = ∑ j, a j := by
        rw [Fin.sum_univ_succAbove a i, hi, zero_add]; rfl
      rw [integral_goodF_of_zero a hi, ih (m + ∑ j, a j) (by omega) m _ (by rw [hsum]),
        multinomialC_of_zero a hi, pow_succ]
      ring
    · push Not at h0
      have ha : ∀ k, 1 ≤ a k := fun k => Nat.one_le_iff_ne_zero.mpr (h0 k)
      have hrec : ∀ᵐ θ ∂(volume.restrict (torusBox (m + 1))),
          goodF a θ = ∑ k, goodF (Function.update a k (a k - 1)) θ := by
        filter_upwards [ae_torus_distinct] with θ hθ
        exact goodF_recursion (Nat.succ_pos m) a ha hθ
      rw [integral_congr_ae hrec, integral_finsetSum _ (fun k _ =>
        integrableOn_torusBox (continuous_goodF _)), multinomialC_recursion (Nat.succ_pos m) a ha,
        mul_sum]
      refine sum_congr rfl fun k _ => ?_
      have hsk : ∑ i, Function.update a k (a k - 1) i + 1 = ∑ i, a i := by
        rw [← add_sum_erase univ _ (mem_univ k), Function.update_self,
          sum_congr rfl fun i hi => Function.update_of_ne (ne_of_mem_erase hi) _ _,
          ← add_sum_erase univ a (mem_univ k)]
        have := ha k; omega
      exact ih _ (by omega) _ _ rfl

/-! ### Dyson's integrand at integer exponents -/

/-- Dyson's integrand `∏_{j<k} |e^{iθⱼ} − e^{iθₖ}|^{2b}`. -/
noncomputable def dysonF {n : ℕ} (b : ℂ) (θ : Fin n → ℝ) : ℂ :=
  ∏ j, ∏ k ∈ Ioi j, ((‖Complex.exp ((θ j : ℂ) * Complex.I) -
    Complex.exp ((θ k : ℂ) * Complex.I)‖ : ℝ) : ℂ) ^ (2 * b)

theorem prod_ite_pairs {M : Type*} [CommMonoid M] {n : ℕ} (h : Fin n → Fin n → M) :
    ∏ i, ∏ j, (if j = i then 1 else h i j) = ∏ i, ∏ j ∈ Ioi i, (h i j * h j i) := by
  have e1 : ∀ i, ∏ j, (if j = i then 1 else h i j) =
      (∏ j, if j < i then h i j else 1) * ∏ j ∈ Ioi i, h i j := fun i => by
    rw [prod_Ioi_eq_prod_ite, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rcases lt_trichotomy j i with hji | rfl | hij
    · simp [hji, hji.ne, not_lt.mpr hji.le]
    · simp
    · simp [hij, hij.ne', not_lt.mpr hij.le]
  simp_rw [e1, prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_comm]
  exact prod_congr rfl fun j _ => (prod_Ioi_eq_prod_ite j (fun k => h k j)).symm

theorem one_sub_exp_mul_one_sub_exp (x y : ℝ) :
    (1 - Complex.exp (((x - y : ℝ) : ℂ) * Complex.I)) *
        (1 - Complex.exp (((y - x : ℝ) : ℂ) * Complex.I)) =
      ((‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) := by
  set u := Complex.exp (((x - y : ℝ) : ℂ) * Complex.I)
  have hconj : Complex.exp (((y - x : ℝ) : ℂ) * Complex.I) = (starRingEnd ℂ) u := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hnorm : ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ =
      ‖1 - u‖ := by
    have : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
        -(Complex.exp ((y : ℂ) * Complex.I) * (1 - u)) := by
      simp only [u, mul_sub, mul_one, ← Complex.exp_add]
      push_cast; ring_nf
    rw [this, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hc : 1 - (starRingEnd ℂ) u = (starRingEnd ℂ) (1 - u) := by simp
  rw [hconj, hnorm, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem dysonF_nat {n : ℕ} (N : ℕ) (θ : Fin n → ℝ) :
    dysonF (N : ℂ) θ = goodF (fun _ => N) θ := by
  unfold dysonF goodF goodQ
  rw [prod_pow, prod_ite_pairs]
  simp_rw [one_sub_exp_mul_one_sub_exp, ← prod_pow]
  refine prod_congr rfl fun j _ => prod_congr rfl fun k _ => ?_
  rw [show 2 * (N : ℂ) = ((2 * N : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast, pow_mul]
  push_cast; ring

theorem multinomialC_const (n N : ℕ) :
    multinomialC (fun _ : Fin n => N) = ((n * N).factorial : ℂ) / (N.factorial : ℂ) ^ n := by
  simp [multinomialC]

/-- Dyson's integral at nonnegative integers:
`∫ ∏_{j<k}|e^{iθⱼ} − e^{iθₖ}|^{2N} = (2π)ⁿ(nN)!/(N!)ⁿ`. -/
theorem integral_dysonF_nat (n N : ℕ) :
    ∫ θ in torusBox n, dysonF (N : ℂ) θ =
      (2 * Real.pi : ℂ) ^ n * (((n * N).factorial : ℂ) / (N.factorial : ℂ) ^ n) := by
  simp_rw [dysonF_nat]
  rw [good_identity, multinomialC_const]

end Azurite.DLMF
