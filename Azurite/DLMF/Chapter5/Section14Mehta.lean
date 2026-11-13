/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Laguerre

/-!
# DLMF 5.14.6: Mehta's integral

We take `a = b = L + 1 → ∞` in 5.14.4 (`dlmf_5_14_4_full`) after the substitution
`t = ½ + s/(2h)`, `h = √(2L)`, under which `t(1 − t) = (1 − s²/(2L))/4`:
`∫_{[−h,h]ⁿ} ∏ (1 − sₖ²/(2L))^L |Δ(s)|^{2c} ds = 4^{nL} (2h)^{n+n(n−1)c} S_n(L + 1, L + 1, c)`.
The integrands converge pointwise to `∏ e^{−sₖ²/2} |Δ(s)|^{2c}` and are bounded by it
(`(1 − x/L)^L ≤ e^{−x}`). As for 5.14.5, Fatou's lemma gives convergence on DLMF's full range
`ℜc > −1/n`, dominated convergence the value; the Gamma factors are handled by Legendre's
duplication formula and 5.11.12.
-/

open Finset MeasureTheory Filter Topology

namespace Azurite.DLMF

variable {n : ℕ}

/-- Mehta's integrand `∏ e^{−tₖ²/2} |Δ(t)|^{2c}`. -/
noncomputable def mehtaF (c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ k, ((Real.exp (-(t k ^ 2) / 2) : ℝ) : ℂ)) * ((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c)

/-- The approximants `∏ (1 − tₖ²/(2L))^L |Δ(t)|^{2c}`. -/
noncomputable def mehtaApprox (L : ℕ) (c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ k, ((1 - t k ^ 2 / (2 * L) : ℝ) : ℂ) ^ L) * ((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c)

/-- The half-width `h = √(2L)` of the box. -/
noncomputable def mehtaH (L : ℕ) : ℝ := Real.sqrt (2 * L)

theorem mehtaH_pos {L : ℕ} (hL : 0 < L) : 0 < mehtaH L :=
  Real.sqrt_pos.mpr (by positivity)

theorem mehtaH_sq (L : ℕ) : mehtaH L ^ 2 = 2 * L :=
  Real.sq_sqrt (by positivity)

/-- The box `[−h, h]ⁿ`. -/
def mehtaBoxSet (L : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (fun _ => -mehtaH L) (fun _ => mehtaH L)

/-- The integrand on the box, extended by zero. -/
noncomputable def mehtaBox (L : ℕ) (c : ℂ) : (Fin n → ℝ) → ℂ :=
  (mehtaBoxSet L).indicator (mehtaApprox L c)

/-- The centre `(½, …, ½)` of the cube. -/
noncomputable def halfVec : Fin n → ℝ := fun _ => 1 / 2

/-! ### Scaling `t = ½ + s/(2h)` -/

theorem ofReal_inv_cpow {r : ℝ} (hr : 0 ≤ r) (w : ℂ) : ((r⁻¹ : ℝ) : ℂ) ^ w = (r : ℂ) ^ (-w) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

theorem ofReal_pow_cpow_real {r : ℝ} (hr : 0 < r) (P : ℕ) (w : ℂ) :
    (((r ^ P : ℝ)) : ℂ) ^ w = (r : ℂ) ^ ((P : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hr P).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    ← Complex.ofReal_log (pow_pos hr P).le, ← Complex.ofReal_log hr.le, Real.log_pow]
  push_cast
  ring_nf

theorem vandermondeDelta_const_add (h : ℝ) (v : Fin n → ℝ) :
    vandermondeDelta ((fun _ => h) + v) = vandermondeDelta v := by
  simp only [vandermondeDelta, Pi.add_apply, add_sub_add_left_eq_sub]

theorem mehta_quad {L : ℕ} (hL : 0 < L) (x : ℝ) :
    (1 / 2 + (2 * mehtaH L)⁻¹ * x) * (1 - (1 / 2 + (2 * mehtaH L)⁻¹ * x)) =
      (1 - x ^ 2 / (2 * L)) / 4 := by
  have hh := mehtaH_sq L
  have hh0 := (mehtaH_pos hL).ne'
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp
  linear_combination 2 * x ^ 2 * hh

/-- The scaled Selberg integrand. -/
theorem mehta_scaled_integrand {L : ℕ} (hL : 0 < L) (c : ℂ) (s : Fin n → ℝ) :
    selbergF ((L : ℂ) + 1) ((L : ℂ) + 1) c (halfVec + (2 * mehtaH L)⁻¹ • s) =
      (((4 : ℂ) ^ L) ^ n)⁻¹ * ((2 * mehtaH L : ℝ) : ℂ) ^ (-((pairCount n : ℂ) * (2 * c))) *
        mehtaApprox L c s := by
  have hρ : 0 < 2 * mehtaH L := by linarith [mehtaH_pos hL]
  have h2 : jacobiWeight ((L : ℂ) + 1) ((L : ℂ) + 1) (halfVec + (2 * mehtaH L)⁻¹ • s) =
      (((4 : ℂ) ^ L) ^ n)⁻¹ * ∏ k, ((1 - s k ^ 2 / (2 * L) : ℝ) : ℂ) ^ L := by
    simp only [jacobiWeight, add_sub_cancel_right, Complex.cpow_natCast, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, halfVec]
    rw [← Fin.prod_const, ← prod_inv_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    rw [← mul_pow, ← Complex.ofReal_mul, mehta_quad hL]
    push_cast
    rw [div_pow]
    ring
  have h3 : ((|vandermondeDelta (halfVec + (2 * mehtaH L)⁻¹ • s)| : ℝ) : ℂ) ^ (2 * c) =
      ((2 * mehtaH L : ℝ) : ℂ) ^ (-((pairCount n : ℂ) * (2 * c))) *
        ((|vandermondeDelta s| : ℝ) : ℂ) ^ (2 * c) := by
    unfold halfVec
    rw [vandermondeDelta_const_add, vandermondeDelta_smul, abs_mul, abs_pow, abs_inv,
      abs_of_pos hρ, inv_pow, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr (by positivity)) (abs_nonneg _),
      ofReal_inv_cpow (by positivity), ofReal_pow_cpow_real hρ, mul_neg]
  rw [selbergF, h2, h3, mehtaApprox]
  ring

theorem mem_cube_mehta_iff {L : ℕ} (hL : 0 < L) (s : Fin n → ℝ) :
    halfVec + (2 * mehtaH L)⁻¹ • s ∈ Set.Icc (0 : Fin n → ℝ) 1 ↔ s ∈ mehtaBoxSet L := by
  have hh := mehtaH_pos hL
  simp only [mehtaBoxSet, Set.mem_Icc, Pi.le_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, Pi.one_apply, halfVec]
  have key : ∀ x : ℝ, (0 ≤ 1 / 2 + (2 * mehtaH L)⁻¹ * x ↔ -mehtaH L ≤ x) ∧
      (1 / 2 + (2 * mehtaH L)⁻¹ * x ≤ 1 ↔ x ≤ mehtaH L) := by
    intro x
    rw [← div_eq_inv_mul]
    constructor
    · constructor
      · intro h
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * mehtaH L)).mp
          (show -(1 / 2) ≤ x / (2 * mehtaH L) by linarith)
        linarith
      · intro h
        have : -(1 / 2) ≤ x / (2 * mehtaH L) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        linarith
    · constructor
      · intro h
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * mehtaH L)).mp
          (show x / (2 * mehtaH L) ≤ 1 / 2 by linarith)
        linarith
      · intro h
        have : x / (2 * mehtaH L) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        linarith
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => (key (s i)).1.mp (h0 i), fun i => (key (s i)).2.mp (h1 i)⟩
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => (key (s i)).1.mpr (h0 i), fun i => (key (s i)).2.mpr (h1 i)⟩

theorem mehtaBox_eq {L : ℕ} (hL : 0 < L) (c : ℂ) (s : Fin n → ℝ) :
    mehtaBox L c s = ((4 : ℂ) ^ L) ^ n *
      ((2 * mehtaH L : ℝ) : ℂ) ^ ((pairCount n : ℂ) * (2 * c)) *
        (Set.Icc (0 : Fin n → ℝ) 1).indicator
          (selbergF ((L : ℂ) + 1) ((L : ℂ) + 1) c) (halfVec + (2 * mehtaH L)⁻¹ • s) := by
  have hρ : ((2 * mehtaH L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [mehtaH_pos hL] : (2 * mehtaH L) ≠ 0)
  have h4 : ((4 : ℂ) ^ L) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have hw : ((2 * mehtaH L : ℝ) : ℂ) ^ ((pairCount n : ℂ) * (2 * c)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hρ]; exact Complex.exp_ne_zero _
  by_cases hs : s ∈ mehtaBoxSet L
  · rw [mehtaBox, Set.indicator_of_mem hs, Set.indicator_of_mem ((mem_cube_mehta_iff hL s).mpr hs),
      mehta_scaled_integrand hL c s, Complex.cpow_neg]
    field_simp
    rw [mul_div_assoc, div_self (by simpa [mul_assoc] using hw), mul_one]
  · rw [mehtaBox, Set.indicator_of_notMem hs,
      Set.indicator_of_notMem (mt (mem_cube_mehta_iff hL s).mp hs), mul_zero]

theorem integrable_mehtaBox {L : ℕ} (hL : 0 < L) (c : ℂ)
    (h : IntegrableOn (selbergF ((L : ℂ) + 1) ((L : ℂ) + 1) c) (Set.Icc (0 : Fin n → ℝ) 1)) :
    Integrable (mehtaBox (n := n) L c) := by
  have hρ : (2 * mehtaH L)⁻¹ ≠ 0 := inv_ne_zero (by linarith [mehtaH_pos hL])
  have := ((((integrable_indicator_iff measurableSet_Icc).mpr h).comp_add_left
    (halfVec (n := n))).comp_smul hρ).const_mul
    (((4 : ℂ) ^ L) ^ n * ((2 * mehtaH L : ℝ) : ℂ) ^ ((pairCount n : ℂ) * (2 * c)))
  exact this.congr (ae_of_all _ fun s => (mehtaBox_eq hL c s).symm)

theorem integral_mehtaBox {L : ℕ} (hL : 0 < L) (c : ℂ) :
    ∫ s, mehtaBox (n := n) L c s = ((4 : ℂ) ^ L) ^ n *
      ((2 * mehtaH L : ℝ) : ℂ) ^ ((n : ℂ) + (pairCount n : ℂ) * (2 * c)) *
        ∫ t in Set.Icc (0 : Fin n → ℝ) 1, selbergF ((L : ℂ) + 1) ((L : ℂ) + 1) c t := by
  have hρ : 0 < 2 * mehtaH L := by linarith [mehtaH_pos hL]
  have hρ' : ((2 * mehtaH L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  simp_rw [mehtaBox_eq hL c]
  rw [integral_const_mul,
    Measure.integral_comp_smul volume (fun u => (Set.Icc (0 : Fin n → ℝ) 1).indicator
      (selbergF ((L : ℂ) + 1) ((L : ℂ) + 1) c) (halfVec + u)),
    integral_add_left_eq_self, Module.finrank_fin_fun, integral_indicator measurableSet_Icc,
    Complex.real_smul, inv_pow, inv_inv, abs_of_nonneg (by positivity), Complex.ofReal_pow,
    Complex.cpow_add _ _ hρ', Complex.cpow_natCast]
  ring

/-! ### Convergence of the integrands -/

theorem measurable_mehtaBox (L : ℕ) (c : ℂ) : Measurable (mehtaBox (n := n) L c) := by
  refine Measurable.indicator ?_ measurableSet_Icc
  unfold mehtaApprox vandermondeDelta
  fun_prop

theorem measurable_mehtaF (c : ℂ) : Measurable (mehtaF (n := n) c) := by
  unfold mehtaF vandermondeDelta
  fun_prop

theorem tendsto_one_sub_sq_div_pow (x : ℝ) :
    Tendsto (fun L : ℕ => (((1 - x ^ 2 / (2 * L) : ℝ)) : ℂ) ^ L) atTop
      (𝓝 ((Real.exp (-(x ^ 2) / 2) : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (Real.tendsto_one_add_div_pow_exp (-(x ^ 2) / 2))
  have e : ∀ L : ℕ, (((1 - x ^ 2 / (2 * L) : ℝ)) : ℂ) ^ L =
      (((1 + -(x ^ 2) / 2 / L) ^ L : ℝ) : ℂ) := fun L => by
    push_cast; ring_nf
  simp_rw [e]
  exact h

theorem tendsto_mehtaApprox (c : ℂ) (s : Fin n → ℝ) :
    Tendsto (fun L => mehtaApprox L c s) atTop (𝓝 (mehtaF c s)) :=
  (tendsto_finsetProd _ fun k _ => tendsto_one_sub_sq_div_pow (s k)).mul_const _

theorem tendsto_mehtaBox (c : ℂ) (s : Fin n → ℝ) :
    Tendsto (fun L => mehtaBox L c s) atTop (𝓝 (mehtaF c s)) := by
  obtain ⟨L₀, hL₀⟩ := exists_nat_ge (∑ i, s i ^ 2)
  refine (tendsto_mehtaApprox c s).congr' ?_
  filter_upwards [eventually_ge_atTop L₀] with L hL
  have hbox : s ∈ mehtaBoxSet L := by
    have hi : ∀ i, |s i| ≤ mehtaH L := fun i => by
      refine Real.abs_le_sqrt ?_
      have h1 := single_le_sum (fun j _ => sq_nonneg (s j)) (mem_univ i)
      have h2 : (L₀ : ℝ) ≤ L := by exact_mod_cast hL
      nlinarith
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  rw [mehtaBox, Set.indicator_of_mem hbox]

theorem mehta_factor_bounds {L : ℕ} {x : ℝ} (hx : -mehtaH L ≤ x ∧ x ≤ mehtaH L) :
    0 ≤ 1 - x ^ 2 / (2 * L) ∧ (1 - x ^ 2 / (2 * L)) ^ L ≤ Real.exp (-(x ^ 2) / 2) := by
  have hx2 : x ^ 2 / 2 ≤ L := by
    have := sq_le_sq' hx.1 hx.2
    rw [mehtaH_sq] at this
    linarith
  have he : x ^ 2 / (2 * L) = x ^ 2 / 2 / L := by rw [div_div]
  rw [he]
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos L with hL | hL
    · simp [hL]
    · rw [sub_nonneg, div_le_one (by exact_mod_cast hL)]; exact hx2
  · have := Real.one_sub_div_pow_le_exp_neg hx2
    rwa [neg_div]

theorem norm_mehtaApprox_le {L : ℕ} (c : ℂ) {s : Fin n → ℝ} (hs : s ∈ mehtaBoxSet L) :
    ‖mehtaApprox L c s‖ ≤ ‖mehtaF c s‖ := by
  unfold mehtaApprox mehtaF
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  refine mul_le_mul_of_nonneg_right
    (prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_) (norm_nonneg _)
  obtain ⟨h0, h1⟩ := mehta_factor_bounds ⟨hs.1 k, hs.2 k⟩
  rw [norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg h0, abs_of_pos (Real.exp_pos _)]
  exact h1

theorem norm_mehtaF_re {c : ℂ} {s : Fin n → ℝ} (hΔ : vandermondeDelta s ≠ 0) :
    ‖mehtaF c s‖ = ‖mehtaF (c.re : ℂ) s‖ := by
  simp only [mehtaF, norm_mul]
  congr 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hΔ),
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hΔ)]
  simp

theorem norm_mehtaBox_le (L : ℕ) (c : ℂ) :
    ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)), ‖mehtaBox L c s‖ ≤ ‖mehtaF (c.re : ℂ) s‖ := by
  filter_upwards [ae_vandermondeDelta_ne_zero] with s hΔ
  by_cases hs : s ∈ mehtaBoxSet L
  · rw [mehtaBox, Set.indicator_of_mem hs, ← norm_mehtaF_re hΔ]
    exact norm_mehtaApprox_le c hs
  · rw [mehtaBox, Set.indicator_of_notMem hs, norm_zero]
    exact norm_nonneg _

open scoped ComplexOrder in
theorem mehtaBox_nonneg (L : ℕ) (c : ℝ) (s : Fin n → ℝ) : 0 ≤ mehtaBox L (c : ℂ) s := by
  by_cases hs : s ∈ mehtaBoxSet L
  · rw [mehtaBox, Set.indicator_of_mem hs]
    refine mul_nonneg (prod_nonneg fun k _ => ?_) ?_
    · rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (pow_nonneg (mehta_factor_bounds ⟨hs.1 k, hs.2 k⟩).1 _)
    · rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (abs_nonneg _)]
      exact Complex.zero_le_real.mpr (Real.rpow_nonneg (abs_nonneg _) _)
  · rw [mehtaBox, Set.indicator_of_notMem hs]

/-- For large `L`, 5.14.4 evaluates the box integrals. -/
theorem eventually_mehtaBox {c : ℂ} (hc1 : -1 < (n : ℝ) * c.re) :
    ∀ᶠ L : ℕ in atTop, Integrable (mehtaBox (n := n) L c) ∧
      ∫ s, mehtaBox (n := n) L c s = ((4 : ℂ) ^ L) ^ n *
        ((2 * mehtaH L : ℝ) : ℂ) ^ ((n : ℂ) + (pairCount n : ℂ) * (2 * c)) *
          selbergRHS n 0 ((L : ℂ) + 1) ((L : ℂ) + 1) c := by
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (-(((n - 1 : ℕ) : ℝ) * c.re))
  filter_upwards [eventually_ge_atTop (L₀ + 1)] with L hL
  have hL0 : 0 < L := by omega
  have hLr : (L₀ : ℝ) + 1 ≤ L := by exact_mod_cast hL
  have ha : 0 < ((L : ℂ) + 1).re := by simp; positivity
  have hca : -((L : ℂ) + 1).re < ((n - 1 : ℕ) : ℝ) * c.re := by simp; linarith
  have hdom : c ∈ selbergDomain n ((L : ℂ) + 1) ((L : ℂ) + 1) := ⟨hc1, hca, hca⟩
  refine ⟨integrable_mehtaBox hL0 c (integrableOn_selbergF ha ha hdom), ?_⟩
  rw [integral_mehtaBox hL0 c]
  have h := dlmf_5_14_4_full (m := 0) (Nat.zero_le n) ha ha hc1 hca hca
  simp only [Nat.not_lt_zero, filter_false, prod_empty, one_mul] at h
  rw [h]

/-- The constant `4^{nL}(2h)^{n+n(n−1)c} S_n(L+1, L+1, c)`. -/
noncomputable def mehtaSeq (n : ℕ) (c : ℂ) (L : ℕ) : ℂ :=
  ((4 : ℂ) ^ L) ^ n * ((2 * mehtaH L : ℝ) : ℂ) ^ ((n : ℂ) + (pairCount n : ℂ) * (2 * c)) *
    selbergRHS n 0 ((L : ℂ) + 1) ((L : ℂ) + 1) c

/-- **Convergence** of Mehta's integral for real `c > −1/n`, by Fatou's lemma, given the limit of
the constants. -/
theorem integrable_mehta_real {c : ℝ} (hc1 : -1 < (n : ℝ) * c) {M : ℂ}
    (hM : Tendsto (mehtaSeq n (c : ℂ)) atTop (𝓝 M)) :
    Integrable (mehtaF (n := n) (c : ℂ)) := by
  have hev := eventually_mehtaBox (n := n) (c := (c : ℂ)) (by simpa)
  refine ⟨(measurable_mehtaF _).aestronglyMeasurable, ?_⟩
  have hint : Tendsto (fun L => ∫⁻ s, ‖mehtaBox (n := n) L (c : ℂ) s‖ₑ) atTop
      (𝓝 (ENNReal.ofReal M.re)) := by
    have h1 := (ENNReal.continuous_ofReal.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp hM)
    refine h1.congr' ?_
    filter_upwards [hev] with L ⟨hi, hI⟩
    rw [Function.comp_apply, Function.comp_apply, mehtaSeq, ← hI,
      show (∫ s, mehtaBox (n := n) L (c : ℂ) s).re =
        ∫ s, (mehtaBox (n := n) L (c : ℂ) s).re from (integral_re hi).symm,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun s => Complex.re_eq_norm.mpr (mehtaBox_nonneg L c s))
  calc ∫⁻ s, ‖mehtaF (n := n) (c : ℂ) s‖ₑ
      = ∫⁻ s, liminf (fun L => ‖mehtaBox (n := n) L (c : ℂ) s‖ₑ) atTop :=
        lintegral_congr fun s => ((tendsto_mehtaBox _ s).enorm.liminf_eq).symm
    _ ≤ liminf (fun L => ∫⁻ s, ‖mehtaBox (n := n) L (c : ℂ) s‖ₑ) atTop :=
        lintegral_liminf_le fun L => (measurable_mehtaBox L _).enorm
    _ = _ := hint.liminf_eq
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Mehta's integral equals the limit of the constants. -/
theorem integral_mehtaF_eq {c : ℂ} (hc1 : -1 < (n : ℝ) * c.re) {M M' : ℂ}
    (hM : Tendsto (mehtaSeq n c) atTop (𝓝 M))
    (hM' : Tendsto (mehtaSeq n (c.re : ℂ)) atTop (𝓝 M')) :
    ∫ s, mehtaF (n := n) c s = M := by
  have hbound := integrable_mehta_real (n := n) hc1 hM'
  have hdct : Tendsto (fun L => ∫ s, mehtaBox (n := n) L c s) atTop (𝓝 (∫ s, mehtaF c s)) :=
    tendsto_integral_of_dominated_convergence _
      (fun L => (measurable_mehtaBox L c).aestronglyMeasurable) hbound.norm
      (fun L => norm_mehtaBox_le L c) (ae_of_all _ fun s => tendsto_mehtaBox c s)
  have hval : Tendsto (fun L => ∫ s, mehtaBox (n := n) L c s) atTop (𝓝 M) :=
    hM.congr' (by filter_upwards [eventually_mehtaBox hc1] with L h using h.2.symm)
  exact tendsto_nhds_unique hdct hval

/-! ### The Gamma factors -/

theorem cpow_sum_range {x : ℂ} (hx : x ≠ 0) (f : ℕ → ℂ) (N : ℕ) :
    x ^ (∑ k ∈ range N, f k) = ∏ k ∈ range N, x ^ f k := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, prod_range_succ, Complex.cpow_add _ _ hx, ih]

theorem sum_range_natCast_mul_two (N : ℕ) : (∑ k ∈ range N, (k : ℂ)) * 2 = N * ((N : ℂ) - 1) := by
  have h : (((∑ k ∈ range N, k) * 2 : ℕ) : ℂ) = ((N * (N - 1) : ℕ) : ℂ) := by
    rw [sum_range_id_mul_two]
  rcases N with _ | N
  · simp
  · push_cast at h ⊢
    simpa using h

/-- `(2h)^w = 2^{3w/2} L^{w/2}` for `h = √(2L)`. -/
theorem mehtaRho_cpow {L : ℕ} (hL : 0 < L) (w : ℂ) :
    ((2 * mehtaH L : ℝ) : ℂ) ^ w = (2 : ℂ) ^ (3 * w / 2) * (L : ℂ) ^ (w / 2) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hρ : 0 < 2 * mehtaH L := by linarith [mehtaH_pos hL]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hρ.ne'),
    Complex.cpow_def_of_ne_zero two_ne_zero, Complex.cpow_def_of_ne_zero (by exact_mod_cast hL.ne'),
    ← Complex.exp_add, ← Complex.ofReal_log hρ.le, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hL'.le,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2),
    mehtaH, Real.log_mul two_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne',
    Real.log_sqrt (by positivity), Real.log_mul two_ne_zero hL'.ne']
  push_cast
  ring_nf

/-- One Gamma factor of `mehtaSeq`. -/
noncomputable def mehtaT (n : ℕ) (c : ℂ) (k L : ℕ) : ℂ :=
  (4 : ℂ) ^ L * ((2 * mehtaH L : ℝ) : ℂ) ^ (1 + 2 * k * c) *
    (Complex.Gamma ((L : ℂ) + 1 + ((n : ℂ) - (k + 1)) * c) *
      Complex.Gamma ((L : ℂ) + 1 + ((n : ℂ) - (k + 1)) * c) /
      Complex.Gamma ((L : ℂ) + 1 + ((L : ℂ) + 1) + (2 * n - (k + 1) - 1) * c))

theorem mehtaSeq_eq (c : ℂ) {L : ℕ} (hL : 0 < L) :
    mehtaSeq n c L = (Complex.Gamma (1 + c) ^ n)⁻¹ *
      ∏ k ∈ range n, (mehtaT n c k L * Complex.Gamma (1 + (k + 1) * c)) := by
  have hρ : ((2 * mehtaH L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [mehtaH_pos hL] : (2 * mehtaH L) ≠ 0)
  have hsum : (n : ℂ) + (pairCount n : ℂ) * (2 * c) = ∑ k ∈ range n, (1 + 2 * (k : ℂ) * c) := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_one, ← sum_mul, ← mul_sum]
    linear_combination c * pairCount_cast n - c * sum_range_natCast_mul_two n
  have h4 : ((4 : ℂ) ^ L) ^ n = ∏ _k ∈ range n, (4 : ℂ) ^ L := by simp
  rw [mehtaSeq, hsum, cpow_sum_range hρ, h4, selbergRHS, range_zero, prod_empty, mul_one]
  calc _ = (Complex.Gamma (1 + c) ^ n)⁻¹ * ((∏ _k ∈ range n, (4 : ℂ) ^ L) *
        (∏ k ∈ range n, ((2 * mehtaH L : ℝ) : ℂ) ^ (1 + 2 * (k : ℂ) * c)) *
        ∏ k ∈ range n, Complex.Gamma ((L : ℂ) + 1 + ((n : ℂ) - (k + 1)) * c) *
          Complex.Gamma ((L : ℂ) + 1 + ((n : ℂ) - (k + 1)) * c) *
          Complex.Gamma (1 + (k + 1) * c) /
          Complex.Gamma ((L : ℂ) + 1 + ((L : ℂ) + 1) + (2 * n - (k + 1) - 1) * c)) := by ring
    _ = _ := by
      rw [← prod_mul_distrib, ← prod_mul_distrib]
      congr 1
      refine prod_congr rfl fun k _ => ?_
      rw [mehtaT]
      ring

/-- The limit of one Gamma factor. -/
theorem tendsto_mehtaT (c : ℂ) (k : ℕ) :
    Tendsto (mehtaT n c k) atTop (𝓝 ((2 : ℂ) ^ (1 / 2 + (4 * k - 2 * n + 2) * c) *
      ((Real.sqrt Real.pi : ℝ) : ℂ))) := by
  set x : ℂ := ((n : ℂ) - (k + 1)) * c
  set y : ℂ := (2 * n - (k + 1) - 1) * c
  set w : ℂ := 1 + 2 * k * c
  have hA1 := tendsto_Gamma_ratio_nat (1 + x) (1 + y / 2)
  have hA2 := tendsto_Gamma_ratio_nat (1 + x) (1 + y / 2 + 1 / 2)
  rw [show 1 + y / 2 - (1 + x) = y / 2 - x by ring] at hA1
  rw [show 1 + y / 2 + 1 / 2 - (1 + x) = y / 2 + 1 / 2 - x by ring] at hA2
  have hlim := (hA1.mul hA2).const_mul ((2 : ℂ) ^ (1 / 2 + (4 * k - 2 * n + 2) * c) *
    ((Real.sqrt Real.pi : ℝ) : ℂ))
  rw [mul_one, mul_one] at hlim
  refine hlim.congr' ?_
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt ‖y‖
  filter_upwards [eventually_ge_atTop (L₀ + 1)] with L hL
  have hL0 : 0 < L := by omega
  have hLr : (L₀ : ℝ) + 1 ≤ L := by exact_mod_cast hL
  set z : ℂ := (L : ℂ) + (1 + y / 2)
  have hre : -‖y‖ ≤ y.re := by linarith [(abs_le.mp (Complex.abs_re_le_norm y)).1]
  have hz : 0 < z.re := by simp [z]; linarith
  have hz' : 0 < (z + 1 / 2).re := by simp [z]; linarith
  have hZ1 := Gamma_ne_zero_of_re hz
  have hZ2 := Gamma_ne_zero_of_re hz'
  have hX : (2 : ℂ) ^ (1 - 2 * z) * ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by rw [Complex.cpow_def_of_ne_zero two_ne_zero]; exact Complex.exp_ne_zero _)
      (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have hdup := Complex.Gamma_mul_Gamma_add_half z
  have hD : Complex.Gamma ((L : ℂ) + 1 + ((L : ℂ) + 1) + y) =
      Complex.Gamma z * Complex.Gamma (z + 1 / 2) /
        ((2 : ℂ) ^ (1 - 2 * z) * ((Real.sqrt Real.pi : ℝ) : ℂ)) := by
    rw [eq_div_iff hX, hdup, show (L : ℂ) + 1 + ((L : ℂ) + 1) + y = 2 * z by simp only [z]; ring]
    ring
  have hP2 : (4 : ℂ) ^ L * (2 : ℂ) ^ (3 * w / 2) * (2 : ℂ) ^ (1 - 2 * z) =
      (2 : ℂ) ^ (1 / 2 + (4 * k - 2 * n + 2) * c) := by
    rw [show (4 : ℂ) ^ L = (2 : ℂ) ^ (((2 * L : ℕ) : ℂ)) by
      rw [Complex.cpow_natCast, pow_mul]; norm_num,
      ← Complex.cpow_add _ _ two_ne_zero, ← Complex.cpow_add _ _ two_ne_zero]
    congr 1
    simp only [z, w, y]
    push_cast
    ring
  have hPL : (L : ℂ) ^ (w / 2) = (L : ℂ) ^ (y / 2 - x) * (L : ℂ) ^ (y / 2 + 1 / 2 - x) := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hL0.ne')]
    congr 1
    simp only [w, x, y]
    ring
  have e1 : (L : ℂ) + (1 + x) = (L : ℂ) + 1 + x := by ring
  have e2 : (L : ℂ) + (1 + y / 2 + 1 / 2) = z + 1 / 2 := by simp only [z]; ring
  rw [mehtaT, hD, mehtaRho_cpow hL0, hPL, e1, e2, ← hP2]
  simp only [z, x, y, w]
  field_simp

theorem two_cpow_half_mul_sqrt_pi (n : ℕ) :
    (2 : ℂ) ^ ((n : ℂ) / 2) * ((Real.sqrt Real.pi : ℝ) : ℂ) ^ n =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ n := by
  have h2 : (2 : ℂ) ^ ((1 : ℂ) / 2) = ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
    push_cast; ring_nf
  rw [show (n : ℂ) / 2 = n * (1 / 2) by ring, Complex.cpow_nat_mul, h2, ← mul_pow,
    ← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]

theorem sum_mehta_exponent (n : ℕ) (c : ℂ) :
    ∑ k ∈ range n, (1 / 2 + (4 * (k : ℂ) - 2 * n + 2) * c) = (n : ℂ) / 2 := by
  have h := sum_range_natCast_mul_two n
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul, sum_sub_distrib,
    ← mul_sum]
  linear_combination 2 * c * h

/-- The constants converge to `(2π)^{n/2} ∏ Γ(1 + kc)/Γ(1 + c)`. -/
theorem tendsto_mehtaSeq (c : ℂ) :
    Tendsto (mehtaSeq n c) atTop (𝓝 (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ n *
      ((Complex.Gamma (1 + c) ^ n)⁻¹ * ∏ k ∈ range n, Complex.Gamma (1 + (k + 1) * c)))) := by
  have h := (tendsto_finsetProd (range n) fun k _ =>
    (tendsto_mehtaT (n := n) c k).mul_const (Complex.Gamma (1 + (k + 1) * c))).const_mul
      (Complex.Gamma (1 + c) ^ n)⁻¹
  have hval : (Complex.Gamma (1 + c) ^ n)⁻¹ * ∏ k ∈ range n,
      ((2 : ℂ) ^ (1 / 2 + (4 * k - 2 * n + 2) * c) * ((Real.sqrt Real.pi : ℝ) : ℂ) *
        Complex.Gamma (1 + (k + 1) * c)) = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ n *
      ((Complex.Gamma (1 + c) ^ n)⁻¹ * ∏ k ∈ range n, Complex.Gamma (1 + (k + 1) * c)) := by
    rw [prod_mul_distrib, prod_mul_distrib, ← cpow_sum_range two_ne_zero, sum_mehta_exponent,
      prod_const, card_range, ← two_cpow_half_mul_sqrt_pi]
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  exact (mehtaSeq_eq c hL).symm

/-- **DLMF 5.14.6** (Mehta's integral) on DLMF's full range `ℜc > −1/n` (stated as
`n ℜc > −1`):
`(2π)^{−n/2} ∫_{ℝⁿ} ∏ e^{−tₖ²/2} |Δ(t)|^{2c} dt = ∏_{k=1}^n Γ(1 + kc)/Γ(1 + c)^n`. -/
theorem dlmf_5_14_6 {c : ℂ} (hc1 : -1 < (n : ℝ) * c.re) :
    (((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)⁻¹ * ∫ t, mehtaF (n := n) c t =
      (∏ k ∈ range n, Complex.Gamma (1 + (k + 1) * c)) / Complex.Gamma (1 + c) ^ n := by
  rw [integral_mehtaF_eq hc1 (tendsto_mehtaSeq c) (tendsto_mehtaSeq (c.re : ℂ))]
  have hs : (2 * Real.pi) ^ ((n : ℝ) / 2) = Real.sqrt (2 * Real.pi) ^ n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  have hne : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ^ n ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne')
  rw [hs, Complex.ofReal_pow, inv_mul_cancel_left₀ hne, div_eq_inv_mul]

end Azurite.DLMF
