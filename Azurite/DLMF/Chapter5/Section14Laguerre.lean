/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Range
import Azurite.DLMF.Chapter5.Section11Ratio

/-!
# DLMF 5.14.5: the Laguerre form of Selberg's integral

We take `b = N + 1 → ∞` in 5.14.4 (`dlmf_5_14_4_full`) after the substitution `t = s/N`:
`∫_{[0,N]ⁿ} s₁⋯sₘ ∏ sₖ^{a−1}(1 − sₖ/N)^N |Δ(s)|^{2c} ds = N^{m+na+n(n−1)c} S_n(a, N + 1, c)`.
The integrands converge pointwise to `s₁⋯sₘ ∏ sₖ^{a−1}e^{−sₖ}|Δ(s)|^{2c}` and are bounded by
it (`(1 − s/N)^N ≤ e^{−s}`). For real parameters they are nonnegative, so **Fatou's lemma** gives
convergence of the limit integral on DLMF's full range; dominated convergence then gives the value,
and the Gamma ratios are handled by 5.11.12 (`Γ(N + x)/Γ(N + y) ∼ N^{x−y}`).
-/

open Finset MeasureTheory Filter Topology

namespace Azurite.DLMF

variable {n : ℕ}

/-- The Laguerre integrand `∏ tₖ^{a−1}e^{−tₖ} |Δ(t)|^{2c}`. -/
noncomputable def laguerreF (a c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ k, (t k : ℂ) ^ (a - 1) * Complex.exp (-(t k : ℂ))) *
    ((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c)

/-- The approximants `∏ tₖ^{a−1}(1 − tₖ/N)^N |Δ(t)|^{2c}`. -/
noncomputable def laguerreApprox (N : ℕ) (a c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ k, (t k : ℂ) ^ (a - 1) * ((1 - t k / N : ℝ) : ℂ) ^ N) *
    ((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c)

/-- The right side of 5.14.5:
`Γ(1+c)^{−n} ∏_{k=1}^m (a+(n−k)c) ∏_{k=1}^n Γ(a+(n−k)c)Γ(1+kc)` (with `k ↦ k + 1`). -/
noncomputable def laguerreRHS (n m : ℕ) (a c : ℂ) : ℂ :=
  (Complex.Gamma (1 + c) ^ n)⁻¹ * (∏ k ∈ range m, (a + ((n : ℂ) - (k + 1)) * c)) *
    ∏ k ∈ range n, Complex.Gamma (a + ((n : ℂ) - (k + 1)) * c) * Complex.Gamma (1 + (k + 1) * c)

/-! ### Scaling `t = s/N` -/

/-- The number of pairs `j < k` in `Fin n`. -/
def pairCount (n : ℕ) : ℕ := ∑ j : Fin n, (Ioi j).card

theorem two_mul_pairCount (n : ℕ) : 2 * pairCount n = n * (n - 1) := by
  rw [pairCount]
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun j => n - 1 - j) n, sum_range_reflect (fun j => j) n,
    mul_comm, sum_range_id_mul_two]

theorem vandermondeDelta_smul (r : ℝ) (t : Fin n → ℝ) :
    vandermondeDelta (r • t) = r ^ pairCount n * vandermondeDelta t := by
  simp only [vandermondeDelta, pairCount, Pi.smul_apply, smul_eq_mul, ← mul_sub,
    prod_mul_distrib, prod_const, prod_pow_eq_pow_sum]

theorem arg_natCast_ne_pi (N : ℕ) : (N : ℂ).arg ≠ Real.pi := by
  rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
  exact Real.pi_ne_zero.symm

theorem ofReal_inv_mul_cpow {N : ℕ} {x : ℝ} (hx : 0 ≤ x) (w : ℂ) :
    ((((N : ℝ))⁻¹ * x : ℝ) : ℂ) ^ w = (N : ℂ) ^ (-w) * (x : ℂ) ^ w := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hx,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ (arg_natCast_ne_pi N),
    Complex.cpow_neg]

theorem ofReal_pow_cpow {N : ℕ} (hN : 0 < N) (P : ℕ) (w : ℂ) :
    ((((N : ℝ) ^ P : ℝ)) : ℂ) ^ w = (N : ℂ) ^ ((P : ℂ) * w) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hN' P).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hN.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (pow_pos hN' P).le, ← Complex.ofReal_log hN'.le, Real.log_pow]
  push_cast
  ring_nf

/-- The scaled Selberg integrand. -/
theorem scaled_integrand {N : ℕ} (hN : 0 < N) (m : ℕ) (a c : ℂ) {s : Fin n → ℝ}
    (hs : ∀ i, 0 ≤ s i) :
    initProd m ((N : ℝ)⁻¹ • s) * selbergF a ((N : ℂ) + 1) c ((N : ℝ)⁻¹ • s) =
      (N : ℂ) ^ (-((min n m : ℕ) + n * (a - 1) + pairCount n * (2 * c))) *
        (initProd m s * laguerreApprox N a c s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : initProd m ((N : ℝ)⁻¹ • s) = (N : ℂ) ^ (-((min n m : ℕ) : ℂ)) * initProd m s := by
    simp only [initProd, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, prod_mul_distrib,
      prod_const, Fin.card_filter_val_lt, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
  have h2 : jacobiWeight a ((N : ℂ) + 1) ((N : ℝ)⁻¹ • s) =
      (N : ℂ) ^ ((n : ℂ) * -(a - 1)) *
        ∏ k, (s k : ℂ) ^ (a - 1) * ((1 - s k / N : ℝ) : ℂ) ^ N := by
    simp only [jacobiWeight, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right,
      Complex.cpow_natCast]
    rw [Complex.cpow_nat_mul, ← Fin.prod_const, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    rw [ofReal_inv_mul_cpow (hs k), div_eq_inv_mul]
    ring
  have h3 : ((|vandermondeDelta ((N : ℝ)⁻¹ • s)| : ℝ) : ℂ) ^ (2 * c) =
      (N : ℂ) ^ (-((pairCount n : ℂ) * (2 * c))) *
        ((|vandermondeDelta s| : ℝ) : ℂ) ^ (2 * c) := by
    rw [vandermondeDelta_smul, abs_mul, abs_pow, abs_inv, Nat.abs_cast, inv_pow,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr (by positivity))
        (abs_nonneg _), Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm),
      ofReal_pow_cpow hN, Complex.cpow_neg]
  rw [selbergF, h1, h2, h3, laguerreApprox]
  have hE : (N : ℂ) ^ (-((min n m : ℕ) + n * (a - 1) + pairCount n * (2 * c)) : ℂ) =
      (N : ℂ) ^ (-((min n m : ℕ) : ℂ)) * (N : ℂ) ^ ((n : ℂ) * -(a - 1)) *
        (N : ℂ) ^ (-((pairCount n : ℂ) * (2 * c))) := by
    rw [← Complex.cpow_add _ _ hN0, ← Complex.cpow_add _ _ hN0]
    ring_nf
  rw [hE]
  ring

theorem mem_cube_smul_iff {N : ℕ} (hN : 0 < N) (s : Fin n → ℝ) :
    (N : ℝ)⁻¹ • s ∈ Set.Icc (0 : Fin n → ℝ) 1 ↔
      s ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Set.mem_Icc, Pi.le_def, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.one_apply]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := h0 i
      rwa [mul_nonneg_iff_of_pos_left (inv_pos.mpr hN')] at this
    · have := h1 i
      rwa [inv_mul_le_iff₀ hN', mul_one] at this
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => mul_nonneg (inv_nonneg.mpr hN'.le) (h0 i), fun i => by
      rw [inv_mul_le_iff₀ hN', mul_one]; exact h1 i⟩

/-- The integrand on the box `[0, N]ⁿ` is the rescaled Selberg integrand. -/
theorem box_indicator_eq {N : ℕ} (hN : 0 < N) (m : ℕ) (a c : ℂ) (s : Fin n → ℝ) :
    (Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))).indicator
        (fun s => initProd m s * laguerreApprox N a c s) s =
      (N : ℂ) ^ ((min n m : ℕ) + n * (a - 1) + pairCount n * (2 * c) : ℂ) *
        (Set.Icc (0 : Fin n → ℝ) 1).indicator
          (fun t => initProd m t * selbergF a ((N : ℂ) + 1) c t) ((N : ℝ)⁻¹ • s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases hs : s ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((mem_cube_smul_iff hN s).mpr hs),
      scaled_integrand hN m a c (fun i => hs.1 i), ← mul_assoc, ← Complex.cpow_add _ _ hN0,
      add_neg_cancel, Complex.cpow_zero, one_mul]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (mt (mem_cube_smul_iff hN s).mp hs),
      mul_zero]

theorem integrable_box {N : ℕ} (hN : 0 < N) (m : ℕ) (a c : ℂ)
    (h : IntegrableOn (fun t => initProd m t * selbergF a ((N : ℂ) + 1) c t)
      (Set.Icc (0 : Fin n → ℝ) 1)) :
    Integrable ((Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))).indicator
        (fun s => initProd m s * laguerreApprox N a c s)) := by
  have hN' : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hN.ne')
  have := (((integrable_indicator_iff measurableSet_Icc).mpr h).comp_smul hN').const_mul
    ((N : ℂ) ^ ((min n m : ℕ) + n * (a - 1) + pairCount n * (2 * c) : ℂ))
  exact this.congr (ae_of_all _ fun s => (box_indicator_eq hN m a c s).symm)

theorem integral_box_eq {N : ℕ} (hN : 0 < N) (m : ℕ) (a c : ℂ) :
    ∫ s, (Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))).indicator
        (fun s => initProd m s * laguerreApprox N a c s) s =
      (N : ℂ) ^ ((min n m : ℕ) + n * a + pairCount n * (2 * c) : ℂ) *
        ∫ t in Set.Icc (0 : Fin n → ℝ) 1, initProd m t * selbergF a ((N : ℂ) + 1) c t := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp_rw [box_indicator_eq hN m a c]
  rw [integral_const_mul, Measure.integral_comp_smul, Module.finrank_fin_fun,
    integral_indicator measurableSet_Icc, Complex.real_smul, inv_pow, inv_inv,
    abs_of_nonneg (by positivity), Complex.ofReal_pow, Complex.ofReal_natCast, ← mul_assoc,
    ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hN0]
  ring_nf

/-- Selberg's integral with Aomoto's factor converges on DLMF's range. -/
theorem integrableOn_initProd_mul_full (m : ℕ) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : c ∈ selbergDomain n a b) :
    IntegrableOn (fun t => initProd m t * selbergF a b c t) (Set.Icc (0 : Fin n → ℝ) 1) := by
  refine (integrableOn_selbergF ha hb hc).norm.mono'
    ((measurable_initProd m).mul (measurable_selbergF a b c)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_initProd_le (mem_cube_iff.mp ht))
    (norm_nonneg _)).trans (one_mul _).le

/-! ### The Gamma factors -/

theorem tendsto_natCast_sector : Tendsto (fun N : ℕ => (N : ℂ)) atTop
    (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (Real.pi - Real.pi))) := by
  refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
  · rw [← tendsto_norm_atTop_iff_cobounded]
    simpa using tendsto_natCast_atTop_atTop (R := ℝ)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    refine ⟨by exact_mod_cast hN.ne', ?_⟩
    simp [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg]

/-- `N^{y−x} Γ(N + x)/Γ(N + y) → 1` (from 5.11.12). -/
theorem tendsto_Gamma_ratio_nat (x y : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (y - x) * (Complex.Gamma (N + x) / Complex.Gamma (N + y)))
      atTop (𝓝 1) := by
  have h : Tendsto _ _ _ := dlmf_5_11_12 x y Real.pi_pos le_rfl
  refine (h.comp tendsto_natCast_sector).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp only [Function.comp_apply]
  rw [show y - x = -(x - y) by ring, Complex.cpow_neg]
  ring

theorem tendsto_nat_div_add (w : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) / (N + w)) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have h2 : Tendsto (fun N : ℕ => (1 + w * (N : ℂ)⁻¹)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ)).add (h.const_mul w)).inv₀ (by simp)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show 1 + w * (N : ℂ)⁻¹ = (N + w) / N by field_simp, inv_div]

/-- `N^{m + n(a + (n−1)c)} S_n(a, N + 1, c) → ` the right side of 5.14.5. -/
theorem tendsto_selbergRHS_scaled (m : ℕ) (a c : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ ((m : ℂ) + n * (a + (n - 1) * c)) *
      selbergRHS n m a ((N : ℂ) + 1) c) atTop (𝓝 (laguerreRHS n m a c)) := by
  set e := a + ((n : ℂ) - 1) * c
  have hlim : Tendsto (fun N : ℕ => (Complex.Gamma (1 + c) ^ n)⁻¹ *
      (∏ k ∈ range m, ((a + ((n : ℂ) - (k + 1)) * c) *
        ((N : ℂ) / (N + (a + 1 + (2 * n - (k + 1) - 1) * c))))) *
      ∏ k ∈ range n, (Complex.Gamma (a + ((n : ℂ) - (k + 1)) * c) *
        Complex.Gamma (1 + (k + 1) * c) *
        ((N : ℂ) ^ e * (Complex.Gamma (N + (1 + ((n : ℂ) - (k + 1)) * c)) /
          Complex.Gamma (N + (a + 1 + (2 * n - (k + 1) - 1) * c))))))
      atTop (𝓝 (laguerreRHS n m a c)) := by
    have hr : ∀ k : ℕ, Tendsto (fun N : ℕ => (N : ℂ) ^ e *
        (Complex.Gamma (N + (1 + ((n : ℂ) - (k + 1)) * c)) /
          Complex.Gamma (N + (a + 1 + (2 * n - (k + 1) - 1) * c)))) atTop (𝓝 1) := by
      intro k
      have := tendsto_Gamma_ratio_nat (1 + ((n : ℂ) - (k + 1)) * c)
        (a + 1 + (2 * n - (k + 1) - 1) * c)
      rwa [show a + 1 + (2 * n - (k + 1) - 1) * c - (1 + ((n : ℂ) - (k + 1)) * c) = e by
        simp only [e]; ring] at this
    have := ((tendsto_const_nhds (x := (Complex.Gamma (1 + c) ^ n)⁻¹)).mul
      (tendsto_finsetProd (range m) fun k _ =>
        (tendsto_const_nhds (x := a + ((n : ℂ) - (k + 1)) * c)).mul
          (tendsto_nat_div_add (a + 1 + (2 * n - (k + 1) - 1) * c)))).mul
      (tendsto_finsetProd (range n) fun k _ =>
        (tendsto_const_nhds (x := Complex.Gamma (a + ((n : ℂ) - (k + 1)) * c) *
          Complex.Gamma (1 + (k + 1) * c))).mul (hr k))
    simpa [laguerreRHS] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm' : (N : ℂ) ^ m = ∏ _k ∈ range m, (N : ℂ) := by simp
  have hn' : ((N : ℂ) ^ e) ^ n = ∏ _k ∈ range n, (N : ℂ) ^ e := by simp
  symm
  rw [Complex.cpow_add (m : ℂ) ((n : ℂ) * e) hN0, Complex.cpow_natCast, Complex.cpow_nat_mul, hm',
    hn', selbergRHS]
  calc _ = (Complex.Gamma (1 + c) ^ n)⁻¹ *
        ((∏ _k ∈ range m, (N : ℂ)) * ∏ k ∈ range m,
          (a + ((n : ℂ) - (k + 1)) * c) / (a + ((N : ℂ) + 1) + (2 * n - (k + 1) - 1) * c)) *
        ((∏ _k ∈ range n, (N : ℂ) ^ e) * ∏ k ∈ range n,
          Complex.Gamma (a + ((n : ℂ) - (k + 1)) * c) *
            Complex.Gamma ((N : ℂ) + 1 + ((n : ℂ) - (k + 1)) * c) *
            Complex.Gamma (1 + (k + 1) * c) /
              Complex.Gamma (a + ((N : ℂ) + 1) + (2 * n - (k + 1) - 1) * c)) := by ring
    _ = _ := by
      rw [← prod_mul_distrib, ← prod_mul_distrib]
      congr 2
      · refine prod_congr rfl fun k _ => ?_
        rw [show a + ((N : ℂ) + 1) + (2 * n - (k + 1) - 1) * c =
          N + (a + 1 + (2 * n - (k + 1) - 1) * c) by ring]
        ring
      · funext k
        rw [show a + ((N : ℂ) + 1) + (2 * n - (k + 1) - 1) * c =
          N + (a + 1 + (2 * n - (k + 1) - 1) * c) by ring, add_assoc (N : ℂ) 1]
        ring

/-! ### Convergence of the integrands -/

/-- The integrand on the box `[0, N]ⁿ`, extended by zero. -/
noncomputable def laguerreBox (N m : ℕ) (a c : ℂ) : (Fin n → ℝ) → ℂ :=
  (Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))).indicator
    (fun s => initProd m s * laguerreApprox N a c s)

/-- The integrand of 5.14.5 on `[0, ∞)ⁿ`, extended by zero. -/
noncomputable def laguerreTarget (m : ℕ) (a c : ℂ) : (Fin n → ℝ) → ℂ :=
  (Set.Ici (0 : Fin n → ℝ)).indicator (fun s => initProd m s * laguerreF a c s)

theorem measurable_laguerreBox (N m : ℕ) (a c : ℂ) : Measurable (laguerreBox (n := n) N m a c) := by
  refine ((measurable_initProd m).mul ?_).indicator measurableSet_Icc
  unfold laguerreApprox vandermondeDelta
  fun_prop

theorem measurable_laguerreTarget (m : ℕ) (a c : ℂ) :
    Measurable (laguerreTarget (n := n) m a c) := by
  refine ((measurable_initProd m).mul ?_).indicator measurableSet_Ici
  unfold laguerreF vandermondeDelta
  fun_prop

theorem tendsto_one_sub_div_pow (x : ℝ) :
    Tendsto (fun N : ℕ => (((1 - x / N : ℝ)) : ℂ) ^ N) atTop (𝓝 (Complex.exp (-(x : ℂ)))) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp (Real.tendsto_one_add_div_pow_exp (-x))
  simpa [Function.comp_def, Complex.ofReal_exp, sub_eq_add_neg, neg_div] using h

theorem tendsto_laguerreApprox (a c : ℂ) (s : Fin n → ℝ) :
    Tendsto (fun N => laguerreApprox N a c s) atTop (𝓝 (laguerreF a c s)) :=
  (tendsto_finsetProd _ fun k _ =>
    tendsto_const_nhds.mul (tendsto_one_sub_div_pow (s k))).mul_const _

theorem tendsto_laguerreBox (m : ℕ) (a c : ℂ) (s : Fin n → ℝ) :
    Tendsto (fun N => laguerreBox N m a c s) atTop (𝓝 (laguerreTarget m a c s)) := by
  by_cases hs : s ∈ Set.Ici (0 : Fin n → ℝ)
  · rw [laguerreTarget, Set.indicator_of_mem hs]
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (∑ i, s i)
    refine ((tendsto_laguerreApprox a c s).const_mul (initProd m s)).congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hbox : s ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ)) :=
      ⟨hs, fun i => (single_le_sum (fun j _ => hs j) (mem_univ i)).trans
        (hN₀.trans (Nat.cast_le.mpr hN))⟩
    rw [laguerreBox, Set.indicator_of_mem hbox]
  · rw [laguerreTarget, Set.indicator_of_notMem hs]
    refine tendsto_const_nhds.congr fun N => ?_
    rw [laguerreBox, Set.indicator_of_notMem fun h => hs h.1]

theorem norm_laguerreApprox_le {N : ℕ} (a c : ℂ) {s : Fin n → ℝ}
    (hs : s ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))) :
    ‖laguerreApprox N a c s‖ ≤ ‖laguerreF a c s‖ := by
  unfold laguerreApprox laguerreF
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  refine mul_le_mul_of_nonneg_right
    (prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_) (norm_nonneg _)
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h0 : 0 ≤ 1 - s k / N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [sub_nonneg, div_le_one (by exact_mod_cast hN)]; exact hs.2 k
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_exp]
  simpa using Real.one_sub_div_pow_le_exp_neg (hs.2 k)

theorem norm_laguerreF_re {a c : ℂ} {s : Fin n → ℝ} (hs : ∀ i, 0 < s i)
    (hΔ : vandermondeDelta s ≠ 0) :
    ‖laguerreF a c s‖ = ‖laguerreF (a.re : ℂ) (c.re : ℂ) s‖ := by
  simp only [laguerreF, norm_mul, norm_prod]
  congr 1
  · refine prod_congr rfl fun k _ => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hs k), Complex.norm_cpow_eq_rpow_re_of_pos (hs k)]
    simp
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hΔ),
      Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hΔ)]
    simp

/-- The approximants are dominated by the limit integrand (with real parts of `a`, `c`). -/
theorem norm_laguerreBox_le (N m : ℕ) (a c : ℂ) :
    ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)),
      ‖laguerreBox N m a c s‖ ≤ ‖laguerreTarget m (a.re : ℂ) (c.re : ℂ) s‖ := by
  filter_upwards [ae_interior, ae_vandermondeDelta_ne_zero] with s hi hΔ
  by_cases hs : s ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))
  · rw [laguerreBox, Set.indicator_of_mem hs, laguerreTarget, Set.indicator_of_mem hs.1,
      norm_mul, norm_mul,
      ← norm_laguerreF_re (fun i => lt_of_le_of_ne (hs.1 i) (hi i).1.symm) hΔ]
    exact mul_le_mul_of_nonneg_left (norm_laguerreApprox_le a c hs) (norm_nonneg _)
  · rw [laguerreBox, Set.indicator_of_notMem hs, norm_zero]
    exact norm_nonneg _

open scoped ComplexOrder in
theorem laguerreBox_nonneg (N m : ℕ) (a c : ℝ) (s : Fin n → ℝ) :
    0 ≤ laguerreBox N m (a : ℂ) (c : ℂ) s := by
  by_cases hs : s ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => (N : ℝ))
  · rw [laguerreBox, Set.indicator_of_mem hs]
    have h0 : ∀ k, 0 ≤ 1 - s k / N := fun k => by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · rw [sub_nonneg, div_le_one (by exact_mod_cast hN)]; exact hs.2 k
    refine mul_nonneg (prod_nonneg fun i _ => Complex.zero_le_real.mpr (hs.1 i))
      (mul_nonneg (prod_nonneg fun k _ => mul_nonneg ?_ ?_) ?_)
    · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow (hs.1 k)]
      exact Complex.zero_le_real.mpr (Real.rpow_nonneg (hs.1 k) _)
    · rw [← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (pow_nonneg (h0 k) _)
    · rw [show (2 * (c : ℂ)) = ((2 * c : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (abs_nonneg _)]
      exact Complex.zero_le_real.mpr (Real.rpow_nonneg (abs_nonneg _) _)
  · rw [laguerreBox, Set.indicator_of_notMem hs]

theorem pairCount_cast (n : ℕ) : (pairCount n : ℂ) * 2 = n * ((n : ℂ) - 1) := by
  cases n with
  | zero => simp [pairCount]
  | succ k =>
    have h : ((2 * pairCount (k + 1) : ℕ) : ℂ) = (((k + 1) * k : ℕ) : ℂ) := by
      rw [two_mul_pairCount]; simp
    push_cast at h ⊢
    linear_combination h

/-- For large `N`, 5.14.4 evaluates the box integrals. -/
theorem eventually_laguerreBox {m : ℕ} (hm : m ≤ n) {a c : ℂ} (ha : 0 < a.re)
    (hc1 : -1 < (n : ℝ) * c.re) (hca : -a.re < ((n - 1 : ℕ) : ℝ) * c.re) :
    ∀ᶠ N : ℕ in atTop, Integrable (laguerreBox (n := n) N m a c) ∧
      ∫ s, laguerreBox (n := n) N m a c s =
        (N : ℂ) ^ ((m : ℂ) + n * (a + (n - 1) * c)) * selbergRHS n m a ((N : ℂ) + 1) c := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-(((n - 1 : ℕ) : ℝ) * c.re))
  filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
  have hN0 : 0 < N := by omega
  have hNr : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hb : 0 < ((N : ℂ) + 1).re := by simp; positivity
  have hcb : -((N : ℂ) + 1).re < ((n - 1 : ℕ) : ℝ) * c.re := by simp; linarith
  have hdom : c ∈ selbergDomain n a ((N : ℂ) + 1) := ⟨hc1, hca, hcb⟩
  refine ⟨integrable_box hN0 m a c (integrableOn_initProd_mul_full m ha hb hdom), ?_⟩
  rw [laguerreBox, integral_box_eq hN0 m a c, min_eq_right hm]
  have h := dlmf_5_14_4_full hm ha hb hc1 hca hcb
  rw [show (∫ t in Set.Icc (0 : Fin n → ℝ) 1, initProd m t * selbergF a ((N : ℂ) + 1) c t) =
    selbergRHS n m a ((N : ℂ) + 1) c from h]
  congr 2
  linear_combination c * pairCount_cast n

/-- **Convergence** of 5.14.5 for real parameters, by Fatou's lemma. -/
theorem integrable_laguerre_real {m : ℕ} (hm : m ≤ n) {a c : ℝ} (ha : 0 < a)
    (hc1 : -1 < (n : ℝ) * c) (hca : -a < ((n - 1 : ℕ) : ℝ) * c) :
    Integrable (laguerreTarget (n := n) m (a : ℂ) (c : ℂ)) := by
  have hev := eventually_laguerreBox (n := n) hm (a := (a : ℂ)) (c := (c : ℂ)) (by simpa)
    (by simpa) (by simpa)
  refine ⟨(measurable_laguerreTarget m _ _).aestronglyMeasurable, ?_⟩
  have hint : Tendsto (fun N => ∫⁻ s, ‖laguerreBox (n := n) N m (a : ℂ) (c : ℂ) s‖ₑ) atTop
      (𝓝 (ENNReal.ofReal (laguerreRHS n m (a : ℂ) (c : ℂ)).re)) := by
    have h1 := (ENNReal.continuous_ofReal.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp
        (tendsto_selbergRHS_scaled (n := n) m (a : ℂ) (c : ℂ)))
    refine h1.congr' ?_
    filter_upwards [hev] with N ⟨hi, hI⟩
    rw [Function.comp_apply, Function.comp_apply, ← hI,
      show (∫ s, laguerreBox (n := n) N m (a : ℂ) (c : ℂ) s).re =
        ∫ s, (laguerreBox (n := n) N m (a : ℂ) (c : ℂ) s).re from (integral_re hi).symm,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun s =>
      Complex.re_eq_norm.mpr (laguerreBox_nonneg N m a c s))
  calc ∫⁻ s, ‖laguerreTarget (n := n) m (a : ℂ) (c : ℂ) s‖ₑ
      = ∫⁻ s, liminf (fun N => ‖laguerreBox (n := n) N m (a : ℂ) (c : ℂ) s‖ₑ) atTop :=
        lintegral_congr fun s => ((tendsto_laguerreBox m _ _ s).enorm.liminf_eq).symm
    _ ≤ liminf (fun N => ∫⁻ s, ‖laguerreBox (n := n) N m (a : ℂ) (c : ℂ) s‖ₑ) atTop :=
        lintegral_liminf_le fun N => (measurable_laguerreBox N m _ _).enorm
    _ = _ := hint.liminf_eq
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **DLMF 5.14.5** (Laguerre form of Selberg's integral, with Aomoto's factor), on DLMF's full
range `ℜa > 0`, `ℜc > −min(1/n, ℜa/(n − 1))`, `0 ≤ m ≤ n`:
`∫_{[0,∞)ⁿ} t₁⋯tₘ ∏ tₖ^{a−1}e^{−tₖ} |Δ(t)|^{2c} dt =
∏_{k=1}^m (a+(n−k)c) ∏_{k=1}^n Γ(a+(n−k)c)Γ(1+kc)/Γ(1+c)`.
The range is stated without division: `n ℜc > −1`, `(n − 1) ℜc > −ℜa`. -/
theorem dlmf_5_14_5 {m : ℕ} (hm : m ≤ n) {a c : ℂ} (ha : 0 < a.re)
    (hc1 : -1 < (n : ℝ) * c.re) (hca : -a.re < ((n - 1 : ℕ) : ℝ) * c.re) :
    ∫ t in Set.Ici (0 : Fin n → ℝ),
      (∏ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < m), (t i : ℂ)) * laguerreF a c t =
        laguerreRHS n m a c := by
  have hbound := integrable_laguerre_real (n := n) hm ha hc1 hca
  have hdct : Tendsto (fun N => ∫ s, laguerreBox (n := n) N m a c s) atTop
      (𝓝 (∫ s, laguerreTarget m a c s)) :=
    tendsto_integral_of_dominated_convergence _
      (fun N => (measurable_laguerreBox N m a c).aestronglyMeasurable) hbound.norm
      (fun N => norm_laguerreBox_le N m a c) (ae_of_all _ fun s => tendsto_laguerreBox m a c s)
  have hval : Tendsto (fun N => ∫ s, laguerreBox (n := n) N m a c s) atTop
      (𝓝 (laguerreRHS n m a c)) :=
    (tendsto_selbergRHS_scaled m a c).congr' (by
      filter_upwards [eventually_laguerreBox hm ha hc1 hca] with N h using h.2.symm)
  rw [← integral_indicator measurableSet_Ici]
  exact tendsto_nhds_unique hdct hval

end Azurite.DLMF
