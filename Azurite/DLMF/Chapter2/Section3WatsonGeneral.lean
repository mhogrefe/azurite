/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Watson
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# DLMF §2.3(ii): Watson's lemma for general kernels (2.3.10–2.3.12)

* `dlmf_2_3_12`: `∫₀^∞ f(xt) q(t) dt ∼ ∑ 𝓜f(αₛ) aₛ x^{−αₛ}` under 2.3.7, 2.3.10 and 2.3.11, with
  Mathlib's `mellin` (`mellin_ofReal_eq` for real arguments). The part `(0, b]` is
  `watson_near_zero`; on `(b, ∞)` the integrand is `O(e^{−cb^κx^κ})`, which is
  `O(x^{−αₙ})` (`eventually_exp_neg_mul_rpow_le_rpow_neg`).
-/

open Set Filter Topology Asymptotics Complex MeasureTheory

namespace Azurite.DLMF

theorem mellin_ofReal_eq {f : ℝ → ℂ} (α : ℝ) :
    mellin f (α : ℂ) = ∫ u in Ioi 0, ((u ^ (α - 1) : ℝ) : ℂ) * f u := by
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  simp only [smul_eq_mul]
  rw [ofReal_cpow (le_of_lt hu)]
  push_cast
  rfl

theorem eventually_exp_neg_mul_rpow_le_rpow_neg (α : ℝ) {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(γ * x ^ κ)) ≤ x ^ (-α) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (α / κ) γ hγ).comp
    (tendsto_rpow_atTop hκ)
  filter_upwards [h.eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop 0] with x hx hx0
  simp only [Function.comp_apply] at hx
  rw [← Real.rpow_mul hx0.le, show κ * (α / κ) = α by field_simp, neg_mul] at hx
  have hp : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  rw [Real.rpow_neg hx0.le, le_inv_comm₀ (Real.exp_pos _) hp, ← one_div,
    le_div_iff₀ (Real.exp_pos _)]
  exact hx

/-- **DLMF 2.3.12**: if `q` satisfies 2.3.7 (`λ, μ > 0`) and, with constants `A, c, β, κ`
(DLMF's `A, a, b, κ`; only `c, κ > 0` is needed), `|f(t)| ≤ A e^{−ct^κ}` on `[0, ∞)` (2.3.10) and
`q(t) = O(e^{βt^κ})` as `t → +∞` (2.3.11), then
`∫₀^∞ f(xt) q(t) dt ∼ ∑ 𝓜f((s+λ)/μ) aₛ x^{−(s+λ)/μ}` as `x → +∞`, with Mathlib's Mellin
transform `mellin`. DLMF's piecewise continuity of `f` and `q` on `(0, ∞)` is replaced by the
weaker measurability of both and integrability of `q` on every `[c, R]`, `c > 0`. -/
theorem dlmf_2_3_12 {f q : ℝ → ℂ} {a : ℕ → ℂ} {lam μ A c β κ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (hc : 0 < c) (hκ : 0 < κ) (hf : Measurable f) (hq : Measurable q)
    (hfb : ∀ t, 0 ≤ t → ‖f t‖ ≤ A * Real.exp (-(c * t ^ κ)))
    (hqb : IsBigODLMF atTop q fun t => (Real.exp (β * t ^ κ) : ℂ))
    (hloc : ∀ c R, 0 < c → IntervalIntegrable q volume c R)
    (hexp : IsGenAsympExpansionDLMF (𝓝[>] 0)
      (fun s t => ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) q
      (fun s t => a s * ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ))) :
    IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))
      (fun x => ∫ t in Ioi 0, f (x * t) * q t)
      (fun s x => mellin f (watsonExp lam μ s : ℂ) * a s *
        ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ)) := by
  set α := watsonExp lam μ with hαdef
  have hαp := watsonExp_pos hlam hμ
  refine ⟨?_, fun n => ?_⟩
  · simpa only [mul_one] using isAsympScale_rpow_neg_mul (one_div_pos.mpr hμ)
      (watsonExp_succ hμ) (w := fun _ => (1 : ℂ)) (Eventually.of_forall fun _ => one_ne_zero)
  obtain ⟨b, C, hb, hb1, hr⟩ := watson_bound hμ hexp n
  have hA : 0 ≤ A := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
    ((norm_nonneg _).trans (hfb 0 le_rfl))
  -- the Mellin integrability
  have hfα : ∀ s, IntegrableOn (fun u : ℝ => u ^ (α s - 1) * ‖f u‖) (Ioi 0) := fun s => by
    have hg := (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [hαp s] : -1 < α s - 1)
      hκ hc).const_mul A
    refine Integrable.mono' hg ((measurable_id.pow_const _).mul
      hf.norm).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
    have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu0.le _)
      (norm_nonneg _)), neg_mul]
    calc u ^ (α s - 1) * ‖f u‖ ≤ u ^ (α s - 1) * (A * Real.exp (-(c * u ^ κ))) :=
          mul_le_mul_of_nonneg_left (hfb u hu0.le) (Real.rpow_nonneg hu0.le _)
      _ = _ := by ring
  -- growth of `q` at infinity
  obtain ⟨B, hB⟩ := hqb
  rw [eventually_map, eventually_atTop] at hB
  obtain ⟨T₀, hT₀⟩ := hB
  have hqT : ∀ t, T₀ ≤ t → ‖q t‖ ≤ B * Real.exp (β * t ^ κ) := fun t ht => by
    have h := hT₀ t ht
    rwa [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      div_le_iff₀ (Real.exp_pos _)] at h
  set T := max T₀ 1
  have hbT : b ≤ T := hb1.trans (le_max_right _ _)
  have hB0 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp
    ((norm_nonneg _).trans (hqT T (le_max_left _ _)))
  have hqI : IntegrableOn q (Ioc b T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hbT).mp (hloc b T hb)
  set Q := ∫ t in Ioc b T, ‖q t‖
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-(c * t ^ κ))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : (-1 : ℝ) < 0) hκ hc
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_zero, one_mul, neg_mul]
  set E := ∫ t in Ioi 0, Real.exp (-(c * t ^ κ))
  set γ := c * b ^ κ
  have hγ : 0 < γ := mul_pos hc (Real.rpow_pos_of_pos hb _)
  set K := (C + ∑ s ∈ Finset.range n, ‖a s‖ * b ^ (α s - α n)) *
    ∫ u in Ioi 0, u ^ (α n - 1) * ‖f u‖
  set K' := A * Q + A * B * Real.exp ((β + c) * b ^ κ) * E
  have hQ0 : 0 ≤ Q := setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _
  have hE0 : 0 ≤ E := setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le
  refine isBigODLMF_of_bound (K := K + K') ?_ ?_
  · filter_upwards [eventually_exp_neg_mul_rpow_le_rpow_neg (α n) hγ hκ,
      eventually_ge_atTop 1, (tendsto_rpow_atTop hκ).eventually_ge_atTop ((β + c) / c)]
      with x hex hx1 hxκ
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    have hcx : 0 ≤ c * x ^ κ - β - c := by
      have := (div_le_iff₀ hc).mp hxκ
      linarith
    obtain ⟨hi0, hN⟩ := watson_near_zero hb hx0 hf hq (fun s hs => watsonExp_mono hμ hs)
      (fun s _ => hfα s) hr
    -- pointwise bound on `f(xt)` for `t ≥ b`
    have hfx : ∀ t, b ≤ t → ‖f (x * t)‖ ≤ A * Real.exp (-(c * x ^ κ * t ^ κ)) := fun t ht => by
      have h := hfb (x * t) (mul_nonneg hx0.le (hb.le.trans ht))
      rwa [Real.mul_rpow hx0.le (hb.le.trans ht), ← mul_assoc] at h
    have hmono : ∀ t, b ≤ t → b ^ κ ≤ t ^ κ := fun t ht =>
      Real.rpow_le_rpow hb.le ht hκ.le
    have hxκ0 : 0 ≤ x ^ κ := Real.rpow_nonneg hx0.le _
    -- the piece on `(b, T]`
    have hb1' : ∀ t ∈ Ioc b T, ‖f (x * t) * q t‖ ≤ A * Real.exp (-(γ * x ^ κ)) * ‖q t‖ :=
      fun t ht => by
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ((hfx t ht.1.le).trans ?_) (norm_nonneg _)
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) hA
        calc γ * x ^ κ = c * x ^ κ * b ^ κ := by ring
          _ ≤ c * x ^ κ * t ^ κ :=
            mul_le_mul_of_nonneg_left (hmono t ht.1.le) (mul_nonneg hc.le hxκ0)
    have hgx : Measurable fun t => f (x * t) * q t :=
      (hf.comp (measurable_const_mul x)).mul hq
    have hI1 : IntegrableOn (fun t => f (x * t) * q t) (Ioc b T) :=
      Integrable.mono' (hqI.norm.const_mul _) hgx.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioc hb1')
    have hn1 : ‖∫ t in Ioc b T, f (x * t) * q t‖ ≤ A * Q * Real.exp (-(γ * x ^ κ)) := by
      calc _ ≤ ∫ t in Ioc b T, A * Real.exp (-(γ * x ^ κ)) * ‖q t‖ :=
            norm_integral_le_of_norm_le (hqI.norm.const_mul _)
              (ae_restrict_of_forall_mem measurableSet_Ioc hb1')
        _ = _ := by rw [integral_const_mul]; ring
    -- the piece on `(T, ∞)`
    have hb2 : ∀ t ∈ Ioi T, ‖f (x * t) * q t‖ ≤
        A * B * Real.exp ((β + c) * b ^ κ) * Real.exp (-(γ * x ^ κ)) *
          Real.exp (-(c * t ^ κ)) := fun t ht => by
      have ht' : T < t := ht
      have htb : b ≤ t := hbT.trans ht'.le
      rw [norm_mul]
      calc ‖f (x * t)‖ * ‖q t‖
          ≤ (A * Real.exp (-(c * x ^ κ * t ^ κ))) * (B * Real.exp (β * t ^ κ)) :=
            mul_le_mul (hfx t htb) (hqT t ((le_max_left _ _).trans ht'.le)) (norm_nonneg _)
              (mul_nonneg hA (Real.exp_pos _).le)
        _ = A * B * Real.exp (-(c * x ^ κ * t ^ κ) + β * t ^ κ) := by
            rw [Real.exp_add]; ring
        _ = A * B * Real.exp (-((c * x ^ κ - β - c) * t ^ κ) + -(c * t ^ κ)) := by
            rw [show -(c * x ^ κ * t ^ κ) + β * t ^ κ =
              -((c * x ^ κ - β - c) * t ^ κ) + -(c * t ^ κ) by ring]
        _ ≤ A * B * Real.exp (-((c * x ^ κ - β - c) * b ^ κ) + -(c * t ^ κ)) := by
            have := hmono t htb
            gcongr
        _ = _ := by
            rw [Real.exp_add, show -((c * x ^ κ - β - c) * b ^ κ) =
              (β + c) * b ^ κ + -(γ * x ^ κ) by ring, Real.exp_add]
            ring
    have hEi : IntegrableOn (fun t : ℝ => A * B * Real.exp ((β + c) * b ^ κ) *
        Real.exp (-(γ * x ^ κ)) * Real.exp (-(c * t ^ κ))) (Ioi T) :=
      (hE.mono_set (Ioi_subset_Ioi ((zero_lt_one.trans_le (le_max_right T₀ 1)).le))).const_mul _
    have hI2 : IntegrableOn (fun t => f (x * t) * q t) (Ioi T) :=
      Integrable.mono' hEi hgx.aestronglyMeasurable.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioi hb2)
    have hn2 : ‖∫ t in Ioi T, f (x * t) * q t‖ ≤
        A * B * Real.exp ((β + c) * b ^ κ) * E * Real.exp (-(γ * x ^ κ)) := by
      calc _ ≤ ∫ t in Ioi T, A * B * Real.exp ((β + c) * b ^ κ) *
            Real.exp (-(γ * x ^ κ)) * Real.exp (-(c * t ^ κ)) :=
            norm_integral_le_of_norm_le hEi (ae_restrict_of_forall_mem measurableSet_Ioi hb2)
        _ ≤ ∫ t in Ioi 0, A * B * Real.exp ((β + c) * b ^ κ) *
            Real.exp (-(γ * x ^ κ)) * Real.exp (-(c * t ^ κ)) :=
            setIntegral_mono_set (hE.const_mul _) (ae_restrict_of_forall_mem measurableSet_Ioi
              fun t _ => by positivity)
              (Ioi_subset_Ioi (zero_lt_one.trans_le (le_max_right T₀ 1)).le).eventuallyLE
        _ = _ := by rw [integral_const_mul]; ring
    -- assemble
    have hsplit : ∫ t in Ioi 0, f (x * t) * q t = (∫ t in Ioc 0 b, f (x * t) * q t) +
        ((∫ t in Ioc b T, f (x * t) * q t) + ∫ t in Ioi T, f (x * t) * q t) := by
      have hIb : IntegrableOn (fun t => f (x * t) * q t) (Ioi b) := by
        rw [← Ioc_union_Ioi_eq_Ioi hbT]; exact hI1.union hI2
      have d1 : Disjoint (Ioc (0 : ℝ) b) (Ioi b) :=
        disjoint_left.mpr fun t h1 h2 => not_lt.mpr h1.2 h2
      have d2 : Disjoint (Ioc b T) (Ioi T) :=
        disjoint_left.mpr fun t h1 h2 => not_lt.mpr h1.2 h2
      rw [← Ioc_union_Ioi_eq_Ioi hb.le, setIntegral_union d1 measurableSet_Ioi hi0 hIb,
        ← Ioc_union_Ioi_eq_Ioi hbT, setIntegral_union d2 measurableSet_Ioi hI1 hI2]
    have hsum : ∑ s ∈ Finset.range n, mellin f (α s : ℂ) * a s * ((x ^ (-α s) : ℝ) : ℂ) =
        ∑ s ∈ Finset.range n, a s * ((x ^ (-α s) : ℝ) : ℂ) *
          ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f u :=
      Finset.sum_congr rfl fun s _ => by rw [mellin_ofReal_eq]; ring
    have hφ : ‖((x ^ (-α n) : ℝ) : ℂ)‖ = x ^ (-α n) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    rw [hsplit, hsum, hφ]
    calc _ = ‖((∫ t in Ioc 0 b, f (x * t) * q t) - ∑ s ∈ Finset.range n,
          a s * ((x ^ (-α s) : ℝ) : ℂ) * ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f u) +
          ((∫ t in Ioc b T, f (x * t) * q t) + ∫ t in Ioi T, f (x * t) * q t)‖ := by
          ring_nf
      _ ≤ K * x ^ (-α n) + (A * Q * Real.exp (-(γ * x ^ κ)) +
          A * B * Real.exp ((β + c) * b ^ κ) * E * Real.exp (-(γ * x ^ κ))) :=
          (norm_add_le _ _).trans (add_le_add hN ((norm_add_le _ _).trans (add_le_add hn1 hn2)))
      _ = K * x ^ (-α n) + K' * Real.exp (-(γ * x ^ κ)) := by ring
      _ ≤ K * x ^ (-α n) + K' * x ^ (-α n) := by
          gcongr
      _ = _ := by ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'

end Azurite.DLMF
