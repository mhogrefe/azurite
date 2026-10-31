/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section14HilbertDensity
import Azurite.DLMF.Chapter1.Section14TableSinImproper

/-!
# DLMF §1.15(v): Summability of Fourier integrals

https://dlmf.nist.gov/1.15.v

Abel–Poisson and Fejér summability of Fourier integrals (1.15.33–1.15.46), with the Fourier
transform `F = dlmfFourier f` of 1.14.1.

* Continuity of translation in `L¹` (`tendsto_integral_translate_sub`) and a general
  approximate-identity theorem (`tendsto_integral_kernel_conv_sub`): nonnegative bounded kernels
  of integral `1` whose tails vanish give `L¹` convergence. Dilated integrable kernels have
  vanishing tails (`tendsto_tail_dilate`).
* The half-plane Poisson kernel `P(x, y) = 2y/(x² + y²)` (`halfPlanePoisson`, 1.15.33–1.15.35),
  the Poisson mean `h(x, y)` in its Fourier form 1.15.36 (`poissonMean`), its kernel form 1.15.37,
  and `L¹` convergence 1.15.38.
* `Φ(z) = (i/π) ∫ f(t)/(z − t) dt` for real `f` (`fourierPhi`, 1.15.39): analytic in the upper
  half-plane with `Re Φ = h`. Its imaginary part is the conjugate Poisson integral (1.15.40).
* Fejér's kernel `K_R` (`fejerKernel`, 1.15.41–1.15.43, from `∫ (1 − cos s)/s² ds = π`), the Fejér
  mean `σ_R` (`fejerMean`, 1.15.44), its kernel form 1.15.45 and `L¹` convergence 1.15.46.

DLMF discrepancy: DLMF says the boundary value of `Im Φ` in 1.15.40 is the Hilbert transform
`ℋf(x)` of 1.14.41. Under DLMF's own definition 1.14.41–1.14.42 it is `−ℋf(x)`. The kernel in
1.15.40 is `(x − t)/((x − t)² + y²)`, while 1.14.42 uses `(t − x)/((t − x)² + y²)`. So
`dlmf_1_15_40_hilbert` proves `Im Φ(x + iy) → −ℋf(x)` at points of continuity of `f`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Continuity of translation in `L¹` -/

/-- For continuous compactly supported `g`, `∫ ‖g(x − s) − g(x)‖ dx → 0` as `s → 0`. -/
theorem tendsto_integral_translate_sub_of_cc {g : ℝ → ℂ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) :
    Tendsto (fun s => ∫ x, ‖g (x - s) - g x‖) (𝓝 0) (𝓝 0) := by
  obtain ⟨M, hM, hMs⟩ := exists_support_bound hgs
  obtain ⟨G, hG⟩ := hgc.bounded_above_of_compact_support hgs
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 (0 : ℝ))
    (F := fun s x => ‖g (x - s) - g x‖) (f := fun _ => (0 : ℝ))
    ((Icc (-(M + 1)) (M + 1)).indicator fun _ => 2 * G) ?_ ?_ ?_ ?_
  · rwa [integral_zero] at key
  · exact Eventually.of_forall fun s =>
      ((hgc.comp (continuous_sub_right s)).sub hgc).norm.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
    refine ae_of_all _ fun x => ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    by_cases hx : x ∈ Icc (-(M + 1)) (M + 1)
    · rw [indicator_of_mem hx]
      linarith [norm_sub_le (g (x - s)) (g x), hG (x - s), hG x]
    · rw [indicator_of_notMem hx]
      have hx' : M + 1 < |x| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact hx
      have h1 : M < |x - s| := by linarith [abs_sub_abs_le_abs_sub x s]
      rw [hMs _ h1, hMs x (by linarith), sub_zero, norm_zero]
  · exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  · refine ae_of_all _ fun x => ?_
    have h : Tendsto (fun s => g (x - s) - g x) (𝓝 0) (𝓝 (g (x - 0) - g x)) :=
      ((hgc.comp (continuous_const.sub continuous_id)).tendsto 0).sub_const _
    rw [sub_zero, sub_self] at h
    simpa using h.norm

/-- **Continuity of translation in `L¹`**: `∫ ‖f(x − s) − f(x)‖ dx → 0` as `s → 0`. -/
theorem tendsto_integral_translate_sub {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun s => ∫ x, ‖f (x - s) - f x‖) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hgs, hfg, hgc, hg⟩ := hf.exists_hasCompactSupport_integral_sub_le
    (show 0 < ε / 4 by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (tendsto_integral_translate_sub_of_cc hgc hgs) (ε / 4)
    (by positivity)] with s hs
  rw [Real.dist_eq, sub_zero, abs_lt] at hs ⊢
  have hfg' : Integrable fun x => ‖f x - g x‖ := (hf.sub hg).norm
  have hA : Integrable fun x => ‖f (x - s) - g (x - s)‖ := hfg'.comp_sub_right s
  have hB : Integrable fun x => ‖g (x - s) - g x‖ := ((hg.comp_sub_right s).sub hg).norm
  have hAB : Integrable fun x => ‖f (x - s) - g (x - s)‖ + ‖g (x - s) - g x‖ := hA.add hB
  have h1 : ∫ x, ‖f (x - s) - f x‖ ≤
      ∫ x, (‖f (x - s) - g (x - s)‖ + ‖g (x - s) - g x‖ + ‖f x - g x‖) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      (hAB.add hfg') (ae_of_all _ fun x => ?_)
    calc ‖f (x - s) - f x‖
        = ‖(f (x - s) - g (x - s)) + (g (x - s) - g x) - (f x - g x)‖ := by congr 1; ring
      _ ≤ ‖(f (x - s) - g (x - s)) + (g (x - s) - g x)‖ + ‖f x - g x‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
  rw [integral_add hAB hfg', integral_add hA hB,
    integral_sub_right_eq_self (fun x => ‖f x - g x‖) s] at h1
  constructor
  · have h0 : 0 ≤ ∫ x, ‖f (x - s) - f x‖ := integral_nonneg fun x => norm_nonneg _
    linarith
  · linarith

theorem integral_translate_sub_le {f : ℝ → ℂ} (hf : Integrable f) (s : ℝ) :
    ∫ x, ‖f (x - s) - f x‖ ≤ 2 * ∫ x, ‖f x‖ := by
  have h1 : ∫ x, ‖f (x - s) - f x‖ ≤ ∫ x, (‖f (x - s)‖ + ‖f x‖) :=
    integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      ((hf.comp_sub_right s).norm.add hf.norm) (ae_of_all _ fun x => norm_sub_le _ _)
  rw [integral_add (hf.comp_sub_right s).norm hf.norm,
    integral_sub_right_eq_self (fun x => ‖f x‖) s] at h1
  linarith

/-! ### Approximate identities in `L¹` -/

section Kernel

variable {k : ℝ → ℝ} {C : ℝ} {f : ℝ → ℂ}

/-- `(∫ k(x − t) f(t) dt) − f(x) = ∫ k(s) (f(x − s) − f(x)) ds` when `∫ k = 1`. -/
theorem kernel_conv_sub_eq (hkm : Measurable k) (hkC : ∀ s, |k s| ≤ C) (hki : Integrable k)
    (hk1 : ∫ s, k s = 1) (hf : Integrable f) (x : ℝ) :
    (∫ t, (k (x - t) : ℂ) * f t) - f x = ∫ s, (k s : ℂ) * (f (x - s) - f x) := by
  have h1 : ∫ t, (k (x - t) : ℂ) * f t = ∫ s, (k s : ℂ) * f (x - s) := by
    rw [← integral_sub_left_eq_self (fun t => (k (x - t) : ℂ) * f t) volume x]
    simp only [sub_sub_cancel]
  have hi : Integrable fun s => (k s : ℂ) * f (x - s) :=
    (hf.comp_sub_left x).bdd_mul (c := C)
      (Complex.measurable_ofReal.comp hkm).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hkC s)
  have hk : Integrable fun s => (k s : ℂ) := hki.ofReal
  simp_rw [mul_sub]
  rw [h1, integral_sub hi (hk.mul_const _), integral_mul_const, integral_complex_ofReal, hk1,
    ofReal_one, one_mul]

/-- The integrand `k(s) ‖f(x − s) − f(x)‖` is integrable on `ℝ × ℝ` (variables `(s, x)`). -/
theorem integrable_kernel_translate (hkm : Measurable k) (hk0 : ∀ s, 0 ≤ k s)
    (hki : Integrable k) (hfm : StronglyMeasurable f) (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ => k p.1 * ‖f (p.2 - p.1) - f p.2‖) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => k p.1 * ‖f (p.2 - p.1) - f p.2‖)
      (volume.prod volume) :=
    ((hkm.comp measurable_fst).mul ((hfm.comp_measurable (measurable_snd.sub measurable_fst)).sub
      (hfm.comp_measurable measurable_snd)).norm.measurable).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨ae_of_all _ fun s => ((hf.comp_sub_right s).sub hf).norm.const_mul (k s), ?_⟩
  refine (hki.mul_const (2 * ∫ x, ‖f x‖)).mono' hm.norm.integral_prod_right'
    (ae_of_all _ fun s => ?_)
  simp only [norm_mul, norm_norm, Real.norm_of_nonneg (hk0 s)]
  rw [integral_const_mul, Real.norm_of_nonneg
    (mul_nonneg (hk0 s) (integral_nonneg fun _ => norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (integral_translate_sub_le hf s) (hk0 s)

/-- The basic `L¹` estimate for a kernel `k ≥ 0` with `∫ k = 1`:
`∫ ‖k ∗ f − f‖ ≤ ∫ k(s) ‖f(· − s) − f‖₁ ds`, and `k ∗ f − f` is integrable. -/
theorem integral_kernel_conv_sub_le (hkm : Measurable k) (hk0 : ∀ s, 0 ≤ k s)
    (hkC : ∀ s, k s ≤ C) (hki : Integrable k) (hk1 : ∫ s, k s = 1) (hfm : StronglyMeasurable f)
    (hf : Integrable f) :
    (∫ x, ‖(∫ t, (k (x - t) : ℂ) * f t) - f x‖) ≤ ∫ s, k s * ∫ x, ‖f (x - s) - f x‖ ∧
      Integrable fun x => (∫ t, (k (x - t) : ℂ) * f t) - f x := by
  have hC : ∀ s, |k s| ≤ C := fun s => by rw [abs_of_nonneg (hk0 s)]; exact hkC s
  have hF := integrable_kernel_translate hkm hk0 hki hfm hf
  have hB : Integrable fun x => ∫ s, k s * ‖f (x - s) - f x‖ := hF.integral_prod_right
  have hpt : ∀ x, ‖(∫ t, (k (x - t) : ℂ) * f t) - f x‖ ≤ ∫ s, k s * ‖f (x - s) - f x‖ :=
    fun x => by
      rw [kernel_conv_sub_eq hkm hC hki hk1 hf x]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (ae_of_all _ fun s => ?_)))
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk0 s)]
  refine ⟨?_, ?_⟩
  · refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hB
      (ae_of_all _ hpt)).trans (le_of_eq ?_)
    rw [← integral_integral_swap (f := fun s x => k s * ‖f (x - s) - f x‖) hF]
    simp_rw [integral_const_mul]
  · have hm : AEStronglyMeasurable (fun x => ∫ s, (k s : ℂ) * (f (x - s) - f x)) volume := by
      refine AEStronglyMeasurable.integral_prod_right' (f := fun p : ℝ × ℝ =>
        (k p.2 : ℂ) * (f (p.1 - p.2) - f p.1)) ?_
      exact ((Complex.measurable_ofReal.comp (hkm.comp measurable_snd)).stronglyMeasurable.mul
        ((hfm.comp_measurable (measurable_fst.sub measurable_snd)).sub
          (hfm.comp_measurable measurable_fst))).aestronglyMeasurable
    refine hB.mono' (hm.congr (ae_of_all _ fun x => (kernel_conv_sub_eq hkm hC hki hk1 hf x).symm))
      (ae_of_all _ hpt)

end Kernel

/-- **Approximate identity in `L¹`**: for kernels `K_i ≥ 0`, bounded, with `∫ K_i = 1` and
`∫_{|s| ≥ δ} K_i → 0`, `∫ ‖K_i ∗ f − f‖ → 0` for every integrable `f`. -/
theorem tendsto_integral_kernel_conv_sub {ι : Type*} {l : Filter ι} {K : ι → ℝ → ℝ}
    (hK : ∀ᶠ i in l, Measurable (K i) ∧ (∀ s, 0 ≤ K i s) ∧ (∃ C, ∀ s, K i s ≤ C) ∧
      Integrable (K i) ∧ ∫ s, K i s = 1)
    (htail : ∀ δ, 0 < δ → Tendsto (fun i => ∫ s in {s | δ ≤ |s|}, K i s) l (𝓝 0))
    {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun i => ∫ x, ‖(∫ t, (K i (x - t) : ℂ) * f t) - f x‖) l (𝓝 0) := by
  set f' := hf.1.mk f
  have hfm : StronglyMeasurable f' := hf.1.stronglyMeasurable_mk
  have hff' : f =ᵐ[volume] f' := hf.1.ae_eq_mk
  have hf' : Integrable f' := hf.congr hff'
  have e : ∀ i, ∫ x, ‖(∫ t, (K i (x - t) : ℂ) * f t) - f x‖ =
      ∫ x, ‖(∫ t, (K i (x - t) : ℂ) * f' t) - f' x‖ := fun i => by
    refine integral_congr_ae ?_
    filter_upwards [hff'] with x hx
    rw [hx, integral_congr_ae (g := fun t => (K i (x - t) : ℂ) * f' t)
      (hff'.mono fun t ht => by simp only [ht])]
  simp_rw [e]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set N := ∫ x, ‖f' x‖
  obtain ⟨δ, hδ, hω⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp (tendsto_integral_translate_sub hf') (ε / 3) (by positivity))
  have hT : Tendsto (fun i => 2 * N * ∫ s in {s | δ ≤ |s|}, K i s) l (𝓝 (2 * N * 0)) :=
    (htail δ hδ).const_mul _
  rw [mul_zero] at hT
  have hS : MeasurableSet {s : ℝ | δ ≤ |s|} := measurableSet_le measurable_const
    continuous_abs.measurable
  filter_upwards [hK, hT.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))] with i
    ⟨hm, h0, ⟨C, hC⟩, hi, h1⟩ hTi
  obtain ⟨hle, -⟩ := integral_kernel_conv_sub_le hm h0 hC hi h1 hfm hf'
  have hN : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have h2 : ∫ s, K i s * ∫ x, ‖f' (x - s) - f' x‖ ≤
      ∫ s, (ε / 3 * K i s + 2 * N * {s | δ ≤ |s|}.indicator (K i) s) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun s => mul_nonneg (h0 s)
      (integral_nonneg fun _ => norm_nonneg _)) ((hi.const_mul _).add
      ((hi.indicator hS).const_mul _)) (ae_of_all _ fun s => ?_)
    have hb := integral_translate_sub_le hf' s
    by_cases hs : δ ≤ |s|
    · simp only [indicator, Set.mem_ofPred_eq, hs, ite_true]
      nlinarith [h0 s]
    · simp only [indicator, Set.mem_ofPred_eq, hs, ite_false, mul_zero, add_zero]
      have := hω (show dist s 0 < δ by rw [Real.dist_eq, sub_zero]; exact lt_of_not_ge hs)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
      nlinarith [h0 s]
  rw [integral_add (hi.const_mul _) ((hi.indicator hS).const_mul _), integral_const_mul,
    integral_const_mul, h1, integral_indicator hS] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  linarith

/-- Tails of a dilated kernel: `∫_{|s| ≥ δ} c k(c s) ds → 0` as `c → ∞`. -/
theorem tendsto_tail_dilate {k : ℝ → ℝ} (hk : Integrable k) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun c => ∫ s in {s | δ ≤ |s|}, c * k (c * s)) atTop (𝓝 0) := by
  have hS : ∀ a : ℝ, MeasurableSet {s : ℝ | a ≤ |s|} := fun a =>
    measurableSet_le measurable_const continuous_abs.measurable
  have e : ∀ᶠ c in atTop, ∫ u, {u | c * δ ≤ |u|}.indicator k u =
      ∫ s in {s | δ ≤ |s|}, c * k (c * s) := by
    filter_upwards [eventually_gt_atTop 0] with c hc
    rw [← integral_indicator (hS δ)]
    have : ({s | δ ≤ |s|}.indicator fun s => c * k (c * s)) =
        fun s => c * {u | c * δ ≤ |u|}.indicator k (c * s) := by
      funext s
      by_cases hs : δ ≤ |s|
      · have : c * δ ≤ |c * s| := by
          rw [abs_mul, abs_of_pos hc]; exact mul_le_mul_of_nonneg_left hs hc.le
        simp only [indicator, Set.mem_ofPred_eq, hs, this, ite_true]
      · have : ¬ c * δ ≤ |c * s| := by
          rw [abs_mul, abs_of_pos hc]; intro h; exact hs (le_of_mul_le_mul_left h hc)
        simp only [indicator, Set.mem_ofPred_eq, hs, this, ite_false, mul_zero]
    rw [this, integral_const_mul, Measure.integral_comp_mul_left, abs_inv, abs_of_pos hc,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  refine Tendsto.congr' e ?_
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun c u => {u | c * δ ≤ |u|}.indicator k u) (f := fun _ => (0 : ℝ)) (fun u => ‖k u‖)
    (Eventually.of_forall fun c => (hk.indicator (hS _)).aestronglyMeasurable)
    (Eventually.of_forall fun c => ae_of_all _ fun u => norm_indicator_le_norm_self _ _)
    hk.norm (ae_of_all _ fun u => ?_)
  · rwa [integral_zero] at key
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ((|u| + 1) / δ)] with c hc
    have : ¬ c * δ ≤ |u| := by rw [div_lt_iff₀ hδ] at hc; linarith
    simp [indicator, this]

/-! ### The Poisson kernel of the half-plane (1.15.33–1.15.38) -/

/-- DLMF 1.15.33: the Poisson kernel `P(x, y) = 2y/(x² + y²)` of the upper half-plane. -/
noncomputable def halfPlanePoisson (x y : ℝ) : ℝ := 2 * y / (x ^ 2 + y ^ 2)

theorem halfPlanePoisson_div (x y : ℝ) : halfPlanePoisson x y / (2 * π) = pK y x := by
  rw [halfPlanePoisson, pK, div_div, show (x ^ 2 + y ^ 2) * (2 * π) = 2 * (π * (x ^ 2 + y ^ 2))
    by ring, mul_div_mul_left _ _ two_ne_zero]

theorem pK_dilate {y : ℝ} (hy : 0 < y) (s : ℝ) : pK y s = y⁻¹ * pK 1 (y⁻¹ * s) := by
  have hπ := Real.pi_pos
  rw [pK, pK]
  field_simp

/-- DLMF 1.15.34: `(1/2π) ∫ P(x, y) dx = 1`. -/
theorem dlmf_1_15_34 {y : ℝ} (hy : 0 < y) : 1 / (2 * π) * ∫ x, halfPlanePoisson x y = 1 := by
  rw [one_div_mul_eq_div, ← integral_div]
  simp_rw [halfPlanePoisson_div]
  exact integral_pK hy

/-- DLMF 1.15.35: `∫_{|x| ≥ δ} P(x, y) dx → 0` as `y → 0+`. -/
theorem dlmf_1_15_35 {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y => ∫ x in {x | δ ≤ |x|}, halfPlanePoisson x y) (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_tail_dilate (integrable_pK one_pos) hδ).comp
    tendsto_inv_nhdsGT_zero).const_mul (2 * π)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  simp only [Function.comp]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_le measurable_const continuous_abs.measurable)
    fun x _ => ?_
  rw [← pK_dilate hy, ← halfPlanePoisson_div]
  field_simp

/-- DLMF 1.15.36: `h(x, y) = (2π)^{-1/2} ∫ e^{−y|t|} e^{−ixt} F(t) dt` with `F` the Fourier
transform of `f`. -/
noncomputable def poissonMean (f : ℝ → ℂ) (x y : ℝ) : ℂ :=
  ((√(2 * π) : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, cexp (-((y : ℂ) * |t|)) * cexp (-(I * x * t)) * dlmfFourier f t

theorem poissonMean_eq_poissonInt {f : ℝ → ℂ} (hf : Integrable f) {y : ℝ} (hy : 0 < y)
    (x : ℝ) : poissonMean f x y = poissonInt y f x := by
  rw [poissonInt_eq_dlmfFourier hf hy, poissonMean, dlmfFourier]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [show I * ((-x : ℝ) : ℂ) * t = -(I * x * t) by push_cast; ring]
  ring

/-- DLMF 1.15.37: `h(x, y) = (1/2π) ∫ f(t) P(x − t, y) dt`. -/
theorem dlmf_1_15_37 {f : ℝ → ℂ} (hf : Integrable f) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    poissonMean f x y = (2 * (π : ℂ))⁻¹ * ∫ t, f t * (halfPlanePoisson (x - t) y : ℂ) := by
  rw [poissonMean_eq_poissonInt hf hy, poissonInt]
  have e : ∫ t, f t * (halfPlanePoisson (x - t) y : ℂ) =
      ∫ t, 2 * ((((y / ((t - x) ^ 2 + y ^ 2)) : ℝ) : ℂ) * f t) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [halfPlanePoisson]
    rw [show (x - t) ^ 2 = (t - x) ^ 2 by ring]
    push_cast
    ring
  rw [e, integral_const_mul]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem poissonMean_eq_pK {f : ℝ → ℂ} (hf : Integrable f) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    poissonMean f x y = ∫ t, (pK y (x - t) : ℂ) * f t := by
  rw [poissonMean_eq_poissonInt hf hy, poissonInt_eq_pK]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [← pK_neg, neg_sub]

/-- DLMF 1.15.38: `h(·, y) → f` in `L¹` as `y → 0+`, for integrable `f`. -/
theorem dlmf_1_15_38 {f : ℝ → ℂ} (hf : Integrable f) :
    (∀ y, 0 < y → Integrable fun x => poissonMean f x y - f x) ∧
      Tendsto (fun y => ∫ x, ‖poissonMean f x y - f x‖) (𝓝[>] 0) (𝓝 0) := by
  have hK : ∀ y, 0 < y → Measurable (pK y) ∧ (∀ s, 0 ≤ pK y s) ∧ (∃ C, ∀ s, pK y s ≤ C) ∧
      Integrable (pK y) ∧ ∫ s, pK y s = 1 := fun y hy =>
    ⟨(continuous_pK hy).measurable, pK_nonneg hy, ⟨_, pK_le hy⟩, integrable_pK hy,
      integral_pK hy⟩
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨hm, h0, ⟨C, hC⟩, hi, h1⟩ := hK y hy
    have := (integral_kernel_conv_sub_le hm h0 hC hi h1 hf.1.stronglyMeasurable_mk
      (hf.congr hf.1.ae_eq_mk)).2
    refine this.congr ?_
    filter_upwards [hf.1.ae_eq_mk] with x hx
    rw [poissonMean_eq_pK hf hy, hx, integral_congr_ae (g := fun t => (pK y (x - t) : ℂ) * f t)
      (hf.1.ae_eq_mk.mono fun t ht => by simp only [ht])]
  have key := tendsto_integral_kernel_conv_sub (l := 𝓝[>] (0 : ℝ)) (K := pK)
    (eventually_mem_nhdsWithin.mono hK) (fun δ hδ => ?_) hf
  · refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    simp_rw [poissonMean_eq_pK hf hy]
  · refine ((tendsto_tail_dilate (integrable_pK one_pos) hδ).comp
      tendsto_inv_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    simp only [Function.comp]
    refine setIntegral_congr_fun (measurableSet_le measurable_const continuous_abs.measurable)
      fun x _ => (pK_dilate hy x).symm

/-! ### The analytic function `Φ` (1.15.39–1.15.40) -/

/-- DLMF 1.15.39: `Φ(z) = (i/π) ∫ f(t)/(z − t) dt` for real integrable `f`, `z = x + iy`. -/
noncomputable def fourierPhi (f : ℝ → ℝ) (z : ℂ) : ℂ := I / π * ∫ t, (f t : ℂ) / (z - t)

theorem fourierPhi_eq_cauchyExt (f : ℝ → ℝ) (z : ℂ) :
    fourierPhi f z = cauchyExt 0 (fun t => (f t : ℂ)) z := by
  simp [fourierPhi, cauchyExt]

/-- DLMF 1.15.39: `Φ` is analytic in the upper half-plane. -/
theorem dlmf_1_15_39_analytic {f : ℝ → ℝ} (hf : Integrable f) :
    DifferentiableOn ℂ (fourierPhi f) {z | 0 < z.im} := by
  have h := differentiableOn_cauchyExt (hf.ofReal (𝕜 := ℂ)) 0
  rw [neg_zero] at h
  exact h.congr fun z _ => fourierPhi_eq_cauchyExt f z

theorem fourierPhi_re_im {f : ℝ → ℝ} (hf : Integrable f) {x y : ℝ} (hy : 0 < y) :
    (fourierPhi f ⟨x, y⟩).re = π⁻¹ * ∫ t, f t * (y / ((x - t) ^ 2 + y ^ 2)) ∧
      (fourierPhi f ⟨x, y⟩).im = π⁻¹ * ∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) := by
  set z : ℂ := ⟨x, y⟩
  have hD : ∀ t : ℝ, 0 < (x - t) ^ 2 + y ^ 2 := fun t => by positivity
  have hpt : ∀ t : ℝ, (f t : ℂ) / (z - t) =
      ((f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) -
        I * ((f t * (y / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) := fun t => by
    have h0 := (hD t).ne'
    have h1 : (x - t) * (x - t) + y * y ≠ 0 := by rw [← sq, ← sq]; exact h0
    apply Complex.ext <;>
      simp only [z, Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, sub_zero, zero_mul, zero_div, add_zero, zero_sub, mul_zero,
        one_mul, ← sq] <;> ring
  have hA : Integrable fun t => f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) :=
    hf.mul_bdd (c := 1 / y) (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs]; exact abs_div_sq_add_sq_le hy)
  have hB : Integrable fun t => f t * (y / ((x - t) ^ 2 + y ^ 2)) :=
    hf.mul_bdd (c := 1 / y) (Measurable.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hy (hD t)), div_le_div_iff₀ (hD t) hy]
      nlinarith [sq_nonneg (x - t)])
  have hint : ∫ t, (f t : ℂ) / (z - t) =
      ((∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) -
        I * ((∫ t, f t * (y / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
    have hA' : Integrable fun t => ((f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) :=
      hA.ofReal
    have hB' : Integrable fun t => I * ((f t * (y / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) :=
      hB.ofReal.const_mul I
    simp_rw [hpt]
    rw [integral_sub hA' hB',
      integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  set a := ∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2))
  set b := ∫ t, f t * (y / ((x - t) ^ 2 + y ^ 2))
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : I / π * ((a : ℂ) - I * b) = ((π⁻¹ * b : ℝ) : ℂ) + ((π⁻¹ * a : ℝ) : ℂ) * I := by
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [fourierPhi, hint, e]
  simp

/-- DLMF 1.15.39: `Re Φ(x + iy) = h(x, y)` for real integrable `f` and `y > 0`. -/
theorem dlmf_1_15_39 {f : ℝ → ℝ} (hf : Integrable f) {x y : ℝ} (hy : 0 < y) :
    ((fourierPhi f ⟨x, y⟩).re : ℂ) = poissonMean (fun t => (f t : ℂ)) x y := by
  have hf' : Integrable fun t => (f t : ℂ) := hf.ofReal
  rw [(fourierPhi_re_im hf hy).1, dlmf_1_15_37 hf' hy]
  have e : ∫ t, (f t : ℂ) * (halfPlanePoisson (x - t) y : ℂ) =
      ((2 * ∫ t, f t * (y / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [halfPlanePoisson]
    push_cast
    ring
  rw [e]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  simp_rw [mul_comm (f _) y]

/-- DLMF 1.15.40: `Im Φ(x + iy) = (1/π) ∫ f(t) (x − t)/((x − t)² + y²) dt`, the conjugate Poisson
integral. -/
theorem dlmf_1_15_40 {f : ℝ → ℝ} (hf : Integrable f) {x y : ℝ} (hy : 0 < y) :
    (fourierPhi f ⟨x, y⟩).im = π⁻¹ * ∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) :=
  (fourierPhi_re_im hf hy).2

/-- DLMF 1.15.40, the boundary value of `Im Φ`, with the sign corrected. At a point of continuity
of `f`, `Im Φ(x + iy)` converges as `y → 0+` exactly when the Hilbert transform `ℋf(x)` of
1.14.41–1.14.42 exists, and then the limit is `−ℋf(x)`. DLMF calls the limit itself the Hilbert
transform, which is off by a sign under DLMF's own definition 1.14.41. -/
theorem dlmf_1_15_40_hilbert {f : ℝ → ℝ} (hf : Integrable f) {x : ℝ} (hc : ContinuousAt f x)
    (L : ℂ) : HasHilbert (fun t => (f t : ℂ)) x L ↔
      Tendsto (fun y => ((fourierPhi f ⟨x, y⟩).im : ℂ)) (𝓝[>] 0) (𝓝 (-L)) := by
  have hf' : Integrable fun t => (f t : ℂ) := hf.ofReal
  have hc' : ContinuousAt (fun t => (f t : ℂ)) x := Complex.continuous_ofReal.continuousAt.comp hc
  rw [dlmf_1_14_42 hf' hc' L]
  have e : ∀ᶠ y in 𝓝[>] (0 : ℝ), -((π : ℂ)⁻¹ *
      ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * (f t : ℂ)) =
        ((fourierPhi f ⟨x, y⟩).im : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [dlmf_1_15_40 hf hy]
    have : ∫ t, (((t - x) / ((t - x) ^ 2 + y ^ 2) : ℝ) : ℂ) * (f t : ℂ) =
        -((∫ t, f t * ((x - t) / ((x - t) ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only
      rw [show (t - x) ^ 2 = (x - t) ^ 2 by ring]
      push_cast
      ring
    rw [this]
    push_cast
    ring
  constructor
  · exact fun h => h.neg.congr' e
  · intro h
    have := (h.congr' (e.mono fun _ hy => hy.symm)).neg
    simpa using this

/-! ### Fejér's integral `∫ (1 − cos s)/s² ds = π` -/

theorem one_sub_cos_div_sq_nonneg (s : ℝ) : 0 ≤ (1 - Real.cos s) / s ^ 2 :=
  div_nonneg (by linarith [Real.cos_le_one s]) (sq_nonneg s)

theorem one_sub_cos_div_sq_le (s : ℝ) : (1 - Real.cos s) / s ^ 2 ≤ 4 * (1 + s ^ 2)⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have h1 : 1 - Real.cos s ≤ s ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have h2 : 1 - Real.cos s ≤ 2 := by linarith [Real.neg_one_le_cos s]
  have h3 : 0 ≤ 1 - Real.cos s := by linarith [Real.cos_le_one s]
  rw [div_le_iff₀ (by positivity), ← div_eq_mul_inv, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg s]

theorem integrable_one_sub_cos_div_sq : Integrable fun s : ℝ => (1 - Real.cos s) / s ^ 2 :=
  (integrable_inv_one_add_sq.const_mul 4).mono'
    ((by fun_prop : Measurable fun s : ℝ => (1 - Real.cos s) / s ^ 2).aestronglyMeasurable)
    (ae_of_all _ fun s => by
      rw [Real.norm_of_nonneg (one_sub_cos_div_sq_nonneg s)]; exact one_sub_cos_div_sq_le s)

theorem continuous_inv_mul_one_sub_cos : Continuous fun u : ℝ => u⁻¹ * (1 - Real.cos u) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · rw [ContinuousAt, inv_zero, zero_mul]
    refine squeeze_zero_norm (a := fun v : ℝ => |v| / 2) (fun v => ?_) ?_
    · rw [Real.norm_eq_abs]; exact abs_inv_mul_one_sub_cos_le v
    · have := ((continuous_abs.div_const 2).tendsto (0 : ℝ))
      simpa using this
  · exact (continuousAt_inv₀ hu).mul (by fun_prop)

theorem hasDerivAt_sinInt {x : ℝ} (hx : x ≠ 0) : HasDerivAt sinInt (Real.sin x / x) x :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_sin_div 0 x)
    ((by fun_prop : Measurable fun z : ℝ => Real.sin z / z).stronglyMeasurable
      |>.stronglyMeasurableAtFilter)
    ((Real.continuous_sin.continuousAt).div continuousAt_id hx)

theorem integral_one_sub_cos_div_sq_interval {R : ℝ} (hR : 0 ≤ R) :
    ∫ s in (0 : ℝ)..R, (1 - Real.cos s) / s ^ 2 = sinInt R - R⁻¹ * (1 - Real.cos R) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (f := fun s => sinInt s - s⁻¹ * (1 - Real.cos s))
    (f' := fun s => (1 - Real.cos s) / s ^ 2)
    ((continuous_sinInt.sub continuous_inv_mul_one_sub_cos).continuousOn)
    (fun x hx => by
      have hx0 : x ≠ 0 := hx.1.ne'
      have h1 := (hasDerivAt_sinInt hx0).sub ((hasDerivAt_inv hx0).mul
        ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_cos x)))
      convert h1 using 1
      simp only [Pi.sub_apply]
      field_simp
      ring)
    (integrable_one_sub_cos_div_sq.intervalIntegrable)
  rw [h]
  simp [sinInt]

theorem integral_Ioi_one_sub_cos_div_sq :
    ∫ s in Ioi (0 : ℝ), (1 - Real.cos s) / s ^ 2 = π / 2 := by
  have h1 := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    integrable_one_sub_cos_div_sq.integrableOn tendsto_id
  have h2 : Tendsto (fun R => sinInt R - R⁻¹ * (1 - Real.cos R)) atTop (𝓝 (π / 2 - 0)) := by
    refine tendsto_sinInt.sub (squeeze_zero_norm' (a := fun R => 2 * R⁻¹) ?_ ?_)
    · filter_upwards [eventually_gt_atTop 0] with R hR
      rw [norm_mul, norm_inv, Real.norm_of_nonneg hR.le, Real.norm_of_nonneg
        (by linarith [Real.cos_le_one R]), mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith [Real.neg_one_le_cos R]) (by positivity)
    · simpa using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  rw [sub_zero] at h2
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [eventually_ge_atTop 0] with R hR
  exact integral_one_sub_cos_div_sq_interval hR

/-- `∫ (1 − cos s)/s² ds = π` over the whole line. -/
theorem integral_one_sub_cos_div_sq : ∫ s, (1 - Real.cos s) / s ^ 2 = π := by
  have h := integral_comp_abs (f := fun s : ℝ => (1 - Real.cos s) / s ^ 2)
  simp only [Real.cos_abs, sq_abs] at h
  rw [h, integral_Ioi_one_sub_cos_div_sq]
  ring

/-! ### Fejér's kernel for Fourier integrals (1.15.41–1.15.43) -/

/-- DLMF 1.15.41: `K_R(s) = (1/(πR)) (1 − cos(Rs))/s²`. -/
noncomputable def fejerKernel (R s : ℝ) : ℝ := 1 / (π * R) * ((1 - Real.cos (R * s)) / s ^ 2)

theorem fejerKernel_nonneg {R : ℝ} (hR : 0 ≤ R) (s : ℝ) : 0 ≤ fejerKernel R s :=
  mul_nonneg (by positivity) (div_nonneg (by linarith [Real.cos_le_one (R * s)]) (sq_nonneg s))

theorem fejerKernel_neg (R s : ℝ) : fejerKernel R (-s) = fejerKernel R s := by
  simp [fejerKernel, mul_neg, Real.cos_neg]

theorem fejerKernel_dilate {R : ℝ} (hR : 0 < R) (s : ℝ) :
    fejerKernel R s = R * fejerKernel 1 (R * s) := by
  have hπ := Real.pi_pos
  rcases eq_or_ne s 0 with rfl | hs
  · simp [fejerKernel]
  simp only [fejerKernel, one_mul]
  field_simp

theorem fejerKernel_le {R : ℝ} (hR : 0 < R) (s : ℝ) : fejerKernel R s ≤ R / π := by
  have hπ := Real.pi_pos
  rcases eq_or_ne s 0 with rfl | hs
  · simp [fejerKernel]; positivity
  have h1 : 1 - Real.cos (R * s) ≤ (R * s) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := R * s)]
  have h2 : (1 - Real.cos (R * s)) / s ^ 2 ≤ R ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (R * s)]
  calc fejerKernel R s ≤ 1 / (π * R) * R ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = R / π := by field_simp

theorem measurable_fejerKernel (R : ℝ) : Measurable (fejerKernel R) := by
  unfold fejerKernel; fun_prop

theorem fejerKernel_one : fejerKernel 1 = fun s => 1 / π * ((1 - Real.cos s) / s ^ 2) := by
  funext s; simp [fejerKernel]

theorem integrable_fejerKernel_one : Integrable (fejerKernel 1) := by
  rw [fejerKernel_one]
  exact integrable_one_sub_cos_div_sq.const_mul _

theorem integrable_fejerKernel {R : ℝ} (hR : 0 < R) : Integrable (fejerKernel R) := by
  have := (integrable_fejerKernel_one.comp_mul_left' hR.ne').const_mul R
  exact this.congr (ae_of_all _ fun s => (fejerKernel_dilate hR s).symm)

/-- DLMF 1.15.42: `∫ K_R(s) ds = 1`. -/
theorem dlmf_1_15_42 {R : ℝ} (hR : 0 < R) : ∫ s, fejerKernel R s = 1 := by
  have h1 : ∫ s, fejerKernel 1 s = 1 := by
    rw [fejerKernel_one, integral_const_mul, integral_one_sub_cos_div_sq]
    field_simp
  simp_rw [fejerKernel_dilate hR]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fejerKernel 1) R, h1, abs_inv,
    abs_of_pos hR, smul_eq_mul, mul_one, mul_inv_cancel₀ hR.ne']

/-- DLMF 1.15.43: `∫_{|s| ≥ δ} K_R(s) ds → 0` as `R → ∞`. -/
theorem dlmf_1_15_43 {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R => ∫ s in {s | δ ≤ |s|}, fejerKernel R s) atTop (𝓝 0) := by
  refine (tendsto_tail_dilate integrable_fejerKernel_one hδ).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact setIntegral_congr_fun (measurableSet_le measurable_const continuous_abs.measurable)
    fun s _ => (fejerKernel_dilate hR s).symm

/-! ### Fejér means of Fourier integrals (1.15.44–1.15.46) -/

theorem integral_triangle_cos {R : ℝ} (hR : 0 < R) {w : ℝ} (hw : w ≠ 0) :
    ∫ t in (0 : ℝ)..R, (1 - t / R) * Real.cos (w * t) = (1 - Real.cos (w * R)) / (R * w ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => (1 - t / R) * Real.sin (w * t) / w - Real.cos (w * t) / (R * w ^ 2))
    (fun t _ => ?_) ((by fun_prop : Continuous fun t : ℝ =>
      (1 - t / R) * Real.cos (w * t)).intervalIntegrable _ _)]
  · simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, sub_zero, mul_zero]
    field_simp
    ring
  · have h := ((((hasDerivAt_id t).div_const R).const_sub 1).mul
      ((hasDerivAt_id t).const_mul w).sin).div_const w |>.sub
      (((hasDerivAt_id t).const_mul w).cos.div_const (R * w ^ 2))
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring

/-- `(1/2π) ∫_{−R}^{R} (1 − |t|/R) e^{iwt} dt = K_R(w)` for `w ≠ 0`. -/
theorem integral_triangle_cexp {R : ℝ} (hR : 0 < R) {w : ℝ} (hw : w ≠ 0) :
    ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * cexp (I * w * t) =
      ((2 * π * fejerKernel R w : ℝ) : ℂ) := by
  set g : ℝ → ℂ := fun t => ((1 - |t| / R : ℝ) : ℂ) * cexp (I * w * t) with hgdef
  have hg : Continuous g := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  have h1 : ∫ t in -R..0, g t = ∫ t in (0 : ℝ)..R, g (-t) := by
    rw [intervalIntegral.integral_comp_neg, neg_zero]
  have hgi : IntervalIntegrable (fun t => g (-t)) volume 0 R :=
    (hg.comp continuous_neg).intervalIntegrable _ _
  rw [h1, ← intervalIntegral.integral_add hgi (hg.intervalIntegrable _ _)]
  have h2 : ∀ t ∈ uIcc (0 : ℝ) R, g (-t) + g t =
      ((2 * ((1 - t / R) * Real.cos (w * t)) : ℝ) : ℂ) := fun t ht => by
    rw [uIcc_of_le hR.le] at ht
    simp only [hgdef, abs_neg, abs_of_nonneg ht.1]
    have hc := Complex.two_cos ((w * t : ℝ) : ℂ)
    push_cast at hc ⊢
    rw [← mul_add, show I * w * -t = -(w * t) * I by ring, show I * w * t = w * t * I by ring,
      add_comm, ← hc]
    ring
  rw [intervalIntegral.integral_congr h2, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul, integral_triangle_cos hR hw]
  congr 1
  have hπ := Real.pi_pos
  rw [fejerKernel, mul_comm w R]
  field_simp

/-- DLMF 1.15.44: `σ_R(θ) = (2π)^{-1/2} ∫_{−R}^{R} (1 − |t|/R) e^{−iθt} F(t) dt`. -/
noncomputable def fejerMean (f : ℝ → ℂ) (R θ : ℝ) : ℂ :=
  ((√(2 * π) : ℝ) : ℂ)⁻¹ *
    ∫ t in -R..R, ((1 - |t| / R : ℝ) : ℂ) * cexp (-(I * θ * t)) * dlmfFourier f t

/-- DLMF 1.15.45: `σ_R(θ) = ∫ f(t) K_R(θ − t) dt`. -/
theorem dlmf_1_15_45 {f : ℝ → ℂ} (hf : Integrable f) {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    fejerMean f R θ = ∫ t, f t * (fejerKernel R (θ - t) : ℂ) := by
  set a : ℝ → ℂ := fun t => ((1 - |t| / R : ℝ) : ℂ)
  have ha : Continuous a := by fun_prop
  set F : ℝ → ℝ → ℂ := fun t u => a t * f u * cexp (I * (u - θ : ℝ) * t)
  have hF : Integrable (Function.uncurry F) ((volume.restrict (uIoc (-R) R)).prod volume) := by
    have hG := Integrable.mul_prod (μ := volume.restrict (uIoc (-R) R)) (ν := volume)
      ((ha.integrableOn_uIcc (a := -R) (b := R)).mono_set uIoc_subset_uIcc) hf
    have hc : Continuous fun p : ℝ × ℝ => cexp (I * (p.2 - θ : ℝ) * p.1) := by fun_prop
    refine hG.mono ?_ (ae_of_all _ fun p => ?_)
    · exact ((ha.comp continuous_fst).aestronglyMeasurable.mul hf.1.comp_snd).mul
        hc.aestronglyMeasurable
    · simp only [Function.uncurry, F, norm_mul]
      rw [show I * ((p.2 - θ : ℝ) : ℂ) * p.1 = ((((p.2 - θ) * p.1 : ℝ)) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsw := intervalIntegral_integral_swap hF
  have e1 : ∫ t in -R..R, a t * cexp (-(I * θ * t)) * dlmfFourier f t =
      ((√(2 * π) : ℝ) : ℂ)⁻¹ * ∫ t in -R..R, ∫ u, F t u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [dlmfFourier, F]
    rw [show a t * cexp (-(I * θ * t)) * (((√(2 * π) : ℝ) : ℂ)⁻¹ *
        ∫ u, f u * cexp (I * t * u)) = ((√(2 * π) : ℝ) : ℂ)⁻¹ *
          ∫ u, a t * cexp (-(I * θ * t)) * (f u * cexp (I * t * u)) by
      rw [integral_const_mul]; ring]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    rw [show I * ((u - θ : ℝ) : ℂ) * t = I * t * u + -(I * θ * t) by push_cast; ring,
      Complex.exp_add]
    ring
  have e2 : ∀ᵐ u ∂volume, ∫ t in -R..R, F t u =
      f u * ((2 * π * fejerKernel R (θ - u) : ℝ) : ℂ) := by
    filter_upwards [(Set.countable_singleton θ).ae_notMem volume] with u hu
    have hne : u - θ ≠ 0 := sub_ne_zero.mpr fun h => hu (by rw [h]; rfl)
    simp only [F]
    rw [show (fun t => a t * f u * cexp (I * ((u - θ : ℝ) : ℂ) * t)) =
      fun t => f u * (a t * cexp (I * ((u - θ : ℝ) : ℂ) * t)) by funext t; ring,
      intervalIntegral.integral_const_mul, integral_triangle_cexp hR hne, ← neg_sub,
      fejerKernel_neg]
  rw [fejerMean, e1, hsw, integral_congr_ae e2]
  have hs : ((√(2 * π) : ℝ) : ℂ)⁻¹ * ((√(2 * π) : ℝ) : ℂ)⁻¹ = ((2 * π : ℝ) : ℂ)⁻¹ := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  rw [← mul_assoc, hs, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  push_cast at hπ ⊢
  field_simp

theorem fejerMean_eq {f : ℝ → ℂ} (hf : Integrable f) {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    fejerMean f R θ = ∫ t, (fejerKernel R (θ - t) : ℂ) * f t := by
  rw [dlmf_1_15_45 hf hR]
  simp_rw [mul_comm (f _)]

/-- DLMF 1.15.46: `σ_R → f` in `L¹` as `R → ∞`, for integrable `f`. -/
theorem dlmf_1_15_46 {f : ℝ → ℂ} (hf : Integrable f) :
    (∀ R, 0 < R → Integrable fun θ => fejerMean f R θ - f θ) ∧
      Tendsto (fun R => ∫ θ, ‖fejerMean f R θ - f θ‖) atTop (𝓝 0) := by
  have hK : ∀ R, 0 < R → Measurable (fejerKernel R) ∧ (∀ s, 0 ≤ fejerKernel R s) ∧
      (∃ C, ∀ s, fejerKernel R s ≤ C) ∧ Integrable (fejerKernel R) ∧
        ∫ s, fejerKernel R s = 1 := fun R hR =>
    ⟨measurable_fejerKernel R, fejerKernel_nonneg hR.le, ⟨_, fejerKernel_le hR⟩,
      integrable_fejerKernel hR, dlmf_1_15_42 hR⟩
  refine ⟨fun R hR => ?_, ?_⟩
  · obtain ⟨hm, h0, ⟨C, hC⟩, hi, h1⟩ := hK R hR
    have := (integral_kernel_conv_sub_le hm h0 hC hi h1 hf.1.stronglyMeasurable_mk
      (hf.congr hf.1.ae_eq_mk)).2
    refine this.congr ?_
    filter_upwards [hf.1.ae_eq_mk] with x hx
    rw [fejerMean_eq hf hR, hx, integral_congr_ae
      (g := fun t => (fejerKernel R (x - t) : ℂ) * f t)
      (hf.1.ae_eq_mk.mono fun t ht => by simp only [ht])]
  have key := tendsto_integral_kernel_conv_sub (l := atTop) (K := fejerKernel)
    ((eventually_gt_atTop 0).mono hK) (fun δ hδ => dlmf_1_15_43 hδ) hf
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  simp_rw [fejerMean_eq hf hR]

end Azurite.DLMF
