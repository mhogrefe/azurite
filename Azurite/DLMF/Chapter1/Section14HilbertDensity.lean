/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertSemigroup

/-!
# DLMF 1.14.45: density of Poisson integrals in `L^p`

`P_b g → g` in `L^p` (`1 ≤ p < ∞`) for continuous compactly supported `g`
(`tendsto_eLpNorm_poissonInt_sub`), by dominated convergence with the majorant
`norm_poissonInt_sub_le_majorant`. With Mathlib's density of such `g`, every real `f ∈ L^p` is
an `L^p`-limit of Poisson integrals (`exists_poissonInt_approx`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real ENNReal

namespace Azurite.DLMF

/-- `|P_b g(x) − g(x)| ≤ (1/π) ∫ b/(b² + s²) |g(x + s) − g(x)| ds`. -/
theorem pK_le {b : ℝ} (hb : 0 < b) (s : ℝ) : pK b s ≤ 1 / (π * b) := by
  have hπ := Real.pi_pos
  rw [pK, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg s, mul_pos hπ hb, mul_nonneg (mul_pos hπ hb).le (sq_nonneg s)]

theorem norm_poissonInt_sub_le {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ‖poissonInt b g x - g x‖ ≤ π⁻¹ * ∫ s, b / (b ^ 2 + s ^ 2) * ‖g (x + s) - g x‖ := by
  have hpi : Integrable fun s => (pK b s : ℂ) := (integrable_pK hb).ofReal
  have hpg : Integrable fun s => (pK b s : ℂ) * g (x + s) :=
    (hg.comp_add_left x).bdd_mul (c := 1 / (π * b))
      (Complex.continuous_ofReal.comp (continuous_pK hb)).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hb _)]; exact pK_le hb s)
  have h1 : poissonInt b g x - g x = ∫ s, (pK b s : ℂ) * (g (x + s) - g x) := by
    rw [poissonInt_eq_pK, show (fun t => (pK b (t - x) : ℂ) * g t) =
      fun t => (fun s => (pK b s : ℂ) * g (x + s)) (t - x) from funext fun t => by
        simp only [add_sub_cancel],
      integral_sub_right_eq_self (fun s => (pK b s : ℂ) * g (x + s)) x]
    simp_rw [mul_sub]
    rw [integral_sub hpg (hpi.mul_const _), integral_mul_const, integral_complex_ofReal,
      integral_pK hb, ofReal_one, one_mul]
  rw [h1, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (ae_of_all _ fun s => ?_)))
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hb _), pK]
  field_simp
  ring

/-- A uniform majorant: for `0 < b ≤ 1`, `|P_b g(x) − g(x)| ≤ C/(1 + x²)` when `g` is bounded by
`G` and vanishes outside `[−M, M]`. -/
theorem norm_poissonInt_sub_le_majorant {g : ℝ → ℂ} (hg : Integrable g) {G M : ℝ}
    (hG : ∀ t, ‖g t‖ ≤ G)
    (hM : 0 ≤ M) (hgs : ∀ t : ℝ, M < |t| → g t = 0) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (x : ℝ) :
    ‖poissonInt b g x - g x‖ ≤ (2 * G * (2 + 4 * M ^ 2) + 8 * ∫ t, ‖g t‖) / (1 + x ^ 2) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hI0 : 0 ≤ ∫ t, ‖g t‖ := integral_nonneg fun _ => norm_nonneg _
  have hpi : Integrable fun t => pK b (t - x) := (integrable_pK hb).comp_sub_right x
  have hpint : ∫ t, pK b (t - x) = 1 := by
    rw [integral_sub_right_eq_self (pK b) x, integral_pK hb]
  by_cases hx : x ^ 2 ≤ 4 * M ^ 2 ∨ x ^ 2 ≤ 1
  · have hP : ‖poissonInt b g x‖ ≤ G := by
      rw [poissonInt_eq_pK]
      calc ‖∫ t, (pK b (t - x) : ℂ) * g t‖ ≤ ∫ t, pK b (t - x) * G :=
            norm_integral_le_of_norm_le (hpi.mul_const _) (ae_of_all _ fun t => by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hb _)]
              exact mul_le_mul_of_nonneg_left (hG t) (pK_nonneg hb _))
        _ = G := by rw [integral_mul_const, hpint, one_mul]
    have h1 : 1 + x ^ 2 ≤ 2 + 4 * M ^ 2 := by
      rcases hx with h | h <;> nlinarith [sq_nonneg M]
    rw [le_div_iff₀ (by positivity)]
    calc ‖poissonInt b g x - g x‖ * (1 + x ^ 2) ≤ (2 * G) * (2 + 4 * M ^ 2) := by
          refine mul_le_mul ((norm_sub_le _ _).trans (by linarith [hG x])) h1 (by positivity)
            (by positivity)
      _ ≤ _ := by linarith
  · push Not at hx
    obtain ⟨hx1, hx2⟩ := hx
    have habs : 2 * M < |x| := by
      rw [← sq_lt_sq₀ (by positivity) (abs_nonneg x), sq_abs]; nlinarith
    have hgx : g x = 0 := hgs x (by linarith)
    have hpt : ∀ t, ‖(pK b (t - x) : ℂ) * g t‖ ≤ 8 / (1 + x ^ 2) * ‖g t‖ := fun t => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hb _)]
      by_cases ht : M < |t|
      · rw [hgs t ht, norm_zero, mul_zero, mul_zero]
      · push Not at ht
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hd : |x| / 2 ≤ |t - x| := by
          have := abs_sub_abs_le_abs_sub x t
          rw [abs_sub_comm] at this
          linarith
        have hd2 : x ^ 2 / 4 ≤ (t - x) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) hd 2
          rw [div_pow, sq_abs, sq_abs] at this; linarith
        have hπ := Real.two_le_pi
        rw [pK, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg b, mul_le_mul_of_nonneg_left hd2 (by positivity : (0 : ℝ) ≤ 8 * π)]
    have hP : ‖poissonInt b g x‖ ≤ 8 / (1 + x ^ 2) * ∫ t, ‖g t‖ := by
      rw [poissonInt_eq_pK, ← integral_const_mul]
      exact norm_integral_le_of_norm_le (hg.norm.const_mul _) (ae_of_all _ hpt)
    rw [hgx, sub_zero]
    refine hP.trans ?_
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hG0 (sq_nonneg M)]) (by positivity)

theorem exists_support_bound {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    ∃ M, 0 ≤ M ∧ ∀ t : ℝ, M < |t| → g t = 0 := by
  obtain ⟨M, hM⟩ := hgs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max M 0, le_max_right _ _, fun t ht => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hM h
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_max_left M 0]

/-- `∫ |P_b g − g|^q → 0` as `b → 0+`, for continuous compactly supported `g` and `q ≥ 1`. -/
theorem tendsto_integral_poissonInt_sub {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {q : ℝ} (hq : 1 ≤ q) :
    Tendsto (fun b => ∫ x, ‖poissonInt b g x - g x‖ ^ q) (𝓝[>] 0) (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  obtain ⟨M, hM, hMs⟩ := exists_support_bound hgs
  obtain ⟨G, hG⟩ := hgc.bounded_above_of_compact_support hgs
  set C := 2 * G * (2 + 4 * M ^ 2) + 8 * ∫ t, ‖g t‖ with hC
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hC0 : 0 ≤ C := by
    have : 0 ≤ ∫ t, ‖g t‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  have hw : Integrable fun t => ‖g t‖ / (1 + t ^ 2) := by
    refine (hg.norm.mul_bdd (c := 1) (Continuous.inv₀ (by fun_prop : Continuous fun t : ℝ =>
      1 + t ^ 2) (fun t => by positivity)).aestronglyMeasurable (ae_of_all _ fun t => ?_)).congr
      (ae_of_all _ fun t => (div_eq_mul_inv _ _).symm)
    simp only [Pi.inv_apply]
    rw [norm_inv, Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
  have hae := ae_tendsto_poissonKernel hg.aestronglyMeasurable hw
  have key := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (F := fun b x => ‖poissonInt b g x - g x‖ ^ q) (f := fun _ => (0 : ℝ))
    (fun x => C ^ q * (1 + x ^ 2)⁻¹) ?_ ?_ (integrable_inv_one_add_sq.const_mul _) ?_
  · rwa [integral_zero] at key
  · filter_upwards [self_mem_nhdsWithin] with b (hb : 0 < b)
    exact (Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable
      ((integrable_poissonInt hb hg).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with b hb
    refine ae_of_all _ fun x => ?_
    have h1 := norm_poissonInt_sub_le_majorant hg hG hM hMs hb.1 hb.2.le x
    have hx1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖poissonInt b g x - g x‖ ^ q ≤ (C / (1 + x ^ 2)) ^ q :=
          Real.rpow_le_rpow (norm_nonneg _) h1 hq0.le
      _ = C ^ q / (1 + x ^ 2) ^ q := Real.div_rpow hC0 (by positivity) _
      _ ≤ C ^ q / (1 + x ^ 2) := div_le_div_of_nonneg_left (Real.rpow_nonneg hC0 _)
          (by positivity) (Real.self_le_rpow_of_one_le hx1 hq)
      _ = C ^ q * (1 + x ^ 2)⁻¹ := div_eq_mul_inv _ _
  · filter_upwards [hae] with x hx
    have h1 : Tendsto (fun b => ‖poissonInt b g x - g x‖) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun b => norm_nonneg _) ?_
        ((hx.const_mul π⁻¹).trans (by rw [mul_zero]))
      filter_upwards [self_mem_nhdsWithin] with b (hb : 0 < b)
      exact norm_poissonInt_sub_le hg hb x
    have h2 := ((Real.continuousAt_rpow_const 0 q (Or.inr hq0.le)).tendsto).comp h1
    rwa [Real.zero_rpow hq0.ne'] at h2

/-- `P_b g → g` in `L^p` (`1 ≤ p < ∞`) for continuous compactly supported `g`. -/
theorem tendsto_eLpNorm_poissonInt_sub {g : ℝ → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    Tendsto (fun b => eLpNorm (fun x => poissonInt b g x - g x) p volume) (𝓝[>] 0) (𝓝 0) := by
  have hp0 : p ≠ 0 := by positivity
  have hq : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp hp1
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hlim := tendsto_integral_poissonInt_sub hgc hgs hq
  have h2 : Tendsto (fun b => ENNReal.ofReal ((∫ x, ‖poissonInt b g x - g x‖ ^ p.toReal) ^
      p.toReal⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto _).comp (((Real.continuousAt_rpow_const 0
      p.toReal⁻¹ (Or.inr (by positivity))).tendsto).comp hlim)
    rwa [Real.zero_rpow (by positivity), ENNReal.ofReal_zero] at this
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with b hb
  have hm : AEStronglyMeasurable (fun x => poissonInt b g x - g x) volume :=
    (integrable_poissonInt hb.1 hg).aestronglyMeasurable.sub hg.aestronglyMeasurable
  have hint : Integrable fun x => ‖poissonInt b g x - g x‖ ^ p.toReal := by
    obtain ⟨M, hM, hMs⟩ := exists_support_bound hgs
    obtain ⟨G, hG⟩ := hgc.bounded_above_of_compact_support hgs
    set C := 2 * G * (2 + 4 * M ^ 2) + 8 * ∫ t, ‖g t‖
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    have hC0 : 0 ≤ C := by
      have : 0 ≤ ∫ t, ‖g t‖ := integral_nonneg fun _ => norm_nonneg _
      positivity
    refine (integrable_inv_one_add_sq.const_mul (C ^ p.toReal)).mono'
      ((Real.continuous_rpow_const (by positivity)).comp_aestronglyMeasurable hm.norm)
      (ae_of_all _ fun x => ?_)
    have h1 := norm_poissonInt_sub_le_majorant hg hG hM hMs hb.1 hb.2.le x
    have hx1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖poissonInt b g x - g x‖ ^ p.toReal ≤ (C / (1 + x ^ 2)) ^ p.toReal :=
          Real.rpow_le_rpow (norm_nonneg _) h1 (by positivity)
      _ = C ^ p.toReal / (1 + x ^ 2) ^ p.toReal := Real.div_rpow hC0 (by positivity) _
      _ ≤ C ^ p.toReal / (1 + x ^ 2) := div_le_div_of_nonneg_left (Real.rpow_nonneg hC0 _)
          (by positivity) (Real.self_le_rpow_of_one_le hx1 hq)
      _ = C ^ p.toReal * (1 + x ^ 2)⁻¹ := div_eq_mul_inv _ _
  rw [((integrable_norm_rpow_iff hm hp0 hp).mp hint).eLpNorm_eq_integral_rpow_norm hp0 hp]

/-- **Density**: every real `f ∈ L^p` (`1 ≤ p < ∞`) is approximated in `L^p` by Poisson integrals
`P_b g` of real continuous compactly supported `g`, with `0 < b < 1`. -/
theorem exists_poissonInt_approx {f : ℝ → ℝ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (hf : MemLp f p volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧ HasCompactSupport g ∧ ∃ b, 0 < b ∧ b < 1 ∧
      eLpNorm (fun x => (f x : ℂ) - poissonInt b (fun t => (g t : ℂ)) x) p volume <
        ENNReal.ofReal ε := by
  obtain ⟨g, hgs, hfg, hgc, -⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (by simp; linarith)
  set gC : ℝ → ℂ := fun t => (g t : ℂ) with hgC
  have hgCc : Continuous gC := Complex.continuous_ofReal.comp hgc
  have hgCs : HasCompactSupport gC := hgs.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero
  have hlim := tendsto_eLpNorm_poissonInt_sub hgCc hgCs hp1 hp
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ),
      eLpNorm (fun x => poissonInt b gC x - gC x) p volume < ENNReal.ofReal (ε / 2) :=
    hlim (Iio_mem_nhds (by simp; linarith))
  obtain ⟨b, hb, hb1⟩ := (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  refine ⟨g, hgc, hgs, b, hb1.1, hb1.2, ?_⟩
  have hsplit : (fun x => (f x : ℂ) - poissonInt b gC x) =
      (fun x => ((f x : ℂ) - gC x)) + (fun x => -(poissonInt b gC x - gC x)) := by
    funext x; simp only [Pi.add_apply]; ring
  have h1 : eLpNorm (fun x => (f x : ℂ) - gC x) p volume = eLpNorm (f - g) p volume := by
    refine eLpNorm_congr_norm_ae ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      hf.aestronglyMeasurable).sub hgCc.aestronglyMeasurable)
      (hf.aestronglyMeasurable.sub hgc.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    simp only [hgC, Pi.sub_apply]
    rw [← ofReal_sub, Complex.norm_real]
  have h2 : eLpNorm (fun x => -(poissonInt b gC x - gC x)) p volume =
      eLpNorm (fun x => poissonInt b gC x - gC x) p volume :=
    eLpNorm_neg (fun x => poissonInt b gC x - gC x) p volume
  rw [hsplit]
  calc eLpNorm ((fun x => (f x : ℂ) - gC x) + fun x => -(poissonInt b gC x - gC x)) p volume
      ≤ eLpNorm (fun x => (f x : ℂ) - gC x) p volume +
        eLpNorm (fun x => -(poissonInt b gC x - gC x)) p volume := eLpNorm_add_le hp1
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        rw [h1, h2]
        exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfg)
          hfg hb
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

end Azurite.DLMF
