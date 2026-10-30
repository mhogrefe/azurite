/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14StieltjesAbel
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# DLMF §1.14(vi): Stieltjes Transform

Formalizations of <https://dlmf.nist.gov/1.14.vi>.  `f` is real-valued and integrable on every
`[0, R]`; the integral (1.14.47) is improper at `∞` and may converge only conditionally.

* 1.14.47: `stieltjesPartial` (`∫_0^R f(t)/(s + t) dt`), `StieltjesConverges`, `stieltjes`.
* Convergence: `dlmf_1_14_vi_converges` (`s > 0` and `f(t) = O(t^{−δ})`, `δ > 0`);
  `dlmf_1_14_vi_uniform` (if the integral converges at one point `s₀` of the cut plane
  `ℂ \ (−∞, 0]` = `Complex.slitPlane`, it converges uniformly on every compact subset: Abel's
  bound with the multiplier `(s₀ + t)/(s + t)` and `|s + t| ≥ c (1 + t)`,
  `exists_mul_one_add_le_norm`); `tendsto_stieltjesPartial`, `tendstoLocallyUniformlyOn_stieltjes`.
* Analyticity: `dlmf_1_14_vi_analytic` (`𝒮f` is analytic in the cut plane, as a locally uniform
  limit of holomorphic partial integrals).
* 1.14.48: `dlmf_1_14_48` (`𝒮f^{(m)}(s) = (−1)^m m! ∫_0^∞ f(t)/(s + t)^{m+1} dt`, the integral
  converging at every `s` of the cut plane); `stieltjesPow`, `hasDerivAt_stieltjesPow`
  (differentiation under the integral sign), `tendstoLocallyUniformlyOn_iteratedDeriv`.
* 1.14.49 is in `Section14StieltjesInversion.lean`, 1.14.50 in `Section14StieltjesLaplace.lean`.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Definition 1.14.47 -/

/-- The partial Stieltjes integral `∫_0^R f(t)/(s + t) dt`. -/
noncomputable def stieltjesPartial (f : ℝ → ℝ) (s : ℂ) (R : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t)

/-- The integral (1.14.47) converges (as an improper integral at `∞`). -/
def StieltjesConverges (f : ℝ → ℝ) (s : ℂ) : Prop :=
  ∃ L, Tendsto (stieltjesPartial f s) atTop (𝓝 L)

/-- **DLMF 1.14.47**: the Stieltjes transform `𝒮f(s) = ∫_0^∞ f(t)/(s + t) dt` (improper). -/
noncomputable def stieltjes (f : ℝ → ℝ) (s : ℂ) : ℂ := limUnder atTop (stieltjesPartial f s)

theorem StieltjesConverges.tendsto {f : ℝ → ℝ} {s : ℂ} (h : StieltjesConverges f s) :
    Tendsto (stieltjesPartial f s) atTop (𝓝 (stieltjes f s)) :=
  tendsto_nhds_limUnder h

theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => (f t : ℂ)) volume a b :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

theorem add_ofReal_ne_zero {s : ℂ} (hs : s ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) : s + t ≠ 0 := by
  intro h
  have hre : s.re = -t := by have := congrArg Complex.re h; simp at this; linarith
  have him : s.im = 0 := by have := congrArg Complex.im h; simpa using this
  rcases mem_slitPlane_iff.mp hs with h1 | h1
  · linarith
  · exact h1 him

/-- On a compact subset of the cut plane `ℂ \ (−∞, 0]`, `|s + t| ≥ c (1 + t)` for `t ≥ 0`. -/
theorem exists_mul_one_add_le_norm {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ slitPlane) :
    ∃ c > 0, ∀ s ∈ K, ∀ t : ℝ, 0 ≤ t → c * (1 + t) ≤ ‖s + t‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun s hs => absurd hs (notMem_empty s)⟩
  set C := slitPlaneᶜ
  have hC : IsClosed C := isOpen_slitPlane.isClosed_compl
  have hC0 : (0 : ℂ) ∈ C := by simp [C, mem_slitPlane_iff]
  obtain ⟨s₁, hs₁, hmin⟩ := hK.exists_isMinOn hne
    (Metric.continuous_infDist_pt C).continuousOn
  set d := Metric.infDist s₁ C
  have hd : 0 < d := (hC.notMem_iff_infDist_pos ⟨0, hC0⟩).mp fun h => h (hKs hs₁)
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s₁ hs₁)
  refine ⟨d / (1 + M + d), by positivity, fun s hs t ht => ?_⟩
  have h1 : d ≤ ‖s + t‖ := by
    have hmem : (-(t : ℂ)) ∈ C := by simp [C, mem_slitPlane_iff]; exact ht
    calc d ≤ Metric.infDist s C := hmin hs
      _ ≤ dist s (-(t : ℂ)) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖s + t‖ := by rw [dist_eq_norm, sub_neg_eq_add]
  have h2 : t - M ≤ ‖s + t‖ := by
    have := norm_sub_norm_le (t : ℂ) (-s)
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg ht, sub_neg_eq_add, add_comm] at this
    linarith [hM s hs]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rcases le_total t (M + d) with h | h
  · nlinarith
  · nlinarith

theorem intervalIntegrable_of_integrableOn {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R))
    {R : ℝ} (hR : 0 ≤ R) : IntervalIntegrable f volume 0 R :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr (hf R)

/-- `t ↦ f(t) k(t)` is integrable on `[0, R]` for `k` continuous there. -/
theorem intervalIntegrable_mul_of_continuousOn {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R))
    {k : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R) (hk : ContinuousOn k (Icc 0 R)) :
    IntervalIntegrable (fun t => (f t : ℂ) * k t) volume 0 R :=
  (intervalIntegrable_ofReal (intervalIntegrable_of_integrableOn hf hR)).mul_continuousOn
    (by rwa [uIcc_of_le hR])

theorem continuousOn_inv_add_pow {s : ℂ} (hs : s ∈ slitPlane) (m : ℕ) (R : ℝ) :
    ContinuousOn (fun t : ℝ => ((s + t) ^ m)⁻¹) (Icc 0 R) :=
  ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero _ (add_ofReal_ne_zero hs ht.1)

/-- The integrand `f(t)/(s + t)^m` is integrable on `[0, R]` for `s` off the cut. -/
theorem intervalIntegrable_div_pow {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s : ℂ}
    (hs : s ∈ slitPlane) (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun t => (f t : ℂ) / (s + t) ^ m) volume 0 R := by
  simpa [div_eq_mul_inv] using intervalIntegrable_mul_of_continuousOn hf hR
    (continuousOn_inv_add_pow hs m R)

theorem uniformCauchySeqOn_of_dist {α : Type*} {F : ℝ → α → ℂ} {K : Set α}
    (h : ∀ ε > 0, ∃ T, ∀ m n, T ≤ m → T ≤ n → ∀ x ∈ K, dist (F m x) (F n x) < ε) :
    UniformCauchySeqOn F atTop K := by
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨T, hT⟩ := h ε hε
  filter_upwards [(eventually_ge_atTop T).prod_mk (eventually_ge_atTop T)] with p hp x hx
  exact hεu (hT p.1 p.2 hp.1 hp.2 x hx)

theorem integral_inv_one_add_sq_le {R R' : ℝ} (hR : 0 ≤ R) (hRR' : R ≤ R') :
    ∫ t in R..R', 1 / (1 + t) ^ 2 ≤ 1 := by
  have hd : ∀ t ∈ uIcc R R', HasDerivAt (fun t : ℝ => -(1 + t)⁻¹) (1 / (1 + t) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hRR'] at ht
    have hne : (1 + t) ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
      simpa using (hasDerivAt_id t).const_add 1
    convert (h1.inv hne).neg using 1
    ring
  have hc : ContinuousOn (fun t : ℝ => 1 / (1 + t) ^ 2) (uIcc R R') := by
    rw [uIcc_of_le hRR']
    exact continuousOn_const.div ((by fun_prop : Continuous fun t : ℝ => (1 + t) ^ 2).continuousOn)
      fun t ht => pow_ne_zero _ (by linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have h1 : 0 < (1 + R')⁻¹ := inv_pos.mpr (by linarith)
  have h2 : (1 + R)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  linarith

/-! ### Convergence -/

/-- **DLMF §1.14(vi)**: for `s > 0` and `f(t) = O(t^{−δ})` as `t → ∞` (`δ > 0`), `f` integrable
on every `[0, R]`, the integral (1.14.47) converges (absolutely). -/
theorem dlmf_1_14_vi_converges {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s : ℝ}
    (hs : 0 < s) {δ : ℝ} (hδ : 0 < δ) (hO : f =O[atTop] fun t => t ^ (-δ)) :
    StieltjesConverges f s := by
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  set T := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right _ _
  have hmeas : AEStronglyMeasurable (fun t => (f t : ℂ) / (s + t)) (volume.restrict (Ioi 0)) := by
    have hU : Ioi (0 : ℝ) ⊆ ⋃ n : ℕ, Ioc 0 (n : ℝ) := fun t ht => by
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact mem_iUnion.mpr ⟨n, ht, hn⟩
    refine AEStronglyMeasurable.mono_set hU (aestronglyMeasurable_iUnion_iff.mpr fun n => ?_)
    have h1 : AEStronglyMeasurable (fun t => (f t : ℂ)) (volume.restrict (Ioc 0 (n : ℝ))) :=
      (((hf n).mono_set Ioc_subset_Icc_self).ofReal (𝕜 := ℂ)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ => ((s : ℂ) + t)⁻¹) (volume.restrict (Ioc 0 n)) :=
      (by fun_prop : Measurable fun t : ℝ => ((s : ℂ) + t)⁻¹).aestronglyMeasurable
    exact (h1.mul h2).congr (ae_of_all _ fun t => (div_eq_mul_inv _ _).symm)
  have hnorm : ∀ t : ℝ, 0 < t → ‖(f t : ℂ) / (s + t)‖ = |f t| / (s + t) := fun t ht => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, ← ofReal_add, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hint : IntegrableOn (fun t => (f t : ℂ) / (s + t)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ T)]
    refine IntegrableOn.union ?_ ?_
    · refine Integrable.mono' (((hf T).mono_set Ioc_subset_Icc_self).abs.div_const s)
        (hmeas.mono_set Ioc_subset_Ioi_self)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
      rw [hnorm t ht.1]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hs (by linarith [ht.1])
    · refine Integrable.mono' (((integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1)
        (by linarith : (0 : ℝ) < T))).const_mul C) (hmeas.mono_set (Ioi_subset_Ioi (by linarith)))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
      have hb := hT₀ t ((le_max_left _ _).trans (mem_Ioi.mp ht).le)
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)] at hb
      rw [hnorm t ht0, Real.rpow_sub_one ht0.ne', mul_div_assoc']
      calc |f t| / (s + t) ≤ |f t| / t := div_le_div_of_nonneg_left (abs_nonneg _) ht0
            (by linarith)
        _ ≤ C * t ^ (-δ) / t := div_le_div_of_nonneg_right hb ht0.le
  exact ⟨_, intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id⟩

/-- The kernel `(s₀ + t)/(s + t)` relating the integrands at `s₀` and at `s`. -/
theorem hasDerivAt_ratio {s s₀ : ℂ} (hs : s ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun t : ℝ => (s₀ + t) / (s + t)) ((s - s₀) / (s + t) ^ 2) t := by
  have hne := add_ofReal_ne_zero hs ht
  have h1 : HasDerivAt (fun t : ℝ => s₀ + (t : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp.const_add s₀
  have h2 : HasDerivAt (fun t : ℝ => s + (t : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp.const_add s
  convert h1.div h2 hne using 1
  field_simp
  ring

/-- **DLMF §1.14(vi)**: if (1.14.47) converges at one point `s₀` of the cut plane
`ℂ \ (−∞, 0]`, then it converges uniformly on every compact subset of the cut plane. -/
theorem dlmf_1_14_vi_uniform {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ slitPlane) :
    TendstoUniformlyOn (fun R s => stieltjesPartial f s R) (stieltjes f) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact tendstoUniformlyOn_empty
  obtain ⟨c, hc, hcK⟩ := exists_mul_one_add_le_norm hK hKs
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  set g : ℝ → ℂ := fun t => (f t : ℂ) / (s₀ + t) with hg
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable g volume 0 R := fun R hR => by
    simpa [hg] using intervalIntegrable_div_pow hf hs₀ 1 hR
  obtain ⟨L₀, hL₀⟩ := hconv
  have hL₀' : Tendsto (fun R => ∫ t in (0 : ℝ)..R, g t) atTop (𝓝 L₀) := hL₀
  set A := (M + ‖s₀‖) / c ^ 2
  set CK := (‖s₀‖ + 1) / c + A
  have hCK : 0 ≤ CK := by positivity
  have hbound : ∀ s ∈ K, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' →
      ‖(s₀ + (R' : ℂ)) / (s + R')‖ + ∫ t in R..R', ‖(s - s₀) / (s + t) ^ 2‖ ≤ CK := by
    intro s hs R R' hR hRR'
    have hR' : 0 ≤ R' := hR.trans hRR'
    have p1 : ‖(s₀ + (R' : ℂ)) / (s + R')‖ ≤ (‖s₀‖ + 1) / c := by
      rw [norm_div]
      have hn : ‖s₀ + (R' : ℂ)‖ ≤ (‖s₀‖ + 1) * (1 + R') := by
        have := norm_add_le s₀ (R' : ℂ)
        rw [Complex.norm_real, Real.norm_of_nonneg hR'] at this
        nlinarith [norm_nonneg s₀]
      calc ‖s₀ + (R' : ℂ)‖ / ‖s + R'‖ ≤ (‖s₀‖ + 1) * (1 + R') / (c * (1 + R')) :=
            div_le_div₀ (by positivity) hn (by positivity) (hcK s hs R' hR')
        _ = (‖s₀‖ + 1) / c := by field_simp
    have p2 : ∫ t in R..R', ‖(s - s₀) / (s + t) ^ 2‖ ≤ A := by
      have hcont : ContinuousOn (fun t : ℝ => ‖(s - s₀) / (s + t) ^ 2‖) (Icc R R') :=
        (ContinuousOn.div continuousOn_const (by fun_prop) fun t ht =>
          pow_ne_zero _ (add_ofReal_ne_zero (hKs hs) (hR.trans ht.1))).norm
      calc ∫ t in R..R', ‖(s - s₀) / (s + t) ^ 2‖ ≤ ∫ t in R..R', A * (1 / (1 + t) ^ 2) := by
            refine intervalIntegral.integral_mono_on hRR' (hcont.intervalIntegrable_of_Icc hRR')
              (ContinuousOn.intervalIntegrable_of_Icc hRR' (by
                refine continuousOn_const.mul (ContinuousOn.div continuousOn_const
                  (by fun_prop) fun t ht => pow_ne_zero _ (by linarith [ht.1]))))
              fun t ht => ?_
            have ht0 : 0 ≤ t := hR.trans ht.1
            have hst := hcK s hs t ht0
            rw [norm_div, norm_pow]
            have hss : ‖s - s₀‖ ≤ M + ‖s₀‖ := (norm_sub_le _ _).trans (by linarith [hM s hs])
            calc ‖s - s₀‖ / ‖s + t‖ ^ 2 ≤ (M + ‖s₀‖) / (c * (1 + t)) ^ 2 :=
                  div_le_div₀ (by positivity) hss (by positivity) (pow_le_pow_left₀
                    (by positivity) hst 2)
              _ = A * (1 / (1 + t) ^ 2) := by simp only [A]; field_simp
        _ = A * ∫ t in R..R', 1 / (1 + t) ^ 2 := intervalIntegral.integral_const_mul _ _
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left (integral_inv_one_add_sq_le hR hRR')
            (by positivity)
        _ = A := mul_one A
    simp only [CK]; linarith
  have hkey : ∀ η > 0, ∃ T, ∀ m n, T ≤ m → m ≤ n → ∀ s ∈ K,
      ‖stieltjesPartial f s n - stieltjesPartial f s m‖ ≤ η * CK := by
    intro η hη
    obtain ⟨T, hT0, hT⟩ := cauchy_of_tendsto_integral (fun R hR => hgI R hR) hL₀' hη
    refine ⟨T, fun m n hm hmn s hs => ?_⟩
    have hm0 : 0 ≤ m := hT0.trans hm
    have hs' := hKs hs
    have e1 : stieltjesPartial f s n - stieltjesPartial f s m =
        ∫ t in m..n, g t * ((s₀ + t) / (s + t)) := by
      unfold stieltjesPartial
      rw [intervalIntegral.integral_interval_sub_left
        (by simpa using intervalIntegrable_div_pow hf hs' 1 (hm0.trans hmn))
        (by simpa using intervalIntegrable_div_pow hf hs' 1 hm0)]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hmn] at ht
      have h1 := add_ofReal_ne_zero hs' (hm0.trans ht.1)
      have h2 := add_ofReal_ne_zero hs₀ (hm0.trans ht.1)
      simp only [hg]
      field_simp
    rw [e1]
    refine (norm_integral_mul_le_abel hmn ((hgI m hm0).symm.trans (hgI n (hm0.trans hmn)))
      (fun t ht => hasDerivAt_ratio hs' (hm0.trans ht.1))
      (ContinuousOn.div continuousOn_const (by fun_prop) fun t ht =>
        pow_ne_zero _ (add_ofReal_ne_zero hs' (hm0.trans ht.1)))
      (fun u hu => hT m u hm (hm.trans hu.1))).trans ?_
    exact mul_le_mul_of_nonneg_left (hbound s hs m n hm0 hmn) hη.le
  have hUC : UniformCauchySeqOn (fun R s => stieltjesPartial f s R) atTop K := by
    refine uniformCauchySeqOn_of_dist fun ε hε => ?_
    obtain ⟨T, hT⟩ := hkey (ε / (2 * (CK + 1))) (by positivity)
    have hlt : ε / (2 * (CK + 1)) * CK < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    refine ⟨T, fun m n hm hn s hs => ?_⟩
    rw [dist_eq_norm]
    rcases le_total m n with h | h
    · rw [norm_sub_rev]; exact (hT m n hm h s hs).trans_lt hlt
    · exact (hT n m hn h s hs).trans_lt hlt
  refine hUC.tendstoUniformlyOn_of_tendsto fun s hs => ?_
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hUC.cauchySeq hs)
  exact StieltjesConverges.tendsto ⟨L, hL⟩

/-- Every point of the cut plane: the integral converges, to `𝒮f(s)`. -/
theorem tendsto_stieltjesPartial {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) {s : ℂ} (hs : s ∈ slitPlane) :
    Tendsto (stieltjesPartial f s) atTop (𝓝 (stieltjes f s)) :=
  (dlmf_1_14_vi_uniform hf hs₀ hconv isCompact_singleton (singleton_subset_iff.mpr hs)).tendsto_at
    (mem_singleton s)

/-- Locally uniform convergence on the cut plane. -/
theorem tendstoLocallyUniformlyOn_stieltjes {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R))
    {s₀ : ℂ} (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) :
    TendstoLocallyUniformlyOn (fun R s => stieltjesPartial f s R) (stieltjes f) atTop
      slitPlane :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_slitPlane).mpr fun _ hK hKc =>
    dlmf_1_14_vi_uniform hf hs₀ hconv hKc hK

/-! ### Analyticity and derivatives (1.14.48) -/

/-- The partial integrals `∫_0^R f(t)/(s + t)^{m+1} dt`. -/
noncomputable def stieltjesPow (f : ℝ → ℝ) (m : ℕ) (s : ℂ) (R : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) ^ (m + 1)

theorem stieltjesPow_zero (f : ℝ → ℝ) (s : ℂ) (R : ℝ) :
    stieltjesPow f 0 s R = stieltjesPartial f s R := by
  simp [stieltjesPow, stieltjesPartial]

theorem hasDerivAt_stieltjesPow {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) (m : ℕ)
    {s₀ : ℂ} (hs₀ : s₀ ∈ slitPlane) {R : ℝ} (hR : 0 ≤ R) :
    HasDerivAt (fun s => stieltjesPow f m s R) (-(m + 1 : ℂ) * stieltjesPow f (m + 1) s₀ R) s₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_slitPlane s₀ hs₀
  have hS : Metric.closedBall s₀ (ε / 2) ⊆ slitPlane :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨c, hc, hcS⟩ := exists_mul_one_add_le_norm (isCompact_closedBall s₀ (ε / 2)) hS
  have hlow : ∀ x ∈ Metric.closedBall s₀ (ε / 2), ∀ t ∈ Ι (0 : ℝ) R, c ≤ ‖x + t‖ := by
    intro x hx t ht
    rw [uIoc_of_le hR] at ht
    have := hcS x hx t ht.1.le
    nlinarith [ht.1]
  have hne : ∀ x ∈ Metric.closedBall s₀ (ε / 2), ∀ t ∈ Ι (0 : ℝ) R, x + t ≠ 0 := fun x hx t ht =>
    norm_pos_iff.mp (hc.trans_le (hlow x hx t ht))
  have hmeas : ∀ k : ℕ, ∀ x ∈ slitPlane,
      AEStronglyMeasurable (fun t => (f t : ℂ) / (x + t) ^ k) (volume.restrict (Ι (0 : ℝ) R)) :=
    fun k x hx => by
      rw [uIoc_of_le hR]; exact (intervalIntegrable_div_pow hf hx k hR).1.aestronglyMeasurable
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := R) (F := fun x t => (f t : ℂ) / (x + t) ^ (m + 1))
    (F' := fun x t => -(m + 1 : ℂ) * ((f t : ℂ) / (x + t) ^ (m + 1 + 1)))
    (bound := fun t => (m + 1) * |f t| / c ^ (m + 1 + 1))
    (Metric.closedBall_mem_nhds s₀ (half_pos hε))
    (eventually_of_mem (isOpen_slitPlane.mem_nhds hs₀) fun x hx => hmeas (m + 1) x hx)
    (intervalIntegrable_div_pow hf hs₀ (m + 1) hR)
    ((hmeas (m + 1 + 1) s₀ hs₀).const_mul _)
    (ae_of_all _ fun t ht x hx => by
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖-(m + 1 : ℂ)‖ = m + 1 := by
        have e : (m + 1 : ℂ) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [norm_neg, e, Complex.norm_natCast]; push_cast; ring
      rw [h1, mul_div_assoc]
      gcongr
      exact hlow x hx t ht)
    ((((intervalIntegrable_of_integrableOn hf hR).abs).const_mul (m + 1)).div_const _)
    (ae_of_all _ fun t ht x hx => by
      have hxt := hne x hx t ht
      have hp0 := (hasDerivAt_pow (m + 1) (x + (t : ℂ))).comp x
        ((hasDerivAt_id x).add_const (t : ℂ))
      have hp : HasDerivAt (fun x : ℂ => (x + t) ^ (m + 1)) ((m + 1 : ℂ) * (x + t) ^ m) x :=
        hp0.congr_deriv (by simp)
      have := (hp.inv (pow_ne_zero _ hxt)).const_mul (f t : ℂ)
      convert this using 1
      · funext y; simp [div_eq_mul_inv]
      · field_simp; ring)
  convert h.2 using 1
  · rfl
  · unfold stieltjesPow
    rw [← intervalIntegral.integral_const_mul]

theorem differentiableOn_stieltjesPow {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) (m : ℕ)
    {R : ℝ} (hR : 0 ≤ R) : DifferentiableOn ℂ (fun s => stieltjesPow f m s R) slitPlane :=
  fun _ hs => (hasDerivAt_stieltjesPow hf m hs hR).differentiableAt.differentiableWithinAt

/-- The `m`-th derivatives: `(−1)^m m! ∫_0^R f/(s + t)^{m+1} → 𝒮f^{(m)}(s)` locally uniformly. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv {f : ℝ → ℝ}
    (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ} (hs₀ : s₀ ∈ slitPlane)
    (hconv : StieltjesConverges f s₀) (m : ℕ) :
    TendstoLocallyUniformlyOn (fun R s => (-1) ^ m * (m.factorial : ℂ) * stieltjesPow f m s R)
      (iteratedDeriv m (stieltjes f)) atTop slitPlane := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul, iteratedDeriv_zero,
      stieltjesPow_zero]
    exact tendstoLocallyUniformlyOn_stieltjes hf hs₀ hconv
  | succ m ih =>
    have hdiff : ∀ᶠ R in atTop, DifferentiableOn ℂ
        (fun s => (-1) ^ m * (m.factorial : ℂ) * stieltjesPow f m s R) slitPlane :=
      (eventually_ge_atTop 0).mono fun R hR =>
        (differentiableOn_stieltjesPow hf m hR).const_mul _
    have hd := ih.deriv hdiff isOpen_slitPlane
    rw [← iteratedDeriv_succ] at hd
    refine hd.congr_inseparable ((eventually_ge_atTop 0).mono fun R hR s hs => .of_eq ?_)
    simp only [Function.comp_apply]
    rw [((hasDerivAt_stieltjesPow hf m hs hR).const_mul ((-1) ^ m * (m.factorial : ℂ))).deriv,
      Nat.factorial_succ]
    push_cast
    ring

/-- **DLMF §1.14(vi)**: if (1.14.47) converges (at some point of the cut plane), `𝒮f` is analytic
in the `s`-plane cut along the negative real axis. -/
theorem dlmf_1_14_vi_analytic {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) :
    DifferentiableOn ℂ (stieltjes f) slitPlane ∧ AnalyticOnNhd ℂ (stieltjes f) slitPlane := by
  have h := (tendstoLocallyUniformlyOn_stieltjes hf hs₀ hconv).differentiableOn
    ((eventually_ge_atTop 0).mono fun R hR => by
      simpa only [stieltjesPow_zero] using differentiableOn_stieltjesPow hf 0 hR)
    isOpen_slitPlane
  exact ⟨h, h.analyticOnNhd isOpen_slitPlane⟩

/-- **DLMF 1.14.48**: `𝒮f^{(m)}(s) = (−1)^m m! ∫_0^∞ f(t)/(s + t)^{m+1} dt`, the integral
converging (improperly) at every `s` of the cut plane. -/
theorem dlmf_1_14_48 {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) (m : ℕ) {s : ℂ}
    (hs : s ∈ slitPlane) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) ^ (m + 1)) atTop
        (𝓝 (limUnder atTop fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) ^ (m + 1))) ∧
      iteratedDeriv m (stieltjes f) s = (-1) ^ m * m.factorial *
        limUnder atTop fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) ^ (m + 1) := by
  have h := (tendstoLocallyUniformlyOn_iteratedDeriv hf hs₀ hconv m).tendsto_at hs
  set c : ℂ := (-1) ^ m * (m.factorial : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast
    (Nat.factorial_pos m).ne')
  have h' : Tendsto (fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) / (s + t) ^ (m + 1)) atTop
      (𝓝 (c⁻¹ * iteratedDeriv m (stieltjes f) s)) := by
    have := h.const_mul c⁻¹
    refine this.congr fun R => ?_
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rfl
  rw [h'.limUnder_eq]
  exact ⟨h', by field_simp⟩

end Azurite.DLMF
