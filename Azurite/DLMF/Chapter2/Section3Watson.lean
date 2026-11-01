/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Laplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# DLMF §2.3(ii): Watson's lemma (2.3.7–2.3.9)

The hypothesis 2.3.7, `q(t) ∼ ∑ aₛ t^{(s+λ−μ)/μ}` as `t → 0+`, is a generalized expansion
(`IsGenAsympExpansionDLMF (𝓝[>] 0)`); the conclusions are generalized expansions as `x → +∞` with
the scale `x^{−αₛ}`, `αₛ = (s+λ)/μ` (`watsonExp`). `q` need not be continuous: it is measurable
and integrable on every `[c, R]`, `c > 0`; integrability near `0` follows from 2.3.7
(`intervalIntegrable_zero_of_bound`). A finite integration range is the case `q = 0` beyond it.

* `watson_near_zero`: the contribution of `(0, b]` for a general kernel `f(xt)`,
  `∫₀^b f(xt) q(t) dt = ∑_{s<n} aₛ x^{−αₛ} ∫₀^∞ u^{αₛ−1} f(u) du + O(x^{−αₙ})`, with an explicit
  constant (scaling `integral_Ioi_rpow_smul_comp_mul`). Used for 2.3.8, 2.3.9 and 2.3.12.
* `dlmf_2_3_8`: Watson's lemma for the improper Laplace integral `laplaceIntegral`; the tail is
  exponentially small by `laplace_tail_exists` (`Section3Laplace.lean`).
* `dlmf_2_3_9`: the logarithmic case, `∑ Γ′(αₛ) aₛ x^{−αₛ} − ln x ∑ Γ(αₛ) aₛ x^{−αₛ}`, as a
  generalized expansion with the scale `x^{−αₛ} ln x`; it uses
  `ln t = ln(xt) − ln x` and the kernel `e^{−u} ln u`, whose Mellin transform is `Γ′`
  (`hasDerivAt_Gamma_integral`, from Mathlib's `Complex.hasDerivAt_GammaIntegral`).
-/

open Set Filter Topology Asymptotics Complex MeasureTheory

namespace Azurite.DLMF

/-! ### Scaling and asymptotic scales -/

theorem integral_Ioi_rpow_smul_comp_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (α : ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi 0, t ^ (α - 1) • g (x * t) = x ^ (-α) • ∫ u in Ioi 0, u ^ (α - 1) • g u := by
  have h : EqOn (fun t : ℝ => t ^ (α - 1) • g (x * t))
      (fun t => x ^ (1 - α) • ((x * t) ^ (α - 1) • g (x * t))) (Ioi 0) := fun t ht => by
    simp only
    rw [smul_smul, Real.mul_rpow hx.le (le_of_lt ht), ← mul_assoc, ← Real.rpow_add hx,
      show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_smul,
    integral_comp_mul_left_Ioi (fun u => u ^ (α - 1) • g u) 0 hx, mul_zero, smul_smul,
    ← Real.rpow_neg_one, ← Real.rpow_add hx, show 1 - α + -1 = -α by ring]

theorem integrableOn_Ioi_rpow_smul_comp_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : ℝ → E} {α x : ℝ} (hx : 0 < x)
    (hg : IntegrableOn (fun u => u ^ (α - 1) • g u) (Ioi 0)) :
    IntegrableOn (fun t => t ^ (α - 1) • g (x * t)) (Ioi 0) := by
  have h1 := ((integrableOn_Ioi_comp_mul_left_iff (fun u => u ^ (α - 1) • g u) 0 hx).mpr
    (by rwa [mul_zero])).smul (x ^ (1 - α))
  refine IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
  simp only [Pi.smul_apply]
  rw [smul_smul, Real.mul_rpow hx.le (le_of_lt ht), ← mul_assoc, ← Real.rpow_add hx,
    show 1 - α + (α - 1) = 0 by ring, Real.rpow_zero, one_mul]

/-- `O` from an eventual bound `‖E‖ ≤ K‖φ‖`, `φ` eventually nonzero. -/
theorem isBigODLMF_of_bound {α : Type*} {l : Filter α} {E φ : α → ℂ} {K : ℝ}
    (h : ∀ᶠ x in l, ‖E x‖ ≤ K * ‖φ x‖) (hφ : ∀ᶠ x in l, φ x ≠ 0) : IsBigODLMF l E φ := by
  refine ⟨K, eventually_map.mpr ?_⟩
  filter_upwards [h, hφ] with x hx hx0
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hx0)]
  exact hx

/-- An `O`-relation as `t → 0+` gives a bound `‖R(t)‖ ≤ C‖φ(t)‖` on some `(0, b]`, `b ≤ b₁`. -/
theorem exists_bound_of_isBigODLMF_nhdsGT {R φ : ℝ → ℂ} (h : IsBigODLMF (𝓝[>] 0) R φ)
    (hφ : ∀ t, 0 < t → φ t ≠ 0) {b₁ : ℝ} (hb₁ : 0 < b₁) :
    ∃ b C, 0 < b ∧ b ≤ b₁ ∧ ∀ t ∈ Ioc 0 b, ‖R t‖ ≤ C * ‖φ t‖ := by
  obtain ⟨C, hC⟩ := h
  rw [eventually_map] at hC
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hC
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min (u / 2) b₁, C, lt_min (half_pos hu0) hb₁, min_le_right _ _, fun t ht => ?_⟩
  have htu : t < u := by linarith [ht.2, min_le_left (u / 2) b₁]
  have h1 : ‖R t / φ t‖ ≤ C := hus ⟨ht.1, htu⟩
  have hφt := hφ t ht.1
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hφt)] at h1
  exact h1

/-- `x^{−α_s} w(x)` is an asymptotic scale when `α_{s+1} = α_s + c`, `c > 0`. -/
theorem isAsympScale_rpow_neg_mul {α : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hα : ∀ s, α (s + 1) = α s + c) {w : ℝ → ℂ} (hw : ∀ᶠ x in atTop, w x ≠ 0) :
    IsAsympScaleDLMF atTop fun s x => ((x ^ (-α s) : ℝ) : ℂ) * w x := fun s => by
  have h := (continuous_ofReal.tendsto 0).comp (tendsto_rpow_neg_atTop hc)
  rw [ofReal_zero] at h
  refine h.congr' ?_
  filter_upwards [hw, eventually_gt_atTop 0] with x hwx hx
  have hp : ((x ^ (-α s) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'
  simp only [Function.comp_apply]
  rw [mul_div_mul_right _ _ hwx, ← ofReal_div, ← Real.rpow_sub hx, hα s]
  congr 2
  ring

theorem eventually_exp_neg_le_rpow_neg (α : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(b * x)) ≤ x ^ (-α) := by
  filter_upwards [(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero α b hb).eventually
    (ge_mem_nhds zero_lt_one), eventually_gt_atTop 0] with x hx hx0
  have hp : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  rw [Real.rpow_neg hx0.le, le_inv_comm₀ (Real.exp_pos _) hp, ← one_div,
    le_div_iff₀ (Real.exp_pos _)]
  rw [neg_mul] at hx
  exact hx

/-- Integrability on `[0, R]` from a bound `‖g(t)‖ ≤ C tᵉ` (`e > −1`) near `0` and local
integrability away from `0`. -/
theorem intervalIntegrable_zero_of_bound {g : ℝ → ℂ} {b C e : ℝ} (hb : 0 < b) (he : -1 < e)
    (hg : AEStronglyMeasurable g volume) (hbd : ∀ t ∈ Ioc 0 b, ‖g t‖ ≤ C * t ^ e)
    (hloc : ∀ c R, 0 < c → c ≤ R → IntervalIntegrable g volume c R) (R : ℝ) (hR : 0 ≤ R) :
    IntervalIntegrable g volume 0 R := by
  have h0 : IntervalIntegrable g volume 0 b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le]
    have hp := (intervalIntegral.intervalIntegrable_rpow' he (a := 0) (b := b)).const_mul C
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le] at hp
    exact Integrable.mono' hp hg.restrict (ae_restrict_of_forall_mem measurableSet_Ioc hbd)
  rcases le_or_gt b R with h | h
  · exact h0.trans (hloc b R hb h)
  · exact h0.mono_set (by rw [uIcc_of_le hR, uIcc_of_le hb.le]; exact Icc_subset_Icc_right h.le)

/-! ### The contribution of a neighbourhood of the origin -/

/-- The core of Watson's lemma, for a general kernel `f(xt)`: if
`|q(t) − ∑_{s<n} aₛ t^{αₛ−1}| ≤ C t^{αₙ−1}` on `(0, b]` and `∫₀^∞ u^{αₛ−1} |f(u)| du < ∞`
(`s ≤ n`), then `∫₀^b f(xt) q(t) dt = ∑_{s<n} aₛ x^{−αₛ} 𝓜f(αₛ) + O(x^{−αₙ})`, with an explicit
constant. -/
theorem watson_near_zero {f q : ℝ → ℂ} {a : ℕ → ℂ} {α : ℕ → ℝ} {n : ℕ} {b C x : ℝ}
    (hb : 0 < b) (hx : 0 < x) (hf : Measurable f) (hq : Measurable q)
    (hα : ∀ s ≤ n, α s ≤ α n)
    (hfα : ∀ s ≤ n, IntegrableOn (fun u : ℝ => u ^ (α s - 1) * ‖f u‖) (Ioi 0))
    (hr : ∀ t ∈ Ioc 0 b,
      ‖q t - ∑ s ∈ Finset.range n, a s * ((t ^ (α s - 1) : ℝ) : ℂ)‖ ≤ C * t ^ (α n - 1)) :
    IntegrableOn (fun t => f (x * t) * q t) (Ioc 0 b) ∧
    ‖(∫ t in Ioc 0 b, f (x * t) * q t) - ∑ s ∈ Finset.range n,
        a s * ((x ^ (-α s) : ℝ) : ℂ) * ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f u‖ ≤
      (C + ∑ s ∈ Finset.range n, ‖a s‖ * b ^ (α s - α n)) *
        (∫ u in Ioi 0, u ^ (α n - 1) * ‖f u‖) * x ^ (-α n) := by
  set M' := ∫ u in Ioi 0, u ^ (α n - 1) * ‖f u‖ with hM'
  have hM'0 : 0 ≤ M' := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (norm_nonneg _)
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hr b ⟨hb, le_rfl⟩)
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hb _)).mp h
  have hfx : Measurable fun t : ℝ => f (x * t) := hf.comp (measurable_const_mul x)
  -- real majorants
  have hG : ∀ s ≤ n, IntegrableOn (fun t : ℝ => t ^ (α s - 1) * ‖f (x * t)‖) (Ioi 0) :=
    fun s hs => by
      simpa only [smul_eq_mul] using integrableOn_Ioi_rpow_smul_comp_mul (g := fun u => ‖f u‖)
        hx (by simpa only [smul_eq_mul] using hfα s hs)
  have hGint : ∫ t in Ioi 0, t ^ (α n - 1) * ‖f (x * t)‖ = x ^ (-α n) * M' := by
    simpa only [smul_eq_mul] using integral_Ioi_rpow_smul_comp_mul (fun u => ‖f u‖) (α n) hx
  -- the complex kernels `t^{αₛ−1} f(xt)`
  set K : ℕ → ℝ → ℂ := fun s t => ((t ^ (α s - 1) : ℝ) : ℂ) * f (x * t) with hKdef
  have hnK : ∀ s t, 0 < t → ‖K s t‖ = t ^ (α s - 1) * ‖f (x * t)‖ := fun s t ht => by
    rw [hKdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  have hKm : ∀ s, AEStronglyMeasurable (K s) volume := fun s =>
    ((Complex.measurable_ofReal.comp (measurable_id.pow_const _)).mul hfx).aestronglyMeasurable
  have hK : ∀ s ≤ n, IntegrableOn (K s) (Ioi 0) := fun s hs =>
    Integrable.mono' (hG s hs) (hKm s).restrict
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hnK s t ht).le)
  have hKint : ∀ s, ∫ t in Ioi 0, K s t =
      ((x ^ (-α s) : ℝ) : ℂ) * ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f u := fun s => by
    have h := integral_Ioi_rpow_smul_comp_mul f (α s) hx
    simp only [Complex.real_smul] at h
    exact h
  -- splitting `(0, ∞) = (0, b] ∪ (b, ∞)`
  have hdisj : Disjoint (Ioc (0 : ℝ) b) (Ioi b) :=
    disjoint_left.mpr fun t h1 h2 => not_lt.mpr h1.2 h2
  have hsplit : ∀ s ≤ n, ∫ t in Ioc 0 b, K s t = (∫ t in Ioi 0, K s t) - ∫ t in Ioi b, K s t :=
    fun s hs => by
      rw [← Ioc_union_Ioi_eq_Ioi hb.le, setIntegral_union hdisj measurableSet_Ioi
        ((hK s hs).mono_set Ioc_subset_Ioi_self) ((hK s hs).mono_set (Ioi_subset_Ioi hb.le))]
      ring
  -- the pieces `∫_b^∞`
  have hJ : ∀ s ≤ n, ‖∫ t in Ioi b, K s t‖ ≤ b ^ (α s - α n) * (x ^ (-α n) * M') := by
    intro s hs
    have hgi : IntegrableOn (fun t : ℝ => b ^ (α s - α n) * (t ^ (α n - 1) * ‖f (x * t)‖))
        (Ioi 0) := (hG n le_rfl).const_mul _
    calc ‖∫ t in Ioi b, K s t‖
        ≤ ∫ t in Ioi b, b ^ (α s - α n) * (t ^ (α n - 1) * ‖f (x * t)‖) := by
          refine norm_integral_le_of_norm_le (hgi.mono_set (Ioi_subset_Ioi hb.le))
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
          have ht0 : 0 < t := hb.trans ht
          rw [hnK s t ht0, show α s - 1 = (α s - α n) + (α n - 1) by ring,
            Real.rpow_add ht0, mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hb (le_of_lt ht) (sub_nonpos.mpr (hα s hs)))
            (mul_nonneg (Real.rpow_nonneg ht0.le _) (norm_nonneg _))
      _ ≤ ∫ t in Ioi 0, b ^ (α s - α n) * (t ^ (α n - 1) * ‖f (x * t)‖) :=
          setIntegral_mono_set hgi (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            mul_nonneg (Real.rpow_nonneg hb.le _)
              (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _)))
            (Ioi_subset_Ioi hb.le).eventuallyLE
      _ = _ := by rw [integral_const_mul, hGint]
  -- the remainder
  set P : ℝ → ℂ := fun t => ∑ s ∈ Finset.range n, a s * ((t ^ (α s - 1) : ℝ) : ℂ) with hPdef
  have hgr : IntegrableOn (fun t : ℝ => C * (t ^ (α n - 1) * ‖f (x * t)‖)) (Ioc 0 b) :=
    IntegrableOn.mono_set ((hG n le_rfl).const_mul C) Ioc_subset_Ioi_self
  have hRbd : ∀ t ∈ Ioc 0 b, ‖f (x * t) * (q t - P t)‖ ≤ C * (t ^ (α n - 1) * ‖f (x * t)‖) :=
    fun t ht => by
      rw [norm_mul]
      calc ‖f (x * t)‖ * ‖q t - P t‖ ≤ ‖f (x * t)‖ * (C * t ^ (α n - 1)) := by
            gcongr; exact hr t ht
        _ = _ := by ring
  have hPm : Measurable P := by
    rw [hPdef]
    exact Finset.measurable_sum _ fun s _ => measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_id.pow_const _))
  have hR : IntegrableOn (fun t => f (x * t) * (q t - P t)) (Ioc 0 b) :=
    Integrable.mono' hgr (hfx.mul (hq.sub hPm)).aestronglyMeasurable.restrict
      (ae_restrict_of_forall_mem measurableSet_Ioc hRbd)
  have hRn : ‖∫ t in Ioc 0 b, f (x * t) * (q t - P t)‖ ≤ C * (x ^ (-α n) * M') := by
    calc _ ≤ ∫ t in Ioc 0 b, C * (t ^ (α n - 1) * ‖f (x * t)‖) :=
          norm_integral_le_of_norm_le hgr (ae_restrict_of_forall_mem measurableSet_Ioc hRbd)
      _ ≤ ∫ t in Ioi 0, C * (t ^ (α n - 1) * ‖f (x * t)‖) :=
          setIntegral_mono_set ((hG n le_rfl).const_mul C)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
              have : 0 ≤ t ^ (α n - 1) := Real.rpow_nonneg (le_of_lt ht) _
              positivity) Ioc_subset_Ioi_self.eventuallyLE
      _ = _ := by rw [integral_const_mul, hGint]
  -- decomposition of `∫₀^b f(xt) q(t) dt`
  have hKb : ∀ s ∈ Finset.range n, IntegrableOn (fun t => a s * K s t) (Ioc 0 b) := fun s hs =>
    (((hK s (Finset.mem_range.mp hs).le)).mono_set Ioc_subset_Ioi_self).const_mul _
  have hpt : ∀ t, f (x * t) * q t =
      f (x * t) * (q t - P t) + ∑ s ∈ Finset.range n, a s * K s t := fun t => by
    rw [hPdef, hKdef]
    rw [mul_sub, Finset.mul_sum]
    have : ∀ s ∈ Finset.range n, f (x * t) * (a s * ((t ^ (α s - 1) : ℝ) : ℂ)) =
        a s * (((t ^ (α s - 1) : ℝ) : ℂ) * f (x * t)) := fun s _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  have hint : IntegrableOn (fun t => f (x * t) * q t) (Ioc 0 b) := by
    simp_rw [hpt]
    exact hR.add (integrable_finsetSum _ hKb)
  have hdec : ∫ t in Ioc 0 b, f (x * t) * q t =
      (∫ t in Ioc 0 b, f (x * t) * (q t - P t)) +
        ∑ s ∈ Finset.range n, a s * ((∫ t in Ioi 0, K s t) - ∫ t in Ioi b, K s t) := by
    simp_rw [hpt]
    rw [integral_add hR (integrable_finsetSum _ hKb), integral_finsetSum _ hKb]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [integral_const_mul, hsplit s (Finset.mem_range.mp hs).le]
  refine ⟨hint, ?_⟩
  have halg : (∫ t in Ioc 0 b, f (x * t) * q t) - ∑ s ∈ Finset.range n,
        a s * ((x ^ (-α s) : ℝ) : ℂ) * ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f u =
      (∫ t in Ioc 0 b, f (x * t) * (q t - P t)) -
        ∑ s ∈ Finset.range n, a s * ∫ t in Ioi b, K s t := by
    rw [hdec]
    simp only [hKint, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [halg]
  calc _ ≤ ‖∫ t in Ioc 0 b, f (x * t) * (q t - P t)‖ +
        ∑ s ∈ Finset.range n, ‖a s‖ * ‖∫ t in Ioi b, K s t‖ := by
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans ?_))
        exact Finset.sum_le_sum fun s _ => (norm_mul _ _).le
    _ ≤ C * (x ^ (-α n) * M') +
        ∑ s ∈ Finset.range n, ‖a s‖ * (b ^ (α s - α n) * (x ^ (-α n) * M')) := by
        gcongr with s hs
        exact hJ s (Finset.mem_range.mp hs).le
    _ = _ := by
        rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun s _ => by ring

/-! ### Watson's lemma (2.3.7–2.3.8) -/

/-- The exponents `αₛ = (s + λ)/μ` of 2.3.8. -/
noncomputable def watsonExp (lam μ : ℝ) (s : ℕ) : ℝ := ((s : ℝ) + lam) / μ

theorem watsonExp_succ {lam μ : ℝ} (hμ : 0 < μ) (s : ℕ) :
    watsonExp lam μ (s + 1) = watsonExp lam μ s + 1 / μ := by
  simp only [watsonExp]
  push_cast
  field_simp
  ring

theorem watsonExp_pos {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (s : ℕ) :
    0 < watsonExp lam μ s := div_pos (by positivity) hμ

theorem watsonExp_mono {lam μ : ℝ} (hμ : 0 < μ) {s n : ℕ} (h : s ≤ n) :
    watsonExp lam μ s ≤ watsonExp lam μ n :=
  div_le_div_of_nonneg_right (by have : (s : ℝ) ≤ n := by exact_mod_cast h
                                 linarith) hμ.le

/-- The `t`-exponent `(s + λ − μ)/μ` of 2.3.7 is `αₛ − 1`. -/
theorem watsonExp_sub_one {lam μ : ℝ} (hμ : 0 < μ) (s : ℕ) :
    ((s : ℝ) + lam - μ) / μ = watsonExp lam μ s - 1 := by
  simp only [watsonExp]
  field_simp

/-- 2.3.7 gives, for each `n`, a bound `|q(t) − ∑_{s<n} aₛ t^{αₛ−1}| ≤ C t^{αₙ−1}` on some
`(0, b]` with `b ≤ 1`. -/
theorem watson_bound {q : ℝ → ℂ} {a : ℕ → ℂ} {lam μ : ℝ} (hμ : 0 < μ)
    (hexp : IsGenAsympExpansionDLMF (𝓝[>] 0)
      (fun s t => ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) q
      (fun s t => a s * ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ))) (n : ℕ) :
    ∃ b C, 0 < b ∧ b ≤ 1 ∧ ∀ t ∈ Ioc 0 b,
      ‖q t - ∑ s ∈ Finset.range n, a s * ((t ^ (watsonExp lam μ s - 1) : ℝ) : ℂ)‖ ≤
        C * t ^ (watsonExp lam μ n - 1) := by
  obtain ⟨b, C, hb, hb1, h⟩ := exists_bound_of_isBigODLMF_nhdsGT (hexp.2 n)
    (fun t ht => ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne') zero_lt_one
  refine ⟨b, C, hb, hb1, fun t ht => ?_⟩
  have h1 := h t ht
  simp only [watsonExp_sub_one hμ, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)] at h1
  exact h1

theorem norm_cexp_neg_ofReal (u : ℝ) : ‖cexp (-(u : ℂ))‖ = Real.exp (-u) := by
  rw [Complex.norm_exp, neg_re, ofReal_re]

theorem integrableOn_rpow_mul_norm_cexp_neg {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun u : ℝ => u ^ (α - 1) * ‖cexp (-(u : ℂ))‖) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent hα).congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [norm_cexp_neg_ofReal]
  ring

theorem integral_rpow_mul_norm_cexp_neg {α : ℝ} (hα : 0 < α) :
    ∫ u : ℝ in Ioi 0, u ^ (α - 1) * ‖cexp (-(u : ℂ))‖ = Real.Gamma α := by
  rw [Real.Gamma_eq_integral hα]
  congr 1
  ext u
  rw [norm_cexp_neg_ofReal]
  ring

theorem integral_ofReal_rpow_mul_cexp_neg (α : ℝ) :
    ∫ u in Ioi 0, ((u ^ (α - 1) : ℝ) : ℂ) * cexp (-(u : ℂ)) =
      ((∫ u in Ioi 0, u ^ (α - 1) * Real.exp (-u) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  ext u
  push_cast
  rfl

theorem integral_ofReal_rpow_mul_cexp_neg_eq_Gamma {α : ℝ} (hα : 0 < α) :
    ∫ u in Ioi 0, ((u ^ (α - 1) : ℝ) : ℂ) * cexp (-(u : ℂ)) = (Real.Gamma α : ℂ) := by
  rw [integral_ofReal_rpow_mul_cexp_neg, Real.Gamma_eq_integral hα]
  congr 2
  ext u
  ring

/-- **DLMF 2.3.8 (Watson's lemma)**: if the Laplace transform 2.3.1 converges for all
sufficiently large `x` and `q(t) ∼ ∑ aₛ t^{(s+λ−μ)/μ}` as `t → 0+` (2.3.7, `λ, μ > 0`), then
`∫₀^∞ e^{−xt} q(t) dt ∼ ∑ Γ((s+λ)/μ) aₛ x^{−(s+λ)/μ}` as `x → +∞`. `q` need not be continuous:
it is measurable and integrable on every `[c, R]`, `c > 0` (integrability near `0` follows from
2.3.7), and the integral is the improper `lim_{R→∞} ∫₀^R` (`laplaceIntegral`). -/
theorem dlmf_2_3_8 {q : ℝ → ℂ} {a : ℕ → ℂ} {lam μ x₀ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
    (hq : Measurable q) (hloc : ∀ c R, 0 < c → IntervalIntegrable q volume c R)
    (hexp : IsGenAsympExpansionDLMF (𝓝[>] 0)
      (fun s t => ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) q
      (fun s t => a s * ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)))
    (hconv : ∀ x, x₀ ≤ x → ∃ L,
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(x : ℂ) * t) * q t) atTop (𝓝 L)) :
    IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))
      (laplaceIntegral q)
      (fun s x => (Real.Gamma (watsonExp lam μ s) : ℂ) * a s *
        ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ)) := by
  set α := watsonExp lam μ with hαdef
  refine ⟨?_, fun n => ?_⟩
  · simpa only [mul_one] using isAsympScale_rpow_neg_mul (one_div_pos.mpr hμ)
      (watsonExp_succ hμ) (w := fun _ => (1 : ℂ)) (Eventually.of_forall fun _ => one_ne_zero)
  obtain ⟨b, C, hb, -, hr⟩ := watson_bound hμ hexp n
  obtain ⟨b₀, C₀, hb₀, -, hr₀⟩ := watson_bound hμ hexp 0
  have hloc0 := intervalIntegrable_zero_of_bound hb₀
    (by linarith [watsonExp_pos hlam hμ 0] : -1 < α 0 - 1) hq.aestronglyMeasurable
    (by simpa using hr₀) (fun c R hc _ => hloc c R hc)
  obtain ⟨B, hB0, hBt⟩ := laplace_tail_exists hb hloc0 (hconv x₀ le_rfl)
  set f0 : ℝ → ℂ := fun u => cexp (-(u : ℂ)) with hf0
  set K := (C + ∑ s ∈ Finset.range n, ‖a s‖ * b ^ (α s - α n)) * Real.Gamma (α n)
  refine isBigODLMF_of_bound (K := 2 * B * Real.exp (x₀ * b) + K) ?_ ?_
  · filter_upwards [eventually_exp_neg_le_rpow_neg (α n) hb, eventually_gt_atTop (max x₀ 0)]
      with x hex hx
    have hxx₀ : x₀ < x := (le_max_left _ _).trans_lt hx
    have hx0 : 0 < x := (le_max_right _ _).trans_lt hx
    obtain ⟨L, hL⟩ := hconv x hxx₀.le
    have hF : laplaceIntegral q x = L := hL.limUnder_eq
    have htail := hBt x hxx₀ L hL
    obtain ⟨-, hNZ⟩ := watson_near_zero (f := f0) hb hx0 (by rw [hf0]; fun_prop) hq
      (fun s hs => watsonExp_mono hμ hs)
      (fun s _ => integrableOn_rpow_mul_norm_cexp_neg (watsonExp_pos hlam hμ s)) hr
    rw [hf0, integral_rpow_mul_norm_cexp_neg (watsonExp_pos hlam hμ n)] at hNZ
    have hI : ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * q t =
        ∫ t in Ioc 0 b, cexp (-((x * t : ℝ) : ℂ)) * q t := by
      rw [intervalIntegral.integral_of_le hb.le]
      congr 1
      ext t
      push_cast
      ring_nf
    have hsum : ∑ s ∈ Finset.range n, (Real.Gamma (α s) : ℂ) * a s *
        ((x ^ (-α s) : ℝ) : ℂ) = ∑ s ∈ Finset.range n, a s * ((x ^ (-α s) : ℝ) : ℂ) *
          ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * cexp (-(u : ℂ)) :=
      Finset.sum_congr rfl fun s _ => by
        rw [integral_ofReal_rpow_mul_cexp_neg_eq_Gamma (watsonExp_pos hlam hμ s)]
        ring
    have hφ : ‖((x ^ (-α n) : ℝ) : ℂ)‖ = x ^ (-α n) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hexp2 : Real.exp (-((x - x₀) * b)) = Real.exp (x₀ * b) * Real.exp (-(b * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hF, hsum, hφ]
    calc _ = ‖(L - ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * q t) +
          ((∫ t in Ioc 0 b, cexp (-((x * t : ℝ) : ℂ)) * q t) -
            ∑ s ∈ Finset.range n, a s * ((x ^ (-α s) : ℝ) : ℂ) *
              ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * cexp (-(u : ℂ)))‖ := by
          rw [hI]; ring_nf
      _ ≤ 2 * B * Real.exp (-((x - x₀) * b)) + K * x ^ (-α n) :=
          (norm_add_le _ _).trans (add_le_add htail hNZ)
      _ ≤ 2 * B * (Real.exp (x₀ * b) * x ^ (-α n)) + K * x ^ (-α n) := by
          rw [hexp2]; gcongr
      _ = _ := by ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'

/-! ### The logarithmic case (2.3.9) -/

theorem abs_log_le_rpow_neg_div {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hε : 0 < ε) :
    |Real.log t| ≤ t ^ (-ε) / ε := by
  have h := Real.abs_log_mul_self_rpow_lt t ε ht ht1 hε
  have hp : 0 < t ^ ε := Real.rpow_pos_of_pos ht ε
  rw [abs_mul, abs_of_pos hp, ← lt_div_iff₀ hp, div_div] at h
  have e : t ^ (-ε) / ε = 1 / (ε * t ^ ε) := by rw [Real.rpow_neg ht.le]; field_simp
  rw [e]
  exact h.le

theorem abs_log_le_rpow_add_rpow_neg {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    |Real.log t| ≤ (t ^ ε + t ^ (-ε)) / ε := by
  have h1 : 0 ≤ t ^ ε / ε := div_nonneg (Real.rpow_nonneg ht.le _) hε.le
  have h2 : 0 ≤ t ^ (-ε) / ε := div_nonneg (Real.rpow_nonneg ht.le _) hε.le
  rw [add_div]
  rcases le_or_gt t 1 with h | h
  · linarith [abs_log_le_rpow_neg_div ht h hε]
  · rw [abs_of_nonneg (Real.log_nonneg h.le)]
    linarith [Real.log_le_rpow_div ht.le hε]

theorem integrableOn_rpow_mul_norm_cexp_neg_mul_log {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun u : ℝ => u ^ (α - 1) * ‖cexp (-(u : ℂ)) * (Real.log u : ℂ)‖) (Ioi 0) := by
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = α / 2 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact half_pos hα
  have hg := ((Real.GammaIntegral_convergent (by linarith : 0 < α + ε)).add
    (Real.GammaIntegral_convergent (by rw [hεdef]; linarith : 0 < α - ε))).const_mul (1 / ε)
  refine Integrable.mono' hg ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_)
  · exact (((measurable_id.pow_const _).mul ((Complex.measurable_exp.comp
      (Complex.measurable_ofReal.neg)).mul (Complex.measurable_ofReal.comp
        Real.measurable_log)).norm)).aestronglyMeasurable
  · have hu0 : 0 < u := hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu0.le _)
      (norm_nonneg _)), norm_mul, norm_cexp_neg_ofReal, Complex.norm_real, Real.norm_eq_abs]
    show _ ≤ 1 / ε * (Real.exp (-u) * u ^ (α + ε - 1) + Real.exp (-u) * u ^ (α - ε - 1))
    have hl := abs_log_le_rpow_add_rpow_neg hu0 hε
    have hp : 0 ≤ u ^ (α - 1) * Real.exp (-u) :=
      mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.exp_pos _).le
    calc u ^ (α - 1) * (Real.exp (-u) * |Real.log u|)
        ≤ u ^ (α - 1) * Real.exp (-u) * ((u ^ ε + u ^ (-ε)) / ε) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hl hp
      _ = 1 / ε * (Real.exp (-u) * u ^ (α + ε - 1) + Real.exp (-u) * u ^ (α - ε - 1)) := by
          rw [show α + ε - 1 = (α - 1) + ε by ring, show α - ε - 1 = (α - 1) + -ε by ring,
            Real.rpow_add hu0, Real.rpow_add hu0]
          ring

/-- `Γ′(α) = ∫₀^∞ u^{α−1} ln u e^{−u} du` for `α > 0`. -/
theorem hasDerivAt_Gamma_integral {α : ℝ} (hα : 0 < α) :
    HasDerivAt Real.Gamma (∫ u in Ioi 0, u ^ (α - 1) * (Real.log u * Real.exp (-u))) α := by
  have hre : 0 < (α : ℂ).re := by simpa using hα
  have h := Complex.hasDerivAt_GammaIntegral hre
  have hev : Complex.Gamma =ᶠ[𝓝 (α : ℂ)] Complex.GammaIntegral := by
    filter_upwards [(continuous_re.isOpen_preimage _ (isOpen_Ioi (a := (0 : ℝ)))).mem_nhds hre]
      with s hs
    exact Complex.Gamma_eq_integral hs
  have hD : (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((α : ℂ) - 1) *
      ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) =
      ((∫ u in Ioi 0, u ^ (α - 1) * (Real.log u * Real.exp (-u)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [ofReal_mul, ofReal_cpow (le_of_lt hu), ofReal_mul]
    push_cast
    ring
  have h3 := (h.congr_of_eventuallyEq hev).real_of_complex
  rw [hD] at h3
  simp only [Complex.Gamma_ofReal, ofReal_re] at h3
  exact h3

theorem integral_ofReal_rpow_mul_cexp_neg_mul_log {α : ℝ} (hα : 0 < α) :
    ∫ u in Ioi 0, ((u ^ (α - 1) : ℝ) : ℂ) * (cexp (-(u : ℂ)) * (Real.log u : ℂ)) =
      ((deriv Real.Gamma α : ℝ) : ℂ) := by
  rw [(hasDerivAt_Gamma_integral hα).deriv, ← integral_complex_ofReal]
  congr 1
  ext u
  push_cast
  ring

/-- **DLMF 2.3.9**: under the hypotheses of Watson's lemma (2.3.7), if
`∫₀^∞ e^{−xt} q(t) ln t dt` converges for all sufficiently large `x`, then
`∫₀^∞ e^{−xt} q(t) ln t dt ∼ ∑ Γ′(αₛ) aₛ x^{−αₛ} − (ln x) ∑ Γ(αₛ) aₛ x^{−αₛ}`, `αₛ = (s+λ)/μ`,
as a generalized expansion with the scale `x^{−αₛ} ln x`. -/
theorem dlmf_2_3_9 {q : ℝ → ℂ} {a : ℕ → ℂ} {lam μ x₀ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
    (hq : Measurable q) (hloc : ∀ c R, 0 < c → IntervalIntegrable q volume c R)
    (hexp : IsGenAsympExpansionDLMF (𝓝[>] 0)
      (fun s t => ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) q
      (fun s t => a s * ((t ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)))
    (hconv : ∀ x, x₀ ≤ x → ∃ L, Tendsto
      (fun R => ∫ t in (0 : ℝ)..R, cexp (-(x : ℂ) * t) * (q t * Real.log t)) atTop (𝓝 L)) :
    IsGenAsympExpansionDLMF atTop
      (fun s x => ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ) * Real.log x)
      (laplaceIntegral fun t => q t * Real.log t)
      (fun s x => ((deriv Real.Gamma (watsonExp lam μ s) : ℝ) : ℂ) * a s *
          ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ) -
        (Real.log x : ℂ) * ((Real.Gamma (watsonExp lam μ s) : ℂ) * a s *
          ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))) := by
  set α := watsonExp lam μ with hαdef
  have hαp := watsonExp_pos hlam hμ
  refine ⟨isAsympScale_rpow_neg_mul (one_div_pos.mpr hμ) (watsonExp_succ hμ) ?_, fun n => ?_⟩
  · filter_upwards [eventually_gt_atTop 1] with x hx
    exact ofReal_ne_zero.mpr (Real.log_pos hx).ne'
  obtain ⟨b, C, hb, -, hr⟩ := watson_bound hμ hexp n
  obtain ⟨b₀, C₀, hb₀, hb₀1, hr₀⟩ := watson_bound hμ hexp 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at hr₀
  -- integrability of `q(t) ln t` on `[0, R]`
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = α 0 / 2 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact half_pos (hαp 0)
  have hC₀ : 0 ≤ C₀ := (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hb₀ _)).mp
    ((norm_nonneg _).trans (hr₀ b₀ ⟨hb₀, le_rfl⟩))
  have hbd0 : ∀ t ∈ Ioc 0 b₀, ‖q t * (Real.log t : ℂ)‖ ≤ C₀ / ε * t ^ (α 0 - ε - 1) := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show α 0 - ε - 1 = (α 0 - 1) + -ε by ring, Real.rpow_add ht.1]
    calc ‖q t‖ * |Real.log t| ≤ (C₀ * t ^ (α 0 - 1)) * (t ^ (-ε) / ε) :=
          mul_le_mul (hr₀ t ht) (abs_log_le_rpow_neg_div ht.1 (ht.2.trans hb₀1) hε)
            (abs_nonneg _) (mul_nonneg hC₀ (Real.rpow_nonneg ht.1.le _))
      _ = _ := by ring
  have hlocl : ∀ c R, 0 < c → c ≤ R →
      IntervalIntegrable (fun t => q t * (Real.log t : ℂ)) volume c R := fun c R hc hcR =>
    (hloc c R hc).mul_continuousOn (continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => by
        rw [uIcc_of_le hcR] at ht; exact (hc.trans_le ht.1).ne'))
  have hloc0 := intervalIntegrable_zero_of_bound hb₀
    (by rw [hεdef]; linarith [hαp 0] : -1 < α 0 - ε - 1)
    (hq.mul (Complex.measurable_ofReal.comp Real.measurable_log)).aestronglyMeasurable
    hbd0 hlocl
  obtain ⟨B, hB0, hBt⟩ := laplace_tail_exists hb hloc0 (hconv x₀ le_rfl)
  set f0 : ℝ → ℂ := fun u => cexp (-(u : ℂ)) with hf0
  set f1 : ℝ → ℂ := fun u => cexp (-(u : ℂ)) * (Real.log u : ℂ) with hf1
  set D := (C + ∑ s ∈ Finset.range n, ‖a s‖ * b ^ (α s - α n))
  set K₀ := D * Real.Gamma (α n)
  set K₁ := D * ∫ u : ℝ in Ioi 0, u ^ (α n - 1) * ‖f1 u‖
  have hK₀ : 0 ≤ K₀ := by
    have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hb _)).mp
      ((norm_nonneg _).trans (hr b ⟨hb, le_rfl⟩))
    have : 0 ≤ D := add_nonneg hC (Finset.sum_nonneg fun s _ =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hb.le _))
    exact mul_nonneg this (Real.Gamma_pos_of_pos (hαp n)).le
  refine isBigODLMF_of_bound (K := 2 * B * Real.exp (x₀ * b) + K₁ + K₀) ?_ ?_
  · filter_upwards [eventually_exp_neg_le_rpow_neg (α n) hb,
      eventually_gt_atTop (max x₀ (Real.exp 1))] with x hex hx
    have hxx₀ : x₀ < x := (le_max_left _ _).trans_lt hx
    have hxe : Real.exp 1 < x := (le_max_right _ _).trans_lt hx
    have hx0 : 0 < x := (Real.exp_pos 1).trans hxe
    have hlog1 : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe.le
    obtain ⟨L, hL⟩ := hconv x hxx₀.le
    have hF : laplaceIntegral (fun t => q t * Real.log t) x = L := hL.limUnder_eq
    have htail := hBt x hxx₀ L hL
    obtain ⟨hi0, hN0⟩ := watson_near_zero (f := f0) hb hx0 (by rw [hf0]; fun_prop) hq
      (fun s hs => watsonExp_mono hμ hs)
      (fun s _ => integrableOn_rpow_mul_norm_cexp_neg (hαp s)) hr
    obtain ⟨hi1, hN1⟩ := watson_near_zero (f := f1) hb hx0 (by
        rw [hf1]; exact (Complex.measurable_exp.comp Complex.measurable_ofReal.neg).mul
          (Complex.measurable_ofReal.comp Real.measurable_log)) hq
      (fun s hs => watsonExp_mono hμ hs)
      (fun s _ => integrableOn_rpow_mul_norm_cexp_neg_mul_log (hαp s)) hr
    rw [hf0, integral_rpow_mul_norm_cexp_neg (hαp n)] at hN0
    have hI : ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * (q t * Real.log t) =
        (∫ t in Ioc 0 b, f1 (x * t) * q t) -
          (Real.log x : ℂ) * ∫ t in Ioc 0 b, f0 (x * t) * q t := by
      rw [intervalIntegral.integral_of_le hb.le, ← integral_const_mul, ← integral_sub hi1
        (hi0.const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      simp only [hf0, hf1]
      rw [Real.log_mul hx0.ne' ht.1.ne']
      push_cast
      ring_nf
    have hsum : ∑ s ∈ Finset.range n, (((deriv Real.Gamma (α s) : ℝ) : ℂ) * a s *
          ((x ^ (-α s) : ℝ) : ℂ) - (Real.log x : ℂ) * ((Real.Gamma (α s) : ℂ) * a s *
          ((x ^ (-α s) : ℝ) : ℂ))) =
        (∑ s ∈ Finset.range n, a s * ((x ^ (-α s) : ℝ) : ℂ) *
          ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f1 u) -
        (Real.log x : ℂ) * ∑ s ∈ Finset.range n, a s * ((x ^ (-α s) : ℝ) : ℂ) *
          ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f0 u := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun s _ => ?_
        rw [hf1, integral_ofReal_rpow_mul_cexp_neg_mul_log (hαp s)]
        ring
      · refine Finset.sum_congr rfl fun s _ => ?_
        rw [hf0, integral_ofReal_rpow_mul_cexp_neg_eq_Gamma (hαp s)]
        ring
    have hφ : ‖((x ^ (-α n) : ℝ) : ℂ) * (Real.log x : ℂ)‖ = x ^ (-α n) * Real.log x := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
        Real.norm_of_nonneg (by linarith)]
    have hexp2 : Real.exp (-((x - x₀) * b)) = Real.exp (x₀ * b) * Real.exp (-(b * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hlx : ‖(Real.log x : ℂ)‖ = Real.log x := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hpx : 0 ≤ x ^ (-α n) := Real.rpow_nonneg hx0.le _
    rw [hF, hsum, hφ]
    calc _ = ‖(L - ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * (q t * Real.log t)) +
          ((∫ t in Ioc 0 b, f1 (x * t) * q t) - ∑ s ∈ Finset.range n,
            a s * ((x ^ (-α s) : ℝ) : ℂ) * ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f1 u) -
          (Real.log x : ℂ) * ((∫ t in Ioc 0 b, f0 (x * t) * q t) - ∑ s ∈ Finset.range n,
            a s * ((x ^ (-α s) : ℝ) : ℂ) *
              ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * f0 u)‖ := by
          rw [hI]; ring_nf
      _ ≤ 2 * B * Real.exp (-((x - x₀) * b)) + K₁ * x ^ (-α n) +
          Real.log x * (K₀ * x ^ (-α n)) := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add htail hN1)) ?_)
          rw [norm_mul, hlx]
          exact mul_le_mul_of_nonneg_left hN0 (by linarith)
      _ ≤ 2 * B * (Real.exp (x₀ * b) * (x ^ (-α n) * Real.log x)) +
          K₁ * (x ^ (-α n) * Real.log x) + Real.log x * (K₀ * x ^ (-α n)) := by
          rw [hexp2]
          have hK₁ : 0 ≤ K₁ := mul_nonneg (by
              have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hb _)).mp
                ((norm_nonneg _).trans (hr b ⟨hb, le_rfl⟩))
              exact add_nonneg hC (Finset.sum_nonneg fun s _ =>
                mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hb.le _)))
            (setIntegral_nonneg measurableSet_Ioi fun u hu =>
              mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (norm_nonneg _))
          gcongr
          · exact hex.trans (le_mul_of_one_le_right hpx hlog1)
          · exact le_mul_of_one_le_right hpx hlog1
      _ = _ := by ring
  · filter_upwards [eventually_gt_atTop 1] with x hx
    exact mul_ne_zero (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by linarith) _).ne')
      (ofReal_ne_zero.mpr (Real.log_pos hx).ne')

end Azurite.DLMF
