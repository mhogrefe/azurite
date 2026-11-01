/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3Watson
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# DLMF §2.3(iii): Laplace's method, core form (2.3.13–2.3.15)

* `laplace_method_core`: `∫_S e^{−xp(t)} q(t) dt ∼ e^{−xp(a)} ∑ Γ((s+λ)/μ) bₛ x^{−(s+λ)/μ}` when
  `p′ > 0` on `(a, a + δ₀)`, the minimum of `p` on `S` is approached only at `a`, the integral
  converges absolutely for large `x`, and `q/p′ ∼ ∑ bₛ v^{(s+λ−μ)/μ}` (2.3.16, with
  `v = p(t) − p(a)`, written as `t → a+`). Near `a` the substitution `w = v(t)`
  (`integral_image_eq_integral_abs_deriv_smul`) reduces to `watson_near_zero`; away from `a`
  the integrand is `O(e^{−x(p(a)+η)})`.
* `exists_bound_of_isBigODLMF_nhdsGT_at`: a pointwise bound on `(a, c]` from an `O`-relation.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory

namespace Azurite.DLMF

/-- An `O`-relation as `t → a+` gives a bound `‖R(t)‖ ≤ C‖φ(t)‖` on some `(a, c]`, `c ≤ b₁`. -/
theorem exists_bound_of_isBigODLMF_nhdsGT_at {a : ℝ} {R φ : ℝ → ℂ}
    (h : IsBigODLMF (𝓝[>] a) R φ) (hφ : ∀ᶠ t in 𝓝[>] a, φ t ≠ 0) {b₁ : ℝ} (hb₁ : a < b₁) :
    ∃ c C, a < c ∧ c ≤ b₁ ∧ ∀ t ∈ Ioc a c, ‖R t‖ ≤ C * ‖φ t‖ := by
  obtain ⟨C, hC⟩ := h
  rw [eventually_map] at hC
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hC.and hφ)
  have hu0 : a < u := hu
  refine ⟨min ((a + u) / 2) b₁, C, lt_min (by linarith) hb₁, min_le_right _ _, fun t ht => ?_⟩
  have htu : t < u := by linarith [ht.2, min_le_left ((a + u) / 2) b₁]
  obtain ⟨h1, hφt⟩ := hus ⟨ht.1, htu⟩
  have h1' : ‖R t / φ t‖ ≤ C := h1
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hφt)] at h1'
  exact h1'

/-- **Laplace's method**, core form of 2.3.15: `p` is differentiable with `p′ > 0` on
`(a, a + δ₀)`, `p(t) → p(a)` as `t → a+`, the minimum of `p` on the range `S` is approached only
at `a`, the integral converges absolutely for large `x`, and `q/p′` has the expansion 2.3.16 in
powers of `v = p(t) − p(a)` (written as `t → a+`, which is the same as `v → 0+`). -/
theorem laplace_method_core {p p' : ℝ → ℝ} {q : ℝ → ℂ} {b : ℕ → ℂ} {S : Set ℝ}
    {a lam μ δ₀ x₀ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (hδ₀ : 0 < δ₀)
    (hS : MeasurableSet S) (hSa : S ⊆ Ioi a) (hSc : Ioo a (a + δ₀) ⊆ S)
    (hp : ∀ t ∈ Ioo a (a + δ₀), HasDerivAt p (p' t) t)
    (hp'pos : ∀ t ∈ Ioo a (a + δ₀), 0 < p' t)
    (hp'c : ContinuousOn p' (Ioo a (a + δ₀))) (hqc : ContinuousOn q (Ioo a (a + δ₀)))
    (hpa : Tendsto p (𝓝[>] a) (𝓝 (p a)))
    (hmin : ∀ δ, 0 < δ → ∃ η, 0 < η ∧ ∀ t ∈ S, a + δ ≤ t → p a + η ≤ p t)
    (hint : ∀ x, x₀ ≤ x → IntegrableOn (fun t => (Real.exp (-(x * p t)) : ℂ) * q t) S)
    (hb : IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => (((p t - p a) ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) (fun t => q t / p' t)
      (fun s t => b s * (((p t - p a) ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ))) :
    IsGenAsympExpansionDLMF atTop
      (fun s x => (Real.exp (-(x * p a)) : ℂ) * ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))
      (fun x => ∫ t in S, (Real.exp (-(x * p t)) : ℂ) * q t)
      (fun s x => (Real.exp (-(x * p a)) : ℂ) * ((Real.Gamma (watsonExp lam μ s) : ℂ) * b s *
        ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))) := by
  set α := watsonExp lam μ with hαdef
  have hαp := watsonExp_pos hlam hμ
  refine ⟨?_, fun n => ?_⟩
  · have h := isAsympScale_rpow_neg_mul (one_div_pos.mpr hμ) (watsonExp_succ (lam := lam) hμ)
      (w := fun x => (Real.exp (-(x * p a)) : ℂ))
      (Eventually.of_forall fun x => ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    simpa only [mul_comm] using h
  set v : ℝ → ℝ := fun t => p t - p a with hvdef
  -- monotonicity of `p` on `[a, a + δ₀)`
  have hpc : ContinuousOn p (Ico a (a + δ₀)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      exact ((continuousWithinAt_Ioi_iff_Ici.mp hpa).mono Ico_subset_Ici_self)
    · exact (hp t ⟨h, ht.2⟩).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn p (Ico a (a + δ₀)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico _ _) hpc fun t ht => ?_
    rw [interior_Ico] at ht
    rw [(hp t ht).deriv]
    exact hp'pos t ht
  have hvpos : ∀ t ∈ Ioo a (a + δ₀), 0 < v t := fun t ht =>
    sub_pos.mpr (hmono (left_mem_Ico.mpr (by linarith)) ⟨ht.1.le, ht.2⟩ ht.1)
  -- the bound from 2.3.16
  have hev : ∀ᶠ t in 𝓝[>] a,
      (((p t - p a) ^ (((n : ℝ) + lam - μ) / μ) : ℝ) : ℂ) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : a < a + δ₀)] with t ht
    exact ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hvpos t ht) _).ne'
  obtain ⟨c, C, hac, hc1, hr⟩ := exists_bound_of_isBigODLMF_nhdsGT_at (hb.2 n) hev
    (by linarith : a < a + δ₀ / 2)
  have hcδ : c < a + δ₀ := by linarith
  have hIoc : Ioc a c ⊆ Ioo a (a + δ₀) := fun t ht => ⟨ht.1, ht.2.trans_lt hcδ⟩
  set P : ℝ → ℂ := fun w => ∑ s ∈ Finset.range n, b s * ((w ^ (α s - 1) : ℝ) : ℂ) with hPdef
  have hR : ∀ t ∈ Ioc a c, ‖q t / p' t - P (v t)‖ ≤ C * v t ^ (α n - 1) := fun t ht => by
    have h := hr t ht
    have hv0 : 0 < p t - p a := hvpos t (hIoc ht)
    simp only [watsonExp_sub_one hμ, Complex.norm_real] at h
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)] at h
    exact h
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right
    (Real.rpow_pos_of_pos (hvpos c (hIoc ⟨hac, le_rfl⟩)) _)).mp
    ((norm_nonneg _).trans (hR c ⟨hac, le_rfl⟩))
  -- the substitution `w = v(t)` on `(a, c]`
  have hv' : ∀ t ∈ Ioc a c, HasDerivWithinAt v (p' t) (Ioc a c) t := fun t ht =>
    ((hp t (hIoc ht)).sub_const (p a)).hasDerivWithinAt
  have hinj : InjOn v (Ioc a c) := fun t ht u hu h =>
    hmono.injOn (Ioc_subset_Ioo_right hcδ |>.trans Ioo_subset_Ico_self ht)
      (Ioc_subset_Ioo_right hcδ |>.trans Ioo_subset_Ico_self hu) (by
        simp only [hvdef] at h; linarith)
  set V := v c with hVdef
  have hV : 0 < V := hvpos c (hIoc ⟨hac, le_rfl⟩)
  have himg : v '' Ioc a c = Ioc 0 V := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hvpos t (hIoc ht), sub_le_sub_right (hmono.monotoneOn ⟨ht.1.le, by linarith [ht.2]⟩
        ⟨hac.le, hcδ⟩ ht.2) _⟩
    · rintro ⟨hw0, hwV⟩
      have hvc : ContinuousOn v (Icc a c) :=
        (hpc.mono fun t ht => ⟨ht.1, ht.2.trans_lt hcδ⟩).sub continuousOn_const
      obtain ⟨t, ht, htw⟩ := intermediate_value_Icc hac.le hvc
        ⟨by simp only [hvdef, sub_self]; exact hw0.le, hwV⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, htw⟩
      rintro rfl
      simp only [hvdef, sub_self] at htw
      exact hw0.ne htw
  have habs : ∀ t ∈ Ioc a c, |p' t| = p' t := fun t ht => abs_of_pos (hp'pos t (hIoc ht))
  -- the tail
  obtain ⟨η, hη, hηp⟩ := hmin (c - a) (by linarith)
  set M₀ := ∫ t in S, ‖(Real.exp (-(x₀ * p t)) : ℂ) * q t‖
  have hM₀ : 0 ≤ M₀ := integral_nonneg fun _ => norm_nonneg _
  set f0 : ℝ → ℂ := fun u => cexp (-(u : ℂ)) with hf0
  set K₁ := (0 + ∑ s ∈ Finset.range n, ‖b s‖ * V ^ (α s - α n)) * Real.Gamma (α n)
  set K := C * Real.Gamma (α n) + K₁ + Real.exp (x₀ * (p a + η)) * M₀
  refine isBigODLMF_of_bound (K := K) ?_ ?_
  · filter_upwards [eventually_exp_neg_le_rpow_neg (α n) hη, eventually_gt_atTop (max x₀ 0)]
      with x hex hx
    have hxx₀ : x₀ < x := (le_max_left _ _).trans_lt hx
    have hx0 : 0 < x := (le_max_right _ _).trans_lt hx
    -- near `0` in the `w` variable
    obtain ⟨hgi, hN⟩ := watson_near_zero (f := f0) (q := P) (C := 0) hV hx0
      (by rw [hf0]; fun_prop)
      (Finset.measurable_sum _ fun s _ => measurable_const.mul
        (Complex.measurable_ofReal.comp (measurable_id.pow_const _)))
      (fun s hs => watsonExp_mono hμ hs)
      (fun s _ => integrableOn_rpow_mul_norm_cexp_neg (hαp s))
      (fun t _ => by rw [hPdef, sub_self, norm_zero, zero_mul])
    rw [hf0, integral_rpow_mul_norm_cexp_neg (hαp n)] at hN
    -- the real majorant `w^{αₙ−1} e^{−xw}`
    have hh : IntegrableOn (fun w : ℝ => w ^ (α n - 1) * Real.exp (-(x * w))) (Ioi 0) := by
      simpa only [smul_eq_mul] using integrableOn_Ioi_rpow_smul_comp_mul
        (g := fun u => Real.exp (-u)) hx0
        (by simpa only [smul_eq_mul, mul_comm] using Real.GammaIntegral_convergent (hαp n))
    have hhint : ∫ w in Ioi 0, w ^ (α n - 1) * Real.exp (-(x * w)) =
        x ^ (-α n) * Real.Gamma (α n) := by
      have h := integral_Ioi_rpow_smul_comp_mul (fun u => Real.exp (-u)) (α n) hx0
      simp only [smul_eq_mul] at h
      rw [h, Real.Gamma_eq_integral (hαp n)]
      congr 2
      ext u
      ring
    set h : ℝ → ℝ := fun w => C * (w ^ (α n - 1) * Real.exp (-(x * w))) with hhdef
    have hhV : IntegrableOn h (v '' Ioc a c) := by
      rw [himg]; exact IntegrableOn.mono_set (hh.const_mul C) Ioc_subset_Ioi_self
    have hhc := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hv'
      hinj h).mp hhV
    -- continuity on `(a, c]`
    have hvc : ContinuousOn v (Ioc a c) := fun t ht =>
      ((hp t (hIoc ht)).sub_const (p a)).continuousAt.continuousWithinAt
    have hPc : ContinuousOn (fun t => P (v t)) (Ioc a c) := by
      rw [hPdef]
      refine continuousOn_finsetSum _ fun s _ => continuousOn_const.mul
        (continuous_ofReal.comp_continuousOn (hvc.rpow_const fun t ht =>
          Or.inl (hvpos t (hIoc ht)).ne'))
    have hRc : ContinuousOn (fun t => (p' t * Real.exp (-(x * v t)) : ℂ) *
        (q t / p' t - P (v t))) (Ioc a c) := by
      refine ContinuousOn.mul ?_ (((hqc.mono hIoc).div (continuous_ofReal.comp_continuousOn
        (hp'c.mono hIoc)) fun t ht => ofReal_ne_zero.mpr (hp'pos t (hIoc ht)).ne').sub hPc)
      exact (continuous_ofReal.comp_continuousOn (hp'c.mono hIoc)).mul
        (continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
          ((continuousOn_const.mul hvc).neg)))
    have hbd1 : ∀ t ∈ Ioc a c, ‖(p' t * Real.exp (-(x * v t)) : ℂ) * (q t / p' t - P (v t))‖ ≤
        |p' t| • h (v t) := fun t ht => by
      have hp0 := (hp'pos t (hIoc ht)).le
      rw [norm_mul, norm_mul, habs t ht, smul_eq_mul, hhdef, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg hp0, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc p' t * Real.exp (-(x * v t)) * ‖q t / p' t - P (v t)‖
          ≤ p' t * Real.exp (-(x * v t)) * (C * v t ^ (α n - 1)) :=
            mul_le_mul_of_nonneg_left (hR t ht) (mul_nonneg hp0 (Real.exp_pos _).le)
        _ = _ := by ring
    have hI1 : IntegrableOn (fun t => (p' t * Real.exp (-(x * v t)) : ℂ) *
        (q t / p' t - P (v t))) (Ioc a c) :=
      Integrable.mono' hhc (hRc.aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hbd1)
    have hn1 : ‖∫ t in Ioc a c, (p' t * Real.exp (-(x * v t)) : ℂ) * (q t / p' t - P (v t))‖ ≤
        C * Real.Gamma (α n) * x ^ (-α n) := by
      calc _ ≤ ∫ t in Ioc a c, |p' t| • h (v t) :=
            norm_integral_le_of_norm_le hhc (ae_restrict_of_forall_mem measurableSet_Ioc hbd1)
        _ = ∫ w in Ioc 0 V, h w := by
            rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hv' hinj]
        _ ≤ ∫ w in Ioi 0, h w := setIntegral_mono_set (hh.const_mul C)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun w hw =>
              mul_nonneg hC (mul_nonneg (Real.rpow_nonneg (le_of_lt hw) _)
                (Real.exp_pos _).le)) Ioc_subset_Ioi_self.eventuallyLE
        _ = _ := by rw [hhdef, integral_const_mul, hhint]; ring
    -- the formal terms
    set g : ℝ → ℂ := fun w => f0 (x * w) * P w with hgdef
    have hgV : IntegrableOn g (v '' Ioc a c) := by rw [himg]; exact hgi
    have hg2 := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hv'
      hinj g).mp hgV
    have hint2 : ∫ t in Ioc a c, |p' t| • g (v t) = ∫ w in Ioc 0 V, f0 (x * w) * P w := by
      rw [← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hv' hinj, himg]
    -- the head `∫_a^c`
    have hhead : ∫ t in Ioc a c, (Real.exp (-(x * p t)) : ℂ) * q t =
        (Real.exp (-(x * p a)) : ℂ) *
          ((∫ t in Ioc a c, (p' t * Real.exp (-(x * v t)) : ℂ) * (q t / p' t - P (v t))) +
            ∫ w in Ioc 0 V, f0 (x * w) * P w) := by
      rw [← hint2, ← integral_add hI1 hg2, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have hp0 : (p' t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hp'pos t (hIoc ht)).ne'
      simp only [hgdef, hf0, habs t ht, Complex.real_smul]
      rw [show p t = p a + v t by simp [hvdef], mul_add, neg_add, Real.exp_add]
      push_cast
      field_simp
      ring
    -- the tail `∫_{S ∖ (a, c]}`
    have hsub : Ioc a c ⊆ S := hIoc.trans hSc
    have htail : ‖∫ t in S \ Ioc a c, (Real.exp (-(x * p t)) : ℂ) * q t‖ ≤
        Real.exp (-((x - x₀) * (p a + η))) * M₀ := by
      have hg0 := ((hint x₀ le_rfl).norm.const_mul (Real.exp (-((x - x₀) * (p a + η)))))
      calc _ ≤ ∫ t in S \ Ioc a c, Real.exp (-((x - x₀) * (p a + η))) *
            ‖(Real.exp (-(x₀ * p t)) : ℂ) * q t‖ := by
            refine norm_integral_le_of_norm_le (IntegrableOn.mono_set hg0 sdiff_subset)
              (ae_restrict_of_forall_mem (hS.diff measurableSet_Ioc) fun t ht => ?_)
            have hta : a < t := hSa ht.1
            have htc : c < t := by
              by_contra hct; exact ht.2 ⟨hta, not_lt.mp hct⟩
            have hpt := hηp t ht.1 (by linarith)
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
              ← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            nlinarith
        _ ≤ ∫ t in S, Real.exp (-((x - x₀) * (p a + η))) *
            ‖(Real.exp (-(x₀ * p t)) : ℂ) * q t‖ :=
            setIntegral_mono_set hg0 (ae_of_all _ fun t => by positivity)
              sdiff_subset.eventuallyLE
        _ = _ := integral_const_mul _ _
    -- assemble
    have hsplit := integral_inter_add_sdiff (μ := volume) (s := S) (t := Ioc a c)
      measurableSet_Ioc (hint x hxx₀.le)
    rw [inter_eq_right.mpr hsub, hhead] at hsplit
    have hsum : ∑ s ∈ Finset.range n, (Real.exp (-(x * p a)) : ℂ) *
        ((Real.Gamma (α s) : ℂ) * b s * ((x ^ (-α s) : ℝ) : ℂ)) =
        (Real.exp (-(x * p a)) : ℂ) * ∑ s ∈ Finset.range n, b s * ((x ^ (-α s) : ℝ) : ℂ) *
          ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * cexp (-(u : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [integral_ofReal_rpow_mul_cexp_neg_eq_Gamma (hαp s)]
      ring
    have hφ : ‖(Real.exp (-(x * p a)) : ℂ) * ((x ^ (-α n) : ℝ) : ℂ)‖ =
        Real.exp (-(x * p a)) * x ^ (-α n) := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hE : (Real.exp (-((x - x₀) * (p a + η)))) =
        Real.exp (-(x * p a)) * (Real.exp (x₀ * (p a + η)) * Real.exp (-(η * x))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hea : ‖(Real.exp (-(x * p a)) : ℂ)‖ = Real.exp (-(x * p a)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [← hsplit, hsum, hφ]
    have he0 := Real.exp_pos (-(x * p a))
    calc _ = ‖(Real.exp (-(x * p a)) : ℂ) *
          ((∫ t in Ioc a c, (p' t * Real.exp (-(x * v t)) : ℂ) * (q t / p' t - P (v t))) +
            ((∫ w in Ioc 0 V, f0 (x * w) * P w) - ∑ s ∈ Finset.range n,
              b s * ((x ^ (-α s) : ℝ) : ℂ) *
                ∫ u in Ioi 0, ((u ^ (α s - 1) : ℝ) : ℂ) * cexp (-(u : ℂ)))) +
          ∫ t in S \ Ioc a c, (Real.exp (-(x * p t)) : ℂ) * q t‖ := by
          ring_nf
      _ ≤ Real.exp (-(x * p a)) * (C * Real.Gamma (α n) * x ^ (-α n) + K₁ * x ^ (-α n)) +
          Real.exp (-((x - x₀) * (p a + η))) * M₀ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ htail)
          rw [norm_mul, hea]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hn1 ?_))
            he0.le
          simpa only [hf0] using hN
      _ ≤ Real.exp (-(x * p a)) * (C * Real.Gamma (α n) * x ^ (-α n) + K₁ * x ^ (-α n)) +
          Real.exp (-(x * p a)) * (Real.exp (x₀ * (p a + η)) * x ^ (-α n)) * M₀ := by
          rw [hE]
          gcongr
      _ = _ := by ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne')
      (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne')

end Azurite.DLMF
