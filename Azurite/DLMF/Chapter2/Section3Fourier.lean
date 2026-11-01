/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section2Reversion
import Azurite.DLMF.Chapter1.Section4

/-!
# DLMF §2.3(i): integration by parts for Fourier integrals (2.3.4–2.3.6)

"`q` infinitely differentiable on `[a, b]`" (or `[a, ∞)`) is modelled as `ContDiffOn ℝ ∞ q U` on
an open `U` containing the interval. The expansions are generalized expansions
(`IsGenAsympExpansionDLMF`) with the scale `invPowScale s x = x^{-(s+1)}`.

* `fourier_ibp`, `fourier_ibp_iter`: repeated integration by parts of `∫_a^b e^{ixt} q(t) dt`.
* `dlmf_2_3_4`:
  `∫_a^b e^{ixt} q(t) dt ∼ e^{iax} ∑ q⁽ˢ⁾(a)(i/x)^{s+1} − e^{ibx} ∑ q⁽ˢ⁾(b)(i/x)^{s+1}`;
  `dlmf_2_3_4_error`: the `n`th error term is at most `x⁻ⁿ 𝒱_{a,b}(q⁽ⁿ⁻¹⁾)`.
* `dlmf_2_3_5`: for `b = ∞`, if each `∫_a^∞ e^{ixt} q⁽ˢ⁾(t) dt` converges uniformly for large `x`
  (`TendstoUniformlyOn` of the partial integrals), the improper integral `fourierIoiIntegral` has
  the expansion `e^{iax} ∑ q⁽ˢ⁾(a)(i/x)^{s+1}`; `dlmf_2_3_5_error`: error at most
  `x⁻ⁿ 𝒱_{a,∞}(q⁽ⁿ⁻¹⁾)` when `q⁽ⁿ⁾` is integrable. The boundary terms at infinity vanish because
  `e^{iR}` has no limit (`not_tendsto_exp_I_mul`).
* `dlmf_2_3_6`: `𝒱_{a,b}(f) = ∫_a^b |f′(t)| dt` (this is `dlmf_1_4_34`).
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

/-! ### Iterated derivatives on an open set -/

theorem hasDerivAt_iteratedDeriv_of_contDiffOn {q : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q U) (s : ℕ) {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (iteratedDeriv s q) (iteratedDeriv (s + 1) q t) t := by
  have hlt : ((s : ℕ) : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.natCast_lt_top s
  have hd := (hq.differentiableOn_iteratedDerivWithin hlt hU.uniqueDiffOn) t ht
  have heq : iteratedDerivWithin s q U =ᶠ[𝓝 t] iteratedDeriv s q :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds ht) (iteratedDerivWithin_of_isOpen hU)
  have hda : DifferentiableAt ℝ (iteratedDeriv s q) t :=
    ((hd.differentiableAt (hU.mem_nhds ht)).congr_of_eventuallyEq heq.symm)
  rw [iteratedDeriv_succ]
  exact hda.hasDerivAt

theorem continuousOn_iteratedDeriv_of_contDiffOn {q : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q U) (s : ℕ) : ContinuousOn (iteratedDeriv s q) U := fun _ ht =>
  (hasDerivAt_iteratedDeriv_of_contDiffOn hU hq s ht).continuousAt.continuousWithinAt

/-! ### Finite Fourier integrals (2.3.4) -/

/-- The terms `(i/x)^{s+1}(e^{iax}q^{(s)}(a) − e^{ibx}q^{(s)}(b))` of 2.3.4. -/
noncomputable def fourierTerm (q : ℝ → ℂ) (a b : ℝ) (s : ℕ) (x : ℝ) : ℂ :=
  (I / x) ^ (s + 1) *
    (cexp (I * a * x) * iteratedDeriv s q a - cexp (I * b * x) * iteratedDeriv s q b)

section Finite

variable {q : ℝ → ℂ} {a b : ℝ} {U : Set ℝ} (hab : a ≤ b) (hU : IsOpen U) (hIU : Icc a b ⊆ U)
  (hq : ContDiffOn ℝ ∞ q U)
include hab hU hIU hq

/-- One integration by parts. -/
theorem fourier_ibp (s : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ∫ t in a..b, cexp (I * x * t) * iteratedDeriv s q t =
      (I / x) * (cexp (I * a * x) * iteratedDeriv s q a - cexp (I * b * x) * iteratedDeriv s q b) +
        (I / x) * ∫ t in a..b, cexp (I * x * t) * iteratedDeriv (s + 1) q t := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  have hIx : I * (x : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hxc
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => cexp (I * x * t) / (I * x)) (cexp (I * x * t)) t := by
    intro t
    have := (((hasDerivAt_id t).ofReal_comp.const_mul (I * x)).cexp).div_const (I * x)
    convert this using 1
    · rfl
    · rw [id_eq, Complex.ofReal_one, mul_one, mul_div_assoc, div_self hIx, mul_one]
  have hu : ∀ t ∈ uIcc a b, HasDerivAt (iteratedDeriv s q) (iteratedDeriv (s + 1) q t) t :=
    fun t ht => hasDerivAt_iteratedDeriv_of_contDiffOn hU hq s (hIU (by rwa [uIcc_of_le hab] at ht))
  have hcont : ∀ k, ContinuousOn (iteratedDeriv k q) (uIcc a b) := fun k =>
    (continuousOn_iteratedDeriv_of_contDiffOn hU hq k).mono (by rw [uIcc_of_le hab]; exact hIU)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu (fun t _ => hv t)
    ((hcont (s + 1)).intervalIntegrable)
    ((show Continuous fun t : ℝ => cexp (I * x * t) by fun_prop).intervalIntegrable a b)
  have e1 : ∫ t in a..b, cexp (I * x * t) * iteratedDeriv s q t =
      ∫ t in a..b, iteratedDeriv s q t * cexp (I * x * t) :=
    intervalIntegral.integral_congr fun t _ => mul_comm _ _
  have e2 : ∫ t in a..b, iteratedDeriv (s + 1) q t * (cexp (I * x * t) / (I * x)) =
      (1 / (I * x)) * ∫ t in a..b, cexp (I * x * t) * iteratedDeriv (s + 1) q t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [e1, h, e2]
  have hI : (1 : ℂ) / (I * x) = -(I / x) := by
    field_simp; rw [I_sq]; ring
  rw [hI, show I * (x : ℂ) * b = I * b * x by ring, show I * (x : ℂ) * a = I * a * x by ring]
  field_simp
  simp only [I_sq]
  ring

/-- `n` integrations by parts: `∫_a^b e^{ixt}q = ∑_{s<n} (term s) + (i/x)ⁿ ∫_a^b e^{ixt}q^{(n)}`. -/
theorem fourier_ibp_iter (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ∫ t in a..b, cexp (I * x * t) * q t =
      ∑ s ∈ Finset.range n, fourierTerm q a b s x +
        (I / x) ^ n * ∫ t in a..b, cexp (I * x * t) * iteratedDeriv n q t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, fourier_ibp hab hU hIU hq n hx, Finset.sum_range_succ, fourierTerm]
    ring

/-- The error after `n` terms is `(i/x)ⁿ ∫_a^b e^{ixt}q^{(n)}`, bounded by
`x^{−n} ∫_a^b |q^{(n)}|`. -/
theorem fourier_error_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖(∫ t in a..b, cexp (I * x * t) * q t) - ∑ s ∈ Finset.range n, fourierTerm q a b s x‖ ≤
      x⁻¹ ^ n * ∫ t in a..b, ‖iteratedDeriv n q t‖ := by
  rw [fourier_ibp_iter hab hU hIU hq n hx.ne', add_sub_cancel_left, norm_mul, norm_pow, norm_div,
    norm_I, norm_real, Real.norm_of_nonneg hx.le, one_div]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [norm_mul]
  rw [show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
    one_mul]

end Finite

/-! ### The scale `x^{−(s+1)}` -/

/-- The scale `x^{−1}, x^{−2}, …` as `x → +∞`. -/
noncomputable def invPowScale (s : ℕ) (x : ℝ) : ℂ := ((x : ℂ)⁻¹) ^ (s + 1)

theorem tendsto_ofReal_inv_atTop : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
  have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  simpa [Function.comp_def] using this

theorem isAsympScale_invPowScale : IsAsympScaleDLMF atTop invPowScale := fun s => by
  refine tendsto_ofReal_inv_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  simp only [invPowScale]
  rw [pow_succ _ (s + 1), mul_div_cancel_left₀ _ (pow_ne_zero _ (inv_ne_zero this))]

theorem isBigODLMF_invPowScale {E : ℝ → ℂ} {n : ℕ} {C : ℝ}
    (h : ∀ᶠ x in atTop, ‖E x‖ ≤ C * x⁻¹ ^ (n + 1)) : IsBigODLMF atTop E (invPowScale n) := by
  refine ⟨C, eventually_map.mpr ?_⟩
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  have hp : 0 < x⁻¹ ^ (n + 1) := by positivity
  simp only [invPowScale, norm_div, norm_pow, norm_inv, norm_real, Real.norm_of_nonneg hx0.le]
  rw [div_le_iff₀ hp]; exact hx

section Finite

variable {q : ℝ → ℂ} {a b : ℝ} {U : Set ℝ} (hab : a ≤ b) (hU : IsOpen U) (hIU : Icc a b ⊆ U)
  (hq : ContDiffOn ℝ ∞ q U)
include hab hU hIU hq

omit hab hU hIU hq in
theorem norm_fourierTerm_le (s : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖fourierTerm q a b s x‖ ≤
      (‖iteratedDeriv s q a‖ + ‖iteratedDeriv s q b‖) * x⁻¹ ^ (s + 1) := by
  have he : ∀ c : ℝ, ‖cexp (I * c * x)‖ = 1 := fun c => by
    rw [show I * (c : ℂ) * x = ((c * x : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]
  rw [fourierTerm, norm_mul, norm_pow, norm_div, norm_I, norm_real, Real.norm_of_nonneg hx.le,
    one_div, mul_comm]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, he, he, one_mul, one_mul]

/-- **DLMF 2.3.4**:
`∫_a^b e^{ixt}q(t) dt ∼ e^{iax}∑ q^{(s)}(a)(i/x)^{s+1} − e^{ibx}∑ q^{(s)}(b)(i/x)^{s+1}`
as `x → +∞`, as a generalized expansion with respect to the scale `x^{−(s+1)}`. -/
theorem dlmf_2_3_4 :
    IsGenAsympExpansionDLMF atTop invPowScale (fun x => ∫ t in a..b, cexp (I * x * t) * q t)
      (fourierTerm q a b) := by
  refine ⟨isAsympScale_invPowScale, fun n => isBigODLMF_invPowScale (C :=
    ‖iteratedDeriv n q a‖ + ‖iteratedDeriv n q b‖ + ∫ t in a..b, ‖iteratedDeriv (n + 1) q t‖) ?_⟩
  filter_upwards [eventually_gt_atTop 0] with x hx
  have h1 := fourier_error_le hab hU hIU hq (n + 1) hx
  have h2 := norm_fourierTerm_le (q := q) (a := a) (b := b) n hx
  rw [Finset.sum_range_succ] at h1
  calc ‖(∫ t in a..b, cexp (I * x * t) * q t) - ∑ s ∈ Finset.range n, fourierTerm q a b s x‖
      = ‖((∫ t in a..b, cexp (I * x * t) * q t) -
          (∑ s ∈ Finset.range n, fourierTerm q a b s x + fourierTerm q a b n x)) +
          fourierTerm q a b n x‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ (x⁻¹ ^ (n + 1) * ∫ t in a..b, ‖iteratedDeriv (n + 1) q t‖) +
        (‖iteratedDeriv n q a‖ + ‖iteratedDeriv n q b‖) * x⁻¹ ^ (n + 1) := add_le_add h1 h2
    _ = _ := by ring

/-- **DLMF §2.3(i)**, error bound for 2.3.4: for `n ≥ 1` and `x > 0` the `n`th error term is at
most `x^{−n} 𝒱_{a,b}(q^{(n−1)})` (2.3.6). -/
theorem dlmf_2_3_4_error {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ‖(∫ t in a..b, cexp (I * x * t) * q t) - ∑ s ∈ Finset.range n, fourierTerm q a b s x‖ ≤
      x⁻¹ ^ n * (eVariationOn (iteratedDeriv (n - 1) q) (Icc a b)).toReal := by
  refine (fourier_error_le hab hU hIU hq n hx).trans ?_
  gcongr
  rcases hab.lt_or_eq with hlt | heq
  · have hc := (continuousOn_iteratedDeriv_of_contDiffOn hU hq n).mono hIU
    have hv := dlmf_1_4_34 (f := iteratedDeriv (n - 1) q) (f' := iteratedDeriv n q) hlt
      ((continuousOn_iteratedDeriv_of_contDiffOn hU hq (n - 1)).mono hIU)
      (fun t ht => by
        have := hasDerivAt_iteratedDeriv_of_contDiffOn hU hq (n - 1) (hIU (Ioo_subset_Icc_self ht))
        rwa [show n - 1 + 1 = n by omega] at this)
      (hc.mono Ioo_subset_Icc_self)
      ((hc.norm.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
    rw [hv, ENNReal.toReal_ofReal
      (intervalIntegral.integral_nonneg hlt.le fun _ _ => norm_nonneg _)]
  · subst heq; simp

end Finite

/-! ### Half-infinite Fourier integrals (2.3.5) -/

/-- `e^{iR}` has no limit as `R → +∞`. -/
theorem not_tendsto_exp_I_mul : ¬ ∃ L : ℂ, Tendsto (fun R : ℝ => cexp (I * R)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  have h2 : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi) + Real.pi) atTop atTop :=
    tendsto_atTop_add_const_right _ _ h1
  have c1 : ∀ k : ℕ, ((fun R : ℝ => cexp (I * R)) ∘ fun k : ℕ => (k : ℝ) * (2 * Real.pi)) k = 1 :=
    fun k => by
      simp only [Function.comp_apply]
      rw [show I * (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * I) by
        push_cast; ring, exp_nat_mul_two_pi_mul_I]
  have c2 : ∀ k : ℕ,
      ((fun R : ℝ => cexp (I * R)) ∘ fun k : ℕ => (k : ℝ) * (2 * Real.pi) + Real.pi) k = -1 :=
    fun k => by
      simp only [Function.comp_apply]
      rw [show I * (((k : ℝ) * (2 * Real.pi) + Real.pi : ℝ) : ℂ) =
          (k : ℂ) * (2 * Real.pi * I) + Real.pi * I by push_cast; ring, Complex.exp_add,
        exp_nat_mul_two_pi_mul_I, exp_pi_mul_I, one_mul]
  have e1 := tendsto_nhds_unique tendsto_const_nhds ((hL.comp h1).congr c1)
  have e2 := tendsto_nhds_unique tendsto_const_nhds ((hL.comp h2).congr c2)
  have := e1.trans e2.symm
  norm_num at this

/-- The terms `e^{iax} q^{(s)}(a) (i/x)^{s+1}` of 2.3.5. -/
noncomputable def fourierTermIoi (q : ℝ → ℂ) (a : ℝ) (s : ℕ) (x : ℝ) : ℂ :=
  (I / x) ^ (s + 1) * (cexp (I * a * x) * iteratedDeriv s q a)

section HalfLine

variable {q : ℝ → ℂ} {a : ℝ} {U : Set ℝ} (hU : IsOpen U) (hIU : Ici a ⊆ U)
  (hq : ContDiffOn ℝ ∞ q U) {X₀ : ℕ → ℝ} {g : ℕ → ℝ → ℂ}
  (hunif : ∀ s, TendstoUniformlyOn
    (fun R (x : ℝ) => ∫ t in a..R, cexp (I * x * t) * iteratedDeriv s q t)
    (g s) atTop (Ici (X₀ s)))
include hU hIU hq hunif

/-- The boundary terms vanish and `Jₛ = (i/x) e^{iax}q^{(s)}(a) + (i/x) Jₛ₊₁`. -/
theorem fourierIoi_step {s : ℕ} {x : ℝ} (hx0 : 0 < x) (hxs : X₀ s ≤ x) (hxs1 : X₀ (s + 1) ≤ x) :
    g s x = (I / x) * (cexp (I * a * x) * iteratedDeriv s q a) + (I / x) * g (s + 1) x := by
  -- the identity on `[a, R]`
  have hibp : ∀ y : ℝ, 0 < y → ∀ R, a ≤ R →
      cexp (I * R * y) * iteratedDeriv s q R = cexp (I * a * y) * iteratedDeriv s q a +
        (∫ t in a..R, cexp (I * y * t) * iteratedDeriv (s + 1) q t) -
          (y / I) * ∫ t in a..R, cexp (I * y * t) * iteratedDeriv s q t := fun y hy R hR => by
    have h := fourier_ibp hR hU (Icc_subset_Ici_self.trans hIU) hq s hy.ne'
    have hy' : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    rw [h]; field_simp; ring_nf
  have hlim : ∀ y : ℝ, 0 < y → X₀ s ≤ y → X₀ (s + 1) ≤ y →
      Tendsto (fun R : ℝ => cexp (I * R * y) * iteratedDeriv s q R) atTop
        (𝓝 (cexp (I * a * y) * iteratedDeriv s q a + g (s + 1) y - (y / I) * g s y)) := by
    intro y hy h1 h2
    have t1 := (hunif (s + 1)).tendsto_at (show y ∈ Ici (X₀ (s + 1)) from h2)
    have t0 := (hunif s).tendsto_at (show y ∈ Ici (X₀ s) from h1)
    refine ((tendsto_const_nhds.add t1).sub (t0.const_mul _)).congr' ?_
    filter_upwards [eventually_ge_atTop a] with R hR
    rw [hibp y hy R hR]
  -- the limit of the boundary term is `0`
  have hzero : cexp (I * a * x) * iteratedDeriv s q a + g (s + 1) x - (x / I) * g s x = 0 := by
    by_contra hne
    set x' := x + 1
    have hA := hlim x hx0 hxs hxs1
    have hB := hlim x' (by linarith) (by linarith) (by linarith)
    have hA0 := hA.eventually_ne hne
    have hq' : Tendsto (fun R : ℝ => cexp (I * R)) atTop
        (𝓝 ((cexp (I * a * x') * iteratedDeriv s q a + g (s + 1) x' - (x' / I) * g s x') /
          (cexp (I * a * x) * iteratedDeriv s q a + g (s + 1) x - (x / I) * g s x))) := by
      refine (hB.div hA hne).congr' ?_
      filter_upwards [hA0] with R hR
      simp only [Pi.div_apply]
      have : cexp (I * R * x') = cexp (I * R) * cexp (I * R * x) := by
        rw [← Complex.exp_add]; congr 1; simp only [x']; push_cast; ring
      rw [this, mul_assoc, mul_div_assoc, div_self hR, mul_one]
    exact not_tendsto_exp_I_mul ⟨_, hq'⟩
  -- pass to the limit in the identity
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have : (x / I) * g s x = cexp (I * a * x) * iteratedDeriv s q a + g (s + 1) x := by
    linear_combination -hzero
  have hI : I / (x : ℂ) * (x / I) = 1 := by field_simp
  calc g s x = I / x * ((x / I) * g s x) := by rw [← mul_assoc, hI, one_mul]
    _ = _ := by rw [this]; ring

theorem fourierIoi_iter (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hX : ∀ s ≤ n, X₀ s ≤ x) :
    g 0 x = ∑ s ∈ Finset.range n, fourierTermIoi q a s x + (I / x) ^ n * g n x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih fun s hs => hX s (by omega), fourierIoi_step hU hIU hq hunif hx0 (hX n (by omega))
      (hX (n + 1) le_rfl), Finset.sum_range_succ, fourierTermIoi]
    ring

omit hU hIU hq hunif in
theorem norm_integral_exp_mul_le {D : ℝ → ℂ} {a R x : ℝ} (hR : a ≤ R) :
    ‖∫ t in a..R, cexp (I * x * t) * D t‖ ≤ ∫ t in a..R, ‖D t‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm hR).trans_eq ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [norm_mul]
  rw [show I * (x : ℂ) * t = ((x * t : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
    one_mul]

omit hU hIU hq in
theorem fourierIoi_bounded (s : ℕ) : ∃ C, ∀ x ∈ Ici (X₀ s), ‖g s x‖ ≤ C := by
  obtain ⟨R, hR⟩ := ((Metric.tendstoUniformlyOn_iff.mp (hunif s)) 1 one_pos).and
    (eventually_ge_atTop a) |>.exists
  refine ⟨1 + ∫ t in a..R, ‖iteratedDeriv s q t‖, fun x hx => ?_⟩
  have h1 := hR.1 x hx
  rw [dist_eq_norm] at h1
  have h2 := norm_integral_exp_mul_le (D := iteratedDeriv s q) (x := x) hR.2
  calc ‖g s x‖ ≤ ‖g s x - ∫ t in a..R, cexp (I * x * t) * iteratedDeriv s q t‖ +
        ‖∫ t in a..R, cexp (I * x * t) * iteratedDeriv s q t‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + ∫ t in a..R, ‖iteratedDeriv s q t‖ := add_le_add h1.le h2

/-- The value of the improper integral `∫_a^∞ e^{ixt}q(t) dt`. -/
noncomputable def fourierIoiIntegral (q : ℝ → ℂ) (a x : ℝ) : ℂ :=
  limUnder atTop fun R => ∫ t in a..R, cexp (I * x * t) * q t

omit hU hIU hq in
theorem fourierIoiIntegral_eq {x : ℝ} (hx : X₀ 0 ≤ x) : fourierIoiIntegral q a x = g 0 x := by
  have := (hunif 0).tendsto_at (show x ∈ Ici (X₀ 0) from hx)
  simp only [iteratedDeriv_zero] at this
  exact this.limUnder_eq

/-- **DLMF 2.3.5**: if `q` is infinitely differentiable on `[a, ∞)` and each
`∫ e^{ixt}q^{(s)}(t) dt` converges as `t → ∞` uniformly for all sufficiently large `x`, then
`∫_a^∞ e^{ixt}q(t) dt ∼ e^{iax} ∑ q^{(s)}(a)(i/x)^{s+1}` as `x → +∞`. -/
theorem dlmf_2_3_5 :
    IsGenAsympExpansionDLMF atTop invPowScale (fourierIoiIntegral q a) (fourierTermIoi q a) := by
  refine ⟨isAsympScale_invPowScale, fun n => ?_⟩
  obtain ⟨C, hC⟩ := fourierIoi_bounded hunif (n + 1)
  refine isBigODLMF_invPowScale (C := ‖iteratedDeriv n q a‖ + C) ?_
  have hall : ∀ᶠ x in atTop, ∀ s ∈ Finset.range (n + 2), X₀ s ≤ x :=
    (Filter.eventually_all_finset _).mpr fun s _ => eventually_ge_atTop (X₀ s)
  filter_upwards [hall, eventually_gt_atTop 0] with x hX hx0
  have hX' : ∀ s ≤ n + 1, X₀ s ≤ x := fun s hs => hX s (Finset.mem_range.mpr (by omega))
  rw [fourierIoiIntegral_eq hunif (hX' 0 (by omega)),
    fourierIoi_iter hU hIU hq hunif (n + 1) hx0 hX', Finset.sum_range_succ]
  have hxx : ‖(I / (x : ℂ))‖ = x⁻¹ := by
    rw [norm_div, norm_I, norm_real, Real.norm_of_nonneg hx0.le, one_div]
  have hterm : ‖fourierTermIoi q a n x‖ ≤ ‖iteratedDeriv n q a‖ * x⁻¹ ^ (n + 1) := by
    rw [fourierTermIoi, norm_mul, norm_pow, hxx, norm_mul,
      show I * (a : ℂ) * x = ((a * x : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
      one_mul, mul_comm]
  have hrest : ‖(I / (x : ℂ)) ^ (n + 1) * g (n + 1) x‖ ≤ C * x⁻¹ ^ (n + 1) := by
    rw [norm_mul, norm_pow, hxx, mul_comm]
    gcongr
    exact hC x (hX' (n + 1) le_rfl)
  calc ‖∑ s ∈ Finset.range n, fourierTermIoi q a s x + fourierTermIoi q a n x +
        (I / (x : ℂ)) ^ (n + 1) * g (n + 1) x - ∑ s ∈ Finset.range n, fourierTermIoi q a s x‖
      = ‖fourierTermIoi q a n x + (I / (x : ℂ)) ^ (n + 1) * g (n + 1) x‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hterm hrest
    _ = _ := by ring

/-- **DLMF §2.3(i)**, error bound for 2.3.5: the `n`th error term is at most
`x^{−n} 𝒱_{a,∞}(q^{(n−1)})` (`n ≥ 1`, `x > 0` beyond the uniformity thresholds, `q^{(n)}`
integrable). -/
theorem dlmf_2_3_5_error {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : 0 < x) (hX : ∀ s ≤ n, X₀ s ≤ x)
    (hint : IntegrableOn (fun t => ‖iteratedDeriv n q t‖) (Ioi a)) :
    ‖fourierIoiIntegral q a x - ∑ s ∈ Finset.range n, fourierTermIoi q a s x‖ ≤
      x⁻¹ ^ n * (eVariationOn (iteratedDeriv (n - 1) q) (Ici a)).toReal := by
  rw [fourierIoiIntegral_eq hunif (hX 0 (by omega)), fourierIoi_iter hU hIU hq hunif n hx0 hX,
    add_sub_cancel_left, norm_mul, norm_pow, norm_div, norm_I, norm_real,
    Real.norm_of_nonneg hx0.le, one_div]
  gcongr
  have hc := continuousOn_iteratedDeriv_of_contDiffOn hU hq n
  have hv := dlmf_1_4_34_Ioi (f := iteratedDeriv (n - 1) q) (f' := iteratedDeriv n q)
    ((continuousOn_iteratedDeriv_of_contDiffOn hU hq (n - 1)) a (hIU (mem_Ici.mpr le_rfl))
      |>.mono hIU)
    (fun t ht => by
      have := hasDerivAt_iteratedDeriv_of_contDiffOn hU hq (n - 1)
        (hIU (mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht))))
      rwa [show n - 1 + 1 = n by omega] at this)
    (hc.mono (Ioi_subset_Ici_self.trans hIU)) hint
  rw [hv, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _)]
  -- `|Jₙ(x)| ≤ ∫_a^∞ |q^{(n)}|`
  have ht := ((hunif n).tendsto_at (show x ∈ Ici (X₀ n) from hX n le_rfl)).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  refine (norm_integral_exp_mul_le hR).trans ?_
  rw [intervalIntegral.integral_of_le hR]
  exact setIntegral_mono_set hint (ae_of_all _ fun _ => norm_nonneg _)
    (ae_of_all _ fun t ht => ht.1)

end HalfLine

/-- **DLMF 2.3.6**: the variation `𝒱_{a,b}(f) = ∫_a^b |f′(t)| dt` (DLMF 1.4.34). -/
theorem dlmf_2_3_6 {f f' : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Ioo a b))
    (hint : IntegrableOn (fun x => ‖f' x‖) (Ioo a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖f' x‖) :=
  dlmf_1_4_34 hab hfc hf hf' hint

end Azurite.DLMF
