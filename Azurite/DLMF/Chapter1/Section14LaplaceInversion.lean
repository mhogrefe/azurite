/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Laplace
import Azurite.DLMF.Chapter1.Section14Inversion

/-!
# DLMF §1.14(iii): Laplace inversion, integration and derivatives

**Results.**
* 1.14.20 (`dlmf_1_14_20`, `dlmf_1_14_20_bv`): Bromwich inversion. On `ℜs = σ` the Laplace
  transform is a Fourier transform (`laplace_eq_dlmfFourier`), so §1.14(i)'s inversion 1.14.3
  applies to `H(τ) e^{−στ} f(τ)`. This is of bounded variation near `t` because products of
  functions of bounded variation are (`boundedVariationOn_mul`, not in Mathlib). DLMF's hypothesis
  (`f` continuous, `f′` piecewise continuous) is used through its consequences: bounded variation
  near `t` and continuity at `t`. The contour integral `∫_{σ−iT}^{σ+iT}` is written with
  `s = σ + iy`.
* The remark after 1.14.20 (`dlmf_1_14_20_shift`): if `ℒ(f)` continues analytically with
  `O(|s|^{−K})` decay on `ℜs ≥ γ`, the line may be moved to any `σ > γ`. The proof uses Cauchy's
  theorem on rectangles, and the horizontal sides vanish as `T → ∞`.
* 1.14.24 (`dlmf_1_14_24`): `∫_s^∞ ℒ(f) = ℒ(f/t)(s)` along `s + [0, ∞)`, by Fubini, when
  `f(t)/t` has a limit at `0+` (`integrableOn_laplace_div`).
* 1.14.27–1.14.29 (`dlmf_1_14_27`, `dlmf_1_14_28`, `dlmf_1_14_29`): transforms of derivatives,
  through integration by parts with one-sided limits on pieces (`ibp_piece`, `ibp_tail`). For
  1.14.28 this is downward induction over `(tₖ, tₖ₊₁)`.
-/

open MeasureTheory Filter Topology Set Complex

namespace Azurite.DLMF

/-! ### Products of functions of bounded variation -/

theorem boundedVariationOn_mul {f h : ℝ → ℂ} {s : Set ℝ} (hf : BoundedVariationOn f s)
    (hh : BoundedVariationOn h s) {A B : ℝ} (hA : ∀ x ∈ s, ‖f x‖ ≤ A)
    (hB : ∀ x ∈ s, ‖h x‖ ≤ B) : BoundedVariationOn (fun x => f x * h x) s := by
  have key : eVariationOn (fun x => f x * h x) s ≤
      ENNReal.ofReal A * eVariationOn h s + ENNReal.ofReal B * eVariationOn f s := by
    refine iSup_le fun p => ?_
    obtain ⟨n, u, hu, us⟩ := p
    have hpt : ∀ i, edist (f (u (i + 1)) * h (u (i + 1))) (f (u i) * h (u i)) ≤
        ENNReal.ofReal A * edist (h (u (i + 1))) (h (u i)) +
          ENNReal.ofReal B * edist (f (u (i + 1))) (f (u i)) := fun i => by
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (us i))
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (us i))
      rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hB0,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      calc ‖f (u (i + 1)) * h (u (i + 1)) - f (u i) * h (u i)‖
          = ‖f (u (i + 1)) * (h (u (i + 1)) - h (u i)) + h (u i) * (f (u (i + 1)) - f (u i))‖ := by
            ring_nf
        _ ≤ ‖f (u (i + 1))‖ * ‖h (u (i + 1)) - h (u i)‖ +
              ‖h (u i)‖ * ‖f (u (i + 1)) - f (u i)‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul, norm_mul]
        _ ≤ A * ‖h (u (i + 1)) - h (u i)‖ + B * ‖f (u (i + 1)) - f (u i)‖ := by
            gcongr
            · exact hA _ (us _)
            · exact hB _ (us _)
    calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) * h (u (i + 1))) (f (u i) * h (u i))
        ≤ ∑ i ∈ Finset.range n, (ENNReal.ofReal A * edist (h (u (i + 1))) (h (u i)) +
            ENNReal.ofReal B * edist (f (u (i + 1))) (f (u i))) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = ENNReal.ofReal A * ∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)) +
            ENNReal.ofReal B * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          · exact eVariationOn.sum_le hu us
          · exact eVariationOn.sum_le hu us
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hh,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf⟩) key

theorem bv_norm_le_of_mem {f : ℝ → ℂ} {s : Set ℝ} (hf : BoundedVariationOn f s)
    {a : ℝ} (ha : a ∈ s) : ∀ x ∈ s, ‖f x‖ ≤ ‖f a‖ + (eVariationOn f s).toReal := fun x hx => by
  have := hf.dist_le hx ha
  rw [dist_eq_norm] at this
  linarith [norm_le_insert' (f x) (f a)]

/-! ### Inversion (1.14.20) -/

/-- On the line `ℜs = σ`, the Laplace transform is a Fourier transform:
`ℒ(f)(σ + iy) = √(2π) 𝓕(g)(−y)` with `g(τ) = H(τ) e^{−στ} f(τ)`. -/
theorem laplace_eq_dlmfFourier (f : ℝ → ℂ) (σ y : ℝ) :
    laplace f (σ + y * I) = ((√(2 * Real.pi) : ℝ) : ℂ) *
      dlmfFourier ((Ioi 0).indicator fun τ => cexp (-((σ : ℂ) * τ)) * f τ) (-y) := by
  rw [dlmfFourier, ← mul_assoc, mul_inv_cancel₀ sqrt_two_pi_ne_zero, one_mul, laplace]
  have hind : ∀ τ : ℝ, (Ioi 0).indicator (fun τ : ℝ => cexp (-((σ : ℂ) * τ)) * f τ) τ *
      cexp (I * ↑(-y) * τ) = (Ioi 0).indicator
        (fun τ : ℝ => cexp (-((σ : ℂ) * τ)) * f τ * cexp (I * ↑(-y) * τ)) τ := fun τ => by
    by_cases h : τ ∈ Ioi (0 : ℝ) <;> simp [h]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  rw [mul_right_comm, ← Complex.exp_add]
  push_cast
  ring_nf

theorem boundedVariationOn_cexp (σ : ℝ) (a b : ℝ) :
    BoundedVariationOn (fun τ : ℝ => cexp (-((σ : ℂ) * τ))) (Icc a b) := by
  obtain ⟨K, hK⟩ := (by fun_prop : ContDiff ℝ 1 fun τ : ℝ => Real.exp (-(σ * τ))).contDiffOn
    (s := Icc a b) |>.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hreal : BoundedVariationOn (fun τ : ℝ => Real.exp (-(σ * τ))) (Icc a b) := by
    rcases le_or_gt a b with hab | hab
    · have := hK.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
      rwa [inter_self] at this
    · rw [Icc_eq_empty (not_le.mpr hab)]
      exact BoundedVariationOn.of_subsingleton subsingleton_empty
  have := Complex.isometry_ofReal.lipschitzWith.comp_boundedVariationOn hreal
  unfold BoundedVariationOn at this ⊢
  rwa [← eVariationOn.congr (f := fun τ : ℝ => cexp (-((σ : ℂ) * τ))) (fun τ _ => by
    simp only [Function.comp_apply, ofReal_exp]; push_cast; ring_nf)] at this

/-- **DLMF (1.14.20)** (Bromwich inversion): for `σ > α`, `t > 0` and `f` of bounded variation
near `t`,
`(2πi)^{−1} ∫_{σ−iT}^{σ+iT} e^{ts} ℒ(f)(s) ds → ½(f(t+) + f(t−))` as `T → ∞`. The contour
integral is written with `s = σ + iy`, `ds = i dy`. -/
theorem dlmf_1_14_20_bv {M α σ : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f)
    (hσ : α < σ) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hbv : BoundedVariationOn f (Icc (t - δ) (t + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] t) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] t) (𝓝 Lm)) :
    Tendsto (fun T : ℝ => (2 * Real.pi : ℂ)⁻¹ *
      ∫ y in (-T)..T, cexp (((σ : ℂ) + y * I) * t) * laplace f (σ + y * I)) atTop
      (𝓝 ((Lp + Lm) / 2)) := by
  set g : ℝ → ℂ := (Ioi 0).indicator fun τ => cexp (-((σ : ℂ) * τ)) * f τ with hgdef
  set c : ℂ := ((√(2 * Real.pi) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := sqrt_two_pi_ne_zero
  have hπ := Real.pi_pos
  have hcc : c * c = 2 * Real.pi := by
    rw [hc, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_laplace hfm hg (show α < (σ : ℂ).re by simpa using hσ))
  -- `g` near `t`
  have heqOn : EqOn g (fun τ => f τ * cexp (-((σ : ℂ) * τ))) (Icc (t - δ) (t + δ)) :=
    fun τ hτ => by
      rw [hgdef, indicator_of_mem (show τ ∈ Ioi 0 from by simp; linarith [hτ.1])]; ring
  have hgbv : BoundedVariationOn g (Icc (t - δ) (t + δ)) := by
    have hmem : t ∈ Icc (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
    have := boundedVariationOn_mul hbv (boundedVariationOn_cexp σ (t - δ) (t + δ))
      (bv_norm_le_of_mem hbv hmem) (B := Real.exp (|σ| * (t + δ))) (fun τ hτ => by
        rw [norm_cexp_neg_mul, ofReal_re]
        refine Real.exp_le_exp.mpr ?_
        have h1 := neg_abs_le σ
        have h2 : 0 ≤ τ := by linarith [hτ.1]
        nlinarith [hτ.2, abs_nonneg σ])
    unfold BoundedVariationOn at this ⊢
    rwa [eVariationOn.congr heqOn]
  have hnear : g =ᶠ[𝓝 t] fun τ => cexp (-((σ : ℂ) * τ)) * f τ := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < t by linarith)] with τ hτ
    rw [hgdef, indicator_of_mem hτ]
  have hexp : Tendsto (fun τ : ℝ => cexp (-((σ : ℂ) * τ))) (𝓝 t) (𝓝 (cexp (-((σ : ℂ) * t)))) :=
    ((by fun_prop : Continuous fun τ : ℝ => cexp (-((σ : ℂ) * τ))).tendsto t)
  have hgp : Tendsto g (𝓝[>] t) (𝓝 (cexp (-((σ : ℂ) * t)) * Lp)) :=
    ((hexp.mono_left nhdsWithin_le_nhds).mul hp).congr'
      (eventually_nhdsWithin_of_eventually_nhds hnear.symm)
  have hgm : Tendsto g (𝓝[<] t) (𝓝 (cexp (-((σ : ℂ) * t)) * Lm)) :=
    ((hexp.mono_left nhdsWithin_le_nhds).mul hm).congr'
      (eventually_nhdsWithin_of_eventually_nhds hnear.symm)
  have main := (dlmf_1_14_3 hgi hδ hgbv hgp hgm).const_mul (cexp ((σ : ℂ) * t))
  have hval : cexp ((σ : ℂ) * t) * ((cexp (-((σ : ℂ) * t)) * Lp +
      cexp (-((σ : ℂ) * t)) * Lm) / 2) = (Lp + Lm) / 2 := by
    rw [← mul_add, mul_div_assoc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, one_mul]
  rw [hval] at main
  refine main.congr fun T => ?_
  -- rewrite the Bromwich integral
  set φ : ℝ → ℂ := fun x => cexp (((σ : ℂ) - x * I) * t) * (c * dlmfFourier g x) with hφ
  have h1 : ∫ y in (-T)..T, cexp (((σ : ℂ) + y * I) * t) * laplace f (σ + y * I) =
      ∫ y in (-T)..T, φ (-y) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [hφ]
    rw [laplace_eq_dlmfFourier, ← hgdef, ← hc]
    congr 3
    push_cast
    ring
  have h2 : ∫ x in (-T)..T, φ x = cexp ((σ : ℂ) * t) * c *
      ∫ x in (-T)..T, dlmfFourier g x * cexp (-(I * x * t)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hφ]
    rw [show ((σ : ℂ) - x * I) * t = (σ : ℂ) * t + -(I * x * t) by ring, Complex.exp_add]
    ring
  rw [h1, intervalIntegral.integral_comp_neg, neg_neg, h2]
  rw [← hc] at *
  field_simp
  rw [sq, hcc]
  ring

/-- **DLMF (1.14.20)** for `f` continuous at `t`: the Bromwich integral tends to `f(t)`. -/
theorem dlmf_1_14_20 {M α σ : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f)
    (hσ : α < σ) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hbv : BoundedVariationOn f (Icc (t - δ) (t + δ))) (hc : ContinuousAt f t) :
    Tendsto (fun T : ℝ => (2 * Real.pi : ℂ)⁻¹ *
      ∫ y in (-T)..T, cexp (((σ : ℂ) + y * I) * t) * laplace f (σ + y * I)) atTop
      (𝓝 (f t)) := by
  have := dlmf_1_14_20_bv hfm hg hσ hδ hδt hbv (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rwa [add_self_div_two] at this

/-! ### Derivatives (1.14.27)–(1.14.29) -/

/-- Integration by parts against `e^{−sx}` on `[a, b]`, for `f` differentiable on `(a, b)` with
one-sided limits `A = f(a+)`, `B = f(b−)`. -/
theorem ibp_piece {f f' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume a b)
    {A B : ℂ} (ha : Tendsto f (𝓝[>] a) (𝓝 A)) (hb : Tendsto f (𝓝[<] b) (𝓝 B)) (s : ℂ) :
    ∫ x in a..b, cexp (-(s * x)) * f' x =
      cexp (-(s * b)) * B - cexp (-(s * a)) * A + s * ∫ x in a..b, cexp (-(s * x)) * f x := by
  set v : ℝ → ℂ := fun x => if x = a then A else if x = b then B else f x with hv
  have hab' : a ≠ b := hab.ne
  have hvf : ∀ x ∈ Ioo a b, v x = f x := fun x hx => by
    simp only [hv, hx.1.ne', hx.2.ne, ↓reduceIte]
  have hva : v a = A := by simp [hv]
  have hvb : v b = B := by simp [hv, hab'.symm]
  have hvcont : ContinuousOn v (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hxa
    · refine (continuousWithinAt_Ioi_iff_Ici.mp ?_).mono Icc_subset_Ici_self
      rw [ContinuousWithinAt, hva]
      exact ha.congr' (by
        filter_upwards [Ioo_mem_nhdsGT hab] with y hy using (hvf y hy).symm)
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · refine (continuousWithinAt_Iio_iff_Iic.mp ?_).mono Icc_subset_Iic_self
      rw [ContinuousWithinAt, hvb]
      exact hb.congr' (by
        filter_upwards [Ioo_mem_nhdsLT hab] with y hy using (hvf y hy).symm)
    · have hev : v =ᶠ[𝓝 x] f := by
        filter_upwards [Ioo_mem_nhds hxa hxb] with y hy using hvf y hy
      exact ((hd x ⟨hxa, hxb⟩).continuousAt.congr hev.symm).continuousWithinAt
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (-(s * x))) (-s * cexp (-(s * x))) x :=
    fun x => by
      have h1 : HasDerivAt (fun x : ℝ => -(s * x)) (-s) x := by
        have := ((hasDerivAt_id x).ofReal_comp.const_mul s).neg
        exact this.congr_deriv (by simp)
      exact h1.cexp.congr_deriv (by ring)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := fun x : ℝ => cexp (-(s * x))) (v := v) (u' := fun x => -s * cexp (-(s * x)))
    (v' := f') (fun x _ => (hu x).continuousAt.continuousWithinAt) hvcont
    (fun x _ => (hu x).hasDerivWithinAt)
    (fun x hx => by
      rw [min_eq_left hab.le, max_eq_right hab.le] at hx
      have hev : v =ᶠ[𝓝 x] f := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using hvf y hy
      exact ((hd x hx).congr_of_eventuallyEq hev).hasDerivWithinAt)
    ((by fun_prop : Continuous fun x : ℝ => -s * cexp (-(s * x))).intervalIntegrable _ _) hf'
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by rw [ae_iff]; simp
  have hcongr : ∫ x in a..b, cexp (-(s * x)) * f' x = ∫ x in a..b, cexp (-(s * x)) * f' x := rfl
  rw [hcongr, hibp, hva, hvb]
  have h2 : ∫ x in a..b, -s * cexp (-(s * x)) * v x = -s * ∫ x in a..b, cexp (-(s * x)) * f x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with x hxb hx
    rw [uIoc_of_le hab.le] at hx
    rw [hvf x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩]
    ring
  rw [h2]
  ring

theorem intervalIntegrable_of_growth {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := M * Real.exp (|α| * b))).mono_fun'
    (hfm.mono_measure (Measure.restrict_mono (by
      rw [uIoc_of_le hab]; exact fun x hx => lt_of_le_of_lt ha hx.1) le_rfl))
    ((ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun x hx => ?_))
  rw [uIoc_of_le hab] at hx
  have hx0 : 0 ≤ x := by linarith [hx.1]
  refine (hg x hx0).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hg.nonneg)
  nlinarith [le_abs_self α, neg_abs_le α, abs_nonneg α, hx.2]

/-- The tail `∫_a^∞ e^{−sx} f′(x) dx = −e^{−sa} f(a+) + s ∫_a^∞ e^{−sx} f(x) dx`. -/
theorem ibp_tail {M M' α : ℝ} {f f' : ℝ → ℂ} {a : ℝ} (ha0 : 0 ≤ a)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x) {A : ℂ} (hA : Tendsto f (𝓝[>] a) (𝓝 A))
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f)
    (hf'm : AEStronglyMeasurable f' (volume.restrict (Ioi 0))) (hg' : ExpGrowth M' α f')
    {s : ℂ} (hs : α < s.re) :
    ∫ x in Ioi a, cexp (-(s * x)) * f' x =
      -(cexp (-(s * a)) * A) + s * ∫ x in Ioi a, cexp (-(s * x)) * f x := by
  have hi' := (integrableOn_laplace hf'm hg' hs).mono_set (Ioi_subset_Ioi ha0)
  have hi := (integrableOn_laplace hfm hg hs).mono_set (Ioi_subset_Ioi ha0)
  have hL := intervalIntegral_tendsto_integral_Ioi a hi' tendsto_id
  have hR := intervalIntegral_tendsto_integral_Ioi a hi tendsto_id
  have hdecay : Tendsto (fun T : ℝ => cexp (-(s * T)) * f T) atTop (𝓝 0) := by
    have hc : 0 < s.re - α := sub_pos.mpr hs
    have h1 : Tendsto (fun T : ℝ => M * Real.exp (-(s.re - α) * T)) atTop (𝓝 (M * 0)) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)).const_mul M
        |>.congr fun T => by
          show M * Real.exp (-((s.re - α) * id T)) = M * Real.exp (-(s.re - α) * T)
          rw [neg_mul, id]
    rw [mul_zero] at h1
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact norm_laplace_integrand_le hg s hT
  have heq : ∀ᶠ T in atTop, ∫ x in a..T, cexp (-(s * x)) * f' x =
      cexp (-(s * T)) * f T - cexp (-(s * a)) * A + s * ∫ x in a..T, cexp (-(s * x)) * f x := by
    filter_upwards [eventually_gt_atTop a] with T hT
    exact ibp_piece hT (fun x hx => hd x hx.1) (intervalIntegrable_of_growth hf'm hg' ha0 hT.le)
      hA ((hd T hT).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) s
  have hRHS := ((hdecay.sub (tendsto_const_nhds (x := cexp (-(s * a)) * A))).add
    (hR.const_mul s))
  rw [zero_sub] at hRHS
  exact tendsto_nhds_unique hL (hRHS.congr' (heq.mono fun T hT => hT.symm))

/-- **DLMF (1.14.27)**: if `f` is differentiable on `(0, ∞)` with right limit `f(0+)` and `f`,
`f′` are of exponential growth, then `ℒ(f′)(s) = s ℒ(f)(s) − f(0+)`. -/
theorem dlmf_1_14_27 {M M' α : ℝ} {f f' : ℝ → ℂ} (hd : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    {A : ℂ} (hA : Tendsto f (𝓝[>] 0) (𝓝 A))
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f)
    (hf'm : AEStronglyMeasurable f' (volume.restrict (Ioi 0))) (hg' : ExpGrowth M' α f')
    {s : ℂ} (hs : α < s.re) : laplace f' s = s * laplace f s - A := by
  have := ibp_tail le_rfl hd hA hfm hg hf'm hg' hs
  simp only [ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at this
  rw [laplace, laplace, this]
  ring

/-- **DLMF (1.14.29)**: if `f = F₀, F₁ = F₀′, …, Fₙ = F_{n−1}′` on `(0, ∞)`, with right limits
`Aₖ = Fₖ(0+)` and exponential growth, then
`ℒ(Fₙ)(s) = sⁿ ℒ(f)(s) − ∑_{k<n} s^{n−1−k} Aₖ`. -/
theorem dlmf_1_14_29 {α : ℝ} {M : ℕ → ℝ} {F : ℕ → ℝ → ℂ} {A : ℕ → ℂ} (n : ℕ)
    (hd : ∀ k < n, ∀ x, 0 < x → HasDerivAt (F k) (F (k + 1) x) x)
    (hA : ∀ k < n, Tendsto (F k) (𝓝[>] 0) (𝓝 (A k)))
    (hm : ∀ k ≤ n, AEStronglyMeasurable (F k) (volume.restrict (Ioi 0)))
    (hg : ∀ k ≤ n, ExpGrowth (M k) α (F k)) {s : ℂ} (hs : α < s.re) :
    laplace (F n) s = s ^ n * laplace (F 0) s -
      ∑ k ∈ Finset.range n, s ^ (n - 1 - k) * A k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := dlmf_1_14_27 (hd n (by omega)) (hA n (by omega)) (hm n (by omega))
      (hg n (by omega)) (hm (n + 1) le_rfl) (hg (n + 1) le_rfl) hs
    rw [h1, ih (fun k hk => hd k (by omega)) (fun k hk => hA k (by omega))
      (fun k hk => hm k (by omega)) (fun k hk => hg k (by omega)), Finset.sum_range_succ,
      mul_sub, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have : ∑ k ∈ Finset.range n, s * (s ^ (n - 1 - k) * A k) =
        ∑ k ∈ Finset.range n, s ^ (n - k) * A k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.mp hk
      rw [← mul_assoc, ← pow_succ', show n - 1 - k + 1 = n - k by omega]
    rw [this]
    ring

/-- **DLMF (1.14.28)**: if `f` is differentiable on `(0, ∞)` except at
`0 = t₀ < t₁ < ⋯ < tₙ`, with one-sided limits `f(tₖ±)`, and `f`, `f′` are of exponential growth,
then `ℒ(f′)(s) = s ℒ(f)(s) − f(0+) − ∑_{k=1}^n e^{−stₖ}(f(tₖ+) − f(tₖ−))`. -/
theorem dlmf_1_14_28 {M M' α : ℝ} {f f' : ℝ → ℂ} {n : ℕ} {t : ℕ → ℝ} (ht0 : t 0 = 0)
    (htm : ∀ k < n, t k < t (k + 1))
    (hd : ∀ x, 0 < x → (∀ k ≤ n, x ≠ t k) → HasDerivAt f (f' x) x) {fp fm : ℕ → ℂ}
    (hp : ∀ k ≤ n, Tendsto f (𝓝[>] (t k)) (𝓝 (fp k)))
    (hmn : ∀ k ≤ n, 1 ≤ k → Tendsto f (𝓝[<] (t k)) (𝓝 (fm k)))
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f)
    (hf'm : AEStronglyMeasurable f' (volume.restrict (Ioi 0))) (hg' : ExpGrowth M' α f')
    {s : ℂ} (hs : α < s.re) :
    laplace f' s = s * laplace f s - fp 0 -
      ∑ k ∈ Finset.Icc 1 n, cexp (-(s * t k)) * (fp k - fm k) := by
  have hmono : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
    intro i j hij hjn
    induction j with
    | zero => rw [Nat.le_zero.mp hij]
    | succ j ih =>
      rcases Nat.of_le_succ hij with h | rfl
      · exact (ih h (by omega)).trans (htm j (by omega)).le
      · exact le_rfl
  have hpos : ∀ k ≤ n, 0 ≤ t k := fun k hk => ht0 ▸ hmono 0 k (Nat.zero_le k) hk
  have hi' := integrableOn_laplace hf'm hg' hs
  have hi := integrableOn_laplace hfm hg hs
  -- the claim on `(tₘ, ∞)`, by downward induction
  have claim : ∀ j ≤ n, ∫ x in Ioi (t (n - j)), cexp (-(s * x)) * f' x =
      -(cexp (-(s * t (n - j))) * fp (n - j)) -
        (∑ k ∈ Finset.Ioc (n - j) n, cexp (-(s * t k)) * (fp k - fm k)) +
        s * ∫ x in Ioi (t (n - j)), cexp (-(s * x)) * f x := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Finset.Ioc_self, Finset.sum_empty, sub_zero]
      exact ibp_tail (hpos n le_rfl) (fun x hx => hd x (lt_of_le_of_lt (hpos n le_rfl) hx)
        fun k hk => (lt_of_le_of_lt (hmono k n hk le_rfl) hx).ne') (hp n le_rfl) hfm hg hf'm
        hg' hs
    | succ j ih =>
      intro hj
      set m := n - (j + 1) with hmdef
      have hm1 : n - j = m + 1 := by omega
      have hmn' : m < n := by omega
      have ih' := ih (by omega)
      rw [hm1] at ih'
      have hlt := htm m hmn'
      have hsplit : ∀ g : ℝ → ℂ, IntegrableOn g (Ioi (t m)) →
          ∫ x in Ioi (t m), g x = (∫ x in (t m)..(t (m + 1)), g x) + ∫ x in Ioi (t (m + 1)), g x :=
        fun g hgi => by
          rw [intervalIntegral.integral_of_le hlt.le, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
            measurableSet_Ioi (hgi.mono_set Ioc_subset_Ioi_self)
            (hgi.mono_set (Ioi_subset_Ioi hlt.le)), Ioc_union_Ioi_eq_Ioi hlt.le]
      have hpiece := ibp_piece hlt (fun x hx => hd x (lt_of_le_of_lt (hpos m hmn'.le) hx.1)
        fun k hk => by
          rcases le_or_gt k m with hkm | hkm
          · exact (lt_of_le_of_lt (hmono k m hkm hmn'.le) hx.1).ne'
          · exact (lt_of_lt_of_le hx.2 (hmono (m + 1) k (by omega) hk)).ne)
        (intervalIntegrable_of_growth hf'm hg' (hpos m hmn'.le) hlt.le) (hp m hmn'.le)
        (hmn (m + 1) (by omega) (by omega)) s
      rw [hsplit _ (hi'.mono_set (Ioi_subset_Ioi (hpos m hmn'.le))),
        hsplit _ (hi.mono_set (Ioi_subset_Ioi (hpos m hmn'.le))), hpiece, ih',
        ← Finset.sum_Ioc_consecutive _ (Nat.le_succ m) (show m + 1 ≤ n by omega),
        Nat.Ioc_succ_singleton, Finset.sum_singleton]
      ring
  have h0 := claim n le_rfl
  rw [Nat.sub_self, ht0] at h0
  simp only [ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at h0
  rw [laplace, laplace, h0, show Finset.Ioc 0 n = Finset.Icc 1 n by ext k; simp; omega]
  ring

/-! ### Integration (1.14.24) -/

/-- `|e^{−st} f(t)| / t` is integrable on `(0, ∞)` when `f(t)/t` has a limit at `0+`. -/
theorem integrableOn_laplace_div {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) {L : ℂ} (hlim : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 L)) :
    IntegrableOn (fun t : ℝ => ‖cexp (-(s * t)) * f t‖ / t) (Ioi 0) := by
  have hi := integrableOn_laplace hfm hg hs
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖cexp (-(s * t)) * f t‖ / t)
      (volume.restrict (Ioi 0)) :=
    (hi.1.norm.mul (measurable_inv.aestronglyMeasurable)).congr
      (ae_of_all _ fun t => (div_eq_mul_inv _ _).symm)
  obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t ∈ Ioo 0 δ, ‖f t / t‖ ≤ ‖L‖ + 1 := by
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖f t / t‖ ≤ ‖L‖ + 1 := by
      filter_upwards [hlim.eventually (Metric.closedBall_mem_nhds L one_pos)] with t ht
      rw [dist_eq_norm] at ht
      linarith [norm_le_insert' (f t / t) L]
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    have hu0 : (0 : ℝ) < u := hu
    exact ⟨min u 1, lt_min hu0 one_pos, min_le_right _ _, fun t ht =>
      hsub ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩⟩
  have hM := hg.nonneg
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (integrableOn_const (C := Real.exp (|s.re|) *
      (‖L‖ + 1 + M * Real.exp (|α|) / δ)) measure_Ioc_lt_top.ne)
      (hmeas.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_))
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_cexp_neg_mul, mul_div_assoc]
    have he : Real.exp (-(s.re * t)) ≤ Real.exp (|s.re|) :=
      Real.exp_le_exp.mpr (by nlinarith [neg_abs_le s.re, ht.2, abs_nonneg s.re])
    have hft : ‖f t‖ / t ≤ ‖L‖ + 1 + M * Real.exp (|α|) / δ := by
      rcases lt_or_ge t δ with htd | htd
      · have := hδ t ⟨ht0, htd⟩
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le] at this
        have : 0 ≤ M * Real.exp (|α|) / δ := by positivity
        linarith
      · have h1 : ‖f t‖ ≤ M * Real.exp (|α|) := (hg t ht0.le).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            nlinarith [le_abs_self α, neg_abs_le α, ht.2, abs_nonneg α])) hM)
        have h2 : ‖f t‖ / t ≤ M * Real.exp (|α|) / δ :=
          div_le_div₀ (by positivity) h1 hδ0 htd
        linarith [norm_nonneg L]
    exact mul_le_mul he hft (by positivity) (Real.exp_pos _).le
  · refine Integrable.mono' (hi.mono_set (Ioi_subset_Ioi zero_le_one)).norm
      (hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
    have ht1 : (1 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (by positivity)]
    exact div_le_self (norm_nonneg _) ht1.le

/-- **DLMF (1.14.24)**: if `f(t)/t` has a limit as `t → 0+`, then
`∫_s^∞ ℒ(f)(u) du = ℒ(f/t)(s)`, the integral taken along `u = s + r`, `r ≥ 0`. -/
theorem dlmf_1_14_24 {M α : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f) {s : ℂ}
    (hs : α < s.re) {L : ℂ} (hlim : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 L)) :
    ∫ r in Ioi (0 : ℝ), laplace f (s + r) = laplace (fun t => f t / t) s := by
  set μ := (volume : Measure ℝ).restrict (Ioi 0)
  set K : ℝ → ℝ → ℂ := fun r t => cexp (-((s + r) * t)) * f t with hK
  have hKeq : ∀ r t : ℝ, K r t = (cexp (-(s * t)) * f t) * (Real.exp (-t * r) : ℂ) :=
    fun r t => by
      simp only [hK]
      rw [ofReal_exp, mul_right_comm, ← Complex.exp_add]
      push_cast; ring_nf
  have hinner : ∀ t : ℝ, 0 < t → ∫ r, K r t ∂μ = cexp (-(s * t)) * (f t / t) := fun t ht => by
    simp only [hKeq]
    rw [integral_const_mul, integral_complex_ofReal, integral_exp_neg_mul_Ioi_zero ht]
    push_cast
    ring
  have hKint : Integrable (Function.uncurry K) (μ.prod μ) := by
    have hmK : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (μ.prod μ) := hfm.comp_snd
      exact ((by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-((s + p.1) * p.2))
        ).aestronglyMeasurable).mul h1
    rw [integrable_prod_iff' hmK]
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_), ?_⟩
    · have ht0 : (0 : ℝ) < t := ht
      have := ((exp_neg_integrableOn_Ioi 0 ht0).ofReal).const_mul (cexp (-(s * t)) * f t)
      refine this.congr (ae_of_all _ fun r => ?_)
      simp [Function.uncurry_apply_pair, hKeq]
    · refine (integrableOn_laplace_div hfm hg hs hlim).congr
        ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
      have ht0 : (0 : ℝ) < t := ht
      simp only [Function.uncurry_apply_pair, hKeq, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero ht0, div_eq_mul_inv]
  have hswap := integral_integral_swap hKint
  rw [laplace]
  calc ∫ r in Ioi (0 : ℝ), laplace f (s + r) = ∫ r, ∫ t, K r t ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        rfl
    _ = ∫ t, ∫ r, K r t ∂μ ∂μ := hswap
    _ = ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (f t / t) :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht => hinner t ht

/-- **DLMF §1.14(iii)**, after (1.14.20): if `ℒ(f)` extends analytically to `F` on `ℜs > γ` with
`F(s) = O(|s|^{−K})` (`K > 1`) there, then (1.14.20) holds with `F` on every line `ℜs = σ > γ`. -/
theorem dlmf_1_14_20_shift {M α γ C K : ℝ} {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hg : ExpGrowth M α f)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (hbv : BoundedVariationOn f (Icc (t - δ) (t + δ)))
    (hc : ContinuousAt f t) {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s | γ < s.re})
    (hFeq : ∀ s : ℂ, α < s.re → F s = laplace f s) (hK : 1 < K)
    (hbound : ∀ s : ℂ, γ ≤ s.re → 1 ≤ ‖s‖ → ‖F s‖ ≤ C * ‖s‖ ^ (-K)) {σ : ℝ} (hσ : γ < σ) :
    Tendsto (fun T : ℝ => (2 * Real.pi : ℂ)⁻¹ *
      ∫ y in (-T)..T, cexp (((σ : ℂ) + y * I) * t) * F (σ + y * I)) atTop (𝓝 (f t)) := by
  set σ' := max σ α + 1 with hσ'
  have hσσ' : σ < σ' := by rw [hσ']; linarith [le_max_left σ α]
  have hασ' : α < σ' := by rw [hσ']; linarith [le_max_right σ α]
  have ht0 : 0 < t := by linarith
  have hK0 : 0 < K := by linarith
  set G : ℂ → ℂ := fun z => cexp (z * t) * F z with hG
  -- the line `σ'`
  have hmain := dlmf_1_14_20 hfm hg hασ' hδ hδt hbv hc
  have hmain' : Tendsto (fun T : ℝ => (2 * Real.pi : ℂ)⁻¹ *
      ∫ y in (-T)..T, G (σ' + y * I)) atTop (𝓝 (f t)) := by
    refine hmain.congr fun T => ?_
    congr 1
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [hG]
    rw [hFeq _ (by simpa using hασ')]
  -- `C ≥ 0`
  have hC0 : 0 ≤ C := by
    have h2 : (1 : ℝ) ≤ ‖((σ : ℂ) + 2 * I)‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + 2 * I)
      simp at this; linarith
    have := (norm_nonneg _).trans (hbound _ (by simpa using hσ.le) h2)
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (by linarith) _)).mp this
  -- the horizontal sides
  have hside : ∀ T : ℝ, 1 ≤ T → ∀ y : ℝ, |y| = T →
      ‖∫ x in σ..σ', G (x + y * I)‖ ≤ (Real.exp (σ' * t) * C * T ^ (-K)) * |σ' - σ| :=
    fun T hT y hy => by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [uIoc_of_le hσσ'.le] at hx
      have hre : γ ≤ ((x : ℂ) + y * I).re := by simp; linarith [hx.1]
      have hnorm : T ≤ ‖((x : ℂ) + y * I)‖ := by
        have := Complex.abs_im_le_norm ((x : ℂ) + y * I)
        simp at this; linarith
      simp only [hG, norm_mul, Complex.norm_exp]
      have hexp : Real.exp ((((x : ℂ) + y * I) * t).re) ≤ Real.exp (σ' * t) := by
        refine Real.exp_le_exp.mpr ?_
        simp; nlinarith [hx.2]
      have hF := hbound _ hre (hT.trans hnorm)
      have hpow : ‖((x : ℂ) + y * I)‖ ^ (-K) ≤ T ^ (-K) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hnorm (by linarith)
      calc Real.exp ((((x : ℂ) + y * I) * t).re) * ‖F (x + y * I)‖
          ≤ Real.exp (σ' * t) * (C * T ^ (-K)) :=
            mul_le_mul hexp (hF.trans (mul_le_mul_of_nonneg_left hpow hC0)) (norm_nonneg _)
              (Real.exp_pos _).le
        _ = _ := by ring
  have hdecay : Tendsto (fun T : ℝ => (Real.exp (σ' * t) * C * T ^ (-K)) * |σ' - σ|) atTop
      (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hK0).const_mul (Real.exp (σ' * t) * C)).mul_const |σ' - σ|
    simpa [mul_assoc] using this
  -- the rectangle
  have hrect : ∀ T : ℝ, 1 ≤ T → ∫ y in (-T)..T, G (σ + y * I) =
      (∫ y in (-T)..T, G (σ' + y * I)) +
        ((∫ x in σ..σ', G (x + (-T) * I)) - ∫ x in σ..σ', G (x + T * I)) / I := fun T hT => by
    have hdiff : DifferentiableOn ℂ G (uIcc (Complex.mk σ (-T)).re (Complex.mk σ' T).re ×ℂ
        uIcc (Complex.mk σ (-T)).im (Complex.mk σ' T).im) := by
      intro z hz
      rw [mem_reProdIm] at hz
      simp only at hz
      rw [uIcc_of_le hσσ'.le] at hz
      have : γ < z.re := by linarith [hz.1.1]
      exact ((((differentiable_id.mul_const (t : ℂ)).cexp).differentiableAt).mul
        (hFd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds this))
        ).differentiableWithinAt
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G _ _ hdiff
    simp only [smul_eq_mul] at h
    push_cast at h
    generalize (∫ (x : ℝ) in σ..σ', G (↑x + -↑T * I)) = Hb at h ⊢
    generalize (∫ (x : ℝ) in σ..σ', G (↑x + ↑T * I)) = Ht at h ⊢
    generalize (∫ (y : ℝ) in -T..T, G (↑σ' + ↑y * I)) = A' at h ⊢
    generalize (∫ (y : ℝ) in -T..T, G (↑σ + ↑y * I)) = A at h ⊢
    have hI : I ≠ 0 := I_ne_zero
    field_simp
    linear_combination -h
  have hE : Tendsto (fun T : ℝ => (2 * Real.pi : ℂ)⁻¹ *
      (((∫ x in σ..σ', G (x + (-T) * I)) - ∫ x in σ..σ', G (x + T * I)) / I)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun T : ℝ => ((2 * Real.pi)⁻¹ * 2) *
        ((Real.exp (σ' * t) * C * T ^ (-K)) * |σ' - σ|)) atTop (𝓝 0) := by
      simpa using hdecay.const_mul ((2 * Real.pi)⁻¹ * 2)
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have h1 := hside T hT (-T) (by rw [abs_neg, abs_of_nonneg hT0])
    have h2 := hside T hT T (abs_of_nonneg hT0)
    have hπ := Real.pi_pos
    push_cast at h1
    rw [norm_mul, norm_div, Complex.norm_I, div_one, norm_inv, show ‖(2 * Real.pi : ℂ)‖ =
      2 * Real.pi by rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]]
    calc (2 * Real.pi)⁻¹ * ‖(∫ x in σ..σ', G (x + -↑T * I)) - ∫ x in σ..σ', G (x + T * I)‖
        ≤ (2 * Real.pi)⁻¹ * (‖∫ x in σ..σ', G (x + -↑T * I)‖ +
            ‖∫ x in σ..σ', G (x + T * I)‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ (2 * Real.pi)⁻¹ * ((Real.exp (σ' * t) * C * T ^ (-K)) * |σ' - σ| +
            (Real.exp (σ' * t) * C * T ^ (-K)) * |σ' - σ|) := by gcongr
      _ = _ := by ring
  have := hmain'.add hE
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [show (fun y : ℝ => cexp (((σ : ℂ) + y * I) * t) * F (σ + y * I)) =
    fun y : ℝ => G (σ + y * I) from rfl, hrect T hT]
  ring

end Azurite.DLMF
