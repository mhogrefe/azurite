/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11Expint

/-!
# DLMF §2.11(ii): 2.11.6 and the compound expansion 2.11.7

With `z = e^w` on the Riemann surface of the logarithm (`Section11Expint.lean`):

* `eiP_eq_ray`: `∫_z^∞ e^{−t} t^{−p} dt` along the ray `t = z(1 + σe)`, `σ ≥ 0`, provided the ray
  stays off `(−∞, 0]·z`, `ℜ(ze) > 0`, and the ray ends on the principal sheet
  (`|ℑw + ph e| < π/2`); `norm_eiP_le_ray` bounds it by `|z^{1−p} e^{−z}|/ℜ(ze)` times a constant.
* `rayAngle`: the direction `e = e^{iθ}`, `θ = clamp(−ph z)`, that works throughout
  `|ph z| ≤ 3π/2 − δ` (`norm_eiP_le_sector`): this is the rotation of the path in Watson's lemma.
* **2.11.6** (`dlmf_2_11_6`): `E_p(z) ∼ (e^{−z}/z) ∑ (−1)^s (p)_s/z^s` as `z → ∞` in
  `|ph z| ≤ 3π/2 − δ`, with remainder `O(|e^{−z}| |z|^{−n−1})` after `n` terms, from the exact
  form `genExpInt_expansion` (repeated integration by parts in place of Watson's lemma).
* **2.11.7** (`dlmf_2_11_7`): `E_p(z) ∼ (2πi e^{−pπi}/Γ(p)) z^{p−1} + (e^{−z}/z) ∑ (−1)^s (p)_s/z^s`
  in `π/2 + δ ≤ ph z ≤ 7π/2 − δ`, from 2.11.6 and the connection formula `dlmf_8_19_18`.
* The added term is relatively exponentially small where `cos(ph z) < 0` (near `ph z = π`) and
  dominant where `cos(ph z) > 0` (past `ph z = 3π/2`): `dlmf_2_11_ii_small`,
  `dlmf_2_11_ii_dominant`.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### The ray representation -/

theorem norm_cpow_neg_le {u p : ℂ} (hu : u ≠ 0) (hp : 0 ≤ p.re) {c : ℝ} (hc : 0 < c)
    (hcu : c ≤ ‖u‖) : ‖u ^ (-p)‖ ≤ c ^ (-p.re) * Real.exp (π * |p.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hu, div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hc hcu (by simp; linarith))
    (Real.exp_le_exp.mpr ?_) (by positivity) (by positivity)
  have h1 := Complex.abs_arg_le_pi u
  have : -(arg u * (-p).im) ≤ |arg u| * |p.im| := by
    rw [Complex.neg_im, mul_neg, neg_neg]
    exact (le_abs_self _).trans (abs_mul _ _).le
  nlinarith [abs_nonneg p.im]

/-- The integrand on the ray: `f_p(v) dv` with `e^v = z(1 + σe)`. -/
theorem eiF_log (p w u : ℂ) (hu : u ≠ 0) (e : ℂ) :
    eiF p (w + Complex.log u) * (e / u) =
      cexp ((1 - p) * w) * e * (cexp (-(cexp w * u)) * u ^ (-p)) := by
  unfold eiF
  rw [Complex.exp_add w, Complex.exp_log hu, Complex.cpow_def_of_ne_zero hu,
    show (1 - p) * (w + Complex.log u) = (1 - p) * w + Complex.log u + Complex.log u * (-p) by
      ring, Complex.exp_add, Complex.exp_add, Complex.exp_log hu]
  field_simp

theorem tendsto_arg_one_add {e : ℂ} (he : e ∈ slitPlane) :
    Tendsto (fun σ : ℝ => arg (1 + σ * e)) atTop (𝓝 (arg e)) := by
  have h1 : Tendsto (fun σ : ℝ => (σ⁻¹ : ℂ) + e) atTop (𝓝 e) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using this.add_const e
  have h2 := ((Complex.continuousAt_arg he).tendsto).comp h1
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with σ hσ
  simp only [Function.comp_apply]
  have hσ' : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [show (1 : ℂ) + σ * e = (σ : ℝ) * ((σ⁻¹ : ℂ) + e) by
    field_simp, Complex.arg_real_mul _ hσ]

theorem tendsto_norm_one_add {e : ℂ} (he : e ≠ 0) :
    Tendsto (fun σ : ℝ => ‖1 + σ * e‖) atTop atTop := by
  have hpos : 0 < ‖e‖ := norm_pos_iff.mpr he
  refine tendsto_atTop_mono (fun σ => ?_) (tendsto_atTop_add_const_right _ (-1)
    (tendsto_id.atTop_mul_const hpos))
  simp only [id]
  have := norm_sub_norm_le ((σ : ℂ) * e) (-1)
  simp only [sub_neg_eq_add, norm_neg, norm_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs] at this
  rw [add_comm] at this
  linarith [le_abs_self σ, mul_le_mul_of_nonneg_right (le_abs_self σ) hpos.le]

/-- **The ray representation** of `∫_z^∞ e^{−t} t^{−p} dt` along `t = z(1 + σe)`. -/
theorem eiP_eq_ray {p w e : ℂ} (hp : 0 ≤ p.re)
    (hslit : ∀ σ : ℝ, 0 ≤ σ → 1 + σ * e ∈ slitPlane) {c : ℝ} (hc : 0 < c)
    (hcb : ∀ σ : ℝ, 0 ≤ σ → c ≤ ‖1 + σ * e‖) (he : e ∈ slitPlane)
    (hdec : 0 < (cexp w * e).re) (harg : |w.im + arg e| < π / 2) :
    eiP p w = cexp ((1 - p) * w) * e *
      ∫ σ in Ioi (0 : ℝ), cexp (-(cexp w * (1 + σ * e))) * (1 + σ * e) ^ (-p) := by
  set g : ℝ → ℂ := fun σ => cexp (-(cexp w * (1 + σ * e))) * (1 + σ * e) ^ (-p)
  set G : ℝ → ℂ := fun σ => eiP p (w + Complex.log (1 + σ * e))
  have hne : ∀ σ : ℝ, 0 ≤ σ → (1 : ℂ) + σ * e ≠ 0 := fun σ hσ => slitPlane_ne_zero (hslit σ hσ)
  -- derivative along the ray
  have hd : ∀ σ : ℝ, 0 ≤ σ → HasDerivAt G (-(cexp ((1 - p) * w) * e * g σ)) σ := by
    intro σ hσ
    have h0 : HasDerivAt (fun u : ℂ => 1 + u * e) e (σ : ℂ) := by
      simpa using ((hasDerivAt_id (σ : ℂ)).mul_const e).const_add 1
    have h1 : HasDerivAt (fun u : ℂ => w + Complex.log (1 + u * e)) (e / (1 + σ * e)) (σ : ℂ) := by
      have := ((Complex.hasDerivAt_log (hslit σ hσ)).comp (σ : ℂ) h0).const_add w
      rw [div_eq_inv_mul]
      exact this
    have h2 := ((hasDerivAt_eiP p _).comp (σ : ℂ) h1).comp_ofReal
    convert h2 using 1
    · rfl
    rw [neg_mul, eiF_log p w _ (hne σ hσ) e]
  -- continuity of `g` on `[0, ∞)`
  have hgc : ContinuousOn g (Ici 0) := by
    intro σ hσ
    have hs := hslit σ hσ
    refine ContinuousAt.continuousWithinAt ?_
    have hu : ContinuousAt (fun σ : ℝ => (1 : ℂ) + σ * e) σ := by fun_prop
    exact (by fun_prop : ContinuousAt (fun σ : ℝ => cexp (-(cexp w * (1 + σ * e)))) σ).mul
      ((continuousAt_cpow_const hs).comp (f := fun σ : ℝ => (1 : ℂ) + σ * e) hu)
  -- integrability
  set K := ‖cexp (-cexp w)‖ * (c ^ (-p.re) * Real.exp (π * |p.im|))
  have hgb : ∀ σ : ℝ, 0 ≤ σ → ‖g σ‖ ≤ K * Real.exp (-(cexp w * e).re * σ) := by
    intro σ hσ
    simp only [g, K]
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    calc Real.exp (-(cexp w * (1 + σ * e))).re * ‖(1 + σ * e) ^ (-p)‖
        ≤ Real.exp (-(cexp w * (1 + σ * e))).re * (c ^ (-p.re) * Real.exp (π * |p.im|)) := by
          gcongr; exact norm_cpow_neg_le (hne σ hσ) hp hc (hcb σ hσ)
      _ = _ := by
          rw [show (-(cexp w * (1 + σ * e))).re = (-cexp w).re + -(cexp w * e).re * σ by
            simp only [mul_add, mul_one, neg_add, Complex.add_re, Complex.neg_re]
            rw [show cexp w * (σ * e) = σ * (cexp w * e) by ring, Complex.re_ofReal_mul]
            ring, Real.exp_add]
          ring
  have hgi : IntegrableOn g (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hdec).const_mul K).mono'
      ((hgc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun σ hσ => ?_)
    refine (hgb σ (le_of_lt hσ)).trans (le_of_eq ?_)
    ring_nf
  -- `G σ → 0`
  have hG : Tendsto G atTop (𝓝 0) := by
    set η := (π / 2 - |w.im + arg e|) / 2
    have hη : 0 < η := by simp only [η]; linarith
    have hη' : η < π / 2 := by simp only [η]; linarith [abs_nonneg (w.im + arg e)]
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨X, hX⟩ := eiP_small p hη hη' (half_pos hε)
    have hre : Tendsto (fun σ : ℝ => (w + Complex.log (1 + σ * e)).re) atTop atTop := by
      simp only [Complex.add_re, Complex.log_re]
      exact tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp
        (tendsto_norm_one_add (slitPlane_ne_zero he)))
    have him : Tendsto (fun σ : ℝ => (w + Complex.log (1 + σ * e)).im) atTop
        (𝓝 (w.im + arg e)) := by
      simp only [Complex.add_im, Complex.log_im]
      exact (tendsto_arg_one_add he).const_add _
    have him' : ∀ᶠ σ : ℝ in atTop, |(w + Complex.log (1 + σ * e)).im| ≤ π / 2 - η := by
      have := him.abs.eventually (ge_mem_nhds (show |w.im + arg e| < π / 2 - η by
        simp only [η]; linarith))
      exact this
    filter_upwards [hre.eventually_ge_atTop X, him'] with σ h1 h2
    rw [dist_zero_right]
    exact (hX _ h1 h2).trans_lt (half_lt_self hε)
  -- FTC on `[0, S]` and `S → ∞`
  have hftc : ∀ S : ℝ, 0 ≤ S → eiP p w = G S + cexp ((1 - p) * w) * e * ∫ σ in (0 : ℝ)..S, g σ := by
    intro S hS
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := S)
      (fun σ hσ => hd σ (by rw [Set.uIcc_of_le hS] at hσ; exact hσ.1))
      ((((hgc.mono Icc_subset_Ici_self).const_smul
        (cexp ((1 - p) * w) * e)).neg).intervalIntegrable_of_Icc hS |>.congr (by
          intro σ _; simp [smul_eq_mul]))
    simp only [G, Complex.ofReal_zero, zero_mul, add_zero, Complex.log_one] at h
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h
    linear_combination h
  have hlim := hG.add ((intervalIntegral_tendsto_integral_Ioi 0 hgi tendsto_id).const_mul
    (cexp ((1 - p) * w) * e))
  rw [zero_add] at hlim
  have hc' : Tendsto (fun S : ℝ => G S + cexp ((1 - p) * w) * e * ∫ σ in (0 : ℝ)..id S, g σ)
      atTop (𝓝 (eiP p w)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with S hS
    exact hftc S hS
  exact tendsto_nhds_unique hc' hlim

/-- The bound from the ray: `|∫_z^∞ e^{−t}t^{−p} dt| ≤ |z^{1−p}| |e| |e^{−z}| c^{−ℜp}
e^{π|ℑp|}/ℜ(ze)`. -/
theorem norm_eiP_le_ray {p w e : ℂ} (hp : 0 ≤ p.re)
    (hslit : ∀ σ : ℝ, 0 ≤ σ → 1 + σ * e ∈ slitPlane) {c : ℝ} (hc : 0 < c)
    (hcb : ∀ σ : ℝ, 0 ≤ σ → c ≤ ‖1 + σ * e‖) (he : e ∈ slitPlane)
    (hdec : 0 < (cexp w * e).re) (harg : |w.im + arg e| < π / 2) :
    ‖eiP p w‖ ≤ ‖cexp ((1 - p) * w)‖ * ‖e‖ * (‖cexp (-cexp w)‖ *
      (c ^ (-p.re) * Real.exp (π * |p.im|))) / (cexp w * e).re := by
  rw [eiP_eq_ray hp hslit hc hcb he hdec harg, norm_mul, norm_mul, mul_div_assoc]
  gcongr
  set K := ‖cexp (-cexp w)‖ * (c ^ (-p.re) * Real.exp (π * |p.im|))
  have hne : ∀ σ : ℝ, 0 ≤ σ → (1 : ℂ) + σ * e ≠ 0 := fun σ hσ => slitPlane_ne_zero (hslit σ hσ)
  have hgb : ∀ σ ∈ Ioi (0 : ℝ), ‖cexp (-(cexp w * (1 + σ * e))) * (1 + σ * e) ^ (-p)‖ ≤
      K * Real.exp (-(cexp w * e).re * σ) := by
    intro σ hσ
    have hσ' : (0 : ℝ) ≤ σ := le_of_lt hσ
    simp only [K]
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    calc Real.exp (-(cexp w * (1 + σ * e))).re * ‖(1 + σ * e) ^ (-p)‖
        ≤ Real.exp (-(cexp w * (1 + σ * e))).re * (c ^ (-p.re) * Real.exp (π * |p.im|)) := by
          gcongr; exact norm_cpow_neg_le (hne σ hσ') hp hc (hcb σ hσ')
      _ = _ := by
          rw [show (-(cexp w * (1 + σ * e))).re = (-cexp w).re + -(cexp w * e).re * σ by
            simp only [mul_add, mul_one, neg_add, Complex.add_re, Complex.neg_re]
            rw [show cexp w * (σ * e) = σ * (cexp w * e) by ring, Complex.re_ofReal_mul]
            ring, Real.exp_add]
          ring
  calc ‖∫ σ in Ioi (0 : ℝ), cexp (-(cexp w * (1 + σ * e))) * (1 + σ * e) ^ (-p)‖
      ≤ ∫ σ in Ioi (0 : ℝ), K * Real.exp (-(cexp w * e).re * σ) :=
        norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hdec).const_mul K)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hgb))
    _ = K / (cexp w * e).re := by
        rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
        simp only [mul_zero, Real.exp_zero]
        field_simp

/-! ### The rotation of the path in `|ph z| ≤ 3π/2 − δ` -/

/-- The ray direction `θ = clamp(−ph z, −(π − δ/2), π − δ/2)`. -/
noncomputable def rayAngle (δ φ : ℝ) : ℝ := max (-(π - δ / 2)) (min (π - δ / 2) (-φ))

theorem abs_rayAngle_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) (φ : ℝ) :
    |rayAngle δ φ| ≤ π - δ / 2 := by
  unfold rayAngle
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem abs_add_rayAngle_le {δ φ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) (hφ : |φ| ≤ 3 * π / 2 - δ) :
    |φ + rayAngle δ φ| ≤ π / 2 - δ / 2 := by
  unfold rayAngle
  rw [abs_le] at hφ ⊢
  by_cases h1 : -φ ≤ π - δ / 2
  · rw [min_eq_right h1]
    by_cases h2 : -(π - δ / 2) ≤ -φ
    · rw [max_eq_right h2]; constructor <;> linarith [Real.pi_pos]
    · rw [max_eq_left (by linarith)]; constructor <;> linarith
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> linarith

theorem sin_le_abs_sin {κ θ : ℝ} (hκ : 0 < κ) (hθ : |θ| ≤ π - κ) (hc : Real.cos θ ≤ 0) :
    Real.sin κ ≤ |Real.sin θ| := by
  have hθ' : π / 2 ≤ |θ| := by
    by_contra h
    push Not at h
    have := Real.cos_pos_of_mem_Ioo (x := θ) ⟨by rw [abs_lt] at h; linarith [h.1],
      by rw [abs_lt] at h; linarith [h.2]⟩
    linarith
  have hs : |Real.sin θ| = Real.sin (π - |θ|) := by
    rw [Real.sin_pi_sub]
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by
        rw [abs_of_nonneg h] at hθ; linarith))]
    · rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h
        (by rw [abs_of_nonpos h] at hθ; linarith))]
  rw [hs]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
    (by linarith)

/-- The ray `1 + σe^{iθ}`, `|θ| ≤ π − κ`, stays in the slit plane at distance `≥ sin κ` from `0`. -/
theorem one_add_ray {κ θ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ π / 2) (hθ : |θ| ≤ π - κ) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    1 + σ * cexp (θ * I) ∈ slitPlane ∧ Real.sin κ ≤ ‖1 + σ * cexp (θ * I)‖ := by
  have hre : (1 + σ * cexp (θ * I)).re = 1 + σ * Real.cos θ := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (1 + σ * cexp (θ * I)).im = σ * Real.sin θ := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hsk : Real.sin κ ≤ 1 := Real.sin_le_one κ
  rcases le_or_gt 0 (Real.cos θ) with hc | hc
  · have h1 : 1 ≤ (1 + σ * cexp (θ * I)).re := by rw [hre]; nlinarith
    exact ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)),
      hsk.trans (h1.trans (Complex.re_le_norm _))⟩
  · have hs := sin_le_abs_sin hκ hθ hc.le
    have hsk0 : 0 < Real.sin κ := Real.sin_pos_of_pos_of_lt_pi hκ (by linarith [Real.pi_pos])
    have hnorm : |Real.sin θ| ≤ ‖1 + σ * cexp (θ * I)‖ := by
      have h2 : ‖1 + σ * cexp (θ * I)‖ ^ 2 = (1 + σ * Real.cos θ) ^ 2 + (σ * Real.sin θ) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
      have h3 : |Real.sin θ| ^ 2 ≤ ‖1 + σ * cexp (θ * I)‖ ^ 2 := by
        rw [h2, sq_abs]
        nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (σ + Real.cos θ)]
      exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
    refine ⟨?_, hs.trans hnorm⟩
    rcases hσ.lt_or_eq with hσ' | hσ'
    · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [him]
      exact mul_ne_zero hσ'.ne' fun h => by rw [h, abs_zero] at hs; linarith
    · rw [← hσ']
      simp [Complex.one_mem_slitPlane]

theorem cos_ge_sin_of_abs_le {x κ : ℝ} (hκ : 0 ≤ κ) (hx : |x| ≤ π / 2 - κ) :
    Real.sin κ ≤ Real.cos x := by
  rw [← Real.cos_abs x, ← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith [Real.pi_pos]) hx

/-- **The bound in `|ph z| ≤ 3π/2 − δ`** (`ℜq ≥ 0`): with `c = sin(δ/2)`,
`|∫_z^∞ e^{−t} t^{−q} dt| ≤ |z^{1−q}| |e^{−z}| c^{−ℜq} e^{π|ℑq|}/(|z| c)`. -/
theorem norm_eiP_le_sector {q : ℂ} (hq : 0 ≤ q.re) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) {w : ℂ}
    (hw : |w.im| ≤ 3 * π / 2 - δ) :
    ‖eiP q w‖ ≤ ‖cexp ((1 - q) * w)‖ * (‖cexp (-cexp w)‖ *
      (Real.sin (δ / 2) ^ (-q.re) * Real.exp (π * |q.im|))) /
        (Real.exp w.re * Real.sin (δ / 2)) := by
  set θ := rayAngle δ w.im
  have hθ := abs_rayAngle_le hδ hδ' w.im
  have hsum := abs_add_rayAngle_le hδ hδ' hw
  have hκ : (0 : ℝ) < δ / 2 := by linarith
  have hκ' : δ / 2 ≤ π / 2 := by linarith
  have hs0 : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi hκ (by linarith)
  have hθI : θ ∈ Ioc (-π) π := by rw [abs_le] at hθ; constructor <;> linarith
  have harg : arg (cexp (θ * I)) = θ := by
    rw [Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I hθI
  have he : cexp (θ * I) ∈ slitPlane := by
    have := (one_add_ray hκ hκ' (θ := θ) (by linarith) (σ := 1) zero_le_one).1
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · rcases hc.lt_or_eq with hc | hc
      · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.exp_ofReal_mul_I_re]; exact hc))
      · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
        rw [Complex.exp_ofReal_mul_I_im]
        intro h
        have := Real.sin_sq_add_cos_sq θ
        rw [h, ← hc] at this; norm_num at this
    · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [Complex.exp_ofReal_mul_I_im]
      have := sin_le_abs_sin hκ (by linarith) hc.le
      intro h; rw [h, abs_zero] at this; linarith
  have hre : (cexp w * cexp (θ * I)).re = Real.exp w.re * Real.cos (w.im + θ) := by
    rw [← Complex.exp_add, Complex.exp_re]; simp
  have hcos : Real.sin (δ / 2) ≤ Real.cos (w.im + θ) :=
    cos_ge_sin_of_abs_le hκ.le (by linarith)
  have hdec : Real.exp w.re * Real.sin (δ / 2) ≤ (cexp w * cexp (θ * I)).re := by
    rw [hre]; exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
  have h := norm_eiP_le_ray hq (fun σ hσ => (one_add_ray hκ hκ' (by linarith) hσ).1) hs0
    (fun σ hσ => (one_add_ray hκ hκ' (by linarith) hσ).2) he
    ((by positivity : 0 < Real.exp w.re * Real.sin (δ / 2)).trans_le hdec)
    (by rw [harg]; linarith)
  rw [Complex.norm_exp_ofReal_mul_I, mul_one] at h
  refine h.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hdec)

/-! ### 2.11.6 -/

theorem norm_cexp_mul_cexp (p : ℂ) (N : ℕ) (w : ℂ) :
    ‖cexp ((p - 1) * w)‖ * ‖cexp ((1 - (p + N)) * w)‖ = 1 / ‖cexp w‖ ^ N := by
  rw [← norm_mul, ← Complex.exp_add, show (p - 1) * w + (1 - (p + N)) * w = -(N * w) by ring,
    Complex.exp_neg, Complex.exp_nat_mul, norm_inv, norm_pow, one_div]

/-- **DLMF 2.11.6**: `E_p(z) ∼ (e^{−z}/z) ∑_{s=0}^{∞} (−1)^s (p)_s/z^s` as `z → ∞` in any closed
sector within `|ph z| < 3π/2`: after `n` terms the remainder is at most
`C |e^{−z}|/|z|^{n+1}` for `|z| ≥ 1`, `|ph z| ≤ 3π/2 − δ`. -/
theorem dlmf_2_11_6 (p : ℂ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ w : ℂ, |w.im| ≤ 3 * π / 2 - δ → 0 ≤ w.re →
      ‖genExpInt p w - cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
          (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s‖ ≤
        C * (‖cexp (-cexp w)‖ / ‖cexp w‖ ^ (n + 1)) := by
  set N := n + ⌈|p.re|⌉₊
  have hnN : n ≤ N := Nat.le_add_right _ _
  have hq : 0 ≤ (p + N).re := by
    simp only [N, Complex.add_re, Complex.natCast_re]
    push_cast
    have := Nat.le_ceil |p.re|
    have := neg_abs_le p.re
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set c := Real.sin (δ / 2)
  have hc0 : 0 < c := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set M := c ^ (-(p + N).re) * Real.exp (π * |(p + N).im|)
  refine ⟨∑ s ∈ Finset.Ico n N, ‖(ascPochhammer ℂ s).eval p‖ +
    ‖(ascPochhammer ℂ N).eval p‖ * M / c, fun w hw hre => ?_⟩
  set z := cexp w
  set r := ‖z‖
  have hr : r = Real.exp w.re := Complex.norm_exp w
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_exp hre
  have hr0 : 0 < r := by linarith
  set A := ‖cexp (-z)‖
  rw [genExpInt_expansion p w N]
  have hsplit :
      cexp (-z) / z * ∑ s ∈ Finset.range N, (-1) ^ s * (ascPochhammer ℂ s).eval p / z ^ s +
      (-1) ^ N * (ascPochhammer ℂ N).eval p * (cexp ((p - 1) * w) * eiP (p + N) w) -
      cexp (-z) / z * ∑ s ∈ Finset.range n, (-1) ^ s * (ascPochhammer ℂ s).eval p / z ^ s =
      cexp (-z) / z * ∑ s ∈ Finset.Ico n N, (-1) ^ s * (ascPochhammer ℂ s).eval p / z ^ s +
      (-1) ^ N * (ascPochhammer ℂ N).eval p * (cexp ((p - 1) * w) * eiP (p + N) w) := by
    rw [Finset.sum_Ico_eq_sub _ hnN]; ring
  rw [hsplit]
  -- the finite part
  have h1 : ‖cexp (-z) / z * ∑ s ∈ Finset.Ico n N, (-1) ^ s * (ascPochhammer ℂ s).eval p / z ^ s‖
      ≤ (∑ s ∈ Finset.Ico n N, ‖(ascPochhammer ℂ s).eval p‖) * (A / r ^ (n + 1)) := by
    rw [norm_mul, norm_div, Finset.sum_mul]
    calc A / r * ‖∑ s ∈ Finset.Ico n N, (-1) ^ s * (ascPochhammer ℂ s).eval p / z ^ s‖
        ≤ A / r * ∑ s ∈ Finset.Ico n N, ‖(ascPochhammer ℂ s).eval p‖ / r ^ n := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
          rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
            (pow_le_pow_right₀ hr1 (Finset.mem_Ico.mp hs).1)
      _ = ∑ s ∈ Finset.Ico n N, ‖(ascPochhammer ℂ s).eval p‖ * (A / r ^ (n + 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [pow_succ]; field_simp
  -- the remainder
  have h2 : ‖(-1) ^ N * (ascPochhammer ℂ N).eval p * (cexp ((p - 1) * w) * eiP (p + N) w)‖ ≤
      ‖(ascPochhammer ℂ N).eval p‖ * M / c * (A / r ^ (n + 1)) := by
    have hb := norm_eiP_le_sector hq hδ hδ' hw
    rw [← hr] at hb
    have hrN : r ^ (n + 1) ≤ r ^ (N + 1) := pow_le_pow_right₀ hr1 (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul]
    calc ‖(ascPochhammer ℂ N).eval p‖ * (‖cexp ((p - 1) * w)‖ * ‖eiP (p + N) w‖)
        ≤ ‖(ascPochhammer ℂ N).eval p‖ * (‖cexp ((p - 1) * w)‖ *
          (‖cexp ((1 - (p + N)) * w)‖ * (A * M) / (r * c))) := by gcongr
      _ = ‖(ascPochhammer ℂ N).eval p‖ * M / c * (A / r ^ (N + 1)) := by
          rw [show ‖cexp ((p - 1) * w)‖ * (‖cexp ((1 - (p + N)) * w)‖ * (A * M) / (r * c)) =
            (‖cexp ((p - 1) * w)‖ * ‖cexp ((1 - (p + N)) * w)‖) * (A * M) / (r * c) by ring,
            norm_cexp_mul_cexp, show ‖cexp w‖ = r from rfl]
          rw [pow_succ]; field_simp
      _ ≤ _ := by gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-! ### 2.11.7 -/

/-- **DLMF 2.11.7**: `E_p(z) ∼ (2πi e^{−pπi}/Γ(p)) z^{p−1} + (e^{−z}/z) ∑ (−1)^s (p)_s/z^s` as
`z → ∞` in any closed sector within `π/2 < ph z < 7π/2` (`z^{p−1} = e^{(p−1)w}` on the Riemann
surface). -/
theorem dlmf_2_11_7 (p : ℂ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ w : ℂ, π / 2 + δ ≤ w.im → w.im ≤ 7 * π / 2 - δ → 0 ≤ w.re →
      ‖genExpInt p w - 2 * π * I * cexp (-(p * π * I)) / Complex.Gamma p * cexp ((p - 1) * w) -
          cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
            (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s‖ ≤
        C * (‖cexp (-cexp w)‖ / ‖cexp w‖ ^ (n + 1)) := by
  obtain ⟨C, hC⟩ := dlmf_2_11_6 p n hδ hδ'
  refine ⟨C, fun w h1 h2 hre => ?_⟩
  set w' := w - 2 * π * I
  have hw' : |w'.im| ≤ 3 * π / 2 - δ := by
    simp only [w', Complex.sub_im, Complex.mul_im]
    simp
    rw [abs_le]; constructor <;> linarith
  have hz : cexp w' = cexp w := by
    rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have hconn := dlmf_8_19_18 p w'
  rw [show w' + 2 * π * I = w by ring] at hconn
  have e : 2 * π * I * cexp (p * π * I) / Complex.Gamma p * cexp ((p - 1) * w') =
      2 * π * I * cexp (-(p * π * I)) / Complex.Gamma p * cexp ((p - 1) * w) := by
    have : cexp (p * π * I) * cexp ((p - 1) * w') = cexp (-(p * π * I)) * cexp ((p - 1) * w) := by
      rw [← Complex.exp_add, ← Complex.exp_add,
        show p * π * I + (p - 1) * w' = (-(p * π * I) + (p - 1) * w) + 2 * π * I by
          simp only [w']; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    calc 2 * π * I * cexp (p * π * I) / Complex.Gamma p * cexp ((p - 1) * w')
        = 2 * π * I / Complex.Gamma p * (cexp (p * π * I) * cexp ((p - 1) * w')) := by ring
      _ = _ := by rw [this]; ring
  rw [hconn, e, add_sub_cancel_left]
  have := hC w' hw' (by simpa [w'] using hre)
  rwa [hz] at this

/-! ### The added term: exponentially small near `ph z = π`, dominant past `ph z = 3π/2` -/

theorem norm_ratio_eq (p : ℂ) (x φ : ℝ) :
    ‖cexp ((p - 1) * (x + φ * I))‖ / ‖cexp (-cexp (x + φ * I)) / cexp (x + φ * I)‖ =
      Real.exp (Real.exp x * Real.cos φ + p.re * x - p.im * φ) := by
  rw [norm_div, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
  have h1 : ((p - 1) * (x + φ * I)).re = (p.re - 1) * x - p.im * φ := by simp
  have h2 : (-cexp (x + φ * I)).re = -(Real.exp x * Real.cos φ) := by simp [Complex.exp_re]
  have h3 : ((x : ℂ) + φ * I).re = x := by simp
  rw [h1, h2, h3, div_div_eq_mul_div, ← Real.exp_add, ← Real.exp_sub]
  congr 1; ring

theorem tendsto_exp_mul_cos_add (p : ℂ) (φ : ℝ) :
    Tendsto (fun x : ℝ => Real.cos φ + (p.re * x - p.im * φ) * Real.exp (-x)) atTop
      (𝓝 (Real.cos φ)) := by
  have h1 : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have := tendsto_const_nhds (x := Real.cos φ) |>.add ((h1.const_mul p.re).sub
    (h2.const_mul (p.im * φ)))
  simp only [mul_zero, sub_zero, add_zero] at this
  refine this.congr fun x => ?_
  ring

theorem exponent_eq (p : ℂ) (φ x : ℝ) :
    Real.exp x * Real.cos φ + p.re * x - p.im * φ =
      Real.exp x * (Real.cos φ + (p.re * x - p.im * φ) * Real.exp (-x)) := by
  rw [mul_add, show Real.exp x * ((p.re * x - p.im * φ) * Real.exp (-x)) =
    (p.re * x - p.im * φ) * (Real.exp x * Real.exp (-x)) by ring, ← Real.exp_add]
  simp
  ring

/-- Where `cos(ph z) < 0` (e.g. near `ph z = π`) the added term `z^{p−1}` of 2.11.7 is
exponentially small compared with `e^{−z}/z`. -/
theorem dlmf_2_11_ii_small (p : ℂ) {φ : ℝ} (hφ : Real.cos φ < 0) :
    Tendsto (fun x : ℝ => ‖cexp ((p - 1) * (x + φ * I))‖ /
      ‖cexp (-cexp (x + φ * I)) / cexp (x + φ * I)‖) atTop (𝓝 0) := by
  simp only [norm_ratio_eq, exponent_eq]
  exact Real.tendsto_exp_atBot.comp
    (Real.tendsto_exp_atTop.atTop_mul_neg hφ (tendsto_exp_mul_cos_add p φ))

/-- Where `cos(ph z) > 0` (past `ph z = 3π/2`) the added term dominates `e^{−z}/z`. -/
theorem dlmf_2_11_ii_dominant (p : ℂ) {φ : ℝ} (hφ : 0 < Real.cos φ) :
    Tendsto (fun x : ℝ => ‖cexp ((p - 1) * (x + φ * I))‖ /
      ‖cexp (-cexp (x + φ * I)) / cexp (x + φ * I)‖) atTop atTop := by
  simp only [norm_ratio_eq, exponent_eq]
  exact Real.tendsto_exp_atTop.comp
    (Real.tendsto_exp_atTop.atTop_mul_pos hφ (tendsto_exp_mul_cos_add p φ))

end Azurite.DLMF
