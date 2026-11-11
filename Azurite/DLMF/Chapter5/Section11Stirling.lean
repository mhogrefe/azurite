/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Psi
import Azurite.DLMF.Chapter2.Section10
import Azurite.DLMF.Chapter2.Section1Ritt
import Azurite.DLMF.Chapter2.Section1Expansion

/-!
# DLMF §5.11(i): Binet's function on the slit plane

Groundwork for <https://dlmf.nist.gov/5.11>. Binet's function `J(z) = Ln Γ(z) − (z − ½) ln z + z
− ½ ln(2π)` (5.9.10_2, `binetJ`, defined there for `ℜz > 0`) is extended to the slit plane
`|ph z| < π` by the Stieltjes-type integral

`J(z) = ∫₀^∞ φ(t)/(z + t)² dt`, `φ(t) = ({t} − {t}²)/2 = (B₂ − B̃₂(t))/2` (`stirlingJ`),

with `B̃ₖ(t) = Bₖ({t})` the periodic Bernoulli functions of §2.10. On `(0, ∞)` it is Stirling's
`μ` of §5.6 (`stirlingJ_ofReal`: `J(x) − J(x + 1) = (x + ½) ln(1 + 1/x) − 1` and `J(x) → 0`),
hence `Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + J(z))` on the slit plane (`Gamma_eq_exp_stirlingJ`,
identity theorem). The sector bound `|z + t| ≥ sin(½δ)(|z| + t)` for `|ph z| ≤ π − δ`
(`norm_add_ofReal_ge`) controls every integral.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### The sector bound -/

/-- For `|ph z| ≤ π − δ` and `t ≥ 0`: `|z + t| ≥ sin(½δ)(|z| + t)`. -/
theorem norm_add_ofReal_ge {z : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ π) (harg : |arg z| ≤ π - δ)
    {t : ℝ} (ht : 0 ≤ t) : Real.sin (δ / 2) * (‖z‖ + t) ≤ ‖z + t‖ := by
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 ≤ s := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : s ≤ 1 := Real.sin_le_one _
  -- `cos(ph z) ≥ cos(π − δ) = 2s² − 1`
  have hcos : 2 * s ^ 2 - 1 ≤ Real.cos (arg z) := by
    rw [← Real.cos_abs]
    have h1 : Real.cos (π - δ) ≤ Real.cos |arg z| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
    rw [Real.cos_pi_sub, show δ = 2 * (δ / 2) by ring, Real.cos_two_mul, Real.cos_sq'] at h1
    linarith
  have hre : ‖z‖ * (2 * s ^ 2 - 1) ≤ z.re := by
    rw [← norm_mul_cos_arg z]; exact mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
  have hsq : ‖z + t‖ ^ 2 = ‖z‖ ^ 2 + 2 * t * z.re + t ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have key : (s * (‖z‖ + t)) ^ 2 ≤ ‖z + t‖ ^ 2 := by
    rw [hsq]
    have hzt := norm_nonneg z
    nlinarith [mul_le_mul_of_nonneg_left hre (by positivity : (0 : ℝ) ≤ 2 * t),
      sq_nonneg (‖z‖ - t), mul_nonneg (sq_nonneg (‖z‖ - t)) (sub_nonneg.mpr (pow_le_one₀ hs0 hs1
        (n := 2)))]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp key

/-- `∫₀^∞ dt/(r + t)^m = 1/((m − 1) r^{m−1})` for `r > 0`, `m ≥ 2`. -/
theorem integral_inv_add_pow {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun t : ℝ => 1 / (r + t) ^ m) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 1 / (r + t) ^ m = 1 / ((m - 1) * r ^ (m - 1)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set g : ℝ → ℝ := fun t => -(1 / (((m : ℝ) - 1) * (r + t) ^ (m - 1))) with hg
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt g (1 / (r + t) ^ m) t := fun t ht => by
    have ht' : (0 : ℝ) ≤ t := ht
    have hrt : 0 < r + t := by linarith
    have h1 : HasDerivAt (fun t : ℝ => (r + t) ^ (m - 1))
        (((m - 1 : ℕ) : ℝ) * (r + t) ^ (m - 1 - 1))
        t := by
      simpa [Function.comp_def] using
        (hasDerivAt_pow (m - 1) (r + t)).comp t ((hasDerivAt_id' t).const_add r)
    have h2 := ((h1.const_mul ((m : ℝ) - 1)).inv (by positivity)).neg
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
    · have e1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      have e2 : (r + t) ^ m = (r + t) ^ (m - 1 - 1) * (r + t) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      have e3 : (r + t) ^ (m - 1) = (r + t) ^ (m - 1 - 1) * (r + t) := by
        rw [← pow_succ]; congr 1; omega
      rw [e1, e2, e3]
      have : (r + t) ^ (m - 1 - 1) ≠ 0 := by positivity
      field_simp
    · exact Eventually.of_forall fun u => by simp [hg, one_div]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (r + t) ^ m := fun t ht => by
    have : (0 : ℝ) < t := ht; positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => ((m : ℝ) - 1) * (r + t) ^ (m - 1)) atTop atTop :=
      Tendsto.const_mul_atTop (by linarith)
        ((tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ r tendsto_id))
    have := (h1.inv_tendsto_atTop).neg
    simpa [hg, one_div] using this
  have hint := integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  simp [hg]

/-! ### Binet's function in Stieltjes form -/

/-- `φ(t) = ({t} − {t}²)/2 ∈ [0, ⅛]`. -/
noncomputable def binetPhi2 (t : ℝ) : ℝ := (Int.fract t - Int.fract t ^ 2) / 2

theorem binetPhi2_nonneg (t : ℝ) : 0 ≤ binetPhi2 t := by
  unfold binetPhi2
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  nlinarith

theorem binetPhi2_le (t : ℝ) : binetPhi2 t ≤ 1 / 8 := by
  unfold binetPhi2
  nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

theorem binetPhi2_add_one (t : ℝ) : binetPhi2 (t + 1) = binetPhi2 t := by
  simp [binetPhi2]

theorem measurable_binetPhi2 : Measurable binetPhi2 := by
  unfold binetPhi2
  exact ((measurable_fract (R := ℝ)).sub ((measurable_fract (R := ℝ)).pow_const 2)).div_const 2

/-- Binet's function on the slit plane: `J(z) = ∫₀^∞ φ(t)/(z + t)² dt`. -/
noncomputable def stirlingJ (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), (binetPhi2 t : ℂ) / (z + t) ^ 2

/-- Integrability and the bound `|∫₀^∞ f(t)/(z + t)^m dt| ≤ C/(sin^m(½δ) (m − 1)|z|^{m−1})` for a
bounded measurable `f`, `|ph z| ≤ π − δ`, `m ≥ 2`. -/
theorem integrableOn_div_add_pow {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) (harg : |arg z| ≤ π - δ) {m : ℕ}
    (hm : 2 ≤ m) :
    IntegrableOn (fun t : ℝ => (f t : ℂ) / (z + t) ^ m) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ), (f t : ℂ) / (z + t) ^ m‖ ≤
        C / (Real.sin (δ / 2) ^ m * ((m - 1) * ‖z‖ ^ (m - 1))) := by
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨hI, hval⟩ := integral_inv_add_pow hr hm
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖(f t : ℂ) / (z + t) ^ m‖ ≤ C / s ^ m * (1 / (‖z‖ + t) ^ m) :=
    fun t ht => by
      have ht' : (0 : ℝ) ≤ t := le_of_lt ht
      have h1 := norm_add_ofReal_ge hδ.le hδπ harg ht'
      have hpos : 0 < s * (‖z‖ + t) := by positivity
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      calc |f t| / ‖z + t‖ ^ m ≤ C / (s * (‖z‖ + t)) ^ m := by
            gcongr
            · exact hC t
        _ = C / s ^ m * (1 / (‖z‖ + t) ^ m) := by rw [mul_pow]; field_simp
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (f t : ℂ) / (z + t) ^ m)
      (volume.restrict (Ioi 0)) := by
    have : Measurable fun t : ℝ => (f t : ℂ) / (z + t) ^ m := by
      have := hf; fun_prop
    exact this.aestronglyMeasurable
  have hint : IntegrableOn (fun t : ℝ => (f t : ℂ) / (z + t) ^ m) (Ioi 0) :=
    (hI.const_mul (C / s ^ m)).mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hbound))
  refine ⟨hint, ?_⟩
  calc ‖∫ t in Ioi (0 : ℝ), (f t : ℂ) / (z + t) ^ m‖
      ≤ ∫ t in Ioi (0 : ℝ), C / s ^ m * (1 / (‖z‖ + t) ^ m) :=
        norm_integral_le_of_norm_le (hI.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hbound))
    _ = C / (s ^ m * ((m - 1) * ‖z‖ ^ (m - 1))) := by
        rw [integral_const_mul, hval]; field_simp

theorem norm_stirlingJ_le {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π)
    (harg : |arg z| ≤ π - δ) :
    ‖stirlingJ z‖ ≤ 1 / 8 / (Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  have h := (integrableOn_div_add_pow measurable_binetPhi2 (C := 1 / 8) (fun t => by
    rw [abs_of_nonneg (binetPhi2_nonneg t)]; exact binetPhi2_le t) hz hδ hδπ harg le_rfl).2
  rw [stirlingJ]
  convert h using 3
  norm_num

/-! ### On `(0, ∞)`: Stirling's `μ` -/

/-- The real form `∫₀^∞ φ(t)/(x + t)² dt`. -/
noncomputable def stirlingJR (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), binetPhi2 t / (x + t) ^ 2

theorem integrableOn_stirlingJR {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => binetPhi2 t / (x + t) ^ 2) (Ioi 0) := by
  obtain ⟨hI, -⟩ := integral_inv_add_pow hx (le_refl 2)
  refine (hI.const_mul (1 / 8)).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun t ht => ?_))
  · exact (measurable_binetPhi2.div (by fun_prop)).aestronglyMeasurable
  · have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (div_nonneg (binetPhi2_nonneg t) (by positivity)), ← mul_one_div]
    exact mul_le_mul_of_nonneg_right (binetPhi2_le t) (by positivity)

theorem stirlingJ_ofReal {x : ℝ} : stirlingJ x = (stirlingJR x : ℂ) := by
  rw [stirlingJ, stirlingJR, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; rfl

/-- `∫₀¹ (t − t²)/(2(x + t)²) dt = (x + ½) ln(1 + 1/x) − 1`. -/
theorem integral_unit_binetPhi2 {x : ℝ} (hx : 0 < x) :
    ∫ t in (0 : ℝ)..1, (t - t ^ 2) / 2 / (x + t) ^ 2 = stirlingG x := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => (-t + (1 + 2 * x) * Real.log (x + t) +
      x * (1 + x) * (x + t)⁻¹) / 2) ((t - t ^ 2) / 2 / (x + t) ^ 2) t := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    have hxt : 0 < x + t := by linarith [ht.1]
    have h1 := ((hasDerivAt_id t).const_add x).log hxt.ne'
    have h2 := ((hasDerivAt_id t).const_add x).inv hxt.ne'
    have := ((((hasDerivAt_id t).neg).add (h1.const_mul (1 + 2 * x))).add
      (h2.const_mul (x * (1 + x)))).div_const 2
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      have hxt : x + t ≠ 0 := by linarith [ht.1]
      exact pow_ne_zero 2 hxt)),
    stirlingG, show 1 + 1 / x = (x + 1) / x by field_simp, Real.log_div (by linarith) hx.ne']
  simp only [add_zero, neg_zero]
  field_simp
  ring

theorem stirlingJR_sub {x : ℝ} (hx : 0 < x) : stirlingJR x - stirlingJR (x + 1) = stirlingG x := by
  set h : ℝ → ℝ := fun s => binetPhi2 s / (x + s) ^ 2 with hh
  have hint := integrableOn_stirlingJR hx
  -- `J(x + 1) = ∫_{(1, ∞)} φ(s)/(x + s)²`
  have hshift : stirlingJR (x + 1) = ∫ s in Ioi (1 : ℝ), h s := by
    rw [stirlingJR, ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
      ← integral_add_right_eq_self (μ := volume) (fun s => (Ioi (1 : ℝ)).indicator h s) 1]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [indicator, mem_Ioi, hh]
    split_ifs with h1 h2 h2
    · rw [binetPhi2_add_one]; ring_nf
    · exact absurd (by linarith : 1 < t + 1) h2
    · exact absurd (by linarith : (0 : ℝ) < t) h1
    · rfl
  rw [hshift, stirlingJR, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)),
    add_sub_cancel_right, ← integral_unit_binetPhi2 hx, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [binetPhi2, Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩]

theorem stirlingJR_eq_stirlingMu {x : ℝ} (hx : 0 < x) : stirlingJR x = stirlingMu x := by
  set D : ℝ → ℝ := fun y => stirlingMu y - stirlingJR y with hD
  have hper : ∀ N : ℕ, D (x + N) = D x := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      have hxn : 0 < x + n := by positivity
      have := stirlingJR_sub hxn
      have := stirlingMu_sub hxn
      simp only [hD] at ih ⊢
      push_cast
      rw [← add_assoc]
      linarith
  have hJ : Tendsto (fun N : ℕ => stirlingJR (x + N)) atTop (𝓝 0) := by
    have hb : ∀ N : ℕ, |stirlingJR (x + N)| ≤ 1 / 8 / (x + N) := fun N => by
      have hxN : 0 < x + N := by positivity
      have h := norm_stirlingJ_le (z := ((x + N : ℝ) : ℂ)) (by exact_mod_cast hxN.ne')
        (δ := π) Real.pi_pos le_rfl (by
          rw [arg_ofReal_of_nonneg hxN.le, abs_zero, sub_self])
      rw [stirlingJ_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_of_nonneg hxN.le, show π / 2 = π / 2 from rfl, Real.sin_pi_div_two] at h
      simpa using h
    exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N)
      (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_left _ x (tendsto_natCast_atTop_atTop (R := ℝ))))
  have hlim : Tendsto (fun N : ℕ => D (x + N)) atTop (𝓝 0) := by
    simpa [hD] using (tendsto_stirlingMu hx).sub hJ
  simp_rw [hper] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  simp only [hD] at this
  linarith

/-! ### Holomorphy and `Γ` on the slit plane -/

theorem hasDerivAt_stirlingJ {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    HasDerivAt stirlingJ (∫ t in Ioi (0 : ℝ), -(2 * (binetPhi2 t : ℂ)) / (z₀ + t) ^ 3) z₀ := by
  have hπ := Real.pi_pos
  have hz0 := slitPlane_ne_zero hz₀
  have hargz : |arg z₀| < π := abs_lt.mpr ⟨by linarith [neg_pi_lt_arg z₀],
    lt_of_le_of_ne (arg_le_pi z₀) (slitPlane_arg_ne_pi hz₀)⟩
  set δ := (π - |arg z₀|) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδπ : δ ≤ π := by rw [hδdef]; linarith [abs_nonneg (arg z₀)]
  set r := ‖z₀‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; have := norm_pos_iff.mpr hz0; linarith
  set N : Set ℂ := {w | w ∈ slitPlane ∧ |arg w| < π - δ ∧ r < ‖w‖} with hN
  have hNnhds : N ∈ 𝓝 z₀ := by
    have h0 : ∀ᶠ w in 𝓝 z₀, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz₀
    have h1 : ∀ᶠ w in 𝓝 z₀, |arg w| < π - δ :=
      (continuous_abs.continuousAt.comp (continuousAt_arg hz₀)).eventually
        (gt_mem_nhds (show (abs ∘ arg) z₀ < π - δ by
          simp only [Function.comp]; rw [hδdef]; linarith))
    have h2 : ∀ᶠ w in 𝓝 z₀, r < ‖w‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by
        rw [hr]; have := norm_pos_iff.mpr hz0; linarith))
    exact h0.and (h1.and h2)
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  obtain ⟨hI3, -⟩ := integral_inv_add_pow hr0 (m := 3) (by norm_num)
  have hC : ∀ t, |binetPhi2 t| ≤ 1 / 8 := fun t => by
    rw [abs_of_nonneg (binetPhi2_nonneg t)]; exact binetPhi2_le t
  have hint : ∀ w ∈ N, IntegrableOn (fun t : ℝ => (binetPhi2 t : ℂ) / (w + t) ^ 2) (Ioi 0) :=
    fun w hw => (integrableOn_div_add_pow measurable_binetPhi2 hC (slitPlane_ne_zero hw.1) hδ hδπ
      hw.2.1.le le_rfl).1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => (binetPhi2 t : ℂ) / (w + t) ^ 2)
    (F' := fun w (t : ℝ) => -(2 * (binetPhi2 t : ℂ)) / (w + t) ^ 3) (x₀ := z₀)
    (bound := fun t => 1 / 4 / s ^ 3 * (1 / (r + t) ^ 3)) hNnhds
    (eventually_of_mem hNnhds fun w hw => (hint w hw).aestronglyMeasurable)
    (hint z₀ ⟨hz₀, by rw [hδdef]; linarith, by rw [hr]; have := norm_pos_iff.mpr hz0; linarith⟩)
    (by
      have : Measurable fun t : ℝ => -(2 * (binetPhi2 t : ℂ)) / (z₀ + t) ^ 3 := by
        have := measurable_binetPhi2; fun_prop
      exact this.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw => by
      have ht' : (0 : ℝ) ≤ t := le_of_lt ht
      have h1 := norm_add_ofReal_ge hδ.le hδπ hw.2.1.le ht'
      have h2 : s * (r + t) ≤ s * (‖w‖ + t) := by gcongr; exact hw.2.2.le
      have hpos : 0 < s * (r + t) := by positivity
      rw [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (binetPhi2_nonneg t), show ‖(2 : ℂ)‖ = 2 by simp]
      calc 2 * binetPhi2 t / ‖w + t‖ ^ 3 ≤ 2 * (1 / 8) / (s * (r + t)) ^ 3 := by
            gcongr
            · exact binetPhi2_le t
            · exact h2.trans h1
        _ = 1 / 4 / s ^ 3 * (1 / (r + t) ^ 3) := by rw [mul_pow]; field_simp; ring))
    (hI3.const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw => by
      have ht' : (0 : ℝ) < t := ht
      have hne : w + t ≠ 0 := slitPlane_ne_zero (by
        have := hw.1
        rw [mem_slitPlane_iff] at this ⊢
        rcases this with h | h
        · left; simp; linarith
        · right; simpa using h)
      have h0 := (hasDerivAt_pow 2 (w + t)).comp w ((hasDerivAt_id' w).add_const (t : ℂ))
      have h := (h0.inv (by simpa [Function.comp] using pow_ne_zero 2 hne)).const_mul
        (binetPhi2 t : ℂ)
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
      · simp only [Function.comp]
        field_simp
        ring
      · simp [Function.comp, div_eq_mul_inv]))
  exact key.2

theorem differentiableOn_stirlingJ : DifferentiableOn ℂ stirlingJ slitPlane := fun _ hz =>
  (hasDerivAt_stirlingJ hz).differentiableAt.differentiableWithinAt

/-- `Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + J(z))` on the slit plane `|ph z| < π`. -/
theorem Gamma_eq_exp_stirlingJ {z : ℂ} (hz : z ∈ slitPlane) :
    Gamma z = cexp ((z - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) +
      stirlingJ z) := by
  have hUo : IsOpen slitPlane := isOpen_slitPlane
  have hΓ : AnalyticOnNhd ℂ Gamma slitPlane := DifferentiableOn.analyticOnNhd (fun w hw =>
    (differentiableAt_Gamma w fun m h => by
      rw [h] at hw
      simp [mem_slitPlane_iff] at hw; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      ).differentiableWithinAt)
    hUo
  have hR : AnalyticOnNhd ℂ (fun w => cexp ((w - 1 / 2) * Complex.log w - w +
      1 / 2 * Complex.log (2 * π) + stirlingJ w)) slitPlane :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (((((differentiableAt_id.sub_const _).mul (differentiableAt_log hw)).sub
        differentiableAt_id).add_const _).add
        ((differentiableOn_stirlingJ w hw).differentiableAt (hUo.mem_nhds hw))).cexp
        |>.differentiableWithinAt) hUo
  have heq := eqOn_of_eq_on_pos_reals hΓ hR
    (StarConvex.isPathConnected starConvex_one_slitPlane (by simp)).isConnected.isPreconnected hUo
    (by simp) (fun x hx _ => by
      rw [stirlingJ_ofReal, stirlingJR_eq_stirlingMu hx, stirlingMu, Gamma_ofReal,
        ← ofReal_log hx.le, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_log (by positivity)]
      have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
      rw [show ((x : ℂ) - 1 / 2) * (Real.log x : ℂ) - x + 1 / 2 * (Real.log (2 * π) : ℂ) +
          ((Real.log (Real.Gamma x) - (x - 1 / 2) * Real.log x + x - 1 / 2 * Real.log (2 * π) :
            ℝ) : ℂ) = ((Real.log (Real.Gamma x) : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_exp, Real.exp_log hG]) hz
  exact heq

/-! ### Stirling's series: integration by parts against `B̃ₖ` -/

theorem measurable_periodicBernoulli (k : ℕ) : Measurable (periodicBernoulli k) :=
  (continuous_bernoulliFun k).measurable.comp measurable_fract

/-- `Kₘ(z) = ∫₀^∞ B̃ₘ(t)/(z + t)^m dt`. -/
noncomputable def stirlingK (m : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (periodicBernoulli m t : ℂ) / (z + t) ^ m

theorem add_ofReal_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    z + t ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp; linarith
  · right; simpa using h

/-- The sector parameter `δ = π − |ph z|` of a point of the slit plane. -/
theorem slitPlane_sector {z : ℂ} (hz : z ∈ slitPlane) :
    0 < π - |arg z| ∧ π - |arg z| ≤ π ∧ |arg z| ≤ π - (π - |arg z|) := by
  have : |arg z| < π := abs_lt.mpr ⟨by linarith [neg_pi_lt_arg z],
    lt_of_le_of_ne (arg_le_pi z) (slitPlane_arg_ne_pi hz)⟩
  exact ⟨by linarith, by linarith [abs_nonneg (arg z)], by linarith⟩

theorem integrableOn_stirlingK (m : ℕ) (hm : 2 ≤ m) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (periodicBernoulli m t : ℂ) / (z + t) ^ m) (Ioi 0) := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound m
  obtain ⟨h1, h2, h3⟩ := slitPlane_sector hz
  exact (integrableOn_div_add_pow (measurable_periodicBernoulli m) (C := C) hC
    (slitPlane_ne_zero hz) h1 h2 h3 hm).1

theorem norm_stirlingK_le (m : ℕ) (hm : 2 ≤ m) : ∃ C, ∀ {z : ℂ} {δ : ℝ}, z ≠ 0 → 0 < δ → δ ≤ π →
    |arg z| ≤ π - δ → ‖stirlingK m z‖ ≤ C / (Real.sin (δ / 2) ^ m * ((m - 1) * ‖z‖ ^ (m - 1))) := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound m
  exact ⟨C, fun hz hδ hδπ harg =>
    (integrableOn_div_add_pow (measurable_periodicBernoulli m) (C := C) hC hz hδ hδπ harg hm).2⟩

/-- `∫₀^∞ dt/(z + t)² = 1/z` on the slit plane. -/
theorem integral_inv_add_sq {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => 1 / (z + t) ^ 2) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 1 / (z + t) ^ 2 = 1 / z := by
  obtain ⟨h1, h2, h3⟩ := slitPlane_sector hz
  have hint := (integrableOn_div_add_pow (f := fun _ => 1) measurable_const (C := 1)
    (fun _ => by simp) (slitPlane_ne_zero hz) h1 h2 h3 le_rfl).1
  simp only [ofReal_one] at hint
  refine ⟨hint, ?_⟩
  have hne : ∀ t : ℝ, 0 ≤ t → z + t ≠ 0 := fun t ht =>
    slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -(1 / (z + t))) (1 / (z + t) ^ 2) t :=
    fun t ht => by
      have h0 : HasDerivAt (fun t : ℝ => z + t) 1 t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).const_add z
      have := (h0.inv (hne t ht)).neg
      refine (this.congr_deriv (by simp [div_eq_mul_inv])).congr_of_eventuallyEq
        (Eventually.of_forall fun u => by simp [one_div])
  have hlim : Tendsto (fun t : ℝ => -(1 / (z + t))) atTop (𝓝 0) := by
    have hn : Tendsto (fun t : ℝ => ‖z + t‖) atTop atTop := by
      refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖z‖) tendsto_id)
      have h1 : ‖(t : ℂ)‖ ≤ ‖z + t‖ + ‖z‖ := by
        have := norm_sub_le (z + t) z; simpa using this
      have h' : t ≤ ‖(t : ℂ)‖ := by rw [Complex.norm_real]; exact le_abs_self t
      simp only [id]
      linarith
    have := (tendsto_inv_atTop_zero.comp hn)
    refine (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
    simpa [norm_neg, one_div, Function.comp_def] using this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  simp

theorem stirlingJ_eq_K2 {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingJ z = (bernoulli 2 : ℂ) / (2 * z) - stirlingK 2 z / 2 := by
  obtain ⟨hI, hv⟩ := integral_inv_add_sq hz
  have hK := integrableOn_stirlingK 2 le_rfl hz
  have hpt : ∀ t : ℝ, (binetPhi2 t : ℂ) / (z + t) ^ 2 = (bernoulli 2 : ℂ) / 2 * (1 / (z + t) ^ 2) -
      1 / 2 * ((periodicBernoulli 2 t : ℂ) / (z + t) ^ 2) := fun t => by
    simp only [binetPhi2, periodicBernoulli, bernoulliFun_two, bernoulli_two]
    push_cast
    ring
  rw [stirlingJ]
  simp_rw [hpt]
  rw [integral_sub (hI.const_mul _) (hK.const_mul _), integral_const_mul, integral_const_mul, hv]
  rw [stirlingK]
  field_simp

/-- One integration by parts on `[j, j + 1]`. -/
theorem stirling_ibp_unit {m : ℕ} (hm : 1 ≤ m) {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    ∫ t in (j : ℝ)..(j + 1), ((m + 1 : ℂ) * ((periodicBernoulli m t : ℂ) / (z + t) ^ m) -
      m * ((periodicBernoulli (m + 1) t : ℂ) / (z + t) ^ (m + 1))) =
      bernoulli (m + 1) * (1 / (z + ((j + 1 : ℝ) : ℂ)) ^ m - 1 / (z + (j : ℂ)) ^ m) := by
  have hne : ∀ t : ℝ, 0 ≤ t → z + t ≠ 0 := fun t ht =>
    slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  set F : ℝ → ℂ := fun t => (bernoulliFun (m + 1) (t - j) : ℂ) / (z + t) ^ m with hF
  set F' : ℝ → ℂ := fun t => (m + 1 : ℂ) * ((bernoulliFun m (t - j) : ℂ) / (z + t) ^ m) -
    m * ((bernoulliFun (m + 1) (t - j) : ℂ) / (z + t) ^ (m + 1)) with hF'
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have hd : ∀ t ∈ uIcc (j : ℝ) (j + 1), HasDerivAt F (F' t) t := fun t ht => by
    rw [uIcc_of_le (by linarith)] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hb : HasDerivAt (fun t : ℝ => (bernoulliFun (m + 1) (t - j) : ℂ))
        (((m + 1 : ℕ) : ℝ) * bernoulliFun m (t - j) : ℝ) t := by
      have := (hasDerivAt_bernoulliFun (m + 1) (t - j)).comp t ((hasDerivAt_id t).sub_const (j : ℝ))
      simpa using this.ofReal_comp
    have h0 : HasDerivAt (fun t : ℝ => z + t) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_add z
    have hp := (hasDerivAt_pow m (z + t)).comp t h0
    have := hb.div hp (pow_ne_zero m (hne t ht0))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun u => rfl)
    simp only [hF', Function.comp]
    have h1 := hne t ht0
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    push_cast
    field_simp
    ring
  have hcont : ContinuousOn F' (uIcc (j : ℝ) (j + 1)) := fun t ht => by
    rw [uIcc_of_le (by linarith)] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h1 := hne t ht0
    simp only [hF']
    refine ContinuousAt.continuousWithinAt ?_
    have hc1 : Continuous fun t : ℝ => (bernoulliFun m (t - j) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_bernoulliFun m).comp (continuous_sub_right _))
    have hc2 : Continuous fun t : ℝ => (bernoulliFun (m + 1) (t - j) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_bernoulliFun _).comp (continuous_sub_right _))
    exact (continuousAt_const.mul (hc1.continuousAt.div (by fun_prop) (pow_ne_zero _ h1))).sub
      (continuousAt_const.mul (hc2.continuousAt.div (by fun_prop) (pow_ne_zero _ h1)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hcongr : ∫ t in (j : ℝ)..(j + 1), ((m + 1 : ℂ) * ((periodicBernoulli m t : ℂ) /
      (z + t) ^ m) - m * ((periodicBernoulli (m + 1) t : ℂ) / (z + t) ^ (m + 1))) =
      ∫ t in (j : ℝ)..(j + 1), F' t := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le
      (by linarith), integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hf : Int.fract t = t - j := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith [ht.1], by linarith [ht.2], ⟨j, by push_cast; ring⟩⟩
    simp only [hF', periodicBernoulli, hf]
  rw [hcongr, hFTC]
  simp only [hF, sub_self, show (j : ℝ) + 1 - j = 1 by ring,
    bernoulliFun_endpoints_eq_of_ne_one (show m + 1 ≠ 1 by omega), bernoulliFun_eval_zero]
  push_cast
  ring

/-- `(m + 1) Kₘ(z) − m K_{m+1}(z) = −B_{m+1}/z^m` (`m ≥ 2`). -/
theorem stirlingK_rec {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hz : z ∈ slitPlane) :
    (m + 1 : ℂ) * stirlingK m z - m * stirlingK (m + 1) z = -(bernoulli (m + 1) / z ^ m) := by
  set G : ℝ → ℂ := fun t => (m + 1 : ℂ) * ((periodicBernoulli m t : ℂ) / (z + t) ^ m) -
    m * ((periodicBernoulli (m + 1) t : ℂ) / (z + t) ^ (m + 1)) with hG
  have hGi : IntegrableOn G (Ioi 0) :=
    ((integrableOn_stirlingK m hm hz).const_mul _).sub
      ((integrableOn_stirlingK (m + 1) (by omega) hz).const_mul _)
  have hII : ∀ k : ℕ, IntervalIntegrable G volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).mpr
      (hGi.mono_set fun t ht => by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; exact lt_of_le_of_lt this ht.1)
  have hN : ∀ N : ℕ, ∫ t in (0 : ℝ)..(N : ℝ), G t =
      bernoulli (m + 1) * (1 / (z + (N : ℂ)) ^ m - 1 / z ^ m) := fun N => by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := N) (fun k _ => hII k)
    simp only [Nat.cast_zero] at h
    rw [← h]
    have e : ∀ k ∈ Finset.range N, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), G t =
        bernoulli (m + 1) * (1 / (z + ((k + 1 : ℕ) : ℂ)) ^ m - 1 / (z + (k : ℂ)) ^ m) :=
      fun k _ => by
        have := stirling_ibp_unit (m := m) (by omega) hz k
        push_cast at this ⊢
        exact this
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_range_sub
      (fun k : ℕ => 1 / (z + (k : ℂ)) ^ m)]
    simp
  have hlim1 : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), G t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), G t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hGi tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), G t) atTop
      (𝓝 (bernoulli (m + 1) * (0 - 1 / z ^ m))) := by
    simp_rw [hN]
    refine tendsto_const_nhds.mul (Tendsto.sub ?_ tendsto_const_nhds)
    have hn : Tendsto (fun N : ℕ => ‖z + (N : ℂ)‖) atTop atTop := by
      refine tendsto_atTop_mono (fun N => ?_)
        (tendsto_atTop_add_const_right _ (-‖z‖) (tendsto_natCast_atTop_atTop (R := ℝ)))
      have h1 : ‖(N : ℂ)‖ ≤ ‖z + N‖ + ‖z‖ := by
        have := norm_sub_le (z + N) z; simpa using this
      rw [Complex.norm_natCast] at h1
      linarith
    have hpow : Tendsto (fun N : ℕ => ‖z + (N : ℂ)‖ ^ m) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp hn
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine hpow.inv_tendsto_atTop.congr fun N => ?_
    simp [norm_pow, norm_inv, one_div]
  have hval := tendsto_nhds_unique hlim1 hlim2
  rw [hG, integral_sub ((integrableOn_stirlingK m hm hz).const_mul _)
    ((integrableOn_stirlingK (m + 1) (by omega) hz).const_mul _), integral_const_mul,
    integral_const_mul] at hval
  rw [stirlingK, stirlingK]
  rw [hval]
  ring

/-- **Stirling's series with remainder**: for `m ≥ 0`,
`J(z) = ∑_{j=0}^{m} B_{j+2}/((j + 2)(j + 1) z^{j+1}) − K_{m+2}(z)/(m + 2)`. -/
theorem stirlingJ_eq_sum {z : ℂ} (hz : z ∈ slitPlane) (m : ℕ) :
    stirlingJ z = ∑ j ∈ Finset.range (m + 1),
      (bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1) * z ^ (j + 1)) -
        stirlingK (m + 2) z / (m + 2) := by
  have hz0 := slitPlane_ne_zero hz
  induction m with
  | zero =>
    rw [stirlingJ_eq_K2 hz]
    simp
  | succ m ih =>
    have hrec := stirlingK_rec (m := m + 2) (by omega) hz
    have h3 : (z ^ (m + 2)) ≠ 0 := pow_ne_zero _ hz0
    have h1 : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
    have h2 : (m : ℂ) + 3 ≠ 0 := by exact_mod_cast (by omega : m + 3 ≠ 0)
    push_cast at hrec
    have hrec' : (((m : ℂ) + 3) * stirlingK (m + 2) z - ((m : ℂ) + 2) * stirlingK (m + 3) z) *
        z ^ (m + 2) = -(bernoulli (m + 3) : ℂ) := by
      rw [show (m : ℂ) + 3 = m + 2 + 1 by ring, show m + 3 = m + 2 + 1 by ring, hrec]
      field_simp
    have hK2 : stirlingK (m + 2) z = (((m : ℂ) + 2) * stirlingK (m + 3) z * z ^ (m + 2) -
        bernoulli (m + 3)) / (((m : ℂ) + 3) * z ^ (m + 2)) := by
      field_simp
      linear_combination hrec'
    rw [ih, Finset.sum_range_succ (n := m + 1), show m + 1 + 2 = m + 3 by ring,
      show m + 1 + 1 = m + 2 by ring]
    have hkey : -(stirlingK (m + 2) z / ((m : ℂ) + 2)) =
        (bernoulli (m + 3) : ℂ) / (((m : ℂ) + 3) * ((m : ℂ) + 2) *
          z ^ (m + 2)) - stirlingK (m + 3) z / ((m : ℂ) + 3) := by
      rw [hK2]
      field_simp
      ring
    push_cast
    rw [show (m : ℂ) + 1 + 2 = m + 3 by ring, show (m : ℂ) + 1 + 1 = m + 2 by ring]
    linear_combination hkey

/-! ### DLMF 5.11.1 -/

/-- The coefficients of Stirling's series in powers of `1/z`: `a₀ = 0`,
`aₛ = B_{s+1}/((s + 1)s)` (`s ≥ 1`), so `a_{2k−1} = B_{2k}/(2k(2k − 1))` and `a_{2k} = 0`. -/
noncomputable def stirlingSeriesCoeff (s : ℕ) : ℂ :=
  if s = 0 then 0 else (bernoulli (s + 1) : ℂ) / (((s : ℂ) + 1) * s)

theorem stirlingSeriesCoeff_odd {k : ℕ} (hk : 1 ≤ k) :
    stirlingSeriesCoeff (2 * k - 1) = (bernoulli (2 * k) : ℂ) / (2 * k * (2 * k - 1)) := by
  rw [stirlingSeriesCoeff, ite_eq_right (by omega), show 2 * k - 1 + 1 = 2 * k by omega,
    Nat.cast_sub (by omega)]
  push_cast
  ring_nf

theorem stirlingSeriesCoeff_even {k : ℕ} (hk : 1 ≤ k) : stirlingSeriesCoeff (2 * k) = 0 := by
  rw [stirlingSeriesCoeff, ite_eq_right (by omega), bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]
  simp

theorem sum_stirlingSeriesCoeff (z : ℂ) (n : ℕ) :
    ∑ s ∈ Finset.range (n + 1), stirlingSeriesCoeff s * z ^ (-(s : ℤ)) =
      ∑ j ∈ Finset.range n, (bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1) * z ^ (j + 1)) := by
  rw [Finset.sum_range_succ']
  simp only [stirlingSeriesCoeff, Nat.succ_ne_zero, ↓reduceIte, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [zpow_neg, zpow_natCast]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem stirlingJ_sub_sum {z : ℂ} (hz : z ∈ slitPlane) {n : ℕ} (hn : 1 ≤ n) :
    stirlingJ z - ∑ s ∈ Finset.range n, stirlingSeriesCoeff s * z ^ (-(s : ℤ)) =
      stirlingSeriesCoeff n * z ^ (-(n : ℤ)) - stirlingK (n + 1) z / (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := sum_stirlingSeriesCoeff z (m + 1)
  rw [Finset.sum_range_succ] at h
  rw [stirlingJ_eq_sum hz m, show m + 2 = m + 1 + 1 by ring]
  push_cast
  rw [show (m : ℂ) + 2 = m + 1 + 1 by ring]
  push_cast at h
  linear_combination -h

/-- **DLMF 5.11.1** (Stirling's series): with `J` holomorphic on the slit plane and
`Γ(z) = exp((z − ½) ln z − z + ½ ln(2π) + J(z))` there (so `J(z) = Ln Γ(z) − (z − ½) ln z + z −
½ ln(2π)` for a value of `Ln Γ(z)`), `J(z) ∼ ∑_{k≥1} B_{2k}/(2k(2k − 1) z^{2k−1})` as `z → ∞` in
`|ph z| ≤ π − δ` (the coefficients `stirlingSeriesCoeff`, see `stirlingSeriesCoeff_odd`,
`stirlingSeriesCoeff_even`). -/
theorem dlmf_5_11_1 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    (∀ z ∈ slitPlane, Gamma z = cexp ((z - 1 / 2) * Complex.log z - z +
      1 / 2 * Complex.log (2 * π) + stirlingJ z)) ∧
      IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) stirlingJ stirlingSeriesCoeff := by
  refine ⟨fun z hz => Gamma_eq_exp_stirlingJ hz, fun n hn => ?_⟩
  obtain ⟨C, hC⟩ := norm_stirlingK_le (n + 1) (by omega)
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine isBoundedUnder_of_eventually_le (a := ‖stirlingSeriesCoeff n‖ +
    C / (s ^ (n + 1) * n) / (n + 1)) ?_
  refine Filter.eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
  obtain ⟨hz0, harg⟩ := hz
  simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at harg
  have hslit : z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hz0⟩
  have hK := hC hz0 hδ hδπ harg
  have hzn : ‖z‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)
  dsimp only
  rw [stirlingJ_sub_sum hslit hn, sub_div, mul_div_assoc, div_self (zpow_ne_zero _ hz0), mul_one]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  push_cast at hK
  have h1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have e : ‖stirlingK (n + 1) z / ((n : ℂ) + 1) / z ^ (-(n : ℤ))‖ =
      ‖stirlingK (n + 1) z‖ * ‖z‖ ^ n / ((n : ℝ) + 1) := by
    rw [norm_div, norm_div, norm_zpow, zpow_neg, zpow_natCast, h1]
    field_simp
  rw [e]
  calc ‖stirlingK (n + 1) z‖ * ‖z‖ ^ n / ((n : ℝ) + 1)
      ≤ C / (s ^ (n + 1) * (n * ‖z‖ ^ n)) * ‖z‖ ^ n / ((n : ℝ) + 1) := by
        gcongr
        rw [show (n : ℝ) + 1 - 1 = n by ring] at hK
        exact hK
    _ = C / (s ^ (n + 1) * n) / (n + 1) := by field_simp

/-! ### Differentiation under the integral sign -/

/-- `∂/∂z ∫₀^∞ f(t)/(z + t)^m dt = −m ∫₀^∞ f(t)/(z + t)^{m+1} dt` on the slit plane, for a
bounded measurable `f` and `m ≥ 2`. -/
theorem hasDerivAt_integral_div_add_pow {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) {m : ℕ} (hm : 2 ≤ m) {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    HasDerivAt (fun z => ∫ t in Ioi (0 : ℝ), (f t : ℂ) / (z + t) ^ m)
      (∫ t in Ioi (0 : ℝ), -((m : ℂ) * (f t : ℂ)) / (z₀ + t) ^ (m + 1)) z₀ := by
  have hπ := Real.pi_pos
  have hz0 := slitPlane_ne_zero hz₀
  obtain ⟨hδ, hδπ, -⟩ := slitPlane_sector hz₀
  set δ := (π - |arg z₀|) / 2 with hδdef
  have hδ' : 0 < δ := by rw [hδdef]; linarith
  have hδπ' : δ ≤ π := by rw [hδdef]; linarith [abs_nonneg (arg z₀)]
  set r := ‖z₀‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; have := norm_pos_iff.mpr hz0; linarith
  set N : Set ℂ := {w | w ∈ slitPlane ∧ |arg w| < π - δ ∧ r < ‖w‖} with hN
  have hNnhds : N ∈ 𝓝 z₀ := by
    have h0 : ∀ᶠ w in 𝓝 z₀, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hz₀
    have h1 : ∀ᶠ w in 𝓝 z₀, |arg w| < π - δ :=
      (continuous_abs.continuousAt.comp (continuousAt_arg hz₀)).eventually
        (gt_mem_nhds (show (abs ∘ arg) z₀ < π - δ by
          simp only [Function.comp]; rw [hδdef]; linarith))
    have h2 : ∀ᶠ w in 𝓝 z₀, r < ‖w‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by
        rw [hr]; have := norm_pos_iff.mpr hz0; linarith))
    exact h0.and (h1.and h2)
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  obtain ⟨hI, -⟩ := integral_inv_add_pow hr0 (m := m + 1) (by omega)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hint : ∀ w ∈ N, IntegrableOn (fun t : ℝ => (f t : ℂ) / (w + t) ^ m) (Ioi 0) :=
    fun w hw => (integrableOn_div_add_pow hf hC (slitPlane_ne_zero hw.1) hδ' hδπ'
      hw.2.1.le hm).1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => (f t : ℂ) / (w + t) ^ m)
    (F' := fun w (t : ℝ) => -((m : ℂ) * (f t : ℂ)) / (w + t) ^ (m + 1)) (x₀ := z₀)
    (bound := fun t => m * C / s ^ (m + 1) * (1 / (r + t) ^ (m + 1))) hNnhds
    (eventually_of_mem hNnhds fun w hw => (hint w hw).aestronglyMeasurable)
    (hint z₀ ⟨hz₀, by rw [hδdef]; linarith, by rw [hr]; have := norm_pos_iff.mpr hz0; linarith⟩)
    (by
      have : Measurable fun t : ℝ => -((m : ℂ) * (f t : ℂ)) / (z₀ + t) ^ (m + 1) := by
        have := hf; fun_prop
      exact this.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw => by
      have ht' : (0 : ℝ) ≤ t := le_of_lt ht
      have h1 := norm_add_ofReal_ge hδ'.le hδπ' hw.2.1.le ht'
      have h2 : s * (r + t) ≤ s * (‖w‖ + t) := by gcongr; exact hw.2.2.le
      have hpos : 0 < s * (r + t) := by positivity
      rw [norm_div, norm_neg, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_natCast]
      calc (m : ℝ) * |f t| / ‖w + t‖ ^ (m + 1) ≤ m * C / (s * (r + t)) ^ (m + 1) := by
            gcongr
            · exact hC t
            · exact h2.trans h1
        _ = m * C / s ^ (m + 1) * (1 / (r + t) ^ (m + 1)) := by rw [mul_pow]; field_simp))
    (hI.const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw => by
      have ht' : (0 : ℝ) ≤ t := le_of_lt ht
      have hne : w + t ≠ 0 := slitPlane_ne_zero (add_ofReal_mem_slitPlane hw.1 ht')
      have h0 := (hasDerivAt_pow m (w + t)).comp w ((hasDerivAt_id' w).add_const (t : ℂ))
      have h := (h0.inv (by simpa [Function.comp] using pow_ne_zero m hne)).const_mul
        (f t : ℂ)
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
      · simp only [Function.comp]
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        push_cast
        field_simp
        ring
      · simp [Function.comp, div_eq_mul_inv]))
  exact key.2

end Azurite.DLMF
