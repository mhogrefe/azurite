/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13OmegaAux
import Azurite.DLMF.Chapter4.Section13Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# DLMF §4.13: the Wright `ω`-function

`ω(z) = W(e^z)` (4.13.1_2) is the unique `y` with `y + ln y = z`, except on the two half-lines
`L± = {t ± iπ : t ≤ −1}`. On `L₊` there are two (real) solutions; on `L₋` there is none, and `ω`
is defined by continuity from below in both cases (`ω(t + iπ) = W₀(−e^t)`,
`ω(t − iπ) = W_{−1}(−e^t)`).

* `existsUnique_omega`: for `ζ ∉ L₋` there is exactly one `y ≠ 0` with `y + ln y = ζ` (taking the
  root `≥ −1` on `L₊`). The proof writes `y = ρ e^{iα}` and reduces to the strictly monotone
  `omegaG` of `Section13OmegaAux`.
* `wrightOmega`, `dlmf_4_13_1_2` (off `L₋`), `wrightOmega_add_log_of_mem` (on `L₋`,
  `ω + ln ω = z + 2πi`: **erratum**, 4.13.1_2 fails there), `wrightOmega_mul_exp`
  (`ω e^ω = e^z` everywhere).
* `hasDerivAt_wrightOmega`: `ω` is analytic off `L₊ ∪ L₋`, with `ω′ = ω/(1 + ω)`.
-/

open Set Filter Topology Complex
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-! ### `y + ln y` in polar form -/

theorem add_log_re (y : ℂ) : (y + log y).re = y.re + Real.log ‖y‖ := by simp [log_re]

theorem add_log_im (y : ℂ) : (y + log y).im = y.im + arg y := by simp [log_im]

theorem arg_mem_Ioo_of_im_pos {y : ℂ} (hy : 0 < y.im) : arg y ∈ Ioo 0 π := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr fun h => by rw [h] at hy; simp at hy
  have hs : 0 < Real.sin (arg y) := by
    have := norm_mul_sin_arg y; rw [← this] at hy; exact pos_of_mul_pos_right hy hn.le
  refine ⟨?_, lt_of_le_of_ne (arg_le_pi y) fun h => by rw [h, Real.sin_pi] at hs; simp at hs⟩
  by_contra h; push Not at h
  exact absurd hs (not_lt.mpr (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (neg_pi_lt_arg y).le))

theorem arg_mem_Ioo_of_im_neg {y : ℂ} (hy : y.im < 0) : arg y ∈ Ioo (-π) 0 := by
  have h := arg_mem_Ioo_of_im_pos (y := conj y) (by simpa using hy)
  have hne : arg y ≠ π := fun h' => by
    have := arg_eq_pi_iff.mp h'; linarith [this.2]
  rw [arg_conj] at h
  simp only [hne, ↓reduceIte] at h
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Upper half-plane solutions correspond to roots of `omegaG`. -/
theorem omegaG_arg_of_upper {y : ℂ} {a b : ℝ} (hy : 0 < y.im) (h : y + log y = ⟨a, b⟩) :
    arg y ∈ omegaDom b ∧ omegaG b (arg y) = a := by
  have hα := arg_mem_Ioo_of_im_pos hy
  have hs : 0 < Real.sin (arg y) := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr fun h => by rw [h] at hy; simp at hy
  have him := congrArg im h
  have hre := congrArg re h
  rw [add_log_im, ← norm_mul_sin_arg] at him
  rw [add_log_re, ← norm_mul_cos_arg] at hre
  simp only at him hre
  have hb : arg y < b := by nlinarith
  refine ⟨⟨hα.1, lt_min hb hα.2⟩, ?_⟩
  have hρ : ‖y‖ = (b - arg y) / Real.sin (arg y) := by rw [eq_div_iff hs.ne']; linarith
  rw [omegaG, ← hre, hρ, Real.log_div (by linarith) hs.ne']
  ring

/-- The upper half-plane point with argument `α` and modulus `(b − α)/sin α`. -/
noncomputable def omegaPt (b α : ℝ) : ℂ :=
  (((b - α) / Real.sin α : ℝ) : ℂ) * (Real.cos α + Real.sin α * I)

theorem omegaPt_props {a b α : ℝ} (hα : α ∈ omegaDom b) (hG : omegaG b α = a) :
    0 < (omegaPt b α).im ∧ omegaPt b α + log (omegaPt b α) = ⟨a, b⟩ ∧ arg (omegaPt b α) = α := by
  obtain ⟨h0, hb, hπ⟩ := mem_omegaDom hα
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hρ : 0 < (b - α) / Real.sin α := div_pos (by linarith) hs
  have harg : arg (omegaPt b α) = α := by
    rw [omegaPt, arg_real_mul _ hρ]
    exact_mod_cast arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hπ.le⟩
  have hnorm : ‖omegaPt b α‖ = (b - α) / Real.sin α := by
    rw [omegaPt, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    have : ‖(Real.cos α : ℂ) + Real.sin α * I‖ = 1 := by
      rw [ofReal_cos, ofReal_sin]
      exact norm_cos_add_sin_mul_I α
    rw [this, mul_one]
  have him : (omegaPt b α).im = b - α := by
    simp only [omegaPt, mul_im, ofReal_re, ofReal_im, add_im, ofReal_im, mul_im, I_re, I_im,
      add_re, mul_re, ofReal_re]
    field_simp
    ring
  refine ⟨by rw [him]; linarith, ?_, harg⟩
  apply Complex.ext
  · rw [add_log_re, hnorm, ← hG, omegaG, Real.log_div (by linarith) hs.ne']
    simp only [omegaPt, mul_re, ofReal_re, ofReal_im, add_re, mul_re, I_re, I_im, add_im, mul_im]
    field_simp
    ring
  · rw [add_log_im, harg, him]; simp

/-- The core: for `b > 0` (and `a > −1` if `b = π`) there is exactly one solution in the upper
half-plane. -/
theorem existsUnique_upper {a b : ℝ} (hb : 0 < b) (h : b ≠ π ∨ -1 < a) :
    ∃! y : ℂ, 0 < y.im ∧ y + log y = ⟨a, b⟩ := by
  obtain ⟨α, hα, hG⟩ := exists_omegaG_eq hb h
  obtain ⟨h1, h2, _⟩ := omegaPt_props hα hG
  refine ⟨omegaPt b α, ⟨h1, h2⟩, fun y ⟨hy, hyeq⟩ => ?_⟩
  obtain ⟨hα', hG'⟩ := omegaG_arg_of_upper hy hyeq
  have hαα : arg y = α := (strictAntiOn_omegaG b).injOn hα' hα (hG'.trans hG.symm)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr fun h => by rw [h] at hy; simp at hy
  obtain ⟨_, _, hπ⟩ := mem_omegaDom hα
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hπ
  -- both points have argument `α` and modulus `(b − α)/sin α`
  have him := congrArg im hyeq
  rw [add_log_im, ← norm_mul_sin_arg, hαα] at him
  simp only at him
  have hρ : ‖y‖ = (b - α) / Real.sin α := by rw [eq_div_iff hs.ne']; linarith
  have hy' : y = ((‖y‖ : ℝ) : ℂ) * (Real.cos (arg y) + Real.sin (arg y) * I) := by
    apply Complex.ext <;> simp
  rw [hy', hαα, hρ]; rfl

/-- For `b = π` and `a ≤ −1` there is no upper half-plane solution. -/
theorem not_exists_upper_pi {a : ℝ} (ha : a ≤ -1) : ¬∃ y : ℂ, 0 < y.im ∧ y + log y = ⟨a, π⟩ := by
  rintro ⟨y, hy, h⟩
  obtain ⟨hα, hG⟩ := omegaG_arg_of_upper hy h
  have := omegaG_pi_gt hα
  linarith

/-! ### Classification of the solutions -/

theorem add_log_im_pos {y : ℂ} (hy : 0 < y.im) : 0 < (y + log y).im := by
  rw [add_log_im]; linarith [(arg_mem_Ioo_of_im_pos hy).1]

theorem add_log_im_neg {y : ℂ} (hy : y.im < 0) : (y + log y).im < 0 := by
  rw [add_log_im]; linarith [(arg_mem_Ioo_of_im_neg hy).2]

theorem add_log_of_pos_real {x : ℝ} (hx : 0 < x) :
    (x : ℂ) + Complex.log (x : ℂ) = ((x + Real.log x : ℝ) : ℂ) := by
  rw [← ofReal_log hx.le]; push_cast; ring

theorem add_log_of_neg_real {x : ℝ} (hx : x < 0) :
    (x : ℂ) + Complex.log (x : ℂ) = ⟨x + Real.log (-x), π⟩ := by
  apply Complex.ext
  · rw [add_log_re]; simp [abs_of_neg hx]
  · rw [add_log_im, arg_ofReal_of_neg hx]; simp

/-- The specification of `ω(ζ)` off `L₋`: `y ≠ 0`, `y + ln y = ζ`, and on `L₊` the real root
`≥ −1`. -/
def OmegaSpec (ζ y : ℂ) : Prop :=
  y ≠ 0 ∧ y + log y = ζ ∧ (ζ.im = π → y.im = 0 → -1 ≤ y.re)

/-- The lower half-line `L₋ = {t − iπ : t ≤ −1}`. -/
def omegaLm (ζ : ℂ) : Prop := ζ.im = -π ∧ ζ.re ≤ -1

/-- The upper half-line `L₊ = {t + iπ : t ≤ −1}`. -/
def omegaLp (ζ : ℂ) : Prop := ζ.im = π ∧ ζ.re ≤ -1

theorem conj_add_log {y : ℂ} (hy : y.im ≠ 0) : conj y + log (conj y) = conj (y + log y) := by
  have hne : arg y ≠ π := fun h => hy (arg_eq_pi_iff.mp h).2
  rw [log_conj y hne, map_add]

/-- **Existence and uniqueness** of `ω(ζ)` for `ζ ∉ L₋`. -/
theorem existsUnique_omega {ζ : ℂ} (hζ : ¬omegaLm ζ) : ∃! y, OmegaSpec ζ y := by
  obtain ⟨a, b⟩ := ζ
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · -- lower half-plane: conjugate
    have hb' : (-b) ≠ π ∨ -1 < a := by
      by_contra h; push Not at h
      exact hζ ⟨by simp only; linarith [h.1], by simpa using h.2⟩
    obtain ⟨y, ⟨hy, hyeq⟩, hu⟩ := existsUnique_upper (a := a) (b := -b) (by linarith) hb'
    have hy' : (conj y).im < 0 := by simpa using hy
    have hc : conj y + log (conj y) = ⟨a, b⟩ := by
      rw [conj_add_log hy.ne', hyeq]; apply Complex.ext <;> simp
    refine ⟨conj y, ⟨fun h => by rw [h] at hy'; simp at hy', hc, fun h => by
      simp only at h; linarith [Real.pi_pos]⟩, fun z ⟨hz0, hz, _⟩ => ?_⟩
    -- every solution lies in the lower half-plane
    have hzim : z.im < 0 := by
      rcases lt_trichotomy z.im 0 with h | h | h
      · exact h
      · exfalso
        have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
        rcases lt_or_gt_of_ne (fun h' : z.re = 0 => hz0 (by rw [hz', h']; simp)) with hr | hr
        · have := congrArg im hz; rw [hz', add_log_of_neg_real hr] at this
          simp only at this; linarith [Real.pi_pos]
        · have := congrArg im hz; rw [hz', add_log_of_pos_real hr] at this
          simp at this; linarith
      · have := add_log_im_pos h; rw [hz] at this; simp only at this; linarith
    have := hu (conj z) ⟨by simpa using hzim, by
      rw [conj_add_log hzim.ne, hz]; apply Complex.ext <;> simp⟩
    rw [← this, conj_conj]
  · -- real axis: the positive real root
    refine ⟨(wrightOmegaReal a : ℂ), ⟨by exact_mod_cast (wrightOmegaReal_pos a).ne', ?_, ?_⟩,
      fun z ⟨hz0, hz, _⟩ => ?_⟩
    · rw [add_log_of_pos_real (wrightOmegaReal_pos a), dlmf_4_13_1_2_real]; rfl
    · intro h; simp only at h; linarith [Real.pi_pos]
    · rcases lt_trichotomy z.im 0 with h | h | h
      · have := add_log_im_neg h; rw [hz] at this; simp at this
      · have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
        rcases lt_or_gt_of_ne (fun h' : z.re = 0 => hz0 (by rw [hz', h']; simp)) with hr | hr
        · have := congrArg im hz; rw [hz', add_log_of_neg_real hr] at this
          simp only at this; linarith [Real.pi_pos]
        · have hre := congrArg re hz
          rw [hz', add_log_of_pos_real hr] at hre
          simp only [ofReal_re] at hre
          have hmono : StrictMonoOn (fun x : ℝ => x + Real.log x) (Ioi 0) := fun u hu v hv huv => by
            simp only; linarith [Real.log_lt_log hu huv]
          have heq := hmono.injOn hr (wrightOmegaReal_pos a)
            (by
              show z.re + Real.log z.re = wrightOmegaReal a + Real.log (wrightOmegaReal a)
              rw [dlmf_4_13_1_2_real]; simpa using hre)
          rw [hz', heq]
      · have := add_log_im_pos h; rw [hz] at this; simp at this
  · rcases eq_or_ne b π with rfl | hbπ
    · rcases lt_or_ge (-1) a with ha | ha
      · -- `L₊`-line above the branch point: the upper root
        obtain ⟨y, ⟨hy, hyeq⟩, hu⟩ := existsUnique_upper (a := a) Real.pi_pos (Or.inr ha)
        refine ⟨y, ⟨fun h => by rw [h] at hy; simp at hy, hyeq, fun _ h => by linarith⟩,
          fun z ⟨hz0, hz, _⟩ => ?_⟩
        rcases lt_trichotomy z.im 0 with h | h | h
        · have := add_log_im_neg h; rw [hz] at this; simp only at this; linarith [Real.pi_pos]
        · exfalso
          have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
          rcases lt_or_gt_of_ne (fun h' : z.re = 0 => hz0 (by rw [hz', h']; simp)) with hr | hr
          · have hre := congrArg re hz
            rw [hz', add_log_of_neg_real hr] at hre
            simp only at hre
            have := Real.log_le_sub_one_of_pos (by linarith : 0 < -z.re)
            linarith
          · have := congrArg im hz; rw [hz', add_log_of_pos_real hr] at this
            simp at this; linarith [Real.pi_pos]
        · exact hu z ⟨h, hz⟩
      · -- `L₊` itself: the real root `≥ −1`
        have hea : -Real.exp (-1) ≤ -Real.exp a := by
          have := Real.exp_le_exp.mpr ha; linarith
        obtain ⟨h1, h2⟩ := lambertW0_spec hea
        set w := lambertW0 (-Real.exp a)
        have hw0 : w < 0 := by
          by_contra h; push Not at h
          have : 0 ≤ w * Real.exp w := mul_nonneg h (Real.exp_pos _).le
          linarith [Real.exp_pos a]
        have hwa : w + Real.log (-w) = a := by
          have : -w * Real.exp w = Real.exp a := by linarith
          have := congrArg Real.log this
          rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
          linarith
        refine ⟨(w : ℂ), ⟨by exact_mod_cast hw0.ne, by rw [add_log_of_neg_real hw0, hwa],
          fun _ _ => by simpa using h1⟩, fun z ⟨hz0, hz, hz1⟩ => ?_⟩
        rcases lt_trichotomy z.im 0 with h | h | h
        · have := add_log_im_neg h; rw [hz] at this; simp only at this; linarith [Real.pi_pos]
        · have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
          have hr : z.re < 0 := by
            rcases lt_or_gt_of_ne (fun h' : z.re = 0 => hz0 (by rw [hz', h']; simp)) with hr | hr
            · exact hr
            · have := congrArg im hz; rw [hz', add_log_of_pos_real hr] at this
              simp at this; linarith [Real.pi_pos]
          have hre := congrArg re hz
          rw [hz', add_log_of_neg_real hr] at hre
          simp only at hre
          have hge : -1 ≤ z.re := hz1 rfl h
          have : z.re * Real.exp z.re = -Real.exp a := by
            have e := congrArg Real.exp hre
            rw [Real.exp_add, Real.exp_log (by linarith)] at e
            linarith
          have := dlmf_4_13_3_1 hge
          rw [‹z.re * Real.exp z.re = -Real.exp a›] at this
          rw [hz', ← this]
        · exact absurd ⟨h, hz⟩ (not_exists_upper_pi ha ∘ fun h' => ⟨z, h'⟩)
    · -- `b > 0`, `b ≠ π`: the upper root
      obtain ⟨y, ⟨hy, hyeq⟩, hu⟩ := existsUnique_upper (a := a) hb (Or.inl hbπ)
      refine ⟨y, ⟨fun h => by rw [h] at hy; simp at hy, hyeq, fun h => absurd h hbπ⟩,
        fun z ⟨hz0, hz, _⟩ => ?_⟩
      rcases lt_trichotomy z.im 0 with h | h | h
      · have := add_log_im_neg h; rw [hz] at this; simp only at this; linarith
      · exfalso
        have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
        rcases lt_or_gt_of_ne (fun h' : z.re = 0 => hz0 (by rw [hz', h']; simp)) with hr | hr
        · have := congrArg im hz; rw [hz', add_log_of_neg_real hr] at this
          simp only at this; exact hbπ this.symm
        · have := congrArg im hz; rw [hz', add_log_of_pos_real hr] at this
          simp at this; linarith
      · exact hu z ⟨h, hz⟩

/-! ### The Wright `ω`-function -/

open Classical in
/-- **DLMF 4.13.1_2**: the Wright `ω`-function `ω(z) = W(e^z)`: the solution of `ω + ln ω = z`
(off `L₋`; on `L₊` the root `≥ −1`), and `W_{−1}(−e^t)` on `L₋ = {t − iπ : t ≤ −1}`. -/
noncomputable def wrightOmega (ζ : ℂ) : ℂ :=
  if h : omegaLm ζ then ((lambertWm1 (-Real.exp ζ.re) : ℝ) : ℂ)
  else (existsUnique_omega h).exists.choose

theorem wrightOmega_spec {ζ : ℂ} (h : ¬omegaLm ζ) : OmegaSpec ζ (wrightOmega ζ) := by
  simp only [wrightOmega, h, ↓reduceDIte]; exact (existsUnique_omega h).exists.choose_spec

theorem wrightOmega_eq {ζ y : ℂ} (h : ¬omegaLm ζ) (hy : OmegaSpec ζ y) : wrightOmega ζ = y :=
  (existsUnique_omega h).unique (wrightOmega_spec h) hy

theorem wrightOmega_of_Lm {ζ : ℂ} (h : omegaLm ζ) :
    wrightOmega ζ = ((lambertWm1 (-Real.exp ζ.re) : ℝ) : ℂ) := by
  simp only [wrightOmega, h, ↓reduceDIte]

/-- **DLMF 4.13.1_2**: `ω(z) + ln ω(z) = z` for `z ∉ L₋`. -/
theorem dlmf_4_13_1_2 {ζ : ℂ} (h : ¬omegaLm ζ) : wrightOmega ζ + log (wrightOmega ζ) = ζ :=
  (wrightOmega_spec h).2.1

theorem lambertWm1_props {t : ℝ} (ht : t ≤ -1) :
    lambertWm1 (-Real.exp t) < 0 ∧ lambertWm1 (-Real.exp t) + Real.log (-lambertWm1 (-Real.exp t))
      = t := by
  have hea : -Real.exp (-1) ≤ -Real.exp t := by have := Real.exp_le_exp.mpr ht; linarith
  obtain ⟨h1, h2⟩ := lambertWm1_spec hea (by linarith [Real.exp_pos t])
  set w := lambertWm1 (-Real.exp t)
  have hw : w < 0 := by linarith
  refine ⟨hw, ?_⟩
  have : -w * Real.exp w = Real.exp t := by linarith
  have := congrArg Real.log this
  rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at this
  linarith

/-- **Erratum to DLMF 4.13.1_2**: on `L₋ = {t − iπ : t ≤ −1}` (where `ω(z) = W_{−1}(−e^t)`),
`ω(z) + ln ω(z) = z + 2πi ≠ z`; indeed `y + ln y = z` has no solution there. -/
theorem wrightOmega_add_log_of_Lm {ζ : ℂ} (h : omegaLm ζ) :
    wrightOmega ζ + log (wrightOmega ζ) = ζ + 2 * π * I ∧
      ¬∃ y : ℂ, y ≠ 0 ∧ y + log y = ζ := by
  obtain ⟨hw, hwt⟩ := lambertWm1_props h.2
  refine ⟨?_, ?_⟩
  · rw [wrightOmega_of_Lm h, add_log_of_neg_real hw, hwt]
    apply Complex.ext <;> simp [h.1]; ring
  · rintro ⟨y, hy0, hy⟩
    rcases lt_trichotomy y.im 0 with hi | hi | hi
    · -- `Im(y + ln y) = Im y + arg y ∈ (−2π, 0)`; equal to `−π` forces `y` to the right of the
      -- boundary curve, which does not meet `Re ≤ −1` at height `−π`: use the conjugate
      have hc : conj y + log (conj y) = ⟨ζ.re, π⟩ := by
        rw [conj_add_log hi.ne, hy]; apply Complex.ext <;> simp [h.1]
      exact not_exists_upper_pi h.2 ⟨conj y, by simpa using hi, hc⟩
    · have hy' : y = (y.re : ℂ) := Complex.ext rfl (by simp [hi])
      rcases lt_or_gt_of_ne (fun h' : y.re = 0 => hy0 (by rw [hy', h']; simp)) with hr | hr
      · have := congrArg im hy; rw [hy', add_log_of_neg_real hr, h.1] at this
        simp only at this; linarith [Real.pi_pos]
      · have := congrArg im hy; rw [hy', add_log_of_pos_real hr, h.1] at this
        simp at this
    · have := add_log_im_pos hi; rw [hy, h.1] at this; linarith [Real.pi_pos]

/-- `ω(z) e^{ω(z)} = e^z` for every `z` (`ω(z)` is a value of `W(e^z)`). -/
theorem wrightOmega_mul_exp (ζ : ℂ) : wrightOmega ζ * exp (wrightOmega ζ) = exp ζ := by
  by_cases h : omegaLm ζ
  · have h1 := (wrightOmega_add_log_of_Lm h).1
    have hne : wrightOmega ζ ≠ 0 := by
      rw [wrightOmega_of_Lm h]; exact_mod_cast (lambertWm1_props h.2).1.ne
    have := congrArg exp h1
    rw [exp_add, exp_log hne, exp_add, exp_two_pi_mul_I, mul_one] at this
    rw [mul_comm]; exact this
  · obtain ⟨hne, h1, _⟩ := wrightOmega_spec h
    have := congrArg exp h1
    rw [exp_add, exp_log hne] at this
    rw [mul_comm]; exact this

/-- On the real line `ω` is the real Wright function `W₀(eˣ)`. -/
theorem wrightOmega_ofReal (x : ℝ) : wrightOmega x = wrightOmegaReal x := by
  have hn : ¬omegaLm (x : ℂ) := fun h => by
    have h1 := h.1; rw [ofReal_im] at h1; linarith [Real.pi_pos]
  refine wrightOmega_eq hn ⟨by exact_mod_cast (wrightOmegaReal_pos x).ne', ?_, fun h => by
    rw [ofReal_im] at h; linarith [Real.pi_pos]⟩
  rw [add_log_of_pos_real (wrightOmegaReal_pos x), dlmf_4_13_1_2_real]

/-! ### Analyticity -/

theorem isClosed_omegaL : IsClosed {ζ : ℂ | omegaLm ζ ∨ omegaLp ζ} := by
  have h1 : IsClosed {ζ : ℂ | omegaLm ζ} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_re continuous_const)
  have h2 : IsClosed {ζ : ℂ | omegaLp ζ} :=
    (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_re continuous_const)
  exact h1.union h2

theorem wrightOmega_mem_slitPlane {ζ : ℂ} (h : ¬omegaLm ζ) (h' : ¬omegaLp ζ) :
    wrightOmega ζ ∈ slitPlane := by
  obtain ⟨hne, heq, _⟩ := wrightOmega_spec h
  rw [mem_slitPlane_iff]
  by_contra hc; push Not at hc
  set y := wrightOmega ζ
  have hy' : y = (y.re : ℂ) := Complex.ext rfl (by simp [hc.2])
  have hr : y.re < 0 := lt_of_le_of_ne hc.1 fun h0 => hne (by rw [hy', h0]; simp)
  rw [hy', add_log_of_neg_real hr] at heq
  apply h'
  rw [← heq]
  refine ⟨rfl, ?_⟩
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < -y.re)
  simp only; linarith

/-- **DLMF §4.13**: `ω` is analytic off `L₊ ∪ L₋`, with `ω′ = ω/(1 + ω)`. -/
theorem hasDerivAt_wrightOmega {ζ : ℂ} (h : ¬omegaLm ζ) (h' : ¬omegaLp ζ) :
    HasDerivAt wrightOmega (wrightOmega ζ / (1 + wrightOmega ζ)) ζ := by
  set y₀ := wrightOmega ζ with hy₀
  have hs := wrightOmega_mem_slitPlane h h'
  obtain ⟨hne, heq, _⟩ := wrightOmega_spec h
  rw [← hy₀] at hne heq hs
  have hm1 : y₀ ≠ -1 := fun e => by
    have : (y₀ + log y₀) = ⟨-1, π⟩ := by
      rw [e]; have := add_log_of_neg_real (x := -1) (by norm_num); push_cast at this
      rw [this]; simp
    exact h' (by rw [← heq, this]; exact ⟨rfl, le_rfl⟩)
  have hf : HasStrictDerivAt (fun y => y + log y) (1 + y₀⁻¹) y₀ :=
    (hasStrictDerivAt_id y₀).add (hasStrictDerivAt_log hs)
  have hf' : (1 : ℂ) + y₀⁻¹ ≠ 0 := fun e => hm1 (by
    have : y₀⁻¹ = -1 := by linear_combination e
    rw [← inv_inv y₀, this]; norm_num)
  set g := hf.localInverse _ _ _ hf'
  have hg := hf.to_localInverse hf'
  have hright := hf.eventually_right_inverse hf'
  rw [heq] at hg hright
  have hg0 : g ζ = y₀ := by
    have := (hf.eventually_left_inverse hf').self_of_nhds
    rw [heq] at this; exact this
  have hcont : Tendsto g (𝓝 ζ) (𝓝 y₀) := by
    have h2 : Tendsto g (𝓝 ζ) (𝓝 (g ζ)) := hg.hasDerivAt.continuousAt.tendsto
    rwa [hg0] at h2
  have hev : wrightOmega =ᶠ[𝓝 ζ] g := by
    filter_upwards [hright, hcont.eventually (isOpen_slitPlane.mem_nhds hs),
      isClosed_omegaL.isOpen_compl.mem_nhds (by simp [h, h'])] with w hw1 hw2 hw3
    simp only [mem_compl_iff, mem_ofPred_eq, not_or] at hw3
    refine wrightOmega_eq hw3.1 ⟨slitPlane_ne_zero hw2, hw1, fun _ him => ?_⟩
    rcases mem_slitPlane_iff.mp hw2 with hre | him'
    · linarith
    · exact absurd him him'
  refine (hg.hasDerivAt.congr_of_eventuallyEq hev).congr_deriv ?_
  have h1 : y₀ + 1 ≠ 0 := fun e => hm1 (by linear_combination e)
  rw [add_comm (1 : ℂ) y₀]
  field_simp

end Azurite.DLMF
