/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertGreen

/-!
# DLMF 1.14.45: a smooth subharmonic regularization of `Re((|a| + ib)^p)`

`Ψ_δ(w) = Re((√(a² + δ²) + ib)^p) − δ^p` (`psiD`) is `C^∞`, vanishes to second order at `0`
(`psiD_zero`, `fderiv_psiD_zero`, by evenness), and is subharmonic for `1 < p ≤ 2`
(`psiD_subharmonic`). The second derivatives are computed along lines
(`fderiv2_apply_eq_of_line`, `fderiv2_psiD`). Their sum is
`|v|² δ²/A³ · p (Re ζ^{p−1} − (p − 1) Re ζ · Re ζ^{p−2})`, which is nonnegative by
`(p − 1) cos θ cos((p − 2)θ) ≤ cos((p − 1)θ)` (`re_cpow_key`). Also `|Ψ_δ(w)| ≤ C|w|^p`
uniformly in `δ`, by scaling (`exists_psiD_bound`), and `Ψ_δ → Re((|a| + ib)^p)`
(`tendsto_psiD`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-- `σ_δ(a + ib) = √(a² + δ²) + ib`, in the open right half-plane for `δ > 0`. -/
noncomputable def sigmaD (δ : ℝ) (w : ℂ) : ℂ := (√(w.re ^ 2 + δ ^ 2) : ℂ) + w.im * I

/-- `Ψ_δ(w) = Re(σ_δ(w)^p) − δ^p`. -/
noncomputable def psiD (p δ : ℝ) (w : ℂ) : ℝ := (sigmaD δ w ^ (p : ℂ)).re - δ ^ p

theorem sigmaD_re {δ : ℝ} (w : ℂ) : (sigmaD δ w).re = √(w.re ^ 2 + δ ^ 2) := by
  simp [sigmaD]

theorem sigmaD_im {δ : ℝ} (w : ℂ) : (sigmaD δ w).im = w.im := by simp [sigmaD]

theorem sigmaD_re_pos {δ : ℝ} (hδ : 0 < δ) (w : ℂ) : 0 < (sigmaD δ w).re := by
  rw [sigmaD_re]; exact Real.sqrt_pos.mpr (by positivity)

theorem sigmaD_mem_slitPlane {δ : ℝ} (hδ : 0 < δ) (w : ℂ) : sigmaD δ w ∈ slitPlane :=
  Or.inl (sigmaD_re_pos hδ w)

theorem contDiff_sigmaD {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ⊤ (sigmaD δ) := by
  have h1 : ContDiff ℝ ⊤ fun w : ℂ => √(w.re ^ 2 + δ ^ 2) :=
    ((reCLM.contDiff.pow 2).add contDiff_const).sqrt fun w => by positivity
  exact (ofRealCLM.contDiff.comp h1).add ((ofRealCLM.contDiff.comp imCLM.contDiff).mul
    contDiff_const)

theorem contDiff_psiD (p : ℝ) {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ⊤ (psiD p δ) := by
  have hpow : ContDiffOn ℝ ⊤ (fun z : ℂ => z ^ (p : ℂ)) slitPlane :=
    ((DifferentiableOn.cpow_const differentiableOn_id fun z hz => hz).contDiffOn
      isOpen_slitPlane).restrict_scalars ℝ
  exact (reCLM.contDiff.comp (hpow.comp_contDiff (contDiff_sigmaD hδ)
    (sigmaD_mem_slitPlane hδ))).sub contDiff_const

theorem sigmaD_zero {δ : ℝ} (hδ : 0 < δ) : sigmaD δ 0 = δ := by
  simp [sigmaD, Real.sqrt_sq hδ.le]

theorem psiD_zero (p : ℝ) {δ : ℝ} (hδ : 0 < δ) : psiD p δ 0 = 0 := by
  rw [psiD, sigmaD_zero hδ, ← ofReal_cpow hδ.le, ofReal_re, sub_self]

/-! ### Second derivatives along lines -/

/-- If `t ↦ Ψ(w + tv)` has derivative `g₁(t)` everywhere and `g₁′(0) = d`, then
`D²Ψ(w)(v, v) = d`. -/
theorem fderiv2_apply_eq_of_line {Ψ : ℂ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) {w v : ℂ} {g₁ : ℝ → ℝ}
    {d : ℝ} (h1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Ψ (w + s • v)) (g₁ t) t)
    (h2 : HasDerivAt g₁ d 0) : fderiv ℝ (fderiv ℝ Ψ) w v v = d := by
  have hℓ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add w
  have hD1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (m := 1) (by norm_num)
  have hg : g₁ = fun t => fderiv ℝ Ψ (w + t • v) v := funext fun t =>
    (h1 t).unique (((hΨ.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t (hℓ t))
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ Ψ (w + t • v))
      (fderiv ℝ (fderiv ℝ Ψ) (w + (0 : ℝ) • v) v) 0 :=
    ((hD1.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt 0 (hℓ 0)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simp only [zero_smul, add_zero, map_zero] at h4
  rw [hg] at h2
  exact (h2.unique h4).symm

/-- The second derivative of `Ψ_δ` along `v` at `w`: with `A = √(a² + δ²)`, `ζ = σ_δ(w)`,
`ζ₁ = a v₁/A + i v₂` and `A₂ = v₁² δ²/A³`,
`D²Ψ_δ(w)(v, v) = Re(p((p − 1) ζ^{p−2} ζ₁² + ζ^{p−1} A₂))`. -/
theorem fderiv2_psiD (p : ℝ) {δ : ℝ} (hδ : 0 < δ) (w v : ℂ) :
    fderiv ℝ (fderiv ℝ (psiD p δ)) w v v =
      ((p : ℂ) * (((p : ℂ) - 1) * sigmaD δ w ^ ((p : ℂ) - 1 - 1) *
        (((w.re * v.re / √(w.re ^ 2 + δ ^ 2) : ℝ) : ℂ) + v.im * I) ^ 2 +
        sigmaD δ w ^ ((p : ℂ) - 1) *
          ((v.re ^ 2 * δ ^ 2 / √(w.re ^ 2 + δ ^ 2) ^ 3 : ℝ) : ℂ))).re := by
  set a := w.re
  set b := w.im
  set v₁ := v.re
  set v₂ := v.im
  set A : ℝ → ℝ := fun s => √((a + s * v₁) ^ 2 + δ ^ 2) with hA
  set A1 : ℝ → ℝ := fun s => (a + s * v₁) * v₁ / A s with hA1
  set A2 : ℝ → ℝ := fun s => v₁ ^ 2 * δ ^ 2 / A s ^ 3 with hA2
  set ζ : ℝ → ℂ := fun s => (A s : ℂ) + (b + s * v₂) * I with hζ
  set ζ1 : ℝ → ℂ := fun s => (A1 s : ℂ) + v₂ * I with hζ1
  have hinner : ∀ s, 0 < (a + s * v₁) ^ 2 + δ ^ 2 := fun s => by
    have := sq_nonneg (a + s * v₁); have := pow_pos hδ 2; linarith
  have hApos : ∀ s, 0 < A s := fun s => Real.sqrt_pos.mpr (hinner s)
  have hAsq : ∀ s, A s ^ 2 = (a + s * v₁) ^ 2 + δ ^ 2 := fun s =>
    Real.sq_sqrt (hinner s).le
  have hline : ∀ s : ℝ, sigmaD δ (w + s • v) = ζ s := fun s => by
    apply Complex.ext <;> simp [sigmaD, hζ, hA, a, b, v₁, v₂]
  have hlin : ∀ s, HasDerivAt (fun s : ℝ => a + s * v₁) v₁ s := fun s => by
    simpa using ((hasDerivAt_id s).mul_const v₁).const_add a
  have hdA : ∀ s, HasDerivAt A (A1 s) s := fun s => by
    have h : HasDerivAt (fun s => (a + s * v₁) ^ 2 + δ ^ 2) (2 * (a + s * v₁) * v₁) s :=
      (((hlin s).mul (hlin s)).add_const (δ ^ 2)).congr_of_eventuallyEq
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring) |>.congr_deriv (by ring)
    refine (h.sqrt (hinner s).ne').congr_deriv ?_
    simp only [hA1, hA]
    have h0 := (hApos s).ne'
    field_simp
  have hdA1 : ∀ s, HasDerivAt A1 (A2 s) s := fun s => by
    have h1 : HasDerivAt (fun s => (a + s * v₁) * v₁) (v₁ * v₁) s := (hlin s).mul_const v₁
    refine (h1.div (hdA s) (hApos s).ne').congr_deriv ?_
    simp only [hA1, hA2]
    have := hAsq s
    have h0 := (hApos s).ne'
    field_simp
    rw [this]
    ring
  have hdζ : ∀ s, HasDerivAt ζ (ζ1 s) s := fun s => by
    have h1 := (hdA s).ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => ((b : ℂ) + s * v₂) * I) (v₂ * I) s := by
      have := ((((hasDerivAt_id s).mul_const v₂).const_add b).ofReal_comp).mul_const I
      simpa using this
    exact h1.add h2
  have hdζ1 : ∀ s, HasDerivAt ζ1 (A2 s) s := fun s => by
    simpa [hζ1] using (hdA1 s).ofReal_comp.add_const ((v₂ : ℂ) * I)
  have hslit : ∀ s, ζ s ∈ slitPlane := fun s => by
    rw [← hline]; exact sigmaD_mem_slitPlane hδ _
  -- first derivative
  set g₁ : ℝ → ℝ := fun s => ((p : ℂ) * ζ s ^ ((p : ℂ) - 1) * ζ1 s).re with hg₁
  have h1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => psiD p δ (w + s • v)) (g₁ t) t := fun t => by
    have hc := (Complex.hasStrictDerivAt_cpow_const (c := (p : ℂ)) (hslit t)).hasDerivAt.comp t
      (hdζ t)
    have hre := (reCLM.hasFDerivAt.comp_hasDerivAt t hc).sub_const (δ ^ p)
    refine hre.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_) |>.congr_deriv rfl
    simp only [psiD, hline, Function.comp_apply, reCLM_apply]
  -- second derivative
  have h2 : HasDerivAt g₁ ((p : ℂ) * (((p : ℂ) - 1) * ζ 0 ^ ((p : ℂ) - 1 - 1) * ζ1 0 * ζ1 0 +
      ζ 0 ^ ((p : ℂ) - 1) * A2 0)).re 0 := by
    have hc := (Complex.hasStrictDerivAt_cpow_const (c := (p : ℂ) - 1) (hslit 0)).hasDerivAt.comp
      0 (hdζ 0)
    have hprod := (hc.mul (hdζ1 0)).const_mul (p : ℂ)
    have hre := reCLM.hasFDerivAt.comp_hasDerivAt 0 hprod
    refine hre.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_) |>.congr_deriv ?_
    · simp only [hg₁, Function.comp_apply, reCLM_apply, mul_assoc, Pi.mul_apply]
    · simp only [reCLM_apply]
      congr 1
  rw [fderiv2_apply_eq_of_line ((contDiff_psiD p hδ).of_le le_top) h1 h2]
  have hz0 : ζ 0 = sigmaD δ w := by rw [← hline 0]; simp
  have hz10 : ζ1 0 = ((a * v₁ / √(a ^ 2 + δ ^ 2) : ℝ) : ℂ) + v₂ * I := by simp [hζ1, hA1, hA]
  have hA20 : A2 0 = v₁ ^ 2 * δ ^ 2 / √(a ^ 2 + δ ^ 2) ^ 3 := by simp [hA2, hA]
  rw [hz0, hz10, hA20]
  congr 2
  ring

/-! ### Subharmonicity -/

/-- `(p − 1) cos θ cos((p − 2)θ) ≤ cos((p − 1)θ)` for `1 < p ≤ 2`, `|θ| ≤ π/2`. -/
theorem cos_mul_cos_le {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {θ : ℝ} (hθ : |θ| ≤ π / 2) :
    (p - 1) * Real.cos θ * Real.cos ((p - 2) * θ) ≤ Real.cos ((p - 1) * θ) := by
  have hπ := Real.pi_pos
  have h2 : 2 * (Real.cos θ * Real.cos ((p - 2) * θ)) =
      Real.cos ((p - 1) * θ) + Real.cos ((3 - p) * θ) := by
    have e1 : (p - 1) * θ = (p - 2) * θ + θ := by ring
    have e2 : (3 - p) * θ = -((p - 2) * θ - θ) := by ring
    rw [e1, e2, Real.cos_neg, Real.cos_add, Real.cos_sub]; ring
  have hev : ∀ c : ℝ, Real.cos (c * θ) = Real.cos (c * |θ|) := fun c => by
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, mul_neg, Real.cos_neg]
  set t := |θ| with ht
  have ht0 : 0 ≤ t := abs_nonneg θ
  have hc1 : 0 ≤ Real.cos ((p - 1) * t) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hc2 : Real.cos ((3 - p) * t) ≤ Real.cos ((p - 1) * t) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) (by nlinarith)
  have hc1' : 0 ≤ Real.cos ((p - 1) * θ) := by rw [hev]; exact hc1
  have hc2' : Real.cos ((3 - p) * θ) ≤ Real.cos ((p - 1) * θ) := by
    rw [hev, hev (p - 1)]; exact hc2
  have hX : Real.cos θ * Real.cos ((p - 2) * θ) =
      (Real.cos ((p - 1) * θ) + Real.cos ((3 - p) * θ)) / 2 := by linarith
  rw [mul_assoc, hX]
  nlinarith [mul_le_mul_of_nonneg_left hc2' (by linarith : (0 : ℝ) ≤ p - 1),
    mul_le_mul_of_nonneg_right (by linarith : p - 1 ≤ 3 - p) hc1']

/-- `(p − 1) Re ζ · Re ζ^{p−2} ≤ Re ζ^{p−1}` on the right half-plane, `1 < p ≤ 2`. -/
theorem re_cpow_key {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {ζ : ℂ} (hζ : 0 < ζ.re) :
    (p - 1) * ζ.re * (ζ ^ ((p : ℂ) - 1 - 1)).re ≤ (ζ ^ ((p : ℂ) - 1)).re := by
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, zero_re] at hζ; exact lt_irrefl 0 hζ
  have e1 : (p : ℂ) - 1 - 1 = ((p - 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (p : ℂ) - 1 = ((p - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, re_cpow_ofReal ζ hζ0, re_cpow_ofReal ζ hζ0, ← norm_mul_cos_arg ζ]
  set ρ := ‖ζ‖
  set θ := arg ζ
  have hρ : 0 < ρ := norm_pos_iff.mpr hζ0
  have hθ : |θ| ≤ π / 2 := abs_arg_le_pi_div_two_iff.mpr hζ.le
  have hpow : ρ ^ (p - 1) = ρ * ρ ^ (p - 2) := by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hρ.ne', mul_comm]
  rw [hpow]
  have := cos_mul_cos_le hp1 hp2 hθ
  have hpos : 0 < ρ * ρ ^ (p - 2) := mul_pos hρ (Real.rpow_pos_of_pos hρ _)
  nlinarith [mul_le_mul_of_nonneg_left this hpos.le]

/-- `Ψ_δ` is subharmonic for `1 < p ≤ 2`: `D²Ψ_δ(w)(v, v) + D²Ψ_δ(w)(iv, iv) ≥ 0`. -/
theorem psiD_subharmonic {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {δ : ℝ} (hδ : 0 < δ) (w v : ℂ) :
    0 ≤ fderiv ℝ (fderiv ℝ (psiD p δ)) w v v +
      fderiv ℝ (fderiv ℝ (psiD p δ)) w (v * I) (v * I) := by
  rw [fderiv2_psiD p hδ, fderiv2_psiD p hδ, ← add_re]
  set a := w.re
  set A := √(a ^ 2 + δ ^ 2) with hA
  have hApos : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hAsq : A ^ 2 = a ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  set v₁ := v.re
  set v₂ := v.im
  have hvI1 : (v * I).re = -v₂ := by simp [v₂]
  have hvI2 : (v * I).im = v₁ := by simp [v₁]
  rw [hvI1, hvI2]
  set Z1 := sigmaD δ w ^ ((p : ℂ) - 1)
  set Z2 := sigmaD δ w ^ ((p : ℂ) - 1 - 1)
  set n := v₁ ^ 2 + v₂ ^ 2 with hn
  have hsq : (((a * v₁ / A : ℝ) : ℂ) + v₂ * I) ^ 2 + (((a * -v₂ / A : ℝ) : ℂ) + v₁ * I) ^ 2 =
      ((-(δ ^ 2 * n / A ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [sq, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im]
      field_simp
      rw [hAsq]
      ring
    · simp only [sq, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im, mul_im]
      field_simp
      ring
  have hsum : (p : ℂ) * (((p : ℂ) - 1) * Z2 * (((a * v₁ / A : ℝ) : ℂ) + v₂ * I) ^ 2 +
      Z1 * ((v₁ ^ 2 * δ ^ 2 / A ^ 3 : ℝ) : ℂ)) +
      (p : ℂ) * (((p : ℂ) - 1) * Z2 * (((a * -v₂ / A : ℝ) : ℂ) + v₁ * I) ^ 2 +
      Z1 * (((-v₂) ^ 2 * δ ^ 2 / A ^ 3 : ℝ) : ℂ)) =
      ((-(p * (p - 1) * (δ ^ 2 * n / A ^ 2)) : ℝ) : ℂ) * Z2 +
      ((p * (δ ^ 2 * n / A ^ 3)) : ℝ) * Z1 := by
    have : (p : ℂ) * (((p : ℂ) - 1) * Z2 * ((((a * v₁ / A : ℝ) : ℂ) + v₂ * I) ^ 2 +
        (((a * -v₂ / A : ℝ) : ℂ) + v₁ * I) ^ 2)) + (p : ℂ) * (Z1 *
        (((v₁ ^ 2 * δ ^ 2 / A ^ 3 : ℝ) : ℂ) + (((-v₂) ^ 2 * δ ^ 2 / A ^ 3 : ℝ) : ℂ))) =
        ((-(p * (p - 1) * (δ ^ 2 * n / A ^ 2)) : ℝ) : ℂ) * Z2 +
        ((p * (δ ^ 2 * n / A ^ 3)) : ℝ) * Z1 := by
      rw [hsq]
      simp only [hn]
      push_cast
      ring
    rw [← this]
    ring
  rw [hsum, add_re, re_ofReal_mul, re_ofReal_mul]
  have hkey := re_cpow_key hp1 hp2 (sigmaD_re_pos hδ w)
  rw [sigmaD_re] at hkey
  have hc : 0 ≤ p * (δ ^ 2 * n / A ^ 3) := by positivity
  have : -(p * (p - 1) * (δ ^ 2 * n / A ^ 2)) * Z2.re + p * (δ ^ 2 * n / A ^ 3) * Z1.re =
      p * (δ ^ 2 * n / A ^ 3) * (Z1.re - (p - 1) * A * Z2.re) := by
    field_simp
    ring
  rw [this]
  exact mul_nonneg hc (by linarith)

/-! ### Vanishing to second order, uniform bounds, and the limit `δ → 0` -/

theorem sigmaD_neg {δ : ℝ} (w : ℂ) : sigmaD δ (-w) = conj (sigmaD δ w) := by
  apply Complex.ext <;> simp [sigmaD]

theorem psiD_neg (p : ℝ) {δ : ℝ} (hδ : 0 < δ) (w : ℂ) : psiD p δ (-w) = psiD p δ w := by
  have hσ := sigmaD_mem_slitPlane hδ w
  have h := cpow_conj (sigmaD δ w) (p : ℂ) (slitPlane_arg_ne_pi hσ)
  rw [conj_ofReal] at h
  rw [psiD, psiD, sigmaD_neg, h, conj_re]

theorem fderiv_psiD_zero (p : ℝ) {δ : ℝ} (hδ : 0 < δ) : fderiv ℝ (psiD p δ) 0 = 0 := by
  set D := fderiv ℝ (psiD p δ) 0
  have hD : HasFDerivAt (psiD p δ) D 0 :=
    ((contDiff_psiD p hδ).differentiable (by simp) 0).hasFDerivAt
  have hneg : HasFDerivAt (fun w => psiD p δ (-w)) (D.comp (-ContinuousLinearMap.id ℝ ℂ)) 0 := by
    have h := (neg_zero (G := ℂ) ▸ hD).comp (0 : ℂ) ((hasFDerivAt_id (0 : ℂ)).neg)
    exact h
  have hfun : (fun w => psiD p δ (-w)) = psiD p δ := funext (psiD_neg p hδ)
  rw [hfun] at hneg
  have hEq := hD.unique hneg
  ext v
  have := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hEq
  simp at this
  simp
  linarith

theorem ofReal_mul_cpow {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0) (p : ℝ) :
    ((δ : ℂ) * z) ^ (p : ℂ) = ((δ ^ p : ℝ) : ℂ) * z ^ (p : ℂ) := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hδ.ne') hz), log_ofReal_mul hδ hz,
    cpow_def_of_ne_zero hz, add_mul, Complex.exp_add, Real.rpow_def_of_pos hδ, ofReal_exp]
  push_cast
  ring_nf

theorem sigmaD_scale {δ : ℝ} (hδ : 0 < δ) (w : ℂ) :
    sigmaD δ w = (δ : ℂ) * sigmaD 1 (w / δ) := by
  have hre : (w / δ).re = w.re / δ := by simp [div_ofReal_re]
  have him : (w / δ).im = w.im / δ := by simp [div_ofReal_im]
  apply Complex.ext
  · rw [sigmaD_re, re_ofReal_mul, sigmaD_re, hre, one_pow,
      Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have : δ * √((w.re / δ) ^ 2 + 1) * (δ * √((w.re / δ) ^ 2 + 1)) =
        δ ^ 2 * ((w.re / δ) ^ 2 + 1) := by
      rw [show δ * √((w.re / δ) ^ 2 + 1) * (δ * √((w.re / δ) ^ 2 + 1)) =
        δ ^ 2 * (√((w.re / δ) ^ 2 + 1) * √((w.re / δ) ^ 2 + 1)) by ring,
        Real.mul_self_sqrt (by positivity)]
    rw [this]
    field_simp
  · rw [sigmaD_im, im_ofReal_mul, sigmaD_im, him]
    field_simp

theorem psiD_scale (p : ℝ) {δ : ℝ} (hδ : 0 < δ) (w : ℂ) :
    psiD p δ w = δ ^ p * psiD p 1 (w / δ) := by
  have hne : sigmaD 1 (w / δ) ≠ 0 := fun h => by
    have := sigmaD_re_pos one_pos (w / δ); rw [h, zero_re] at this; exact lt_irrefl 0 this
  rw [psiD, sigmaD_scale hδ, ofReal_mul_cpow hδ hne, re_ofReal_mul, psiD, Real.one_rpow]
  ring

/-- `|Ψ_δ(w)| ≤ C |w|^p` uniformly in `δ > 0`, for `1 < p ≤ 2`. -/
theorem exists_psiD_bound {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ C, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ w : ℂ, |psiD p δ w| ≤ C * ‖w‖ ^ p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨M, hM0, hM⟩ := exists_quadratic_bound ((contDiff_psiD p one_pos).of_le le_top)
    (psiD_zero p one_pos) (fderiv_psiD_zero p one_pos) 1
  refine ⟨M + 5, by positivity, fun δ hδ w => ?_⟩
  have hwp : 0 ≤ ‖w‖ ^ p := Real.rpow_nonneg (norm_nonneg _) _
  rcases le_or_gt ‖w‖ δ with h | h
  · set u := w / δ with hu
    have hun : ‖u‖ = ‖w‖ / δ := by rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    have hu1 : ‖u‖ ≤ 1 := by rw [hun, div_le_one hδ]; exact h
    have hq := (hM u hu1).1
    have h2p : ‖u‖ ^ 2 ≤ ‖u‖ ^ p := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hu1 hp0.le hp2
    have hδu : δ ^ p * ‖u‖ ^ p = ‖w‖ ^ p := by
      rw [← Real.mul_rpow hδ.le (norm_nonneg _), hun, mul_div_cancel₀ _ hδ.ne']
    rw [psiD_scale p hδ, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hδ _)]
    calc δ ^ p * |psiD p 1 u| ≤ δ ^ p * (M * ‖u‖ ^ p) :=
          mul_le_mul_of_nonneg_left (hq.trans (mul_le_mul_of_nonneg_left h2p hM0))
            (Real.rpow_nonneg hδ.le _)
      _ = M * ‖w‖ ^ p := by rw [← hδu]; ring
      _ ≤ (M + 5) * ‖w‖ ^ p := by nlinarith
  · have hσ : ‖sigmaD δ w‖ ≤ 2 * ‖w‖ := by
      have h1 : ‖sigmaD δ w‖ ^ 2 = ‖w‖ ^ 2 + δ ^ 2 := by
        rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply, sigmaD_re, sigmaD_im,
          Real.mul_self_sqrt (by positivity)]
        ring
      have h2 : ‖sigmaD δ w‖ ^ 2 ≤ (2 * ‖w‖) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    have hσp : ‖sigmaD δ w‖ ^ p ≤ 4 * ‖w‖ ^ p := by
      calc ‖sigmaD δ w‖ ^ p ≤ (2 * ‖w‖) ^ p :=
            Real.rpow_le_rpow (norm_nonneg _) hσ hp0.le
        _ = 2 ^ p * ‖w‖ ^ p := Real.mul_rpow (by norm_num) (norm_nonneg _)
        _ ≤ 4 * ‖w‖ ^ p := by
            refine mul_le_mul_of_nonneg_right ?_ hwp
            calc (2 : ℝ) ^ p ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
              _ = 4 := by norm_num
    have hδp : δ ^ p ≤ ‖w‖ ^ p := Real.rpow_le_rpow hδ.le h.le hp0.le
    rw [psiD]
    calc |(sigmaD δ w ^ (p : ℂ)).re - δ ^ p| ≤ |(sigmaD δ w ^ (p : ℂ)).re| + |δ ^ p| :=
          abs_sub _ _
      _ ≤ ‖sigmaD δ w‖ ^ p + ‖w‖ ^ p := by
          refine add_le_add ((abs_re_le_norm _).trans (norm_cpow_real _ _).le) ?_
          rw [abs_of_nonneg (Real.rpow_nonneg hδ.le _)]; exact hδp
      _ ≤ (M + 5) * ‖w‖ ^ p := by nlinarith

/-- The limit `Φ(w) = Re((|a| + ib)^p)` of `Ψ_δ`, the function in Pichorides' inequality. -/
noncomputable def pichoridesPhi (p : ℝ) (w : ℂ) : ℝ :=
  ((((|w.re| : ℝ) : ℂ) + w.im * I) ^ (p : ℂ)).re

theorem tendsto_psiD {p : ℝ} (hp : 0 < p) (w : ℂ) :
    Tendsto (fun δ => psiD p δ w) (𝓝[>] 0) (𝓝 (pichoridesPhi p w)) := by
  set z₀ : ℂ := ((|w.re| : ℝ) : ℂ) + w.im * I
  have hσ : Tendsto (fun δ => sigmaD δ w) (𝓝 0) (𝓝 z₀) := by
    have hc : Continuous fun δ : ℝ => sigmaD δ w := by
      unfold sigmaD; fun_prop
    have := hc.tendsto 0
    simpa [sigmaD, Real.sqrt_sq_eq_abs, z₀] using this
  have hpow : ContinuousAt (fun z : ℂ => z ^ (p : ℂ)) z₀ := by
    by_cases hz : z₀ ∈ slitPlane
    · exact continuousAt_cpow_const hz
    · have h0 : z₀ = 0 := by
        rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hz
        apply Complex.ext
        · simp only [z₀, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
            sub_zero, add_zero, zero_re] at hz ⊢
          linarith [abs_nonneg w.re, hz.1]
        · simpa using hz.2
      rw [h0]
      exact (continuousAt_cpow_zero_of_re_pos (z := (p : ℂ)) (by simpa using hp)).comp
        (f := fun z : ℂ => (z, (p : ℂ))) (continuousAt_id.prodMk continuousAt_const)
  have h1 := (Complex.continuous_re.tendsto _).comp (hpow.tendsto.comp hσ)
  have h2 : Tendsto (fun δ : ℝ => δ ^ p) (𝓝 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
    rwa [Real.zero_rpow hp.ne'] at this
  have := (h1.sub h2).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [sub_zero] at this
  exact this

end Azurite.DLMF
