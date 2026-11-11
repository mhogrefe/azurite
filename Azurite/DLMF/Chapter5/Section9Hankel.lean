/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9Trig

/-!
# DLMF §5.9(i): Hankel's loop integral

Formalization of <https://dlmf.nist.gov/5.9>, equation 5.9.2,
`1/Γ(z) = (2πi)⁻¹ ∫_{−∞}^{(0+)} e^t t^{−z} dt`.

The loop is the keyhole contour (Figure 5.9.1): in from `∞ e^{−iβ}` along the ray `arg t = −β`
to `|t| = δ`, once around the circle `|t| = δ` counterclockwise from `arg t = −β` to `arg t = α`,
and out along the ray `arg t = α`. The power `t^{−z}` is continued along the contour from its
principal value on the positive real axis: at `t = r e^{iϑ}` it is `r^{−z} e^{−izϑ}`
(`hankelF`). DLMF's loop is `α = β = π` (`dlmf_5_9_2`); we prove the formula for every
`α, β ∈ (½π, 3π/2)` and `δ > 0` (`hankelLoop_eq`), which is used for 5.9.2_5.

Proof: for `ℜz < 1` each full ray `∫₀^∞` is a complex Laplace transform (5.9.1), giving
`Γ(1 − z) e^{±iπ(1−z)}` (`integral_ray_full`), so the two rays contribute
`2i sin(πz) Γ(1 − z) = 2πi/Γ(z)`; the pieces of the rays inside `|t| ≤ δ` and the arc expand
termwise in the exponential series and cancel (`hasSum_integral_ray_small`,
`hasSum_hankelArc`). Both sides are entire in `z` (the rays are Mellin transforms, the arc a
parametric integral over a compact interval), so the identity theorem removes `ℜz < 1`.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-- `e^t t^{−z}` at `t = r e^{iϑ}`, with the branch `t^{−z} = r^{−z} e^{−izϑ}`. -/
noncomputable def hankelF (z : ℂ) (r ϑ : ℝ) : ℂ :=
  cexp (r * cexp (ϑ * I)) * ((r : ℂ) ^ (-z) * cexp (-(z * ϑ * I)))

/-- The ray `arg t = ϑ`, `|t| > δ`, traversed outward: `∫_δ^∞ e^t t^{−z} e^{iϑ} dr`. -/
noncomputable def hankelRay (z : ℂ) (δ ϑ : ℝ) : ℂ := ∫ r in Ioi δ, hankelF z r ϑ * cexp (ϑ * I)

/-- The arc `|t| = δ`, `−β ≤ arg t ≤ α`, traversed counterclockwise. -/
noncomputable def hankelArc (z : ℂ) (δ α β : ℝ) : ℂ :=
  ∫ θ in (-β)..α, hankelF z δ θ * (I * δ * cexp (θ * I))

/-- The keyhole loop integral `∫ e^t t^{−z} dt`: in along `arg t = −β`, around `|t| = δ`, out along
`arg t = α`. -/
noncomputable def hankelLoop (z : ℂ) (δ α β : ℝ) : ℂ :=
  hankelRay z δ α - hankelRay z δ (-β) + hankelArc z δ α β

theorem hankelF_mul_eq (z : ℂ) (r ϑ : ℝ) :
    hankelF z r ϑ * cexp (ϑ * I) =
      cexp ((1 - z) * ϑ * I) * ((r : ℂ) ^ ((1 - z) - 1) * cexp (-(-cexp (ϑ * I) * r))) := by
  unfold hankelF
  rw [show (1 - z) - 1 = -z by ring, show (1 - z) * ϑ * I = -(z * ϑ * I) + ϑ * I by ring,
    Complex.exp_add]
  ring_nf

theorem norm_cexp_mul_I_ofReal (ϑ : ℝ) : ‖cexp (ϑ * I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem re_neg_cexp {ϑ : ℝ} : (-cexp (ϑ * I)).re = -Real.cos ϑ := by
  rw [neg_re, exp_ofReal_mul_I_re]

/-! ### The full rays (`ℜz < 1`) -/

theorem cexp_ofReal_mul_I_cpow {ψ : ℝ} (h1 : -π < ψ) (h2 : ψ ≤ π) (w : ℂ) :
    cexp (ψ * I) ^ w = cexp (ψ * I * w) := by
  rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _), log_exp (by simpa using h1) (by simpa using h2)]

/-- A full ray `∫₀^∞ e^t t^{−z} e^{iϑ} dr` with `ϑ = ψ + σπ`, `|ψ| < ½π`, `σ = ±1`. -/
theorem integral_ray_full {z : ℂ} (hz : z.re < 1) {ψ σ : ℝ} (hψ1 : -(π / 2) < ψ) (hψ2 : ψ < π / 2)
    (hσ : σ = 1 ∨ σ = -1) :
    ∫ r in Ioi (0 : ℝ), hankelF z r (ψ + σ * π) * cexp ((ψ + σ * π : ℝ) * I) =
      Gamma (1 - z) * cexp (σ * π * (1 - z) * I) := by
  have hneg : -cexp (((ψ + σ * π : ℝ) : ℂ) * I) = cexp (ψ * I) := by
    have : cexp ((σ * π : ℝ) * I) = -1 := by
      rcases hσ with rfl | rfl
      · simp [exp_pi_mul_I]
      · push_cast; rw [show -1 * (π : ℂ) * I = -(π * I) by ring, Complex.exp_neg, exp_pi_mul_I]
        norm_num
    rw [ofReal_add, add_mul, Complex.exp_add, this]; ring
  have hre : 0 < (cexp (ψ * I)).re := by
    rw [exp_ofReal_mul_I_re]; exact Real.cos_pos_of_mem_Ioo ⟨hψ1, hψ2⟩
  have ha : 0 < (1 - z).re := by simp; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (fun r _ => hankelF_mul_eq z r _), hneg,
    integral_const_mul, integral_cpow_mul_cexp_neg ha hre,
    cexp_ofReal_mul_I_cpow (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  rw [show ∀ A B C : ℂ, A * (B * C) = B * (A * C) from fun A B C => by ring, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem integrableOn_hankelRay {z : ℂ} (hz : z.re < 1) {ϑ : ℝ} (hϑ : Real.cos ϑ < 0) :
    IntegrableOn (fun r : ℝ => hankelF z r ϑ * cexp (ϑ * I)) (Ioi 0) := by
  have ha : 0 < (1 - z).re := by simp; linarith
  have hre : 0 < (-cexp (ϑ * I)).re := by rw [re_neg_cexp]; linarith
  exact ((integrableOn_cpow_sub_one_mul_cexp_neg ha hre).const_mul (cexp ((1 - z) * ϑ * I))).congr
    (ae_of_all _ fun r => (hankelF_mul_eq z r ϑ).symm)

/-! ### The small pieces (`ℜz < 1`) -/

/-- Termwise integration: `∫₀^δ r^{a−1} e^{cr} dr = ∑ cⁿ/n! · δ^{a+n}/(a + n)` (`ℜa > 0`). -/
theorem hasSum_integral_cpow_mul_cexp {δ : ℝ} (hδ : 0 < δ) (c a : ℂ) (ha : 0 < a.re) :
    HasSum (fun n : ℕ => c ^ n / (n ! : ℂ) * ((δ : ℂ) ^ (a + n) / (a + n)))
      (∫ r in (0 : ℝ)..δ, (r : ℂ) ^ (a - 1) * cexp (c * r)) := by
  have hre : ∀ n : ℕ, 0 < (a + n).re := fun n => by
    simp only [add_re, natCast_re]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hval : ∀ n : ℕ, ∫ r in (0 : ℝ)..δ, c ^ n / (n ! : ℂ) * (r : ℂ) ^ ((a + n) - 1) =
      c ^ n / (n ! : ℂ) * ((δ : ℂ) ^ (a + n) / (a + n)) := fun n => by
    rw [intervalIntegral.integral_const_mul, integral_cpow (Or.inl (by simp; linarith [hre n]))]
    have h0 : (a + n) ≠ 0 := fun h => by have := hre n; rw [h] at this; simp at this
    simp [h0]
  simp_rw [← hval]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n r => ‖c‖ ^ n * δ ^ n / n ! * r ^ (a.re - 1)) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun r hr => ?_) measurableSet_uIoc
    rw [uIoc_of_le hδ.le] at hr
    exact ((hasDerivAt_ofReal_cpow' _ hr.1).continuousAt.const_mul _).continuousWithinAt
  · refine ae_of_all _ fun r hr => ?_
    rw [uIoc_of_le hδ.le] at hr
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, norm_cpow_eq_rpow_re_of_pos hr.1]
    have e : (a + n - 1).re = (a.re - 1) + n := by simp; ring
    rw [e, Real.rpow_add hr.1, Real.rpow_natCast]
    have h1 : r ^ n ≤ δ ^ n := pow_le_pow_left₀ hr.1.le hr.2 n
    have h2 : 0 ≤ r ^ (a.re - 1) := Real.rpow_nonneg hr.1.le _
    have h3 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right h3]
    calc ‖c‖ ^ n * (r ^ (a.re - 1) * r ^ n) = ‖c‖ ^ n * r ^ n * r ^ (a.re - 1) := by ring
      _ ≤ ‖c‖ ^ n * δ ^ n * r ^ (a.re - 1) := by gcongr
  · exact ae_of_all _ fun r _ =>
      ((Real.summable_pow_div_factorial (‖c‖ * δ)).mul_right (r ^ (a.re - 1))).congr
        fun n => by rw [mul_pow]
  · have : (fun r : ℝ => ∑' n : ℕ, ‖c‖ ^ n * δ ^ n / n ! * r ^ (a.re - 1)) =
        fun r => Real.exp (‖c‖ * δ) * r ^ (a.re - 1) := by
      funext r
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, ← (NormedSpace.expSeries_div_hasSum_exp
        (‖c‖ * δ)).tsum_eq]
      simp_rw [mul_pow]
    rw [this]
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  · refine ae_of_all _ fun r hr => ?_
    rw [uIoc_of_le hδ.le] at hr
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.1.ne'
    have := ((hasSum_cexp (c * r)).mul_left ((r : ℂ) ^ (a - 1)))
    convert this using 1
    funext n
    rw [show a + n - 1 = (a - 1) + n by ring, cpow_add _ _ hr0, cpow_natCast, mul_pow]
    ring

/-- The arc expanded termwise: with `k = n + 1 − z`,
`∫_{−β}^{α} e^{δe^{iθ}} δ^{−z} e^{−izθ} iδe^{iθ} dθ = ∑ δᵏ/n! · (e^{ikα} − e^{−ikβ})/k`. -/
theorem hasSum_hankelArc {δ : ℝ} (hδ : 0 < δ) {α β : ℝ} (hαβ : -β ≤ α) (z : ℂ)
    (hz : ∀ n : ℕ, (n : ℂ) + 1 - z ≠ 0) :
    HasSum (fun n : ℕ => (δ : ℂ) ^ ((n : ℂ) + 1 - z) / (n ! : ℂ) *
      ((cexp (((n : ℂ) + 1 - z) * α * I) - cexp (-(((n : ℂ) + 1 - z) * β * I))) /
        ((n : ℂ) + 1 - z))) (hankelArc z δ α β) := by
  have hδ0 : (δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hδ.ne'
  set F : ℕ → ℝ → ℂ := fun n θ => I * (δ : ℂ) ^ ((n : ℂ) + 1 - z) / (n ! : ℂ) *
    cexp ((((n : ℂ) + 1 - z) * I) * θ) with hF
  have hval : ∀ n : ℕ, ∫ θ in (-β)..α, F n θ = (δ : ℂ) ^ ((n : ℂ) + 1 - z) / (n ! : ℂ) *
      ((cexp (((n : ℂ) + 1 - z) * α * I) - cexp (-(((n : ℂ) + 1 - z) * β * I))) /
        ((n : ℂ) + 1 - z)) := fun n => by
    simp only [hF]
    rw [intervalIntegral.integral_const_mul,
      integral_exp_mul_complex (mul_ne_zero (hz n) I_ne_zero)]
    have := hz n
    push_cast
    field_simp
  simp_rw [← hval]
  set M : ℝ := max |α| |β| with hM
  set C : ℝ := δ ^ (1 - z.re) * Real.exp (M * |z.im|) with hC
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => δ ^ n / n ! * C) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · exact (by fun_prop : Continuous (F n)).aestronglyMeasurable
  · refine ae_of_all _ fun θ hθ => ?_
    rw [uIoc_of_le hαβ] at hθ
    simp only [hF]
    rw [norm_mul, norm_div, norm_mul, norm_I, one_mul, norm_cpow_eq_rpow_re_of_pos hδ,
      Complex.norm_natCast, Complex.norm_exp]
    have hre : ((n : ℂ) + 1 - z).re = n + (1 - z.re) := by simp; ring
    have him : ((((n : ℂ) + 1 - z) * I) * θ).re = z.im * θ := by simp
    rw [hre, him, Real.rpow_add hδ, Real.rpow_natCast]
    have hθM : |θ| ≤ M := by
      rw [hM, abs_le]
      constructor
      · have := le_abs_self β; have := le_max_right |α| |β|; linarith [hθ.1]
      · have := le_abs_self α; have := le_max_left |α| |β|; linarith [hθ.2]
    have he : Real.exp (z.im * θ) ≤ Real.exp (M * |z.im|) := by
      refine Real.exp_le_exp.mpr ?_
      calc z.im * θ ≤ |z.im * θ| := le_abs_self _
        _ = |z.im| * |θ| := abs_mul _ _
        _ ≤ |z.im| * M := mul_le_mul_of_nonneg_left hθM (abs_nonneg _)
        _ = M * |z.im| := mul_comm _ _
    have h3 : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    rw [hC, div_mul_eq_mul_div (δ ^ n), div_mul_eq_mul_div, div_le_div_iff_of_pos_right h3]
    have := Real.rpow_nonneg hδ.le (1 - z.re)
    have := pow_nonneg hδ.le n
    calc δ ^ n * δ ^ (1 - z.re) * Real.exp (z.im * θ)
        ≤ δ ^ n * δ ^ (1 - z.re) * Real.exp (M * |z.im|) := by gcongr
      _ = _ := by ring
  · exact ae_of_all _ fun _ _ => (Real.summable_pow_div_factorial δ).mul_right C
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun θ _ => ?_
    have := (hasSum_cexp ((δ : ℂ) * cexp (θ * I))).mul_right
      ((δ : ℂ) ^ (-z) * cexp (-(z * θ * I)) * (I * δ * cexp (θ * I)))
    convert this using 1
    · funext n
      simp only [hF]
      rw [show (n : ℂ) + 1 - z = (-z) + (n : ℂ) + 1 by ring, cpow_add _ _ hδ0, cpow_add _ _ hδ0,
        cpow_natCast, cpow_one, mul_pow, ← Complex.exp_nat_mul]
      rw [show ((-z + n + 1) * I) * θ = (n * (θ * I)) + (-(z * θ * I)) + θ * I by ring,
        Complex.exp_add, Complex.exp_add]
      ring
    · unfold hankelF
      ring

/-- For `ℜz < 1`: the small pieces of the rays cancel the arc. -/
theorem hankelLoop_eq_of_re_lt_one {z : ℂ} (hz : z.re < 1) {δ α β : ℝ} (hδ : 0 < δ)
    (hα1 : π / 2 < α) (hα2 : α < 3 * π / 2) (hβ1 : π / 2 < β) (hβ2 : β < 3 * π / 2) :
    hankelLoop z δ α β = 2 * π * I * (Gamma z)⁻¹ := by
  have hk : ∀ n : ℕ, (n : ℂ) + 1 - z ≠ 0 := fun n h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have ha : 0 < (1 - z).re := by simp; linarith
  have hcos : ∀ ϑ : ℝ, π / 2 < |ϑ| → |ϑ| < 3 * π / 2 → Real.cos ϑ < 0 := fun ϑ h1 h2 => by
    rw [← Real.cos_abs]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  have hcα : Real.cos α < 0 := hcos α (by rw [abs_of_pos (by linarith [Real.pi_pos])]; exact hα1)
    (by rw [abs_of_pos (by linarith [Real.pi_pos])]; exact hα2)
  have hcβ : Real.cos (-β) < 0 := hcos (-β)
    (by rw [abs_neg, abs_of_pos (by linarith [Real.pi_pos])]; exact hβ1)
    (by rw [abs_neg, abs_of_pos (by linarith [Real.pi_pos])]; exact hβ2)
  -- splitting a ray at `δ`
  have hsplit : ∀ ϑ : ℝ, Real.cos ϑ < 0 → hankelRay z δ ϑ =
      (∫ r in Ioi (0 : ℝ), hankelF z r ϑ * cexp (ϑ * I)) -
        ∫ r in (0 : ℝ)..δ, hankelF z r ϑ * cexp (ϑ * I) := fun ϑ hϑ => by
    have hi := integrableOn_hankelRay hz hϑ
    rw [hankelRay, intervalIntegral.integral_of_le hδ.le, ← Ioc_union_Ioi_eq_Ioi hδ.le,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hδ.le))]
    ring
  -- the small piece of a ray as a series
  have hsmall : ∀ ϑ : ℝ, HasSum (fun n : ℕ => (δ : ℂ) ^ ((n : ℂ) + 1 - z) / (n ! : ℂ) *
      (cexp (((n : ℂ) + 1 - z) * ϑ * I) / ((n : ℂ) + 1 - z)))
      (∫ r in (0 : ℝ)..δ, hankelF z r ϑ * cexp (ϑ * I)) := fun ϑ => by
    have h := (hasSum_integral_cpow_mul_cexp hδ (cexp (ϑ * I)) (1 - z) ha).mul_left
      (cexp ((1 - z) * ϑ * I))
    rw [← intervalIntegral.integral_const_mul] at h
    convert h using 1
    · funext n
      rw [show (1 - z) + (n : ℂ) = (n : ℂ) + 1 - z by ring, ← Complex.exp_nat_mul,
        show ((n : ℂ) + 1 - z) * ϑ * I = (1 - z) * ϑ * I + n * (ϑ * I) by ring, Complex.exp_add]
      ring
    · refine intervalIntegral.integral_congr fun r _ => ?_
      rw [hankelF_mul_eq, neg_mul, neg_neg]
  have hzero := ((hasSum_hankelArc hδ (α := α) (β := β) (by linarith [Real.pi_pos]) z hk).sub
    (hsmall α)).add (hsmall (-β))
  have hzero' : HasSum (fun _ : ℕ => (0 : ℂ))
      (hankelArc z δ α β - (∫ r in (0 : ℝ)..δ, hankelF z r α * cexp (α * I)) +
        ∫ r in (0 : ℝ)..δ, hankelF z r (-β) * cexp ((-β : ℝ) * I)) := by
    convert hzero using 1
    funext n
    push_cast
    rw [show ((n : ℂ) + 1 - z) * -(β : ℂ) * I = -(((n : ℂ) + 1 - z) * β * I) by ring]
    ring
  have h0 := hzero'.unique hasSum_zero
  have hfull1 := integral_ray_full hz (ψ := α - π) (σ := 1) (by linarith) (by linarith)
    (Or.inl rfl)
  have hfull2 := integral_ray_full hz (ψ := π - β) (σ := -1) (by linarith) (by linarith)
    (Or.inr rfl)
  rw [show α - π + 1 * π = α by ring] at hfull1
  rw [show π - β + -1 * π = -β by ring] at hfull2
  rw [hankelLoop, hsplit α hcα, hsplit (-β) hcβ, hfull1, hfull2]
  have e : Gamma (1 - z) * cexp ((1 : ℝ) * π * (1 - z) * I) -
      Gamma (1 - z) * cexp ((-1 : ℝ) * π * (1 - z) * I) =
        2 * I * Complex.sin (π * z) * Gamma (1 - z) := by
    rw [← Complex.sin_pi_sub, show (π : ℂ) - π * z = π * (1 - z) by ring]
    have := two_sin (π * (1 - z))
    push_cast
    rw [show 2 * I * Complex.sin (π * (1 - z)) * Gamma (1 - z) =
      I * (2 * Complex.sin (π * (1 - z))) * Gamma (1 - z) by ring, this]
    ring_nf
    rw [I_sq]
    ring_nf
  have hrefl : 2 * I * Complex.sin (π * z) * Gamma (1 - z) = 2 * π * I * (Gamma z)⁻¹ := by
    by_cases hs : Complex.sin (π * z) = 0
    · obtain ⟨k, hk'⟩ := Complex.sin_eq_zero_iff.mp hs
      have hzk : z = k := by
        have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
        field_simp at hk'
        linear_combination hk'
      have hk0 : k ≤ 0 := by
        have := congrArg re hzk
        simp at this
        have : (k : ℝ) < 1 := by linarith
        exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
      obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hk0
      have hz' : z = -(m : ℂ) := by rw [hzk, hm]; push_cast; ring
      rw [hs, hz', Gamma_neg_nat_eq_zero, inv_zero]
      ring
    · have hG : Gamma z ≠ 0 := by
        refine Gamma_ne_zero fun m hm => hs ?_
        rw [hm, show (π : ℂ) * -(m : ℂ) = -(m * π) by ring, Complex.sin_neg,
          Complex.sin_nat_mul_pi, neg_zero]
      have hrf := Gamma_mul_Gamma_one_sub z
      have : Gamma (1 - z) = π / Complex.sin (π * z) / Gamma z := by
        rw [← hrf]; field_simp
      rw [this]
      field_simp
  rw [← hrefl, ← e]
  linear_combination h0

/-! ### Analytic continuation in `z` -/

/-- A ray, as a function of `z`, is a Mellin transform at `1 − z`. -/
theorem hankelRay_eq_mellin (z : ℂ) (δ ϑ : ℝ) (hδ : 0 ≤ δ) :
    hankelRay z δ ϑ = cexp ((1 - z) * ϑ * I) *
      mellin ((Ioi δ).indicator fun r : ℝ => cexp (cexp (ϑ * I) * r)) (1 - z) := by
  unfold mellin hankelRay
  rw [← integral_const_mul]
  have e : ∀ r : ℝ, cexp ((1 - z) * ϑ * I) *
      ((r : ℂ) ^ (1 - z - 1) • (Ioi δ).indicator (fun r : ℝ => cexp (cexp (ϑ * I) * r)) r) =
      (Ioi δ).indicator (fun r : ℝ => hankelF z r ϑ * cexp (ϑ * I)) r := fun r => by
    by_cases hr : r ∈ Ioi δ
    · rw [indicator_of_mem hr, indicator_of_mem hr, smul_eq_mul, hankelF_mul_eq, neg_mul, neg_neg]
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, smul_zero, mul_zero]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hδ]

theorem differentiable_hankelRay {δ ϑ : ℝ} (hδ : 0 < δ) (hϑ : Real.cos ϑ < 0) :
    Differentiable ℂ fun z => hankelRay z δ ϑ := by
  intro z
  simp_rw [fun z => hankelRay_eq_mellin z δ ϑ hδ.le]
  refine ((((differentiableAt_const _).sub differentiableAt_id).mul_const _).mul_const _).cexp.mul
    ?_
  have hm : DifferentiableAt ℂ (mellin ((Ioi δ).indicator fun r : ℝ => cexp (cexp (ϑ * I) * r)))
      (1 - z) := by
    refine mellin_differentiableAt_of_isBigO_rpow_exp (a := -Real.cos ϑ) (b := (1 - z).re - 1)
      (by linarith) ?_ ?_ ?_ (by linarith)
    · exact ((by fun_prop : Continuous fun r : ℝ => cexp (cexp (ϑ * I) * r))
        |>.locallyIntegrable.indicator
        measurableSet_Ioi).locallyIntegrableOn _
    · refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_gt_atTop δ] with r hr
      rw [indicator_of_mem (show r ∈ Ioi δ from hr), Complex.norm_exp, one_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      refine le_of_eq ?_
      congr 1
      simp only [mul_re, exp_ofReal_mul_I_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      ring
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
      rw [indicator_of_notMem (show r ∉ Ioi δ from fun h => by
        simp only [mem_Ioi] at h; linarith [hr.2])]
      simp
  exact hm.comp z ((differentiableAt_const _).sub differentiableAt_id)

/-- `z ↦ ∫ₐᵇ A(θ) e^{−zL(θ)} dθ` is entire. -/
theorem differentiable_integral_mul_cexp {A L : ℝ → ℂ} (hA : Continuous A) (hL : Continuous L)
    (a b : ℝ) : Differentiable ℂ fun z => ∫ θ in a..b, A θ * cexp (-(z * L θ)) := by
  intro z₀
  obtain ⟨CA, hCA⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    hA.continuousOn
  obtain ⟨CL, hCL⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    hL.continuousOn
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := a) (b := b)
    (F := fun z θ => A θ * cexp (-(z * L θ)))
    (F' := fun z θ => A θ * cexp (-(z * L θ)) * (-L θ)) (x₀ := z₀)
    (bound := fun _ => CA * Real.exp ((‖z₀‖ + 1) * CL) * CL)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (by fun_prop : Continuous fun θ => A θ * cexp (-(z * L θ)))
      |>.aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => A θ * cexp (-(z₀ * L θ))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ => A θ * cexp (-(z₀ * L θ)) * (-L θ)).aestronglyMeasurable)
    (ae_of_all _ fun θ hθ z hz => by
      have h1 := hCA θ (uIoc_subset_uIcc hθ)
      have h2 := hCL θ (uIoc_subset_uIcc hθ)
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall
          (show z ∈ Metric.ball z₀ 1 from hz))
        have h3 : ‖z‖ ≤ ‖z₀‖ + dist z z₀ := by
          rw [dist_eq_norm]; linarith [norm_sub_norm_le z z₀]
        linarith [(Metric.mem_ball.mp hz).le]
      rw [norm_mul, norm_mul, norm_neg]
      have h4 : ‖cexp (-(z * L θ))‖ ≤ Real.exp ((‖z₀‖ + 1) * CL) := by
        refine (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_neg, norm_mul]
        exact mul_le_mul hz' h2 (norm_nonneg _) (by positivity)
      have hCA0 : 0 ≤ CA := (norm_nonneg _).trans h1
      calc ‖A θ‖ * ‖cexp (-(z * L θ))‖ * ‖L θ‖
          ≤ CA * Real.exp ((‖z₀‖ + 1) * CL) * CL := by gcongr)
    intervalIntegrable_const
    (ae_of_all _ fun θ _ z _ => by
      have := ((hasDerivAt_id z).mul_const (L θ)).neg.cexp.const_mul (A θ)
      simpa [mul_comm, mul_assoc, mul_left_comm] using this)
  exact hd.2.differentiableAt

theorem hankelArc_eq (z : ℂ) {δ : ℝ} (hδ : 0 < δ) (α β : ℝ) :
    hankelArc z δ α β = ∫ θ in (-β)..α, (cexp (δ * cexp (θ * I)) * (I * δ * cexp (θ * I))) *
      cexp (-(z * (((Real.log δ : ℝ) : ℂ) + θ * I))) := by
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hδ0 : (δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hδ.ne'
  simp only [hankelF]
  rw [cpow_def_of_ne_zero hδ0, ← ofReal_log hδ.le, mul_add, neg_add, Complex.exp_add]
  ring_nf

theorem differentiable_hankelArc {δ : ℝ} (hδ : 0 < δ) (α β : ℝ) :
    Differentiable ℂ fun z => hankelArc z δ α β := by
  simp_rw [fun z => hankelArc_eq z hδ α β]
  exact differentiable_integral_mul_cexp (by fun_prop) (by fun_prop) _ _

/-- Hankel's loop for every keyhole with `α, β ∈ (½π, 3π/2)`: `∫ e^t t^{−z} dt = 2πi/Γ(z)`. -/
theorem hankelLoop_eq (z : ℂ) {δ α β : ℝ} (hδ : 0 < δ) (hα1 : π / 2 < α) (hα2 : α < 3 * π / 2)
    (hβ1 : π / 2 < β) (hβ2 : β < 3 * π / 2) :
    hankelLoop z δ α β = 2 * π * I * (Gamma z)⁻¹ := by
  have hcos : ∀ ϑ : ℝ, π / 2 < ϑ → ϑ < 3 * π / 2 → Real.cos ϑ < 0 := fun ϑ h1 h2 =>
    Real.cos_neg_of_pi_div_two_lt_of_lt h1 (by linarith)
  have hf : Differentiable ℂ fun z => hankelLoop z δ α β :=
    ((differentiable_hankelRay hδ (hcos α hα1 hα2)).sub
      (differentiable_hankelRay hδ (by rw [Real.cos_neg]; exact hcos β hβ1 hβ2))).add
      (differentiable_hankelArc hδ α β)
  have hg : Differentiable ℂ fun z => 2 * π * I * (Gamma z)⁻¹ :=
    differentiable_one_div_Gamma.const_mul _
  have heq := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ 0) (by
      filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds
        (show (0 : ℂ) ∈ {w : ℂ | w.re < 1} by simp)] with w hw
      exact hankelLoop_eq_of_re_lt_one hw hδ hα1 hα2 hβ1 hβ2)
  exact heq (mem_univ z)

/-- **DLMF 5.9.2** (Hankel's loop integral):
`1/Γ(z) = (2πi)⁻¹ ∫_{−∞}^{(0+)} e^t t^{−z} dt`, for every `z`, on the keyhole loop around the
negative real axis of any radius `δ > 0` (`α = β = π`). -/
theorem dlmf_5_9_2 (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    1 / Gamma z = 1 / (2 * π * I) * hankelLoop z δ π π := by
  have hπ := Real.pi_pos
  rw [hankelLoop_eq z hδ (by linarith) (by linarith) (by linarith) (by linarith)]
  have : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

end Azurite.DLMF
