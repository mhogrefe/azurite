/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11RatioThree
import Azurite.DLMF.Chapter5.Section12Holo

/-!
# DLMF §5.12: Beta function — Euler's beta integral

Formalization of <https://dlmf.nist.gov/5.12>, equations 5.12.1–5.12.4 and 5.12.7.

5.12.1 defines `B(a, b) = ∫₀¹ t^{a−1}(1 − t)^{b−1} dt = Γ(a)Γ(b)/Γ(a + b)` for `ℜa, ℜb > 0`. Later
equations of the section use `B` for arguments outside these half-planes, meaning its meromorphic
continuation, which is the Gamma quotient; so `dlmfBeta a b` is that quotient (with Mathlib's
`Γ(−n) = 0`, a pole of `Γ(a)` or `Γ(b)` gives `B = 0`, the value of `1/B` used in 5.12.5–5.12.9
being `0` there too), and `dlmf_5_12_1` proves that it is the integral.

* 5.12.2 (`t = sin²θ`), 5.12.3 (`t = u/(1 − u)`), 5.12.7 (`s = e^{2t}` and 5.12.3) are
  substitutions in Euler's integral (`integral_image_eq_integral_abs_deriv_smul`).
* 5.12.4 is the substitution `t = zu/(1 + z − u)` for `z > 0`, continued analytically to
  `|ph z| < π` (`differentiableOn_integral_of_holo`, identity theorem on the slit plane).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- **The beta function** `B(a, b) = Γ(a)Γ(b)/Γ(a + b)` (5.12.1; the integral form is
`dlmf_5_12_1`). -/
noncomputable def dlmfBeta (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

theorem dlmfBeta_comm (a b : ℂ) : dlmfBeta a b = dlmfBeta b a := by
  simp only [dlmfBeta, mul_comm (Gamma a), add_comm a]

/-- **DLMF 5.12.1** (Euler's beta integral):
`B(a, b) = ∫₀¹ t^{a−1}(1 − t)^{b−1} dt = Γ(a)Γ(b)/Γ(a + b)`, `ℜa, ℜb > 0`. -/
theorem dlmf_5_12_1 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    dlmfBeta a b = ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) ∧
      ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) =
        Gamma a * Gamma b / Gamma (a + b) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div a b ha hb
  rw [Complex.betaIntegral] at h
  exact ⟨h.symm, h⟩

/-- Euler's integral over the open interval. -/
theorem integral_Ioo_beta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) = dlmfBeta a b := by
  rw [(dlmf_5_12_1 ha hb).1, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

theorem integrableOn_beta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) (Ioo 0 1) := by
  have h := (Complex.betaIntegral_convergent ha hb)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
  exact h

/-! ### Powers of positive reals -/

theorem cpow_pos_eq {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w = cexp (w * Real.log x) := by
  rw [ofReal_cpow_eq_exp hx, mul_comm]

/-! ### 5.12.2 -/

theorem sin_sq_image :
    (fun θ : ℝ => Real.sin θ ^ 2) '' Ioo 0 (π / 2) = Ioo 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
    have hs := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · have h := intermediate_value_Ioo (f := fun θ : ℝ => Real.sin θ ^ 2)
      (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2) (by fun_prop)
    simpa using h

theorem sin_sq_injOn : InjOn (fun θ : ℝ => Real.sin θ ^ 2) (Ioo 0 (π / 2)) := by
  intro x hx y hy hxy
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_pos, hx.2])
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy.1 (by linarith [Real.pi_pos, hy.2])
  have h : Real.sin x = Real.sin y := (pow_left_inj₀ hsx.le hsy.le two_ne_zero).mp hxy
  have hπ := Real.pi_pos
  exact Real.injOn_sin ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ h

/-- **DLMF 5.12.2**: `∫₀^{π/2} sin^{2a−1}θ cos^{2b−1}θ dθ = ½B(a, b)`. -/
theorem dlmf_5_12_2 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ θ in (0 : ℝ)..(π / 2), (Real.sin θ : ℂ) ^ (2 * a - 1) * (Real.cos θ : ℂ) ^ (2 * b - 1) =
      1 / 2 * dlmfBeta a b := by
  have hπ := Real.pi_pos
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 (π / 2))
    (f := fun θ : ℝ => Real.sin θ ^ 2) (f' := fun θ => 2 * Real.sin θ * Real.cos θ)
    measurableSet_Ioo (fun θ _ => by
      have := (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_sin θ)
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      · ext x; simp [sq]
      · ring)
    sin_sq_injOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1))
  rw [sin_sq_image, integral_Ioo_beta ha hb] at h
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo, h,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
  have h1 : (1 : ℂ) - ((Real.sin θ ^ 2 : ℝ) : ℂ) = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by
    have : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by rw [← Real.cos_sq_add_sin_sq θ]; ring
    rw [this]; push_cast; ring
  rw [abs_of_pos (by positivity), Complex.real_smul]
  rw [h1, cpow_pos_eq hs, cpow_pos_eq hc,
    cpow_pos_eq (by positivity), cpow_pos_eq (by positivity), Real.log_pow, Real.log_pow]
  rw [show ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) =
    2 * cexp (Real.log (Real.sin θ)) * cexp (Real.log (Real.cos θ)) by
      rw [← ofReal_exp, ← ofReal_exp, Real.exp_log hs, Real.exp_log hc]; push_cast; ring]
  rw [show (1 : ℂ) / 2 * (2 * cexp (Real.log (Real.sin θ)) * cexp (Real.log (Real.cos θ)) *
      (cexp ((a - 1) * ((2 : ℕ) * Real.log (Real.sin θ) : ℝ)) *
        cexp ((b - 1) * ((2 : ℕ) * Real.log (Real.cos θ) : ℝ)))) =
      cexp (Real.log (Real.sin θ) + (a - 1) * ((2 : ℕ) * Real.log (Real.sin θ) : ℝ)) *
      cexp (Real.log (Real.cos θ) + (b - 1) * ((2 : ℕ) * Real.log (Real.cos θ) : ℝ)) by
    rw [Complex.exp_add, Complex.exp_add]; ring]
  congr 2 <;> push_cast <;> ring

/-! ### 5.12.3 -/

theorem div_one_sub_image : (fun u : ℝ => u / (1 - u)) '' Ioo 0 1 = Ioi 0 := by
  apply Subset.antisymm
  · rintro _ ⟨u, ⟨h0, h1⟩, rfl⟩
    exact div_pos h0 (by linarith)
  · intro t ht
    have ht' : 0 < t := ht
    refine ⟨t / (1 + t), ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩, ?_⟩
    have : (1 : ℝ) + t ≠ 0 := by linarith
    field_simp
    ring

theorem div_one_sub_injOn : InjOn (fun u : ℝ => u / (1 - u)) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have hy1 : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
  simp only at hxy
  rw [div_eq_div_iff hx1 hy1] at hxy
  linarith

theorem hasDerivWithinAt_div_one_sub {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (fun u : ℝ => u / (1 - u)) (1 / (1 - u) ^ 2) (Ioo 0 1) u := by
  have h1 : (1 : ℝ) - u ≠ 0 := by linarith [hu.2]
  have := (hasDerivAt_id' u).div ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id' u)) h1
  refine HasDerivAt.hasDerivWithinAt ?_
  convert this using 1
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- The substitution `t = u/(1 − u)` turns 5.12.3's integrand into Euler's. -/
theorem beta_subst_div_one_sub (a b : ℂ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |1 / (1 - u) ^ 2| • (((u / (1 - u) : ℝ) : ℂ) ^ (a - 1) /
      (1 + ((u / (1 - u) : ℝ) : ℂ)) ^ (a + b)) = (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) := by
  have h0 : 0 < u := hu.1
  have h1 : 0 < 1 - u := by linarith [hu.2]
  have h2 : (1 : ℂ) + ((u / (1 - u) : ℝ) : ℂ) = (((1 - u)⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp [show (1 : ℂ) - u ≠ 0 from by exact_mod_cast h1.ne']
    ring
  rw [abs_of_pos (by positivity), Complex.real_smul]
  rw [h2, cpow_pos_eq (div_pos h0 h1), cpow_pos_eq (by positivity),
    cpow_pos_eq h0, show (1 : ℂ) - u = ((1 - u : ℝ) : ℂ) by push_cast; ring, cpow_pos_eq h1,
    Real.log_div h0.ne' h1.ne', Real.log_inv, ← Complex.exp_sub]
  rw [show ((1 / (1 - u) ^ 2 : ℝ) : ℂ) = cexp (-2 * Real.log (1 - u)) by
    rw [show (-2 : ℂ) * Real.log (1 - u) = ((-(2 * Real.log (1 - u)) : ℝ) : ℂ) by
        push_cast; ring, ← ofReal_exp, Real.exp_neg,
      show 2 * Real.log (1 - u) = Real.log ((1 - u) ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    push_cast; ring]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrableOn_beta_Ioi {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b)) (Ioi 0) := by
  rw [← div_one_sub_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u hu => hasDerivWithinAt_div_one_sub hu) div_one_sub_injOn]
  exact (integrableOn_beta ha hb).congr_fun (fun u hu => (beta_subst_div_one_sub a b hu).symm)
    measurableSet_Ioo

/-- **DLMF 5.12.3**: `∫₀^∞ t^{a−1}/(1 + t)^{a+b} dt = B(a, b)`, `ℜa, ℜb > 0`. -/
theorem dlmf_5_12_3 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b) = dlmfBeta a b := by
  rw [← div_one_sub_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => hasDerivWithinAt_div_one_sub hu) div_one_sub_injOn, ← integral_Ioo_beta ha hb]
  exact setIntegral_congr_fun measurableSet_Ioo fun u hu => beta_subst_div_one_sub a b hu

/-! ### 5.12.7 -/

theorem exp_two_mul_image : (fun t : ℝ => Real.exp (2 * t)) '' univ = Ioi 0 := by
  apply Subset.antisymm
  · rintro _ ⟨t, -, rfl⟩
    exact Real.exp_pos _
  · intro s hs
    refine ⟨Real.log s / 2, mem_univ _, ?_⟩
    simp only
    rw [show 2 * (Real.log s / 2) = Real.log s by ring, Real.exp_log hs]

theorem exp_two_mul_injOn : InjOn (fun t : ℝ => Real.exp (2 * t)) univ := fun x _ y _ h => by
  have := Real.exp_injective h
  linarith

theorem hasDerivWithinAt_exp_two_mul (t : ℝ) :
    HasDerivWithinAt (fun t : ℝ => Real.exp (2 * t)) (2 * Real.exp (2 * t)) univ t := by
  have := ((hasDerivAt_id' t).const_mul 2).exp
  refine HasDerivAt.hasDerivWithinAt ?_
  convert this using 1
  ring

theorem log_cosh_eq (t : ℝ) :
    Real.log (Real.cosh t) = -t + Real.log (1 + Real.exp (2 * t)) - Real.log 2 := by
  have h : Real.cosh t = Real.exp (-t) * (1 + Real.exp (2 * t)) / 2 := by
    rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add]
    ring_nf
  rw [h, Real.log_div (by positivity) two_ne_zero, Real.log_mul (by positivity) (by positivity),
    Real.log_exp]

/-- `e^{2bt}/cosh^{2a}t` is `4^a/2` times the substituted 5.12.3 integrand. -/
theorem cosh_subst (a b : ℂ) (t : ℝ) :
    cexp (2 * b * t) / (Real.cosh t : ℂ) ^ (2 * a) = (4 : ℂ) ^ a / 2 *
      (|2 * Real.exp (2 * t)| • (((Real.exp (2 * t) : ℝ) : ℂ) ^ (a + b - 1) /
        (1 + ((Real.exp (2 * t) : ℝ) : ℂ)) ^ (a + b + (a - b)))) := by
  have h4 : (4 : ℂ) ^ a / 2 = cexp (a * (2 * Real.log 2) - Real.log 2) := by
    rw [Complex.exp_sub, ← ofReal_exp, Real.exp_log two_pos,
      show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, cpow_pos_eq (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring_nf
  rw [h4, abs_of_pos (by positivity), Complex.real_smul, cpow_pos_eq (Real.cosh_pos t),
    cpow_pos_eq (Real.exp_pos _), Real.log_exp, log_cosh_eq,
    show (1 : ℂ) + ((Real.exp (2 * t) : ℝ) : ℂ) = ((1 + Real.exp (2 * t) : ℝ) : ℂ) by
      push_cast; ring,
    cpow_pos_eq (by positivity)]
  rw [show (((2 * Real.exp (2 * t)) : ℝ) : ℂ) = cexp (Real.log 2 + 2 * t) by
    rw [Complex.exp_add, ← ofReal_exp, Real.exp_log two_pos, ← ofReal_ofNat, ← ofReal_mul,
      ← ofReal_exp]; push_cast; ring]
  simp only [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **DLMF 5.12.7**: `∫₀^∞ cosh(2bt)/cosh^{2a}t dt = 4^{a−1}B(a + b, a − b)`, `ℜa > |ℜb|`. -/
theorem dlmf_5_12_7 {a b : ℂ} (hab : |b.re| < a.re) :
    ∫ t in Ioi (0 : ℝ), Complex.cosh (2 * b * t) / (Real.cosh t : ℂ) ^ (2 * a) =
      (4 : ℂ) ^ (a - 1) * dlmfBeta (a + b) (a - b) := by
  have h1 : 0 < (a + b).re := by rw [add_re]; linarith [neg_abs_le b.re]
  have h2 : 0 < (a - b).re := by rw [sub_re]; linarith [le_abs_self b.re]
  set E : ℝ → ℂ := fun t => cexp (2 * b * t) / (Real.cosh t : ℂ) ^ (2 * a) with hE
  set G : ℝ → ℂ := fun s => (s : ℂ) ^ (a + b - 1) / (1 + (s : ℂ)) ^ (a + b + (a - b))
  have hEq : E = fun t => (4 : ℂ) ^ a / 2 *
      (|2 * Real.exp (2 * t)| • G (Real.exp (2 * t))) := funext fun t => cosh_subst a b t
  have hGi : IntegrableOn G (Ioi 0) := integrableOn_beta_Ioi h1 h2
  rw [← exp_two_mul_image, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => hasDerivWithinAt_exp_two_mul t) exp_two_mul_injOn] at hGi
  have hEi : Integrable E := by
    rw [hEq]
    exact (integrableOn_univ.mp hGi).const_mul _
  have hEall : ∫ t, E t = (4 : ℂ) ^ a / 2 * dlmfBeta (a + b) (a - b) := by
    rw [hEq, integral_const_mul, ← setIntegral_univ, ← integral_image_eq_integral_abs_deriv_smul
      MeasurableSet.univ (fun t _ => hasDerivWithinAt_exp_two_mul t) exp_two_mul_injOn,
      exp_two_mul_image, dlmf_5_12_3 h1 h2]
  have hcosh : ∀ t : ℝ, Complex.cosh (2 * b * t) / (Real.cosh t : ℂ) ^ (2 * a) =
      (E t + E (-t)) / 2 := fun t => by
    simp only [hE, Real.cosh_neg, Complex.cosh, ofReal_neg]
    ring_nf
  simp_rw [hcosh]
  rw [integral_div, integral_add hEi.integrableOn (hEi.comp_neg).integrableOn,
    integral_comp_neg_Ioi, neg_zero, add_comm,
    intervalIntegral.integral_Iic_add_Ioi hEi.integrableOn
    hEi.integrableOn, hEall, cpow_sub _ _ (by norm_num), cpow_one]
  ring

/-! ### 5.12.4 -/

/-- The Möbius substitution `t = xu/(1 + x − u)`, which maps `(0, 1)` onto itself. -/
noncomputable def betaMobius (x u : ℝ) : ℝ := x * u / (1 + x - u)

theorem betaMobius_mem {x : ℝ} (hx : 0 < x) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaMobius x u ∈ Ioo (0 : ℝ) 1 := by
  have hD : 0 < 1 + x - u := by linarith [hu.2]
  refine ⟨div_pos (mul_pos hx hu.1) hD, (div_lt_one hD).mpr ?_⟩
  nlinarith [hu.2]

theorem betaMobius_image {x : ℝ} (hx : 0 < x) : betaMobius x '' Ioo 0 1 = Ioo 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact betaMobius_mem hx hu
  · intro t ht
    have h1 : 0 < x + t := by linarith [ht.1]
    refine ⟨t * (1 + x) / (x + t), ⟨by have := ht.1; positivity, ?_⟩, ?_⟩
    · rw [div_lt_one h1]; nlinarith [ht.2]
    · simp only [betaMobius]
      have h2 : 1 + x - t * (1 + x) / (x + t) = x * (1 + x) / (x + t) := by
        field_simp; ring
      rw [h2]
      field_simp

theorem betaMobius_injOn {x : ℝ} (hx : 0 < x) : InjOn (betaMobius x) (Ioo 0 1) := by
  intro u hu v hv h
  have hDu : 1 + x - u ≠ 0 := by linarith [hu.2]
  have hDv : 1 + x - v ≠ 0 := by linarith [hv.2]
  simp only [betaMobius] at h
  rw [div_eq_div_iff hDu hDv] at h
  have : x * (1 + x) * (u - v) = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · nlinarith
  · linarith

theorem hasDerivWithinAt_betaMobius {x : ℝ} {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) :
    HasDerivWithinAt (betaMobius x) (x * (1 + x) / (1 + x - u) ^ 2) (Ioo 0 1) u := by
  have hD : 1 + x - u ≠ 0 := by linarith [hu.2]
  have := ((hasDerivAt_id' u).const_mul x).div
    ((hasDerivAt_const u (1 + x)).sub (hasDerivAt_id' u)) hD
  refine HasDerivAt.hasDerivWithinAt ?_
  convert this using 1
  · funext y; simp [betaMobius]
  · simp only [Pi.sub_apply]
    field_simp
    ring

/-- The substitution `t = xu/(1 + x − u)` in 5.12.4. -/
theorem beta_subst_betaMobius (a b : ℂ) {x : ℝ} (hx : 0 < x) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |x * (1 + x) / (1 + x - u) ^ 2| • ((betaMobius x u : ℂ) ^ (a - 1) *
      (1 - (betaMobius x u : ℂ)) ^ (b - 1) / ((betaMobius x u : ℂ) + x) ^ (a + b)) =
      (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
        ((1 + (x : ℂ)) ^ (-a) * (x : ℂ) ^ (-b)) := by
  have h0 : 0 < u := hu.1
  have h1 : 0 < 1 - u := by linarith [hu.2]
  have hD : 0 < 1 + x - u := by linarith [hu.2]
  have hx1 : 0 < 1 + x := by linarith
  have e1 : 1 - betaMobius x u = (1 + x) * (1 - u) / (1 + x - u) := by
    simp only [betaMobius]; field_simp; ring
  have e2 : betaMobius x u + x = x * (1 + x) / (1 + x - u) := by
    simp only [betaMobius]; field_simp; ring
  have hm := (betaMobius_mem hx hu).1
  rw [abs_of_pos (by positivity), Complex.real_smul,
    show (1 : ℂ) - (betaMobius x u : ℂ) = ((1 - betaMobius x u : ℝ) : ℂ) by push_cast; ring,
    show (betaMobius x u : ℂ) + x = ((betaMobius x u + x : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - u = ((1 - u : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring,
    cpow_pos_eq hm, cpow_pos_eq (by rw [e1]; positivity), cpow_pos_eq (by positivity),
    cpow_pos_eq h0, cpow_pos_eq h1, cpow_pos_eq hx1, cpow_pos_eq hx, e1, e2]
  simp only [betaMobius]
  rw [show ((x * (1 + x) / (1 + x - u) ^ 2 : ℝ) : ℂ) =
      cexp ((Real.log x + Real.log (1 + x) - 2 * Real.log (1 + x - u) : ℝ)) by
    rw [← ofReal_exp, Real.exp_sub, Real.exp_add, Real.exp_log hx, Real.exp_log hx1,
      show 2 * Real.log (1 + x - u) = Real.log ((1 + x - u) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]]
  rw [Real.log_div (by positivity) hD.ne', Real.log_div (by positivity) hD.ne',
    Real.log_div (by positivity) hD.ne', Real.log_mul hx.ne' h0.ne',
    Real.log_mul hx1.ne' h1.ne', Real.log_mul hx.ne' hx1.ne']
  simp only [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- 5.12.4 for `z = x > 0`. -/
theorem dlmf_5_12_4_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + x) ^ (a + b) =
      dlmfBeta a b * (1 + (x : ℂ)) ^ (-a) * (x : ℂ) ^ (-b) := by
  rw [← betaMobius_image hx, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => hasDerivWithinAt_betaMobius hu hx) (betaMobius_injOn hx), ← integral_Ioo_beta ha hb,
    mul_assoc, ← integral_mul_const]
  exact setIntegral_congr_fun measurableSet_Ioo fun u hu => beta_subst_betaMobius a b hx hu

/-- Near a point of the slit plane, `t + z` stays uniformly inside it for `t ≥ 0`. -/
theorem exists_slit_shift {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ ρ > 0, ∀ z ∈ Metric.closedBall z₀ (ρ / 2), ∀ t : ℝ, 0 ≤ t →
      (t : ℂ) + z ∈ slitPlane ∧ ρ / 2 ≤ ‖(t : ℂ) + z‖ := by
  rw [mem_slitPlane_iff] at hz₀
  refine ⟨max z₀.re |z₀.im|, ?_, fun z hz t ht => ?_⟩
  · rcases hz₀ with h | h
    · exact lt_max_of_lt_left h
    · exact lt_max_of_lt_right (abs_pos.mpr h)
  have hd : ‖z - z₀‖ ≤ max z₀.re |z₀.im| / 2 := by
    rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz
  have hre : |z.re - z₀.re| ≤ max z₀.re |z₀.im| / 2 :=
    (by rw [← sub_re]; exact abs_re_le_norm _ : |z.re - z₀.re| ≤ ‖z - z₀‖).trans hd
  have him : |z.im - z₀.im| ≤ max z₀.re |z₀.im| / 2 :=
    (by rw [← sub_im]; exact abs_im_le_norm _ : |z.im - z₀.im| ≤ ‖z - z₀‖).trans hd
  rcases le_total |z₀.im| z₀.re with h | h
  · rw [max_eq_left h] at hre ⊢
    have hp : 0 < z₀.re := by
      rcases hz₀ with h' | h'
      · exact h'
      · exact (abs_pos.mpr h').trans_le h
    have : z₀.re / 2 ≤ ((t : ℂ) + z).re := by
      simp only [add_re, ofReal_re]
      linarith [(abs_le.mp hre).1]
    exact ⟨mem_slitPlane_iff.mpr (Or.inl (by linarith)), this.trans (re_le_norm _)⟩
  · rw [max_eq_right h] at him ⊢
    have hp : 0 < |z₀.im| := by
      rcases hz₀ with h' | h'
      · exact h'.trans_le h
      · exact abs_pos.mpr h'
    have : |z₀.im| / 2 ≤ |((t : ℂ) + z).im| := by
      simp only [add_im, ofReal_im, zero_add]
      have := abs_sub_abs_le_abs_sub z₀.im z.im
      rw [abs_sub_comm] at this
      linarith
    refine ⟨mem_slitPlane_iff.mpr (Or.inr fun h0 => ?_), this.trans (abs_im_le_norm _)⟩
    rw [h0, abs_zero] at this
    linarith

theorem differentiableOn_dlmf_5_12_4 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t in Ioo (0 : ℝ) 1,
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + z) ^ (a + b)) slitPlane := by
  set w : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)
  have hw := integrableOn_beta ha hb
  set c := a + b
  refine differentiableOn_integral_of_holo (F := fun z t => w t / ((t : ℂ) + z) ^ c)
    (F' := fun z t => -(w t * (c * ((t : ℂ) + z) ^ (c - 1))) / (((t : ℂ) + z) ^ c) ^ 2)
    (fun z _ => (by fun_prop : Measurable fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)
      / ((t : ℂ) + z) ^ c).aestronglyMeasurable)
    (fun z _ => (by fun_prop : Measurable fun t : ℝ => -((t : ℂ) ^ (a - 1) *
      (1 - (t : ℂ)) ^ (b - 1) * (c * ((t : ℂ) + z) ^ (c - 1))) /
      (((t : ℂ) + z) ^ c) ^ 2).aestronglyMeasurable)
    fun z₀ hz₀ => ?_
  obtain ⟨ρ, hρ, hsh⟩ := exists_slit_shift hz₀
  refine ⟨ρ / 4, by positivity, fun z hz => ?_, fun t => ‖w t‖ * ((ρ / 2) ^ (-c.re) *
    Real.exp (π * |c.im|)), hw.norm.mul_const _, ?_, ?_⟩
  · have := (hsh z (Metric.closedBall_subset_closedBall (by linarith)
      (Metric.ball_subset_closedBall hz)) 0 le_rfl).1
    simpa using this
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht z hz => ?_
    have hz' : z ∈ Metric.closedBall z₀ (ρ / 2) := by
      rw [show 2 * (ρ / 4) = ρ / 2 by ring] at hz; exact hz
    obtain ⟨hs, hn⟩ := hsh z hz' t ht.1.le
    have hne : ((t : ℂ) + z) ^ c ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h => slitPlane_ne_zero hs h.1
    have hd := ((hasDerivAt_id z).const_add (t : ℂ)).cpow_const (c := c) hs
    simp only [id, mul_one] at hd
    convert (hasDerivAt_const z (w t)).fun_div hd hne using 2
    ring
  · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht z hz => ?_
    have hz' : z ∈ Metric.closedBall z₀ (ρ / 2) := by
      rw [show 2 * (ρ / 4) = ρ / 2 by ring] at hz; exact hz
    obtain ⟨hs, hn⟩ := hsh z hz' t ht.1.le
    have h0 : (t : ℂ) + z ≠ 0 := slitPlane_ne_zero hs
    have hpos : 0 < ρ / 2 := by positivity
    have hcre : 0 < c.re := by simp only [c, add_re]; linarith
    have hpow : (ρ / 2) ^ c.re ≤ ‖(t : ℂ) + z‖ ^ c.re := Real.rpow_le_rpow hpos.le hn hcre.le
    have hexp : Real.exp (arg ((t : ℂ) + z) * c.im) ≤ Real.exp (π * |c.im|) := by
      refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_arg_le_pi _) (abs_nonneg _)
    have hL : (ρ / 2) ^ c.re / Real.exp (π * |c.im|) ≤ ‖((t : ℂ) + z) ^ c‖ := by
      rw [norm_cpow_of_ne_zero h0]
      exact div_le_div₀ (by positivity) hpow (Real.exp_pos _) hexp
    have hLpos : 0 < (ρ / 2) ^ c.re / Real.exp (π * |c.im|) := by positivity
    calc ‖w t / ((t : ℂ) + z) ^ c‖ = ‖w t‖ * ‖((t : ℂ) + z) ^ c‖⁻¹ := by
          rw [norm_div, div_eq_mul_inv]
      _ ≤ ‖w t‖ * ((ρ / 2) ^ c.re / Real.exp (π * |c.im|))⁻¹ := by gcongr
      _ = ‖w t‖ * ((ρ / 2) ^ (-c.re) * Real.exp (π * |c.im|)) := by
          rw [inv_div, Real.rpow_neg hpos.le]; ring

/-- **DLMF 5.12.4**: `∫₀¹ t^{a−1}(1 − t)^{b−1}/(t + z)^{a+b} dt = B(a, b)(1 + z)^{−a}z^{−b}`,
`|ph z| < π`, `ℜa, ℜb > 0`. -/
theorem dlmf_5_12_4 {a b z : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hz0 : z ≠ 0)
    (hz : |arg z| < π) :
    ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + z) ^ (a + b) =
      dlmfBeta a b * (1 + z) ^ (-a) * z ^ (-b) := by
  have hzs : z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at hz; exact lt_irrefl _ hz, hz0⟩
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hg : DifferentiableOn ℂ (fun z : ℂ => dlmfBeta a b * (1 + z) ^ (-a) * z ^ (-b))
      slitPlane := fun z hz => by
    have h1 : 1 + z ∈ slitPlane := by
      have := (exists_slit_shift hz).choose_spec.2 z
        (Metric.mem_closedBall_self (by have := (exists_slit_shift hz).choose_spec.1; positivity))
        1 zero_le_one
      simpa using this.1
    exact ((((differentiableAt_const _).add differentiableAt_id).cpow
      (differentiableAt_const _) h1).const_mul _ |>.mul
      (differentiableAt_id.cpow (differentiableAt_const _) hz)).differentiableWithinAt
  refine eqOn_of_eq_on_pos_reals ((differentiableOn_dlmf_5_12_4 ha hb).analyticOnNhd
    isOpen_slitPlane) (hg.analyticOnNhd isOpen_slitPlane)
    (StarConvex.isPathConnected starConvex_one_slitPlane (by simp)).isConnected.isPreconnected
    isOpen_slitPlane (by simp [mem_slitPlane_iff]) (fun x hx _ => dlmf_5_12_4_pos ha hb hx) hzs

end Azurite.DLMF
