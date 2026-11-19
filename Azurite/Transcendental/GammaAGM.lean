/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.EllipticIntegrals
import Azurite.DLMF.Chapter5.Section12

/-!
# `Γ(1/4)` and `Γ(1/3)` by the arithmetic–geometric mean

  `Γ(1/4)² = 2π √(2π) / AGM(1, √2)`                               (`gamma_one_quarter_sq`),
  `Γ(1/3)³ = 2 · 2^(1/3) π² / AGM(√((√3 + 3/2)/2), √√3)`          (`gamma_one_third_cube`).

Both come from one substitution in the Beta integral `B(1/2, b) = ∫₀^∞ t^(−1/2) (1 + t)^(−1/2−b) dt`
(DLMF 5.12.3): `t = (1 + s²)ⁿ − 1` with `n = 2`, `b = 1/4` and `n = 3`, `b = 1/6` removes the
fractional powers,

  `B(1/2, 1/4) = 4 ∫₀^∞ ds/√((s² + 1)(s² + 2))`,   `B(1/2, 1/6) = 6 ∫₀^∞ ds/√(s⁴ + 3s² + 3)`.

The first integral is Gauss's `J(1, √2) = π/(2 AGM(1, √2))`.  The quartic of the second has no
real factorization `(s² + a²)(s² + b²)` — `a` and `b` are complex conjugates — but the Landen
substitution `u = (s − d/s)/2` only involves `ab = d` and `(a + b)²/4 = (d + c)/2`, which are
real: `∫₀^∞ ds/√(s⁴ + 2cs² + d²) = J(√((d + c)/2), √d)` for `d > 0`, `d + c > 0`
(`integral_quarticKernel`), one AGM step with a real result.

The Gamma quotients are reduced by the reflection and duplication formulas:
`Γ(3/4) = √2 π/Γ(1/4)`; `Γ(2/3) = 2π/(√3 Γ(1/3))` and `Γ(1/6) Γ(2/3) = 2^(2/3) √π Γ(1/3)`.
-/

namespace Azurite

open Real MeasureTheory Set BZ

/-! ### The quartic integral -/

/-- The integrand `1/√(t⁴ + 2ct² + d²)`. -/
noncomputable def quarticKernel (c d t : ℝ) : ℝ := (√(t ^ 4 + 2 * c * t ^ 2 + d ^ 2))⁻¹

theorem quartic_pos {c d t : ℝ} (hcd : 0 < d + c) (ht : 0 < t) :
    0 < t ^ 4 + 2 * c * t ^ 2 + d ^ 2 := by
  nlinarith [sq_nonneg (t ^ 2 - d), mul_pos hcd (pow_pos ht 2)]

/-- The pointwise identity of the Landen step for the quartic. -/
theorem landen_quartic {c d t : ℝ} (hd : 0 < d) (hcd : 0 < d + c) (ht : 0 < t) :
    |(1 + √d * √d * (t ^ 2)⁻¹) / 2|
        * agmKernel (√((d + c) / 2)) (√d) (landen (√d) (√d) t)
      = 2 * quarticKernel c d t := by
  unfold agmKernel landen quarticKernel
  have hdd : √d * √d = d := Real.mul_self_sqrt hd.le
  have hd2 : √d ^ 2 = d := Real.sq_sqrt hd.le
  have hA2 : √((d + c) / 2) ^ 2 = (d + c) / 2 := Real.sq_sqrt (by positivity)
  have hQ := quartic_pos hcd ht
  have hR : 0 ≤ (t ^ 2 + d) / (4 * t ^ 2) := by positivity
  have hprod : (((t - √d * √d * t⁻¹) / 2) ^ 2 + √((d + c) / 2) ^ 2)
      * (((t - √d * √d * t⁻¹) / 2) ^ 2 + √d ^ 2)
      = (t ^ 4 + 2 * c * t ^ 2 + d ^ 2) * ((t ^ 2 + d) / (4 * t ^ 2)) ^ 2 := by
    rw [hdd, hd2, hA2]
    field_simp
    ring
  rw [hprod, Real.sqrt_mul hQ.le, Real.sqrt_sq hR, hdd, abs_of_pos (by positivity)]
  have hs : 0 < √(t ^ 4 + 2 * c * t ^ 2 + d ^ 2) := Real.sqrt_pos.mpr hQ
  have hq : 0 < t ^ 2 + d := by positivity
  field_simp
  ring

/-- **The Landen step with complex-conjugate parameters**:
`∫₀^∞ dt/√(t⁴ + 2ct² + d²) = J(√((d + c)/2), √d)`. -/
theorem integral_quarticKernel {c d : ℝ} (hd : 0 < d) (hcd : 0 < d + c) :
    ∫ t in Ioi (0 : ℝ), quarticKernel c d t = agmIntegral (√((d + c) / 2)) (√d) := by
  have hs : 0 < √d := Real.sqrt_pos.mpr hd
  have ha1 : 0 < √((d + c) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := landen (√d) (√d)) (f' := fun t => (1 + √d * √d * (t ^ 2)⁻¹) / 2) measurableSet_Ioi
    (fun t ht => (hasDerivAt_landen (√d) (√d) (ne_of_gt ht)).hasDerivWithinAt)
    (landen_injOn hs hs) (agmKernel (√((d + c) / 2)) (√d))
  rw [landen_image hs hs, Measure.restrict_univ, integral_agmKernel ha1 hs] at hcov
  have h2 : ∫ t in Ioi (0 : ℝ), |(1 + √d * √d * (t ^ 2)⁻¹) / 2|
      • agmKernel (√((d + c) / 2)) (√d) (landen (√d) (√d) t)
      = ∫ t in Ioi (0 : ℝ), 2 * quarticKernel c d t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [smul_eq_mul, landen_quartic hd hcd ht]
  rw [h2, MeasureTheory.integral_const_mul] at hcov
  linarith

/-! ### The Beta integral `B(1/2, b)` on the real line -/

/-- The integrand of `B(1/2, b)` in the form of DLMF 5.12.3. -/
noncomputable def betaHalfKernel (b t : ℝ) : ℝ := t ^ (-(1 / 2) : ℝ) / (1 + t) ^ (1 / 2 + b)

/-- DLMF 5.12.3 for the real parameters `1/2`, `b`. -/
theorem integral_betaHalfKernel {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), betaHalfKernel b t
      = Real.Gamma (1 / 2) * Real.Gamma b / Real.Gamma (1 / 2 + b) := by
  have h := DLMF.dlmf_5_12_3 (a := ((1 / 2 : ℝ) : ℂ)) (b := (b : ℂ))
    (by rw [Complex.ofReal_re]; norm_num) (by rw [Complex.ofReal_re]; exact hb)
  have hcongr : ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - 1) / (1 + (t : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) + (b : ℂ))
      = ∫ t in Ioi (0 : ℝ), ((betaHalfKernel b t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      have e1 : ((1 / 2 : ℝ) : ℂ) - 1 = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
      have e2 : 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) := by push_cast; rfl
      have e3 : ((1 / 2 : ℝ) : ℂ) + (b : ℂ) = ((1 / 2 + b : ℝ) : ℂ) := by push_cast; rfl
      simp only [betaHalfKernel]
      rw [e1, e2, e3, ← Complex.ofReal_cpow ht0.le, ← Complex.ofReal_cpow (by positivity),
        ← Complex.ofReal_div]
  rw [hcongr, integral_complex_ofReal] at h
  unfold DLMF.dlmfBeta at h
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_div] at h
  exact Complex.ofReal_injective h

/-! ### The substitution `t = (1 + s²)ⁿ − 1` -/

/-- The map `s ↦ (1 + s²)ⁿ − 1`. -/
noncomputable def powSubst (n : ℕ) (s : ℝ) : ℝ := (1 + s ^ 2) ^ n - 1

theorem hasDerivAt_powSubst (n : ℕ) (s : ℝ) :
    HasDerivAt (powSubst n) (n * (1 + s ^ 2) ^ (n - 1) * (2 * s)) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * s) s := by
    have := (hasDerivAt_pow 2 s).const_add 1
    simpa using this
  have := (h1.pow n).sub_const 1
  exact this

theorem powSubst_injOn {n : ℕ} (hn : n ≠ 0) : InjOn (powSubst n) (Ioi 0) := by
  have hmono : StrictMonoOn (powSubst n) (Ioi 0) := fun s hs t _ hst => by
    have hs0 : (0 : ℝ) < s := hs
    unfold powSubst
    have : 1 + s ^ 2 < 1 + t ^ 2 := by nlinarith
    have := pow_lt_pow_left₀ this (by positivity) hn
    linarith
  exact hmono.injOn

theorem powSubst_image {n : ℕ} (hn : n ≠ 0) : powSubst n '' Ioi 0 = Ioi 0 := by
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs0 : (0 : ℝ) < s := hs
    have : (1 : ℝ) < (1 + s ^ 2) ^ n := one_lt_pow₀ (by nlinarith) hn
    simp only [mem_Ioi, powSubst]
    linarith
  · intro hw
    have hw0 : (0 : ℝ) < w := hw
    have hr : (1 : ℝ) < (1 + w) ^ ((n : ℝ)⁻¹) :=
      Real.one_lt_rpow (by linarith) (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn))
    refine ⟨√((1 + w) ^ ((n : ℝ)⁻¹) - 1), Real.sqrt_pos.mpr (by linarith), ?_⟩
    unfold powSubst
    rw [Real.sq_sqrt (by linarith), add_sub_cancel, Real.rpow_inv_natCast_pow (by linarith) hn]
    ring

/-- The substitution `t = (1 + s²)ⁿ − 1` in an integral over `(0, ∞)`. -/
theorem integral_comp_powSubst {n : ℕ} (hn : n ≠ 0) (F : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), F t
      = ∫ s in Ioi (0 : ℝ), |n * (1 + s ^ 2) ^ (n - 1) * (2 * s)| * F (powSubst n s) := by
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := powSubst n) (f' := fun s => n * (1 + s ^ 2) ^ (n - 1) * (2 * s)) measurableSet_Ioi
    (fun s _ => (hasDerivAt_powSubst n s).hasDerivWithinAt) (powSubst_injOn hn) F
  rw [powSubst_image hn] at hcov
  simpa only [smul_eq_mul] using hcov

/-- `B(1/2, 1/4) = 4 J(1, √2)`. -/
theorem betaHalfKernel_quarter {s : ℝ} (hs : 0 < s) :
    |(2 : ℕ) * (1 + s ^ 2) ^ (2 - 1) * (2 * s)| * betaHalfKernel (1 / 4) (powSubst 2 s)
      = 4 * agmKernel 1 (√2) s := by
  unfold betaHalfKernel powSubst agmKernel
  have h2 : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hq : 0 < s ^ 2 + 2 := by positivity
  have hp : 0 < 1 + s ^ 2 := by positivity
  have e1 : (1 + s ^ 2) ^ 2 - 1 = s ^ 2 * (s ^ 2 + 2) := by ring
  have e2 : 1 + ((1 + s ^ 2) ^ 2 - 1) = (1 + s ^ 2) ^ 2 := by ring
  have e3 : ((1 + s ^ 2) ^ 2) ^ ((1 / 2 + 1 / 4 : ℝ)) = (1 + s ^ 2) * √(1 + s ^ 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, Real.sqrt_eq_rpow,
      ← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  have e4 : (s ^ 2 * (s ^ 2 + 2)) ^ (-(1 / 2) : ℝ) = (s * √(s ^ 2 + 2))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hs.le]
  have e5 : √((s ^ 2 + 1 ^ 2) * (s ^ 2 + √2 ^ 2)) = √(1 + s ^ 2) * √(s ^ 2 + 2) := by
    rw [h2, ← Real.sqrt_mul hp.le]
    congr 1
    ring
  rw [e2, e1, e3, e4, e5, abs_of_pos (by positivity)]
  have h1 : 0 < √(1 + s ^ 2) := Real.sqrt_pos.mpr hp
  have h3 : 0 < √(s ^ 2 + 2) := Real.sqrt_pos.mpr hq
  field_simp
  ring

/-- `B(1/2, 1/6) = 6 ∫₀^∞ ds/√(s⁴ + 3s² + 3)`. -/
theorem betaHalfKernel_sixth {s : ℝ} (hs : 0 < s) :
    |(3 : ℕ) * (1 + s ^ 2) ^ (3 - 1) * (2 * s)| * betaHalfKernel (1 / 6) (powSubst 3 s)
      = 6 * quarticKernel (3 / 2) (√3) s := by
  unfold betaHalfKernel powSubst quarticKernel
  have h3 : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hq : 0 < s ^ 4 + 3 * s ^ 2 + 3 := by positivity
  have hp : 0 < 1 + s ^ 2 := by positivity
  have e1 : (1 + s ^ 2) ^ 3 - 1 = s ^ 2 * (s ^ 4 + 3 * s ^ 2 + 3) := by ring
  have e2 : 1 + ((1 + s ^ 2) ^ 3 - 1) = (1 + s ^ 2) ^ 3 := by ring
  have e3 : ((1 + s ^ 2) ^ 3) ^ ((1 / 2 + 1 / 6 : ℝ)) = (1 + s ^ 2) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_natCast]
    norm_num
  have e4 : (s ^ 2 * (s ^ 4 + 3 * s ^ 2 + 3)) ^ (-(1 / 2) : ℝ)
      = (s * √(s ^ 4 + 3 * s ^ 2 + 3))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hs.le]
  have e5 : s ^ 4 + 2 * (3 / 2) * s ^ 2 + √3 ^ 2 = s ^ 4 + 3 * s ^ 2 + 3 := by rw [h3]; ring
  rw [e2, e1, e3, e4, e5, abs_of_pos (by positivity)]
  have h1 : 0 < √(s ^ 4 + 3 * s ^ 2 + 3) := Real.sqrt_pos.mpr hq
  field_simp
  ring

/-! ### `Γ(1/4)` -/

/-- **`Γ(1/4)² = 2π √(2π) / AGM(1, √2)`.** -/
theorem gamma_one_quarter_sq :
    Real.Gamma (1 / 4) ^ 2 = 2 * π * √(2 * π) / AGM 1 (√2) := by
  have hs2 : (0 : ℝ) < √2 := by positivity
  have hM : 0 < AGM 1 (√2) := lt_of_lt_of_le (lt_min one_pos hs2) (min_le_AGM one_pos hs2)
  have hB := integral_betaHalfKernel (b := 1 / 4) (by norm_num)
  rw [integral_comp_powSubst (by norm_num : (2 : ℕ) ≠ 0),
    setIntegral_congr_fun measurableSet_Ioi (fun s hs => betaHalfKernel_quarter hs),
    MeasureTheory.integral_const_mul] at hB
  have hJ : ∫ s in Ioi (0 : ℝ), agmKernel 1 (√2) s = π / (2 * AGM 1 (√2)) :=
    agmIntegral_eq_pi_div_AGM one_pos hs2
  rw [hJ, Real.Gamma_one_half_eq, show (1 / 2 + 1 / 4 : ℝ) = 1 - 1 / 4 by norm_num] at hB
  have hg : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hh : 0 < Real.Gamma (1 - 1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show π * (1 / 4 : ℝ) = π / 4 by ring, Real.sin_pi_div_four] at hR
  set g := Real.Gamma (1 / 4)
  set h := Real.Gamma (1 - 1 / 4)
  have hπ := Real.pi_pos
  have hsπ : 0 < √π := Real.sqrt_pos.mpr hπ
  have hsπ2 : √π * √π = π := Real.mul_self_sqrt hπ.le
  have h22 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [Real.sqrt_mul (by norm_num)]
  -- `√π g / h = 2π/M`, `g h = 2π/√2`
  have h1 : √π * g * AGM 1 (√2) = 2 * π * h := by
    field_simp at hB
    linarith
  have h2 : g * h * √2 = 2 * π := by
    field_simp at hR
    linarith
  rw [eq_div_iff hM.ne']
  have key : (g ^ 2 * AGM 1 (√2)) * (√π * h * √2) = (2 * π * (√2 * √π)) * (√π * h * √2) := by
    calc (g ^ 2 * AGM 1 (√2)) * (√π * h * √2)
        = (√π * g * AGM 1 (√2)) * (g * h * √2) := by ring
      _ = (2 * π * h) * (2 * π) := by rw [h1, h2]
      _ = 2 * π * h * (π * (√2 * √2)) := by rw [h22]; ring
      _ = 2 * π * h * (√π * √π * (√2 * √2)) := by rw [hsπ2]
      _ = (2 * π * (√2 * √π)) * (√π * h * √2) := by ring
  exact mul_right_cancel₀ (by positivity) key

/-! ### `Γ(1/3)` -/

/-- **`Γ(1/3)³ = 2 · 2^(1/3) π² / AGM(√((√3 + 3/2)/2), √√3)`**, with any `c > 0`, `c³ = 2`
for the cube root of `2`. -/
theorem gamma_one_third_cube {c : ℝ} (hc0 : 0 < c) (hc : c ^ 3 = 2) :
    Real.Gamma (1 / 3) ^ 3 = 2 * c * π ^ 2 / AGM (√((√3 + 3 / 2) / 2)) (√√3) := by
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hA : 0 < √((√3 + 3 / 2) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hBp : 0 < √√3 := Real.sqrt_pos.mpr hs3
  have hM : 0 < AGM (√((√3 + 3 / 2) / 2)) (√√3) :=
    lt_of_lt_of_le (lt_min hA hBp) (min_le_AGM hA hBp)
  have hB := integral_betaHalfKernel (b := 1 / 6) (by norm_num)
  rw [integral_comp_powSubst (by norm_num : (3 : ℕ) ≠ 0),
    setIntegral_congr_fun measurableSet_Ioi (fun s hs => betaHalfKernel_sixth hs),
    MeasureTheory.integral_const_mul, integral_quarticKernel hs3 (by positivity),
    agmIntegral_eq_pi_div_AGM hA hBp, Real.Gamma_one_half_eq] at hB
  -- reflection and duplication
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show π * (1 / 3 : ℝ) = π / 3 by ring, Real.sin_pi_div_three,
    show (1 - 1 / 3 : ℝ) = 1 / 2 + 1 / 6 by norm_num] at hR
  have hD := Real.Gamma_mul_Gamma_add_half (1 / 6)
  rw [show (1 / 6 + 1 / 2 : ℝ) = 1 / 2 + 1 / 6 by norm_num,
    show (2 * (1 / 6) : ℝ) = 1 / 3 by norm_num] at hD
  -- `2^(2/3) = c²`
  have hpow : (2 : ℝ) ^ (1 - 1 / 3 : ℝ) = c ^ 2 := by
    have e : (c ^ 3 : ℝ) ^ (2 / 3 : ℝ) = c ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_natCast]
      norm_num
    rw [hc] at e
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num]
    exact e
  rw [hpow] at hD
  have hg : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hh : 0 < Real.Gamma (1 / 2 + 1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  have hk : 0 < Real.Gamma (1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  set g := Real.Gamma (1 / 3)
  set h := Real.Gamma (1 / 2 + 1 / 6)
  set k := Real.Gamma (1 / 6)
  set M := AGM (√((√3 + 3 / 2) / 2)) (√√3)
  have hπ := Real.pi_pos
  have hsπ : 0 < √π := Real.sqrt_pos.mpr hπ
  have hsπ2 : √π * √π = π := Real.mul_self_sqrt hπ.le
  have h33 : √3 * √3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  -- `√π k M = 3π h`, `g h √3 = 2π`, `k h = g c² √π`
  have h1 : √π * k * M = 3 * π * h := by
    field_simp at hB
    linarith
  have h2 : g * h * √3 = 2 * π := by
    field_simp at hR
    linarith
  rw [eq_div_iff hM.ne']
  -- multiply `h1` by `h`: `π g c² M = 3π h²`, so `g c² M = 3 h²`
  have h4 : g * c ^ 2 * M = 3 * h ^ 2 := by
    have : π * (g * c ^ 2 * M) = π * (3 * h ^ 2) := by
      calc π * (g * c ^ 2 * M) = (√π * √π) * (g * c ^ 2 * M) := by rw [hsπ2]
        _ = √π * (g * c ^ 2 * √π) * M := by ring
        _ = √π * (k * h) * M := by rw [hD]
        _ = (√π * k * M) * h := by ring
        _ = π * (3 * h ^ 2) := by rw [h1]; ring
    exact mul_left_cancel₀ hπ.ne' this
  -- `3 g² h² = 4π²`
  have h5 : 3 * (g * h) ^ 2 = 4 * π ^ 2 := by
    have : (g * h * √3) ^ 2 = (2 * π) ^ 2 := by rw [h2]
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at this
    linarith
  have key : (g ^ 3 * M) * c ^ 2 = (2 * c * π ^ 2) * c ^ 2 := by
    calc (g ^ 3 * M) * c ^ 2 = g ^ 2 * (g * c ^ 2 * M) := by ring
      _ = 3 * (g * h) ^ 2 := by rw [h4]; ring
      _ = 4 * π ^ 2 := h5
      _ = 2 * c ^ 3 * π ^ 2 := by rw [hc]; ring
      _ = (2 * c * π ^ 2) * c ^ 2 := by ring
  exact mul_right_cancel₀ (by positivity) key

end Azurite
