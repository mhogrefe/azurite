/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section14Other
import Azurite.DLMF.Chapter5.Section9Psi
import Azurite.DLMF.Chapter5.Section4

/-!
# DLMF §6.15: sums

Formalizations of <https://dlmf.nist.gov/6.15>.  The sums `∑_{n=1}^∞` are written as `HasSum`
over `n : ℕ` with `n + 1` in place of `n`.

## Main results

* `dlmf_6_15_1`: `∑ Ci(πn) = ½(ln 2 − γ)`.
* `dlmf_6_15_2`: `∑ si(πn)/n = ½π(ln π − 1)`.
* `dlmf_6_15_3`: `∑ (−1)ⁿ Ci(2πn) = 1 − ln 2 − ½γ`.
* `dlmf_6_15_4`: `∑ (−1)ⁿ si(2πn)/n = π(3/2 ln 2 − 1)`.

## Method

At `x = cn` (`c = π, 2π`) the auxiliary-function forms 6.2.19, 6.2.20 reduce `Ci`, `si` to
`∓(±1)ⁿ g(cn)`, `∓(±1)ⁿ f(cn)` (`CiR_nat_mul_pi`, …).  With the Laplace integrals 6.7.13, 6.7.14
for `f`, `g` the sums are integrated termwise (`hasSum_gR`, `hasSum_fR`,
`hasSum_integral_of_summable_integral_norm`), giving `∫_0^∞ u/((u² + 1)(e^{cu} + 1)) du` and
`∫_0^∞ ln(1 + e^{−cu})/(u² + 1) du`.  Splitting `1/(e^x + 1)` and `ln(1 + e^{−x})` and rescaling
turns these into Binet's integrals `B(z)` (5.9.15, for `ψ`) and `A(z)` (5.9.10, for `ln Γ`) at
`z = ½, 1, 2` (`integral_Tg`, `integral_Tf`), evaluated by `ψ(½), ψ(1), ψ(2)` and
`Γ(½) = √π, Γ(1) = Γ(2) = 1` (`binB_half`, …, `binA_two`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Binet's integrals at `z = 1/2, 1, 2` -/

/-- Binet's integral `B(z) = ∫_0^∞ t/((t² + z²)(e^{2πt} − 1)) dt` of 5.9.15 (real `z`). -/
noncomputable def binB (z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t / ((t ^ 2 + z ^ 2) * (Real.exp (2 * π * t) - 1))

/-- Binet's integral `A(z) = ∫_0^∞ ln(1 − e^{−2πt})/(t² + z²) dt` of 5.9.10 (real `z`). -/
noncomputable def binA (z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.log (1 - Real.exp (-(2 * π * t))) / (t ^ 2 + z ^ 2)

/-- 5.9.15 at real `z > 0`: `ψ(z) = ln z − 1/(2z) − 2B(z)`. -/
theorem digamma_ofReal_eq_binB {z : ℝ} (hz : 0 < z) :
    digamma z = ((Real.log z - 1 / (2 * z) - 2 * binB z : ℝ) : ℂ) := by
  have hB : ∫ t in Ioi (0 : ℝ), (t : ℂ) / (((t : ℂ) ^ 2 + (z : ℂ) ^ 2) *
      ((Real.exp (2 * π * t) - 1 : ℝ) : ℂ)) = (binB z : ℂ) := by
    rw [binB, ← integral_complex_ofReal]; push_cast; rfl
  rw [dlmf_5_9_15 (by simpa using hz), hB, ← ofReal_log hz.le]
  push_cast; ring

/-- 5.9.10 at real `z > 0`: `(z/π) A(z) = (z − ½) ln z − z + ½ ln 2π − ln Γ(z)`. -/
theorem binA_spec {z : ℝ} (hz : 0 < z) :
    z / π * binA z = (z - 1 / 2) * Real.log z - z + 1 / 2 * Real.log (2 * π) -
      Real.log (Real.Gamma z) := by
  have h := dlmf_5_9_10_1 (z := (z : ℂ)) (by simpa using hz)
  have hA : ∫ t in Ioi (0 : ℝ), ((Real.log (1 - Real.exp (-(2 * π * t))) : ℝ) : ℂ) /
      ((t : ℂ) ^ 2 + (z : ℂ) ^ 2) = (binA z : ℂ) := by
    rw [binA, ← integral_complex_ofReal]; push_cast; rfl
  set r : ℝ := (z - 1 / 2) * Real.log z - z + 1 / 2 * Real.log (2 * π) - z / π * binA z
  have e : (z - 1 / 2) * Complex.log z - z + 1 / 2 * Complex.log (2 * π) -
      z / π * ∫ t in Ioi (0 : ℝ), ((Real.log (1 - Real.exp (-(2 * π * t))) : ℝ) : ℂ) /
        ((t : ℂ) ^ 2 + (z : ℂ) ^ 2) = (r : ℂ) := by
    rw [hA, ← ofReal_log hz.le, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log (by positivity)]
    simp only [r]
    push_cast
    ring
  rw [e, Complex.Gamma_ofReal, ← ofReal_exp] at h
  have h' : Real.Gamma z = Real.exp r := by exact_mod_cast h
  rw [h', Real.log_exp]
  simp only [r]; ring

theorem binB_one : binB 1 = (γ - 1 / 2) / 2 := by
  have h := digamma_ofReal_eq_binB (z := 1) one_pos
  rw [ofReal_one, digamma_one] at h
  have h' : -γ = Real.log 1 - 1 / (2 * 1) - 2 * binB 1 := by exact_mod_cast h
  rw [Real.log_one] at h'
  linarith

theorem binB_half : binB (1 / 2) = (Real.log 2 - 1 + γ) / 2 := by
  have h := digamma_ofReal_eq_binB (z := 1 / 2) (by norm_num)
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring, dlmf_5_4_13] at h
  have h' : -γ - 2 * Real.log 2 = Real.log (1 / 2) - 1 / (2 * (1 / 2)) - 2 * binB (1 / 2) := by
    exact_mod_cast h
  rw [one_div, Real.log_inv] at h'
  linarith

theorem binB_two : binB 2 = (Real.log 2 - 5 / 4 + γ) / 2 := by
  have h := digamma_ofReal_eq_binB (z := 2) two_pos
  have h2 : digamma 2 = 1 - γ := by
    have := digamma_apply_add_one 1 (fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [m.cast_nonneg (α := ℝ)])
    rw [show (1 : ℂ) + 1 = 2 by norm_num, digamma_one, inv_one] at this
    rw [this]; ring
  rw [show ((2 : ℝ) : ℂ) = 2 by norm_num, h2] at h
  have h' : 1 - γ = Real.log 2 - 1 / (2 * 2) - 2 * binB 2 := by exact_mod_cast h
  linarith

theorem binA_one : binA 1 = π * (1 / 2 * Real.log (2 * π) - 1) := by
  have h := binA_spec (z := 1) one_pos
  rw [Real.Gamma_one, Real.log_one] at h
  have hπ := Real.pi_pos
  field_simp at h ⊢
  linarith

theorem binA_half : binA (1 / 2) = π * (Real.log 2 - 1) := by
  have h := binA_spec (z := 1 / 2) (by norm_num)
  rw [Real.Gamma_one_half_eq, Real.log_sqrt Real.pi_pos.le, Real.log_mul two_ne_zero
    Real.pi_pos.ne'] at h
  have hπ := Real.pi_pos
  field_simp at h ⊢
  linarith

theorem binA_two : binA 2 = π / 2 * (3 / 2 * Real.log 2 - 2 + 1 / 2 * Real.log (2 * π)) := by
  have h := binA_spec (z := 2) two_pos
  rw [Real.Gamma_two, Real.log_one] at h
  have hπ := Real.pi_pos
  field_simp at h ⊢
  linarith

/-! ### Rescaling Binet's integrals -/

theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  linarith [Real.add_one_lt_exp hx.ne']

theorem integrableOn_binB_scaled {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u / ((u ^ 2 + 1) * (Real.exp (c * u) - 1))) (Ioi 0) := by
  refine (integrable_inv_one_add_sq.integrableOn.const_mul c⁻¹).mono'
    (ContinuousOn.aestronglyMeasurable (fun u (hu : 0 < u) => ?_) measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u (hu : 0 < u) => ?_))
  · have := exp_sub_one_pos (mul_pos hc hu)
    exact (continuousAt_id.div (by fun_prop) (by positivity)).continuousWithinAt
  · have he := exp_sub_one_pos (mul_pos hc hu)
    have hle : c * u ≤ Real.exp (c * u) - 1 := by linarith [Real.add_one_le_exp (c * u)]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    calc u = c⁻¹ * (c * u) := by field_simp
      _ ≤ c⁻¹ * (Real.exp (c * u) - 1) := by gcongr
      _ = c⁻¹ * (1 + u ^ 2)⁻¹ * ((u ^ 2 + 1) * (Real.exp (c * u) - 1)) := by
          field_simp; ring

/-- `|ln(1 − e^{−cu})|` is at most `|ln c| + c + |ln u|` on `(0, 1]` and `1/(cu)` on `(0, ∞)`. -/
theorem abs_log_one_sub_exp_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    |Real.log (1 - Real.exp (-(c * u)))| ≤ |Real.log c| + c * u + |Real.log u| ∧
      |Real.log (1 - Real.exp (-(c * u)))| ≤ 1 / (c * u) := by
  set y := c * u with hy
  have hy0 : 0 < y := mul_pos hc hu
  have hx0 : 0 < Real.exp (-y) := Real.exp_pos _
  have hx1 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hlneg : Real.log (1 - Real.exp (-y)) < 0 := Real.log_neg (by linarith) (by linarith)
  rw [abs_of_neg hlneg]
  constructor
  · -- `1 − e^{−y} ≥ y e^{−y}`
    have h1 : y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by
      have := Real.add_one_le_exp y
      have hm : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hy0.ne' hx0.ne', Real.log_exp, hy, Real.log_mul hc.ne' hu.ne'] at h2
    linarith [neg_abs_le (Real.log c), neg_abs_le (Real.log u)]
  · -- `−ln(1 − x) ≤ x/(1 − x) = 1/(e^y − 1) ≤ 1/y`
    have h1 := Real.log_le_sub_one_of_pos (x := (1 - Real.exp (-y))⁻¹) (by
      have : 0 < 1 - Real.exp (-y) := by linarith
      positivity)
    rw [Real.log_inv] at h1
    have h2 : (1 - Real.exp (-y))⁻¹ - 1 = 1 / (Real.exp y - 1) := by
      have hm : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
      have : 0 < 1 - Real.exp (-y) := by linarith
      have := exp_sub_one_pos hy0
      field_simp
      nlinarith
    rw [h2] at h1
    refine h1.trans ?_
    exact one_div_le_one_div_of_le hy0 (by linarith [Real.add_one_le_exp y])

theorem integrableOn_binA_scaled {c : ℝ} (hc : 1 ≤ c) :
    IntegrableOn (fun u : ℝ => Real.log (1 - Real.exp (-(c * u))) / (u ^ 2 + 1)) (Ioi 0) := by
  have hc0 : 0 < c := by linarith
  have h := integrableOn_mul_of_log_bounds (F := fun u => Real.log (1 - Real.exp (-(c * u))))
    (G := fun u => 1 / (u ^ 2 + 1)) (M := |Real.log c| + c)
    (fun u (hu : 0 < u) => by
      have : Real.exp (-(c * u)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
      exact (Real.continuousAt_log (by linarith)).comp (by fun_prop) |>.continuousWithinAt)
    (continuousOn_const.div ((continuous_id.pow 2).add continuous_const).continuousOn
      fun u _ => by positivity) (by positivity)
    (fun u hu => by
      have := (abs_log_one_sub_exp_le hc0 hu.1).1
      nlinarith [hu.2, abs_nonneg (Real.log u)])
    (fun u hu => by
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      have : 1 ≤ |Real.log c| + c := by linarith [abs_nonneg (Real.log c)]
      nlinarith [abs_nonneg (Real.log u), sq_nonneg u])
    (fun u hu => by
      refine (abs_log_one_sub_exp_le hc0 (by linarith : 0 < u)).2.trans ?_
      rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith)
    (fun u hu => by
      rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith)
  refine h.congr_fun (fun u _ => by simp only; ring) measurableSet_Ioi

/-- `∫_0^∞ u/((u² + 1)(e^{cu} − 1)) du = B(c/(2π))`. -/
theorem integral_binB_scaled {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) - 1)) = binB (c / (2 * π)) := by
  set k := c / (2 * π) with hk
  have hk0 : 0 < k := by positivity
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => t / ((t ^ 2 + k ^ 2) *
    (Real.exp (2 * π * t) - 1))) 0 hk0
  rw [mul_zero, smul_eq_mul] at h
  have e : ∀ u ∈ Ioi (0 : ℝ), k * u / ((k * u) ^ 2 + k ^ 2) / (Real.exp (2 * π * (k * u)) - 1) =
      k⁻¹ * (u / ((u ^ 2 + 1) * (Real.exp (c * u) - 1))) := fun u (hu : 0 < u) => by
    have : 2 * π * (k * u) = c * u := by rw [hk]; field_simp
    rw [this]
    have := exp_sub_one_pos (mul_pos hc hu)
    field_simp
  simp only [div_mul_eq_div_div] at h
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul] at h
  rw [binB]
  simp only [div_mul_eq_div_div] at h ⊢
  have hk' : k⁻¹ ≠ 0 := inv_ne_zero hk0.ne'
  exact mul_left_cancel₀ hk' h

/-- `∫_0^∞ ln(1 − e^{−cu})/(u² + 1) du = (c/(2π)) A(c/(2π))`. -/
theorem integral_binA_scaled {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), Real.log (1 - Real.exp (-(c * u))) / (u ^ 2 + 1) =
      c / (2 * π) * binA (c / (2 * π)) := by
  set k := c / (2 * π) with hk
  have hk0 : 0 < k := by positivity
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => Real.log (1 - Real.exp (-(2 * π * t))) /
    (t ^ 2 + k ^ 2)) 0 hk0
  rw [mul_zero, smul_eq_mul] at h
  have e : ∀ u ∈ Ioi (0 : ℝ), Real.log (1 - Real.exp (-(2 * π * (k * u)))) / ((k * u) ^ 2 + k ^ 2) =
      (k ^ 2)⁻¹ * (Real.log (1 - Real.exp (-(c * u))) / (u ^ 2 + 1)) := fun u _ => by
    have : 2 * π * (k * u) = c * u := by rw [hk]; field_simp
    rw [this]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, ← binA] at h
  have hk2 : (k ^ 2)⁻¹ ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

/-- `∫_0^∞ u/((u² + 1)(e^{cu} + 1)) du = B(c/(2π)) − 2B(c/π)`. -/
theorem integral_Tg {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) + 1)) =
      binB (c / (2 * π)) - 2 * binB (c / π) := by
  have e : ∀ u ∈ Ioi (0 : ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) + 1)) =
      u / ((u ^ 2 + 1) * (Real.exp (c * u) - 1)) -
        2 * (u / ((u ^ 2 + 1) * (Real.exp ((2 * c) * u) - 1))) := fun u (hu : 0 < u) => by
    have h1 := exp_sub_one_pos (mul_pos hc hu)
    have h2 : Real.exp ((2 * c) * u) = Real.exp (c * u) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]
    have hE1 : Real.exp (c * u) - 1 ≠ 0 := h1.ne'
    have hE2 : Real.exp (c * u) ^ 2 - 1 ≠ 0 := by nlinarith
    have hE3 : Real.exp (c * u) + 1 ≠ 0 := by positivity
    have hu2 : u ^ 2 + 1 ≠ 0 := by positivity
    rw [show Real.exp (c * u) ^ 2 - 1 = (Real.exp (c * u) - 1) * (Real.exp (c * u) + 1) by ring]
    clear h2 hE2 h1
    generalize Real.exp (c * u) = E at *
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub (integrableOn_binB_scaled hc)
    ((integrableOn_binB_scaled (by positivity)).const_mul 2), integral_const_mul,
    integral_binB_scaled hc, integral_binB_scaled (by positivity)]
  congr 3; field_simp

/-- `∫_0^∞ ln(1 + e^{−cu})/(u² + 1) du = (c/π) A(c/π) − (c/(2π)) A(c/(2π))`, `c ≥ 1`. -/
theorem integral_Tf {c : ℝ} (hc : 1 ≤ c) :
    ∫ u in Ioi (0 : ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1) =
      c / π * binA (c / π) - c / (2 * π) * binA (c / (2 * π)) := by
  have hc0 : 0 < c := by linarith
  have e : ∀ u ∈ Ioi (0 : ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1) =
      Real.log (1 - Real.exp (-((2 * c) * u))) / (u ^ 2 + 1) -
        Real.log (1 - Real.exp (-(c * u))) / (u ^ 2 + 1) := fun u (hu : 0 < u) => by
    have hx1 : Real.exp (-(c * u)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have hx0 := Real.exp_pos (-(c * u))
    have h2 : Real.exp (-((2 * c) * u)) = Real.exp (-(c * u)) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h2, show 1 - Real.exp (-(c * u)) ^ 2 =
      (1 - Real.exp (-(c * u))) * (1 + Real.exp (-(c * u))) by ring,
      Real.log_mul (by linarith) (by linarith)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub
    (integrableOn_binA_scaled (by linarith)) (integrableOn_binA_scaled hc),
    integral_binA_scaled (by positivity), integral_binA_scaled hc0]
  congr 2 <;> field_simp

/-! ### Summing the Laplace integrals of `f`, `g` -/

theorem gR_eq_integral {x : ℝ} (hx : 0 < x) :
    gR x = ∫ u in Ioi (0 : ℝ), u * Real.exp (-(x * u)) / (u ^ 2 + 1) := by
  have h := (dlmf_6_7_14_second (z := x) (by simp [hx.le]) (by simpa using hx.ne')).2
    (by simpa using hx)
  have e : ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-((x : ℂ) * t)) / ((t : ℂ) ^ 2 + 1) =
      ((∫ u in Ioi (0 : ℝ), u * Real.exp (-(x * u)) / (u ^ 2 + 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e, (fR_gR_spec hx 0).2.1] at h
  exact_mod_cast h.symm

theorem fR_eq_integral {x : ℝ} (hx : 0 < x) :
    fR x = ∫ u in Ioi (0 : ℝ), Real.exp (-(x * u)) / (u ^ 2 + 1) := by
  have h := dlmf_6_7_13_second (z := x) (by simp [hx.le])
  rw [(fR_gR_spec hx 0).1] at h
  have e : ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) / ((t : ℂ) ^ 2 + 1) =
      ((∫ u in Ioi (0 : ℝ), Real.exp (-(x * u)) / (u ^ 2 + 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; push_cast; rfl
  rw [e] at h
  exact_mod_cast h.symm

theorem integral_pow_mul_exp_neg_le {k : ℝ} (hk : 0 < k) (j : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ j * Real.exp (-(k * u)) = j ! / k ^ (j + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := k) (by positivity) hk
  rw [show (j : ℝ) + 1 - 1 = (j : ℕ) by ring, show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by
    push_cast; ring, show Real.Gamma ((j + 1 : ℕ) : ℝ) = ((j ! : ℕ) : ℝ) by
      rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]] at h
  simp only [Real.rpow_natCast] at h
  rw [h, one_div_pow]; field_simp

theorem summable_one_div_succ_sq (C : ℝ) :
    Summable (fun n : ℕ => C / ((n : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine (this.mul_left C).congr fun n => ?_
  push_cast; ring

/-- `∑_{n≥0} (−1)ⁿ g(c(n + 1)) = ∫_0^∞ u/((u² + 1)(e^{cu} + 1)) du`. -/
theorem hasSum_gR {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => (-1) ^ n * gR (c * (n + 1)))
      (∫ u in Ioi (0 : ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) + 1))) := by
  set F : ℕ → ℝ → ℝ := fun n u => (-1) ^ n * (u * Real.exp (-(c * (n + 1) * u)) / (u ^ 2 + 1))
  have hk : ∀ n : ℕ, 0 < c * (n + 1) := fun n => by positivity
  have hbound : ∀ n : ℕ, ∀ u ∈ Ioi (0 : ℝ), ‖F n u‖ ≤ u ^ 1 * Real.exp (-(c * (n + 1) * u)) :=
    fun n u (hu : 0 < u) => by
      simp only [F, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
        pow_one]
      rw [abs_of_nonneg (by positivity)]
      exact div_le_self (by positivity) (by nlinarith)
  have hden : ∀ u : ℝ, u ^ 2 + 1 ≠ 0 := fun u => by positivity
  have hcont : ∀ n : ℕ, Continuous (F n) := fun n =>
    continuous_const.mul (((by fun_prop : Continuous fun u : ℝ =>
      u * Real.exp (-(c * (n + 1) * u)))).div (by fun_prop) hden)
  have hint : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := fun n =>
    (integrableOn_pow_mul_exp_neg_mul 1 (hk n)).mono'
      ((hcont n).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hbound n)))
  have hsum : Summable fun n => ∫ u in Ioi (0 : ℝ), ‖F n u‖ := by
    refine (summable_one_div_succ_sq (1 / c ^ 2)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) fun n => ?_
    refine (setIntegral_mono_on (hint n).norm (integrableOn_pow_mul_exp_neg_mul 1 (hk n))
      measurableSet_Ioi (hbound n)).trans (le_of_eq ?_)
    rw [integral_pow_mul_exp_neg_le (hk n) 1]
    simp; field_simp
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : (fun n => ∫ u in Ioi (0 : ℝ), F n u) =
      fun n : ℕ => (-1 : ℝ) ^ n * gR (c * ((n : ℝ) + 1)) :=
    funext fun n => by
      simp only [F]
      rw [integral_const_mul, gR_eq_integral (hk n)]
  have e2 : ∫ u in Ioi (0 : ℝ), ∑' n, F n u =
      ∫ u in Ioi (0 : ℝ), u / ((u ^ 2 + 1) * (Real.exp (c * u) + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    set x := Real.exp (-(c * u))
    have hx0 : 0 < x := Real.exp_pos _
    have hx1 : x < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have hg := (hasSum_geometric_of_abs_lt_one (r := -x) (by
      rw [abs_neg, abs_of_pos hx0]; exact hx1)).mul_left (x * u / (u ^ 2 + 1))
    have hF : ∀ n : ℕ, F n u = x * u / (u ^ 2 + 1) * (-x) ^ n := fun n => by
      simp only [F, x]
      rw [neg_pow, show -(c * ((n : ℝ) + 1) * u) = (n + 1 : ℕ) * (-(c * u)) by push_cast; ring,
        Real.exp_nat_mul]
      ring
    simp only [hF]
    rw [hg.tsum_eq]
    have hex : Real.exp (c * u) * x = 1 := by
      simp only [x]; rw [← Real.exp_add]; simp
    rw [eq_inv_of_mul_eq_one_left hex, sub_neg_eq_add]
    field_simp
  rw [e1, e2] at h
  exact h

/-- `∑_{n≥0} (−1)ⁿ f(c(n + 1))/(n + 1) = ∫_0^∞ ln(1 + e^{−cu})/(u² + 1) du`. -/
theorem hasSum_fR {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => (-1) ^ n * fR (c * (n + 1)) / (n + 1))
      (∫ u in Ioi (0 : ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1)) := by
  set F : ℕ → ℝ → ℝ := fun n u =>
    (-1) ^ n / (n + 1) * (Real.exp (-(c * (n + 1) * u)) / (u ^ 2 + 1))
  have hk : ∀ n : ℕ, 0 < c * (n + 1) := fun n => by positivity
  have hbound : ∀ n : ℕ, ∀ u ∈ Ioi (0 : ℝ),
      ‖F n u‖ ≤ 1 / ((n : ℝ) + 1) * (u ^ 0 * Real.exp (-(c * (n + 1) * u))) :=
    fun n u (hu : 0 < u) => by
      simp only [F, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_eq_abs,
        pow_zero, one_mul]
      rw [abs_of_pos (by positivity : (0 : ℝ) < n + 1), abs_of_nonneg (by positivity),
        abs_of_pos (by positivity : (0 : ℝ) < u ^ 2 + 1)]
      gcongr
      exact div_le_self (by positivity) (by nlinarith)
  have hint0 : ∀ n : ℕ, IntegrableOn (fun u : ℝ => 1 / ((n : ℝ) + 1) *
      (u ^ 0 * Real.exp (-(c * (n + 1) * u)))) (Ioi 0) := fun n =>
    (integrableOn_pow_mul_exp_neg_mul 0 (hk n)).const_mul _
  have hden : ∀ u : ℝ, u ^ 2 + 1 ≠ 0 := fun u => by positivity
  have hcont : ∀ n : ℕ, Continuous (F n) := fun n =>
    continuous_const.mul (((by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(c * (n + 1) * u)))).div (by fun_prop) hden)
  have hint : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := fun n =>
    (hint0 n).mono' ((hcont n).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hbound n)))
  have hsum : Summable fun n => ∫ u in Ioi (0 : ℝ), ‖F n u‖ := by
    refine (summable_one_div_succ_sq (1 / c)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) fun n => ?_
    refine (setIntegral_mono_on (hint n).norm (hint0 n) measurableSet_Ioi (hbound n)).trans
      (le_of_eq ?_)
    rw [integral_const_mul, integral_pow_mul_exp_neg_le (hk n) 0]
    simp; field_simp
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : (fun n => ∫ u in Ioi (0 : ℝ), F n u) =
      fun n : ℕ => (-1 : ℝ) ^ n * fR (c * ((n : ℝ) + 1)) / ((n : ℝ) + 1) :=
    funext fun n => by
      simp only [F]
      rw [integral_const_mul, fR_eq_integral (hk n)]
      have : ∫ u in Ioi (0 : ℝ), Real.exp (-(c * (n + 1) * u)) / (u ^ 2 + 1) =
          ∫ u in Ioi (0 : ℝ), Real.exp (-(c * ((n : ℝ) + 1) * u)) / (u ^ 2 + 1) := rfl
      rw [this]; ring
  have e2 : ∫ u in Ioi (0 : ℝ), ∑' n, F n u =
      ∫ u in Ioi (0 : ℝ), Real.log (1 + Real.exp (-(c * u))) / (u ^ 2 + 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    set x := Real.exp (-(c * u))
    have hx0 : 0 < x := Real.exp_pos _
    have hx1 : x < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have hl := (Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by
      rw [abs_neg, abs_of_pos hx0]; exact hx1)).neg.mul_left (1 / (u ^ 2 + 1))
    have hF : ∀ n : ℕ, F n u = 1 / (u ^ 2 + 1) * -((-x) ^ (n + 1) / (n + 1)) := fun n => by
      simp only [F, x]
      rw [show -(c * ((n : ℝ) + 1) * u) = (n + 1 : ℕ) * (-(c * u)) by push_cast; ring,
        Real.exp_nat_mul, neg_pow (Real.exp _) (n + 1), pow_succ (-1 : ℝ)]
      ring
    simp only [hF]
    rw [hl.tsum_eq, sub_neg_eq_add, neg_neg]
    ring
  rw [e1, e2] at h
  exact h

/-! ### 6.15.1–6.15.4 -/

theorem CiR_nat_mul_pi {m : ℕ} (hm : 0 < m) : CiR (π * m) = -((-1) ^ m * gR (π * m)) := by
  rw [CiR_eq (by positivity), mul_comm π, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]; ring

theorem siR_nat_mul_pi {m : ℕ} (hm : 0 < m) :
    SiR (π * m) - π / 2 = -((-1) ^ m * fR (π * m)) := by
  rw [SiR_eq (by positivity), mul_comm π, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]; ring

theorem CiR_two_nat_mul_pi {m : ℕ} (hm : 0 < m) : CiR (2 * π * m) = -gR (2 * π * m) := by
  rw [CiR_eq (by positivity), show 2 * π * m = ((2 * m : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, pow_mul]; norm_num

theorem siR_two_nat_mul_pi {m : ℕ} (hm : 0 < m) :
    SiR (2 * π * m) - π / 2 = -fR (2 * π * m) := by
  rw [SiR_eq (by positivity), show 2 * π * m = ((2 * m : ℕ) : ℝ) * π by push_cast; ring,
    Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, pow_mul]; norm_num

/-- **DLMF 6.15.1**: `∑_{n=1}^∞ Ci(πn) = ½(ln 2 − γ)`. -/
theorem dlmf_6_15_1 :
    HasSum (fun n : ℕ => Ci (π * (n + 1))) (((Real.log 2 - γ) / 2 : ℝ) : ℂ) := by
  have h := hasSum_gR Real.pi_pos
  rw [integral_Tg Real.pi_pos, show π / (2 * π) = 1 / 2 by field_simp,
    div_self Real.pi_ne_zero, binB_half, binB_one] at h
  rw [show (Real.log 2 - γ) / 2 = (Real.log 2 - 1 + γ) / 2 - 2 * ((γ - 1 / 2) / 2) by ring]
  refine (hasSum_ofReal.2 h).congr_fun fun n => ?_
  rw [show (π : ℂ) * ((n : ℂ) + 1) = ((π * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; ring,
    Ci_ofReal (by positivity), CiR_nat_mul_pi (Nat.succ_pos n), pow_succ]
  push_cast; ring

/-- **DLMF 6.15.2**: `∑_{n=1}^∞ si(πn)/n = ½π(ln π − 1)`. -/
theorem dlmf_6_15_2 :
    HasSum (fun n : ℕ => si (π * (n + 1)) / (n + 1)) ((π / 2 * (Real.log π - 1) : ℝ) : ℂ) := by
  have h := hasSum_fR Real.pi_pos
  rw [integral_Tf (by linarith [Real.pi_gt_three]), div_self Real.pi_ne_zero,
    show π / (2 * π) = 1 / 2 by field_simp, binA_one, binA_half,
    Real.log_mul two_ne_zero Real.pi_ne_zero] at h
  rw [show π / 2 * (Real.log π - 1) = 1 * (π * (1 / 2 * (Real.log 2 + Real.log π) - 1)) -
    1 / 2 * (π * (Real.log 2 - 1)) by ring]
  refine (hasSum_ofReal.2 h).congr_fun fun n => ?_
  rw [show (π : ℂ) * ((n : ℂ) + 1) = ((π * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; ring,
    si_ofReal, siR_nat_mul_pi (Nat.succ_pos n), pow_succ]
  push_cast; ring

/-- **DLMF 6.15.3**: `∑_{n=1}^∞ (−1)ⁿ Ci(2πn) = 1 − ln 2 − ½γ`. -/
theorem dlmf_6_15_3 :
    HasSum (fun n : ℕ => (-1) ^ (n + 1) * Ci (2 * π * (n + 1)))
      ((1 - Real.log 2 - γ / 2 : ℝ) : ℂ) := by
  have h := hasSum_gR (c := 2 * π) (by positivity)
  rw [integral_Tg (by positivity), show 2 * π / (2 * π) = 1 by field_simp,
    show 2 * π / π = 2 by field_simp, binB_one, binB_two] at h
  rw [show 1 - Real.log 2 - γ / 2 = (γ - 1 / 2) / 2 - 2 * ((Real.log 2 - 5 / 4 + γ) / 2) by ring]
  refine (hasSum_ofReal.2 h).congr_fun fun n => ?_
  rw [show 2 * (π : ℂ) * ((n : ℂ) + 1) = ((2 * π * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) by
    push_cast; ring, Ci_ofReal (by positivity), CiR_two_nat_mul_pi (Nat.succ_pos n)]
  push_cast; ring

/-- **DLMF 6.15.4**: `∑_{n=1}^∞ (−1)ⁿ si(2πn)/n = π(3/2 ln 2 − 1)`. -/
theorem dlmf_6_15_4 :
    HasSum (fun n : ℕ => (-1) ^ (n + 1) * si (2 * π * (n + 1)) / (n + 1))
      ((π * (3 / 2 * Real.log 2 - 1) : ℝ) : ℂ) := by
  have h := hasSum_fR (c := 2 * π) (by positivity)
  rw [integral_Tf (by nlinarith [Real.pi_gt_three]), show 2 * π / π = 2 by field_simp,
    show 2 * π / (2 * π) = 1 by field_simp, binA_one, binA_two] at h
  rw [show π * (3 / 2 * Real.log 2 - 1) =
    2 * (π / 2 * (3 / 2 * Real.log 2 - 2 + 1 / 2 * Real.log (2 * π))) -
      1 * (π * (1 / 2 * Real.log (2 * π) - 1)) by ring]
  refine (hasSum_ofReal.2 h).congr_fun fun n => ?_
  rw [show 2 * (π : ℂ) * ((n : ℂ) + 1) = ((2 * π * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) by
    push_cast; ring, si_ofReal, siR_two_nat_mul_pi (Nat.succ_pos n)]
  push_cast; ring

end Azurite.DLMF
