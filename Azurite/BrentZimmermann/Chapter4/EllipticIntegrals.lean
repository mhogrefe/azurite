/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AGM
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Brent–Zimmermann §4.8.1: Elliptic integrals and Gauss's theorem

The complete elliptic integrals of the first and second kind are

  `K(k) = ∫_0^{π/2} dθ/√(1 − k² sin²θ) = ∫_0^1 dt/√((1−t²)(1−k²t²))`,                       (4.67)
  `E(k) = ∫_0^{π/2} √(1 − k² sin²θ) dθ`,

with modulus `k ∈ [0, 1]` and complementary modulus `k' = √(1 − k²)`; `K'(k) := K(k')`.  Gauss
discovered

  `1/AGM(1, k) = (2/π) K'(k)`,                                                              (4.68)

so `K` can be computed rapidly by the AGM, and logarithms follow.  For small `k`,
`K(k) = (π/2)(1 + k²/4 + O(k⁴))` (4.69) (in fact `K(k) = (π/2) ₂F₁(1/2, 1/2; 1; k²)`), and
`K'(k) = (2/π) ln(4/k) K(k) − k²/4 + O(k⁴)` (4.70).

What is formalized:

* `ellipticK`, `ellipticE` (the `θ`-forms of (4.67)), `ellipticK_zero`, `ellipticE_zero`,
  `ellipticE_le_pi_div_two`, `pi_div_two_le_ellipticK` (for `k² < 1`), and (4.69) as the two-sided
  bound `ellipticK_bounds`: `(π/2)(1 + k²/4) ≤ K(k) ≤ (π/2)(1 + k²/4 + 3k⁴/8)` for `k² ≤ 1/2`.
* **Gauss's theorem (4.68).**  With `J(a, b) = ∫_0^∞ dt/√((t² + a²)(t² + b²))` (`agmIntegral`):
  `J(c, c) = π/(2c)` (`agmIntegral_self`), the Landen/Gauss substitution `u = (t − ab/t)/2`
  gives `J((a+b)/2, √(ab)) = J(a, b)` (`agmIntegral_landen`, via the one-dimensional change of
  variables `integral_image_eq_integral_abs_deriv_smul`), hence `J(a_j, b_j) = J(a, b)` along the
  AGM iteration and, squeezing between `π/(2a_j)` and `π/(2b_j)`,
  `J(a, b) = π/(2 AGM(a, b))` (`agmIntegral_eq_pi_div_AGM`).  The substitution `t = tan θ` turns
  `J(1, k)` into `∫_0^{π/2} dθ/√(cos²θ + k² sin²θ)` (`agmIntegral_one_eq`), which is `K(k')`
  for `k ≤ 1`; so `one_div_AGM_one`: `1/AGM(1, k) = (2/π) K(√(1 − k²))`, and in general
  `∫_0^{π/2} dθ/√(a² cos²θ + b² sin²θ) = π/(2 AGM(a, b))` (`integral_inv_sqrt_eq_pi_div_AGM`).

Not formalized: the `t`-forms of (4.67) (improper at `t = 1`), the hypergeometric identification,
and the expansion (4.70) of `K'` near `k = 0` (that is the asymptotics of `K` near `k = 1`).
-/

namespace Azurite

namespace BZ

open Filter Topology Set MeasureTheory intervalIntegral Real

/-! ### The complete elliptic integrals -/

/-- `K(k) = ∫_0^{π/2} dθ/√(1 − k² sin²θ)`. -/
noncomputable def ellipticK (k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹

/-- `E(k) = ∫_0^{π/2} √(1 − k² sin²θ) dθ`. -/
noncomputable def ellipticE (k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)

theorem one_sub_mul_sin_sq_pos {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    0 < 1 - k ^ 2 * Real.sin θ ^ 2 := by
  have h1 := Real.sin_sq_le_one θ
  have h2 : k ^ 2 * Real.sin θ ^ 2 ≤ k ^ 2 := mul_le_of_le_one_right (sq_nonneg k) h1
  linarith

theorem continuous_ellipticK_integrand {k : ℝ} (hk : k ^ 2 < 1) :
    Continuous fun θ : ℝ => (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ :=
  (Real.continuous_sqrt.comp (by fun_prop)).inv₀ fun θ =>
    (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hk θ)).ne'

theorem continuous_ellipticE_integrand (k : ℝ) :
    Continuous fun θ : ℝ => Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
  Real.continuous_sqrt.comp (by fun_prop)

theorem ellipticK_zero : ellipticK 0 = π / 2 := by
  simp [ellipticK]

theorem ellipticE_zero : ellipticE 0 = π / 2 := by
  simp [ellipticE]

/-- `E(k) ≤ π/2`. -/
theorem ellipticE_le_pi_div_two (k : ℝ) : ellipticE k ≤ π / 2 := by
  unfold ellipticE
  have h : ∫ θ in (0 : ℝ)..(π / 2), (1 : ℝ) = π / 2 := by simp
  have hE : IntervalIntegrable (fun θ : ℝ => Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) volume 0
      (π / 2) := (continuous_ellipticE_integrand k).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (π / 2) :=
    continuous_const.intervalIntegrable _ _
  calc ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      ≤ ∫ θ in (0 : ℝ)..(π / 2), (1 : ℝ) := by
        refine integral_mono_on Real.pi_div_two_pos.le hE h1 fun θ _ => ?_
        rw [Real.sqrt_le_one]
        nlinarith [sq_nonneg k, sq_nonneg (Real.sin θ)]
    _ = π / 2 := h

/-- `π/2 ≤ K(k)` for `k² < 1`. -/
theorem pi_div_two_le_ellipticK {k : ℝ} (hk : k ^ 2 < 1) : π / 2 ≤ ellipticK k := by
  unfold ellipticK
  have h : ∫ θ in (0 : ℝ)..(π / 2), (1 : ℝ) = π / 2 := by simp
  have hK : IntervalIntegrable (fun θ : ℝ => (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹) volume 0
      (π / 2) := (continuous_ellipticK_integrand hk).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (π / 2) :=
    continuous_const.intervalIntegrable _ _
  calc π / 2 = ∫ θ in (0 : ℝ)..(π / 2), (1 : ℝ) := h.symm
    _ ≤ ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))⁻¹ := by
        refine integral_mono_on Real.pi_div_two_pos.le h1 hK fun θ _ => ?_
        rw [one_le_inv₀ (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hk θ)), Real.sqrt_le_one]
        nlinarith [sq_nonneg k, sq_nonneg (Real.sin θ)]

/-- `1 + x/2 ≤ 1/√(1−x) ≤ 1 + x/2 + x²` for `0 ≤ x ≤ 1/2`. -/
theorem inv_sqrt_one_sub_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    1 + x / 2 ≤ (Real.sqrt (1 - x))⁻¹ ∧ (Real.sqrt (1 - x))⁻¹ ≤ 1 + x / 2 + x ^ 2 := by
  have h1x : 0 < 1 - x := by linarith
  have hs : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr h1x
  constructor
  · rw [inv_eq_one_div, le_div_iff₀ hs,
      show (1 + x / 2) * Real.sqrt (1 - x) = Real.sqrt ((1 + x / 2) ^ 2 * (1 - x)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)],
      Real.sqrt_le_one]
    have e : (1 + x / 2) ^ 2 * (1 - x) = 1 - 3 / 4 * x ^ 2 - 1 / 4 * x ^ 3 := by ring
    rw [e]
    linarith [sq_nonneg x, pow_nonneg hx0 3]
  · rw [inv_eq_one_div, div_le_iff₀ hs,
      show (1 + x / 2 + x ^ 2) * Real.sqrt (1 - x)
          = Real.sqrt ((1 + x / 2 + x ^ 2) ^ 2 * (1 - x)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)],
      Real.le_sqrt zero_le_one (by positivity), one_pow]
    have e : (1 + x / 2 + x ^ 2) ^ 2 * (1 - x) = 1 + 5 / 4 * x ^ 2 - 5 / 4 * x ^ 3 - x ^ 5 := by
      ring
    have h3 : x ^ 3 ≤ x ^ 2 / 2 := by
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 2 - x)]
    have h5 : x ^ 5 ≤ x ^ 2 / 8 := by
      have h8 : x ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hx0 hx 3
      nlinarith [mul_le_mul_of_nonneg_left h8 (sq_nonneg x)]
    rw [e]
    linarith [sq_nonneg x]

theorem integral_sin_sq_pi_div_two : ∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ 2 = π / 4 := by
  rw [integral_sin_sq]
  simp
  ring

theorem integral_sin_pow_four_pi_div_two :
    ∫ θ in (0 : ℝ)..(π / 2), Real.sin θ ^ 4 = 3 * π / 16 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, integral_sin_pow, integral_sin_sq_pi_div_two]
  simp
  ring

/-- (4.69) with explicit constants: `(π/2)(1 + k²/4) ≤ K(k) ≤ (π/2)(1 + k²/4 + 3k⁴/8)` for
`k² ≤ 1/2`. -/
theorem ellipticK_bounds {k : ℝ} (hk : k ^ 2 ≤ 1 / 2) :
    π / 2 * (1 + k ^ 2 / 4) ≤ ellipticK k
      ∧ ellipticK k ≤ π / 2 * (1 + k ^ 2 / 4 + 3 / 8 * k ^ 4) := by
  have hk1 : k ^ 2 < 1 := by linarith
  have hcont := continuous_ellipticK_integrand hk1
  have hsin2 : IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ 2) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin θ ^ 2).intervalIntegrable _ _
  have hsin4 : IntervalIntegrable (fun θ : ℝ => Real.sin θ ^ 4) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin θ ^ 4).intervalIntegrable _ _
  have hx : ∀ θ : ℝ, 0 ≤ k ^ 2 * Real.sin θ ^ 2 ∧ k ^ 2 * Real.sin θ ^ 2 ≤ 1 / 2 := fun θ =>
    ⟨by positivity, (mul_le_of_le_one_right (sq_nonneg k) (Real.sin_sq_le_one θ)).trans hk⟩
  constructor
  · have hlow : ∫ θ in (0 : ℝ)..(π / 2), (1 + k ^ 2 / 2 * Real.sin θ ^ 2)
        = π / 2 * (1 + k ^ 2 / 4) := by
      rw [integral_add (continuous_const.intervalIntegrable _ _) (hsin2.const_mul _),
        intervalIntegral.integral_const_mul, integral_sin_sq_pi_div_two]
      simp
      ring
    rw [← hlow]
    refine integral_mono_on Real.pi_div_two_pos.le
      ((continuous_const.add (continuous_const.mul (by fun_prop))).intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) fun θ _ => ?_
    have := (inv_sqrt_one_sub_bounds (hx θ).1 (hx θ).2).1
    linarith
  · have hup : ∫ θ in (0 : ℝ)..(π / 2),
        (1 + k ^ 2 / 2 * Real.sin θ ^ 2 + k ^ 4 * Real.sin θ ^ 4)
        = π / 2 * (1 + k ^ 2 / 4 + 3 / 8 * k ^ 4) := by
      rw [integral_add ((continuous_const.intervalIntegrable _ _).add (hsin2.const_mul _))
        (hsin4.const_mul _), integral_add (continuous_const.intervalIntegrable _ _)
        (hsin2.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_sin_sq_pi_div_two,
        integral_sin_pow_four_pi_div_two]
      simp
      ring
    rw [← hup]
    refine integral_mono_on Real.pi_div_two_pos.le (hcont.intervalIntegrable _ _)
      ((continuous_const.add (continuous_const.mul (by fun_prop)) |>.add
        (continuous_const.mul (by fun_prop))).intervalIntegrable _ _) fun θ _ => ?_
    have := (inv_sqrt_one_sub_bounds (hx θ).1 (hx θ).2).2
    have h4 : (k ^ 2 * Real.sin θ ^ 2) ^ 2 = k ^ 4 * Real.sin θ ^ 4 := by ring
    linarith

/-! ### The integral `J(a, b) = ∫_0^∞ dt/√((t² + a²)(t² + b²))` -/

/-- The integrand of `J(a, b)`. -/
noncomputable def agmKernel (a b t : ℝ) : ℝ := (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹

/-- `J(a, b) = ∫_0^∞ dt/√((t² + a²)(t² + b²))`. -/
noncomputable def agmIntegral (a b : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), agmKernel a b t

variable {a b : ℝ}

theorem agmKernel_pos (ha : 0 < a) (hb : 0 < b) (t : ℝ) : 0 < agmKernel a b t := by
  unfold agmKernel
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem agmKernel_neg (a b t : ℝ) : agmKernel a b (-t) = agmKernel a b t := by
  simp [agmKernel]

theorem continuous_agmKernel (ha : 0 < a) (hb : 0 < b) : Continuous (agmKernel a b) :=
  (Real.continuous_sqrt.comp (by fun_prop)).inv₀ fun t =>
    (Real.sqrt_pos.mpr (by positivity)).ne'

theorem agmKernel_comm (a b t : ℝ) : agmKernel a b t = agmKernel b a t := by
  unfold agmKernel; rw [mul_comm]

/-- `kernel ≤ (t² + min(a,b)²)⁻¹`. -/
theorem agmKernel_le (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    agmKernel a b t ≤ (t ^ 2 + min a b ^ 2)⁻¹ := by
  unfold agmKernel
  have hm : 0 < min a b := lt_min ha hb
  have h1 : min a b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hm.le (min_le_left a b) 2
  have h2 : min a b ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hm.le (min_le_right a b) 2
  rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity))
      (add_pos_of_nonneg_of_pos (sq_nonneg t) (pow_pos hm 2)),
    show t ^ 2 + min a b ^ 2 = Real.sqrt ((t ^ 2 + min a b ^ 2) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  calc (t ^ 2 + min a b ^ 2) ^ 2 = (t ^ 2 + min a b ^ 2) * (t ^ 2 + min a b ^ 2) := sq _
    _ ≤ (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2) := by gcongr

/-- Monotonicity of the kernel in the parameters. -/
theorem agmKernel_anti (ha : 0 < a) (hb : 0 < b) {a' b' : ℝ} (ha' : a ≤ a') (hb' : b ≤ b') (t : ℝ) :
    agmKernel a' b' t ≤ agmKernel a b t := by
  unfold agmKernel
  have ha0 : 0 < a' := ha.trans_le ha'
  have hb0 : 0 < b' := hb.trans_le hb'
  rw [inv_le_inv₀
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (t ^ 2 + a' ^ 2) * (t ^ 2 + b' ^ 2)))
    (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))]
  apply Real.sqrt_le_sqrt
  have h1 : a ^ 2 ≤ a' ^ 2 := pow_le_pow_left₀ ha.le ha' 2
  have h2 : b ^ 2 ≤ b' ^ 2 := pow_le_pow_left₀ hb.le hb' 2
  gcongr

theorem integrable_agmKernel (ha : 0 < a) (hb : 0 < b) : Integrable (agmKernel a b) := by
  set m := min (min a b) 1 with hm
  have hm0 : 0 < m := lt_min (lt_min ha hb) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmab : m ≤ min a b := min_le_left _ _
  refine (integrable_inv_one_add_sq.const_mul (m ^ 2)⁻¹).mono'
    (continuous_agmKernel ha hb).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (agmKernel_pos ha hb t)]
  refine (agmKernel_le ha hb t).trans ?_
  have hmin : 0 < min a b := lt_min ha hb
  have h1 : m ^ 2 ≤ min a b ^ 2 := pow_le_pow_left₀ hm0.le hmab 2
  rw [← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
  have hm2 : m ^ 2 ≤ 1 := pow_le_one₀ hm0.le hm1
  have := mul_le_mul_of_nonneg_right hm2 (sq_nonneg t)
  nlinarith

/-- `J(c, c) = ∫_0^∞ dt/(t² + c²) = π/(2c)`. -/
theorem agmIntegral_self {c : ℝ} (hc : 0 < c) : agmIntegral c c = π / (2 * c) := by
  unfold agmIntegral
  have h1 : ∀ t : ℝ, agmKernel c c t = (c⁻¹) ^ 2 * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    intro t
    unfold agmKernel
    rw [← sq, Real.sqrt_sq (by positivity)]
    field_simp
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul, integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0
    (inv_pos.mpr hc), mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
    inv_inv, smul_eq_mul]
  field_simp

/-- `J` is antitone in each parameter. -/
theorem agmIntegral_anti (ha : 0 < a) (hb : 0 < b) {a' b' : ℝ} (ha' : a ≤ a') (hb' : b ≤ b') :
    agmIntegral a' b' ≤ agmIntegral a b :=
  setIntegral_mono_on (integrable_agmKernel (ha.trans_le ha') (hb.trans_le hb')).integrableOn
    (integrable_agmKernel ha hb).integrableOn measurableSet_Ioi
    fun t _ => agmKernel_anti ha hb ha' hb' t

/-! ### The Landen–Gauss substitution -/

/-- The Landen map `t ↦ (t − ab/t)/2`. -/
noncomputable def landen (a b t : ℝ) : ℝ := (t - a * b * t⁻¹) / 2

theorem hasDerivAt_landen (a b : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (landen a b) ((1 + a * b * (t ^ 2)⁻¹) / 2) t := by
  have h := ((hasDerivAt_id t).sub ((hasDerivAt_inv ht).const_mul (a * b))).div_const 2
  refine h.congr_deriv ?_
  field_simp
  ring

theorem landen_injOn (ha : 0 < a) (hb : 0 < b) : InjOn (landen a b) (Ioi 0) := by
  intro s hs t ht h
  simp only [mem_Ioi] at hs ht
  unfold landen at h
  have h2 : (s - t) * (s * t + a * b) = s * t * ((s - a * b * s⁻¹) - (t - a * b * t⁻¹)) := by
    field_simp
    ring
  have h3 : (s - a * b * s⁻¹) - (t - a * b * t⁻¹) = 0 := by linarith
  rw [h3, mul_zero] at h2
  rcases mul_eq_zero.mp h2 with h4 | h4
  · linarith
  · nlinarith [mul_pos hs ht, mul_pos ha hb]

theorem landen_image (ha : 0 < a) (hb : 0 < b) : landen a b '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun u => ?_
  have hr : 0 ≤ u ^ 2 + a * b := by positivity
  set r := Real.sqrt (u ^ 2 + a * b) with hr_def
  have hr2 : r ^ 2 = u ^ 2 + a * b := Real.sq_sqrt hr
  have hru : |u| < r := by
    rw [hr_def, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg u) (by nlinarith [mul_pos ha hb])
  have ht : 0 < u + r := by linarith [neg_abs_le u]
  refine ⟨u + r, ht, ?_⟩
  unfold landen
  field_simp
  nlinarith [hr2]

/-- The pointwise identity behind the Landen step: `|f'(t)| · kernel((a+b)/2, √(ab))(f t)
= 2 · kernel(a, b)(t)`. -/
theorem landen_kernel (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    |(1 + a * b * (t ^ 2)⁻¹) / 2| * agmKernel ((a + b) / 2) (Real.sqrt (a * b)) (landen a b t)
      = 2 * agmKernel a b t := by
  unfold agmKernel landen
  have hab : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (by positivity)
  have hA : 0 ≤ (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2) := by positivity
  have hQ : 0 ≤ (t ^ 2 + a * b) / (4 * t ^ 2) := by positivity
  have hprod : (((t - a * b * t⁻¹) / 2) ^ 2 + ((a + b) / 2) ^ 2)
      * (((t - a * b * t⁻¹) / 2) ^ 2 + Real.sqrt (a * b) ^ 2)
      = (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2) * ((t ^ 2 + a * b) / (4 * t ^ 2)) ^ 2 := by
    rw [hab]
    field_simp
    ring
  rw [hprod, Real.sqrt_mul hA, Real.sqrt_sq hQ, abs_of_pos (by positivity)]
  have hs : 0 < Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  have hq : 0 < t ^ 2 + a * b := by positivity
  field_simp
  ring

/-- Evenness: `∫_ℝ kernel = 2 J`. -/
theorem integral_agmKernel (ha : 0 < a) (hb : 0 < b) :
    ∫ t, agmKernel a b t = 2 * agmIntegral a b := by
  have hint := integrable_agmKernel ha hb
  rw [← integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have h : ∫ t in Iic (0 : ℝ), agmKernel a b t = ∫ t in Ioi (0 : ℝ), agmKernel a b t := by
    rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
    exact setIntegral_congr_fun measurableSet_Iic fun t _ => (agmKernel_neg a b t).symm
  rw [h]
  unfold agmIntegral
  ring

/-- The Landen–Gauss transformation: `J((a+b)/2, √(ab)) = J(a, b)`. -/
theorem agmIntegral_landen (ha : 0 < a) (hb : 0 < b) :
    agmIntegral ((a + b) / 2) (Real.sqrt (a * b)) = agmIntegral a b := by
  have ha1 : 0 < (a + b) / 2 := by positivity
  have hb1 : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (by positivity)
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := landen a b) (f' := fun t => (1 + a * b * (t ^ 2)⁻¹) / 2) measurableSet_Ioi
    (fun t ht => (hasDerivAt_landen a b (ne_of_gt ht)).hasDerivWithinAt)
    (landen_injOn ha hb) (agmKernel ((a + b) / 2) (Real.sqrt (a * b)))
  rw [landen_image ha hb, Measure.restrict_univ, integral_agmKernel ha1 hb1] at hcov
  have h2 : ∫ t in Ioi (0 : ℝ), |(1 + a * b * (t ^ 2)⁻¹) / 2|
      • agmKernel ((a + b) / 2) (Real.sqrt (a * b)) (landen a b t)
      = ∫ t in Ioi (0 : ℝ), 2 * agmKernel a b t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      rw [smul_eq_mul, landen_kernel ha hb ht]
  rw [h2, MeasureTheory.integral_const_mul] at hcov
  unfold agmIntegral at hcov ⊢
  linarith

theorem agmIntegral_agmSeq (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmIntegral (agmA a b j) (agmB a b j) = agmIntegral a b := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨hA, hB⟩ := agm_pos ha hb j
    rw [agmA_succ, agmB_succ, agmIntegral_landen hA hB, ih]

/-- Gauss: `J(a, b) = π/(2 AGM(a, b))`. -/
theorem agmIntegral_eq_pi_div_AGM (ha : 0 < a) (hb : 0 < b) :
    agmIntegral a b = π / (2 * AGM a b) := by
  have hAGM : 0 < AGM a b := lt_of_lt_of_le (lt_min ha hb) (min_le_AGM ha hb)
  have hup : ∀ j : ℕ, agmIntegral a b ≤ π / (2 * agmB a b (j + 1)) := fun j => by
    obtain ⟨hA, hB⟩ := agm_pos ha hb (j + 1)
    rw [← agmIntegral_agmSeq ha hb (j + 1), ← agmIntegral_self hB]
    exact agmIntegral_anti hB hB (agmB_le_agmA_succ ha hb j) le_rfl
  have hlow : ∀ j : ℕ, π / (2 * agmA a b (j + 1)) ≤ agmIntegral a b := fun j => by
    obtain ⟨hA, hB⟩ := agm_pos ha hb (j + 1)
    rw [← agmIntegral_agmSeq ha hb (j + 1), ← agmIntegral_self hA]
    exact agmIntegral_anti hA hB le_rfl (agmB_le_agmA_succ ha hb j)
  have hta : Tendsto (fun j : ℕ => π / (2 * agmA a b (j + 1))) atTop (𝓝 (π / (2 * AGM a b))) :=
    tendsto_const_nhds.div ((tendsto_agmA_succ ha hb).const_mul 2) (by positivity)
  have htb : Tendsto (fun j : ℕ => π / (2 * agmB a b (j + 1))) atTop (𝓝 (π / (2 * AGM a b))) :=
    tendsto_const_nhds.div ((tendsto_agmB_succ ha hb).const_mul 2) (by positivity)
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds htb hup)
    (le_of_tendsto_of_tendsto' hta tendsto_const_nhds hlow)

/-! ### The substitution `t = tan θ` and Gauss's theorem (4.68) -/

theorem tan_image_Ioo : Real.tan '' Ioo 0 (π / 2) = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨θ, ⟨h0, hπ⟩, rfl⟩
    exact Real.tan_pos_of_pos_of_lt_pi_div_two h0 hπ
  · intro hu
    refine ⟨Real.arctan u, ⟨Real.arctan_pos.mpr hu, Real.arctan_lt_pi_div_two u⟩,
      Real.tan_arctan u⟩

/-- The pointwise identity for `t = tan θ`, `0 < θ < π/2`. -/
theorem tan_kernel {k : ℝ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    |1 / Real.cos θ ^ 2| * agmKernel 1 k (Real.tan θ)
      = (Real.sqrt (Real.sin θ ^ 2 + k ^ 2 * Real.cos θ ^ 2))⁻¹ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  unfold agmKernel
  rw [Real.tan_eq_sin_div_cos]
  have e : ((Real.sin θ / Real.cos θ) ^ 2 + 1 ^ 2) * ((Real.sin θ / Real.cos θ) ^ 2 + k ^ 2)
      = (Real.sin θ ^ 2 + k ^ 2 * Real.cos θ ^ 2) / (Real.cos θ ^ 2) ^ 2 := by
    have hsc := Real.sin_sq_add_cos_sq θ
    field_simp
    linear_combination (Real.sin θ ^ 2 + k ^ 2 * Real.cos θ ^ 2) * hsc
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity),
    abs_of_pos (by positivity)]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hs : 0 < Real.sqrt (Real.sin θ ^ 2 + k ^ 2 * Real.cos θ ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `J(1, k) = ∫_0^{π/2} dθ/√(cos²θ + k² sin²θ)`. -/
theorem agmIntegral_one_eq (k : ℝ) :
    agmIntegral 1 k = ∫ θ in (0 : ℝ)..(π / 2),
      (Real.sqrt (Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2))⁻¹ := by
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 (π / 2))
    (f := Real.tan) (f' := fun θ => 1 / Real.cos θ ^ 2) measurableSet_Ioo
    (fun θ hθ => (Real.hasDerivAt_tan
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne').hasDerivWithinAt)
    (Real.strictMonoOn_tan.injOn.mono (Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl))
    (agmKernel 1 k)
  rw [tan_image_Ioo] at hcov
  have h2 : ∫ θ in Ioo (0 : ℝ) (π / 2), |1 / Real.cos θ ^ 2| • agmKernel 1 k (Real.tan θ)
      = ∫ θ in Ioo (0 : ℝ) (π / 2), (Real.sqrt (Real.sin θ ^ 2 + k ^ 2 * Real.cos θ ^ 2))⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioo fun θ hθ => by rw [smul_eq_mul]; exact tan_kernel hθ
  have h3 := integral_comp_sub_left (fun θ : ℝ =>
    (Real.sqrt (Real.sin θ ^ 2 + k ^ 2 * Real.cos θ ^ 2))⁻¹) (π / 2) (a := 0) (b := π / 2)
  rw [sub_self, sub_zero] at h3
  unfold agmIntegral
  rw [hcov, h2, ← integral_Ioc_eq_integral_Ioo, ← integral_of_le Real.pi_div_two_pos.le, ← h3]
  refine integral_congr fun θ _ => ?_
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

/-- Gauss's theorem in the `θ`-form: `∫_0^{π/2} dθ/√(a² cos²θ + b² sin²θ) = π/(2 AGM(a, b))`. -/
theorem integral_inv_sqrt_eq_pi_div_AGM (ha : 0 < a) (hb : 0 < b) :
    ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
      = π / (2 * AGM a b) := by
  have hk : 0 < b / a := by positivity
  have h1 : ∀ θ : ℝ, (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
      = a⁻¹ * (Real.sqrt (Real.cos θ ^ 2 + (b / a) ^ 2 * Real.sin θ ^ 2))⁻¹ := by
    intro θ
    rw [show a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2
        = a ^ 2 * (Real.cos θ ^ 2 + (b / a) ^ 2 * Real.sin θ ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le, mul_inv]
  have hAGM : AGM a b = a * AGM 1 (b / a) := by
    rw [← AGM_smul ha one_pos hk, mul_one, show a * (b / a) = b by field_simp]
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, ← agmIntegral_one_eq,
    agmIntegral_eq_pi_div_AGM one_pos hk, hAGM]
  have : 0 < AGM 1 (b / a) := lt_of_lt_of_le (lt_min one_pos hk) (min_le_AGM one_pos hk)
  field_simp

/-- Gauss (4.68): `1/AGM(1, k) = (2/π) K'(k)` with `K'(k) = K(√(1 − k²))`, for `0 < k ≤ 1`. -/
theorem one_div_AGM_one {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) :
    1 / AGM 1 k = 2 / π * ellipticK (Real.sqrt (1 - k ^ 2)) := by
  have hK : ellipticK (Real.sqrt (1 - k ^ 2)) = agmIntegral 1 k := by
    rw [agmIntegral_one_eq]
    unfold ellipticK
    refine integral_congr fun θ _ => ?_
    rw [Real.sq_sqrt (by nlinarith), show 1 - (1 - k ^ 2) * Real.sin θ ^ 2
      = Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2 by
        linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq θ]
  rw [hK, agmIntegral_eq_pi_div_AGM one_pos hk]
  have : 0 < AGM 1 k := lt_of_lt_of_le (lt_min one_pos hk) (min_le_AGM one_pos hk)
  field_simp

end BZ

end Azurite
