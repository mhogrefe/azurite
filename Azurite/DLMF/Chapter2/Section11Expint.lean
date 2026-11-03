/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Mellin
import Azurite.DLMF.Chapter2.Section11
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# DLMF §2.11(ii): the generalized exponential integral on the Riemann surface of the logarithm

§2.11(ii) uses `E_p(z)` for `ph z` up to `7π/2`, so `z` lives on the Riemann surface of `ln`.
We use the logarithmic coordinate `w`: `z = e^w`, `ph z = ℑw`, and powers
`z^c = e^{cw}`. Then (DLMF 8.19.1–8.19.3)
`E_p(z) = z^{p−1} ∫_z^∞ e^{−t} t^{−p} dt`, and in the variable `t = e^v` the integrand is
`f_p(v) = exp(−e^v) e^{(1−p)v}` (`eiF`), which is entire in `v`. So

* `eiP p w = ∫_1^∞ e^{−t}t^{−p} dt − ∫_0^w f_p` (`= ∫_z^∞ e^{−t} t^{−p} dt`, the second integral
  along any path, `Complex.wedgeIntegral`),
* `genExpInt p w = e^{(p−1)w} eiP p w` (`= E_p(z)`), for every `p ∈ ℂ`, entire in `w`.

The integral representation 2.11.5 (`Re p > 0`, `|ph z| < π/2`) is `dlmf_2_11_5`
(`Section11ExpintLaplace.lean`); `genExpInt` is its analytic continuation in `w` (it is entire).

Here:
* `hasDerivAt_eiP`: `d/dw eiP p w = −f_p(w)`; `eiP_ofReal_eq`, `tendsto_eiP_atTop`.
* `eiP_small`: `eiP p v → 0` as `ℜv → ∞`, uniformly for `|ℑv| ≤ π/2 − η`.
* `eiP_succ`: `eiP p = e^{−z} z^{−p} − p eiP (p+1)` (integration by parts, 8.19.12), and
  `genExpInt_expansion`: `E_p(z) = (e^{−z}/z) ∑_{s<n} (−1)^s (p)_s z^{−s}
  + (−1)^n (p)_n z^{p−1} eiP (p+n)` exactly.
* `dlmf_8_19_18`: the connection formula with `m = 1`,
  `E_p(ze^{2πi}) = (2πi e^{pπi}/Γ(p)) z^{p−1} + E_p(z)`, from the `2πi`-periodicity of `f_p` up to
  the factor `e^{−2πip}`; the constant is `(e^{2πip} − 1)Γ(1 − p)` for `ℜp < 1` (shrinking the
  loop), then `= 2πi e^{pπi}/Γ(p)` by the reflection formula, for all `p` by `eiC_succ` and
  continuity in `p`.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### The integrand and its primitive -/

/-- `f_p(v) = exp(−e^v) e^{(1−p)v}`: `e^{−t} t^{−p} dt` in the variable `t = e^v`. -/
noncomputable def eiF (p v : ℂ) : ℂ := cexp (-cexp v) * cexp ((1 - p) * v)

theorem differentiable_eiF (p : ℂ) : Differentiable ℂ (eiF p) := by
  unfold eiF; fun_prop

theorem continuous_eiF_uncurry : Continuous fun q : ℂ × ℂ => eiF q.1 q.2 := by
  unfold eiF; fun_prop

theorem eiF_add_two_pi_I (p v : ℂ) :
    eiF p (v + 2 * π * I) = cexp (-(2 * π * I * p)) * eiF p v := by
  unfold eiF
  rw [Complex.exp_periodic v, show (1 - p) * (v + 2 * π * I) =
    (1 - p) * v + -(2 * π * I * p) + 2 * π * I by ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_two_pi_mul_I]
  ring

theorem norm_eiF (p : ℂ) (x y : ℝ) :
    ‖eiF p (x + y * I)‖ = Real.exp (-(Real.exp x * Real.cos y)) *
      Real.exp ((1 - p.re) * x + p.im * y) := by
  unfold eiF
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp [Complex.exp_re]
  · simp

theorem norm_eiF_ofReal (p : ℂ) (x : ℝ) :
    ‖eiF p x‖ = Real.exp (-Real.exp x) * Real.exp ((1 - p.re) * x) := by
  have := norm_eiF p x 0
  simpa using this

/-- `exp(−e^x) ≤ k! e^{−kx}`. -/
theorem exp_neg_exp_le (k : ℕ) (x : ℝ) :
    Real.exp (-Real.exp x) ≤ k.factorial * Real.exp (-(k * x)) := by
  have h := Real.pow_div_factorial_le_exp _ (Real.exp_pos x).le k
  rw [← Real.exp_nat_mul, div_le_iff₀ (by positivity)] at h
  rw [Real.exp_neg, Real.exp_neg]
  have h1 : 0 < Real.exp (Real.exp x) := Real.exp_pos _
  have h2 : 0 < Real.exp (k * x) := Real.exp_pos _
  rw [inv_le_iff_one_le_mul₀ h1]
  calc (1 : ℝ) = Real.exp (k * x) * (Real.exp (k * x))⁻¹ := (mul_inv_cancel₀ h2.ne').symm
    _ ≤ Real.exp (Real.exp x) * k.factorial * (Real.exp (k * x))⁻¹ := by gcongr
    _ = _ := by ring

/-- A uniform exponential bound: `|f_p(x)| ≤ k! e^{−bx}` with `b = k + ℜp − 1`. -/
theorem norm_eiF_ofReal_le (p : ℂ) (k : ℕ) (x : ℝ) :
    ‖eiF p x‖ ≤ k.factorial * Real.exp (-((k + p.re - 1) * x)) := by
  rw [norm_eiF_ofReal]
  calc Real.exp (-Real.exp x) * Real.exp ((1 - p.re) * x)
      ≤ k.factorial * Real.exp (-(k * x)) * Real.exp ((1 - p.re) * x) := by
        gcongr; exact exp_neg_exp_le k x
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- An index `k` with `k + ℜp − 1 ≥ 1`. -/
noncomputable def eiK (p : ℂ) : ℕ := ⌈|p.re|⌉₊ + 2

theorem eiK_spec (p : ℂ) : 1 ≤ (eiK p : ℝ) + p.re - 1 := by
  unfold eiK
  push_cast
  have := Nat.le_ceil |p.re|
  have := neg_abs_le p.re
  linarith

theorem integrableOn_eiF_Ioi (p : ℂ) (a : ℝ) :
    IntegrableOn (fun x : ℝ => eiF p x) (Ioi a) := by
  have hb := eiK_spec p
  refine ((exp_neg_integrableOn_Ioi a (by linarith : (0 : ℝ) < eiK p + p.re - 1)).const_mul
    ((eiK p).factorial : ℝ)).mono' ((differentiable_eiF p).continuous.comp
      continuous_ofReal).aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => ?_)
  refine (norm_eiF_ofReal_le p (eiK p) x).trans (le_of_eq ?_)
  ring_nf

/-- `A_p = ∫_0^∞ f_p = ∫_1^∞ e^{−t} t^{−p} dt`. -/
noncomputable def eiA (p : ℂ) : ℂ := ∫ x in Ioi (0 : ℝ), eiF p x

/-- `eiP p w = ∫_z^∞ e^{−t} t^{−p} dt`, `z = e^w`, on the Riemann surface of `ln`. -/
noncomputable def eiP (p w : ℂ) : ℂ := eiA p - wedgeIntegral 0 w (eiF p)

/-- **The generalized exponential integral** `E_p(z) = z^{p−1} ∫_z^∞ e^{−t} t^{−p} dt`
(DLMF 8.19.1, 8.19.2), `z = e^w` on the Riemann surface of the logarithm. -/
noncomputable def genExpInt (p w : ℂ) : ℂ := cexp ((p - 1) * w) * eiP p w

theorem hasDerivAt_wedgeIntegral_eiF (p w : ℂ) :
    HasDerivAt (fun w => wedgeIntegral 0 w (eiF p)) (eiF p w) w := by
  have h₂ := ((isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).2
    (differentiable_eiF p).differentiableOn).1
  have h₃ : IsConservativeOn (eiF p) (Metric.ball 0 (‖w‖ + 1)) := h₂.mono (subset_univ _)
  exact h₃.hasDerivAt_wedgeIntegral (differentiable_eiF p).continuous.continuousOn
    (by rw [Metric.mem_ball, dist_zero_right]; linarith)

theorem hasDerivAt_eiP (p w : ℂ) : HasDerivAt (eiP p) (-eiF p w) w :=
  (hasDerivAt_wedgeIntegral_eiF p w).const_sub _

theorem differentiable_eiP (p : ℂ) : Differentiable ℂ (eiP p) :=
  fun w => (hasDerivAt_eiP p w).differentiableAt

theorem differentiable_genExpInt (p : ℂ) : Differentiable ℂ (genExpInt p) := by
  unfold genExpInt
  exact (by fun_prop : Differentiable ℂ fun w => cexp ((p - 1) * w)).mul (differentiable_eiP p)

theorem wedgeIntegral_zero_ofReal (f : ℂ → ℂ) (x : ℝ) :
    wedgeIntegral 0 (x : ℂ) f = ∫ t in (0 : ℝ)..x, f t := by
  simp [wedgeIntegral]

theorem eiP_ofReal (p : ℂ) (x : ℝ) : eiP p x = eiA p - ∫ t in (0 : ℝ)..x, eiF p t := by
  rw [eiP, wedgeIntegral_zero_ofReal]

theorem tendsto_eiP_atTop (p : ℂ) : Tendsto (fun x : ℝ => eiP p x) atTop (𝓝 0) := by
  have h : Tendsto (fun i : ℝ => ∫ x in (0 : ℝ)..i, eiF p x) atTop (𝓝 (eiA p)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_eiF_Ioi p 0) tendsto_id
  have := (tendsto_const_nhds (x := eiA p)).sub h
  rw [sub_self] at this
  exact this.congr fun x => (eiP_ofReal p x).symm

/-! ### Decay in the right half of the principal sheet -/

/-- The vertical step: `eiP p v = eiP p (ℜv) − i ∫_0^{ℑv} f_p(ℜv + iy) dy`. -/
theorem eiP_vertical (p : ℂ) (x b : ℝ) :
    eiP p (x + b * I) = eiP p x - I * ∫ y in (0 : ℝ)..b, eiF p (x + y * I) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => eiP p (x + y * I)) (-eiF p (x + y * I) * I) y := by
    intro y
    have h1 : HasDerivAt (fun u : ℂ => (x : ℂ) + u * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)
    exact ((hasDerivAt_eiP p _).comp (y : ℂ) h1).comp_ofReal
  have hc : Continuous fun y : ℝ => -eiF p (x + y * I) * I := by
    have := (differentiable_eiF p).continuous
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
    (hc.intervalIntegrable 0 b)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  rw [show (∫ y in (0 : ℝ)..b, -eiF p (x + y * I) * I) =
    -(I * ∫ y in (0 : ℝ)..b, eiF p (x + y * I)) by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      congr 1; funext y; ring] at h
  linear_combination -h

/-- `|f_p(x + iy)| ≤ exp(−e^x sin η) e^{(1−ℜp)x + π|ℑp|}` for `|y| ≤ π/2 − η`. -/
theorem norm_eiF_strip_le (p : ℂ) {η x y : ℝ} (hη : 0 ≤ η) (hy : |y| ≤ π / 2 - η) :
    ‖eiF p (x + y * I)‖ ≤ Real.exp (-(Real.exp x * Real.sin η)) *
      Real.exp ((1 - p.re) * x + |p.im| * π) := by
  rw [norm_eiF]
  have hcos : Real.sin η ≤ Real.cos y := by
    rw [← Real.cos_abs y, ← Real.cos_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) (by linarith [Real.pi_pos]) hy
  have hpi : |y| ≤ π := by linarith [Real.pi_pos]
  refine mul_le_mul (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) (by positivity)
    (by positivity)
  · exact neg_le_neg (mul_le_mul_of_nonneg_left hcos (Real.exp_pos x).le)
  · have : p.im * y ≤ |p.im| * π :=
      calc p.im * y ≤ |p.im * y| := le_abs_self _
        _ = |p.im| * |y| := abs_mul _ _
        _ ≤ |p.im| * π := mul_le_mul_of_nonneg_left hpi (abs_nonneg _)
    linarith

theorem tendsto_strip_bound (p : ℂ) {η : ℝ} (hη : 0 < η) (hη' : η < π / 2) :
    Tendsto (fun x : ℝ => π * (Real.exp (-(Real.exp x * Real.sin η)) *
      Real.exp ((1 - p.re) * x + |p.im| * π))) atTop (𝓝 0) := by
  have hs : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη (by linarith)
  set k := eiK p
  have hk := eiK_spec p
  -- `exp(−e^x sin η) ≤ k! e^{−k(x + ln sin η)}`
  have hb : ∀ x : ℝ, Real.exp (-(Real.exp x * Real.sin η)) ≤
      k.factorial * Real.exp (-(k * (x + Real.log (Real.sin η)))) := fun x => by
    have := exp_neg_exp_le k (x + Real.log (Real.sin η))
    rwa [Real.exp_add, Real.exp_log hs] at this
  have hlim : Tendsto (fun x : ℝ => π * (k.factorial * Real.exp (-(k * (x +
      Real.log (Real.sin η)))) * Real.exp ((1 - p.re) * x + |p.im| * π))) atTop (𝓝 0) := by
    have e : ∀ x : ℝ, π * (k.factorial * Real.exp (-(k * (x + Real.log (Real.sin η)))) *
        Real.exp ((1 - p.re) * x + |p.im| * π)) =
        π * k.factorial * Real.exp (-(k * Real.log (Real.sin η)) + |p.im| * π) *
          Real.exp (-((k + p.re - 1) * x)) := fun x => by
      rw [mul_assoc (π * k.factorial), ← Real.exp_add, mul_assoc, mul_assoc, ← Real.exp_add]
      ring_nf
    simp only [e]
    rw [show (0 : ℝ) = π * k.factorial * Real.exp (-(k * Real.log (Real.sin η)) + |p.im| * π) * 0
      by ring]
    refine tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ?_)
    exact tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by linarith))
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) hlim
  gcongr
  exact hb x

/-- **Decay**: `eiP p v → 0` as `ℜv → ∞` uniformly for `|ℑv| ≤ π/2 − η`. -/
theorem eiP_small (p : ℂ) {η : ℝ} (hη : 0 < η) (hη' : η < π / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ v : ℂ, X ≤ v.re → |v.im| ≤ π / 2 - η → ‖eiP p v‖ ≤ ε := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp ((tendsto_eiP_atTop p).norm.eventually
    (gt_mem_nhds (show ‖(0 : ℂ)‖ < ε / 2 by simpa using half_pos hε)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp ((tendsto_strip_bound p hη hη').eventually
    (gt_mem_nhds (half_pos hε)))
  refine ⟨max X₁ X₂, fun v hv hvi => ?_⟩
  have hv' : v = (v.re : ℂ) + (v.im : ℂ) * I := (Complex.re_add_im v).symm
  rw [hv', eiP_vertical]
  have hint : ‖∫ y in (0 : ℝ)..v.im, eiF p (v.re + y * I)‖ ≤
      (Real.exp (-(Real.exp v.re * Real.sin η)) * Real.exp ((1 - p.re) * v.re + |p.im| * π)) *
        |v.im - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
    refine norm_eiF_strip_le p hη.le ?_
    rcases Set.mem_uIoc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_le] at hvi ⊢; constructor <;> linarith
    · rw [abs_le] at hvi ⊢; constructor <;> linarith
  have h1 := hX₁ v.re (le_of_max_le_left hv)
  have h2 := hX₂ v.re (le_of_max_le_right hv)
  have him : |v.im| ≤ π := by linarith [Real.pi_pos]
  have hpos : 0 ≤ Real.exp (-(Real.exp v.re * Real.sin η)) *
      Real.exp ((1 - p.re) * v.re + |p.im| * π) := by positivity
  calc ‖eiP p v.re - I * ∫ y in (0 : ℝ)..v.im, eiF p (v.re + y * I)‖
      ≤ ‖eiP p v.re‖ + ‖∫ y in (0 : ℝ)..v.im, eiF p (v.re + y * I)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add h1.le (hint.trans ?_)
        rw [sub_zero]
        calc _ ≤ (Real.exp (-(Real.exp v.re * Real.sin η)) *
              Real.exp ((1 - p.re) * v.re + |p.im| * π)) * π :=
              mul_le_mul_of_nonneg_left him hpos
          _ ≤ ε / 2 := by linarith
    _ = ε := by ring

/-! ### Integration by parts -/

theorem eiF_eq (p w : ℂ) : eiF p w = cexp (-cexp w) * cexp w * cexp (-(p * w)) := by
  unfold eiF
  rw [mul_assoc (cexp (-cexp w)), ← Complex.exp_add w]
  congr 2
  ring

/-- **8.19.12** on the Riemann surface: `∫_z^∞ e^{−t}t^{−p} dt = e^{−z}z^{−p} − p ∫_z^∞ e^{−t}
t^{−p−1} dt`. -/
theorem eiP_succ (p w : ℂ) :
    eiP p w = cexp (-cexp w) * cexp (-(p * w)) - p * eiP (p + 1) w := by
  set D : ℂ → ℂ := fun w => eiP p w - cexp (-cexp w) * cexp (-(p * w)) + p * eiP (p + 1) w
  have hD : ∀ w, HasDerivAt D 0 w := by
    intro w
    have h1 : HasDerivAt (fun w => cexp (-cexp w) * cexp (-(p * w)))
        (cexp (-cexp w) * (-cexp w) * cexp (-(p * w)) +
          cexp (-cexp w) * (cexp (-(p * w)) * (-p))) w := by
      have ha : HasDerivAt (fun w => cexp (-cexp w)) (cexp (-cexp w) * (-cexp w)) w := by
        simpa using ((Complex.hasDerivAt_exp w).neg).cexp
      have hb : HasDerivAt (fun w => cexp (-(p * w))) (cexp (-(p * w)) * (-p)) w := by
        simpa using (((hasDerivAt_id w).const_mul p).neg).cexp
      exact ha.mul hb
    have := ((hasDerivAt_eiP p w).sub h1).add ((hasDerivAt_eiP (p + 1) w).const_mul p)
    convert this using 1
    rw [eiF_eq, eiF_eq, show -((p + 1) * w) = -(p * w) + -w by ring, Complex.exp_add,
      Complex.exp_neg w]
    field_simp
    ring
  have hconst : ∀ a b, D a = D b := is_const_of_deriv_eq_zero
    (fun w => (hD w).differentiableAt) (fun w => (hD w).deriv)
  have hlim : Tendsto (fun x : ℝ => D x) atTop (𝓝 0) := by
    have h1 := tendsto_eiP_atTop p
    have h2 := (tendsto_eiP_atTop (p + 1)).const_mul p
    have h3 : Tendsto (fun x : ℝ => cexp (-cexp x) * cexp (-(p * x))) atTop (𝓝 0) := by
      have := tendsto_eiP_atTop p
      refine squeeze_zero_norm (fun x : ℝ => ?_) ((tendsto_strip_bound
        (p + 1) (η := π / 4) (by positivity) (by linarith [Real.pi_pos])).comp
        tendsto_id |>.congr fun x => rfl)
      simp only [Function.comp_apply, id]
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
      have hs : Real.sin (π / 4) ≤ 1 := Real.sin_le_one _
      have hp : 0 ≤ |(p + 1).im| * π := by positivity
      simp only [Complex.neg_re, Complex.exp_ofReal_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, Complex.add_re, Complex.one_re]
      calc Real.exp (-Real.exp x) * Real.exp (-(p.re * x))
          ≤ 1 * (Real.exp (-(Real.exp x * Real.sin (π / 4))) *
            Real.exp ((1 - (p.re + 1)) * x + |(p + 1).im| * π)) := by
            rw [one_mul]
            gcongr
            · nlinarith [Real.exp_pos x, Real.sin_pos_of_pos_of_lt_pi (x := π / 4)
                (by positivity) (by linarith [Real.pi_pos])]
            · linarith
        _ ≤ π * (Real.exp (-(Real.exp x * Real.sin (π / 4))) *
            Real.exp ((1 - (p + 1).re) * x + |(p + 1).im| * π)) := by
            simp only [Complex.add_re, Complex.one_re]
            gcongr
            linarith [Real.two_le_pi]
    have := (h1.sub h3).add h2
    rw [sub_zero, mul_zero, add_zero] at this
    exact this
  have hc : Tendsto (fun x : ℝ => D x) atTop (𝓝 (D w)) := by
    simp only [hconst _ w]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique hc hlim
  simp only [D] at this
  linear_combination this

/-- Iterated integration by parts: `eiP p = e^{−z} ∑_{s<n} (−1)^s (p)_s z^{−p−s}
+ (−1)^n (p)_n eiP (p+n)`. -/
theorem eiP_expansion (p w : ℂ) (n : ℕ) :
    eiP p w = cexp (-cexp w) * ∑ s ∈ Finset.range n,
        (-1) ^ s * (ascPochhammer ℂ s).eval p * cexp (-((p + s) * w)) +
      (-1) ^ n * (ascPochhammer ℂ n).eval p * eiP (p + n) w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, eiP_succ (p + n) w, Finset.sum_range_succ, ascPochhammer_succ_eval]
    push_cast
    rw [show p + n + 1 = p + (n + 1) by ring]
    ring

/-- **2.11.6, exact form**: `E_p(z) = (e^{−z}/z) ∑_{s<n} (−1)^s (p)_s/z^s
+ (−1)^n (p)_n z^{p−1} eiP (p+n) w`, `z = e^w`. -/
theorem genExpInt_expansion (p w : ℂ) (n : ℕ) :
    genExpInt p w = cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
        (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s +
      (-1) ^ n * (ascPochhammer ℂ n).eval p * (cexp ((p - 1) * w) * eiP (p + n) w) := by
  rw [genExpInt, eiP_expansion p w n, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    have e : cexp ((p - 1) * w) * cexp (-((p + s) * w)) = 1 / (cexp w * cexp w ^ s) := by
      rw [← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add, one_div,
        ← Complex.exp_neg]
      congr 1; ring
    calc cexp ((p - 1) * w) * (cexp (-cexp w) * ((-1) ^ s * (ascPochhammer ℂ s).eval p *
          cexp (-((p + s) * w))))
        = cexp (-cexp w) * ((-1) ^ s * (ascPochhammer ℂ s).eval p) *
          (cexp ((p - 1) * w) * cexp (-((p + s) * w))) := by ring
      _ = _ := by rw [e]; field_simp
  · ring

/-! ### The connection formula -/

/-- The connection constant `e^{2πip} eiP p (w + 2πi) − eiP p w` (independent of `w`). -/
noncomputable def eiC (p : ℂ) : ℂ := cexp (2 * π * I * p) * eiP p (2 * π * I) - eiP p 0

/-- The value of the connection constant: `2πi e^{pπi}/Γ(p)`. -/
noncomputable def connConst (p : ℂ) : ℂ := 2 * π * I * cexp (π * I * p) / Complex.Gamma p

theorem exp_two_pi_I_mul_neg (p : ℂ) :
    cexp (2 * π * I * p) * cexp (-(2 * π * I * p)) = 1 := by
  rw [← Complex.exp_add]; simp

theorem eiC_eq (p w : ℂ) :
    cexp (2 * π * I * p) * eiP p (w + 2 * π * I) - eiP p w = eiC p := by
  set D : ℂ → ℂ := fun w => cexp (2 * π * I * p) * eiP p (w + 2 * π * I) - eiP p w
  have hD : ∀ w, HasDerivAt D 0 w := fun w => by
    have h1 := ((hasDerivAt_eiP p (w + 2 * π * I)).comp w
      ((hasDerivAt_id w).add_const (2 * π * I))).const_mul (cexp (2 * π * I * p))
    have := h1.sub (hasDerivAt_eiP p w)
    convert this using 1
    · rfl
    rw [eiF_add_two_pi_I]
    linear_combination (eiF p w) * exp_two_pi_I_mul_neg p
  have hc := is_const_of_deriv_eq_zero (fun w => (hD w).differentiableAt)
    (fun w => (hD w).deriv) w 0
  simp only [D, zero_add] at hc
  rw [hc, eiC]

theorem genExpInt_add_two_pi_I (p w : ℂ) :
    genExpInt p (w + 2 * π * I) = genExpInt p w + eiC p * cexp ((p - 1) * w) := by
  have h := eiC_eq p w
  have e : cexp ((p - 1) * (w + 2 * π * I)) = cexp ((p - 1) * w) * cexp (2 * π * I * p) := by
    rw [show (p - 1) * (w + 2 * π * I) = ((p - 1) * w + 2 * π * I * p) + -(2 * π * I) by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one,
      Complex.exp_add]
  unfold genExpInt
  rw [e]
  linear_combination cexp ((p - 1) * w) * h

theorem eiC_succ (p : ℂ) : eiC p = -p * eiC (p + 1) := by
  unfold eiC
  rw [eiP_succ p (2 * π * I), eiP_succ p 0, Complex.exp_two_pi_mul_I, mul_zero, neg_zero,
    Complex.exp_zero, show 2 * π * I * (p + 1) = 2 * π * I * p + 2 * π * I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
    show -(p * (2 * π * I)) = -(2 * π * I * p) by ring]
  linear_combination cexp (-1) * exp_two_pi_I_mul_neg p

/-- `∫_ℝ f_p = ∫_0^∞ e^{−t} t^{−p} dt = Γ(1 − p)` for `ℜp < 1`. -/
theorem integral_eiF_eq_Gamma {p : ℂ} (hp : p.re < 1) :
    ∫ x : ℝ, eiF p x = Complex.Gamma (1 - p) := by
  rw [Complex.Gamma_eq_integral (by simp; linarith), Complex.GammaIntegral, ← integral_comp_exp]
  congr 1
  funext x
  rw [Complex.real_smul, ofReal_exp_cpow, eiF, Complex.ofReal_exp, Complex.ofReal_exp]
  push_cast
  simp only [← Complex.exp_add]
  congr 1
  ring

theorem integrableOn_eiF_Iic {p : ℂ} (hp : p.re < 1) (b : ℝ) :
    IntegrableOn (fun x : ℝ => eiF p x) (Iic b) := by
  refine (integrableOn_exp_mul_Iic (by linarith : (0 : ℝ) < 1 - p.re) b).mono'
    ((differentiable_eiF p).continuous.comp continuous_ofReal).aestronglyMeasurable.restrict
    (Eventually.of_forall fun x => ?_)
  rw [norm_eiF_ofReal]
  calc Real.exp (-Real.exp x) * Real.exp ((1 - p.re) * x) ≤ 1 * Real.exp ((1 - p.re) * x) := by
        gcongr; rw [Real.exp_le_one_iff]; linarith [Real.exp_pos x]
    _ = _ := one_mul _

/-- The loop shrinks to `0`: for `ℜp < 1` the constant is `(e^{2πip} − 1) Γ(1 − p)`. -/
theorem eiC_of_re_lt_one {p : ℂ} (hp : p.re < 1) :
    eiC p = (cexp (2 * π * I * p) - 1) * Complex.Gamma (1 - p) := by
  set V : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..2 * π, eiF p (x + y * I)
  have hform : ∀ x : ℝ, eiC p = (cexp (2 * π * I * p) - 1) * eiP p x -
      cexp (2 * π * I * p) * I * V x := fun x => by
    rw [← eiC_eq p x, show (x : ℂ) + 2 * π * I = x + ((2 * π : ℝ) : ℂ) * I by push_cast; ring,
      eiP_vertical]
    ring
  -- `eiP p x → Γ(1 − p)` as `x → −∞`
  have hP : Tendsto (fun x : ℝ => eiP p x) atBot (𝓝 (Complex.Gamma (1 - p))) := by
    have h := intervalIntegral_tendsto_integral_Iic 0 (integrableOn_eiF_Iic hp 0) tendsto_id
    have h2 := (tendsto_const_nhds (x := eiA p)).add h
    rw [show eiA p + ∫ x in Iic (0 : ℝ), eiF p x = Complex.Gamma (1 - p) by
      rw [add_comm, eiA, intervalIntegral.integral_Iic_add_Ioi (integrableOn_eiF_Iic hp 0)
        (integrableOn_eiF_Ioi p 0), integral_eiF_eq_Gamma hp] ] at h2
    refine h2.congr fun x => ?_
    rw [eiP_ofReal, intervalIntegral.integral_symm]
    simp only [id]
    ring
  -- the vertical integral tends to `0`
  have hV : Tendsto V atBot (𝓝 0) := by
    have hb : ∀ x : ℝ, x ≤ 0 → ‖V x‖ ≤ Real.exp 1 * Real.exp (|p.im| * (2 * π)) *
        (2 * π) * Real.exp ((1 - p.re) * x) := fun x hx => by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
        (f := fun y : ℝ => eiF p (x + y * I))
        (C := Real.exp 1 * Real.exp (|p.im| * (2 * π)) * Real.exp ((1 - p.re) * x))
        (fun y hy => by
          rw [norm_eiF]
          have hy' : y ∈ Icc 0 (2 * π) := by
            rcases Set.mem_uIoc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1.le, h2⟩
            · exfalso; linarith [Real.pi_pos]
          have h1 : -(Real.exp x * Real.cos y) ≤ 1 := by
            have := Real.neg_one_le_cos y
            have := Real.exp_le_one_iff.mpr hx
            nlinarith [Real.exp_pos x, Real.cos_le_one y]
          have h2 : p.im * y ≤ |p.im| * (2 * π) := by
            calc p.im * y ≤ |p.im * y| := le_abs_self _
              _ = |p.im| * |y| := abs_mul _ _
              _ ≤ |p.im| * (2 * π) := by
                rw [abs_of_nonneg hy'.1]; exact mul_le_mul_of_nonneg_left hy'.2 (abs_nonneg _)
          calc Real.exp (-(Real.exp x * Real.cos y)) * Real.exp ((1 - p.re) * x + p.im * y)
              ≤ Real.exp 1 * (Real.exp ((1 - p.re) * x) * Real.exp (|p.im| * (2 * π))) := by
                rw [Real.exp_add]
                gcongr
            _ = _ := by ring)
      rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
      exact this.trans (le_of_eq (by ring))
    have hlim : Tendsto (fun x : ℝ => Real.exp 1 * Real.exp (|p.im| * (2 * π)) * (2 * π) *
        Real.exp ((1 - p.re) * x)) atBot (𝓝 0) := by
      rw [show (0 : ℝ) = Real.exp 1 * Real.exp (|p.im| * (2 * π)) * (2 * π) * 0 by ring]
      exact tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atBot (by linarith)))
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_le_atBot 0] with x hx using hb x hx
  have hlim := (hP.const_mul (cexp (2 * π * I * p) - 1)).sub
    (hV.const_mul (cexp (2 * π * I * p) * I))
  rw [mul_zero, sub_zero] at hlim
  have hc : Tendsto (fun x : ℝ => (cexp (2 * π * I * p) - 1) * eiP p x -
      cexp (2 * π * I * p) * I * V x) atBot (𝓝 (eiC p)) := by
    simp only [← hform]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hc hlim

/-- `(e^{2πip} − 1) Γ(1 − p) = 2πi e^{pπi}/Γ(p)` for `ℜp < 1` (reflection formula). -/
theorem reflection_connConst {p : ℂ} (hp : p.re < 1) :
    (cexp (2 * π * I * p) - 1) * Complex.Gamma (1 - p) = connConst p := by
  unfold connConst
  by_cases hs : Complex.sin (π * p) = 0
  · obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hpk : p = k := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk
      linear_combination hk
    have hk0 : k ≤ 0 := by
      have : (k : ℝ) < 1 := by have := congrArg Complex.re hpk; simp at this; linarith
      exact_mod_cast Int.lt_add_one_iff.mp (by exact_mod_cast this)
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -n := ⟨k.natAbs, by omega⟩
    have hG : Complex.Gamma p = 0 := by rw [hpk]; push_cast; exact Complex.Gamma_neg_nat_eq_zero n
    have he : cexp (2 * π * I * p) = 1 := by
      rw [hpk, show 2 * π * I * ((-(n : ℤ) : ℤ) : ℂ) = ((-(n : ℤ) : ℤ) : ℂ) * (2 * π * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [he, hG]; simp
  · have hG : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero fun m hm => hs (by
      rw [hm, show (π : ℂ) * -(m : ℂ) = ((-(m : ℤ) : ℤ) : ℂ) * π by push_cast; ring]
      exact Complex.sin_int_mul_pi _)
    have hr := Complex.Gamma_mul_Gamma_one_sub p
    have h2 := Complex.two_sin (π * p)
    have he : cexp (2 * π * I * p) = cexp (π * I * p) * cexp (π * I * p) := by
      rw [← Complex.exp_add]; ring_nf
    have hm : cexp (-(π * p) * I) * cexp (π * I * p) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    rw [show cexp (π * p * I) = cexp (π * I * p) by ring_nf] at h2
    have hG1 : Complex.Gamma (1 - p) = π / Complex.sin (π * p) / Complex.Gamma p := by
      rw [← hr]; field_simp
    have hcm : cexp (π * I * p) * cexp (π * I * p) - 1 =
        2 * I * Complex.sin (π * p) * cexp (π * I * p) := by
      linear_combination hm + (-I * cexp (π * I * p)) * h2 +
        (-(cexp (-(π * p) * I) - cexp (π * I * p)) * cexp (π * I * p)) * Complex.I_sq
    rw [hG1, he, hcm]
    field_simp

theorem connConst_succ (q : ℂ) : connConst q = -q * connConst (q + 1) := by
  by_cases hq : q = 0
  · subst hq
    simp [connConst, Complex.Gamma_zero]
  unfold connConst
  rw [Complex.Gamma_add_one q hq, show π * I * (q + 1) = π * I * q + π * I by ring,
    Complex.exp_add, show (π : ℂ) * I = (π : ℂ) * I from rfl]
  have : cexp (π * I) = -1 := Complex.exp_pi_mul_I
  rw [this]
  by_cases hG : Complex.Gamma q = 0
  · simp [hG]
  field_simp

/-- The connection constant off the positive integers, by `eiC_succ` from `ℜp < 1`. -/
theorem eiC_eq_connConst_aux : ∀ n : ℕ, ∀ p : ℂ, p.re < n + 1 → (∀ k : ℕ, p ≠ k + 1) →
    eiC p = connConst p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    rw [eiC_of_re_lt_one (by simpa using hp), reflection_connConst (by simpa using hp)]
  | succ n ih =>
    intro p hp hk
    by_cases hlt : p.re < n + 1
    · exact ih p hlt hk
    set q := p - 1
    have hq0 : q ≠ 0 := fun h => hk 0 (by simp only [q] at h; push_cast; linear_combination h)
    have hqk : ∀ k : ℕ, q ≠ k + 1 := fun k h => hk (k + 1) (by
      simp only [q] at h; push_cast; linear_combination h)
    have hqre : q.re < n + 1 := by
      simp only [q, Complex.sub_re, Complex.one_re]; push_cast at hp; linarith
    have h1 := eiC_succ q
    have h2 := connConst_succ q
    rw [ih q hqre hqk, show q + 1 = p by ring] at h1
    rw [show q + 1 = p by ring] at h2
    have : -q * eiC p = -q * connConst p := by rw [← h1, ← h2]
    exact mul_left_cancel₀ (neg_ne_zero.mpr hq0) this

theorem continuous_eiA : Continuous eiA := by
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  set k := eiK p₀ + 1
  have hk := eiK_spec p₀
  show ContinuousAt (fun p => ∫ x in Ioi (0 : ℝ), eiF p x) p₀
  refine continuousAt_of_dominated
    (bound := fun x : ℝ => (k.factorial : ℝ) * Real.exp (-1 * x))
    (Eventually.of_forall fun p => ((differentiable_eiF p).continuous.comp
      continuous_ofReal).aestronglyMeasurable.restrict) ?_
    ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _) ?_
  · filter_upwards [Metric.ball_mem_nhds p₀ one_pos] with p hp
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hre : p₀.re - 1 ≤ p.re := by
      have := Complex.abs_re_le_norm (p - p₀)
      rw [Metric.mem_ball, dist_eq_norm] at hp
      rw [Complex.sub_re, abs_le] at this
      linarith [this.1]
    refine (norm_eiF_ofReal_le p k x).trans ?_
    gcongr
    have hx' : 0 < x := hx
    simp only [k]; push_cast
    nlinarith
  · exact Eventually.of_forall fun x => ((continuous_eiF_uncurry.comp
      (continuous_id.prodMk continuous_const)).continuousAt (x := p₀))

theorem continuous_eiC : Continuous eiC := by
  have h0 : ∀ p, eiP p 0 = eiA p := fun p => by simp [eiP, wedgeIntegral]
  have h1 : ∀ p, eiP p (2 * π * I) =
      eiA p - I * ∫ y in (0 : ℝ)..2 * π, eiF p (y * I) := fun p => by
    simp [eiP, wedgeIntegral]
  have hc : Continuous fun p : ℂ => ∫ y in (0 : ℝ)..2 * π, eiF p (y * I) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun p (y : ℝ) => eiF p (y * I)) ?_ _ _
    exact continuous_eiF_uncurry.comp
      (by fun_prop : Continuous fun q : ℂ × ℝ => (q.1, (q.2 : ℂ) * I))
  have : eiC = fun p => cexp (2 * π * I * p) * (eiA p - I * ∫ y in (0 : ℝ)..2 * π,
      eiF p (y * I)) - eiA p := by
    funext p; rw [eiC, h0, h1]
  rw [this]
  have := continuous_eiA
  fun_prop

theorem continuous_connConst : Continuous connConst := by
  have h := Complex.differentiable_one_div_Gamma.continuous
  unfold connConst
  simp only [div_eq_mul_inv]
  fun_prop

/-- **The connection constant** `e^{2πip} eiP p (w + 2πi) − eiP p w = 2πi e^{pπi}/Γ(p)`. -/
theorem eiC_eq_connConst (p : ℂ) : eiC p = connConst p := by
  by_cases hk : ∀ k : ℕ, p ≠ k + 1
  · obtain ⟨n, hn⟩ := exists_nat_gt p.re
    exact eiC_eq_connConst_aux n p (by linarith) hk
  push Not at hk
  obtain ⟨m, rfl⟩ := hk
  set u : ℕ → ℂ := fun j => ((m + 1 + 1 / (j + 2 : ℝ) : ℝ) : ℂ)
  have hu : Tendsto u atTop (𝓝 ((m : ℂ) + 1)) := by
    have : Tendsto (fun j : ℕ => (m + 1 + 1 / ((j : ℝ) + 2) : ℝ)) atTop (𝓝 ((m : ℝ) + 1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop))
    rw [add_zero] at this
    have h3 := (Complex.continuous_ofReal.tendsto _).comp this
    have h4 : (((m : ℝ) + 1 : ℝ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    rw [h4] at h3
    exact h3
  have heq : ∀ j, eiC (u j) = connConst (u j) := fun j => by
    refine eiC_eq_connConst_aux (m + 2) (u j) ?_ fun k hk => ?_
    · simp only [u, Complex.ofReal_re]
      have : 1 / ((j : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
      push_cast; linarith
    · have hre := congrArg Complex.re hk
      simp only [u, Complex.ofReal_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at hre
      have h0 : (0 : ℝ) < 1 / ((j : ℝ) + 2) := by positivity
      have h1 : 1 / ((j : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
      have hd : ((k : ℤ) - m : ℤ) = (1 / ((j : ℝ) + 2) : ℝ) := by push_cast; linarith
      have a : (0 : ℝ) < ((k : ℤ) - m : ℤ) := hd ▸ h0
      have b : (((k : ℤ) - m : ℤ) : ℝ) < 1 := hd ▸ h1
      have a' : (0 : ℤ) < (k : ℤ) - m := by exact_mod_cast a
      have b' : (k : ℤ) - m < 1 := by exact_mod_cast b
      omega
  have h1 := (continuous_eiC.tendsto _).comp hu
  have h2 := (continuous_connConst.tendsto _).comp hu
  exact tendsto_nhds_unique h1 (h2.congr fun j => (heq j).symm)

/-- **DLMF 8.19.18** with `m = 1`: `E_p(ze^{2πi}) = (2πi e^{pπi}/Γ(p)) z^{p−1} + E_p(z)`
(`z = e^w`, `ze^{2πi} = e^{w + 2πi}`, `z^{p−1} = e^{(p−1)w}`). -/
theorem dlmf_8_19_18 (p w : ℂ) :
    genExpInt p (w + 2 * π * I) =
      2 * π * I * cexp (p * π * I) / Complex.Gamma p * cexp ((p - 1) * w) + genExpInt p w := by
  rw [genExpInt_add_two_pi_I, eiC_eq_connConst, connConst,
    show (π : ℂ) * I * p = p * π * I by ring]
  ring

end Azurite.DLMF
