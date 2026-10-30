/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Parseval
import Azurite.DLMF.Chapter1.Section14Inversion

/-!
# DLMF §1.14(ii): Fourier Cosine and Sine Transforms

Formalizations of <https://dlmf.nist.gov/1.14#ii>, for complex-valued `f` on `[0, ∞)` (DLMF's
real case included).

**Method.** The DLMF transform (1.14.1) of the even extension `f(|t|)` is `𝓕_c(f)`
(`dlmfFourier_evenExt`), and that of the odd extension is `i 𝓕_s(f)` (`dlmfFourier_oddExt`). The
symmetric partial integrals of §1.14(i) then become `2 ∫₀ᴿ` (`intervalIntegral_eq_halves`), and
whole-line integrals of even functions become `2 ∫₀^∞` (`integral_eq_halves`).

**Results.**
* 1.14.9–1.14.10: `dlmfFourierCos`, `dlmfFourierSin`; parity (`dlmfFourierCos_neg`,
  `dlmfFourierSin_neg`) and continuity for `f` integrable on `(0, ∞)`.
* 1.14.11–1.14.12 (`dlmf_1_14_11`, `dlmf_1_14_12`): for `f` absolutely integrable on `[0, ∞)` and
  of bounded variation near `u > 0`, `√(2/π) ∫₀^∞ F_c(x) cos(ux) dx` and
  `√(2/π) ∫₀^∞ F_s(x) sin(ux) dx` (limits of `∫₀^R`) equal `½(f(u+) + f(u−))`. This is derived
  from 1.14.3.
* 1.14.13–1.14.16 (`dlmf_1_14_13`–`dlmf_1_14_16`): Parseval for `f`, `g` absolutely and square
  integrable on `[0, ∞)`, derived from 1.14.7.
-/

open MeasureTheory Filter Topology Set Complex

namespace Azurite.DLMF

/-! ### Halves of the line -/

theorem integrableOn_Iic_of_comp_neg {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (h : IntegrableOn (fun x => g (-x)) (Ioi 0)) : IntegrableOn g (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi h

theorem integrable_of_halves {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (h1 : IntegrableOn g (Ioi 0)) (h2 : IntegrableOn (fun x => g (-x)) (Ioi 0)) : Integrable g := by
  have := (integrableOn_Iic_of_comp_neg h2).union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem integral_eq_halves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E}
    (hg : Integrable g) : ∫ x, g x = ∫ x in Ioi 0, (g x + g (-x)) := by
  rw [integral_add hg.integrableOn (hg.comp_neg.integrableOn), integral_comp_neg_Ioi, neg_zero,
    add_comm, ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hg.integrableOn
      hg.integrableOn, Iic_union_Ioi, Measure.restrict_univ]

theorem intervalIntegral_eq_halves {g : ℝ → ℂ} (hg : Continuous g) (R : ℝ) :
    ∫ x in (-R)..R, g x = ∫ x in (0 : ℝ)..R, (g x + g (-x)) := by
  have hg' : Continuous fun x => g (-x) := hg.comp continuous_neg
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_add (hg.intervalIntegrable 0 R)
    (hg'.intervalIntegrable 0 R), intervalIntegral.integral_comp_neg (fun x => g x),
    neg_zero, add_comm]

/-! ### Definitions and the even and odd extensions -/

/-- **DLMF (1.14.9)**: `𝓕_c(f)(x) = √(2/π) ∫₀^∞ f(t) cos(xt) dt`. -/
noncomputable def dlmfFourierCos (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((√(2 / Real.pi) : ℝ) : ℂ) * ∫ t in Ioi 0, f t * ((Real.cos (x * t) : ℝ) : ℂ)

/-- **DLMF (1.14.10)**: `𝓕_s(f)(x) = √(2/π) ∫₀^∞ f(t) sin(xt) dt`. -/
noncomputable def dlmfFourierSin (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((√(2 / Real.pi) : ℝ) : ℂ) * ∫ t in Ioi 0, f t * ((Real.sin (x * t) : ℝ) : ℂ)

/-- The even extension `f(|t|)`. -/
def evenExt (f : ℝ → ℂ) (t : ℝ) : ℂ := f |t|

/-- The odd extension `sign(t) f(|t|)` (with value `f(0)` at `0`). -/
noncomputable def oddExt (f : ℝ → ℂ) (t : ℝ) : ℂ := if 0 ≤ t then f t else -f (-t)

theorem sqrt_two_div_pi : (2 : ℂ) * ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ = ((√(2 / Real.pi) : ℝ) : ℂ) := by
  have hπ := Real.pi_pos
  have h : √(2 / Real.pi) * √(2 * Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity), show 2 / Real.pi * (2 * Real.pi) = 2 ^ 2 by
      field_simp, Real.sqrt_sq (by norm_num)]
  have hs : (√(2 * Real.pi) : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hr : 2 * (√(2 * Real.pi))⁻¹ = √(2 / Real.pi) := by
    rw [mul_inv_eq_iff_eq_mul₀ hs]; exact h.symm
  have := congrArg (fun r : ℝ => (r : ℂ)) hr
  push_cast at this
  exact this

theorem integrable_evenExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (evenExt f) :=
  integrable_of_halves
    (hf.congr_fun (fun t ht => by
      simp only [evenExt, abs_of_pos (show (0 : ℝ) < t from ht)]) measurableSet_Ioi)
    (hf.congr_fun (fun t ht => by
      simp only [evenExt, abs_neg, abs_of_pos (show (0 : ℝ) < t from ht)]) measurableSet_Ioi)

theorem integrable_oddExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (oddExt f) :=
  integrable_of_halves (hf.congr_fun (fun t ht => by
      simp only [oddExt, (show (0 : ℝ) < t from ht).le, ↓reduceIte]) measurableSet_Ioi)
    (hf.neg.congr_fun (fun t ht => by
      have : ¬ (0 ≤ -t) := by simp only [not_le, neg_lt_zero]; exact ht
      simp only [oddExt, this, ↓reduceIte, neg_neg, Pi.neg_apply]) measurableSet_Ioi)

/-- `𝓕(f(|·|)) = 𝓕_c(f)`. -/
theorem dlmfFourier_evenExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    dlmfFourier (evenExt f) x = dlmfFourierCos f x := by
  rw [dlmfFourier, integral_eq_halves (integrable_mul_exp (integrable_evenExt hf) x),
    dlmfFourierCos, ← sqrt_two_div_pi, mul_comm (2 : ℂ), mul_assoc,
    ← integral_const_mul (2 : ℂ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  simp only [evenExt, abs_neg, abs_of_pos ht', ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- `𝓕(sign · f(|·|)) = i 𝓕_s(f)`. -/
theorem dlmfFourier_oddExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    dlmfFourier (oddExt f) x = I * dlmfFourierSin f x := by
  rw [dlmfFourier, integral_eq_halves (integrable_mul_exp (integrable_oddExt hf) x),
    dlmfFourierSin, ← sqrt_two_div_pi]
  rw [show ∀ c J : ℂ, I * (2 * c * J) = c * (2 * I * J) from fun c J => by ring,
    ← integral_const_mul (2 * I)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  have : ¬ (0 ≤ -t) := by simp only [not_le, neg_lt_zero]; exact ht'
  simp only [oddExt, ht'.le, this, ↓reduceIte, neg_neg, ofReal_sin, Complex.sin]
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem dlmfFourierCos_neg (f : ℝ → ℂ) (x : ℝ) : dlmfFourierCos f (-x) = dlmfFourierCos f x := by
  simp only [dlmfFourierCos, neg_mul, Real.cos_neg]

theorem dlmfFourierSin_neg (f : ℝ → ℂ) (x : ℝ) :
    dlmfFourierSin f (-x) = -dlmfFourierSin f x := by
  simp only [dlmfFourierSin, neg_mul, Real.sin_neg, ofReal_neg, mul_neg, integral_neg]

theorem continuous_dlmfFourierCos {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Continuous (dlmfFourierCos f) := by
  have := dlmf_1_14_i_continuous (integrable_evenExt hf)
  rwa [show dlmfFourier (evenExt f) = dlmfFourierCos f from funext (dlmfFourier_evenExt hf)]
    at this

theorem continuous_dlmfFourierSin {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) :
    Continuous (dlmfFourierSin f) := by
  have := (dlmf_1_14_i_continuous (integrable_oddExt hf)).mul (continuous_const (y := -I))
  refine this.congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [dlmfFourier_oddExt hf, mul_comm, ← mul_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I,
    neg_neg], one_mul]

/-! ### Inversion -/

theorem bv_of_eqOn {f g : ℝ → ℂ} {s : Set ℝ} (hf : BoundedVariationOn f s) (h : EqOn f g s) :
    BoundedVariationOn g s := by
  unfold BoundedVariationOn at *
  rwa [← eVariationOn.congr h]

/-- **DLMF (1.14.11)**: if `f` is absolutely integrable on `[0, ∞)` and of bounded variation near
`u > 0`, then `√(2/π) ∫₀^∞ 𝓕_c(f)(x) cos(ux) dx = ½(f(u+) + f(u−))`, the integral being the
limit of `∫₀^R`. -/
theorem dlmf_1_14_11 {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {u δ : ℝ} (hδ : 0 < δ)
    (hδu : δ < u) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] u) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] u) (𝓝 Lm)) :
    Tendsto (fun R : ℝ => ((√(2 / Real.pi) : ℝ) : ℂ) *
      ∫ x in (0 : ℝ)..R, dlmfFourierCos f x * ((Real.cos (u * x) : ℝ) : ℂ)) atTop
      (𝓝 ((Lp + Lm) / 2)) := by
  have hfe := integrable_evenExt hf
  have hpos : ∀ t ∈ Icc (u - δ) (u + δ), f t = evenExt f t := fun t ht => by
    simp only [evenExt, abs_of_pos (show 0 < t by linarith [ht.1])]
  have hev : ∀ᶠ t in 𝓝 u, f t = evenExt f t := by
    filter_upwards [Icc_mem_nhds (show u - δ < u by linarith) (show u < u + δ by linarith)]
      with t ht using hpos t ht
  have main := dlmf_1_14_3 hfe hδ (bv_of_eqOn hbv hpos)
    (hp.congr' (eventually_nhdsWithin_of_eventually_nhds hev))
    (hm.congr' (eventually_nhdsWithin_of_eventually_nhds hev))
  have hF : dlmfFourier (evenExt f) = dlmfFourierCos f := funext (dlmfFourier_evenExt hf)
  rw [hF] at main
  refine main.congr fun R => ?_
  rw [intervalIntegral_eq_halves (g := fun x : ℝ => dlmfFourierCos f x * cexp (-(I * x * u)))
    ((continuous_dlmfFourierCos hf).mul (by fun_prop)) R,
    ← sqrt_two_div_pi, mul_comm (2 : ℂ), mul_assoc,
    ← intervalIntegral.integral_const_mul (2 : ℂ)]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [dlmfFourierCos_neg, ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- **DLMF (1.14.12)**: the same for the sine transform,
`√(2/π) ∫₀^∞ 𝓕_s(f)(x) sin(ux) dx = ½(f(u+) + f(u−))`. -/
theorem dlmf_1_14_12 {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0)) {u δ : ℝ} (hδ : 0 < δ)
    (hδu : δ < u) (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] u) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] u) (𝓝 Lm)) :
    Tendsto (fun R : ℝ => ((√(2 / Real.pi) : ℝ) : ℂ) *
      ∫ x in (0 : ℝ)..R, dlmfFourierSin f x * ((Real.sin (u * x) : ℝ) : ℂ)) atTop
      (𝓝 ((Lp + Lm) / 2)) := by
  have hfo := integrable_oddExt hf
  have hpos : ∀ t ∈ Icc (u - δ) (u + δ), f t = oddExt f t := fun t ht => by
    simp only [oddExt, (show 0 ≤ t by linarith [ht.1]), ↓reduceIte]
  have hev : ∀ᶠ t in 𝓝 u, f t = oddExt f t := by
    filter_upwards [Icc_mem_nhds (show u - δ < u by linarith) (show u < u + δ by linarith)]
      with t ht using hpos t ht
  have main := dlmf_1_14_3 hfo hδ (bv_of_eqOn hbv hpos)
    (hp.congr' (eventually_nhdsWithin_of_eventually_nhds hev))
    (hm.congr' (eventually_nhdsWithin_of_eventually_nhds hev))
  have hF : dlmfFourier (oddExt f) = fun x => I * dlmfFourierSin f x :=
    funext (dlmfFourier_oddExt hf)
  rw [hF] at main
  beta_reduce at main
  refine main.congr fun R => ?_
  rw [intervalIntegral_eq_halves
    (g := fun x : ℝ => I * dlmfFourierSin f x * cexp (-(I * x * u)))
    ((continuous_const.mul (continuous_dlmfFourierSin hf)).mul (by fun_prop)) R,
    ← sqrt_two_div_pi, mul_comm (2 : ℂ), mul_assoc,
    ← intervalIntegral.integral_const_mul (2 : ℂ)]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [dlmfFourierSin_neg, ofReal_sin, Complex.sin]
  push_cast
  ring_nf

/-! ### Parseval -/

theorem memLp_two_of_halves {g : ℝ → ℂ} (hg : AEStronglyMeasurable g)
    (h1 : IntegrableOn (fun t => ‖g t‖ ^ 2) (Ioi 0))
    (h2 : IntegrableOn (fun t => ‖g (-t)‖ ^ 2) (Ioi 0)) : MemLp g 2 :=
  (memLp_two_iff_integrable_sq_norm hg).mpr (integrable_of_halves h1 h2)

theorem integrableOn_sq_of_memLp {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) :
    IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi 0) :=
  (memLp_two_iff_integrable_sq_norm hf.1).mp hf2

theorem memLp_evenExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) : MemLp (evenExt f) 2 := by
  have h := integrableOn_sq_of_memLp hf hf2
  refine memLp_two_of_halves (integrable_evenExt hf).1
    (h.congr_fun (fun t ht => by
      simp only [evenExt, abs_of_pos (show (0 : ℝ) < t from ht)]) measurableSet_Ioi)
    (h.congr_fun (fun t ht => by
      simp only [evenExt, abs_neg, abs_of_pos (show (0 : ℝ) < t from ht)]) measurableSet_Ioi)

theorem memLp_oddExt {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) : MemLp (oddExt f) 2 := by
  have h := integrableOn_sq_of_memLp hf hf2
  refine memLp_two_of_halves (integrable_oddExt hf).1
    (h.congr_fun (fun t ht => by
      simp only [oddExt, (show (0 : ℝ) < t from ht).le, ↓reduceIte]) measurableSet_Ioi)
    (h.congr_fun (fun t ht => by
      have : ¬ (0 ≤ -t) := by simp only [not_le, neg_lt_zero]; exact ht
      simp only [oddExt, this, ↓reduceIte, neg_neg, norm_neg]) measurableSet_Ioi)

theorem integrable_mul_of_sq {a b : ℝ → ℂ} (ha : MemLp a 2) (hb : MemLp b 2) :
    Integrable fun t => a t * b t := by
  refine Integrable.mono' (((ha.integrable_norm_pow (by norm_num)).add
    (hb.integrable_norm_pow (by norm_num))).div_const 2)
    (ha.aestronglyMeasurable.mul hb.aestronglyMeasurable)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖a t‖ - ‖b t‖)]

/-- **DLMF (1.14.13)**: `∫₀^∞ F_c G_c = ∫₀^∞ f g` for `f`, `g` absolutely and square integrable on
`[0, ∞)`. -/
theorem dlmf_1_14_13 {f g : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) (hg : IntegrableOn g (Ioi 0))
    (hg2 : MemLp g 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi 0, dlmfFourierCos f x * dlmfFourierCos g x = ∫ t in Ioi 0, f t * g t := by
  have hfe := integrable_evenExt hf
  have hge := integrable_evenExt hg
  have hfe2 := memLp_evenExt hf hf2
  have hge2 := memLp_evenExt hg hg2
  have h7 := dlmf_1_14_7 hfe hfe2 hge hge2
  simp only [dlmfFourier_evenExt hf, dlmfFourier_evenExt hg] at h7
  have hL : Integrable fun x => dlmfFourierCos f x * dlmfFourierCos g x := by
    have := integrable_dlmfFourier_mul hfe hfe2 hge hge2
    simpa only [dlmfFourier_evenExt hf, dlmfFourier_evenExt hg] using this
  have hR : Integrable fun t => evenExt f t * evenExt g (-t) := by
    have := integrable_mul_of_sq hfe2 hge2
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [evenExt, abs_neg]
  rw [integral_eq_halves hL, integral_eq_halves hR] at h7
  have e1 : ∫ x in Ioi 0, (dlmfFourierCos f x * dlmfFourierCos g x +
      dlmfFourierCos f (-x) * dlmfFourierCos g (-x)) =
      2 * ∫ x in Ioi 0, dlmfFourierCos f x * dlmfFourierCos g x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [dlmfFourierCos_neg]
    ring
  have e2 : ∫ t in Ioi 0, (evenExt f t * evenExt g (-t) + evenExt f (-t) * evenExt g (- -t)) =
      2 * ∫ t in Ioi 0, f t * g t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [evenExt, abs_neg, neg_neg, abs_of_pos (show (0 : ℝ) < t from ht)]
    ring
  rw [e1, e2] at h7
  exact mul_left_cancel₀ two_ne_zero h7

/-- **DLMF (1.14.14)**: `∫₀^∞ F_s G_s = ∫₀^∞ f g`. -/
theorem dlmf_1_14_14 {f g : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) (hg : IntegrableOn g (Ioi 0))
    (hg2 : MemLp g 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi 0, dlmfFourierSin f x * dlmfFourierSin g x = ∫ t in Ioi 0, f t * g t := by
  have hfo := integrable_oddExt hf
  have hgo := integrable_oddExt hg
  have hfo2 := memLp_oddExt hf hf2
  have hgo2 := memLp_oddExt hg hg2
  have h7 := dlmf_1_14_7 hfo hfo2 hgo hgo2
  simp only [dlmfFourier_oddExt hf, dlmfFourier_oddExt hg] at h7
  have hL : Integrable fun x => I * dlmfFourierSin f x * (I * dlmfFourierSin g x) := by
    have := integrable_dlmfFourier_mul hfo hfo2 hgo hgo2
    simpa only [dlmfFourier_oddExt hf, dlmfFourier_oddExt hg] using this
  have hR : Integrable fun t => oddExt f t * oddExt g (-t) := by
    have hg' : MemLp (fun t => oddExt g (-t)) 2 :=
      hgo2.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
    exact integrable_mul_of_sq hfo2 hg'
  rw [integral_eq_halves hL, integral_eq_halves hR] at h7
  have e1 : ∫ x in Ioi 0, (I * dlmfFourierSin f x * (I * dlmfFourierSin g x) +
      I * dlmfFourierSin f (-x) * (I * dlmfFourierSin g (-x))) =
      -2 * ∫ x in Ioi 0, dlmfFourierSin f x * dlmfFourierSin g x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [dlmfFourierSin_neg]
    ring_nf
    rw [I_sq]
    ring
  have e2 : ∫ t in Ioi 0, (oddExt f t * oddExt g (-t) + oddExt f (-t) * oddExt g (- -t)) =
      -2 * ∫ t in Ioi 0, f t * g t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have : ¬ (0 ≤ -t) := by simp only [not_le, neg_lt_zero]; exact ht'
    simp only [oddExt, ht'.le, this, ↓reduceIte, neg_neg]
    ring
  rw [e1, e2] at h7
  exact mul_left_cancel₀ (by norm_num) h7

/-- **DLMF (1.14.15)**: `∫₀^∞ (F_c)² = ∫₀^∞ f²`. -/
theorem dlmf_1_14_15 {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi 0, dlmfFourierCos f x ^ 2 = ∫ t in Ioi 0, f t ^ 2 := by
  simpa only [sq] using dlmf_1_14_13 hf hf2 hf hf2

/-- **DLMF (1.14.16)**: `∫₀^∞ (F_s)² = ∫₀^∞ f²`. -/
theorem dlmf_1_14_16 {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 0))
    (hf2 : MemLp f 2 (volume.restrict (Ioi 0))) :
    ∫ x in Ioi 0, dlmfFourierSin f x ^ 2 = ∫ t in Ioi 0, f t ^ 2 := by
  simpa only [sq] using dlmf_1_14_14 hf hf2 hf hf2

end Azurite.DLMF
