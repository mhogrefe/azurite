/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11RatioExp
import Azurite.DLMF.Chapter5.Section11LaplaceAsymp

/-!
# DLMF §5.11(iii): the coefficients for `b = a + m + 1`

For `b − a = m + 1` (`m ∈ ℕ`), Watson's lemma identifies the exponentiated coefficients of
`Section11RatioExp.lean` with `(−m−1 choose s) B_s^{(−m)}(a)` (`ratioExpCoeff_eq_nat`):

* `Γ(x + a) m!/Γ(x + a + m + 1) = ∫₀^∞ e^{−(x+a)t} (1 − e^{−t})^m dt` (the Beta integral with
  `u = e^{−t}`, `laplace_ratio_eq`);
* `e^{−at}(1 − e^{−t})^m = tᵐ ψ(t)`,
  `ψ(t) = e^{−at}((1 − e^{−t})/t)^m ∼ ∑ (−1)ˢ B_s^{(−m)}(a) tˢ/s!`
  as `t → 0+` (`hasPowExpansion_ratioPsi`; the generating function `((eʷ − 1)/w)^m e^{aw}` of
  `mk_genBernoulli_one_sub` at `w = −t`);
* Watson's lemma (2.3.8) gives `∑ Γ(s + m + 1)(−1)ˢ B_s^{(−m)}(a)/(s! m!) x^{m+1−s}` for the
  ratio, and
  uniqueness of asymptotic expansions along `x → +∞` finishes.
-/

open Complex Filter Topology Set Asymptotics MeasureTheory PowerSeries
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The binomial coefficient -/

/-- The binomial coefficient `(z choose k) = z(z − 1)⋯(z − k + 1)/k!` for complex `z`. -/
noncomputable def cBinom (z : ℂ) (k : ℕ) : ℂ := (descPochhammer ℂ k).eval z / (k ! : ℂ)

theorem cBinom_neg_nat (m s : ℕ) :
    cBinom (-((m : ℂ) + 1)) s = (-1) ^ s * ((m + s)! : ℂ) / ((m ! : ℂ) * (s ! : ℂ)) := by
  have key : ∀ s : ℕ, (descPochhammer ℂ s).eval (-((m : ℂ) + 1)) * (m ! : ℂ) =
      (-1) ^ s * ((m + s)! : ℂ) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_natCast, mul_right_comm, ih, show m + (s + 1) = (m + s) + 1 by ring,
        Nat.factorial_succ]
      push_cast
      ring
  rw [cBinom]
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hs : (s ! : ℂ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  rw [div_eq_div_iff hs (mul_ne_zero hm hs), ← key]
  ring

/-! ### The expansion of `ψ` at `0+` -/

theorem hasPowExpansion_neg_var {α : Type*} {l : Filter α} {y f : α → ℂ} {A : ℂ⟦X⟧}
    (h : HasPowExpansion l y f A) :
    HasPowExpansion l (fun x => -y x) f (rescale (-1 : ℂ) A) := fun n => by
  have e : ∀ x, (trunc n (rescale (-1 : ℂ) A)).eval (-y x) = (trunc n A).eval (y x) := fun x => by
    rw [eval_trunc_eq_sum, eval_trunc_eq_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [coeff_rescale, neg_pow (y x), ← mul_assoc, mul_comm _ ((-1 : ℂ) ^ s), ← mul_assoc,
      ← pow_add, ← two_mul, pow_mul]
    simp
  refine ((h n).congr_left fun x => by rw [e]).trans ?_
  exact isBigO_of_le l fun x => by rw [norm_pow, norm_pow, norm_neg]

/-- `ψ(t) = e^{−at}((1 − e^{−t})/t)^m`. -/
noncomputable def ratioPsi (a : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  cexp (-(a * t)) * ((1 - cexp (-(t : ℂ))) / t) ^ m

theorem tendsto_ofReal_nhdsGT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have := (continuous_ofReal.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

theorem eventually_ofReal_ne_zero : ∀ᶠ t : ℝ in 𝓝[>] 0, (t : ℂ) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ofReal_ne_zero.mpr (ne_of_gt ht)

/-- `ψ(t) ∼ ∑ (−1)ˢ B_s^{(−m)}(a) tˢ/s!` as `t → 0+`. -/
theorem hasPowExpansion_ratioPsi (a : ℂ) (m : ℕ) :
    HasPowExpansion (𝓝[>] 0) (fun t : ℝ => (t : ℂ)) (ratioPsi a m)
      (rescale (-1 : ℂ) (mk fun k => genBernoulli (1 - (m + 1 : ℕ)) a k / (k ! : ℂ))) := by
  set w : ℝ → ℂ := fun t => -(t : ℂ) with hw
  have hwt : Tendsto w (𝓝[>] 0) (𝓝 0) := by
    simpa [hw] using tendsto_ofReal_nhdsGT.neg
  have hw0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), w t ≠ 0 := by
    filter_upwards [eventually_ofReal_ne_zero] with t ht
    simpa [hw] using ht
  -- `eʷ − 1`
  have h1 : HasPowExpansion (𝓝[>] 0) w (fun t => cexp (w t) - 1) (exp ℂ - 1) := by
    have := hasPowExpansion_cexp_zero.comp_tendsto hwt
    exact this.sub (hasPowExpansion_const hwt 1) |>.congr' (Eventually.of_forall fun _ => rfl)
  -- `(eʷ − 1)/w`
  have h2 : HasPowExpansion (𝓝[>] 0) w (fun t => (cexp (w t) - 1) / w t) expDivGen := by
    have := h1.div_var (by simp) hw0
    convert this using 1
    ext k
    simp [expDivGen, coeff_exp, Nat.factorial_succ]
  -- `e^{aw}`
  have h3 : HasPowExpansion (𝓝[>] 0) w (fun t => cexp (a * w t))
      (mk fun k => a ^ k / (k ! : ℂ)) := by
    have hlin : HasPowExpansion (𝓝[>] 0) w (fun t => a * w t)
        (mk fun k => if k = 1 then a else 0) := by
      have := (hasPowExpansion_id hwt).const_mul a
      convert this using 1
      ext k
      simp [coeff_X]
    have := hlin.cexp' hwt (by simp)
    rwa [expPS_linear] at this
  have h4 := (h2.pow hwt m).mul hwt h3
  rw [← mk_genBernoulli_one_sub] at h4
  have h5 := hasPowExpansion_neg_var h4
  refine h5.congr' ?_ |>.congr_var ?_
  · filter_upwards [eventually_ofReal_ne_zero] with t ht
    simp only [Pi.mul_apply, ratioPsi, hw]
    rw [mul_comm]
    congr 2
    · ring_nf
    · field_simp
      ring
  · exact Eventually.of_forall fun t => by simp [hw]

/-! ### Watson's form -/

/-- `q(t) = e^{−at}(1 − e^{−t})^m = tᵐ ψ(t)`. -/
noncomputable def ratioQ (a : ℂ) (m : ℕ) (t : ℝ) : ℂ := cexp (-(a * t)) * (1 - cexp (-(t : ℂ))) ^ m

theorem ratioQ_eq (a : ℂ) (m : ℕ) {t : ℝ} (ht : (t : ℂ) ≠ 0) :
    ratioQ a m t = (t : ℂ) ^ m * ratioPsi a m t := by
  rw [ratioQ, ratioPsi, div_pow]
  field_simp

/-- The coefficients `(−1)ˢ B_s^{(−m)}(a)/s!` of `ψ`. -/
noncomputable def ratioPsiCoeff (a : ℂ) (m s : ℕ) : ℂ :=
  (-1) ^ s * (genBernoulli (1 - (m + 1 : ℕ)) a s / (s ! : ℂ))

theorem rpow_watson (m s : ℕ) (t : ℝ) :
    t ^ (((s : ℝ) + ((m : ℝ) + 1) - 1) / 1) = t ^ (s + m) := by
  rw [show ((s : ℝ) + ((m : ℝ) + 1) - 1) / 1 = ((s + m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-- 2.3.7 for `q`: `q(t) ∼ ∑ (−1)ˢ B_s^{(−m)}(a)/s! · t^{s+m}` as `t → 0+`. -/
theorem isGenAsymp_ratioQ (a : ℂ) (m : ℕ) :
    IsGenAsympExpansionDLMF (𝓝[>] 0)
      (fun s t => ((t ^ (((s : ℝ) + ((m : ℝ) + 1) - 1) / 1) : ℝ) : ℂ)) (ratioQ a m)
      (fun s t => ratioPsiCoeff a m s * ((t ^ (((s : ℝ) + ((m : ℝ) + 1) - 1) / 1) : ℝ) : ℂ)) := by
  have hP := hasPowExpansion_ratioPsi a m
  refine ⟨fun s => ?_, fun n => ?_⟩
  · refine tendsto_ofReal_nhdsGT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [rpow_watson m _ t, rpow_watson m _ t]
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht'.ne'
    push_cast
    rw [show s + 1 + m = (s + m) + 1 by ring, pow_succ]
    field_simp
  · obtain ⟨C, hC⟩ := (hP n).bound
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hC, self_mem_nhdsWithin] with t h1 ht
    have ht' : (0 : ℝ) < t := ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht'.ne'
    have hnum : ratioQ a m t - ∑ s ∈ Finset.range n, ratioPsiCoeff a m s *
          ((t ^ (((s : ℝ) + ((m : ℝ) + 1) - 1) / 1) : ℝ) : ℂ) =
        (t : ℂ) ^ m * (ratioPsi a m t - (trunc n (rescale (-1 : ℂ) (mk fun k =>
          genBernoulli (1 - (m + 1 : ℕ)) a k / (k ! : ℂ)))).eval (t : ℂ)) := by
      rw [ratioQ_eq a m ht0, mul_sub, eval_trunc_eq_sum, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [rpow_watson m _ t, coeff_rescale, coeff_mk, ratioPsiCoeff]
      push_cast
      ring
    have e : (ratioQ a m t - ∑ s ∈ Finset.range n, ratioPsiCoeff a m s *
          ((t ^ (((s : ℝ) + ((m : ℝ) + 1) - 1) / 1) : ℝ) : ℂ)) /
        ((t ^ (((n : ℝ) + ((m : ℝ) + 1) - 1) / 1) : ℝ) : ℂ) =
        (ratioPsi a m t - (trunc n (rescale (-1 : ℂ) (mk fun k =>
          genBernoulli (1 - (m + 1 : ℕ)) a k / (k ! : ℂ)))).eval (t : ℂ)) / (t : ℂ) ^ n := by
      rw [hnum, rpow_watson m _ t]
      push_cast
      rw [pow_add]
      field_simp
    rw [e, norm_div, norm_pow]
    have hpos : 0 < ‖(t : ℂ)‖ ^ n := pow_pos (norm_pos_iff.mpr ht0) n
    rw [div_le_iff₀ hpos]
    simpa [norm_pow] using h1

/-! ### The Laplace transform of `q` is a Beta integral -/

theorem exp_neg_image_Ioi : (fun t : ℝ => Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    have := Real.exp_lt_exp.mpr (show -t < 0 by linarith [show (0 : ℝ) < t from ht])
    rwa [Real.exp_zero] at this
  · rintro ⟨h0, h1⟩
    refine ⟨-Real.log u, ?_, by simp [Real.exp_log h0]⟩
    have := Real.log_neg h0 h1
    show 0 < -Real.log u
    linarith

theorem integral_Ioo_eq_integral_exp_neg (g : ℝ → ℂ) :
    ∫ u in Ioo (0 : ℝ) 1, g u = ∫ t in Ioi (0 : ℝ), Real.exp (-t) • g (Real.exp (-t)) := by
  rw [← exp_neg_image_Ioi, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (f := fun t => Real.exp (-t)) (f' := fun t => -Real.exp (-t))
    (fun t _ => ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).hasDerivWithinAt.congr_deriv
      (by ring))
    (fun x _ y _ h => by simpa using h)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]

theorem ofReal_exp_neg_cpow (t : ℝ) (c : ℂ) :
    ((Real.exp (-t) : ℝ) : ℂ) ^ c = cexp (-(t : ℂ) * c) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log
    (Real.exp_pos _).le, Real.log_exp]
  push_cast
  ring_nf

theorem norm_cexp_neg_mul_ratioQ (a : ℂ) (m : ℕ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖cexp (-(x : ℂ) * t) * ratioQ a m t‖ ≤ Real.exp (-(x + a.re) * t) := by
  rw [ratioQ, ← mul_assoc, ← Complex.exp_add, norm_mul, norm_pow, norm_exp]
  have h1 : ‖1 - cexp (-(t : ℂ))‖ ≤ 1 := by
    rw [show cexp (-(t : ℂ)) = ((Real.exp (-t) : ℝ) : ℂ) by push_cast; rfl,
      show (1 : ℂ) - ((Real.exp (-t) : ℝ) : ℂ) = ((1 - Real.exp (-t) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [Real.exp_pos (-t), Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith)]
  have h2 : (-(x : ℂ) * t + -(a * t)).re = -(x + a.re) * t := by simp; ring
  rw [h2]
  calc Real.exp (-(x + a.re) * t) * ‖1 - cexp (-(t : ℂ))‖ ^ m
      ≤ Real.exp (-(x + a.re) * t) * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) h1
    _ = _ := mul_one _

theorem integrableOn_ratioQ (a : ℂ) (m : ℕ) {x : ℝ} (hx : 0 < x + a.re) :
    IntegrableOn (fun t : ℝ => cexp (-(x : ℂ) * t) * ratioQ a m t) (Ioi 0) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi 0 hx) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact (by unfold ratioQ; fun_prop : Continuous fun t : ℝ =>
      cexp (-(x : ℂ) * t) * ratioQ a m t).aestronglyMeasurable
  · simpa [neg_mul] using norm_cexp_neg_mul_ratioQ a m x ht

/-- `∫₀^∞ e^{−xt} q(t) dt = m! Γ(x + a)/Γ(x + a + m + 1)` for `x + ℜa > 0`. -/
theorem integral_ratioQ (a : ℂ) (m : ℕ) {x : ℝ} (hx : 0 < x + a.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(x : ℂ) * t) * ratioQ a m t =
      (m ! : ℂ) * Gamma (x + a) / Gamma (x + a + ((m : ℂ) + 1)) := by
  set p : ℂ := x + a
  have hp : 0 < p.re := by simpa [p] using hx
  have hm : 0 < ((m : ℂ) + 1).re := by simp; positivity
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hp hm
  have hG0 : Gamma (p + ((m : ℂ) + 1)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hB : betaIntegral p ((m : ℂ) + 1) =
      ∫ t in Ioi (0 : ℝ), cexp (-(x : ℂ) * t) * ratioQ a m t := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      integral_Ioo_eq_integral_exp_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [ofReal_exp_neg_cpow, show (m : ℂ) + 1 - 1 = (m : ℕ) by ring, cpow_natCast, ratioQ,
      Complex.real_smul]
    push_cast
    have e : cexp (-(t : ℂ)) * cexp (-(t : ℂ) * (p - 1)) =
        cexp (-(x : ℂ) * t) * cexp (-(a * t)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [p]
      ring
    rw [← mul_assoc, e, mul_assoc]
  rw [← hB, eq_div_iff hG0]
  rw [Complex.Gamma_nat_eq_factorial] at hbeta
  linear_combination -hbeta

/-! ### Watson's lemma and the identification -/

theorem continuous_ratioQ (a : ℂ) (m : ℕ) : Continuous (ratioQ a m) := by
  unfold ratioQ; fun_prop

theorem laplaceIntegral_ratioQ (a : ℂ) (m : ℕ) {x : ℝ} (hx : 0 < x + a.re) :
    laplaceIntegral (ratioQ a m) x =
      (m ! : ℂ) * Gamma (x + a) / Gamma (x + a + ((m : ℂ) + 1)) := by
  rw [← integral_ratioQ a m hx]
  exact (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_ratioQ a m hx)
    tendsto_id).limUnder_eq

/-- Watson's lemma (2.3.8) for `q`. -/
theorem watson_ratioQ (a : ℂ) (m : ℕ) :
    IsGenAsympExpansionDLMF atTop (fun s x => ((x ^ (-watsonExp ((m : ℝ) + 1) 1 s) : ℝ) : ℂ))
      (laplaceIntegral (ratioQ a m))
      (fun s x => (Real.Gamma (watsonExp ((m : ℝ) + 1) 1 s) : ℂ) * ratioPsiCoeff a m s *
        ((x ^ (-watsonExp ((m : ℝ) + 1) 1 s) : ℝ) : ℂ)) :=
  dlmf_2_3_8 (x₀ := |a.re| + 1) (by positivity) one_pos (continuous_ratioQ a m).measurable
    (fun c R _ => (continuous_ratioQ a m).intervalIntegrable c R) (isGenAsymp_ratioQ a m)
    (fun x hx => ⟨_, intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_ratioQ a m (by linarith [neg_abs_le a.re])) tendsto_id⟩)

/-- The ratio along `x → +∞` for `b = a + m + 1`. -/
theorem hasPowExpansion_ratio_real (a : ℂ) (m : ℕ) :
    HasPowExpansion atTop (fun x : ℝ => ((x : ℂ))⁻¹)
      (fun x : ℝ => Gamma (x + a) / Gamma (x + (a + ((m : ℂ) + 1))) /
        (x : ℂ) ^ (a - (a + ((m : ℂ) + 1))))
      (mk fun s => ((s + m)! : ℂ) / (m ! : ℂ) * ratioPsiCoeff a m s) := fun n => by
  obtain ⟨C, hC⟩ := (watson_ratioQ a m).2 n
  rw [eventually_map] at hC
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hmr : (0 : ℝ) < m ! := by exact_mod_cast m.factorial_pos
  refine IsBigO.of_bound (C / m !) ?_
  filter_upwards [hC, eventually_ge_atTop (|a.re| + 1)] with x hx hx1
  have hx0 : 0 < x := by linarith [abs_nonneg a.re]
  have hxa : 0 < x + a.re := by linarith [neg_abs_le a.re]
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  have hw : ∀ s : ℕ, ((x ^ (-watsonExp ((m : ℝ) + 1) 1 s) : ℝ) : ℂ) =
      ((x : ℂ) ^ (s + m + 1))⁻¹ := fun s => by
    rw [watsonExp, div_one, show (s : ℝ) + ((m : ℝ) + 1) = ((s + m + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hx0.le, Real.rpow_natCast]
    push_cast
    rfl
  have hΓ : ∀ s : ℕ, (Real.Gamma (watsonExp ((m : ℝ) + 1) 1 s) : ℂ) = ((s + m)! : ℂ) := fun s => by
    rw [watsonExp, div_one, show (s : ℝ) + ((m : ℝ) + 1) = ((s + m : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
    push_cast
    rfl
  have hpow : (x : ℂ) ^ (a - (a + ((m : ℂ) + 1))) = ((x : ℂ) ^ (m + 1))⁻¹ := by
    rw [show a - (a + ((m : ℂ) + 1)) = -(((m + 1 : ℕ) : ℂ)) by push_cast; ring, cpow_neg,
      cpow_natCast]
  set E := laplaceIntegral (ratioQ a m) x - ∑ s ∈ Finset.range n,
    (Real.Gamma (watsonExp ((m : ℝ) + 1) 1 s) : ℂ) * ratioPsiCoeff a m s *
      ((x ^ (-watsonExp ((m : ℝ) + 1) 1 s) : ℝ) : ℂ) with hE
  have hL := laplaceIntegral_ratioQ a m hxa
  have key : Gamma (x + a) / Gamma (x + (a + ((m : ℂ) + 1))) / (x : ℂ) ^ (a - (a + ((m : ℂ) + 1))) -
      (trunc n (mk fun s => ((s + m)! : ℂ) / (m ! : ℂ) * ratioPsiCoeff a m s)).eval ((x : ℂ))⁻¹ =
      (x : ℂ) ^ (m + 1) / (m ! : ℂ) * E := by
    rw [hE, hL, hpow, eval_trunc_eq_sum, mul_sub, Finset.mul_sum, ← add_assoc]
    congr 1
    · field_simp
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [coeff_mk, hΓ, hw, inv_pow, pow_add, pow_add]
      field_simp
      ring
  rw [key, norm_mul]
  have hEb : ‖E‖ ≤ C * x ^ (-(n + m + 1 : ℝ)) := by
    have h := hx
    have hwpos : 0 < ‖((x ^ (-watsonExp ((m : ℝ) + 1) 1 n) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hx0 _).le]
      exact Real.rpow_pos_of_pos hx0 _
    rw [norm_div, div_le_iff₀ hwpos] at h
    refine h.trans (le_of_eq ?_)
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_pos_of_pos hx0 _).le, watsonExp,
      div_one]
    ring_nf
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hx
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le, Complex.norm_natCast,
    norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  calc x ^ (m + 1) / (m ! : ℝ) * ‖E‖ ≤ x ^ (m + 1) / (m ! : ℝ) * (C * x ^ (-(n + m + 1 : ℝ))) := by
        gcongr
    _ = C / m ! * (x⁻¹) ^ n := by
        rw [show (-(n + m + 1 : ℝ)) = -((n : ℝ) + ((m + 1 : ℕ) : ℝ)) by push_cast; ring,
          Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_natCast, Real.rpow_natCast, inv_pow]
        field_simp

/-- **The coefficients for `b = a + m + 1`**:
`eₛ(a, a + m + 1) = ((s + m)!/m!) (−1)ˢ B_s^{(−m)}(a)/s!`. -/
theorem ratioExpCoeff_eq_watson (a : ℂ) (m s : ℕ) :
    ratioExpCoeff a (a + ((m : ℂ) + 1)) s = ((s + m)! : ℂ) / (m ! : ℂ) * ratioPsiCoeff a m s := by
  have hS := isAsympExpansionDLMF_iff.mp
    (isAsympExpansion_gammaRatio_exp a (a + ((m : ℂ) + 1)) Real.pi_pos le_rfl)
  have hk : Tendsto (fun x : ℝ => (x : ℂ)) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - π))) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
    · simpa using tendsto_abs_atTop_atTop
    · filter_upwards [eventually_gt_atTop 0] with x hx
      refine ⟨Complex.ofReal_ne_zero.mpr hx.ne', ?_⟩
      simp [arg_ofReal_of_nonneg hx.le]
  have h1 := hS.comp_tendsto hk
  have h2 := hasPowExpansion_ratio_real a m
  have hy : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv₀_cobounded.comp (tendsto_inf.mp hk).1
  have hy0 : ∀ᶠ x : ℝ in atTop, ((x : ℂ))⁻¹ ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact inv_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have h := HasPowExpansion.unique hy hy0 h1 h2
  have := congrArg (coeff s) h
  simpa [ratioExpCoeff] using this

/-- In DLMF's form: `eₛ(a, a + m + 1) = (−m−1 choose s) B_s^{(−m)}(a)`. -/
theorem ratioExpCoeff_eq_nat (a : ℂ) (m s : ℕ) :
    ratioExpCoeff a (a + ((m : ℂ) + 1)) s =
      cBinom (-((m : ℂ) + 1)) s * genBernoulli (1 - (m + 1 : ℕ)) a s := by
  rw [ratioExpCoeff_eq_watson, cBinom_neg_nat, ratioPsiCoeff, add_comm s m]
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hs : (s ! : ℂ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
  field_simp

end Azurite.DLMF
