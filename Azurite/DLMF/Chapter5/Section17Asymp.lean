/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section17Log

/-!
# DLMF 5.17.5–5.17.7: Glaisher's constant and the asymptotic expansion of `Ln G(z + 1)`

Formalization of <https://dlmf.nist.gov/5.17> (part 3).

* Glaisher's constant: `C = lim_{n→∞} (∑_{k=1}^{n} k ln k − (½n² + ½n + 1/12) ln n + ¼n²)`
  (`glaisherSeq`, `glaisherC`, the first form of 5.17.7) and `A = e^C` (`glaisherA`, 5.17.6). The
  limit exists (`tendsto_glaisherSeq`) by the argument below.
* With `R(z) = Ln G(z + 1) − ¼z² − z Ln Γ(z + 1) + (½z(z + 1) + 1/12) ln z` (`glaisherR`),
  `R′(z) = ½K₂(z)`, `K₂(z) = ∫₀^∞ B̃₂(t)/(z + t)² dt`, from 5.17.4's derivative, `Ln Γ(z + 1) =
  Ln Γ(z) + ln z` and Binet's `J = 1/(12z) − ½K₂`. With `Q(z) = ∫₀^∞ B̃₃(t)/(z + t)² dt`
  (`glaisherQ`), `Q′ = −3K₂`, so `R + Q/6` is constant on the slit plane. At `z = n`,
  `R(n) = −(∑ k ln k − (½n² + ½n + 1/12) ln n + ¼n²)` (`glaisherR_nat`), and `Q(n) → 0`, hence the
  limit `C` exists and `R(z) = −C − Q(z)/6` (`glaisherR_eq`).
* Repeated integration by parts (`bernInt_rec`, `glaisherQ_expand`) gives
  `R(z) = −ln A + ∑_{j=2}^{N+1} B_{j+2}/(j(j + 1)(j + 2) z^j) − K/((N + 2)(N + 3))` with
  `K = ∫₀^∞ B̃_{N+3}(t)/(z + t)^{N+2} dt = O(z^{−N−1})` in `|ph z| ≤ π − δ`: 5.17.5
  (`dlmf_5_17_5`, coefficients `glaisherCoeff`: `−ln A`, then `B_{2k+2}/(2k(2k + 1)(2k + 2))` at
  `z^{−2k}` and `0` at odd powers).
-/

open Complex Filter Topology Set Finset MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Integrals of periodic Bernoulli functions -/

/-- `∫₀^∞ B̃ₐ(t)/(z + t)^p dt`. -/
noncomputable def bernInt (a p : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (periodicBernoulli a t : ℂ) / (z + t) ^ p

theorem bernInt_bound (a : ℕ) : ∃ C, ∀ {p : ℕ}, 2 ≤ p → ∀ {z : ℂ} {δ : ℝ}, z ≠ 0 → 0 < δ →
    δ ≤ π → |arg z| ≤ π - δ →
    IntegrableOn (fun t : ℝ => (periodicBernoulli a t : ℂ) / (z + t) ^ p) (Ioi 0) ∧
      ‖bernInt a p z‖ ≤ C / (Real.sin (δ / 2) ^ p * ((p - 1) * ‖z‖ ^ (p - 1))) := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound a
  exact ⟨C, fun hp z δ hz hδ hδπ harg =>
    integrableOn_div_add_pow (measurable_periodicBernoulli a) (C := C) hC hz hδ hδπ harg hp⟩

theorem integrableOn_bernInt (a : ℕ) {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => (periodicBernoulli a t : ℂ) / (z + t) ^ p) (Ioi 0) := by
  obtain ⟨C, hC⟩ := bernInt_bound a
  obtain ⟨h1, h2, h3⟩ := slitPlane_sector hz
  exact (hC hp (slitPlane_ne_zero hz) h1 h2 h3).1

theorem hasDerivAt_bernInt (a : ℕ) {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (bernInt a p) (-(p : ℂ) * bernInt a (p + 1) z) z := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound a
  have h := hasDerivAt_integral_div_add_pow (measurable_periodicBernoulli a) (C := C) hC hp hz
  have h' : HasDerivAt (bernInt a p) _ z := h
  refine h'.congr_deriv ?_
  unfold bernInt
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

/-- One integration by parts on `[j, j + 1]`. -/
theorem bern_ibp_unit {a p : ℕ} (ha : 1 ≤ a) (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    ∫ t in (j : ℝ)..(j + 1), ((a + 1 : ℂ) * ((periodicBernoulli a t : ℂ) / (z + t) ^ p) -
      p * ((periodicBernoulli (a + 1) t : ℂ) / (z + t) ^ (p + 1))) =
      bernoulli (a + 1) * (1 / (z + ((j + 1 : ℝ) : ℂ)) ^ p - 1 / (z + (j : ℂ)) ^ p) := by
  have hne : ∀ t : ℝ, 0 ≤ t → z + t ≠ 0 := fun t ht =>
    slitPlane_ne_zero (add_ofReal_mem_slitPlane hz ht)
  set F : ℝ → ℂ := fun t => (bernoulliFun (a + 1) (t - j) : ℂ) / (z + t) ^ p with hF
  set F' : ℝ → ℂ := fun t => (a + 1 : ℂ) * ((bernoulliFun a (t - j) : ℂ) / (z + t) ^ p) -
    p * ((bernoulliFun (a + 1) (t - j) : ℂ) / (z + t) ^ (p + 1)) with hF'
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have hd : ∀ t ∈ uIcc (j : ℝ) (j + 1), HasDerivAt F (F' t) t := fun t ht => by
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hb : HasDerivAt (fun t : ℝ => (bernoulliFun (a + 1) (t - j) : ℂ))
        (((a + 1 : ℕ) : ℝ) * bernoulliFun a (t - j) : ℝ) t := by
      have := (hasDerivAt_bernoulliFun (a + 1) (t - j)).comp t
        ((hasDerivAt_id t).sub_const (j : ℝ))
      simpa using this.ofReal_comp
    have h0 : HasDerivAt (fun t : ℝ => z + t) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_add z
    have hpw := (hasDerivAt_pow p (z + t)).comp t h0
    have := hb.div hpw (pow_ne_zero p (hne t ht0))
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun u => rfl)
    simp only [hF', Function.comp]
    have h1 := hne t ht0
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    push_cast
    field_simp
    ring
  have hcont : ContinuousOn F' (uIcc (j : ℝ) (j + 1)) := fun t ht => by
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h1 := hne t ht0
    simp only [hF']
    refine ContinuousAt.continuousWithinAt ?_
    have hc1 : Continuous fun t : ℝ => (bernoulliFun a (t - j) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_bernoulliFun a).comp (continuous_sub_right _))
    have hc2 : Continuous fun t : ℝ => (bernoulliFun (a + 1) (t - j) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_bernoulliFun _).comp (continuous_sub_right _))
    exact (continuousAt_const.mul (hc1.continuousAt.div (by fun_prop) (pow_ne_zero _ h1))).sub
      (continuousAt_const.mul (hc2.continuousAt.div (by fun_prop) (pow_ne_zero _ h1)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hcongr : ∫ t in (j : ℝ)..(j + 1), ((a + 1 : ℂ) * ((periodicBernoulli a t : ℂ) /
      (z + t) ^ p) - p * ((periodicBernoulli (a + 1) t : ℂ) / (z + t) ^ (p + 1))) =
      ∫ t in (j : ℝ)..(j + 1), F' t := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le
      (by linarith), integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hf : Int.fract t = t - j := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith [ht.1], by linarith [ht.2], ⟨j, by push_cast; ring⟩⟩
    simp only [hF', periodicBernoulli, hf]
  rw [hcongr, hFTC]
  simp only [hF, sub_self, show (j : ℝ) + 1 - j = 1 by ring,
    bernoulliFun_endpoints_eq_of_ne_one (show a + 1 ≠ 1 by omega), bernoulliFun_eval_zero]
  push_cast
  ring

/-- `(a + 1) ∫ B̃ₐ/(z + t)^p − p ∫ B̃_{a+1}/(z + t)^{p+1} = −B_{a+1}/z^p` (`a ≥ 1`, `p ≥ 2`). -/
theorem bernInt_rec {a p : ℕ} (ha : 1 ≤ a) (hp : 2 ≤ p) {z : ℂ} (hz : z ∈ slitPlane) :
    (a + 1 : ℂ) * bernInt a p z - p * bernInt (a + 1) (p + 1) z = -(bernoulli (a + 1) / z ^ p) := by
  set G : ℝ → ℂ := fun t => (a + 1 : ℂ) * ((periodicBernoulli a t : ℂ) / (z + t) ^ p) -
    p * ((periodicBernoulli (a + 1) t : ℂ) / (z + t) ^ (p + 1)) with hG
  have hI1 := integrableOn_bernInt a hp hz
  have hI2 := integrableOn_bernInt (a + 1) (show 2 ≤ p + 1 by omega) hz
  have hGi : IntegrableOn G (Ioi 0) := (hI1.const_mul _).sub (hI2.const_mul _)
  have hII : ∀ k : ℕ, IntervalIntegrable G volume (k : ℝ) ((k + 1 : ℕ) : ℝ) := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).mpr
      (hGi.mono_set fun t ht => by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; exact lt_of_le_of_lt this ht.1)
  have hN : ∀ N : ℕ, ∫ t in (0 : ℝ)..(N : ℝ), G t =
      bernoulli (a + 1) * (1 / (z + (N : ℂ)) ^ p - 1 / z ^ p) := fun N => by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := N) (fun k _ => hII k)
    simp only [Nat.cast_zero] at h
    rw [← h]
    have e : ∀ k ∈ Finset.range N, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), G t =
        bernoulli (a + 1) * (1 / (z + ((k + 1 : ℕ) : ℂ)) ^ p - 1 / (z + (k : ℂ)) ^ p) :=
      fun k _ => by
        have := bern_ibp_unit (a := a) (p := p) ha (by omega) hz k
        push_cast at this ⊢
        exact this
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_range_sub
      (fun k : ℕ => 1 / (z + (k : ℂ)) ^ p)]
    simp
  have hlim1 : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), G t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), G t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hGi tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..(N : ℝ), G t) atTop
      (𝓝 (bernoulli (a + 1) * (0 - 1 / z ^ p))) := by
    simp_rw [hN]
    refine tendsto_const_nhds.mul (Tendsto.sub ?_ tendsto_const_nhds)
    have hn : Tendsto (fun N : ℕ => ‖z + (N : ℂ)‖) atTop atTop := by
      refine tendsto_atTop_mono (fun N => ?_)
        (tendsto_atTop_add_const_right _ (-‖z‖) (tendsto_natCast_atTop_atTop (R := ℝ)))
      have h1 : ‖(N : ℂ)‖ ≤ ‖z + N‖ + ‖z‖ := by
        have := norm_sub_le (z + N) z; simpa using this
      rw [Complex.norm_natCast] at h1
      linarith
    have hpow : Tendsto (fun N : ℕ => ‖z + (N : ℂ)‖ ^ p) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp hn
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine hpow.inv_tendsto_atTop.congr fun N => ?_
    simp [norm_pow, norm_inv, one_div]
  have hval := tendsto_nhds_unique hlim1 hlim2
  rw [hG, integral_sub (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
    integral_const_mul] at hval
  rw [bernInt, bernInt, hval]
  ring

/-! ### `R(z) + Q(z)/6` is constant -/

/-- `Q(z) = ∫₀^∞ B̃₃(t)/(z + t)² dt`. -/
noncomputable def glaisherQ (z : ℂ) : ℂ := bernInt 3 2 z

/-- `R(z) = Ln G(z + 1) − ¼z² − z Ln Γ(z + 1) + (½z(z + 1) + 1/12) ln z`. -/
noncomputable def glaisherR (z : ℂ) : ℂ :=
  barnesLog z - z ^ 2 / 4 - z * lnGamma (z + 1) + (z * (z + 1) / 2 + 1 / 12) * Complex.log z

theorem hasDerivAt_glaisherR {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt glaisherR (stirlingK 2 z / 2) z := by
  have hz1 := mem_slitPlane_add_one hz
  have hz0 := slitPlane_ne_zero hz
  have hl : HasDerivAt (fun v => lnGamma (v + 1)) (digamma (z + 1)) z :=
    (hasDerivAt_lnGamma hz1).comp_add_const z 1
  have h := (((hasDerivAt_barnesLog hz1).sub ((hasDerivAt_pow 2 z).div_const 4)).sub
    ((hasDerivAt_id z).mul hl)).add
    (((((hasDerivAt_id z).mul ((hasDerivAt_id z).add_const 1)).div_const 2).add_const
      (1 / 12 : ℂ)).mul (Complex.hasDerivAt_log hz))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
  rw [lnGamma_add_one hz, lnGamma, stirlingJ_eq_K2 hz, bernoulli_two]
  simp only [id_eq, Pi.mul_apply]
  push_cast
  field_simp
  ring

theorem hasDerivAt_glaisherQ {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt glaisherQ (-3 * stirlingK 2 z) z := by
  have h := hasDerivAt_bernInt 3 le_rfl hz
  have hrec := stirlingK_rec (m := 2) le_rfl hz
  have hb3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by norm_num)
  norm_num [hb3] at hrec
  refine h.congr_deriv ?_
  change -((2 : ℕ) : ℂ) * stirlingK 3 z = _
  push_cast
  linear_combination hrec

theorem glaisherR_add_glaisherQ_const {z : ℂ} (hz : z ∈ slitPlane) :
    glaisherR z + glaisherQ z / 6 = glaisherR 1 + glaisherQ 1 / 6 := by
  have hd : ∀ w ∈ slitPlane, HasDerivAt (fun v => glaisherR v + glaisherQ v / 6) 0 w :=
    fun w hw => by
      have := (hasDerivAt_glaisherR hw).add ((hasDerivAt_glaisherQ hw).div_const 6)
      convert this using 1
      ring
  exact isOpen_slitPlane.is_const_of_deriv_eq_zero isPreconnected_slitPlane_of_star
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (by simp)

/-! ### Values at the positive integers -/

theorem barnesLog_sub_one {x : ℝ} (hx : 0 < x) :
    barnesLog x = barnesLog ((x : ℂ) - 1) + lnGamma x := by
  have hpole : (x : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by simpa using hx)
  have h1 := dlmf_5_17_1.1 x hpole
  have hs1 : (x : ℂ) + 1 ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; linarith
  have hs0 : (x : ℂ) - 1 + 1 ∈ slitPlane := by
    rw [sub_add_cancel, mem_slitPlane_iff]; left; simpa using hx
  have hxs : (x : ℂ) ∈ slitPlane := by rw [mem_slitPlane_iff]; left; simpa using hx
  rw [barnesG_add_one_eq_exp hs1, show barnesG (x : ℂ) = barnesG ((x : ℂ) - 1 + 1) by ring_nf,
    barnesG_add_one_eq_exp hs0, ← exp_lnGamma hxs, ← exp_add] at h1
  rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring] at h1 ⊢
  rw [barnesLog_ofReal (by linarith), barnesLog_ofReal (by linarith), lnGamma_ofReal hx] at h1 ⊢
  rw [← ofReal_add, ← ofReal_exp, ← ofReal_exp, ofReal_inj] at h1
  rw [← ofReal_add, ofReal_inj, Real.exp_injective h1]
  ring

theorem lnGamma_nat_add_one (n : ℕ) : lnGamma ((n : ℂ) + 1) = (Real.log (n ! : ℝ) : ℂ) := by
  rw [show (n : ℂ) + 1 = ((n + 1 : ℝ) : ℂ) by push_cast; ring, lnGamma_ofReal (by positivity),
    Real.Gamma_nat_eq_factorial]

/-- `Ln G(n + 1) = ∑_{k<n} ln k!`. -/
theorem barnesLog_nat (n : ℕ) : barnesLog n = (∑ k ∈ range n, Real.log (k ! : ℝ) : ℝ) := by
  induction n with
  | zero => simp [barnesLog_zero]
  | succ n ih =>
    have h := barnesLog_sub_one (x := (n + 1 : ℝ)) (by positivity)
    push_cast at h ⊢
    rw [add_sub_cancel_right, ih, lnGamma_nat_add_one] at h
    rw [h, sum_range_succ]
    push_cast
    ring

theorem sum_log_factorial (n : ℕ) :
    ∑ k ∈ range n, Real.log (k ! : ℝ) - n * Real.log (n ! : ℝ) =
      -∑ k ∈ Icc 1 n, (k : ℝ) * Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_Icc_succ_top (by omega), Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    linear_combination ih

/-- `∑_{k=1}^{n} k ln k − (½n² + ½n + 1/12) ln n + ¼n²`, the sequence of 5.17.7. -/
noncomputable def glaisherSeq (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, (k : ℝ) * Real.log k - ((n : ℝ) ^ 2 / 2 + n / 2 + 1 / 12) * Real.log n +
    (n : ℝ) ^ 2 / 4

theorem glaisherR_nat (n : ℕ) : glaisherR n = -(glaisherSeq n : ℂ) := by
  have h := sum_log_factorial n
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_log n.cast_nonneg]
  have hr : ∑ k ∈ range n, Real.log (k ! : ℝ) - (n : ℝ) ^ 2 / 4 - n * Real.log (n ! : ℝ) +
      ((n : ℝ) * (n + 1) / 2 + 1 / 12) * Real.log n = -glaisherSeq n := by
    rw [glaisherSeq]; linarith
  rw [glaisherR, barnesLog_nat, lnGamma_nat_add_one, hlog,
    show -(glaisherSeq n : ℂ) = ((-glaisherSeq n : ℝ) : ℂ) by push_cast; ring, ← hr]
  push_cast
  ring

theorem tendsto_glaisherQ_nat : Tendsto (fun n : ℕ => glaisherQ n) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := bernInt_bound 3
  refine squeeze_zero_norm' (a := fun n : ℕ => C / (n : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h := (hC (p := 2) le_rfl hn0 Real.pi_pos le_rfl (by simp)).2
    show ‖bernInt 3 2 n‖ ≤ C / n
    convert h using 2
    simp [Real.sin_pi_div_two]
    norm_num
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-! ### Glaisher's constant -/

/-- Glaisher's `C = lim_{n→∞} (∑_{k=1}^{n} k ln k − (½n² + ½n + 1/12) ln n + ¼n²)` (5.17.7). -/
noncomputable def glaisherC : ℝ := limUnder atTop glaisherSeq

/-- **Glaisher's constant** `A = e^C` (5.17.6). -/
noncomputable def glaisherA : ℝ := Real.exp glaisherC

theorem tendsto_glaisherSeq_complex :
    Tendsto (fun n : ℕ => (glaisherSeq n : ℂ)) atTop
      (𝓝 (-(glaisherR 1 + glaisherQ 1 / 6))) := by
  have h := (tendsto_glaisherQ_nat.div_const 6).sub
    (tendsto_const_nhds (x := glaisherR 1 + glaisherQ 1 / 6))
  rw [zero_div, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : (n : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simp; exact_mod_cast hn
  have := glaisherR_add_glaisherQ_const hs
  rw [glaisherR_nat] at this
  linear_combination this

/-- The limit defining `C` exists (5.17.7, first form). -/
theorem tendsto_glaisherSeq : Tendsto glaisherSeq atTop (𝓝 glaisherC) := by
  have h := (Complex.continuous_re.tendsto _).comp tendsto_glaisherSeq_complex
  have h' : Tendsto glaisherSeq atTop (𝓝 (-(glaisherR 1 + glaisherQ 1 / 6)).re) := by
    refine h.congr fun n => ?_
    simp
  exact tendsto_nhds_limUnder ⟨_, h'⟩

theorem glaisherR_one_add : glaisherR 1 + glaisherQ 1 / 6 = -(glaisherC : ℂ) := by
  have h := (Complex.continuous_ofReal.tendsto _).comp tendsto_glaisherSeq
  have := tendsto_nhds_unique tendsto_glaisherSeq_complex h
  linear_combination -this

/-- `R(z) = −C − Q(z)/6` on the slit plane. -/
theorem glaisherR_eq {z : ℂ} (hz : z ∈ slitPlane) :
    glaisherR z = -(glaisherC : ℂ) - glaisherQ z / 6 := by
  have h := glaisherR_add_glaisherQ_const hz
  rw [glaisherR_one_add] at h
  linear_combination h

/-- **DLMF 5.17.6**: `A = e^C`, i.e. `ln A = C`. -/
theorem dlmf_5_17_6 : Real.log glaisherA = glaisherC := Real.log_exp _

/-! ### The asymptotic expansion -/

theorem bernInt_step {j : ℕ} (hj : 2 ≤ j) {z : ℂ} (hz : z ∈ slitPlane) :
    bernInt (j + 1) j z = -((bernoulli (j + 2) : ℂ) / ((j + 2) * z ^ j)) +
      j / (j + 2) * bernInt (j + 2) (j + 1) z := by
  have h := bernInt_rec (a := j + 1) (p := j) (by omega) hj hz
  have hz0 := slitPlane_ne_zero hz
  have h2 : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast (show j + 2 ≠ 0 by omega)
  have hzj : z ^ j ≠ 0 := pow_ne_zero _ hz0
  push_cast at h
  rw [show (j : ℂ) + 1 + 1 = j + 2 by ring, show j + 1 + 1 = j + 2 by ring] at h
  have hv : bernInt (j + 1) j z =
      (-((bernoulli (j + 2) : ℂ) / z ^ j) + j * bernInt (j + 2) (j + 1) z) / (j + 2) := by
    rw [eq_div_iff h2]; linear_combination h
  rw [hv]
  field_simp

/-- `Q(z) = −∑_{j<N} 6B_{j+4}/((j + 2)(j + 3)(j + 4) z^{j+2}) + 6/((N + 2)(N + 3)) ·
∫₀^∞ B̃_{N+3}(t)/(z + t)^{N+2} dt`. -/
theorem glaisherQ_expand (N : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    glaisherQ z = -∑ j ∈ range N, 6 * (bernoulli (j + 4) : ℂ) /
        (((j : ℂ) + 2) * (j + 3) * (j + 4) * z ^ (j + 2)) +
      6 / (((N : ℂ) + 2) * (N + 3)) * bernInt (N + 3) (N + 2) z := by
  induction N with
  | zero => simp [glaisherQ]; norm_num
  | succ N ih =>
    have hs := bernInt_step (j := N + 2) (by omega) hz
    have hz0 := slitPlane_ne_zero hz
    have h2 : (N : ℂ) + 2 ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
    have h3 : (N : ℂ) + 3 ≠ 0 := by exact_mod_cast (show N + 3 ≠ 0 by omega)
    have h4 : (N : ℂ) + 4 ≠ 0 := by exact_mod_cast (show N + 4 ≠ 0 by omega)
    rw [show N + 2 + 1 = N + 3 by ring, show N + 2 + 2 = N + 4 by ring,
      show ((N + 2 : ℕ) : ℂ) + 2 = (N : ℂ) + 4 by push_cast; ring,
      show ((N + 2 : ℕ) : ℂ) = (N : ℂ) + 2 by push_cast; ring] at hs
    rw [ih, hs, sum_range_succ, show N + 1 + 3 = N + 4 by ring, show N + 1 + 2 = N + 3 by ring,
      show ((N + 1 : ℕ) : ℂ) + 2 = N + 3 by push_cast; ring,
      show ((N + 1 : ℕ) : ℂ) + 3 = N + 4 by push_cast; ring]
    generalize (∑ j ∈ range N, 6 * (bernoulli (j + 4) : ℂ) /
      (((j : ℂ) + 2) * (j + 3) * (j + 4) * z ^ (j + 2))) = S
    generalize bernInt (N + 4) (N + 3) z = W
    field_simp
    ring

/-- The coefficients of 5.17.5: `−ln A` at `z⁰`, `B_{s+2}/(s(s + 1)(s + 2))` at `z^{−s}`. -/
noncomputable def glaisherCoeff (s : ℕ) : ℂ :=
  if s = 0 then -(glaisherC : ℂ) else (bernoulli (s + 2) : ℂ) / (s * (s + 1) * (s + 2))

theorem glaisherCoeff_zero : glaisherCoeff 0 = -(Real.log glaisherA : ℂ) := by
  simp [glaisherCoeff, dlmf_5_17_6]

theorem glaisherCoeff_even {k : ℕ} (hk : 1 ≤ k) :
    glaisherCoeff (2 * k) =
      (bernoulli (2 * k + 2) : ℂ) / (2 * k * (2 * k + 1) * (2 * k + 2)) := by
  simp only [glaisherCoeff, show 2 * k ≠ 0 by omega, ↓reduceIte]
  push_cast
  ring_nf

theorem glaisherCoeff_odd (k : ℕ) : glaisherCoeff (2 * k + 1) = 0 := by
  simp only [glaisherCoeff, show 2 * k + 1 ≠ 0 by omega, ↓reduceIte,
    show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
    bernoulli_eq_zero_of_odd ⟨k + 1, rfl⟩ (by omega : 1 < 2 * (k + 1) + 1)]
  simp

/-- `R(z) = ∑_{s<N+2} aₛ z^{−s} − K/((N + 2)(N + 3))`, `K = ∫₀^∞ B̃_{N+3}/(z + t)^{N+2}`. -/
theorem glaisherR_sub_sum (N : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    glaisherR z - ∑ s ∈ range (N + 2), glaisherCoeff s * z ^ (-(s : ℤ)) =
      -(1 / (((N : ℂ) + 2) * (N + 3)) * bernInt (N + 3) (N + 2) z) := by
  have hz0 := slitPlane_ne_zero hz
  have h1 : glaisherCoeff (0 + 1) = 0 := glaisherCoeff_odd 0
  have h0 : glaisherCoeff 0 = -(glaisherC : ℂ) := by simp [glaisherCoeff]
  have e : ∀ j ∈ range N, glaisherCoeff (j + 1 + 1) * z ^ (-((j + 1 + 1 : ℕ) : ℤ)) =
      6 * (bernoulli (j + 4) : ℂ) / (((j : ℂ) + 2) * (j + 3) * (j + 4) * z ^ (j + 2)) / 6 :=
    fun j _ => by
      simp only [glaisherCoeff, show j + 1 + 1 ≠ 0 by omega, ↓reduceIte,
        show j + 1 + 1 + 2 = j + 4 by ring, zpow_neg, zpow_natCast]
      have hzj : z ^ (j + 2) ≠ 0 := pow_ne_zero _ hz0
      have hj2 : (j : ℂ) + 2 ≠ 0 := by exact_mod_cast (show j + 2 ≠ 0 by omega)
      have hj3 : (j : ℂ) + 3 ≠ 0 := by exact_mod_cast (show j + 3 ≠ 0 by omega)
      have hj4 : (j : ℂ) + 4 ≠ 0 := by exact_mod_cast (show j + 4 ≠ 0 by omega)
      rw [show j + 1 + 1 = j + 2 by ring]
      push_cast
      rw [show (j : ℂ) + 2 + 1 = j + 3 by ring, show (j : ℂ) + 2 + 2 = j + 4 by ring]
      field_simp
  rw [glaisherR_eq hz, glaisherQ_expand N hz, sum_range_succ', sum_range_succ', h1,
    sum_congr rfl e, ← sum_div]
  simp only [h0, Nat.cast_zero, neg_zero, zpow_zero, mul_one, zero_mul, add_zero]
  generalize (∑ j ∈ range N, 6 * (bernoulli (j + 4) : ℂ) /
    (((j : ℂ) + 2) * (j + 3) * (j + 4) * z ^ (j + 2))) = S
  have h2 : (N : ℂ) + 2 ≠ 0 := by exact_mod_cast (show N + 2 ≠ 0 by omega)
  have h3 : (N : ℂ) + 3 ≠ 0 := by exact_mod_cast (show N + 3 ≠ 0 by omega)
  field_simp
  ring

/-- **DLMF 5.17.5**: as `z → ∞` in `|ph z| ≤ π − δ`,
`Ln G(z + 1) ∼ ¼z² + z Ln Γ(z + 1) − (½z(z + 1) + 1/12) ln z − ln A +
∑_{k≥1} B_{2k+2}/(2k(2k + 1)(2k + 2) z^{2k})`: the difference `R(z)` (`glaisherR`) has the
asymptotic expansion with coefficients `glaisherCoeff` (`glaisherCoeff_zero`, `glaisherCoeff_even`,
`glaisherCoeff_odd`). -/
theorem dlmf_5_17_5 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) glaisherR glaisherCoeff := by
  intro n hn
  obtain ⟨C, hC⟩ := bernInt_bound (n + 2)
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine isBoundedUnder_of_eventually_le (a := ‖glaisherCoeff n‖ +
    C / (s ^ (n + 1) * n) / ((n + 1) * (n + 2))) ?_
  refine Filter.eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
  obtain ⟨hz0, harg⟩ := hz
  simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at harg
  have hslit : z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hz0⟩
  have hK := (hC (p := n + 1) (by omega) hz0 hδ hδπ harg).2
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hsum := glaisherR_sub_sum N hslit
  rw [sum_range_succ] at hsum
  have hzn : ‖z‖ ^ (N + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)
  have e1 : glaisherR z - ∑ s ∈ range (N + 1), glaisherCoeff s * z ^ (-(s : ℤ)) =
      glaisherCoeff (N + 1) * z ^ (-((N + 1 : ℕ) : ℤ)) -
        1 / (((N : ℂ) + 2) * (N + 3)) * bernInt (N + 3) (N + 2) z := by
    linear_combination hsum
  dsimp only
  rw [e1, sub_div, mul_div_assoc, div_self (zpow_ne_zero _ hz0), mul_one]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  have hN2 : ‖(((N : ℂ) + 2) * (N + 3))‖ = ((N : ℝ) + 2) * (N + 3) := by
    rw [show (((N : ℂ) + 2) * (N + 3)) = (((N + 2) * (N + 3) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have e : ‖1 / (((N : ℂ) + 2) * (N + 3)) * bernInt (N + 3) (N + 2) z /
      z ^ (-((N + 1 : ℕ) : ℤ))‖ =
      ‖bernInt (N + 3) (N + 2) z‖ * ‖z‖ ^ (N + 1) / (((N : ℝ) + 2) * (N + 3)) := by
    rw [norm_div, norm_mul, norm_div, norm_one, hN2, norm_zpow, zpow_neg, zpow_natCast]
    field_simp
  rw [e, show N + 1 + 2 = N + 3 by ring] at *
  push_cast at hK ⊢
  rw [show (N : ℝ) + 1 + 1 = N + 2 by ring, show (N : ℝ) + 1 + 2 = N + 3 by ring]
  calc ‖bernInt (N + 3) (N + 2) z‖ * ‖z‖ ^ (N + 1) / (((N : ℝ) + 2) * (N + 3))
      ≤ C / (s ^ (N + 1 + 1) * (((N : ℝ) + 1 + 1 - 1) * ‖z‖ ^ (N + 1 + 1 - 1))) *
          ‖z‖ ^ (N + 1) / (((N : ℝ) + 2) * (N + 3)) := by
        gcongr
        simpa [hs] using hK
    _ = C / (s ^ (N + 1 + 1) * ((N : ℝ) + 1)) / (((N : ℝ) + 2) * (N + 3)) := by
        rw [show N + 1 + 1 - 1 = N + 1 by omega]
        field_simp
        ring

end Azurite.DLMF
