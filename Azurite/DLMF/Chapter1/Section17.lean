/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16Derivatives
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# DLMF §1.17(i): Delta sequences

https://dlmf.nist.gov/1.17.i

* 1.17.1–1.17.2: the Dirac delta is a symbolic function. No function vanishing off `0` satisfies
  1.17.2 even for all test functions (`dlmf_1_17_1_2_not_function`). 1.17.2 is made rigorous by the
  Dirac distribution of §1.16(iii) (`dlmf_1_17_2`) or the Dirac measure (`dlmf_1_17_2_measure`).
* 1.17.3: `IsDeltaSequence`, with `φ` ranging over the test functions on `ℝ` (§1.16(i)).
* 1.17.4: `lim δₙ = δ` means convergence of distributions (1.16.7): `δₙ` is a delta sequence iff
  the regular distributions of the `δₙ(· − a)` converge to `δ_a` for every `a` (`dlmf_1_17_4`).
* 1.17.5: the Gaussian `gaussDelta n x = √(n/π) e^{−n x²}`, with integral `1`
  (`integral_gaussDelta`) and `1/2` over `(0, ∞)`. It is a delta sequence
  (`isDeltaSequence_gaussDelta`, `dlmf_1_17_4_gaussDelta`).
* 1.17.6–1.17.7: the general limit `tendsto_integral_gaussDelta`. If `e^{−n(x−a)²} φ(x)` is
  integrable for all large `n` and `φ(a±)` exist, then `∫ δₙ(x − a) φ(x) dx → ½φ(a−) + ½φ(a+)`.
  On each half-line, `δₙ = ½ kₙ e^{−Nt²}` with `kₙ = 2√(n/π) e^{−(n−N)t²}` (`gaussPeak`), a peak
  family (`∫_0^∞ kₙ → 1`, `kₙ → 0` uniformly away from `0`), so Mathlib's
  `tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux` applies to the integrable
  `e^{−Nt²} ψ(t)`. `dlmf_1_17_6` is the continuous case. `dlmf_1_17_6_growth` shows the
  integrability condition holds for `n > α` when `φ = O(e^{αx²})` as `x → ±∞`. `dlmf_1_17_7` is
  the piecewise continuous case (`IsPiecewiseContinuous` of §1.4(ii) on every `[−c, c]`, real `φ`).

No discrepancies with the DLMF were found.
-/

open Set Filter Topology MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### The Dirac delta and delta sequences (1.17.1–1.17.4) -/

/-- A smooth bump: a test function on `ℝ` with value `1` at `0`. -/
theorem exists_testFunction_one : ∃ φ : ℝ → ℂ, IsTestFunction univ φ ∧ φ 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun x => ((b x : ℝ) : ℂ), ⟨Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, subset_univ _⟩, ?_⟩
  simp only
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  simp

/-- DLMF 1.17.1–1.17.2: the Dirac delta is only a symbolic function. No function `δ` with
`δ(x) = 0` for `x ≠ 0` (1.17.1) satisfies 1.17.2 even for all test functions `φ`, since then
`δ = 0` almost everywhere and every integral `∫ δ(x − a) φ(x) dx` vanishes. -/
theorem dlmf_1_17_1_2_not_function :
    ¬ ∃ δ : ℝ → ℂ, (∀ x, x ≠ 0 → δ x = 0) ∧
      ∀ (a : ℝ) (φ : ℝ → ℂ), IsTestFunction univ φ → ∫ x, δ (x - a) * φ x = φ a := by
  rintro ⟨δ, h1, h2⟩
  obtain ⟨φ, hφ, hφ0⟩ := exists_testFunction_one
  have h := h2 0 φ hφ
  have h0 : ∫ x, δ (x - 0) * φ x = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [(countable_singleton (0 : ℝ)).ae_notMem volume] with x hx
    have hx0 : x ≠ 0 := fun e => hx (by rw [e]; rfl)
    simp [h1 x hx0]
  rw [h0, hφ0] at h
  exact zero_ne_one h

/-- DLMF 1.17.2, made rigorous as the Dirac distribution `δ_a` of §1.16(iii) (1.16.11). -/
theorem dlmf_1_17_2 (a : ℝ) (φ : testSpace univ) : diracDist univ a φ = (φ : ℝ → ℂ) a := rfl

/-- DLMF 1.17.2, made rigorous as integration against the Dirac measure at `a`. -/
theorem dlmf_1_17_2_measure (φ : ℝ → ℂ) (a : ℝ) : ∫ x, φ x ∂(Measure.dirac a) = φ a :=
  integral_dirac φ a

/-- DLMF 1.17.3: `δₙ` is a delta sequence when `∫ δₙ(x − a) φ(x) dx → φ(a)` for every `a ∈ ℝ`
and every test function `φ`. -/
def IsDeltaSequence (δs : ℕ → ℝ → ℝ) : Prop :=
  ∀ (a : ℝ) (φ : ℝ → ℂ), IsTestFunction univ φ →
    Tendsto (fun n => ∫ x, (δs n (x - a) : ℂ) * φ x) atTop (𝓝 (φ a))

/-- DLMF 1.17.4: `lim δₙ(x − a) = δ(x − a)` holds in the sense of distributions (1.16.7), the
regular distributions of the `δₙ(· − a)` converging to `δ_a`, exactly for delta sequences. -/
theorem dlmf_1_17_4 {δs : ℕ → ℝ → ℝ}
    (hloc : ∀ n a, LocallyIntegrableOn (fun x => (δs n (x - a) : ℂ)) univ) :
    IsDeltaSequence δs ↔ ∀ a, DistConverges univ (fun n => regularDist isOpen_univ (hloc n a))
      (diracDist univ a) := by
  constructor
  · intro h a φ
    simpa [dlmf_1_16_3, dlmf_1_16_11] using h a φ (mem_testSpace.mp φ.2)
  · intro h a φ hφ
    simpa [dlmf_1_16_3, dlmf_1_16_11] using h a ⟨φ, hφ⟩

/-! ### The Gaussian delta sequence (1.17.5) -/

/-- DLMF 1.17.5: the Gaussian delta sequence `δₙ(x) = √(n/π) e^{−n x²}`. -/
noncomputable def gaussDelta (n : ℕ) (x : ℝ) : ℝ := √(n / π) * Real.exp (-(n * x ^ 2))

/-- DLMF 1.17.5: `δₙ(x − a) = √(n/π) e^{−n(x−a)²}`. -/
theorem dlmf_1_17_5 (n : ℕ) (x a : ℝ) :
    gaussDelta n (x - a) = √(n / π) * Real.exp (-(n * (x - a) ^ 2)) := rfl

theorem gaussDelta_nonneg (n : ℕ) (x : ℝ) : 0 ≤ gaussDelta n x := by
  unfold gaussDelta; positivity

theorem gaussDelta_neg (n : ℕ) (x : ℝ) : gaussDelta n (-x) = gaussDelta n x := by
  simp [gaussDelta]

theorem integrable_exp_neg_mul_sq' {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => Real.exp (-(b * x ^ 2)) := by
  simpa [neg_mul] using integrable_exp_neg_mul_sq hb

theorem integrable_gaussDelta {n : ℕ} (hn : 0 < n) : Integrable (gaussDelta n) :=
  (integrable_exp_neg_mul_sq' (by exact_mod_cast hn)).const_mul _

theorem sqrt_div_pi_mul_sqrt_pi_div {b : ℝ} (hb : 0 ≤ b) (c : ℝ) :
    √(b / π) * √(π / c) = √(b / c) := by
  rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm b π,
    mul_div_mul_left _ _ Real.pi_pos.ne']

theorem integral_Ioi_gaussDelta {n : ℕ} (hn : 0 < n) : ∫ x in Ioi 0, gaussDelta n x = 1 / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [gaussDelta, ← neg_mul]
  rw [integral_const_mul, integral_gaussian_Ioi, mul_div_assoc',
    sqrt_div_pi_mul_sqrt_pi_div hn'.le _, div_self hn'.ne', Real.sqrt_one]

theorem integral_gaussDelta {n : ℕ} (hn : 0 < n) : ∫ x, gaussDelta n x = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [gaussDelta, ← neg_mul]
  rw [integral_const_mul, integral_gaussian, sqrt_div_pi_mul_sqrt_pi_div hn'.le _,
    div_self hn'.ne', Real.sqrt_one]

/-! ### The limit (1.17.6)–(1.17.7) on a half-line -/

/-- The reweighted kernel `2√(n/π) e^{−(n−N)t²}`, so that `δₙ(t) = ½ kₙ(t) e^{−Nt²}`. -/
noncomputable def gaussPeak (N n : ℕ) (t : ℝ) : ℝ :=
  2 * (√(n / π) * Real.exp (-(((n : ℝ) - N) * t ^ 2)))

theorem gaussDelta_eq_gaussPeak (N n : ℕ) (t : ℝ) :
    gaussDelta n t = 1 / 2 * gaussPeak N n t * Real.exp (-(N * t ^ 2)) := by
  have : Real.exp (-(n * t ^ 2)) = Real.exp (-(((n : ℝ) - N) * t ^ 2)) *
      Real.exp (-(N * t ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [gaussDelta, gaussPeak, this]; ring

theorem gaussPeak_nonneg (N n : ℕ) (t : ℝ) : 0 ≤ gaussPeak N n t := by
  unfold gaussPeak; positivity

theorem continuous_gaussPeak (N n : ℕ) : Continuous (gaussPeak N n) := by
  unfold gaussPeak; fun_prop

theorem tendsto_integral_Ioi_gaussPeak (N : ℕ) :
    Tendsto (fun n : ℕ => ∫ t in Ioi 0, gaussPeak N n t) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => √((n : ℝ) / (n + -(N : ℝ)))) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp (tendsto_natCast_div_add_atTop (-(N : ℝ)))
    rwa [Real.sqrt_one] at this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop N] with n _
  simp_rw [gaussPeak, ← neg_mul]
  rw [integral_const_mul, integral_const_mul, integral_gaussian_Ioi, mul_div_assoc',
    sqrt_div_pi_mul_sqrt_pi_div n.cast_nonneg _, ← sub_eq_add_neg]
  ring

theorem tendsto_sqrt_mul_exp_neg (N : ℕ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => 2 * (√(n / π) * Real.exp (-(((n : ℝ) - N) * η ^ 2)))) atTop
      (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (η ^ 2)
    (by positivity)).comp tendsto_natCast_atTop_atTop
  have h2 := h.const_mul (2 / √π * Real.exp (N * η ^ 2))
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp]
  rw [Real.sqrt_div' _ Real.pi_pos.le, Real.sqrt_eq_rpow (n : ℝ), show -(((n : ℝ) - N) * η ^ 2) =
    -η ^ 2 * n + N * η ^ 2 by ring, Real.exp_add]
  ring

theorem tendstoUniformlyOn_gaussPeak (N : ℕ) {u : Set ℝ} (hu : IsOpen u) (h0 : (0 : ℝ) ∈ u) :
    TendstoUniformlyOn (gaussPeak N) 0 atTop (Ioi 0 \ u) := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hu 0 h0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_sqrt_mul_exp_neg N hη).eventually (gt_mem_nhds hε),
    eventually_ge_atTop N] with n hn hnN t ht
  have htη : η ≤ t := by
    by_contra h
    exact ht.2 (hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith))
  have hc : (0 : ℝ) ≤ n - N := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hnN
    linarith
  rw [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (gaussPeak_nonneg _ _ _)]
  refine lt_of_le_of_lt ?_ hn
  unfold gaussPeak
  gcongr

/-- On `(0, ∞)`: if `e^{−Nt²} ψ(t)` is integrable and `ψ(0+) = R`, then
`∫_0^∞ δₙ(t) ψ(t) dt → R/2`. -/
theorem tendsto_setIntegral_Ioi_gaussDelta {ψ : ℝ → ℂ} {N : ℕ} (hN : 0 < N) {R : ℂ}
    (hint : IntegrableOn (fun t => (Real.exp (-(N * t ^ 2)) : ℂ) * ψ t) (Ioi 0))
    (hR : Tendsto ψ (𝓝[>] 0) (𝓝 R)) :
    Tendsto (fun n : ℕ => ∫ t in Ioi 0, (gaussDelta n t : ℂ) * ψ t) atTop (𝓝 (R / 2)) := by
  set w : ℝ → ℂ := fun t => (Real.exp (-(N * t ^ 2)) : ℂ)
  have hw : Continuous w := by fun_prop
  have hwi : Integrable w :=
    (integrable_exp_neg_mul_sq' (by exact_mod_cast hN : (0 : ℝ) < N)).ofReal
  set g : ℝ → ℂ := fun t => w t * ψ t - w t * R
  have hg : IntegrableOn g (Ioi 0) := hint.sub (hwi.mul_const R).integrableOn
  have hcg : Tendsto g (𝓝[Ioi 0] 0) (𝓝 0) := by
    have h := (((hw.tendsto 0).mono_left nhdsWithin_le_nhds).mul hR).sub
      (((hw.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))).mul_const R)
    rw [sub_self] at h
    exact h
  have hlφ := fun u hu h0 => tendstoUniformlyOn_gaussPeak N (u := u) hu h0
  have h'iφ : ∀ᶠ n in atTop, AEStronglyMeasurable (gaussPeak N n) (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun n => (continuous_gaussPeak N n).aestronglyMeasurable
  have key := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto_aux measurableSet_Ioi
    measurableSet_Ioi subset_rfl self_mem_nhdsWithin
    (Eventually.of_forall fun n x _ => gaussPeak_nonneg N n x) hlφ
    (tendsto_integral_Ioi_gaussPeak N) h'iφ hg hcg
  have hint' := integrableOn_peak_smul_of_integrableOn_of_tendsto measurableSet_Ioi
    self_mem_nhdsWithin hlφ (tendsto_integral_Ioi_gaussPeak N) h'iφ hg hcg
  have h2 := (key.const_mul (1 / 2 : ℂ)).add_const (R / 2)
  rw [mul_zero, zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [hint', eventually_gt_atTop 0] with n hn hn0
  have hδ : IntegrableOn (fun t => (gaussDelta n t : ℂ) * R) (Ioi 0) :=
    ((integrable_gaussDelta hn0).ofReal.mul_const R).integrableOn
  have e : ∫ t in Ioi 0, (gaussDelta n t : ℂ) * ψ t =
      ∫ t in Ioi 0, ((1 / 2 : ℂ) * (gaussPeak N n t • g t) + (gaussDelta n t : ℂ) * R) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [g, w, Complex.real_smul, gaussDelta_eq_gaussPeak N n t]
    push_cast
    ring
  rw [e, integral_add (hn.const_mul _) hδ, integral_const_mul, integral_mul_const,
    integral_complex_ofReal, integral_Ioi_gaussDelta hn0]
  push_cast
  ring

/-- The general limit behind 1.17.6–1.17.7: if `e^{−n(x−a)²} φ(x)` is integrable for all large
`n` and `φ(a−) = L`, `φ(a+) = R`, then `∫ δₙ(x − a) φ(x) dx → L/2 + R/2`. -/
theorem tendsto_integral_gaussDelta {φ : ℝ → ℂ} {a : ℝ} {L R : ℂ}
    (hint : ∀ᶠ n : ℕ in atTop, Integrable fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * φ x)
    (hL : Tendsto φ (𝓝[<] a) (𝓝 L)) (hR : Tendsto φ (𝓝[>] a) (𝓝 R)) :
    Tendsto (fun n : ℕ => ∫ x, (gaussDelta n (x - a) : ℂ) * φ x) atTop (𝓝 (L / 2 + R / 2)) := by
  obtain ⟨N, hN⟩ := (hint.and (eventually_ge_atTop 1)).exists
  have hN0 : 0 < N := hN.2
  set ψ : ℝ → ℂ := fun t => φ (t + a)
  have hψ : Integrable fun t => (Real.exp (-(N * t ^ 2)) : ℂ) * ψ t := by
    have := hN.1.comp_add_right a
    simpa [ψ] using this
  have hψneg : Integrable fun t => (Real.exp (-(N * t ^ 2)) : ℂ) * ψ (-t) := by
    have := hψ.comp_neg
    simpa using this
  have hRψ : Tendsto ψ (𝓝[>] 0) (𝓝 R) := by
    refine hR.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · have h : Tendsto (fun t : ℝ => t + a) (𝓝 0) (𝓝 (0 + a)) :=
        (by fun_prop : Continuous fun t : ℝ => t + a).tendsto 0
      rw [zero_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      show a < t + a
      linarith
  have hLψ : Tendsto (fun t => ψ (-t)) (𝓝[>] 0) (𝓝 L) := by
    refine hL.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · have h : Tendsto (fun t : ℝ => -t + a) (𝓝 0) (𝓝 (-0 + a)) :=
        (by fun_prop : Continuous fun t : ℝ => -t + a).tendsto 0
      rw [neg_zero, zero_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      show -t + a < a
      linarith
  have h1 := tendsto_setIntegral_Ioi_gaussDelta hN0 hψ.integrableOn hRψ
  have h2 := tendsto_setIntegral_Ioi_gaussDelta hN0 hψneg.integrableOn hLψ
  rw [add_comm]
  refine (h1.add h2).congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hf : Integrable fun t => (gaussDelta n t : ℂ) * ψ t := by
    have := hψ.bdd_mul (c := √(n / π))
      (f := fun t => ((√(n / π) * Real.exp (-(((n : ℝ) - N) * t ^ 2)) : ℝ) : ℂ))
      (by fun_prop) (ae_of_all _ fun t => by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
        have : 0 ≤ ((n : ℝ) - N) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg t)
        linarith)
    refine this.congr (ae_of_all _ fun t => ?_)
    simp only [gaussDelta_eq_gaussPeak N n t, gaussPeak]
    push_cast
    ring
  have e : ∫ x, (gaussDelta n (x - a) : ℂ) * φ x = ∫ t, (gaussDelta n t : ℂ) * ψ t := by
    rw [← integral_sub_right_eq_self (fun t => (gaussDelta n t : ℂ) * ψ t) a]
    simp [ψ]
  rw [e, ← integral_add_compl measurableSet_Ioi hf, compl_Ioi,
    ← neg_zero, ← integral_comp_neg_Ioi, neg_zero]
  simp only [gaussDelta_neg]

/-! ### DLMF 1.17.6–1.17.7 -/

/-- DLMF 1.17.6: for continuous `φ` such that, for each `a`, `∫ e^{−n(x−a)²} φ(x) dx` converges
absolutely for all sufficiently large `n`, `√(n/π) ∫ e^{−n(x−a)²} φ(x) dx → φ(a)`. -/
theorem dlmf_1_17_6 {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hint : ∀ a : ℝ, ∀ᶠ n : ℕ in atTop,
      Integrable fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * φ x) (a : ℝ) :
    Tendsto (fun n : ℕ => ((√(n / π) : ℝ) : ℂ) *
      ∫ x, (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * φ x) atTop (𝓝 (φ a)) := by
  have h := tendsto_integral_gaussDelta (hint a) ((hφ.tendsto a).mono_left nhdsWithin_le_nhds)
    ((hφ.tendsto a).mono_left nhdsWithin_le_nhds)
  rw [add_halves] at h
  refine h.congr fun n => ?_
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [dlmf_1_17_5]
  push_cast
  ring

/-- DLMF §1.17(i): the integrability condition of 1.17.6 holds when `φ` is continuous and
`φ(x) = O(e^{αx²})` as `x → ±∞`; it then holds for every `n > α`. -/
theorem dlmf_1_17_6_growth {φ : ℝ → ℂ} (hφ : Continuous φ) {α : ℝ}
    (htop : φ =O[atTop] fun x => Real.exp (α * x ^ 2))
    (hbot : φ =O[atBot] fun x => Real.exp (α * x ^ 2)) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, Integrable fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * φ x := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop α] with n hn
  have hc : 0 < (n : ℝ) - α := by linarith
  have hloc : LocallyIntegrable fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * φ x :=
    ((by fun_prop : Continuous fun x : ℝ => (Real.exp (-(n * (x - a) ^ 2)) : ℂ)).mul
      hφ).locallyIntegrable
  refine hloc.integrable_of_isBigO_cocompact
    (g := fun x => Real.exp (-(((n : ℝ) - α) / 2 * x ^ 2))) ?_
    ((integrable_exp_neg_mul_sq' (by linarith : 0 < ((n : ℝ) - α) / 2)).integrableAtFilter _)
  have hφc : φ =O[cocompact ℝ] fun x => Real.exp (α * x ^ 2) := by
    rw [cocompact_eq_atBot_atTop]; exact hbot.sup htop
  have he : (fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ)) =O[cocompact ℝ]
      fun x => Real.exp (-(n * (x - a) ^ 2)) :=
    Asymptotics.isBigO_of_le _ fun x => (Complex.norm_real _).le
  have h1 := he.mul hφc
  refine h1.trans (Asymptotics.IsBigO.of_bound (Real.exp (2 * n ^ 2 * a ^ 2 / ((n : ℝ) - α)))
    (Eventually.of_forall fun x => ?_))
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have key : (2 * n ^ 2 * a ^ 2 / ((n : ℝ) - α) + -(((n : ℝ) - α) / 2 * x ^ 2)) -
      (-(n * (x - a) ^ 2) + α * x ^ 2) =
      ((n : ℝ) - α) / 2 * (x - 2 * n * a / ((n : ℝ) - α)) ^ 2 + n * a ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg hc.le (sq_nonneg (x - 2 * n * a / ((n : ℝ) - α))),
    mul_nonneg (n.cast_nonneg : (0 : ℝ) ≤ n) (sq_nonneg a)]

/-- DLMF 1.17.7: for `φ` piecewise continuous on every `[−c, c]` and with the integrability
condition of 1.17.6, the one-sided limits `φ(a±)` exist and
`√(n/π) ∫ e^{−n(x−a)²} φ(x) dx → ½ φ(a−) + ½ φ(a+)`. -/
theorem dlmf_1_17_7 {φ : ℝ → ℝ} (hpc : ∀ c : ℝ, 0 < c → IsPiecewiseContinuous φ (Icc (-c) c))
    (hint : ∀ a : ℝ, ∀ᶠ n : ℕ in atTop,
      Integrable fun x => Real.exp (-(n * (x - a) ^ 2)) * φ x) (a : ℝ) :
    ∃ L R : ℝ, Tendsto φ (𝓝[<] a) (𝓝 L) ∧ Tendsto φ (𝓝[>] a) (𝓝 R) ∧
      Tendsto (fun n : ℕ => √(n / π) * ∫ x, Real.exp (-(n * (x - a) ^ 2)) * φ x) atTop
        (𝓝 (1 / 2 * L + 1 / 2 * R)) := by
  obtain ⟨L, R, hL, hR⟩ : ∃ L R : ℝ, Tendsto φ (𝓝[<] a) (𝓝 L) ∧ Tendsto φ (𝓝[>] a) (𝓝 R) := by
    obtain ⟨S, hS, hdisc⟩ := hpc (|a| + 1) (by positivity)
    have h1 := neg_abs_le a
    have h2 := le_abs_self a
    by_cases haS : a ∈ S
    · obtain ⟨L, R, hR, hL, -⟩ := hdisc a haS
      exact ⟨L, R, hL, hR⟩
    · have hc : ContinuousAt φ a := (hS a ⟨by linarith, by linarith⟩ haS).continuousAt
        (Icc_mem_nhds (by linarith) (by linarith))
      exact ⟨φ a, φ a, hc.tendsto.mono_left nhdsWithin_le_nhds,
        hc.tendsto.mono_left nhdsWithin_le_nhds⟩
  refine ⟨L, R, hL, hR, ?_⟩
  have hintC : ∀ᶠ n : ℕ in atTop,
      Integrable fun x => (Real.exp (-(n * (x - a) ^ 2)) : ℂ) * (φ x : ℂ) :=
    (hint a).mono fun n h => by
      have := h.ofReal (𝕜 := ℂ)
      refine this.congr (ae_of_all _ fun x => ?_)
      norm_cast
  have h := tendsto_integral_gaussDelta hintC ((Complex.continuous_ofReal.tendsto L).comp hL)
    ((Complex.continuous_ofReal.tendsto R).comp hR)
  have e : ∀ n : ℕ, ∫ x, (gaussDelta n (x - a) : ℂ) * (φ x : ℂ) =
      ((√(n / π) * ∫ x, Real.exp (-(n * (x - a) ^ 2)) * φ x : ℝ) : ℂ) := fun n => by
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
    congr 1
    funext x
    rw [dlmf_1_17_5]
    push_cast
    ring
  simp_rw [e] at h
  have h3 := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, Complex.ofReal_re] at h3
  convert h3 using 2
  simp only [Complex.add_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

/-! ### The Gaussian delta sequence is a delta sequence -/

theorem continuous_gaussDelta (n : ℕ) : Continuous (gaussDelta n) := by
  unfold gaussDelta; fun_prop

theorem locallyIntegrableOn_gaussDelta (n : ℕ) (a : ℝ) :
    LocallyIntegrableOn (fun x => (gaussDelta n (x - a) : ℂ)) univ :=
  (Complex.continuous_ofReal.comp ((continuous_gaussDelta n).comp
    (continuous_sub_right a))).locallyIntegrable.locallyIntegrableOn univ

/-- DLMF 1.17.5–1.17.6: `√(n/π) e^{−n x²}` is a delta sequence. -/
theorem isDeltaSequence_gaussDelta : IsDeltaSequence gaussDelta := by
  intro a φ hφ
  have hc := hφ.1.continuous
  have hi : Integrable φ := hc.integrable_of_hasCompactSupport hφ.2.1
  have h := tendsto_integral_gaussDelta (L := φ a) (R := φ a)
    (Eventually.of_forall fun n => hi.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun x => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      have := mul_nonneg (n.cast_nonneg : (0 : ℝ) ≤ n) (sq_nonneg (x - a))
      linarith))
    ((hc.tendsto a).mono_left nhdsWithin_le_nhds) ((hc.tendsto a).mono_left nhdsWithin_le_nhds)
  rwa [add_halves] at h

/-- DLMF 1.17.4 for the Gaussian delta sequence: `√(n/π) e^{−n(x−a)²} → δ(x − a)` in the sense
of distributions. -/
theorem dlmf_1_17_4_gaussDelta (a : ℝ) :
    DistConverges univ (fun n => regularDist isOpen_univ (locallyIntegrableOn_gaussDelta n a))
      (diracDist univ a) :=
  (dlmf_1_17_4 locallyIntegrableOn_gaussDelta).mp isDeltaSequence_gaussDelta a

end Azurite.DLMF
