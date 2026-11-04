/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# DLMF §3.5(vii): oscillatory integrals

The integrals 3.5.34 (`oscCos`, `oscSin`) and Longman's method for infinite oscillatory integrals:
"the integral is written as an alternating series of positive and negative subintegrals". Under
the classical hypotheses (`f` decreasing on `[0, ∞)` with limit `0`, `ω > 0`):

* `longman_core`: for `f(x) sin(ω(x − c))` on `[c, ∞)`, the subintegrals `longmanI` over the
  half-periods between consecutive zeros alternate in sign, decrease in magnitude
  (`longmanA_antitone`) to `0` (`longmanA_tendsto`), their series converges (alternating series
  test), and its sum is the improper integral (`sum_longmanI`, `longman_rem_le`).
* `dlmf_3_5_vii_longman_sin`: `∫_0^∞ f(x) sin(ωx) dx = ∑_k ∫_{kπ/ω}^{(k+1)π/ω}` (`I_0 ≥ 0`,
  `I_1 ≤ 0`, …).
* `dlmf_3_5_vii_longman_cos`: `∫_0^∞ f(x) cos(ωx) dx = ∫_0^{π/(2ω)} + ∑_k J_k` with `J_k`
  (`longmanJ`) between the zeros `(k + ½)π/ω` (`J_0 ≤ 0`, `J_1 ≥ 0`, …).

Filon's rule, Wong's Gaussian-quadrature method, the Evans–Webster comparison, Levin's
transformation (§3.9(v)), Clendenin, Lyness and the Iserles et al. survey are references only.
-/

open Filter Topology Finset Set Real MeasureTheory

namespace Azurite.DLMF

/-- The oscillatory integrals 3.5.34: `∫_a^b f(x) cos(ωx) dx`. -/
noncomputable def oscCos (f : ℝ → ℝ) (ω a b : ℝ) : ℝ := ∫ x in a..b, f x * cos (ω * x)

/-- The oscillatory integrals 3.5.34: `∫_a^b f(x) sin(ωx) dx`. -/
noncomputable def oscSin (f : ℝ → ℝ) (ω a b : ℝ) : ℝ := ∫ x in a..b, f x * sin (ω * x)

/-! ### Longman's method: the core lemma -/

section Core

variable {f : ℝ → ℝ} {ω c : ℝ}

/-- The subintegral of `f(x) sin(ω(x − c))` over its `k`-th half-period
`[c + kπ/ω, c + (k+1)π/ω]`. -/
noncomputable def longmanI (f : ℝ → ℝ) (ω c : ℝ) (k : ℕ) : ℝ :=
  ∫ x in c + k * (π / ω)..c + (k + 1) * (π / ω), f x * sin (ω * (x - c))

/-- Its magnitude `∫_0^{π/ω} f(c + kπ/ω + s) sin(ωs) ds`. -/
noncomputable def longmanA (f : ℝ → ℝ) (ω c : ℝ) (k : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..π / ω, f (c + k * (π / ω) + s) * sin (ω * s)

theorem longman_f_nonneg (hf : AntitoneOn f (Ici 0)) (h0 : Tendsto f atTop (𝓝 0)) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ f x := by
  refine le_of_tendsto h0 ?_
  filter_upwards [eventually_ge_atTop x] with y hy
  exact hf hx (hx.trans hy) hy

theorem longman_intervalIntegrable (hf : AntitoneOn f (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (g : ℝ → ℝ)
    (hg : Continuous g) : IntervalIntegrable (fun x => f x * g x) volume a b :=
  (AntitoneOn.intervalIntegrable (hf.mono fun _ hx => (le_min ha hb).trans hx.1)).mul_continuousOn
    hg.continuousOn

theorem longmanI_eq (hω : 0 < ω) (k : ℕ) : longmanI f ω c k = (-1) ^ k * longmanA f ω c k := by
  rw [longmanI, longmanA, ← intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_add_left
    (fun x => f x * sin (ω * (x - c))) (c + k * (π / ω)) (a := 0) (b := π / ω)
  simp only [add_zero] at h
  rw [show c + (k + 1) * (π / ω) = c + k * (π / ω) + π / ω by ring, ← h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show ω * (c + k * (π / ω) + s - c) = ω * s + k * π by field_simp; ring, sin_add_nat_mul_pi]
  ring

theorem sin_nonneg_half (hω : 0 < ω) (s : ℝ) (hs : s ∈ Icc 0 (π / ω)) : 0 ≤ sin (ω * s) := by
  apply sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hs.1])
  have := hs.2
  rw [le_div_iff₀ hω] at this
  linarith

theorem longmanA_nonneg (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0))
    (h0 : Tendsto f atTop (𝓝 0)) (k : ℕ) : 0 ≤ longmanA f ω c k := by
  have hpos : 0 ≤ π / ω := (div_pos pi_pos hω).le
  refine intervalIntegral.integral_nonneg hpos fun s hs => mul_nonneg ?_ (sin_nonneg_half hω s hs)
  exact longman_f_nonneg hf h0 (by have := hs.1; positivity)

theorem longmanA_integrable (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0)) (k : ℕ) :
    IntervalIntegrable (fun s => f (c + k * (π / ω) + s) * sin (ω * s)) volume 0 (π / ω) := by
  have hpos : 0 ≤ π / ω := (div_pos pi_pos hω).le
  have ht : 0 ≤ c + k * (π / ω) := by positivity
  refine (AntitoneOn.intervalIntegrable ?_).mul_continuousOn (by fun_prop)
  intro x hx y hy hxy
  rw [uIcc_of_le hpos] at hx hy
  exact hf (by simp only [Set.mem_Ici]; linarith [hx.1])
    (by simp only [Set.mem_Ici]; linarith [hy.1])
    (by linarith)

theorem longmanA_antitone (hω : 0 < ω) (hc : 0 ≤ c)
    (hf : AntitoneOn f (Ici 0)) : Antitone (longmanA f ω c) := by
  have hpos : 0 ≤ π / ω := (div_pos pi_pos hω).le
  refine antitone_nat_of_succ_le fun k => ?_
  refine intervalIntegral.integral_mono_on hpos (longmanA_integrable hω hc hf (k + 1))
    (longmanA_integrable hω hc hf k) fun s hs => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sin_nonneg_half hω s hs)
  have hk : 0 ≤ c + k * (π / ω) := by positivity
  push_cast
  exact hf (by simp only [Set.mem_Ici]; linarith [hs.1])
    (by simp only [Set.mem_Ici]; nlinarith [hs.1])
    (by nlinarith)

theorem integral_sin_half (hω : 0 < ω) : ∫ s in (0 : ℝ)..π / ω, sin (ω * s) = 2 / ω := by
  rw [intervalIntegral.integral_comp_mul_left (fun s => sin s) hω.ne', integral_sin]
  simp only [mul_zero, cos_zero]
  rw [show ω * (π / ω) = π by field_simp, cos_pi, div_eq_inv_mul]
  ring

theorem longmanA_le (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0))
    (k : ℕ) : longmanA f ω c k ≤ f (c + k * (π / ω)) * (2 / ω) := by
  have hpos : 0 ≤ π / ω := (div_pos pi_pos hω).le
  have hk : 0 ≤ c + k * (π / ω) := by positivity
  rw [← integral_sin_half hω, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hpos (longmanA_integrable hω hc hf k)
    ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _) fun s hs =>
      mul_le_mul_of_nonneg_right ?_ (sin_nonneg_half hω s hs)
  exact hf (by simp only [Set.mem_Ici]; exact hk) (by simp only [Set.mem_Ici]; linarith [hs.1])
    (by linarith [hs.1])

theorem longmanA_tendsto (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0))
    (h0 : Tendsto f atTop (𝓝 0)) : Tendsto (longmanA f ω c) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => c + k * (π / ω)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const
      (div_pos pi_pos hω))
  have hu : Tendsto (fun k : ℕ => f (c + k * (π / ω)) * (2 / ω)) atTop (𝓝 0) := by
    simpa using (h0.comp ht).mul_const (2 / ω)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (longmanA_nonneg hω hc hf h0) (longmanA_le hω hc hf)

theorem sum_longmanI (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0)) (N : ℕ) :
    ∑ k ∈ range N, longmanI f ω c k =
      ∫ x in c..c + N * (π / ω), f x * sin (ω * (x - c)) := by
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x => f x * sin (ω * (x - c))) (μ := volume)
    (a := fun k : ℕ => c + k * (π / ω)) (n := N) fun k _ =>
      longman_intervalIntegrable hf (by positivity) (by positivity) _ (by fun_prop)
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ] at h
  rw [← h]
  rfl

/-- The remainder over a partial half-period is bounded by the full subintegral. -/
theorem longman_rem_le (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0))
    (h0 : Tendsto f atTop (𝓝 0)) (N : ℕ) {b : ℝ} (hb1 : c + N * (π / ω) ≤ b)
    (hb2 : b ≤ c + (N + 1) * (π / ω)) :
    |∫ x in c + N * (π / ω)..b, f x * sin (ω * (x - c))| ≤ longmanA f ω c N := by
  have hpos : 0 ≤ π / ω := (div_pos pi_pos hω).le
  have h := intervalIntegral.integral_comp_add_left
    (fun x => f x * sin (ω * (x - c))) (c + N * (π / ω)) (a := 0) (b := b - (c + N * (π / ω)))
  simp only [add_zero, add_sub_cancel] at h
  rw [← h]
  have e : ∀ s, f (c + N * (π / ω) + s) * sin (ω * (c + N * (π / ω) + s - c)) =
      (-1) ^ N * (f (c + N * (π / ω) + s) * sin (ω * s)) := fun s => by
    rw [show ω * (c + N * (π / ω) + s - c) = ω * s + N * π by field_simp; ring,
      sin_add_nat_mul_pi]
    ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  set u := b - (c + N * (π / ω))
  have hu0 : 0 ≤ u := by simp only [u]; linarith
  have hu1 : u ≤ π / ω := by simp only [u]; linarith
  have hnn : ∀ s ∈ Icc (0 : ℝ) (π / ω), 0 ≤ f (c + N * (π / ω) + s) * sin (ω * s) :=
    fun s hs => mul_nonneg (longman_f_nonneg hf h0 (by have := hs.1; positivity))
      (sin_nonneg_half hω s hs)
  have hI := longmanA_integrable hω hc hf (c := c) N
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg hu0 fun s hs =>
    hnn s ⟨hs.1, hs.2.trans hu1⟩)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI.mono_set (by rw [uIcc_of_le hu0, uIcc_of_le hpos]; exact Icc_subset_Icc le_rfl hu1))
    (hI.mono_set (by rw [uIcc_of_le hu1, uIcc_of_le hpos]; exact Icc_subset_Icc hu0 le_rfl))
  rw [longmanA, ← hsplit]
  have := intervalIntegral.integral_nonneg (μ := volume) hu1 fun s hs =>
    hnn s ⟨hu0.trans hs.1, hs.2⟩
  linarith

/-- **Longman's method** (core): the subintegrals alternate in sign, decrease in magnitude to `0`,
their series converges, and its sum is the improper integral `∫_c^∞ f(x) sin(ω(x − c)) dx`. -/
theorem longman_core (hω : 0 < ω) (hc : 0 ≤ c) (hf : AntitoneOn f (Ici 0))
    (h0 : Tendsto f atTop (𝓝 0)) :
    (∀ k, 0 ≤ (-1) ^ k * longmanI f ω c k) ∧
    Antitone (fun k => (-1) ^ k * longmanI f ω c k) ∧
    Tendsto (fun k => (-1) ^ k * longmanI f ω c k) atTop (𝓝 0) ∧
    ∃ L, Tendsto (fun N => ∑ k ∈ range N, longmanI f ω c k) atTop (𝓝 L) ∧
      Tendsto (fun b => ∫ x in c..b, f x * sin (ω * (x - c))) atTop (𝓝 L) := by
  have hpos : 0 < π / ω := div_pos pi_pos hω
  have hA : ∀ k, (-1) ^ k * longmanI f ω c k = longmanA f ω c k := fun k => by
    rw [longmanI_eq hω, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
  simp only [hA]
  refine ⟨longmanA_nonneg hω hc hf h0, longmanA_antitone hω hc hf,
    longmanA_tendsto hω hc hf h0, ?_⟩
  obtain ⟨L, hL⟩ := (longmanA_antitone hω hc hf).tendsto_alternating_series_of_tendsto_zero
    (longmanA_tendsto hω hc hf h0)
  have hS : ∀ N, ∑ k ∈ range N, longmanI f ω c k = ∑ i ∈ range N, (-1) ^ i * longmanA f ω c i :=
    fun N => sum_congr rfl fun k _ => longmanI_eq hω k
  refine ⟨L, by simpa only [hS] using hL, ?_⟩
  -- the improper integral
  set N : ℝ → ℕ := fun b => ⌊(b - c) / (π / ω)⌋₊
  have hN : Tendsto N atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_atTop_add_const_right _ (-c) tendsto_id).atTop_div_const
      hpos |>.congr fun b => by simp [sub_eq_add_neg])
  have hdecomp : ∀ᶠ b in atTop, ∫ x in c..b, f x * sin (ω * (x - c)) =
      ∑ k ∈ range (N b), longmanI f ω c k +
        ∫ x in c + (N b) * (π / ω)..b, f x * sin (ω * (x - c)) := by
    filter_upwards [eventually_ge_atTop c] with b hb
    have hq : 0 ≤ (b - c) / (π / ω) := div_nonneg (by linarith) hpos.le
    have h1 : (N b : ℝ) * (π / ω) ≤ b - c := by
      have := Nat.floor_le hq; rw [le_div_iff₀ hpos] at this; exact this
    rw [sum_longmanI hω hc hf, intervalIntegral.integral_add_adjacent_intervals
      (longman_intervalIntegrable hf hc (by positivity) _ (by fun_prop))
      (longman_intervalIntegrable hf (by positivity) (by linarith) _ (by fun_prop))]
  have hrem : Tendsto (fun b => ∫ x in c + (N b) * (π / ω)..b, f x * sin (ω * (x - c)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((longmanA_tendsto hω hc hf h0).comp hN)
    filter_upwards [eventually_ge_atTop c] with b hb
    have hq : 0 ≤ (b - c) / (π / ω) := div_nonneg (by linarith) hpos.le
    have h1 : (N b : ℝ) * (π / ω) ≤ b - c := by
      have := Nat.floor_le hq; rw [le_div_iff₀ hpos] at this; exact this
    have h2 : b - c < ((N b : ℝ) + 1) * (π / ω) := by
      have := Nat.lt_floor_add_one ((b - c) / (π / ω)); rw [div_lt_iff₀ hpos] at this
      exact this
    rw [Real.norm_eq_abs]
    exact longman_rem_le hω hc hf h0 (N b) (by linarith) (by linarith)
  have hsum : Tendsto (fun b => ∑ k ∈ range (N b), longmanI f ω c k) atTop (𝓝 L) := by
    have := hL.comp hN
    simp only [Function.comp_def] at this
    simpa only [hS] using this
  have := hsum.add hrem
  rw [add_zero] at this
  exact this.congr' (hdecomp.mono fun b hb => hb.symm)

end Core

/-! ### Longman's method for 3.5.34 on `[0, ∞)` -/

section Longman

variable {f : ℝ → ℝ} {ω : ℝ} (hω : 0 < ω) (hf : AntitoneOn f (Ici 0))
  (h0 : Tendsto f atTop (𝓝 0))
include hω hf h0

/-- **Longman's method** for `∫_0^∞ f(x) sin(ωx) dx` (`f` decreasing to `0`, `ω > 0`): with the
subintegrals `I_k = ∫_{kπ/ω}^{(k+1)π/ω} f(x) sin(ωx) dx` between consecutive zeros of `sin(ωx)`,
`I_0 ≥ 0, I_1 ≤ 0, …` alternate in sign with decreasing magnitudes tending to `0`, the alternating
series `∑ I_k` converges, and its sum is the improper integral. -/
theorem dlmf_3_5_vii_longman_sin :
    (∀ k, 0 ≤ (-1) ^ k * longmanI f ω 0 k) ∧
    Antitone (fun k => (-1) ^ k * longmanI f ω 0 k) ∧
    Tendsto (fun k => (-1) ^ k * longmanI f ω 0 k) atTop (𝓝 0) ∧
    ∃ L, Tendsto (fun N => ∑ k ∈ range N, longmanI f ω 0 k) atTop (𝓝 L) ∧
      Tendsto (fun b => oscSin f ω 0 b) atTop (𝓝 L) := by
  have h := longman_core hω le_rfl hf h0
  simp only [sub_zero] at h
  exact h

omit hω hf h0 in
theorem longmanI_sin_eq (k : ℕ) :
    longmanI f ω 0 k = ∫ x in k * (π / ω)..(k + 1) * (π / ω), f x * sin (ω * x) := by
  simp [longmanI]

/-- The subintegral of `f(x) cos(ωx)` between consecutive zeros `(k + ½)π/ω`, `(k + 3/2)π/ω`. -/
noncomputable def longmanJ (f : ℝ → ℝ) (ω : ℝ) (k : ℕ) : ℝ :=
  ∫ x in π / (2 * ω) + k * (π / ω)..π / (2 * ω) + (k + 1) * (π / ω), f x * cos (ω * x)

omit hω hf h0 in
theorem cos_eq_neg_sin_shift (hω' : ω ≠ 0) (x : ℝ) :
    cos (ω * x) = -sin (ω * (x - π / (2 * ω))) := by
  rw [show ω * (x - π / (2 * ω)) = ω * x - π / 2 by field_simp, sin_sub_pi_div_two, neg_neg]

/-- **Longman's method** for `∫_0^∞ f(x) cos(ωx) dx`: after the first piece `[0, π/(2ω)]`, the
subintegrals `J_k` between consecutive zeros of `cos(ωx)` alternate in sign (`J_0 ≤ 0`,
`J_1 ≥ 0`, …) with decreasing magnitudes tending to `0`, and
`∫_0^∞ = ∫_0^{π/(2ω)} + ∑ J_k`. -/
theorem dlmf_3_5_vii_longman_cos :
    (∀ k, 0 ≤ (-1) ^ (k + 1) * longmanJ f ω k) ∧
    Antitone (fun k => (-1) ^ (k + 1) * longmanJ f ω k) ∧
    Tendsto (fun k => (-1) ^ (k + 1) * longmanJ f ω k) atTop (𝓝 0) ∧
    ∃ L, Tendsto (fun N => ∑ k ∈ range N, longmanJ f ω k) atTop (𝓝 L) ∧
      Tendsto (fun b => oscCos f ω 0 b) atTop (𝓝 (oscCos f ω 0 (π / (2 * ω)) + L)) := by
  have hc : 0 ≤ π / (2 * ω) := by positivity
  obtain ⟨h1, h2, h3, L, h4, h5⟩ := longman_core hω hc hf h0
  have hJ : ∀ k, longmanJ f ω k = -longmanI f ω (π / (2 * ω)) k := fun k => by
    rw [longmanJ, longmanI, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [cos_eq_neg_sin_shift hω.ne']; ring
  have hJ' : ∀ k, (-1) ^ (k + 1) * longmanJ f ω k =
      (-1) ^ k * longmanI f ω (π / (2 * ω)) k := fun k => by rw [hJ, pow_succ]; ring
  simp only [hJ']
  refine ⟨h1, h2, h3, -L, ?_, ?_⟩
  · simpa only [hJ, sum_neg_distrib] using h4.neg
  · have hint : ∀ b, 0 ≤ b → IntervalIntegrable (fun x => f x * cos (ω * x)) volume 0 b :=
      fun b hb => longman_intervalIntegrable hf le_rfl hb _ (by fun_prop)
    have hcos : ∀ b, ∫ x in π / (2 * ω)..b, f x * cos (ω * x) =
        -∫ x in π / (2 * ω)..b, f x * sin (ω * (x - π / (2 * ω))) := fun b => by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [cos_eq_neg_sin_shift hω.ne']; ring
    have := tendsto_const_nhds (x := oscCos f ω 0 (π / (2 * ω))) |>.add h5.neg
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (π / (2 * ω))] with b hb
    rw [oscCos, oscCos, ← intervalIntegral.integral_add_adjacent_intervals (hint _ hc)
      (longman_intervalIntegrable hf hc (hc.trans hb) _ (by fun_prop)), hcos]

end Longman

end Azurite.DLMF
