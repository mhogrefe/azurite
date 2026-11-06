/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2Base
import Azurite.DLMF.Chapter4.Section2Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# DLMF §4.2(iv): Powers

Formalizations of <https://dlmf.nist.gov/4.2.iv>. The principal value `z^a = exp(a ln z)` is
Mathlib's `Complex.cpow` (`z ^ a`, with `0 ^ a = 0` for `a ≠ 0`); the general value is the set
`genPowSet z a = {exp(a w) : w ∈ Ln z}` (`Ln z = genLogSet z`, §4.2(iii)), and the principal value
under the DLMF's closed definition of the cut (§4.2(i), `ph z ∈ [−π, π]`, two-valued on the cut) is
the set `closedPowSet z a`.

* 4.2.26: `genPowSet` (`mem_genPowSet_iff`); `z⁰ = 1` and 4.2.27 for `a = n` and `a = −n`
  (`dlmf_4_2_26_zero`, `dlmf_4_2_27`); "In all other cases, `z^a` is a multivalued function":
  `genPowSet z a` is a single value iff `a ∈ ℤ` (`dlmf_4_2_iv_multivalued`).
* 4.2.28: the principal value (`dlmf_4_2_28`); "an analytic function of `z` on `ℂ ∖ (−∞, 0]`"
  (`dlmf_4_2_iv_analytic`), "two-valued and discontinuous on the cut … unless `a ∈ ℤ`"
  (`dlmf_4_2_iv_closed_cut`, `dlmf_4_2_iv_discontinuous`, `dlmf_4_2_iv_continuous_int`).
* 4.2.29, 4.2.30: modulus and phase of every value `exp(a(ln|z| + iθ))`, `z = |z|e^{iθ}`, `θ`
  unrestricted (`dlmf_4_2_29_30`), and of the principal value (`dlmf_4_2_29`, `dlmf_4_2_30`).
* 4.2.31: `a` real (`dlmf_4_2_31`).
* 4.2.32–4.2.34: `e^z = exp z` (`dlmf_4_2_32`), its general value (`dlmf_4_2_33`), and
  `e = ∑ 1/n!` (`dlmf_4_2_34`).
* 4.2.35: `z^a = w ⟺ z = exp((1/a) Ln w)` for the general value (`dlmf_4_2_35`); 4.2.36 for the
  closed principal value (`dlmf_4_2_36`), and with `−π < Im(Ln w/a) ≤ π` for Mathlib's principal
  value (`dlmf_4_2_36_open`).
* 4.2.37: `√(z²) = z` (`Re z ≥ 0`), `−z` (`Re z ≤ 0`) with the closed definition
  (`dlmf_4_2_37`); with the open definition 4.2.5 only for `Re z > 0`, `Re z < 0`
  (`dlmf_4_2_37_open`), and the non-strict signs fail at `z = ∓i` (`dlmf_4_2_37_open_fails`).

"Unless indicated otherwise, it is assumed throughout the DLMF that a power assumes its principal
value" is a convention. Levinson and Redheffer (1970, pp. 62–67) is a reference.
-/

open Complex Set Filter Topology
open scoped Real

namespace Azurite.DLMF

/-! ### Polar form -/

theorem mul_polar (a : ℂ) (L θ : ℝ) :
    a * (L + θ * I) = ((a.re * L - a.im * θ : ℝ) : ℂ) + ((a.re * θ + a.im * L : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem exp_mul_polar (a : ℂ) (L θ : ℝ) :
    exp (a * (L + θ * I)) =
      (Real.exp (a.re * L - a.im * θ) : ℂ) * exp ((a.re * θ + a.im * L : ℝ) * I) := by
  rw [mul_polar, exp_add, ofReal_exp]

theorem norm_exp_mul_polar (a : ℂ) (L θ : ℝ) :
    ‖exp (a * (L + θ * I))‖ = Real.exp (a.re * L - a.im * θ) := by
  rw [exp_mul_polar, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- The polar decompositions of `z ≠ 0`: `z = |z| e^{iθ}` iff `ln |z| + iθ ∈ Ln z`. -/
theorem polar_iff_mem_genLogSet {z : ℂ} (hz : z ≠ 0) (θ : ℝ) :
    z = ‖z‖ * exp (θ * I) ↔ (Real.log ‖z‖ + θ * I : ℂ) ∈ genLogSet z := by
  rw [← dlmf_4_2_25 hz, exp_add, ← ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz), eq_comm]

theorem mem_genLogSet_iff {z : ℂ} (hz : z ≠ 0) (w : ℂ) : w ∈ genLogSet z ↔ exp w = z :=
  (dlmf_4_2_25 hz w).symm

/-! ### General and principal values -/

/-- **DLMF 4.2.26**: the general value `z^a = exp(a Ln z)`. -/
def genPowSet (z a : ℂ) : Set ℂ := (fun w => exp (a * w)) '' genLogSet z

/-- **DLMF 4.2.26**. -/
theorem mem_genPowSet_iff {z : ℂ} (hz : z ≠ 0) (a v : ℂ) :
    v ∈ genPowSet z a ↔ ∃ w, exp w = z ∧ v = exp (a * w) := by
  simp only [genPowSet, mem_image, mem_genLogSet_iff hz]
  exact ⟨fun ⟨w, h1, h2⟩ => ⟨w, h1, h2.symm⟩, fun ⟨w, h1, h2⟩ => ⟨w, h1, h2.symm⟩⟩

theorem genPowSet_eq {z : ℂ} (a : ℂ) :
    genPowSet z a = {v | ∃ k : ℤ, v = exp (a * log z) * exp (2 * k * π * I * a)} := by
  ext v
  simp only [genPowSet, genLogSet, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨w, ⟨k, rfl⟩, rfl⟩; exact ⟨k, by rw [← exp_add]; ring_nf⟩
  · rintro ⟨k, rfl⟩; exact ⟨_, ⟨k, rfl⟩, by rw [← exp_add]; ring_nf⟩

theorem exp_int_mul (k n : ℤ) : exp (2 * k * π * I * n) = 1 := by
  rw [show 2 * (k : ℂ) * π * I * n = ((k * n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    exp_int_mul_two_pi_mul_I]

/-- For an integer power every value of `exp(n Ln z)` is `exp(n ln z)`. -/
theorem genPowSet_int {z : ℂ} (n : ℤ) : genPowSet z n = {exp (n * log z)} := by
  rw [genPowSet_eq]
  ext v
  simp only [mem_ofPred_eq, mem_singleton_iff, exp_int_mul, mul_one]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩

/-- **DLMF §4.2(iv)**: "`z⁰ = 1`". -/
theorem dlmf_4_2_26_zero (z : ℂ) : genPowSet z 0 = {1} := by
  simpa using genPowSet_int (z := z) 0

/-- **DLMF 4.2.27**: for `a = n = 1, 2, 3, …`, `z^a = z ⋯ z` (`n` times) and `z^{−a} = 1/z^a`
(`z ≠ 0`). -/
theorem dlmf_4_2_27 {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    genPowSet z n = {z ^ n} ∧ genPowSet z (-(n : ℂ)) = {1 / z ^ n} := by
  have h1 := genPowSet_int (z := z) n
  have h2 := genPowSet_int (z := z) (-(n : ℤ))
  push_cast at h1 h2
  refine ⟨?_, ?_⟩
  · rw [h1, mul_comm, ← cpow_def_of_ne_zero hz, cpow_natCast]
  · rw [h2, mul_comm, ← cpow_def_of_ne_zero hz, cpow_neg, cpow_natCast, one_div]

/-- **DLMF §4.2(iv)**: "In all other cases, `z^a` is a multivalued function": for `z ≠ 0` the
general value is single-valued exactly when `a ∈ ℤ`. -/
theorem dlmf_4_2_iv_multivalued {z : ℂ} (a : ℂ) :
    (genPowSet z a).Subsingleton ↔ ∃ k : ℤ, a = k := by
  constructor
  · intro h
    rw [genPowSet_eq] at h
    have := h ⟨0, rfl⟩ ⟨1, rfl⟩
    simp only [Int.cast_zero, mul_zero, zero_mul, exp_zero, mul_one, Int.cast_one] at this
    have h1 : exp (2 * π * I * a) = 1 := by
      have hne := exp_ne_zero (a * log z)
      have := (mul_right_inj' hne).mp (this.symm.trans (mul_one _).symm |>.symm)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
    obtain ⟨n, hn⟩ := exp_eq_one_iff.mp h1
    refine ⟨n, ?_⟩
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have : (2 * π * I) * a = (2 * π * I) * n := by rw [hn]; ring
    exact mul_left_cancel₀ h2 this
  · rintro ⟨k, rfl⟩
    rw [genPowSet_int]
    exact subsingleton_singleton

/-- **DLMF 4.2.28**: the principal value `z^a = exp(a ln z)` (`z ≠ 0`); it is one of the values of
4.2.26. -/
theorem dlmf_4_2_28 {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    z ^ a = exp (a * log z) ∧ z ^ a ∈ genPowSet z a := by
  have h : z ^ a = exp (a * log z) := by rw [cpow_def_of_ne_zero hz, mul_comm]
  refine ⟨h, ?_⟩
  rw [genPowSet_eq]
  exact ⟨0, by simp [h]⟩

/-- **DLMF §4.2(iv)**: "This is an analytic function of `z` on `ℂ ∖ (−∞, 0]`". -/
theorem dlmf_4_2_iv_analytic (a : ℂ) : AnalyticOnNhd ℂ (fun z : ℂ => z ^ a) slitPlane :=
  fun _ hz => analyticAt_id.cpow analyticAt_const hz

/-! ### The closed definition on the cut -/

/-- The principal value under the closed definition: `exp(a(ln|z| + iθ))` with `z = |z|e^{iθ}`,
`θ ∈ [−π, π]` (two values on the cut, `θ = ±π`). -/
def closedPowSet (z a : ℂ) : Set ℂ :=
  {v | ∃ θ : ℝ, -π ≤ θ ∧ θ ≤ π ∧ z = ‖z‖ * exp (θ * I) ∧
    v = exp (a * (Real.log ‖z‖ + θ * I))}

/-- Mathlib's principal value is one of the closed principal values. -/
theorem cpow_mem_closedPowSet {z : ℂ} (hz : z ≠ 0) (a : ℂ) : z ^ a ∈ closedPowSet z a := by
  refine ⟨arg z, (neg_pi_lt_arg z).le, arg_le_pi z, (norm_mul_exp_arg_mul_I z).symm, ?_⟩
  rw [(dlmf_4_2_28 hz a).1]
  congr 2

theorem exp_I_eq_neg_one_iff {θ : ℝ} (h1 : -π ≤ θ) (h2 : θ ≤ π) :
    exp (θ * I) = -1 ↔ θ = π ∨ θ = -π := by
  constructor
  · intro h
    rw [← exp_pi_mul_I, exp_eq_exp_iff_exists_int] at h
    obtain ⟨k, hk⟩ := h
    have := congrArg im hk
    simp at this
    have hk' : θ = π * (1 + 2 * k) := by linarith
    have hpi := Real.pi_pos
    have hk1 : (k : ℝ) ≤ 0 := by
      by_contra hc
      have : (1 : ℝ) ≤ k := by exact_mod_cast (Int.cast_pos.mp (by linarith : (0 : ℝ) < k))
      nlinarith
    have hk2 : (-1 : ℝ) ≤ k := by
      by_contra hc
      have : (k : ℝ) ≤ -2 := by
        have : k < -1 := by exact_mod_cast (by linarith : (k : ℝ) < -1)
        exact_mod_cast (by omega : k ≤ -2)
      nlinarith
    have : k = 0 ∨ k = -1 := by
      have h3 : k ≤ 0 := by exact_mod_cast hk1
      have h4 : -1 ≤ k := by exact_mod_cast hk2
      omega
    rcases this with rfl | rfl
    · left; simpa using hk'
    · right; rw [hk']; push_cast; ring
  · rintro (rfl | rfl)
    · exact exp_pi_mul_I
    · rw [ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I]; norm_num

/-- **DLMF §4.2(iv)**: on the cut `x < 0` the closed principal value has the two values
`exp(a(ln|x| ± iπ))`, which differ unless `a ∈ ℤ`: "two-valued … on the cut". -/
theorem dlmf_4_2_iv_closed_cut {x : ℝ} (hx : x < 0) (a : ℂ) :
    closedPowSet x a = {exp (a * (Real.log |x| + π * I)), exp (a * (Real.log |x| - π * I))} ∧
      (exp (a * (Real.log |x| + π * I)) = exp (a * (Real.log |x| - π * I)) ↔
        ∃ k : ℤ, a = k) := by
  have hn : ‖(x : ℂ)‖ = |x| := by rw [norm_real, Real.norm_eq_abs]
  have hxc : (x : ℂ) = ((|x| : ℝ) : ℂ) * -1 := by
    rw [abs_of_neg hx]; push_cast; ring
  have habs : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hx.ne).ne'
  refine ⟨?_, ?_⟩
  · ext v
    simp only [closedPowSet, hn, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨θ, h1, h2, h3, rfl⟩
      have : exp (θ * I) = -1 := by
        have := h3.symm.trans hxc
        exact mul_left_cancel₀ habs this
      rcases (exp_I_eq_neg_one_iff h1 h2).mp this with rfl | rfl
      · left; rfl
      · right; push_cast; ring_nf
    · rintro (rfl | rfl)
      · exact ⟨π, by linarith [Real.pi_pos], le_rfl, by rw [exp_pi_mul_I]; exact hxc, rfl⟩
      · refine ⟨-π, le_rfl, by linarith [Real.pi_pos], ?_, by push_cast; ring_nf⟩
        rw [ofReal_neg, neg_mul, exp_neg, exp_pi_mul_I]
        rw [hxc]; norm_num
  · rw [exp_eq_exp_iff_exists_int]
    constructor
    · rintro ⟨n, hn'⟩
      refine ⟨n, ?_⟩
      have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have : (2 * π * I) * a = (2 * π * I) * n := by linear_combination hn'
      exact mul_left_cancel₀ h2 this
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ring⟩

/-- **DLMF §4.2(iv)**: the principal value `z^a` is "discontinuous on the cut … unless `a ∈ ℤ`". -/
theorem dlmf_4_2_iv_discontinuous {x : ℝ} (hx : x < 0) {a : ℂ} (ha : ¬ ∃ k : ℤ, a = k) :
    ¬ ContinuousAt (fun z : ℂ => z ^ a) x := by
  intro hc
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne
  have hev : ∀ᶠ z in 𝓝 (x : ℂ), z ^ a = exp (a * log z) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with z hz
    exact (dlmf_4_2_28 hz a).1
  have hcont : Continuous fun w : ℂ => exp (a * w) := by fun_prop
  obtain ⟨hu, hl⟩ := dlmf_4_2_7 hx
  have hu' := ((hcont.tendsto _).comp hu).congr' (eventually_nhdsWithin_of_eventually_nhds
    (hev.mono fun z hz => hz.symm))
  have hl' := ((hcont.tendsto _).comp hl).congr' (eventually_nhdsWithin_of_eventually_nhds
    (hev.mono fun z hz => hz.symm))
  have hbot : ∀ s : Set ℂ, (∀ n : ℕ, (x : ℂ) + (((1 : ℝ) / (n + 1) : ℝ) : ℂ) * I ∈ s ∨ True) →
      True := fun _ _ => trivial
  clear hbot
  have hneU : (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_seq_limit]
    refine ⟨fun n => x + ((1 : ℝ) / (n + 1) : ℝ) * I, fun n => ?_, ?_⟩
    · simp only [mem_ofPred_eq, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero,
        add_zero, mul_one, zero_add]
      positivity
    · have : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((continuous_ofReal.tendsto 0).comp this).mul_const I
      simpa using (tendsto_const_nhds (x := (x : ℂ))).add this
  have hneL : (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_seq_limit]
    refine ⟨fun n => x - ((1 : ℝ) / (n + 1) : ℝ) * I, fun n => ?_, ?_⟩
    · simp only [mem_ofPred_eq, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero,
        add_zero, mul_one, zero_sub, Left.neg_neg_iff]
      positivity
    · have : Tendsto (fun n : ℕ => ((1 : ℝ) / (n + 1) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := ((continuous_ofReal.tendsto 0).comp this).mul_const I
      simpa using (tendsto_const_nhds (x := (x : ℂ))).sub this
  have e1 := tendsto_nhds_unique hu' (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have e2 := tendsto_nhds_unique hl' (hc.tendsto.mono_left nhdsWithin_le_nhds)
  exact ha ((dlmf_4_2_iv_closed_cut hx a).2.mp (e1.trans e2.symm))

/-- **DLMF §4.2(iv)**: for `a ∈ ℤ` the principal value `z^a = zⁿ` is continuous at every point of
the cut. -/
theorem dlmf_4_2_iv_continuous_int {x : ℝ} (hx : x < 0) (k : ℤ) :
    ContinuousAt (fun z : ℂ => z ^ (k : ℂ)) x := by
  have e : (fun z : ℂ => z ^ (k : ℂ)) = fun z => z ^ k := funext fun z => cpow_intCast z k
  rw [e]
  exact continuousAt_zpow₀ _ _ (Or.inl (by exact_mod_cast hx.ne))

/-! ### Modulus and phase -/

/-- **DLMF 4.2.29, 4.2.30** (general value): for `z = |z|e^{iθ}` (`θ` unrestricted) the value
`v = exp(a(ln|z| + iθ))` of `z^a` has `|v| = |z|^{Re a} exp(−(Im a)θ)` and phase
`(Re a)θ + (Im a) ln|z|`. -/
theorem dlmf_4_2_29_30 {z : ℂ} (hz : z ≠ 0) (a : ℂ) {θ : ℝ} (hθ : z = ‖z‖ * exp (θ * I)) :
    exp (a * (Real.log ‖z‖ + θ * I)) ∈ genPowSet z a ∧
      ‖exp (a * (Real.log ‖z‖ + θ * I))‖ = ‖z‖ ^ a.re * Real.exp (-(a.im * θ)) ∧
      exp (a * (Real.log ‖z‖ + θ * I)) = ‖exp (a * (Real.log ‖z‖ + θ * I))‖ *
        exp ((a.re * θ + a.im * Real.log ‖z‖ : ℝ) * I) := by
  have hpos := norm_pos_iff.mpr hz
  refine ⟨⟨_, (polar_iff_mem_genLogSet hz θ).mp hθ, rfl⟩, ?_, ?_⟩
  · rw [norm_exp_mul_polar, sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos hpos, mul_comm a.re]
  · rw [norm_exp_mul_polar, exp_mul_polar]

/-- **DLMF 4.2.29**: `|z^a| = |z|^{Re a} exp(−(Im a) ph z)` for the principal value. -/
theorem dlmf_4_2_29 {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    ‖z ^ a‖ = ‖z‖ ^ a.re * Real.exp (-(a.im * arg z)) := by
  rw [norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg, mul_comm (arg z)]

/-- **DLMF 4.2.30**: `ph(z^a) = (Re a) ph z + (Im a) ln|z|` for the principal value (a value of the
phase: `z^a = |z^a| e^{iφ}` with this `φ`). -/
theorem dlmf_4_2_30 {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    z ^ a = ‖z ^ a‖ * exp ((a.re * arg z + a.im * Real.log ‖z‖ : ℝ) * I) := by
  have h := (dlmf_4_2_29_30 hz a (norm_mul_exp_arg_mul_I z).symm).2.2
  have e : z ^ a = exp (a * (Real.log ‖z‖ + arg z * I)) := by
    rw [(dlmf_4_2_28 hz a).1, log]
  rw [e]; exact h

/-- **DLMF 4.2.31**: for real `a`, `|z^a| = |z|^a` and `ph(z^a) = a ph z`. -/
theorem dlmf_4_2_31 {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    ‖z ^ (a : ℂ)‖ = ‖z‖ ^ a ∧ z ^ (a : ℂ) = ‖z ^ (a : ℂ)‖ * exp ((a * arg z : ℝ) * I) := by
  refine ⟨by simp, ?_⟩
  simpa using dlmf_4_2_30 hz a

/-! ### Powers of `e` -/

/-- **DLMF 4.2.32**: `e^z = exp z` (principal value). -/
theorem dlmf_4_2_32 (z : ℂ) : (Real.exp 1 : ℂ) ^ z = exp z := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos 1).ne'), (dlmf_4_2_12).2.2, one_mul]

/-- **DLMF 4.2.33**: the general value `e^z = (exp z) exp(2kzπi)`, `k ∈ ℤ`. -/
theorem dlmf_4_2_33 (z : ℂ) :
    genPowSet (Real.exp 1) z = {v | ∃ k : ℤ, v = exp z * exp (2 * k * z * π * I)} := by
  rw [genPowSet_eq, (dlmf_4_2_12).2.2, mul_one]
  ext v
  simp only [mem_ofPred_eq]
  exact ⟨fun ⟨k, h⟩ => ⟨k, by rw [h]; ring_nf⟩, fun ⟨k, h⟩ => ⟨k, by rw [h]; ring_nf⟩⟩

/-- **DLMF 4.2.34**: `e = 1 + 1/1! + 1/2! + ⋯`. -/
theorem dlmf_4_2_34 : HasSum (fun n : ℕ => 1 / (n.factorial : ℝ)) (Real.exp 1) := by
  have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) 1
  rw [← Real.exp_eq_exp_ℝ] at this
  simpa using this

/-! ### Inversion -/

/-- **DLMF 4.2.35**: for the general value, `a ≠ 0`, `w ≠ 0` (and `z ≠ 0`, where `z^a` is defined):
`z^a = w ⟺ z = exp((1/a) Ln w)`. -/
theorem dlmf_4_2_35 {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    w ∈ genPowSet z a ↔ ∃ u ∈ genLogSet w, z = exp (u / a) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨a * v, (mem_genLogSet_iff hw _).mpr rfl, ?_⟩
    rw [mul_div_cancel_left₀ _ ha, (mem_genLogSet_iff hz v).mp hv]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u / a, (mem_genLogSet_iff (exp_ne_zero _) _).mpr rfl, ?_⟩
    show exp (a * (u / a)) = w
    rw [mul_div_cancel₀ _ ha, (mem_genLogSet_iff hw u).mp hu]

/-- **DLMF 4.2.36**: for the (closed) principal value, `z^a = w ⟺ z = exp((1/a) Ln w)` with the
branch of `Ln w` satisfying `−π ≤ Im((1/a) Ln w) ≤ π` (`a ≠ 0`, `w ≠ 0`). -/
theorem dlmf_4_2_36 {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    w ∈ closedPowSet z a ↔
      ∃ u ∈ genLogSet w, -π ≤ (u / a).im ∧ (u / a).im ≤ π ∧ z = exp (u / a) := by
  constructor
  · rintro ⟨θ, h1, h2, h3, rfl⟩
    refine ⟨a * (Real.log ‖z‖ + θ * I), (mem_genLogSet_iff hw _).mpr rfl, ?_⟩
    rw [mul_div_cancel_left₀ _ ha]
    refine ⟨by simpa using h1, by simpa using h2, ?_⟩
    rw [exp_add, ← ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz)]
    exact h3
  · rintro ⟨u, hu, h1, h2, rfl⟩
    refine ⟨(u / a).im, h1, h2, ?_, ?_⟩
    · rw [norm_exp]
      conv_lhs => rw [← re_add_im (u / a), exp_add, ← ofReal_exp]
    · rw [norm_exp, Real.log_exp, re_add_im, mul_div_cancel₀ _ ha,
        (mem_genLogSet_iff hw u).mp hu]

/-- **DLMF 4.2.36** for Mathlib's principal value (the open definition 4.2.5): the branch must
satisfy `−π < Im((1/a) Ln w) ≤ π`. -/
theorem dlmf_4_2_36_open {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    z ^ a = w ↔ ∃ u ∈ genLogSet w, -π < (u / a).im ∧ (u / a).im ≤ π ∧ z = exp (u / a) := by
  rw [(dlmf_4_2_28 hz a).1]
  constructor
  · rintro rfl
    refine ⟨a * log z, (mem_genLogSet_iff (exp_ne_zero _) _).mpr rfl, ?_⟩
    rw [mul_div_cancel_left₀ _ ha, log_im]
    exact ⟨neg_pi_lt_arg z, arg_le_pi z, (exp_log hz).symm⟩
  · rintro ⟨u, hu, h1, h2, rfl⟩
    rw [log_exp h1 h2, mul_div_cancel₀ _ ha, (mem_genLogSet_iff hw u).mp hu]

/-! ### Example 4.2.37 -/

/-- **DLMF 4.2.37** (closed definition): `√(z²) = z` for `Re z ≥ 0` and `√(z²) = −z` for
`Re z ≤ 0` (`z ≠ 0`; on `Re z = 0` both are values of the two-valued closed principal root). -/
theorem dlmf_4_2_37 {z : ℂ} (hz : z ≠ 0) :
    (0 ≤ z.re → z ∈ closedPowSet (z ^ 2) (1 / 2)) ∧
      (z.re ≤ 0 → -z ∈ closedPowSet (z ^ 2) (1 / 2)) := by
  have key : ∀ y : ℂ, y ≠ 0 → 0 ≤ y.re → y ∈ closedPowSet (y ^ 2) (1 / 2) := by
    intro y hy hre
    have hpos := norm_pos_iff.mpr hy
    have harg : |arg y| ≤ π / 2 := abs_arg_le_pi_div_two_iff.mpr hre
    obtain ⟨h1, h2⟩ := abs_le.mp harg
    refine ⟨2 * arg y, by linarith, by linarith, ?_, ?_⟩
    · conv_lhs => rw [← norm_mul_exp_arg_mul_I y]
      rw [norm_pow, mul_pow, ← exp_nat_mul]
      push_cast; ring_nf
    · rw [norm_pow, Real.log_pow]
      conv_lhs => rw [← norm_mul_exp_arg_mul_I y]
      rw [← exp_log (show (‖y‖ : ℂ) ≠ 0 by exact_mod_cast hpos.ne'), ← exp_add,
        ← ofReal_log hpos.le]
      congr 1
      push_cast; ring
  refine ⟨key z hz, fun h => ?_⟩
  have := key (-z) (neg_ne_zero.mpr hz) (by simpa using h)
  rwa [neg_sq] at this

/-- **DLMF 4.2.37** with the open definition 4.2.5 (Mathlib's principal value): `√(z²) = z` for
`Re z > 0` and `−z` for `Re z < 0`. -/
theorem dlmf_4_2_37_open {z : ℂ} :
    (0 < z.re → (z ^ 2) ^ (1 / 2 : ℂ) = z) ∧ (z.re < 0 → (z ^ 2) ^ (1 / 2 : ℂ) = -z) := by
  have key : ∀ y : ℂ, 0 < y.re → (y ^ 2) ^ (1 / 2 : ℂ) = y := by
    intro y hre
    have hy : y ≠ 0 := fun h => by simp [h] at hre
    have harg : |arg y| < π / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    obtain ⟨h1, h2⟩ := abs_lt.mp harg
    have hlog : log (y ^ 2) = 2 * log y := by
      have e : exp (2 * log y) = y ^ 2 := by rw [two_mul, exp_add, exp_log hy, sq]
      have him : (2 * log y).im = 2 * arg y := by simp [log_im]
      rw [← e, log_exp] <;> rw [him] <;> linarith
    rw [cpow_def_of_ne_zero (pow_ne_zero 2 hy), hlog]
    rw [show 2 * log y * (1 / 2) = log y by ring, exp_log hy]
  refine ⟨key z, fun h => ?_⟩
  have := key (-z) (by simpa using h)
  rwa [neg_sq] at this

/-- **DLMF §4.2(iv)**: "without the closed definition the `≥` and `≤` signs would have to be
replaced by `>` and `<`": at `z = −i` (`Re z = 0`) the open principal value of `√(z²)` is `i ≠ z`,
and at `z = i` it is `i ≠ −z`. -/
theorem dlmf_4_2_37_open_fails :
    ((-I) ^ 2) ^ (1 / 2 : ℂ) ≠ -I ∧ (I ^ 2) ^ (1 / 2 : ℂ) ≠ -I := by
  have h : (-1 : ℂ) ^ (1 / 2 : ℂ) = I := by
    rw [cpow_def_of_ne_zero (by norm_num), log_neg_one, show π * I * (1 / 2) = (π / 2 : ℝ) * I by
      push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simp
  have hI : I ≠ -I := by
    intro h'
    have := congrArg im h'
    simp at this
    linarith
  refine ⟨?_, ?_⟩ <;> simp only [neg_sq, I_sq, h] <;> exact hI

end Azurite.DLMF
