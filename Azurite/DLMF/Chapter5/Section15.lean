/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section7
import Azurite.DLMF.Chapter5.Section5
import Azurite.DLMF.Chapter5.Section14Carlson
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# DLMF §5.15: Polygamma functions

Formalization of <https://dlmf.nist.gov/5.15>. Following DLMF, `ψ⁽ⁿ⁾ = dⁿψ/dzⁿ`
(`polygamma n = iteratedDeriv n digamma`, Mathlib's `digamma = Γ′/Γ`).

The basic result is the series
`ψ⁽ⁿ⁾(z) = (−1)ⁿ⁺¹ n! ∑_{k≥0} (k + z)^{−n−1}`, `n ≥ 1`, `z ≠ 0, −1, …`
(`hasSum_polygamma`), obtained from 5.7.6 by termwise differentiation of locally uniformly
convergent series. It gives 5.15.1 (`n = 1`), 5.15.2 (`z = 1`), 5.15.3 (`z = ½`, splitting
`ζ` into odd and even terms), 5.15.5 (shift of the index) and hence 5.15.4.
-/

open Complex Filter Topology Set Finset
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- The polygamma function `ψ⁽ⁿ⁾(z) = dⁿψ(z)/dzⁿ`. -/
noncomputable def polygamma (n : ℕ) : ℂ → ℂ := iteratedDeriv n digamma

/-- The terms `(k + z)^{−n−1}` of the series of `ψ⁽ⁿ⁾`. -/
noncomputable def polyTerm (n k : ℕ) (z : ℂ) : ℂ := ((k : ℂ) + z) ^ (-((n : ℤ) + 1))

/-- `∑_{k≥0} (k + z)^{−n−1}`. -/
noncomputable def polySeries (n : ℕ) (z : ℂ) : ℂ := ∑' k, polyTerm n k z

theorem isOpen_compl_gammaPoles : IsOpen gammaPolesᶜ := isClosed_gammaPoles.isOpen_compl

theorem hasDerivAt_polyTerm (n k : ℕ) {z : ℂ} (hz : (k : ℂ) + z ≠ 0) :
    HasDerivAt (polyTerm n k) (-((n : ℂ) + 1) * polyTerm (n + 1) k z) z := by
  have h := (hasDerivAt_zpow (-((n : ℤ) + 1)) ((k : ℂ) + z) (Or.inl hz)).comp z
    ((hasDerivAt_id z).const_add (k : ℂ))
  have h' : HasDerivAt (fun w => ((k : ℂ) + w) ^ (-((n : ℤ) + 1))) _ z := h
  unfold polyTerm
  convert h' using 1
  rw [mul_one, show -(((n + 1 : ℕ) : ℤ) + 1) = -((n : ℤ) + 1) - 1 by push_cast; ring]
  push_cast
  ring

theorem polyTerm_bound {n : ℕ} (hn : 1 ≤ n) {z₀ : ℂ} (hz₀ : z₀ ∉ gammaPoles) :
    ∃ r > 0, ∃ M : ℝ, ∀ w ∈ Metric.ball z₀ r, ∀ k : ℕ,
      ‖polyTerm n k w‖ ≤ M * (1 / ((k : ℝ) + 1) ^ 2) ∧ (k : ℂ) + w ≠ 0 := by
  obtain ⟨r, hr, c, hc, h⟩ := exists_norm_add_nat_ge hz₀
  refine ⟨r, hr, (c ^ (n + 1))⁻¹, fun w hw k => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hwk := h w hw k
  have hpos : 0 < ‖w + k‖ := lt_of_lt_of_le (by positivity) hwk
  have hne : (k : ℂ) + w ≠ 0 := by rw [add_comm]; exact norm_pos_iff.mp hpos
  refine ⟨?_, hne⟩
  rw [polyTerm, norm_zpow, zpow_neg, ← Int.natCast_succ, zpow_natCast, add_comm (k : ℂ) w]
  have h1 : (c * ((k : ℝ) + 1)) ^ (n + 1) ≤ ‖w + k‖ ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) hwk _
  have h2 : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  rw [mul_pow] at h1
  calc (‖w + k‖ ^ (n + 1))⁻¹ ≤ (c ^ (n + 1) * ((k : ℝ) + 1) ^ (n + 1))⁻¹ :=
        inv_anti₀ (by positivity) h1
    _ ≤ (c ^ (n + 1) * ((k : ℝ) + 1) ^ 2)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
    _ = _ := by rw [mul_inv]; ring

theorem summable_polyTerm {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∉ gammaPoles) :
    Summable fun k => polyTerm n k z := by
  obtain ⟨r, hr, M, h⟩ := polyTerm_bound hn hz
  exact Summable.of_norm_bounded (summable_inv_succ_sq.mul_left M)
    fun k => (h z (Metric.mem_ball_self hr) k).1

/-- `(∑ (k + z)^{−n−1})′ = −(n + 1) ∑ (k + z)^{−n−2}`. -/
theorem hasDerivAt_polySeries {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∉ gammaPoles) :
    HasDerivAt (polySeries n) (-((n : ℂ) + 1) * polySeries (n + 1) z) z := by
  obtain ⟨r, hr, M, h⟩ := polyTerm_bound hn hz
  have hdo : ∀ k, DifferentiableOn ℂ (polyTerm n k) (Metric.ball z r) := fun k w hw =>
    (hasDerivAt_polyTerm n k (h w hw k).2).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ (polySeries n) (Metric.ball z r) :=
    differentiableOn_tsum_of_summable_norm (summable_inv_succ_sq.mul_left M) hdo
      Metric.isOpen_ball fun k w hw => (h w hw k).1
  have hs := hasSum_deriv_of_summable_norm (summable_inv_succ_sq.mul_left M) hdo
    Metric.isOpen_ball (fun k w hw => (h w hw k).1) (Metric.mem_ball_self hr)
  have hval : deriv (polySeries n) z = -((n : ℂ) + 1) * polySeries (n + 1) z := by
    refine hs.unique ?_
    simp_rw [(hasDerivAt_polyTerm n _ (h z (Metric.mem_ball_self hr) _).2).deriv]
    exact (summable_polyTerm (by omega) hz).hasSum.mul_left _
  rw [← hval]
  exact (hd.differentiableAt (Metric.ball_mem_nhds z hr)).hasDerivAt

theorem digamma_eq_psiSeries {z : ℂ} (hz : z ∉ gammaPoles) : digamma z = psiSeries z - γ := by
  have h := (dlmf_5_7_6 hz).tsum_eq
  show digamma z = (∑' k : ℕ, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z))) - γ
  rw [h]; ring

theorem deriv_psiSeries {z : ℂ} (hz : z ∉ gammaPoles) : deriv psiSeries z = polySeries 1 z := by
  obtain ⟨r, hr, M, h⟩ := exists_psiTerm_bound hz
  have hdt : ∀ (k : ℕ) (w : ℂ), (k : ℂ) + w ≠ 0 → HasDerivAt (psiTerm k) (polyTerm 1 k w) w :=
    fun k w hw => by
      have h1 := ((hasDerivAt_id w).const_add (k : ℂ)).inv hw
      have h2 := (hasDerivAt_const w (1 / ((k : ℂ) + 1))).sub h1
      refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      · unfold polyTerm
        push_cast
        simp only [id, zpow_neg, zpow_two]
        ring
      · simp [psiTerm, one_div]
  have hdo : ∀ k, DifferentiableOn ℂ (psiTerm k) (Metric.ball z r) := fun k w hw =>
    (hdt k w (h w hw k).2).differentiableAt.differentiableWithinAt
  have hs := hasSum_deriv_of_summable_norm (summable_inv_succ_sq.mul_left M) hdo
    Metric.isOpen_ball (fun k w hw => (h w hw k).1) (Metric.mem_ball_self hr)
  simp_rw [(hdt _ z (h z (Metric.mem_ball_self hr) _).2).deriv] at hs
  exact hs.unique (summable_polyTerm le_rfl hz).hasSum |>.symm.symm

/-- `ψ⁽ⁿ⁾ = (−1)ⁿ⁺¹ n! ∑ (k + z)^{−n−1}` off the poles, `n ≥ 1`. -/
theorem polygamma_eq_series {n : ℕ} (hn : 1 ≤ n) :
    EqOn (polygamma n) (fun z => (-1) ^ (n + 1) * (n ! : ℂ) * polySeries n z) gammaPolesᶜ := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro z hz
    have hev : digamma =ᶠ[𝓝 z] fun w => psiSeries w - γ := by
      filter_upwards [isOpen_compl_gammaPoles.mem_nhds hz] with w hw
      exact digamma_eq_psiSeries hw
    show iteratedDeriv 1 digamma z = _
    rw [iteratedDeriv_one, hev.deriv_eq, deriv_sub_const, deriv_psiSeries hz]
    simp
  | succ n hn ih =>
    intro z hz
    have hev : polygamma n =ᶠ[𝓝 z] fun w => (-1) ^ (n + 1) * (n ! : ℂ) * polySeries n w := by
      filter_upwards [isOpen_compl_gammaPoles.mem_nhds hz] with w hw
      exact ih hw
    have hp : polygamma (n + 1) z = deriv (polygamma n) z := by
      show iteratedDeriv (n + 1) digamma z = deriv (iteratedDeriv n digamma) z
      rw [iteratedDeriv_succ]
    rw [hp, hev.deriv_eq, ((hasDerivAt_polySeries hn hz).const_mul _).deriv]
    simp only [Nat.factorial_succ]
    push_cast
    ring

/-- `ψ⁽ⁿ⁾(z) = (−1)ⁿ⁺¹ n! ∑_{k≥0} (k + z)^{−n−1}`, `n ≥ 1`, `z ≠ 0, −1, …`. -/
theorem hasSum_polygamma {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∉ gammaPoles) :
    HasSum (fun k : ℕ => (-1) ^ (n + 1) * (n ! : ℂ) / ((k : ℂ) + z) ^ (n + 1))
      (polygamma n z) := by
  have he := polygamma_eq_series hn hz
  simp only at he
  rw [he, polySeries]
  convert (summable_polyTerm hn hz).hasSum.mul_left ((-1) ^ (n + 1) * (n ! : ℂ)) using 1
  funext k
  rw [polyTerm, zpow_neg, ← Int.natCast_succ, zpow_natCast, div_eq_mul_inv]

/-- **DLMF 5.15.1**: `ψ′(z) = ∑_{k≥0} 1/(k + z)²`, `z ≠ 0, −1, …`. -/
theorem dlmf_5_15_1 {z : ℂ} (hz : z ∉ gammaPoles) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + z) ^ 2) (polygamma 1 z) := by
  simpa using hasSum_polygamma le_rfl hz

theorem polygamma_one_eq_deriv (z : ℂ) : polygamma 1 z = deriv digamma z := by
  simp [polygamma]

/-- `∑_{k≥0} 1/(k + 1)^{n+1} = ζ(n + 1)`. -/
theorem hasSum_inv_succ_pow_zeta {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ (n + 1)) (riemannZeta ((n : ℂ) + 1)) := by
  have h := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (n : ℂ) + 1) (by
    simp; exact_mod_cast hn)
  have hs : Summable fun k : ℕ => 1 / ((k : ℂ) + 1) ^ (n + 1) := by
    refine Summable.of_norm_bounded (summable_inv_succ_sq) fun k => ?_
    rw [norm_div, norm_one, norm_pow, show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast
    rw [one_div, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
      (by omega))
  have e : (fun k : ℕ => 1 / ((k : ℂ) + 1) ^ ((n : ℂ) + 1)) =
      fun k : ℕ => 1 / ((k : ℂ) + 1) ^ (n + 1) := funext fun k => by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
  rw [h, e]
  exact hs.hasSum

/-- **DLMF 5.15.2**: `ψ⁽ⁿ⁾(1) = (−1)ⁿ⁺¹ n! ζ(n + 1)`, `n ≥ 1`. -/
theorem dlmf_5_15_2 {n : ℕ} (hn : 1 ≤ n) :
    polygamma n 1 = (-1) ^ (n + 1) * (n ! : ℂ) * riemannZeta ((n : ℂ) + 1) := by
  have h1 : (1 : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by simp)
  refine (hasSum_polygamma hn h1).unique ?_
  convert (hasSum_inv_succ_pow_zeta hn).mul_left ((-1) ^ (n + 1) * (n ! : ℂ)) using 1
  funext k
  ring

/-- **DLMF 5.15.5**: `ψ⁽ⁿ⁾(z + 1) = ψ⁽ⁿ⁾(z) + (−1)ⁿ n! z^{−n−1}`, `n ≥ 1`, `z ≠ 0, −1, …`. -/
theorem dlmf_5_15_5 {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∉ gammaPoles) :
    polygamma n (z + 1) = polygamma n z + (-1) ^ n * (n ! : ℂ) * z ^ (-(n : ℤ) - 1) := by
  have hz1 : z + 1 ∉ gammaPoles := by
    rw [not_mem_gammaPoles] at hz ⊢
    intro m hm
    exact hz (m + 1) (by push_cast; linear_combination hm)
  have h := hasSum_polygamma hn hz
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [range_one, sum_singleton, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add] at h'
  have e : (fun k : ℕ => (-1) ^ (n + 1) * (n ! : ℂ) / ((k : ℂ) + 1 + z) ^ (n + 1)) =
      fun k : ℕ => (-1) ^ (n + 1) * (n ! : ℂ) / ((k : ℂ) + (z + 1)) ^ (n + 1) := by
    funext k; ring_nf
  rw [e] at h'
  rw [(hasSum_polygamma hn hz1).unique h', zpow_sub₀ (by
    intro h0; exact hz ⟨0, by simp [h0]⟩), zpow_neg, zpow_natCast, zpow_one]
  rw [pow_succ]
  field_simp
  ring

/-! ### 5.15.3 and 5.15.4 -/

/-- `∑_{k≥0} 1/(2k + 1)^{n+1} = (1 − 2^{−n−1}) ζ(n + 1)`. -/
theorem hasSum_odd_inv_pow_zeta {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℂ) + 1) ^ (n + 1))
      ((1 - ((2 : ℂ) ^ (n + 1))⁻¹) * riemannZeta ((n : ℂ) + 1)) := by
  set f : ℕ → ℂ := fun j => 1 / ((j : ℂ) + 1) ^ (n + 1)
  have hf : HasSum f (riemannZeta ((n : ℂ) + 1)) := hasSum_inv_succ_pow_zeta hn
  have h2 : ((2 : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  have ho : HasSum (fun k : ℕ => f (2 * k + 1))
      (((2 : ℂ) ^ (n + 1))⁻¹ * riemannZeta ((n : ℂ) + 1)) := by
    have e : (fun k : ℕ => f (2 * k + 1)) = fun k : ℕ => ((2 : ℂ) ^ (n + 1))⁻¹ * f k := by
      funext k
      simp only [f]
      push_cast
      rw [show (2 * (k : ℂ) + 1 + 1) = 2 * ((k : ℂ) + 1) by ring, mul_pow]
      field_simp
    rw [e]
    exact hf.mul_left _
  have he : Summable fun k : ℕ => f (2 * k) :=
    hf.summable.comp_injective (f := f) (i := fun k : ℕ => 2 * k)
      fun a b h => Nat.eq_of_mul_eq_mul_left two_pos h
  have h := HasSum.even_add_odd (f := f) he.hasSum ho
  have hval := hf.unique h
  have e2 : (fun k : ℕ => f (2 * k)) = fun k : ℕ => 1 / (2 * (k : ℂ) + 1) ^ (n + 1) := by
    funext k; simp only [f]; push_cast; ring_nf
  rw [← e2]
  convert he.hasSum using 1
  linear_combination hval

/-- **DLMF 5.15.3**: `ψ⁽ⁿ⁾(½) = (−1)ⁿ⁺¹ n! (2ⁿ⁺¹ − 1) ζ(n + 1)`, `n ≥ 1`. -/
theorem dlmf_5_15_3 {n : ℕ} (hn : 1 ≤ n) :
    polygamma n (1 / 2) =
      (-1) ^ (n + 1) * (n ! : ℂ) * (2 ^ (n + 1) - 1) * riemannZeta ((n : ℂ) + 1) := by
  have h12 : (1 / 2 : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by norm_num)
  refine (hasSum_polygamma hn h12).unique ?_
  have h2 : ((2 : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  convert (hasSum_odd_inv_pow_zeta hn).mul_left ((-1) ^ (n + 1) * (n ! : ℂ) * 2 ^ (n + 1))
    using 1
  · funext k
    rw [show (k : ℂ) + 1 / 2 = (2 * k + 1) / 2 by ring, div_pow]
    field_simp
  · field_simp

/-- **DLMF 5.15.4**: `ψ′(n − ½) = π²/2 − 4 ∑_{k=1}^{n−1} 1/(2k − 1)²`, `n ≥ 1`. -/
theorem dlmf_5_15_4 {n : ℕ} (hn : 1 ≤ n) :
    polygamma 1 ((n : ℂ) - 1 / 2) =
      (π : ℂ) ^ 2 / 2 - 4 * ∑ k ∈ Finset.Ico 1 n, 1 / (2 * (k : ℂ) - 1) ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show ((1 : ℕ) : ℂ) - 1 / 2 = 1 / 2 by push_cast; ring, dlmf_5_15_3 le_rfl,
      show ((1 : ℕ) : ℂ) + 1 = 2 by norm_num, riemannZeta_two]
    simp
    ring
  | succ n hn ih =>
    have hz : (n : ℂ) - 1 / 2 ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by
      simp; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    have hne : (n : ℂ) - 1 / 2 ≠ 0 := fun h => hz ⟨0, by
      simp only [Nat.cast_zero, neg_zero]; exact h.symm⟩
    have h2 : 2 * (n : ℂ) - 1 ≠ 0 := by
      intro h; apply hne; linear_combination h / 2
    rw [show ((n + 1 : ℕ) : ℂ) - 1 / 2 = ((n : ℂ) - 1 / 2) + 1 by push_cast; ring,
      dlmf_5_15_5 le_rfl hz, ih, Finset.sum_Ico_succ_top hn]
    rw [show -((1 : ℕ) : ℤ) - 1 = -2 by norm_num, zpow_neg, zpow_two]
    field_simp
    ring

/-! ### 5.15.6: reflection -/

theorem contDiffAt_cot_pi {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) (k : ℕ) :
    ContDiffAt ℂ k (fun w => Complex.cot (π * w)) z := by
  have hU : IsOpen {w : ℂ | Complex.sin (π * w) ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hd : DifferentiableOn ℂ (fun w => Complex.cot (π * w)) {w | Complex.sin (π * w) ≠ 0} := by
    intro w hw
    have e : (fun w => Complex.cot (π * w)) =
        fun w => Complex.cos (π * w) / Complex.sin (π * w) :=
      funext fun w => Complex.cot_eq_cos_div_sin _
    rw [e]
    exact (by fun_prop : DifferentiableAt ℂ (fun w => Complex.cos (π * w)) w).div
      (by fun_prop) (show Complex.sin (π * w) ≠ 0 from hw) |>.differentiableWithinAt
  exact ((hd.analyticOnNhd hU) z hz).contDiffAt

theorem not_mem_gammaPoles_of_not_int {z : ℂ} (hz : ∀ m : ℤ, z ≠ m) : z ∉ gammaPoles := by
  rintro ⟨m, rfl⟩; exact hz (-m) (by push_cast; ring)

/-- **DLMF 5.15.6**: `ψ⁽ⁿ⁾(1 − z) + (−1)ⁿ⁻¹ ψ⁽ⁿ⁾(z) = (−1)ⁿ π dⁿ cot(πz)/dzⁿ`, `n ≥ 1`,
`z ∉ ℤ`. -/
theorem dlmf_5_15_6 {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : ∀ m : ℤ, z ≠ m) :
    polygamma n (1 - z) + (-1) ^ (n - 1) * polygamma n z =
      (-1) ^ n * π * iteratedDeriv n (fun w => Complex.cot (π * w)) z := by
  set U : Set ℂ := {w | Complex.sin (π * w) ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun (by fun_prop) continuous_const
  have hzU : z ∈ U := fun h => by
    obtain ⟨m, hm⟩ := (sin_pi_eq_zero_iff z).mp h; exact hz m hm
  have heq : EqOn (fun w => digamma (1 - w)) (digamma + fun w => π * Complex.cot (π * w)) U :=
    fun w hw => by
      have hw' : ∀ m : ℤ, w ≠ m := fun m hm => hw ((sin_pi_eq_zero_iff w).mpr ⟨m, hm⟩)
      simp only [Pi.add_apply]
      exact digamma_one_sub hw'
  have h := heq.iteratedDeriv_of_isOpen hU n hzU
  have hL : iteratedDeriv n (fun w => digamma (1 - w)) z = (-1) ^ n * polygamma n (1 - z) := by
    simp only [iteratedDeriv_comp_const_sub, smul_eq_mul]; rfl
  have hpz : z ∉ gammaPoles := not_mem_gammaPoles_of_not_int hz
  have hR : iteratedDeriv n (digamma + fun w => π * Complex.cot (π * w)) z =
      polygamma n z + π * iteratedDeriv n (fun w => Complex.cot (π * w)) z := by
    rw [iteratedDeriv_add (dlmf_5_2_2_analytic z hpz).contDiffAt
      ((contDiffAt_cot_pi hzU n).const_smul (π : ℂ) |>.congr_of_eventuallyEq
        (Eventually.of_forall fun w => by simp [smul_eq_mul])),
      iteratedDeriv_const_mul _ (contDiffAt_cot_pi hzU n)]
    rfl
  rw [hL, hR] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  rw [pow_succ] at h ⊢
  have hsq : ((-1 : ℂ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-((-1 : ℂ) ^ m)) * h - polygamma (m + 1) (1 - z) * hsq

/-! ### 5.15.7: multiplication -/

theorem AnalyticOnNhd.iteratedDeriv' {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) :
    ∀ n, AnalyticOnNhd ℂ (iteratedDeriv n f) U
  | 0 => by simpa using hf
  | n + 1 => by rw [iteratedDeriv_succ]; exact (AnalyticOnNhd.iteratedDeriv' hf n).deriv

/-- `dⁿ f(cx)/dxⁿ = cⁿ f⁽ⁿ⁾(cx)` for `f` analytic on an open set. -/
theorem iteratedDeriv_comp_mul_eqOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (c : ℂ) :
    ∀ n, EqOn (iteratedDeriv n fun x => f (c * x)) (fun x => c ^ n * iteratedDeriv n f (c * x))
      {x | c * x ∈ U}
  | 0 => fun x _ => by simp
  | n + 1 => fun x hx => by
    have hV : IsOpen {x : ℂ | c * x ∈ U} := hU.preimage (continuous_const.mul continuous_id)
    have hev : (iteratedDeriv n fun x => f (c * x)) =ᶠ[𝓝 x]
        fun x => c ^ n * iteratedDeriv n f (c * x) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact iteratedDeriv_comp_mul_eqOn hU hf c n hy
    have hd : HasDerivAt (fun x => iteratedDeriv n f (c * x))
        (deriv (iteratedDeriv n f) (c * x) * c) x := by
      have h1 := ((AnalyticOnNhd.iteratedDeriv' hf n) (c * x) hx).differentiableAt.hasDerivAt
      exact (h1.comp x ((hasDerivAt_id x).const_mul c)).congr_deriv (by simp)
    simp only [iteratedDeriv_succ]
    rw [hev.deriv_eq, (hd.const_mul (c ^ n)).deriv]
    ring

theorem iteratedDeriv_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℂ → ℂ} {x : ℂ} (n : ℕ)
    (hg : ∀ i ∈ s, ContDiffAt ℂ n (g i) x) :
    iteratedDeriv n (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, iteratedDeriv n (g i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 := hg a (Finset.mem_insert_self a s)
    have h2 : ContDiffAt ℂ n (fun y => ∑ i ∈ s, g i y) x :=
      ContDiffAt.sum fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [← ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]
    exact iteratedDeriv_add h1 h2

/-- **DLMF 5.15.7**: `ψ⁽ⁿ⁾(mz) = m^{−n−1} ∑_{k=0}^{m−1} ψ⁽ⁿ⁾(z + k/m)`, `n, m ≥ 1`,
`mz ≠ 0, −1, …`. -/
theorem dlmf_5_15_7 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {z : ℂ} (hz : (m : ℂ) * z ∉ gammaPoles) :
    polygamma n (m * z) = 1 / (m : ℂ) ^ (n + 1) * ∑ k ∈ range m, polygamma n (z + k / m) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  set V : Set ℂ := {x | (m : ℂ) * x ∈ gammaPolesᶜ}
  have hV : IsOpen V := isOpen_compl_gammaPoles.preimage (continuous_const.mul continuous_id)
  have hshift : ∀ x ∈ V, ∀ k : ℕ, x + k / m ∉ gammaPoles := by
    intro x hx k hk
    obtain ⟨j, hj⟩ := hk
    apply hx
    refine ⟨m * j + k, ?_⟩
    push_cast
    field_simp at hj ⊢
    linear_combination hj
  have heq : EqOn (fun x => digamma ((m : ℂ) * x))
      (fun x => (Real.log m : ℂ) + 1 / m * ∑ k ∈ range m, digamma (x + k / m)) V :=
    fun x hx => by simp only; rw [dlmf_5_5_9 hm hx, add_comm]
  have h := heq.iteratedDeriv_of_isOpen hV n hz
  rw [iteratedDeriv_comp_mul_eqOn isOpen_compl_gammaPoles dlmf_5_2_2_analytic _ n hz,
    iteratedDeriv_const_add (by omega)] at h
  have hc : ∀ k ∈ range m, ContDiffAt ℂ n (fun x => digamma (x + k / m)) z := fun k _ =>
    ((dlmf_5_2_2_analytic _ (hshift z hz k)).comp_of_eq
      (analyticAt_id.add analyticAt_const) rfl).contDiffAt
  rw [iteratedDeriv_const_mul _ (ContDiffAt.sum hc), iteratedDeriv_finsetSum _ n hc] at h
  simp only [iteratedDeriv_comp_add_const] at h
  have hpow : (m : ℂ) ^ n ≠ 0 := pow_ne_zero _ hm0
  have h' : (m : ℂ) ^ n * polygamma n (m * z) =
      1 / m * ∑ k ∈ range m, polygamma n (z + k / m) := h
  calc polygamma n (m * z) = ((m : ℂ) ^ n)⁻¹ * ((m : ℂ) ^ n * polygamma n (m * z)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpow, one_mul]
    _ = ((m : ℂ) ^ n)⁻¹ * (1 / m * ∑ k ∈ range m, polygamma n (z + k / m)) := by rw [h']
    _ = _ := by rw [pow_succ]; ring

end Azurite.DLMF
