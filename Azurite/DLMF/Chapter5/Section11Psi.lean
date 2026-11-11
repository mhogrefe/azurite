/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Stirling

/-!
# DLMF §5.11(i): the expansion of `ψ` (5.11.2)

Formalization of <https://dlmf.nist.gov/5.11>, equation 5.11.2,
`ψ(z) ∼ ln z − 1/(2z) − ∑_{k≥1} B_{2k}/(2k z^{2k})` as `z → ∞` in `|ph z| ≤ π − δ`
(`dlmf_5_11_2`, stated for `ψ(z) − ln z` with the coefficients `psiCoeff`).

`ψ = Γ′/Γ` is the derivative of the exponent of `Gamma_eq_exp_stirlingJ`:
`ψ(z) = ln z − 1/(2z) + J′(z)` on the slit plane (`digamma_eq_log_sub_add_deriv`), and the closed
form
`J = ∑_{j≤m} B_{j+2}/((j + 2)(j + 1) z^{j+1}) − K_{m+2}/(m + 2)` differentiates term by term, the
remainder `−K′_{m+2}/(m + 2) = ∫₀^∞ B̃_{m+2}(t)/(z + t)^{m+3} dt = O(z^{−m−2})`
(`hasDerivAt_integral_div_add_pow`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- `ψ(z) = ln z − 1/(2z) + J′(z)` on the slit plane. -/
theorem digamma_eq_log_sub_add_deriv {z : ℂ} (hz : z ∈ slitPlane) :
    digamma z = Complex.log z - 1 / (2 * z) + deriv stirlingJ z := by
  have hz0 := slitPlane_ne_zero hz
  have hJ := hasDerivAt_stirlingJ hz
  set E : ℂ → ℂ := fun w => (w - 1 / 2) * Complex.log w - w + 1 / 2 * Complex.log (2 * π) +
    stirlingJ w with hE
  have hD : HasDerivAt E (Complex.log z + (z - 1 / 2) / z - 1 + deriv stirlingJ z) z := by
    have hl := hasDerivAt_log hz
    have h1 : HasDerivAt (fun w => (w - 1 / 2) * Complex.log w) (1 * Complex.log z +
        (z - 1 / 2) * z⁻¹) z := ((hasDerivAt_id' z).sub_const _).mul hl
    have := ((h1.sub (hasDerivAt_id' z)).add_const (1 / 2 * Complex.log (2 * π))).add
      hJ.differentiableAt.hasDerivAt
    refine HasDerivAt.congr_deriv (f := E) this ?_
    field_simp
  have key := digamma_add_eq_deriv (a := 0) isOpen_slitPlane hz hD.differentiableAt
    (fun w hw => by rw [add_zero]; exact Gamma_eq_exp_stirlingJ hw)
  rw [add_zero] at key
  rw [key, hD.deriv]
  field_simp
  ring

/-- The remainder `Lₘ(z) = ∫₀^∞ B̃_{m+2}(t)/(z + t)^{m+3} dt` of the derivative. -/
noncomputable def stirlingL (m : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (periodicBernoulli (m + 2) t : ℂ) / (z + t) ^ (m + 3)

theorem hasDerivAt_stirlingK {m : ℕ} (hm : 2 ≤ m) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (stirlingK m) (-(m : ℂ) * ∫ t in Ioi (0 : ℝ),
      (periodicBernoulli m t : ℂ) / (z + t) ^ (m + 1)) z := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound m
  have h := hasDerivAt_integral_div_add_pow (measurable_periodicBernoulli m) (C := C) hC hm hz
  refine h.congr_deriv ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ring

/-- `J′(z) = −∑_{j≤m} B_{j+2}/((j + 2) z^{j+2}) + Lₘ(z)` on the slit plane. -/
theorem deriv_stirlingJ_eq {z : ℂ} (hz : z ∈ slitPlane) (m : ℕ) :
    deriv stirlingJ z = -∑ j ∈ Finset.range (m + 1),
      (bernoulli (j + 2) : ℂ) / ((j + 2) * z ^ (j + 2)) + stirlingL m z := by
  have hz0 := slitPlane_ne_zero hz
  have hev : stirlingJ =ᶠ[𝓝 z] fun w => ∑ j ∈ Finset.range (m + 1),
      (bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1) * w ^ (j + 1)) -
        stirlingK (m + 2) w / (m + 2) :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => stirlingJ_eq_sum hw m
  have hterm : ∀ j ∈ Finset.range (m + 1), HasDerivAt
      (fun w : ℂ => (bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1) * w ^ (j + 1)))
      (-((bernoulli (j + 2) : ℂ) / ((j + 2) * z ^ (j + 2)))) z := fun j _ => by
    have h0 := (hasDerivAt_pow (j + 1) z).inv (pow_ne_zero _ hz0)
    have h1 := h0.const_mul ((bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1)))
    refine (h1.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    · have hj1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
      have hj2 : ((j : ℂ) + 2) ≠ 0 := by exact_mod_cast (show j + 2 ≠ 0 by omega)
      push_cast
      field_simp
      ring
    · simp [div_eq_mul_inv]
      ring
  have hsum := HasDerivAt.fun_sum hterm
  have hK := (hasDerivAt_stirlingK (m := m + 2) (by omega) hz).div_const ((m : ℂ) + 2)
  have hall : HasDerivAt (fun w => ∑ j ∈ Finset.range (m + 1),
      (bernoulli (j + 2) : ℂ) / ((j + 2) * (j + 1) * w ^ (j + 1)) -
        stirlingK (m + 2) w / (m + 2)) _ z := hsum.sub (by push_cast at hK; exact hK)
  rw [hev.deriv_eq, hall.deriv, Finset.sum_neg_distrib, stirlingL]
  have hm2 : ((m : ℂ) + 2) ≠ 0 := by exact_mod_cast (show m + 2 ≠ 0 by omega)
  rw [show m + 2 + 1 = m + 3 by ring]
  field_simp
  ring

theorem norm_stirlingL_le (m : ℕ) : ∃ C, 0 ≤ C ∧ ∀ {z : ℂ} {δ : ℝ}, z ≠ 0 → 0 < δ → δ ≤ π →
    |arg z| ≤ π - δ →
      ‖stirlingL m z‖ ≤ C / (Real.sin (δ / 2) ^ (m + 3) * ((m + 2) * ‖z‖ ^ (m + 2))) := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound (m + 2)
  refine ⟨C, (abs_nonneg _).trans (hC 0), fun hz hδ hδπ harg => ?_⟩
  have h := (integrableOn_div_add_pow (measurable_periodicBernoulli (m + 2)) (C := C) hC hz hδ
    hδπ harg (m := m + 3) (by omega)).2
  push_cast at h
  rw [show (m : ℝ) + 3 - 1 = m + 2 by ring] at h
  exact h

/-- The coefficients of 5.11.2 in powers of `1/z`: `d₀ = 0`, `d₁ = −½`, `dₛ = −Bₛ/s` (`s ≥ 2`). -/
noncomputable def psiCoeff (s : ℕ) : ℂ :=
  if s = 0 then 0 else if s = 1 then -1 / 2 else -(bernoulli s : ℂ) / s

theorem psiCoeff_even {k : ℕ} (hk : 1 ≤ k) :
    psiCoeff (2 * k) = -(bernoulli (2 * k) : ℂ) / (2 * k) := by
  rw [psiCoeff, ite_eq_right (by omega), ite_eq_right (by omega)]
  push_cast; ring

theorem psiCoeff_odd {k : ℕ} (hk : 1 ≤ k) : psiCoeff (2 * k + 1) = 0 := by
  rw [psiCoeff, ite_eq_right (by omega), ite_eq_right (by omega),
    bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]
  simp

theorem sum_psiCoeff (z : ℂ) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 3), psiCoeff s * z ^ (-(s : ℤ)) =
      -1 / (2 * z) - ∑ j ∈ Finset.range (m + 1),
        (bernoulli (j + 2) : ℂ) / ((j + 2) * z ^ (j + 2)) := by
  have e : ∀ j ∈ Finset.range (m + 1), psiCoeff (j + 1 + 1) * z ^ (-((j + 1 + 1 : ℕ) : ℤ)) =
      -((bernoulli (j + 2) : ℂ) / ((j + 2) * z ^ (j + 2))) := fun j _ => by
    rw [psiCoeff, ite_eq_right (by omega), ite_eq_right (by omega), zpow_neg, zpow_natCast,
      show j + 1 + 1 = j + 2 by ring]
    push_cast
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [show m + 3 = (m + 1) + 1 + 1 by ring, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_congr rfl e, Finset.sum_neg_distrib]
  simp [psiCoeff]
  ring

/-- **DLMF 5.11.2**: `ψ(z) − ln z ∼ −1/(2z) − ∑_{k≥1} B_{2k}/(2k z^{2k})` as `z → ∞` in
`|ph z| ≤ π − δ` (coefficients `psiCoeff`, see `psiCoeff_even`, `psiCoeff_odd`). -/
theorem dlmf_5_11_2 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) (fun z => digamma z - Complex.log z)
      psiCoeff := by
  intro n hn
  obtain ⟨C, hC0, hC⟩ := norm_stirlingL_le (n - 1)
  set s := Real.sin (δ / 2) with hs
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  refine isBoundedUnder_of_eventually_le (a := ‖psiCoeff n‖ + ‖psiCoeff (n + 1)‖ +
    C / (s ^ (n - 1 + 3) * ((n - 1 : ℕ) + 2))) ?_
  have hA : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)), 1 ≤ ‖z‖ :=
    (tendsto_norm_cobounded_atTop.eventually_ge_atTop 1).filter_mono inf_le_left
  have hB : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)),
      z ∈ closedSectorDLMF 0 (π - δ) := mem_inf_of_right (mem_principal_self _)
  filter_upwards [hA, hB] with z h1 hz
  obtain ⟨hz0, harg⟩ := hz
  simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at harg
  have hslit : z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hz0⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hC ⊢
  have hL := hC hz0 hδ hδπ harg
  -- `ψ − ln z − ∑_{s<m+1} dₛ z^{−s} = d_{m+1} z^{−(m+1)} + d_{m+2} z^{−(m+2)} + Lₘ`
  have hrep : digamma z - Complex.log z - ∑ s ∈ Finset.range (m + 1), psiCoeff s * z ^ (-(s : ℤ)) =
      psiCoeff (m + 1) * z ^ (-((m + 1 : ℕ) : ℤ)) + psiCoeff (m + 2) * z ^ (-((m + 2 : ℕ) : ℤ)) +
        stirlingL m z := by
    have h := sum_psiCoeff z m
    rw [show m + 3 = m + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ] at h
    rw [digamma_eq_log_sub_add_deriv hslit, deriv_stirlingJ_eq hslit m]
    linear_combination -h
  have hzn : ‖z‖ ^ (m + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)
  have hz1 : 0 < ‖z‖ := by linarith
  rw [hrep, add_div, add_div, mul_div_assoc, div_self (zpow_ne_zero _ hz0), mul_one]
  have e1 : ‖psiCoeff (m + 2) * z ^ (-((m + 2 : ℕ) : ℤ)) / z ^ (-((m + 1 : ℕ) : ℤ))‖ =
      ‖psiCoeff (m + 2)‖ / ‖z‖ := by
    rw [norm_div, norm_mul, norm_zpow, norm_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    rw [pow_succ]
    field_simp
  have e2 : ‖stirlingL m z / z ^ (-((m + 1 : ℕ) : ℤ))‖ = ‖stirlingL m z‖ * ‖z‖ ^ (m + 1) := by
    rw [norm_div, norm_zpow, zpow_neg, zpow_natCast]
    field_simp
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_
  · rw [e1]
    exact div_le_self (norm_nonneg _) h1
  · rw [e2]
    calc ‖stirlingL m z‖ * ‖z‖ ^ (m + 1)
        ≤ C / (s ^ (m + 3) * ((m + 2) * ‖z‖ ^ (m + 2))) * ‖z‖ ^ (m + 1) := by gcongr
      _ = C / (s ^ (m + 3) * (m + 2)) / ‖z‖ := by field_simp; ring
      _ ≤ C / (s ^ (m + 3) * (m + 2)) := div_le_self (by positivity) h1
      _ = _ := by ring

end Azurite.DLMF
