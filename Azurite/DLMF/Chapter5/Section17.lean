/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section8
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# DLMF §5.17: Barnes' `G`-function, 5.17.1–5.17.3

Formalization of <https://dlmf.nist.gov/5.17> (part 1). Barnes' `G` is defined by DLMF's
infinite product 5.17.3,

`G(z + 1) = (2π)^{z/2} exp(−½z(z + 1) − ½γz²) ∏_{k≥1} (1 + z/k)^k exp(−z + z²/(2k))`

(`barnesG`, with the factors `barnesFactor`, index shifted to start at `0`). The product converges
unconditionally for every `z` (`multipliable_barnesFactor`: the factor is `exp(u)` with
`|u| ≤ ⅔|z|³/k²` for large `k`).

* 5.17.1: the partial products satisfy
  `Pₙ(z) ∏_{j<n} (z + j) = Pₙ(z − 1)(z + n)ⁿ exp((z − ½)Hₙ − n)` (`barnes_partial_rec`); with
  Euler's limit for `Γ`, `Hₙ − ln n → γ` and Stirling's formula this gives `G(z + 1) = Γ(z)G(z)`
  for `z ≠ 0, −1, −2, …` (`dlmf_5_17_1`; at those points Mathlib's `Γ` takes the junk value `0`),
  and `G(1) = 1`.
* 5.17.2: `G(n) = (n − 2)! ⋯ 1!` (`dlmf_5_17_2`).
-/

open Complex Filter Topology Finset
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- The factor `(1 + z/k)^k exp(−z + z²/(2k))` of 5.17.3 (index shifted: `k ↦ k + 1`). -/
noncomputable def barnesFactor (z : ℂ) (k : ℕ) : ℂ :=
  (1 + z / ((k : ℂ) + 1)) ^ (k + 1) * cexp (-z + z ^ 2 / (2 * ((k : ℂ) + 1)))

/-- The prefactor `(2π)^{z/2} exp(−½z(z + 1) − ½γz²)` of 5.17.3. -/
noncomputable def barnesPre (z : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (z / 2) * cexp (-(z * (z + 1)) / 2 - γ * z ^ 2 / 2)

/-- **Barnes' `G`-function** (double gamma function), defined by DLMF's product 5.17.3:
`G(z + 1) = (2π)^{z/2} exp(−½z(z + 1) − ½γz²) ∏_{k≥1} (1 + z/k)^k exp(−z + z²/(2k))`. -/
noncomputable def barnesG (z : ℂ) : ℂ := barnesPre (z - 1) * ∏' k, barnesFactor (z - 1) k

theorem barnesG_add_one (z : ℂ) : barnesG (z + 1) = barnesPre z * ∏' k, barnesFactor z k := by
  simp [barnesG]

/-! ### Convergence of the product -/

/-- `ℓₖ(z) = k ln(1 + z/k) − z + z²/(2k)` (index shifted), the logarithm of the factor of 5.17.3
for `1 + z/k ≠ 0`. -/
noncomputable def barnesLogTerm (z : ℂ) (k : ℕ) : ℂ :=
  ((k : ℂ) + 1) * Complex.log (1 + z / ((k : ℂ) + 1)) - z + z ^ 2 / (2 * ((k : ℂ) + 1))

theorem barnesFactor_eq_exp {z : ℂ} {k : ℕ} (h : 1 + z / ((k : ℂ) + 1) ≠ 0) :
    barnesFactor z k = cexp (barnesLogTerm z k) := by
  have he : cexp (((k + 1 : ℕ) : ℂ) * Complex.log (1 + z / ((k : ℂ) + 1))) =
      (1 + z / ((k : ℂ) + 1)) ^ (k + 1) := by
    rw [Complex.exp_nat_mul, exp_log h]
  push_cast at he
  rw [barnesFactor, barnesLogTerm, ← he, ← exp_add]
  congr 1
  ring

/-- `|ℓₖ(z)| ≤ ⅔|z|³/k²` for `k ≥ 2|z|`. -/
theorem norm_barnesLogTerm_le {z : ℂ} {k : ℕ} (hk1 : 2 * ‖z‖ ≤ (k : ℝ) + 1) :
    ‖barnesLogTerm z k‖ ≤ 2 / 3 * ‖z‖ ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
  set w := z / ((k : ℂ) + 1) with hw
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk0' : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hnk : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  have hnw : ‖w‖ = ‖z‖ / ((k : ℝ) + 1) := by rw [hw, norm_div, hnk]
  have hw2 : ‖w‖ ≤ 1 / 2 := by rw [hnw, div_le_iff₀ hk0]; linarith
  have hw1 : ‖w‖ < 1 := by linarith
  have heq : barnesLogTerm z k = ((k : ℂ) + 1) * (Complex.log (1 + w) - logTaylor 3 w) := by
    have hT : logTaylor 3 w = w - w ^ 2 / 2 := by
      simp [logTaylor, Finset.sum_range_succ]; ring
    rw [barnesLogTerm, hT, hw]
    field_simp
    ring
  have hl := norm_log_sub_logTaylor_le 2 hw1
  norm_num at hl
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]; linarith
  rw [heq, norm_mul, hnk]
  have hw0 := norm_nonneg w
  calc ((k : ℝ) + 1) * ‖Complex.log (1 + w) - logTaylor 3 w‖
      ≤ ((k : ℝ) + 1) * (‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3) := by gcongr
    _ ≤ ((k : ℝ) + 1) * (‖w‖ ^ 3 * 2 / 3) := by gcongr
    _ = 2 / 3 * ‖z‖ ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by rw [hnw]; field_simp

theorem one_add_div_ne_zero_of_le {z : ℂ} {k : ℕ} (hk1 : 2 * ‖z‖ ≤ (k : ℝ) + 1) :
    1 + z / ((k : ℂ) + 1) ≠ 0 := fun h => by
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnk : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by exact_mod_cast Complex.norm_natCast (k + 1)
  have : z / ((k : ℂ) + 1) = -1 := by linear_combination h
  have h2 := congrArg norm this
  rw [norm_div, hnk, norm_neg, norm_one, div_eq_one_iff_eq hk0.ne'] at h2
  linarith [norm_nonneg z]

theorem norm_barnesFactor_sub_one_le {z : ℂ} {k : ℕ} (hk1 : 2 * ‖z‖ ≤ (k : ℝ) + 1)
    (hk2 : ‖z‖ ^ 3 ≤ (k : ℝ) + 1) :
    ‖barnesFactor z k - 1‖ ≤ 2 * ‖z‖ ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hu_le := norm_barnesLogTerm_le hk1
  set u := barnesLogTerm z k
  have hu1 : ‖u‖ ≤ 1 := by
    refine hu_le.trans ?_
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [mul_one_div, div_le_one (by positivity)]
    nlinarith
  rw [barnesFactor_eq_exp (one_add_div_ne_zero_of_le hk1)]
  calc ‖cexp u - 1‖ ≤ 2 * ‖u‖ := norm_exp_sub_one_le hu1
    _ ≤ 2 * (2 / 3 * ‖z‖ ^ 3 * (1 / ((k : ℝ) + 1) ^ 2)) := by gcongr
    _ ≤ 2 * ‖z‖ ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by
        have : 0 ≤ ‖z‖ ^ 3 * (1 / ((k : ℝ) + 1) ^ 2) := by positivity
        nlinarith

theorem multipliable_barnesFactor (z : ℂ) : Multipliable (barnesFactor z) := by
  have hs : Summable (fun k => barnesFactor z k - 1) := by
    refine Summable.of_norm_bounded_eventually_nat
      (summable_one_div_natCast_add_one_sq.mul_left (2 * ‖z‖ ^ 3)) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (2 * ‖z‖ + ‖z‖ ^ 3)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : 0 ≤ ‖z‖ ^ 3 := by positivity
    have h1 : 0 ≤ ‖z‖ := norm_nonneg z
    exact norm_barnesFactor_sub_one_le (by linarith) (by linarith)
  simpa using Complex.multipliable_one_add_of_summable hs

/-- **DLMF 5.17.3**: the product converges (unconditionally) and is Barnes' `G(z + 1)`. -/
theorem dlmf_5_17_3 (z : ℂ) :
    Multipliable (fun k : ℕ =>
        (1 + z / ((k : ℂ) + 1)) ^ (k + 1) * cexp (-z + z ^ 2 / (2 * ((k : ℂ) + 1)))) ∧
      barnesG (z + 1) = (2 * π : ℂ) ^ (z / 2) * cexp (-(z * (z + 1)) / 2 - γ * z ^ 2 / 2) *
        ∏' k : ℕ, (1 + z / ((k : ℂ) + 1)) ^ (k + 1) *
          cexp (-z + z ^ 2 / (2 * ((k : ℂ) + 1))) :=
  ⟨multipliable_barnesFactor z, barnesG_add_one z⟩

/-! ### The recurrence 5.17.1 -/

/-- The harmonic numbers `Hₙ = ∑_{k<n} 1/(k + 1)` in `ℂ`. -/
noncomputable def harmonicC (n : ℕ) : ℂ := ∑ k ∈ range n, 1 / ((k : ℂ) + 1)

/-- `Pₙ(z) ∏_{j<n} (z + j) = Pₙ(z − 1) (z + n)ⁿ exp((z − ½)Hₙ − n)`. -/
theorem barnes_partial_rec (z : ℂ) (n : ℕ) :
    (∏ k ∈ range n, barnesFactor z k) * ∏ j ∈ range n, (z + j) =
      (∏ k ∈ range n, barnesFactor (z - 1) k) * (z + n) ^ n *
        cexp ((z - 1 / 2) * harmonicC n - n) := by
  induction n with
  | zero => simp [harmonicC]
  | succ n ih =>
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h1 : 1 + z / ((n : ℂ) + 1) = (z + n + 1) / ((n : ℂ) + 1) := by field_simp; ring
    have h2 : 1 + (z - 1) / ((n : ℂ) + 1) = (z + n) / ((n : ℂ) + 1) := by field_simp; ring
    have hE : cexp (-z + z ^ 2 / (2 * ((n : ℂ) + 1))) * cexp ((z - 1 / 2) * harmonicC n - n) =
        cexp (-(z - 1) + (z - 1) ^ 2 / (2 * ((n : ℂ) + 1))) *
          cexp ((z - 1 / 2) * harmonicC (n + 1) - ((n + 1 : ℕ) : ℂ)) := by
      rw [← exp_add, ← exp_add]
      congr 1
      simp only [harmonicC, sum_range_succ]
      push_cast
      field_simp
      ring
    have key : barnesFactor z n * (z + n) * ((z + n) ^ n * cexp ((z - 1 / 2) * harmonicC n - n)) =
        barnesFactor (z - 1) n * ((z + ((n + 1 : ℕ) : ℂ)) ^ (n + 1) *
          cexp ((z - 1 / 2) * harmonicC (n + 1) - ((n + 1 : ℕ) : ℂ))) := by
      simp only [barnesFactor]
      rw [h1, h2, div_pow, div_pow]
      push_cast at hE ⊢
      rw [show z + ((n : ℂ) + 1) = z + n + 1 by ring]
      linear_combination ((z + n + 1) ^ (n + 1) * (z + n) ^ (n + 1) / ((n : ℂ) + 1) ^ (n + 1)) * hE
    rw [prod_range_succ, prod_range_succ, prod_range_succ]
    calc (∏ k ∈ range n, barnesFactor z k) * barnesFactor z n *
          ((∏ j ∈ range n, (z + j)) * (z + n))
        = barnesFactor z n * (z + n) *
            ((∏ k ∈ range n, barnesFactor z k) * ∏ j ∈ range n, (z + j)) := by ring
      _ = barnesFactor z n * (z + n) * ((∏ k ∈ range n, barnesFactor (z - 1) k) *
            ((z + n) ^ n * cexp ((z - 1 / 2) * harmonicC n - n))) := by rw [ih]; ring
      _ = (∏ k ∈ range n, barnesFactor (z - 1) k) * (barnesFactor z n * (z + n) *
            ((z + n) ^ n * cexp ((z - 1 / 2) * harmonicC n - n))) := by ring
      _ = _ := by rw [key]; ring

theorem tendsto_harmonicC_sub_log :
    Tendsto (fun n : ℕ => harmonicC n - Complex.log n) atTop (𝓝 (γ : ℂ)) := by
  have h := (continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, harmonicC, harmonic]
  rw [ofReal_sub, Complex.ofReal_log (Nat.cast_nonneg _), ofReal_natCast]
  push_cast
  simp [one_div]

/-- `√n nⁿ e^{−n}/n!`, which tends to `1/√(2π)` by Stirling's formula. -/
noncomputable def stirlingRecip (n : ℕ) : ℝ := √n * (n : ℝ) ^ n * Real.exp (-n) / n !

theorem tendsto_stirlingRecip : Tendsto stirlingRecip atTop (𝓝 (1 / √(2 * π))) := by
  have h := (tendsto_const_nhds (x := 1 / √2)).div Stirling.tendsto_stirlingSeq_sqrt_pi
    (by positivity)
  rw [show 1 / √2 / √π = 1 / √(2 * π) by
    rw [Real.sqrt_mul (by norm_num)]; field_simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : √(2 * (n : ℝ)) = √2 * √n := Real.sqrt_mul (by norm_num) _
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have he : (n / Real.exp 1 : ℝ) ^ n = (n : ℝ) ^ n * Real.exp (-n) := by
    rw [div_pow, Real.exp_one_pow, Real.exp_neg]; ring
  simp only [Pi.div_apply, stirlingRecip, Stirling.stirlingSeq]
  rw [hs, he]
  have : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have : (0 : ℝ) < (n : ℝ) ^ n := by positivity
  field_simp

/-- `(z + n)^{n+1} exp((z − ½)Hₙ − n)/(n^z n!) =
(1 + z/n)^{n+1} exp((z − ½)(Hₙ − ln n)) · √n nⁿ e^{−n}/n!`. -/
theorem barnes_ratio_eq (z : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (z + n) ^ (n + 1) * cexp ((z - 1 / 2) * harmonicC n - n) / ((n : ℂ) ^ z * n !) =
      (1 + z / n) ^ (n + 1) * cexp ((z - 1 / 2) * (harmonicC n - Complex.log n)) *
        (stirlingRecip n : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  set L := Complex.log n with hL
  have hsqrt : ((√(n : ℝ) : ℝ) : ℂ) = cexp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnr, ofReal_exp]
    congr 1
    push_cast
    rw [hL]
    ring
  have hsq : cexp (L / 2) * cexp (L / 2) = n := by
    rw [← exp_add, show L / 2 + L / 2 = L by ring, hL, exp_log hn0]
  have hcpow : (n : ℂ) ^ z = cexp (L * z) := by rw [cpow_def_of_ne_zero hn0]
  have hE : cexp ((z - 1 / 2) * harmonicC n - n) =
      cexp ((z - 1 / 2) * (harmonicC n - L)) * cexp (L * z) * cexp (-n) /
        cexp (L / 2) := by
    rw [eq_div_iff (exp_ne_zero _), ← exp_add, ← exp_add, ← exp_add]
    congr 1; ring
  rw [stirlingRecip]
  push_cast
  rw [hsqrt, hcpow, hE]
  have h1 : (z + n) = n * (1 + z / n) := by field_simp; ring
  rw [h1, mul_pow]
  have hL2 := exp_ne_zero (L / 2)
  have hLz := exp_ne_zero (L * z)
  set X := (1 + z / n) ^ (n + 1)
  set A := cexp ((z - 1 / 2) * (harmonicC n - L))
  set D := cexp (L / 2)
  rw [pow_succ, ← hsq]
  field_simp

theorem tendsto_barnes_ratio (z : ℂ) :
    Tendsto (fun n : ℕ => (1 + z / n) ^ (n + 1) * cexp ((z - 1 / 2) *
        (harmonicC n - Complex.log n)) * (stirlingRecip n : ℂ)) atTop
      (𝓝 (cexp z * cexp ((z - 1 / 2) * γ) * ((1 / √(2 * π) : ℝ) : ℂ))) := by
  have h1 : Tendsto (fun n : ℕ => (1 + z / n) ^ (n + 1)) atTop (𝓝 (cexp z)) := by
    have hd : Tendsto (fun n : ℕ => 1 + z / n) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => z / (n : ℂ)) atTop (𝓝 0) := by
        have := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa [div_eq_mul_inv] using this.const_mul z
      simpa using h0.const_add 1
    have := (tendsto_one_add_div_pow_exp z).mul hd
    rw [mul_one] at this
    exact this.congr fun n => by rw [pow_succ]
  have h2 : Tendsto (fun n : ℕ => cexp ((z - 1 / 2) * (harmonicC n - Complex.log n))) atTop
      (𝓝 (cexp ((z - 1 / 2) * γ))) :=
    (continuous_exp.tendsto _).comp (tendsto_harmonicC_sub_log.const_mul (z - 1 / 2))
  have h3 := (continuous_ofReal.tendsto _).comp tendsto_stirlingRecip
  exact (h1.mul h2).mul h3

theorem barnesPre_ratio (z : ℂ) :
    barnesPre z * (cexp z * cexp ((z - 1 / 2) * γ) * ((1 / √(2 * π) : ℝ) : ℂ)) =
      barnesPre (z - 1) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hc : ((1 / √(2 * π) : ℝ) : ℂ) = 1 / (2 * π : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_div, ofReal_one, Complex.ofReal_cpow h2π]
    push_cast; ring_nf
  have hne : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  rw [hc, barnesPre, barnesPre, show (z - 1) / 2 = z / 2 - 1 / 2 by ring, cpow_sub _ _ hne]
  have hp : (2 * π : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; tauto
  have hexp : cexp (-(z * (z + 1)) / 2 - γ * z ^ 2 / 2) * (cexp z * cexp ((z - 1 / 2) * γ)) =
      cexp (-((z - 1) * (z - 1 + 1)) / 2 - γ * (z - 1) ^ 2 / 2) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  rw [← hexp]
  field_simp

/-- **DLMF 5.17.1**: `G(z + 1) = Γ(z) G(z)` (`z ≠ 0, −1, −2, …`) and `G(1) = 1`. -/
theorem dlmf_5_17_1 :
    (∀ z ∉ gammaPoles, barnesG (z + 1) = Gamma z * barnesG z) ∧ barnesG 1 = 1 := by
  refine ⟨fun z hz => ?_, ?_⟩
  · have hzj : ∀ j : ℕ, z + j ≠ 0 := fun j h => hz ⟨j, by linear_combination -h⟩
    have hT := (multipliable_barnesFactor z).hasProd.tendsto_prod_nat
    have hT' := (multipliable_barnesFactor (z - 1)).hasProd.tendsto_prod_nat
    have hlim := (hT'.mul (GammaSeq_tendsto_Gamma z)).mul (tendsto_barnes_ratio z)
    have heq : ∀ᶠ n : ℕ in atTop, (∏ k ∈ range n, barnesFactor (z - 1) k) * GammaSeq z n *
        ((1 + z / n) ^ (n + 1) * cexp ((z - 1 / 2) * (harmonicC n - Complex.log n)) *
          (stirlingRecip n : ℂ)) = ∏ k ∈ range n, barnesFactor z k := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hp : ∏ j ∈ range n, (z + j) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => hzj j
      have hcp : (n : ℂ) ^ z ≠ 0 := (cpow_ne_zero_iff.mpr (Or.inl hn0))
      have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      rw [← barnes_ratio_eq z hn, GammaSeq, prod_range_succ]
      have hzn := hzj n
      have hr : ∏ k ∈ range n, barnesFactor z k = (∏ k ∈ range n, barnesFactor (z - 1) k) *
          (z + n) ^ n * cexp ((z - 1 / 2) * harmonicC n - n) / ∏ j ∈ range n, (z + j) := by
        rw [eq_div_iff hp]; exact barnes_partial_rec z n
      rw [hr]
      set E := cexp ((z - 1 / 2) * harmonicC n - n)
      field_simp
      ring
    have hval := tendsto_nhds_unique (hlim.congr' heq) hT
    rw [barnesG_add_one, ← hval]
    conv_rhs => rw [barnesG, ← barnesPre_ratio z]
    ring
  · rw [show (1 : ℂ) = 0 + 1 by ring, barnesG_add_one]
    have h : barnesFactor 0 = fun _ => 1 := funext fun k => by simp [barnesFactor]
    simp [h, barnesPre]

/-- **DLMF 5.17.2**: `G(n) = (n − 2)! (n − 3)! ⋯ 1!`, `n = 2, 3, …`. -/
theorem dlmf_5_17_2 {n : ℕ} (hn : 2 ≤ n) : barnesG n = ∏ k ∈ Icc 1 (n - 2), (k ! : ℂ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h := dlmf_5_17_1.1 1 (not_mem_gammaPoles_of_re_pos (by simp))
    rw [dlmf_5_17_1.2, Gamma_one] at h
    norm_num at h ⊢
    exact h
  | succ n hn ih =>
    have hp : (n : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by
      simp only [natCast_re]; exact_mod_cast (by omega : 0 < n))
    have h := dlmf_5_17_1.1 n hp
    push_cast
    rw [h, ih]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 - 1 = (m - 1) + 1 by omega, prod_Icc_succ_top (by omega),
      show m - 1 + 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
    push_cast
    rw [Gamma_nat_eq_factorial]
    ring

end Azurite.DLMF
