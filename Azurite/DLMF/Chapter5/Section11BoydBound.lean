/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11BoydRem
import Azurite.DLMF.Chapter5.Section10

/-!
# DLMF 5.11.11: the `sec(ph z)` branch

Formalization of the first branch of <https://dlmf.nist.gov/5.11.E11> (Boyd 1994): for
`ℜz > 0` and `K ≥ 1`,
`|R_K(z)| ≤ (1 + ζ(K)) Γ(K) / (2 (2π)^{K+1} |z|^K) · (1 + sec(ph z))`,
with `1 + ζ(1)` replaced by `4` (`boydZeta`; `dlmf_5_11_11_sec`).

From Boyd's representation (`norm_boydRem_le`) it remains to bound
`J_K = ∫₀^∞ t^{K−1} e^{−2πt}(1 − e^{−2πt})^{−1/2} dt` (`boydMom (K − 1)`):
* `J₁ = 1/π` (`boydMom_zero`, an exact primitive);
* `(1 − e^{−x})^{−1/2} ≤ ½(1 + (1 − e^{−x})⁻¹)` (`boydM_le_half`) and
  `∫₀^∞ t^{K−1} e^{−2πt}/(1 − e^{−2πt}) dt = Γ(K) ζ(K)/(2π)^K` for `K ≥ 2`
  (`integral_zetaIntegrand`, term-by-term from the geometric series) give
  `J_K ≤ (1 + ζ(K)) Γ(K)/(2 (2π)^K)` (`boydMom_le`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### `∫₀^∞ tⁿ e^{−2πt}/(1 − e^{−2πt}) dt = n! ζ(n+1)/(2π)^{n+1}` -/

/-- `(1 − e^{−x})⁻¹ ≤ 1 + 1/x` for `x > 0`. -/
theorem inv_one_sub_exp_le {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 + 1 / x := by
  have h1 := Real.add_one_le_exp x
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hlt : Real.exp (-x) < 1 := by
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith); rwa [Real.exp_zero] at this
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  rw [show (1 + 1 / x) * (1 - Real.exp (-x)) = (x + 1) * (1 - Real.exp (-x)) / x by
    field_simp, le_div_iff₀ hx]
  nlinarith [Real.exp_pos (-x)]

/-- The integrand `tⁿ e^{−2πt}/(1 − e^{−2πt})`. -/
noncomputable def zetaIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n * (Real.exp (-(2 * π * t)) / (1 - Real.exp (-(2 * π * t))))

theorem zetaIntegrand_nonneg (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ zetaIntegrand n t :=
  mul_nonneg (pow_nonneg ht.le n) (div_nonneg (Real.exp_pos _).le (one_sub_exp_pos ht).le)

theorem zetaIntegrand_le {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    zetaIntegrand n t ≤ t ^ n * Real.exp (-(2 * π * t)) +
      (2 * π)⁻¹ * (t ^ (n - 1) * Real.exp (-(2 * π * t))) := by
  have hx : 0 < 2 * π * t := by positivity
  have h := inv_one_sub_exp_le hx
  have hp := pow_nonneg ht.le n
  have hE := (Real.exp_pos (-(2 * π * t))).le
  have htn : t ^ n = t ^ (n - 1) * t := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [zetaIntegrand, div_eq_mul_inv (Real.exp _)]
  calc t ^ n * (Real.exp (-(2 * π * t)) * (1 - Real.exp (-(2 * π * t)))⁻¹)
      ≤ t ^ n * (Real.exp (-(2 * π * t)) * (1 + 1 / (2 * π * t))) := by gcongr
    _ = _ := by rw [htn]; field_simp

theorem integrableOn_zetaIntegrand {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (zetaIntegrand n) (Ioi 0) := by
  have h1 := integrableOn_pow_mul_exp_neg_mul n (r := 2 * π) (by positivity)
  have h2 := (integrableOn_pow_mul_exp_neg_mul (n - 1) (r := 2 * π) (by positivity)).const_mul
    (2 * π)⁻¹
  refine Integrable.mono' (h1.add h2) ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · unfold zetaIntegrand; fun_prop
  · have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (zetaIntegrand_nonneg n ht')]
    exact zetaIntegrand_le hn ht'

/-- The real `ζ(j + 2) = ∑_{k ≥ 0} 1/(k + 1)^{j+2}`. -/
theorem hasSum_zeta_re (j : ℕ) :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ (j + 2)) (riemannZeta (j + 2)).re := by
  have h := Complex.reCLM.hasSum (hasSum_zeta_add_two j)
  refine h.congr_fun fun k => ?_
  simp only [Complex.reCLM_apply]
  rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_pow, ← ofReal_one,
    ← ofReal_div, ofReal_re]

/-- `∫₀^∞ t^{j+1} e^{−2πt}/(1 − e^{−2πt}) dt = (j+1)! ζ(j+2)/(2π)^{j+2}`. -/
theorem integral_zetaIntegrand (j : ℕ) :
    ∫ t in Ioi (0 : ℝ), zetaIntegrand (j + 1) t =
      (j + 1)! * (riemannZeta (j + 2)).re / (2 * π) ^ (j + 2) := by
  set n := j + 1
  set F : ℕ → ℝ → ℝ := fun k t => t ^ n * Real.exp (-((2 * π * ((k : ℝ) + 1)) * t)) with hF
  have hc : ∀ k : ℕ, 0 < 2 * π * ((k : ℝ) + 1) := fun k => by positivity
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    integrableOn_pow_mul_exp_neg_mul n (hc k)
  have hval : ∀ k, ∫ t in Ioi (0 : ℝ), F k t = n ! / (2 * π) ^ (n + 1) *
      (1 / ((k : ℝ) + 1) ^ (j + 2)) := fun k => by
    rw [integral_pow_mul_exp_neg_mul n (hc k), mul_pow]
    have : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    rfl
  have hnorm : ∀ k, ∫ t in Ioi (0 : ℝ), ‖F k t‖ = ∫ t in Ioi (0 : ℝ), F k t := fun k =>
    setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt ht) n) (Real.exp_pos _).le)
  have hS := (hasSum_zeta_re j).mul_left (n ! / (2 * π) ^ (n + 1))
  have hsum : HasSum (fun k => ∫ t in Ioi (0 : ℝ), F k t)
      (n ! / (2 * π) ^ (n + 1) * (riemannZeta (j + 2)).re) := by
    simpa only [hval] using hS
  have h := hasSum_integral_of_summable_integral_norm hint (by
    simpa only [hnorm] using hsum.summable)
  have heq : ∫ t in Ioi (0 : ℝ), (∑' k, F k t) = ∫ t in Ioi (0 : ℝ), zetaIntegrand n t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    set r := Real.exp (-(2 * π * t))
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by linarith [one_sub_exp_pos ht']
    have hterm : ∀ k : ℕ, F k t = t ^ n * r * r ^ k := fun k => by
      rw [mul_assoc, ← pow_succ', ← Real.exp_nat_mul]
      simp only [hF]
      congr 2
      push_cast
      ring
    simp only [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    show t ^ n * r * (1 - r)⁻¹ = t ^ n * (r / (1 - r))
    rw [div_eq_mul_inv]
    ring
  rw [← heq, ← h.tsum_eq, hsum.tsum_eq]
  push_cast [n]
  ring

/-! ### The moments `J_K` -/

/-- `J₁ = ∫₀^∞ e^{−2πt}(1 − e^{−2πt})^{−1/2} dt = 1/π`. -/
theorem boydMom_zero : boydMom 0 = 1 / π := by
  have hπ := Real.pi_pos
  set f : ℝ → ℝ := fun t => π⁻¹ * Real.sqrt (1 - Real.exp (-(2 * π * t))) with hf
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (t ^ 0 * boydM t) t := fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have hE : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(2 * π * t)))
        (2 * π * Real.exp (-(2 * π * t))) t := by
      have h2 := ((hasDerivAt_mul_const (-(2 * π)) (x := t)).exp).const_sub 1
      convert h2 using 1
      · funext s; ring_nf
      · ring_nf
    have := (hE.sqrt (one_sub_exp_pos ht').ne').const_mul π⁻¹
    convert this using 1
    rw [boydM, pow_zero, one_mul]
    field_simp
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    rw [hf]; exact (by fun_prop : Continuous f).continuousWithinAt
  have hlim : Tendsto f atTop (𝓝 (π⁻¹ * Real.sqrt (1 - 0))) := by
    refine tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.sub ?_))
    have : Tendsto (fun t : ℝ => -(2 * π * t)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity))
    exact Real.tendsto_exp_atBot.comp this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_pow_mul_boydM 0) hlim
  rw [boydMom, h, hf]
  simp

/-- `(1 − e^{−x})^{−1/2} ≤ ½(1 + (1 − e^{−x})⁻¹)`, i.e. `|A(t)| ≤ ½(e^{−2πt} + e^{−2πt}/(1 −
e^{−2πt}))`. -/
theorem boydM_le_half {t : ℝ} (ht : 0 < t) :
    boydM t ≤ (Real.exp (-(2 * π * t)) + Real.exp (-(2 * π * t)) /
      (1 - Real.exp (-(2 * π * t)))) / 2 := by
  have ha := one_sub_exp_pos ht
  set a := 1 - Real.exp (-(2 * π * t))
  set s := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hss : s * s = a := Real.mul_self_sqrt ha.le
  have hE := Real.exp_pos (-(2 * π * t))
  rw [boydM]
  rw [← hss, div_le_iff₀ hs]
  have key : 2 * (s * s) ≤ (s * s + 1) * s := by
    nlinarith [mul_nonneg hs.le (sq_nonneg (s - 1))]
  have e : (Real.exp (-(2 * π * t)) + Real.exp (-(2 * π * t)) / (s * s)) / 2 * s =
      Real.exp (-(2 * π * t)) * ((s * s + 1) * s) / (2 * (s * s)) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left key hE.le

/-- `J_{n+1} ≤ (1 + ζ(n+1)) n!/(2 (2π)^{n+1})` for `n ≥ 1`. -/
theorem boydMom_le (j : ℕ) :
    boydMom (j + 1) ≤ (1 + (riemannZeta (j + 2)).re) * (j + 1)! / (2 * (2 * π) ^ (j + 2)) := by
  have hπ := Real.pi_pos
  have h1 := integrableOn_pow_mul_exp_neg_mul (j + 1) (r := 2 * π) (by positivity)
  have h2 := integrableOn_zetaIntegrand (n := j + 1) le_add_self
  have hle : boydMom (j + 1) ≤ ∫ t in Ioi (0 : ℝ),
      (t ^ (j + 1) * Real.exp (-(2 * π * t)) + zetaIntegrand (j + 1) t) / 2 := by
    refine setIntegral_mono_on (integrableOn_pow_mul_boydM (j + 1))
      ((h1.add h2).div_const 2) measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have := mul_le_mul_of_nonneg_left (boydM_le_half ht') (pow_nonneg ht'.le (j + 1))
    refine this.trans (le_of_eq ?_)
    rw [zetaIntegrand]
    ring
  rw [integral_div, integral_add h1 h2, integral_pow_mul_exp_neg_mul _ (by positivity),
    integral_zetaIntegrand] at hle
  refine hle.trans (le_of_eq ?_)
  field_simp

/-! ### The bound -/

/-- `1 + ζ(K)` of 5.11.11 is read with `ζ(1)` replaced by `3`. -/
noncomputable def boydZeta (K : ℕ) : ℝ := if K = 1 then 3 else (riemannZeta K).re

/-- `J_K ≤ (1 + ζ(K)) Γ(K)/(2 (2π)^K)` for `K ≥ 1` (with `ζ(1) → 3`). -/
theorem boydMom_le_boydZeta (n : ℕ) :
    boydMom n ≤ (1 + boydZeta (n + 1)) * Real.Gamma (n + 1) / (2 * (2 * π) ^ (n + 1)) := by
  rw [Real.Gamma_nat_eq_factorial]
  rcases n with _ | j
  · have hz : boydZeta (0 + 1) = 3 := by simp [boydZeta]
    rw [boydMom_zero, hz]
    have := Real.pi_pos
    simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, mul_one]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have hz : boydZeta (j + 1 + 1) = (riemannZeta ((j + 1 + 1 : ℕ) : ℂ)).re := by
      simp [boydZeta]
    rw [hz]
    have := boydMom_le j
    push_cast at this ⊢
    rwa [show (j : ℂ) + 1 + 1 = j + 2 by ring]

/-- **DLMF 5.11.11** (the `sec` branch, Boyd 1994): for `ℜz > 0` and `K ≥ 1`,
`|R_K(z)| ≤ (1 + ζ(K)) Γ(K)/(2 (2π)^{K+1} |z|^K) · (1 + sec(ph z))`, with `ζ(1)` replaced by `3`. -/
theorem dlmf_5_11_11_sec {K : ℕ} (hK : 1 ≤ K) {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingR K z‖ ≤ (1 + boydZeta K) * Real.Gamma K / (2 * (2 * π) ^ (K + 1) * ‖z‖ ^ K) *
      (1 + 1 / Real.cos (arg z)) := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  have hz0 := ne_zero_of_pos_re hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [stirlingR_eq_boydRem hz, cos_arg hz0, one_div_div]
  refine (norm_boydRem_le hz n).trans ?_
  have hM := boydMom_le_boydZeta n
  have hsec : 0 ≤ 1 + ‖z‖ / z.re := by positivity
  calc (1 + ‖z‖ / z.re) / (2 * π * ‖z‖ ^ (n + 1)) * boydMom n
      ≤ (1 + ‖z‖ / z.re) / (2 * π * ‖z‖ ^ (n + 1)) *
          ((1 + boydZeta (n + 1)) * Real.Gamma (n + 1) / (2 * (2 * π) ^ (n + 1))) := by
        gcongr
    _ = _ := by
        push_cast
        rw [pow_succ (2 * π) (n + 1)]
        field_simp

end Azurite.DLMF
