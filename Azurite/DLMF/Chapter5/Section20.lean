/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Mehta
import Azurite.DLMF.Chapter5.Section14Dyson
import Azurite.DLMF.Chapter5.Section14Range
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# DLMF §5.20: Physical applications (Coulomb gases)

Formalization of <https://dlmf.nist.gov/5.20>, with inverse temperature `β = 1/(kT) > 0`.

* 5.20.1: `W = ½ ∑ x_ℓ² − ∑_{ℓ<j} ln |x_ℓ − x_j|` (`coulombLineW`, definition).
* 5.20.2: the equilibrium density `P = C e^{−βW}` (`coulombLineDensity`); with
  `C = 1/ψₙ(β)` it is a probability density (`dlmf_5_20_2`).
* 5.20.3: `ψₙ(β) = ∫_{ℝⁿ} e^{−βW} dx = (2π)^{n/2} β^{−n/2 − βn(n−1)/4}
  ∏_{j=1}^n Γ(1 + ½jβ) / Γ(1 + ½β)ⁿ` (`coulombLinePsi`, `dlmf_5_20_3`): Mehta's integral 5.14.6
  with `c = β/2` after `x = t/√β`.
* 5.20.4: `W = −∑_{ℓ<j} ln |e^{iθ_ℓ} − e^{iθ_j}|` on the unit circle (`coulombCircleW`).
* 5.20.5: `ψₙ(β) = (2π)^{−n} ∫_{[−π,π]ⁿ} e^{−βW} dθ = Γ(1 + ½nβ) / Γ(1 + ½β)ⁿ`
  (`coulombCirclePsi`, `dlmf_5_20_5`, for `β ≥ 0`): Dyson's integral 5.14.7 with `b = β/2`.

`ln 0` is Lean's `0` on the null set where two charges coincide; the integrands agree with the
§5.14 integrands almost everywhere.
-/

open Finset MeasureTheory
open scoped Real

namespace Azurite.DLMF

variable {n : ℕ}

/-! ### Charges on a line -/

/-- DLMF 5.20.1: `W = ½ ∑ x_ℓ² − ∑_{ℓ<j} ln |x_ℓ − x_j|`. -/
noncomputable def coulombLineW (x : Fin n → ℝ) : ℝ :=
  1 / 2 * ∑ l, x l ^ 2 - ∑ l, ∑ j ∈ Ioi l, Real.log |x l - x j|

/-- DLMF 5.20.3 (definition): the partition function `ψₙ(β) = ∫_{ℝⁿ} e^{−βW} dx`. -/
noncomputable def coulombLinePsi (n : ℕ) (β : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, Real.exp (-(β * coulombLineW x))

/-- DLMF 5.20.2: the equilibrium density `P = C e^{−βW}`, `C = 1/ψₙ(β)`. -/
noncomputable def coulombLineDensity (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  (coulombLinePsi n β)⁻¹ * Real.exp (-(β * coulombLineW x))

/-- Mehta's integrand with `c = β/2`, real form. -/
noncomputable def mehtaReal (β : ℝ) (t : Fin n → ℝ) : ℝ :=
  (∏ k, Real.exp (-(t k ^ 2) / 2)) * |vandermondeDelta t| ^ β

theorem mehtaF_half_eq (β : ℝ) (t : Fin n → ℝ) :
    mehtaF (n := n) ((β : ℂ) / 2) t = (mehtaReal β t : ℂ) := by
  rw [mehtaF, mehtaReal, Complex.ofReal_mul, Complex.ofReal_prod,
    show 2 * ((β : ℂ) / 2) = (β : ℂ) by ring, ← Complex.ofReal_cpow (abs_nonneg _)]

theorem integral_mehtaReal {β : ℝ} (hβ : 0 ≤ β) :
    ∫ t, mehtaReal (n := n) β t = (2 * π) ^ ((n : ℝ) / 2) *
      (∏ k ∈ range n, Real.Gamma (1 + (k + 1) * β / 2)) / Real.Gamma (1 + β / 2) ^ n := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← mehtaF_half_eq]
  have h := dlmf_5_14_6 (n := n) (c := (β : ℂ) / 2) (by
    have : ((β : ℂ) / 2).re = β / 2 := by simp
    rw [this]; have : (0 : ℝ) ≤ n * (β / 2) := by positivity
    linarith)
  have hpos : (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  rw [inv_mul_eq_iff_eq_mul₀ hpos] at h
  rw [h]
  have hG : ∀ k : ℕ, Complex.Gamma (1 + ((k : ℂ) + 1) * ((β : ℂ) / 2)) =
      ((Real.Gamma (1 + (k + 1) * β / 2) : ℝ) : ℂ) := by
    intro k
    rw [← Complex.Gamma_ofReal]; congr 1; push_cast; ring
  have hG1 : Complex.Gamma (1 + (β : ℂ) / 2) = ((Real.Gamma (1 + β / 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; congr 1; push_cast; ring
  simp only [hG, hG1]
  push_cast
  ring

theorem natCast_pairCount (n : ℕ) : (pairCount n : ℝ) = n * ((n : ℝ) - 1) / 2 := by
  have h := two_mul_pairCount n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pairCount]
  · have h' : (2 : ℝ) * pairCount n = n * ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hn, Nat.cast_one] at h'
    linarith

/-- The rescaling `x = t/√β`: `e^{−βW(t/√β)} = (1/√β)^{βP} e^{−|t|²/2} |Δ(t)|^β`. -/
theorem exp_coulombLineW_smul {β : ℝ} (hβ : 0 < β) {t : Fin n → ℝ}
    (hΔ : vandermondeDelta t ≠ 0) :
    Real.exp (-(β * coulombLineW ((√β)⁻¹ • t))) =
      (√β)⁻¹ ^ (β * pairCount n) * mehtaReal β t := by
  set R := (√β)⁻¹ with hRdef
  have hR : 0 < R := inv_pos.2 (Real.sqrt_pos.2 hβ)
  have hR2 : R ^ 2 * β = 1 := by
    rw [hRdef, inv_pow, Real.sq_sqrt hβ.le, inv_mul_cancel₀ hβ.ne']
  have hd : ∀ l, ∀ j ∈ Ioi l, t l - t j ≠ 0 := by
    intro l j hj h0
    apply hΔ
    exact Finset.prod_eq_zero (mem_univ l) (Finset.prod_eq_zero hj h0)
  have habs : |vandermondeDelta t| = ∏ l, ∏ j ∈ Ioi l, |t l - t j| := by
    rw [vandermondeDelta, Finset.abs_prod]
    exact Finset.prod_congr rfl fun l _ => Finset.abs_prod _ _
  have hlogΔ : Real.log |vandermondeDelta t| = ∑ l, ∑ j ∈ Ioi l, Real.log |t l - t j| := by
    rw [habs, Real.log_prod]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Real.log_prod]
      exact fun j hj => abs_ne_zero.2 (hd l j hj)
    · exact fun l _ => Finset.prod_ne_zero_iff.2 fun j hj => abs_ne_zero.2 (hd l j hj)
  have hlog : ∑ l, ∑ j ∈ Ioi l, Real.log |(R • t) l - (R • t) j| =
      pairCount n * Real.log R + Real.log |vandermondeDelta t| := by
    rw [hlogΔ, pairCount, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos hR, Real.log_mul hR.ne' (abs_ne_zero.2 (hd l j hj))]
  have hsq : ∑ l, ((R • t) l) ^ 2 = R ^ 2 * ∑ l, t l ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hΔpos : 0 < |vandermondeDelta t| := abs_pos.2 hΔ
  rw [coulombLineW, hlog, hsq, mehtaReal, Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hΔpos,
    ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have e : ∑ x, -t x ^ 2 / 2 = -(1 / 2) * ∑ l, t l ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  rw [e]
  linear_combination (-(1 / 2) * ∑ l, t l ^ 2) * hR2

/-- DLMF 5.20.3: `ψₙ(β) = (2π)^{n/2} β^{−n/2 − βn(n−1)/4} ∏_{j=1}^n Γ(1 + ½jβ) / Γ(1 + ½β)ⁿ`. -/
theorem dlmf_5_20_3 {β : ℝ} (hβ : 0 < β) :
    coulombLinePsi n β = (2 * π) ^ ((n : ℝ) / 2) * β ^ (-(n : ℝ) / 2 - β * n * (n - 1) / 4) *
      (∏ k ∈ range n, Real.Gamma (1 + (k + 1) * β / 2)) / Real.Gamma (1 + β / 2) ^ n := by
  set s := √β with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hβ
  have hcomp := Measure.integral_comp_smul (μ := (volume : Measure (Fin n → ℝ)))
    (fun x => Real.exp (-(β * coulombLineW x))) s⁻¹
  rw [Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos hs0 n), smul_eq_mul] at hcomp
  have hae : (fun t : Fin n → ℝ => Real.exp (-(β * coulombLineW (s⁻¹ • t)))) =ᵐ[volume]
      fun t => s⁻¹ ^ (β * pairCount n) * mehtaReal β t := by
    filter_upwards [ae_vandermondeDelta_ne_zero] with t ht
    exact exp_coulombLineW_smul hβ ht
  rw [integral_congr_ae hae, integral_const_mul, integral_mehtaReal hβ.le] at hcomp
  have hpsi : coulombLinePsi n β = (s ^ n)⁻¹ * (s⁻¹ ^ (β * pairCount n) *
      ((2 * π) ^ ((n : ℝ) / 2) * (∏ k ∈ range n, Real.Gamma (1 + (k + 1) * β / 2)) /
        Real.Gamma (1 + β / 2) ^ n)) := by
    rw [coulombLinePsi, hcomp, inv_mul_cancel_left₀ (pow_ne_zero _ hs0.ne')]
  rw [hpsi]
  have hexp : (s ^ n)⁻¹ * s⁻¹ ^ (β * pairCount n) = β ^ (-(n : ℝ) / 2 - β * n * (n - 1) / 4) := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hβ.le,
      Real.inv_rpow (Real.rpow_nonneg hβ.le _), ← Real.rpow_mul hβ.le, ← Real.rpow_neg hβ.le,
      ← Real.rpow_neg hβ.le, ← Real.rpow_add hβ, natCast_pairCount]
    congr 1; ring
  rw [← hexp]
  ring

theorem coulombLinePsi_pos {β : ℝ} (hβ : 0 < β) : 0 < coulombLinePsi n β := by
  rw [dlmf_5_20_3 hβ]
  have hG : ∀ x : ℝ, 0 < x → 0 < Real.Gamma x := fun x hx => Real.Gamma_pos_of_pos hx
  have hP : 0 < ∏ k ∈ range n, Real.Gamma (1 + (k + 1) * β / 2) :=
    Finset.prod_pos fun k _ => hG _ (by positivity)
  have h1 := hG (1 + β / 2) (by positivity)
  have h2 : 0 < β ^ (-(n : ℝ) / 2 - β * n * (n - 1) / 4) := Real.rpow_pos_of_pos hβ _
  positivity

/-- DLMF 5.20.2: with `C = 1/ψₙ(β)`, `P = C e^{−βW}` is a probability density on `ℝⁿ`. -/
theorem dlmf_5_20_2 {β : ℝ} (hβ : 0 < β) :
    (∀ x, 0 ≤ coulombLineDensity (n := n) β x) ∧ ∫ x, coulombLineDensity (n := n) β x = 1 := by
  have hψ := coulombLinePsi_pos (n := n) hβ
  refine ⟨fun x => by unfold coulombLineDensity; positivity, ?_⟩
  simp only [coulombLineDensity]
  rw [integral_const_mul, ← coulombLinePsi, inv_mul_cancel₀ hψ.ne']

/-! ### Charges on a circle -/

/-- DLMF 5.20.4: `W = −∑_{ℓ<j} ln |e^{iθ_ℓ} − e^{iθ_j}|`. -/
noncomputable def coulombCircleW (θ : Fin n → ℝ) : ℝ :=
  -∑ l, ∑ j ∈ Ioi l, Real.log (chordR θ l j)

/-- DLMF 5.20.5 (definition): `ψₙ(β) = (2π)^{−n} ∫_{[−π,π]ⁿ} e^{−βW} dθ`. -/
noncomputable def coulombCirclePsi (n : ℕ) (β : ℝ) : ℝ :=
  ((2 * π) ^ n)⁻¹ * ∫ θ in torusBox n, Real.exp (-(β * coulombCircleW θ))

theorem exp_coulombCircleW {β : ℝ} {θ : Fin n → ℝ}
    (h : ∀ j k : Fin n, j < k → chordR θ j k ≠ 0) :
    ((Real.exp (-(β * coulombCircleW θ)) : ℝ) : ℂ) = dysonF ((β : ℂ) / 2) θ := by
  have hpos : ∀ l, ∀ j ∈ Ioi l, 0 < chordR θ l j := fun l j hj =>
    lt_of_le_of_ne (norm_nonneg _) (h l j (mem_Ioi.1 hj)).symm
  have e : Real.exp (-(β * coulombCircleW θ)) = ∏ l, ∏ j ∈ Ioi l, chordR θ l j ^ β := by
    rw [coulombCircleW, mul_neg, neg_neg, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Real.rpow_def_of_pos (hpos l j hj), mul_comm]
  rw [e, dysonF, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show 2 * ((β : ℂ) / 2) = (β : ℂ) by ring, ← Complex.ofReal_cpow (norm_nonneg _)]
  rfl

/-- DLMF 5.20.5: `ψₙ(β) = Γ(1 + ½nβ) / Γ(1 + ½β)ⁿ` (Dyson). -/
theorem dlmf_5_20_5 {β : ℝ} (hβ : 0 ≤ β) :
    coulombCirclePsi n β = Real.Gamma (1 + n * β / 2) / Real.Gamma (1 + β / 2) ^ n := by
  apply Complex.ofReal_injective
  have h := dlmf_5_14_7 (n := n) (b := (β : ℂ) / 2) (by
    have : ((β : ℂ) / 2).re = β / 2 := by simp
    rw [this]; have : (0 : ℝ) ≤ n * (β / 2) := by positivity
    linarith)
  have hint : ((∫ θ in torusBox n, Real.exp (-(β * coulombCircleW θ)) : ℝ) : ℂ) =
      ∫ θ in torusBox n, dysonF ((β : ℂ) / 2) θ := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [ae_chordR_ne_zero] with θ hθ
    exact exp_coulombCircleW hθ
  rw [coulombCirclePsi, Complex.ofReal_mul, hint]
  have hd : ∫ θ in torusBox n, dysonF ((β : ℂ) / 2) θ = ∫ θ in torusBox n,
      ∏ j, ∏ k ∈ Ioi j, ((‖Complex.exp ((θ j : ℂ) * Complex.I) -
        Complex.exp ((θ k : ℂ) * Complex.I)‖ : ℝ) : ℂ) ^ (2 * ((β : ℂ) / 2)) := rfl
  rw [hd]
  push_cast at h ⊢
  rw [h]
  have hG : Complex.Gamma (1 + (β : ℂ) / 2 * n) = ((Real.Gamma (1 + n * β / 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; congr 1; push_cast; ring
  have hG1 : Complex.Gamma (1 + (β : ℂ) / 2) = ((Real.Gamma (1 + β / 2) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; congr 1; push_cast; ring
  rw [hG, hG1]

end Azurite.DLMF
