/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section11TerminantAsymp
import Azurite.DLMF.Chapter5.Section11Gstar

/-!
# DLMF §2.11(iii): 2.11.13 with the DLMF normalization, and 2.11.14

`dlmf_2_11_13` (`Section11TerminantAsymp.lean`) has the prefactor `Γ(ρ)ρ^{−ρ}/(2π)` and the
coefficients `â_{2s}` (`ahat`). Since `Γ(ρ)ρ^{−ρ} = (2π/ρ)^{1/2} e^{−ρ} Γ*(ρ)` and
`Γ*(ρ) ∼ ∑ gₖ ρ^{−k}` (5.11.3), the DLMF form
`F_{n+p}(z) ∼ e^{−i(ρ+α)θ}/(1 + e^{−iθ}) · e^{−ρ−z}/(2πρ)^{1/2} ∑ a_{2s}(θ, α)/ρˢ`
holds with the Cauchy product `a_{2s} = ∑_{k≤s} gₖ â_{2(s−k)}` (`terminantA`), uniformly for
`|θ| ≤ π − δ`, `|α| ≤ A` (`dlmf_2_11_13_dlmf`). Then `a₂ = (6α² − 6α + 1)/12 − α/(1 + e^{iθ}) +
1/(1 + e^{iθ})²` (`terminantA_zero_one`).
-/

open Complex Filter Topology Set
open scoped Real

namespace Azurite.DLMF

/-- DLMF's prefactor `e^{−i(ρ+α)θ}/(1 + e^{−iθ}) · e^{−ρ−z}/(2πρ)^{1/2}`, `z = ρe^{iθ}`. -/
noncomputable def terminantPrefDLMF (ρ θ : ℝ) (α : ℂ) : ℂ :=
  cexp (-(((ρ : ℂ) + α) * (θ * I))) / (1 + cexp (-(θ * I))) *
    cexp (-(ρ : ℂ) - ρ * cexp (θ * I)) / (Real.sqrt (2 * π * ρ) : ℂ)

/-- DLMF's coefficients `a_{2s}(θ, α) = ∑_{k≤s} gₖ â_{2(s−k)}(θ, α)`. -/
noncomputable def terminantA (θ : ℝ) (α : ℂ) (s : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (s + 1), (BZ.stirlingCoeff k : ℂ) * ahat θ α (s - k)

theorem terminantPref_eq {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) (α : ℂ) :
    terminantPref ρ θ α = terminantPrefDLMF ρ θ α * scaledGamma ρ := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr hpos
  have hsρ : Real.sqrt (2 * π * ρ) = Real.sqrt (2 * π) * Real.sqrt ρ :=
    Real.sqrt_mul hpos.le ρ
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hpow : ρ ^ (ρ - 1 / 2) * Real.sqrt ρ = ρ ^ ρ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hρ]; ring_nf
  have hcp : (ρ : ℂ) ^ ((ρ : ℂ) - 1 / 2) = ((ρ ^ (ρ - 1 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hρ.le]; push_cast; ring_nf
  have hp1 := Real.rpow_pos_of_pos hρ (ρ - 1 / 2)
  have hp2 := Real.rpow_pos_of_pos hρ ρ
  have hrneg : ρ ^ (-ρ) = (ρ ^ ρ)⁻¹ := Real.rpow_neg hρ.le ρ
  rw [terminantPref, terminantPrefDLMF, scaledGamma, Complex.Gamma_ofReal, hcp,
    show -(ρ : ℂ) - ρ * cexp (θ * I) = -(ρ : ℂ) + -(ρ * cexp (θ * I)) by ring, Complex.exp_add,
    hsρ, hrneg, ← hpow]
  have he : cexp (-(ρ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  push_cast
  field_simp
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  push_cast
  ring

/-! ### Real Stirling bound -/

theorem scaledGamma_real_bound (K : ℕ) : ∃ C R : ℝ, 1 ≤ R ∧ ∀ ρ : ℝ, R ≤ ρ →
    ‖scaledGamma ρ - ∑ k ∈ Finset.range K, (BZ.stirlingCoeff k : ℂ) / (ρ : ℂ) ^ k‖ ≤
      C / ρ ^ K := by
  have hS := isAsympExpansionDLMF_iff.mp (dlmf_5_11_3 Real.pi_pos le_rfl)
  have hk : Tendsto (fun x : ℝ => (x : ℂ)) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - π))) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
    · simpa using tendsto_abs_atTop_atTop
    · filter_upwards [eventually_gt_atTop 0] with x hx
      refine ⟨Complex.ofReal_ne_zero.mpr hx.ne', ?_⟩
      simp [arg_ofReal_of_nonneg hx.le]
  obtain ⟨C, hC⟩ := ((hS K).comp_tendsto hk).bound
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hC.and (eventually_ge_atTop 1))
  refine ⟨C, max R 1, le_max_right _ _, fun ρ hρ => ?_⟩
  obtain ⟨h1, h2⟩ := hR ρ (le_trans (le_max_left _ _) hρ)
  have hρ0 : 0 < ρ := by linarith
  simp only [Function.comp, eval_trunc_eq_sum, PowerSeries.coeff_mk] at h1
  have e : ∑ k ∈ Finset.range K, (BZ.stirlingCoeff k : ℂ) * (ρ : ℂ)⁻¹ ^ k =
      ∑ k ∈ Finset.range K, (BZ.stirlingCoeff k : ℂ) / (ρ : ℂ) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [inv_pow, div_eq_mul_inv]
  rw [e, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ0.le, inv_pow] at h1
  rwa [div_eq_mul_inv]

/-! ### Uniform bounds on `â` -/

theorem norm_ahat_le {δ A θ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hθ : |θ| ≤ π - δ) {α : ℂ}
    (hα : ‖α‖ ≤ A) (s : ℕ) :
    ‖ahat θ α s‖ ≤ ∑ i ∈ Finset.range (2 * s + 1), ∑ j ∈ Finset.range (2 * s + 1),
      (A + i) ^ i * (1 / Real.sin δ) ^ j * |(mPoly (i + j)).coeff s| := by
  have hr := norm_rTheta_le hδ hδ' hθ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hA0 : 0 ≤ A := (norm_nonneg α).trans hα
  rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right (mul_le_mul ((norm_binomC_le α i).trans (by gcongr))
    (pow_le_pow_left₀ (norm_nonneg _) hr j) (by positivity) (pow_nonneg (by positivity) _))
    (abs_nonneg _)

/-! ### Truncated Cauchy products -/

/-- `(∑_{k<K} gₖ w^k)(∑_{s<K} aₛ wˢ) − ∑_{s<K} (g ⋆ a)ₛ wˢ = O(w^K)` with an explicit constant,
`w = 1/ρ ≤ 1`. -/
theorem norm_cauchy_trunc_sub_le (g a : ℕ → ℂ) (K : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ‖(∑ k ∈ Finset.range K, g k / (ρ : ℂ) ^ k) * (∑ s ∈ Finset.range K, a s / (ρ : ℂ) ^ s) -
        ∑ s ∈ Finset.range K, (∑ k ∈ Finset.range (s + 1), g k * a (s - k)) / (ρ : ℂ) ^ s‖ ≤
      (∑ k ∈ Finset.range K, ∑ s ∈ Finset.range K, ‖g k‖ * ‖a s‖) / ρ ^ K := by
  have hρ0 : 0 < ρ := by linarith
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  set F : ℕ → ℕ → ℂ := fun k j => g k * a j / (ρ : ℂ) ^ (k + j) with hF
  have hprod : (∑ k ∈ Finset.range K, g k / (ρ : ℂ) ^ k) *
      (∑ s ∈ Finset.range K, a s / (ρ : ℂ) ^ s) =
      ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range K, F k s := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [hF, pow_add]
    field_simp
  have hdiag : ∑ s ∈ Finset.range K, (∑ k ∈ Finset.range (s + 1), g k * a (s - k)) /
      (ρ : ℂ) ^ s = ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range (K - k), F k j := by
    rw [← Finset.sum_range_diag_flip K F]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    simp only [hF]
    rw [show k + (s - k) = s by omega]
  rw [hprod, hdiag, ← Finset.sum_sub_distrib]
  have hsub : ∀ k ∈ Finset.range K, ∑ s ∈ Finset.range K, F k s -
      ∑ j ∈ Finset.range (K - k), F k j = ∑ s ∈ Finset.Ico (K - k) K, F k s := fun k _ =>
    (Finset.sum_Ico_eq_sub _ (Nat.sub_le K k)).symm
  rw [Finset.sum_congr rfl hsub, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [Finset.sum_div]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun s hs => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (by rw [Finset.range_eq_Ico]; exact Finset.Ico_subset_Ico_left (Nat.zero_le _))
    fun s _ _ => by positivity)
  · have hs' := Finset.mem_Ico.mp hs
    simp only [hF]
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    gcongr
    omega

/-! ### 2.11.13 and 2.11.14 -/

/-- **DLMF 2.11.13** with DLMF's normalization: with `z = ρe^{iθ}` and `q = n + p = ρ + α`,
`F_q(z) ∼ e^{−i(ρ+α)θ}/(1 + e^{−iθ}) · e^{−ρ−z}/(2πρ)^{1/2} ∑ a_{2s}(θ, α)/ρˢ` as `ρ → ∞`,
uniformly for `|θ| ≤ π − δ` and `|α| ≤ A`, with `a_{2s} = terminantA θ α s`. -/
theorem dlmf_2_11_13_dlmf (K : ℕ) {δ A : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hA : 0 ≤ A) :
    ∃ C ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ θ : ℝ, |θ| ≤ π - δ → ∀ α : ℂ, ‖α‖ ≤ A →
      ‖terminant (ρ + α) (polarW ρ θ) -
          terminantPrefDLMF ρ θ α * ∑ s ∈ Finset.range K, terminantA θ α s / (ρ : ℂ) ^ s‖ ≤
        C * ‖terminantPrefDLMF ρ θ α‖ / ρ ^ K := by
  obtain ⟨C1, ρ1, h1⟩ := dlmf_2_11_13 K hδ hδ' hA
  obtain ⟨C2, R, hR1, h2⟩ := scaledGamma_real_bound K
  set Mh : ℕ → ℝ := fun s => ∑ i ∈ Finset.range (2 * s + 1), ∑ j ∈ Finset.range (2 * s + 1),
    (A + i) ^ i * (1 / Real.sin δ) ^ j * |(mPoly (i + j)).coeff s| with hMh
  set g : ℕ → ℂ := fun k => (BZ.stirlingCoeff k : ℂ) with hg
  set MG := ∑ k ∈ Finset.range K, ‖g k‖
  set MT := ∑ s ∈ Finset.range K, Mh s
  set M3 := ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range K, ‖g k‖ * Mh s
  refine ⟨max C1 0 * (MG + |C2|) + |C2| * MT + M3, max ρ1 R,
    fun ρ hρ θ hθ α hα => ?_⟩
  have hρR : R ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρ1 : 1 ≤ ρ := le_trans hR1 hρR
  have hρ0 : 0 < ρ := by linarith
  have hρK : 0 < ρ ^ K := pow_pos hρ0 K
  have hMh : ∀ s, ‖ahat θ α s‖ ≤ Mh s := fun s => norm_ahat_le hδ hδ' hθ hα s
  have hinv : ∀ s, ‖1 / (ρ : ℂ) ^ s‖ ≤ 1 := fun s => by
    rw [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    exact div_le_one_of_le₀ (one_le_pow₀ hρ1) (by positivity)
  set P := terminantPrefDLMF ρ θ α
  set Γs := scaledGamma ρ
  set T := ∑ s ∈ Finset.range K, ahat θ α s / (ρ : ℂ) ^ s
  set G := ∑ k ∈ Finset.range K, g k / (ρ : ℂ) ^ k
  set D := ∑ s ∈ Finset.range K, terminantA θ α s / (ρ : ℂ) ^ s
  have hD : D = ∑ s ∈ Finset.range K,
      (∑ k ∈ Finset.range (s + 1), g k * ahat θ α (s - k)) / (ρ : ℂ) ^ s := rfl
  have hT : ‖T‖ ≤ MT := (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => by
    rw [div_eq_mul_one_div, norm_mul]
    calc ‖ahat θ α s‖ * ‖1 / (ρ : ℂ) ^ s‖ ≤ Mh s * 1 :=
          mul_le_mul (hMh s) (hinv s) (norm_nonneg _) ((norm_nonneg _).trans (hMh s))
      _ = Mh s := mul_one _)
  have hG : ‖G‖ ≤ MG := (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by
    rw [div_eq_mul_one_div, norm_mul]
    calc ‖g k‖ * ‖1 / (ρ : ℂ) ^ k‖ ≤ ‖g k‖ * 1 := by gcongr; exact hinv k
      _ = ‖g k‖ := mul_one _)
  have hΓG : ‖Γs - G‖ ≤ C2 / ρ ^ K := h2 ρ hρR
  have hC2 : C2 / ρ ^ K ≤ |C2| / ρ ^ K := by gcongr; exact le_abs_self _
  have hC2' : |C2| / ρ ^ K ≤ |C2| := div_le_self (abs_nonneg _) (one_le_pow₀ hρ1)
  have hΓ : ‖Γs‖ ≤ MG + |C2| := by
    calc ‖Γs‖ = ‖G + (Γs - G)‖ := by ring_nf
      _ ≤ ‖G‖ + ‖Γs - G‖ := norm_add_le _ _
      _ ≤ MG + |C2| := by linarith
  have e1 : ‖terminant (ρ + α) (polarW ρ θ) - terminantPref ρ θ α * T‖ ≤
      max C1 0 * (MG + |C2|) * ‖P‖ / ρ ^ K := by
    refine (h1 ρ (le_trans (le_max_left _ _) hρ) θ hθ α hα).trans ?_
    rw [terminantPref_eq hρ0, norm_mul]
    have hP := norm_nonneg P
    have hΓ0 := norm_nonneg Γs
    have hm : C1 * (‖P‖ * ‖Γs‖) ≤ max C1 0 * (‖P‖ * (MG + |C2|)) :=
      (mul_le_mul_of_nonneg_right (le_max_left C1 0) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (by gcongr) (le_max_right C1 0))
    calc C1 * (‖P‖ * ‖Γs‖) / ρ ^ K ≤ max C1 0 * (‖P‖ * (MG + |C2|)) / ρ ^ K := by gcongr
      _ = _ := by ring
  have e2 : ‖P * ((Γs - G) * T)‖ ≤ |C2| * MT * ‖P‖ / ρ ^ K := by
    rw [norm_mul, norm_mul]
    calc ‖P‖ * (‖Γs - G‖ * ‖T‖) ≤ ‖P‖ * (|C2| / ρ ^ K * MT) := by
          gcongr
          exact hΓG.trans hC2
      _ = _ := by ring
  have e3 : ‖P * (G * T - D)‖ ≤ M3 * ‖P‖ / ρ ^ K := by
    rw [norm_mul, hD]
    have hc := norm_cauchy_trunc_sub_le g (ahat θ α) K hρ1
    have hM : ∑ k ∈ Finset.range K, ∑ s ∈ Finset.range K, ‖g k‖ * ‖ahat θ α s‖ ≤ M3 :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun s _ => by gcongr; exact hMh s
    calc ‖P‖ * ‖G * T - _‖ ≤ ‖P‖ * (M3 / ρ ^ K) := by
          gcongr
          exact hc.trans (by gcongr)
      _ = _ := by ring
  have hsplit : terminant (ρ + α) (polarW ρ θ) - P * D =
      (terminant (ρ + α) (polarW ρ θ) - terminantPref ρ θ α * T) + P * ((Γs - G) * T) +
        P * (G * T - D) := by
    rw [terminantPref_eq hρ0]; ring
  rw [hsplit]
  refine (norm_add₃_le).trans ?_
  calc _ ≤ max C1 0 * (MG + |C2|) * ‖P‖ / ρ ^ K + |C2| * MT * ‖P‖ / ρ ^ K +
        M3 * ‖P‖ / ρ ^ K := by linarith
    _ = _ := by ring

/-- DLMF 2.11.14 for the coefficients of `dlmf_2_11_13_dlmf`: `a₀ = 1` and
`a₂(θ, α) = (6α² − 6α + 1)/12 − α/(1 + e^{iθ}) + 1/(1 + e^{iθ})²`. -/
theorem terminantA_zero_one (θ : ℝ) (α : ℂ) :
    terminantA θ α 0 = 1 ∧
      terminantA θ α 1 = (6 * α ^ 2 - 6 * α + 1) / 12 - α / (1 + cexp (θ * I)) +
        1 / (1 + cexp (θ * I)) ^ 2 := by
  refine ⟨by simp [terminantA, ahat_zero, BZ.stirlingCoeff_zero], ?_⟩
  rw [terminantA, Finset.sum_range_succ, Finset.sum_range_one, ahat_one, Nat.sub_self, ahat_zero,
    BZ.stirlingCoeff_zero, BZ.stirlingCoeff_one, rTheta]
  push_cast
  simp only [div_eq_mul_inv, one_mul, inv_pow]
  ring

end Azurite.DLMF
