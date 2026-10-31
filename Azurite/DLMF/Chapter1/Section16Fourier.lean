/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16Several
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# DLMF §1.16(vii): Fourier transforms of tempered distributions

https://dlmf.nist.gov/1.16.vii

* 1.16.29: `fourierN`, DLMF's `𝓕φ(x) = (2π)^{−n/2} ∫ φ(t) e^{i x·t} dt` on `ℝⁿ = Fin n → ℝ`. It is
  Mathlib's `VectorFourier.fourierIntegral 𝐞` for the bilinear form `L(t, x) = −(x·t)/(2π)`
  (`dotL`). Mathlib's packaged Schwartz Fourier transform needs an inner product space, so the
  estimate of its proof is rerun for `L` to make `𝓕` a continuous linear map of `𝓢(ℝⁿ, ℂ)`
  (`fourierIntegralCLM`, `fourierCLM`). Hence `𝓕φ ∈ 𝒯ₙ` (`isTempTestN_fourierN`, `fourierTest`).
* `𝓕(∂ⱼφ) = −i xⱼ 𝓕φ` (`fourierN_partialDeriv`) and `∂ⱼ𝓕φ = 𝓕(i tⱼ φ)`
  (`partialDeriv_fourierN`), from Mathlib's `fourierIntegral_fderiv`/`hasFDerivAt_fourierIntegral`.
* 1.16.30–1.16.32: `Dⱼ = (1/i)∂ⱼ` (`DT`), multiplication by `xⱼ` (`XT`), words `D^α`/`x^α`
  (`DW`, `XW`), the polynomial `P` (`polyEvalN`) over a finite set of multi-indices, and the
  operators `P(D)` (`PD`), `P`, `P₋` (`PX`, `PXneg`).
* 1.16.33–1.16.34: `𝓕(P(D)φ) = P(−x) 𝓕φ` and `𝓕(Pφ) = P(D)𝓕φ`.
* 1.16.35–1.16.37: `𝓕(u)` for tempered `u` (`fourierDist`, again tempered:
  `isTempDistN_fourierDist`), distributional `P(D)u` (`PDD`), multiplication by 1.16.6, and the
  two identities.
-/

open Set Filter Topology MeasureTheory Complex
open scoped ContDiff SchwartzMap Real FourierTransform

namespace Azurite.DLMF

variable {n : ℕ}

/-! ### The Fourier transform on `𝒯ₙ` (1.16.29) -/

/-- The bilinear form `L(t, x) = −(x · t)/(2π)` on `ℝⁿ`, chosen so that Mathlib's
`VectorFourier.fourierIntegral 𝐞` with `L` has kernel `e^{i x·t}`. -/
noncomputable def dotL (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  (-(2 * π)⁻¹) • ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

theorem dotL_apply (t x : Fin n → ℝ) : dotL n t x = -(2 * π)⁻¹ * ∑ i, t i * x i := by
  simp [dotL, smul_eq_mul]

/-- `(2π)^{n/2}`. -/
noncomputable def twoPiPow (n : ℕ) : ℂ := (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ)

theorem twoPiPow_ne_zero (n : ℕ) : twoPiPow n ≠ 0 :=
  ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'

/-- The DLMF Fourier transform, through Mathlib's vector Fourier integral. -/
noncomputable def fourierN (φ : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  (twoPiPow n)⁻¹ * VectorFourier.fourierIntegral 𝐞 volume (dotL n).toLinearMap₁₂ φ x

/-- DLMF 1.16.29: `𝓕φ(x) = (2π)^{−n/2} ∫_{ℝⁿ} φ(t) e^{i x·t} dt`. -/
theorem dlmf_1_16_29 (φ : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    fourierN φ x = (twoPiPow n)⁻¹ * ∫ t, φ t * cexp (I * ∑ i, (x i : ℂ) * t i) := by
  rw [fourierN, VectorFourier.fourierIntegral]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, dotL_apply, Circle.smul_def,
    Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  rw [Finset.sum_congr rfl fun i _ => mul_comm (t i : ℂ) (x i)]

/-! ### `𝓕` maps `𝓢(ℝⁿ, ℂ)` continuously to itself -/

theorem dotL_unitVec (i : Fin n) (x : Fin n → ℝ) : dotL n (unitVec i) x = -(2 * π)⁻¹ * x i := by
  rw [dotL_apply, Finset.sum_eq_single i (fun j _ hj => by simp [unitVec, hj])
    (by simp)]
  simp [unitVec]

/-- The finite sum of integrals appearing in Mathlib's estimate. -/
noncomputable def fourierT (f : 𝓢(Fin n → ℝ, ℂ)) (k m : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (m + 1),
    ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (⇑f) v‖

theorem fourierT_nonneg (f : 𝓢(Fin n → ℝ, ℂ)) (k m : ℕ) : 0 ≤ fourierT f k m :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => by positivity

theorem fourierT_mono (f : 𝓢(Fin n → ℝ, ℂ)) (k m : ℕ) : fourierT f k 0 ≤ fourierT f k m :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.product_subset_product le_rfl (Finset.range_subset_range.mpr (by omega)))
    fun _ _ _ => integral_nonneg fun _ => by positivity

theorem norm_pow_mul_iteratedFDeriv_fourierIntegral_le (f : 𝓢(Fin n → ℝ, ℂ)) (K k : ℕ)
    (x : Fin n → ℝ) :
    ‖x‖ ^ K * ‖iteratedFDeriv ℝ k
        (VectorFourier.fourierIntegral 𝐞 volume (dotL n).toLinearMap₁₂ ⇑f) x‖ ≤
      ((2 * π * ‖dotL n‖) ^ k + n * (2 * π) ^ K * (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K) *
        fourierT f k K := by
  set A := VectorFourier.fourierIntegral 𝐞 volume (dotL n).toLinearMap₁₂ ⇑f
  have hint : ∀ (k n : ℕ), k ≤ (⊤ : ℕ∞) → n ≤ (⊤ : ℕ∞) →
      Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) v‖) volume :=
    fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume f k n
  have hb : ∀ (m : ℕ) (v : Fin n → ℝ), |dotL n v x| ^ m * ‖iteratedFDeriv ℝ k A x‖ ≤
      ‖v‖ ^ m * (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ m * fourierT f k m := fun m v =>
    VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (dotL n) (f.smooth ⊤) hint
      le_top le_top v x
  have h0 : ‖iteratedFDeriv ℝ k A x‖ ≤ (2 * π * ‖dotL n‖) ^ k * fourierT f k K := by
    have := hb 0 0
    simp only [pow_zero, one_mul, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_left (fourierT_mono f k K) (by positivity))
  have hi : ∀ i, ‖x i‖ ^ K * ‖iteratedFDeriv ℝ k A x‖ ≤
      (2 * π) ^ K * (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K * fourierT f k K := fun i => by
    have h1 := hb K (unitVec i)
    rw [dotL_unitVec, abs_mul, abs_neg, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      mul_pow] at h1
    have h2 : ‖unitVec i‖ ^ K ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_unitVec_le i)
    have h3 : ‖x i‖ ^ K * ‖iteratedFDeriv ℝ k A x‖ =
        (2 * π) ^ K * (((2 * π)⁻¹ ^ K * |x i| ^ K) * ‖iteratedFDeriv ℝ k A x‖) := by
      rw [Real.norm_eq_abs, inv_pow]; field_simp
    rw [h3, mul_assoc ((2 * π) ^ K), mul_assoc ((2 * π) ^ K)]
    refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
    have : 0 ≤ (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K * fourierT f k K := by
      have := fourierT_nonneg f k K; positivity
    calc ‖unitVec i‖ ^ K * (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K * fourierT f k K
        = ‖unitVec i‖ ^ K * ((2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K * fourierT f k K) := by
          ring
      _ ≤ 1 * ((2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K * fourierT f k K) :=
          mul_le_mul_of_nonneg_right h2 this
      _ = _ := by ring
  calc ‖x‖ ^ K * ‖iteratedFDeriv ℝ k A x‖
      ≤ (1 + ∑ i, ‖x i‖ ^ K) * ‖iteratedFDeriv ℝ k A x‖ :=
        mul_le_mul_of_nonneg_right (norm_pow_le_one_add_sum x K) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k A x‖ + ∑ i, ‖x i‖ ^ K * ‖iteratedFDeriv ℝ k A x‖ := by
        rw [add_mul, one_mul, Finset.sum_mul]
    _ ≤ (2 * π * ‖dotL n‖) ^ k * fourierT f k K +
          ∑ _i : Fin n, (2 * π) ^ K * (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K *
            fourierT f k K := add_le_add h0 (Finset.sum_le_sum fun i _ => hi i)
    _ = _ := by simp; ring

theorem fourierT_le (k K : ℕ) : ∃ C, 0 ≤ C ∧ ∀ f : 𝓢(Fin n → ℝ, ℂ), fourierT f k K ≤
    C * (Finset.range (k + (volume : Measure (Fin n → ℝ)).integrablePower + 1) ×ˢ
      Finset.range (K + 1)).sup (schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ) f := by
  set P := (volume : Measure (Fin n → ℝ)).integrablePower
  set I := ∫ x : Fin n → ℝ, (1 + ‖x‖) ^ (-(P : ℝ))
  have hI : 0 ≤ I := integral_nonneg fun x => by positivity
  set s := Finset.range (k + 1) ×ˢ Finset.range (K + 1)
  refine ⟨s.card * (2 ^ P * I * 2), by positivity, fun f => ?_⟩
  set S := (Finset.range (k + P + 1) ×ˢ Finset.range (K + 1)).sup
    (schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ) f
  have hterm : ∀ p ∈ s, ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (⇑f) v‖ ≤
      2 ^ P * I * 2 * S := fun p hp => by
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    refine (f.integral_pow_mul_iteratedFDeriv_le ℂ volume p.1 p.2).trans ?_
    have h1 : SchwartzMap.seminorm ℂ 0 p.2 f ≤ S := by
      have := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ)
        (x := f) (show (0, p.2) ∈ Finset.range (k + P + 1) ×ˢ Finset.range (K + 1) by
          simp only [Finset.mem_product, Finset.mem_range]; omega)
      rwa [SchwartzMap.schwartzSeminormFamily_apply] at this
    have h2 : SchwartzMap.seminorm ℂ (p.1 + P) p.2 f ≤ S := by
      have := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ)
        (x := f) (show (p.1 + P, p.2) ∈ Finset.range (k + P + 1) ×ˢ Finset.range (K + 1) by
          simp only [Finset.mem_product, Finset.mem_range]; omega)
      rwa [SchwartzMap.schwartzSeminormFamily_apply] at this
    have : 0 ≤ 2 ^ P * I := by positivity
    nlinarith
  calc fourierT f k K ≤ s.card • (2 ^ P * I * 2 * S) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = _ := by rw [nsmul_eq_mul]; ring

/-- The Fourier integral `φ ↦ ∫ φ(t) e^{i x·t} dt` as a continuous linear map of `𝓢(ℝⁿ, ℂ)`. -/
noncomputable def fourierIntegralCLM (n : ℕ) : 𝓢(Fin n → ℝ, ℂ) →L[ℂ] 𝓢(Fin n → ℝ, ℂ) := by
  refine SchwartzMap.mkCLM (fun f => VectorFourier.fourierIntegral 𝐞 volume
    (dotL n).toLinearMap₁₂ ⇑f) ?_ ?_ ?_ ?_
  · intro f g x
    have := VectorFourier.fourierIntegral_add (μ := volume) (e := 𝐞) Real.continuous_fourierChar
      (L := (dotL n).toLinearMap₁₂) (dotL n).continuous₂ f.integrable g.integrable
    exact congrFun this x
  · intro a f x
    have := VectorFourier.fourierIntegral_const_smul 𝐞 volume (dotL n).toLinearMap₁₂ ⇑f a
    exact congrFun this x
  · intro f
    exact VectorFourier.contDiff_fourierIntegral (dotL n)
      fun k _ => SchwartzMap.integrable_pow_mul volume f k
  · rintro ⟨K, k⟩
    set P := (volume : Measure (Fin n → ℝ)).integrablePower
    set I := ∫ x : Fin n → ℝ, (1 + ‖x‖) ^ (-(P : ℝ))
    have hI : 0 ≤ I := integral_nonneg fun x => by positivity
    set c₁ := (2 * π * ‖dotL n‖) ^ k + n * (2 * π) ^ K * (2 * π * ‖dotL n‖) ^ k * (2 * k + 2) ^ K
    have hc₁ : 0 ≤ c₁ := by positivity
    obtain ⟨c₂, hc₂, hT⟩ := fourierT_le (n := n) k K
    refine ⟨Finset.range (k + P + 1) ×ˢ Finset.range (K + 1), c₁ * c₂, mul_nonneg hc₁ hc₂,
      fun f x => ?_⟩
    calc ‖x‖ ^ K * ‖iteratedFDeriv ℝ k
          (VectorFourier.fourierIntegral 𝐞 volume (dotL n).toLinearMap₁₂ ⇑f) x‖
        ≤ c₁ * fourierT f k K := norm_pow_mul_iteratedFDeriv_fourierIntegral_le f K k x
      _ ≤ c₁ * (c₂ * (Finset.range (k + P + 1) ×ˢ Finset.range (K + 1)).sup
            (schwartzSeminormFamily ℂ (Fin n → ℝ) ℂ) f) :=
          mul_le_mul_of_nonneg_left (hT f) hc₁
      _ = _ := by ring

/-! ### `𝓕` on `𝒯ₙ` -/

/-- The DLMF Fourier transform as a continuous linear map of `𝓢(ℝⁿ, ℂ)`. -/
noncomputable def fourierCLM (n : ℕ) : 𝓢(Fin n → ℝ, ℂ) →L[ℂ] 𝓢(Fin n → ℝ, ℂ) :=
  (twoPiPow n)⁻¹ • fourierIntegralCLM n

theorem coe_fourierCLM (f : 𝓢(Fin n → ℝ, ℂ)) : ⇑(fourierCLM n f) = fourierN ⇑f := by
  funext x
  simp only [fourierCLM, smul_apply, smul_eq_mul, fourierN]
  rfl

/-- DLMF §1.16(vii): `𝓕φ` is again in `𝒯ₙ`. -/
theorem isTempTestN_fourierN {φ : (Fin n → ℝ) → ℂ} (hφ : IsTempTestN φ) :
    IsTempTestN (fourierN φ) := by
  obtain ⟨f, rfl⟩ := isTempTestN_iff_schwartz.mp hφ
  exact isTempTestN_iff_schwartz.mpr ⟨fourierCLM n f, coe_fourierCLM f⟩

/-- The Fourier transform `𝒯ₙ → 𝒯ₙ`. -/
noncomputable def fourierTest (n : ℕ) : tempSpaceN n →ₗ[ℂ] tempSpaceN n :=
  (tempEquivN n).symm.toLinearMap ∘ₗ (fourierCLM n).toLinearMap ∘ₗ (tempEquivN n).toLinearMap

theorem coe_tempEquivN (φ : tempSpaceN n) : ⇑(tempEquivN n φ) = (φ : (Fin n → ℝ) → ℂ) :=
  (isTempTestN_iff_schwartz.mp φ.2).choose_spec

theorem coe_fourierTest (φ : tempSpaceN n) :
    (fourierTest n φ : (Fin n → ℝ) → ℂ) = fourierN φ := by
  change ⇑(fourierCLM n (tempEquivN n φ)) = _
  rw [coe_fourierCLM, coe_tempEquivN]

/-! ### Derivatives and multiplication by coordinates -/

theorem schwartz_integrable (φ : tempSpaceN n) : Integrable (φ : (Fin n → ℝ) → ℂ) := by
  rw [← coe_tempEquivN]; exact (tempEquivN n φ).integrable

theorem fourierN_smul (c : ℂ) (φ : (Fin n → ℝ) → ℂ) :
    fourierN (fun t => c * φ t) = fun x => c * fourierN φ x := by
  funext x
  have := congrFun (VectorFourier.fourierIntegral_const_smul 𝐞 volume
    (dotL n).toLinearMap₁₂ φ c) x
  simp only [fourierN, Pi.smul_apply, smul_eq_mul] at this ⊢
  rw [show (fun t => c * φ t) = c • φ from rfl, this]
  ring

/-- `𝓕(∂ⱼφ)(x) = −i xⱼ 𝓕φ(x)`. -/
theorem fourierN_partialDeriv (φ : tempSpaceN n) (j : Fin n) (x : Fin n → ℝ) :
    fourierN (partialDeriv j (φ : (Fin n → ℝ) → ℂ)) x =
      -I * (x j : ℂ) * fourierN (φ : (Fin n → ℝ) → ℂ) x := by
  set f := tempEquivN n φ
  have hf : (φ : (Fin n → ℝ) → ℂ) = ⇑f := (coe_tempEquivN φ).symm
  rw [hf]
  have hd : Integrable (fderiv ℝ ⇑f) := by
    have := (SchwartzMap.fderivCLM ℝ (Fin n → ℝ) ℂ f).integrable (μ := volume)
    exact this.congr (ae_of_all _ fun x => SchwartzMap.fderivCLM_apply ℝ f x)
  have h := VectorFourier.fourierIntegral_fderiv (dotL n) f.integrable
    (f.differentiable) hd
  have h2 := congrArg (fun G => G x (unitVec j)) h
  rw [Real.fourierIntegral_continuousLinearMap_apply' hd] at h2
  simp only [VectorFourier.fourierSMulRight, FunLike.coe_smul, Pi.smul_apply,
    neg_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply, dotL_unitVec, smul_eq_mul] at h2
  simp only [fourierN]
  rw [show partialDeriv j ⇑f = fun x => fderiv ℝ ⇑f x (unitVec j) from rfl, h2]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.real_smul]
  push_cast
  field_simp

theorem integrable_fourierSMulRight (f : 𝓢(Fin n → ℝ, ℂ)) :
    Integrable (VectorFourier.fourierSMulRight (dotL n) ⇑f) := by
  refine ((SchwartzMap.integrable_pow_mul (volume : Measure (Fin n → ℝ)) f 1).const_mul
    (2 * π * ‖dotL n‖)).mono'
    f.integrable.1.fourierSMulRight (ae_of_all _ fun v => ?_)
  refine (VectorFourier.norm_fourierSMulRight_le (dotL n) ⇑f v).trans (le_of_eq ?_)
  ring

/-- `∂ⱼ𝓕φ(x) = 𝓕(i tⱼ φ)(x)`. -/
theorem partialDeriv_fourierN (φ : tempSpaceN n) (j : Fin n) (x : Fin n → ℝ) :
    partialDeriv j (fourierN (φ : (Fin n → ℝ) → ℂ)) x =
      fourierN (fun t => I * (t j : ℂ) * (φ : (Fin n → ℝ) → ℂ) t) x := by
  set f := tempEquivN n φ
  have hf : (φ : (Fin n → ℝ) → ℂ) = ⇑f := (coe_tempEquivN φ).symm
  rw [hf]
  have h1 := (SchwartzMap.integrable_pow_mul (volume : Measure (Fin n → ℝ)) f 1)
  simp only [pow_one] at h1
  have hD := VectorFourier.hasFDerivAt_fourierIntegral (dotL n) f.integrable h1 x
  have hE : HasFDerivAt (fourierN ⇑f)
      ((twoPiPow n)⁻¹ • VectorFourier.fourierIntegral 𝐞 volume (dotL n).toLinearMap₁₂
        (VectorFourier.fourierSMulRight (dotL n) ⇑f) x) x := hD.const_mul _ |>.congr_fderiv
      (by ext v; simp [smul_eq_mul])
  simp only [partialDeriv]
  rw [hE.fderiv, smul_apply,
    Real.fourierIntegral_continuousLinearMap_apply' (integrable_fourierSMulRight f)]
  simp only [VectorFourier.fourierSMulRight, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, fourierN]
  congr 1
  congr 1
  funext t
  rw [show (dotL n) t (unitVec j) = -(2 * π)⁻¹ * t j by
    rw [dotL_apply, Finset.sum_eq_single j (fun i _ hi => by simp [unitVec, hi])
      (by simp)]
    simp [unitVec]]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.real_smul]
  push_cast
  field_simp

/-! ### The operators `Dⱼ = (1/i) ∂/∂xⱼ` and `xⱼ` on `𝒯ₙ` (1.16.30) -/

theorem isTempTestN_partialDeriv {φ : (Fin n → ℝ) → ℂ} (hφ : IsTempTestN φ) (j : Fin n) :
    IsTempTestN (partialDeriv j φ) := by
  refine ⟨contDiff_partialDeriv hφ.1 j, fun m k => ?_⟩
  obtain ⟨c, hc⟩ := hφ.2 m (fun i => (wordOf k ++ [j]).count i)
  exact ⟨c, fun x => by rw [mDeriv_partialDeriv hφ.1]; exact hc x⟩

theorem hasTemperateGrowth_coord (j : Fin n) :
    Function.HasTemperateGrowth fun t : Fin n → ℝ => ((t j : ℝ) : ℂ) :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).hasTemperateGrowth

theorem isTempTestN_coord_mul {φ : (Fin n → ℝ) → ℂ} (hφ : IsTempTestN φ) (j : Fin n) :
    IsTempTestN fun t => (t j : ℂ) * φ t := by
  obtain ⟨f, rfl⟩ := isTempTestN_iff_schwartz.mp hφ
  refine isTempTestN_iff_schwartz.mpr ⟨SchwartzMap.smulLeftCLM ℂ (fun t : Fin n → ℝ =>
    ((t j : ℝ) : ℂ)) f, ?_⟩
  funext t
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_coord j), smul_eq_mul]

theorem partialDeriv_add {φ ψ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (j : Fin n) : partialDeriv j (φ + ψ) = partialDeriv j φ + partialDeriv j ψ := by
  funext x
  simp only [partialDeriv, Pi.add_apply]
  rw [fderiv_add ((hφ.differentiable (by simp)) x) ((hψ.differentiable (by simp)) x)]
  rfl

theorem partialDeriv_smul {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (c : ℂ) (j : Fin n) :
    partialDeriv j (c • φ) = c • partialDeriv j φ := by
  funext x
  simp only [partialDeriv, Pi.smul_apply]
  rw [fderiv_const_smul ((hφ.differentiable (by simp)) x)]
  rfl

/-- `Dⱼ = (1/i) ∂/∂xⱼ` on `𝒯ₙ`. -/
noncomputable def DT (j : Fin n) : tempSpaceN n →ₗ[ℂ] tempSpaceN n where
  toFun φ := ⟨I⁻¹ • partialDeriv j φ, (tempSpaceN n).smul_mem _
    (isTempTestN_partialDeriv φ.2 j)⟩
  map_add' φ ψ := by
    ext x
    simp only [Submodule.coe_add, partialDeriv_add φ.2.1 ψ.2.1, Pi.smul_apply, Pi.add_apply,
      smul_add]
  map_smul' c φ := by
    ext x
    simp only [Submodule.coe_smul, partialDeriv_smul φ.2.1, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul]
    ring

/-- Multiplication by `xⱼ` on `𝒯ₙ`. -/
noncomputable def XT (j : Fin n) : tempSpaceN n →ₗ[ℂ] tempSpaceN n where
  toFun φ := ⟨fun t => (t j : ℂ) * (φ : (Fin n → ℝ) → ℂ) t, isTempTestN_coord_mul φ.2 j⟩
  map_add' φ ψ := by ext x; simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' c φ := by
    ext x; simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; ring

theorem coe_DT (j : Fin n) (φ : tempSpaceN n) :
    (DT j φ : (Fin n → ℝ) → ℂ) = I⁻¹ • partialDeriv j φ := rfl

theorem coe_XT (j : Fin n) (φ : tempSpaceN n) :
    (XT j φ : (Fin n → ℝ) → ℂ) = fun t => (t j : ℂ) * (φ : (Fin n → ℝ) → ℂ) t := rfl

/-- `𝓕(Dⱼφ) = −xⱼ 𝓕φ`. -/
theorem fourierTest_DT (j : Fin n) (φ : tempSpaceN n) :
    fourierTest n (DT j φ) = -XT j (fourierTest n φ) := by
  apply Subtype.ext
  funext x
  rw [coe_fourierTest, coe_DT, Submodule.coe_neg, coe_XT, coe_fourierTest]
  have := congrFun (fourierN_smul I⁻¹ (partialDeriv j (φ : (Fin n → ℝ) → ℂ))) x
  simp only [Pi.neg_apply]
  rw [show I⁻¹ • partialDeriv j (φ : (Fin n → ℝ) → ℂ) =
    fun t => I⁻¹ * partialDeriv j (φ : (Fin n → ℝ) → ℂ) t from rfl, this,
    fourierN_partialDeriv]
  field_simp

/-- `𝓕(xⱼφ) = Dⱼ𝓕φ`. -/
theorem fourierTest_XT (j : Fin n) (φ : tempSpaceN n) :
    fourierTest n (XT j φ) = DT j (fourierTest n φ) := by
  apply Subtype.ext
  funext x
  rw [coe_fourierTest, coe_DT, coe_fourierTest, coe_XT, Pi.smul_apply, partialDeriv_fourierN,
    smul_eq_mul]
  have := congrFun (fourierN_smul I fun t => (t j : ℂ) * (φ : (Fin n → ℝ) → ℂ) t) x
  rw [show (fun t => I * (t j : ℂ) * (φ : (Fin n → ℝ) → ℂ) t) =
    fun t => I * ((t j : ℂ) * (φ : (Fin n → ℝ) → ℂ) t) from funext fun t => by ring, this]
  field_simp

theorem DT_comm (i j : Fin n) (φ : tempSpaceN n) : DT i (DT j φ) = DT j (DT i φ) := by
  apply Subtype.ext
  simp only [coe_DT]
  rw [partialDeriv_smul (contDiff_partialDeriv φ.2.1 j), partialDeriv_smul
    (contDiff_partialDeriv φ.2.1 i), partialDeriv_comm φ.2.1]

/-! ### Words and polynomials (1.16.31–1.16.32) -/

/-- `D_{l₁} ⋯ D_{lᵣ}` along a word. -/
noncomputable def DW (l : List (Fin n)) : tempSpaceN n →ₗ[ℂ] tempSpaceN n :=
  l.foldr (fun j T => DT j ∘ₗ T) LinearMap.id

/-- `x_{l₁} ⋯ x_{lᵣ}` along a word. -/
noncomputable def XW (l : List (Fin n)) : tempSpaceN n →ₗ[ℂ] tempSpaceN n :=
  l.foldr (fun j T => XT j ∘ₗ T) LinearMap.id

theorem fourierTest_DW (l : List (Fin n)) (φ : tempSpaceN n) :
    fourierTest n (DW l φ) = (-1 : ℂ) ^ l.length • XW l (fourierTest n φ) := by
  induction l with
  | nil => simp [DW, XW]
  | cons j l ih =>
    simp only [DW, XW, List.foldr_cons, LinearMap.comp_apply] at ih ⊢
    rw [fourierTest_DT, ih, map_smul, List.length_cons, pow_succ, mul_comm, ← smul_smul,
      neg_one_smul]

theorem fourierTest_XW (l : List (Fin n)) (φ : tempSpaceN n) :
    fourierTest n (XW l φ) = DW l (fourierTest n φ) := by
  induction l with
  | nil => simp [DW, XW]
  | cons j l ih =>
    simp only [DW, XW, List.foldr_cons, LinearMap.comp_apply] at ih ⊢
    rw [fourierTest_XT, ih]

instance : LeftCommutative (fun (j : Fin n) (T : tempSpaceN n →ₗ[ℂ] tempSpaceN n) =>
    DT j ∘ₗ T) where
  left_comm i j T := LinearMap.ext fun φ => DT_comm i j (T φ)

theorem DW_perm {l₁ l₂ : List (Fin n)} (h : l₁.Perm l₂) : DW l₁ = DW l₂ := h.foldr_eq _

theorem coe_XW (l : List (Fin n)) (φ : tempSpaceN n) (x : Fin n → ℝ) :
    (XW l φ : (Fin n → ℝ) → ℂ) x = (l.map fun j => (x j : ℂ)).prod * (φ : (Fin n → ℝ) → ℂ) x := by
  induction l with
  | nil => simp [XW]
  | cons j l ih =>
    simp only [XW, List.foldr_cons, LinearMap.comp_apply] at ih ⊢
    rw [coe_XT]
    simp only [List.map_cons, List.prod_cons]
    rw [ih]; ring

theorem prod_flatMap_replicate (α : Fin n → ℕ) (g : Fin n → ℂ) (L : List (Fin n)) :
    ((L.flatMap fun i => List.replicate (α i) i).map g).prod = (L.map fun i => g i ^ α i).prod := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_replicate,
      List.prod_replicate, List.map_cons, List.prod_cons]

theorem prod_wordOf (α : Fin n → ℕ) (x : Fin n → ℝ) :
    ((wordOf α).map fun j => (x j : ℂ)).prod = monomialN α x := by
  rw [wordOf, prod_flatMap_replicate, monomialN, Fin.prod_univ_def]

theorem coe_DW (l : List (Fin n)) (φ : tempSpaceN n) :
    (DW l φ : (Fin n → ℝ) → ℂ) = (I⁻¹) ^ l.length • partialWord l φ := by
  induction l with
  | nil => simp [DW, partialWord]
  | cons j l ih =>
    simp only [DW, List.foldr_cons, LinearMap.comp_apply] at ih ⊢
    rw [coe_DT, ih, partialDeriv_smul (contDiff_partialWord φ.2.1 l), smul_smul,
      List.length_cons, pow_succ, mul_comm]
    rfl

/-- DLMF 1.16.31: `P(x) = ∑_α c_α x^α`, `α` ranging over a finite set `s` of multi-indices. -/
noncomputable def polyEvalN (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ α ∈ s, c α * monomialN α x

/-- Multiplication by `P` on `𝒯ₙ`. -/
noncomputable def PX (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    tempSpaceN n →ₗ[ℂ] tempSpaceN n :=
  ∑ α ∈ s, c α • XW (wordOf α)

/-- Multiplication by `P₋(x) = P(−x)` on `𝒯ₙ`. -/
noncomputable def PXneg (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    tempSpaceN n →ₗ[ℂ] tempSpaceN n :=
  ∑ α ∈ s, (c α * (-1) ^ (∑ i, α i)) • XW (wordOf α)

/-- DLMF 1.16.32: `P(D) = ∑_α c_α D^α`. -/
noncomputable def PD (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    tempSpaceN n →ₗ[ℂ] tempSpaceN n :=
  ∑ α ∈ s, c α • DW (wordOf α)

theorem coe_PX (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) (φ : tempSpaceN n)
    (x : Fin n → ℝ) :
    (PX s c φ : (Fin n → ℝ) → ℂ) x = polyEvalN s c x * (φ : (Fin n → ℝ) → ℂ) x := by
  simp only [PX, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, coe_XW, prod_wordOf,
    polyEvalN, Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem monomialN_neg (α : Fin n → ℕ) (x : Fin n → ℝ) :
    monomialN α (-x) = (-1) ^ (∑ i, α i) * monomialN α x := by
  rw [monomialN, monomialN, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.neg_apply, ofReal_neg, neg_pow]

theorem coe_PXneg (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) (φ : tempSpaceN n)
    (x : Fin n → ℝ) :
    (PXneg s c φ : (Fin n → ℝ) → ℂ) x = polyEvalN s c (-x) * (φ : (Fin n → ℝ) → ℂ) x := by
  simp only [PXneg, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, coe_XW, prod_wordOf,
    polyEvalN, Finset.sum_mul, monomialN_neg]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- `P(D)φ = ∑_α c_α (1/i)^{|α|} φ⁽ᵅ⁾`. -/
theorem coe_PD (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) (φ : tempSpaceN n)
    (x : Fin n → ℝ) : (PD s c φ : (Fin n → ℝ) → ℂ) x =
      ∑ α ∈ s, c α * ((I⁻¹) ^ (∑ i, α i) * mDeriv α (φ : (Fin n → ℝ) → ℂ) x) := by
  simp only [PD, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, coe_DW, length_wordOf]
  rfl

/-- DLMF 1.16.33: `𝓕(P(D)φ)(x) = P(−x) 𝓕φ(x)`. -/
theorem dlmf_1_16_33 (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) (φ : tempSpaceN n) :
    fourierTest n (PD s c φ) = PXneg s c (fourierTest n φ) ∧
      ∀ x, fourierN (PD s c φ : (Fin n → ℝ) → ℂ) x =
        polyEvalN s c (-x) * fourierN (φ : (Fin n → ℝ) → ℂ) x := by
  have h : fourierTest n (PD s c φ) = PXneg s c (fourierTest n φ) := by
    simp only [PD, PXneg, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, fourierTest_DW, length_wordOf, smul_smul]
  refine ⟨h, fun x => ?_⟩
  rw [← coe_fourierTest, h, coe_PXneg, coe_fourierTest]

/-- DLMF 1.16.34: `𝓕(Pφ)(x) = P(D)𝓕φ(x)`. -/
theorem dlmf_1_16_34 (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) (φ : tempSpaceN n) :
    fourierTest n (PX s c φ) = PD s c (fourierTest n φ) ∧
      ∀ x, fourierN (fun t => polyEvalN s c t * (φ : (Fin n → ℝ) → ℂ) t) x =
        (PD s c (fourierTest n φ) : (Fin n → ℝ) → ℂ) x := by
  have h : fourierTest n (PX s c φ) = PD s c (fourierTest n φ) := by
    simp only [PD, PX, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, fourierTest_XW]
  refine ⟨h, fun x => ?_⟩
  rw [← h, coe_fourierTest]
  congr 1
  funext t
  rw [coe_PX]

/-! ### Fourier transforms of tempered distributions (1.16.35–1.16.37) -/

/-- DLMF 1.16.35: `⟨𝓕(u), φ⟩ = ⟨u, 𝓕(φ)⟩`. -/
noncomputable def fourierDist (u : tempSpaceN n →ₗ[ℂ] ℂ) : tempSpaceN n →ₗ[ℂ] ℂ :=
  u ∘ₗ fourierTest n

theorem dlmf_1_16_35 (u : tempSpaceN n →ₗ[ℂ] ℂ) (φ : tempSpaceN n) :
    fourierDist u φ = u (fourierTest n φ) := rfl

/-- DLMF §1.16(vii): the Fourier transform of a tempered distribution is a tempered
distribution. -/
theorem isTempDistN_fourierDist {u : tempSpaceN n →ₗ[ℂ] ℂ} (hu : IsTempDistN u) :
    IsTempDistN (fourierDist u) := by
  unfold IsTempDistN at hu ⊢
  have e : ⇑(fourierDist u ∘ₗ (tempEquivN n).symm.toLinearMap) =
      ⇑(u ∘ₗ (tempEquivN n).symm.toLinearMap) ∘ ⇑(fourierCLM n) := by
    funext ψ
    simp [fourierDist, fourierTest]
  rw [e]
  exact hu.comp (fourierCLM n).continuous

/-- `⟨Dⱼu, φ⟩ = −⟨u, Dⱼφ⟩`, the derivative `(1/i)∂ⱼ` in the sense of distributions. -/
noncomputable def DD (j : Fin n) (u : tempSpaceN n →ₗ[ℂ] ℂ) : tempSpaceN n →ₗ[ℂ] ℂ :=
  -(u ∘ₗ DT j)

/-- `D^α u` along a word. -/
noncomputable def DDW (l : List (Fin n)) (u : tempSpaceN n →ₗ[ℂ] ℂ) : tempSpaceN n →ₗ[ℂ] ℂ :=
  l.foldr DD u

theorem DW_append (l₁ l₂ : List (Fin n)) : DW (l₁ ++ l₂) = DW l₁ ∘ₗ DW l₂ := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp only [DW, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih]; rfl

theorem DDW_apply (l : List (Fin n)) (u : tempSpaceN n →ₗ[ℂ] ℂ) (φ : tempSpaceN n) :
    DDW l u φ = (-1) ^ l.length * u (DW l φ) := by
  have key : ∀ φ, DDW l u φ = (-1) ^ l.length * u (DW l.reverse φ) := by
    induction l with
    | nil => intro φ; simp [DDW, DW]
    | cons j l ih =>
      intro φ
      simp only [DDW, List.foldr_cons] at ih ⊢
      rw [DD, LinearMap.neg_apply, LinearMap.comp_apply, ih, List.reverse_cons, DW_append,
        LinearMap.comp_apply, List.length_cons]
      have : DW [j] φ = DT j φ := rfl
      rw [this]
      ring
  rw [key, DW_perm (List.reverse_perm l)]

/-- `P(D)u = ∑_α c_α D^α u` in the sense of distributions. -/
noncomputable def PDD (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (u : tempSpaceN n →ₗ[ℂ] ℂ) : tempSpaceN n →ₗ[ℂ] ℂ :=
  ∑ α ∈ s, c α • DDW (wordOf α) u

/-- DLMF 1.16.36: `⟨𝓕(P(D)u), φ⟩ = ⟨P₋𝓕(u), φ⟩ = ⟨𝓕(u), P₋φ⟩`, where `⟨P₋𝓕(u), φ⟩` is
defined by 1.16.6 as `⟨𝓕(u), P₋φ⟩`. -/
theorem dlmf_1_16_36 (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (u : tempSpaceN n →ₗ[ℂ] ℂ) (φ : tempSpaceN n) :
    fourierDist (PDD s c u) φ = (fourierDist u ∘ₗ PXneg s c) φ ∧
      (fourierDist u ∘ₗ PXneg s c) φ = fourierDist u (PXneg s c φ) := by
  refine ⟨?_, rfl⟩
  simp only [fourierDist, PDD, PXneg, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, DDW_apply, ← fourierTest_XW, map_sum, map_smul, length_wordOf,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- DLMF 1.16.37: `⟨𝓕(Pu), φ⟩ = ⟨P(D)𝓕(u), φ⟩`, where `⟨Pu, φ⟩ = ⟨u, Pφ⟩` (1.16.6). -/
theorem dlmf_1_16_37 (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (u : tempSpaceN n →ₗ[ℂ] ℂ) (φ : tempSpaceN n) :
    fourierDist (u ∘ₗ PX s c) φ = PDD s c (fourierDist u) φ := by
  simp only [fourierDist, PDD, PX, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, DDW_apply, fourierTest_DW, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : ((-1 : ℂ) ^ (wordOf α).length) * (-1) ^ (wordOf α).length = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (-(u ((XW (wordOf α)) ((fourierTest n) φ)) * c α)) * h

end Azurite.DLMF
