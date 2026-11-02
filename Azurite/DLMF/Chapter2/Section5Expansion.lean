/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5Residues
import Azurite.DLMF.Chapter2.Section5Truncation

/-!
# DLMF §2.5(ii), 2.5.32–2.5.36: the expansion of `I_{jk}(x)` as `x → +∞`

* 2.5.32: `G_{jk}(z) = 𝓜f_j(1 − z) 𝓜h_k(z)` (`mellinG`).
* 2.5.33 (`dlmf_2_5_33`): for a real `p_{jk}` in `D_{jk}` at which the Parseval formula 2.5.5
  applies, `I_{jk}(x) = (2πi)⁻¹ ∫_{p−i∞}^{p+i∞} x^{−z} G_{jk}(z) dz`.
* 2.5.34–2.5.35 (`dlmf_2_5_35`): if `G_{jk}` continues to a function `G` analytic in a
  neighbourhood of the strip `p ≤ ℜz ≤ q` except for finitely many poles, with
  `sup_{p ≤ σ ≤ q} |G(σ + iy)| → 0` as `y → ±∞` (2.5.34) and `G` integrable on the two lines,
  then `I_{jk}(x) = ∑_{p<ℜz<q} res[−x^{−z} G(z)] + E_{jk}(x)` with
  `E_{jk}(x) = (2πi)⁻¹ ∫_{q−i∞}^{q+i∞} x^{−z} G(z) dz` (2.5.36). The horizontal integrals are
  bounded by `(q − p) max(x^{−p}, x^{−q}) sup|G|`, so 2.5.34 is exactly what is needed to shift
  the contour (`lineIntegral_shift`).
* 2.5.36 (`dlmf_2_5_36`): `E_{jk}(x) = o(x^{−q})` as `x → +∞`, by the Riemann–Lebesgue lemma:
  `x^{−(q+iy)} = x^{−q} e^{−iy ln x}`, so `E_{jk}(x) = x^{−q} (2π)^{−1/2} 𝓕[G(q + i·)](−ln x)`.
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 2.5.32**: `G_{jk}(z) = 𝓜f_j(1 − z) 𝓜h_k(z)`. -/
noncomputable def mellinG (fj hk : ℝ → ℂ) (z : ℂ) : ℂ := mellin fj (1 - z) * mellin hk z

/-- **DLMF 2.5.33**: for a real `p` in `D_{jk}` at which the Parseval formula applies,
`I_{jk}(x) = (2πi)⁻¹ ∫_{p−i∞}^{p+i∞} x^{−z} G_{jk}(z) dz`, written with `z = p + iy`. -/
theorem dlmf_2_5_33 {fj hk : ℝ → ℂ} {p : ℝ} (hf : MellinConvergent fj (1 - p))
    (hh : MellinConvergent hk p)
    (hint : VerticalIntegrable (mellin hk) p ∨ Integrable fun y : ℝ => mellin fj (1 - p - y * I))
    {x : ℝ} (hx : 0 < x) :
    mellinConvInt fj hk x = (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
      (x : ℂ) ^ (-((p : ℂ) + y * I)) * mellinG fj hk (p + y * I) := by
  rw [dlmf_2_5_5 hf hh hint hx]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mellinG, mul_assoc]

/-! ### Shifting the line of integration -/

theorem residue_neg (f : ℂ → ℂ) (s : ℂ) (R : ℝ) : residue (fun z => -f z) s R = -residue f s R := by
  have h := circleIntegral.integral_smul (-1 : ℂ) (fun z => f z / (z - s) ^ ((-1 : ℤ) + 1)) s
    (R / 2)
  simp only [neg_one_smul] at h
  simp only [residue, laurentCoeff, neg_div]
  rw [h]
  ring

/-- The residue theorem on `[p, q] × [−T, T]` for large `T`, then `T → ∞`: with `F` analytic on a
neighbourhood `U` of the strip `p ≤ ℜz ≤ q` except at the poles `S` inside the open strip,
horizontal integrals tending to `0` and `F` integrable on the two lines,
`∫_{ℜz=q} F = ∫_{ℜz=p} F + 2π ∑ res`. -/
theorem lineIntegral_shift {F : ℂ → ℂ} {p q : ℝ} (hpq : p < q) {U : Set ℂ} (hU : IsOpen U)
    (hstrip : {z : ℂ | z.re ∈ Icc p q} ⊆ U) {S : Finset ℂ} (hS : ∀ s ∈ S, p < s.re ∧ s.re < q)
    (hFd : DifferentiableOn ℂ F (U \ ↑S)) (R : ℂ → ℝ)
    (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ U ∧ ∀ t ∈ S, t ≠ s → R s ≤ dist t s)
    (htop : Tendsto (fun T : ℝ => ∫ σ in p..q, F (σ + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ σ in p..q, F (σ - T * I)) atTop (𝓝 0))
    (hFp : Integrable fun y : ℝ => F (p + y * I))
    (hFq : Integrable fun y : ℝ => F (q + y * I)) :
    (∫ y : ℝ, F (q + y * I)) = (∫ y : ℝ, F (p + y * I)) + 2 * π * ∑ s ∈ S, residue F s (R s) := by
  obtain ⟨M, hM⟩ := (S.finite_toSet.image fun s : ℂ => |s.im|).bddAbove
  have hM' : ∀ s ∈ S, |s.im| ≤ M := fun s hs => hM ⟨s, hs, rfl⟩
  have hrect : ∀ T : ℝ, max M 0 < T →
      rectBoundary F ⟨p, -T⟩ ⟨q, T⟩ = 2 * π * I * ∑ s ∈ S, residue F s (R s) := by
    intro T hT
    have hT0 : 0 < T := lt_of_le_of_lt (le_max_right _ _) hT
    have hTM : M < T := lt_of_le_of_lt (le_max_left _ _) hT
    refine rectBoundary_eq_sum_residues (p := ⟨p, -T⟩) (q := ⟨q, T⟩) hpq (by simp; linarith) hU
      (fun z hz => hstrip hz.1) (fun s hs => ⟨(hS s hs).1, (hS s hs).2, ?_, ?_⟩) hFd R hR
    · have := (abs_le.mp (hM' s hs)).1
      show -T < s.im
      linarith
    · have := (abs_le.mp (hM' s hs)).2
      show s.im < T
      linarith
  set Φ : ℝ → ℂ := fun T => rectBoundary F ⟨p, -T⟩ ⟨q, T⟩ with hΦ
  have h1 : Tendsto Φ atTop (𝓝 (2 * π * I * ∑ s ∈ S, residue F s (R s))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max M 0)] with T hT
    exact (hrect T hT).symm
  set Lq : ℂ := ∫ y : ℝ, F ((q : ℂ) + y * I) with hLq
  set Lp : ℂ := ∫ y : ℝ, F ((p : ℂ) + y * I) with hLp
  have hq : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F (q + y * I)) atTop (𝓝 Lq) :=
    intervalIntegral_tendsto_integral hFq tendsto_neg_atTop_atBot tendsto_id
  have hp : Tendsto (fun T : ℝ => ∫ y in (-T)..T, F (p + y * I)) atTop (𝓝 Lp) :=
    intervalIntegral_tendsto_integral hFp tendsto_neg_atTop_atBot tendsto_id
  have h2 : Tendsto Φ atTop (𝓝 (0 - 0 + I * Lq - I * Lp)) := by
    have := ((hbot.sub htop).add (hq.const_mul I)).sub (hp.const_mul I)
    refine this.congr' (Eventually.of_forall fun T => ?_)
    show _ = rectBoundary F ⟨p, -T⟩ ⟨q, T⟩
    rw [rectBoundary_strip]
  have hkey := tendsto_nhds_unique h1 h2
  have : I * Lq = I * (Lp + 2 * π * ∑ s ∈ S, residue F s (R s)) := by
    linear_combination -hkey
  exact mul_left_cancel₀ I_ne_zero this

/-- `|x^{−(σ+iy)}| = x^{−σ} ≤ max(x^{−p}, x^{−q})` for `p ≤ σ ≤ q`, `x > 0`. -/
theorem norm_cpow_neg_le_max {x : ℝ} (hx : 0 < x) {p q σ y : ℝ} (hσ : σ ∈ Icc p q) :
    ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ ≤ max (x ^ (-p)) (x ^ (-q)) := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]
  simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, ofReal_im,
    sub_self, add_zero]
  rcases le_total x 1 with h1 | h1
  · -- `x ≤ 1`: `x^{−σ}` is increasing in `σ`
    refine le_max_of_le_right ?_
    exact Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hσ.2])
  · refine le_max_of_le_left ?_
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hσ.1])

/-- **DLMF 2.5.34** gives the vanishing of the horizontal integrals of `x^{−z} G(z)`. -/
theorem tendsto_horizontal_of_sup {x : ℝ} (hx : 0 < x) {G : ℂ → ℂ} {p q : ℝ} (hpq : p ≤ q)
    (h34 : ∀ ε > 0, ∀ᶠ y : ℝ in cocompact ℝ, ∀ σ ∈ Icc p q, ‖G (σ + y * I)‖ ≤ ε)
    (l : Filter ℝ) (hl : l ≤ cocompact ℝ) :
    Tendsto (fun T : ℝ => ∫ σ in p..q, (x : ℂ) ^ (-((σ : ℂ) + T * I)) * G (σ + T * I)) l
      (𝓝 0) := by
  set C : ℝ := max (x ^ (-p)) (x ^ (-q)) * |q - p| with hC
  have hC0 : 0 ≤ C := mul_nonneg (le_max_of_le_left (Real.rpow_nonneg hx.le _)) (abs_nonneg _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (C + 1) := div_pos hε (by linarith)
  filter_upwards [hl (h34 _ hε')] with T hT
  rw [dist_zero_right]
  calc ‖∫ σ in p..q, (x : ℂ) ^ (-((σ : ℂ) + T * I)) * G (σ + T * I)‖
      ≤ max (x ^ (-p)) (x ^ (-q)) * (ε / (C + 1)) * |q - p| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
        have hσ' : σ ∈ Icc p q := Ioc_subset_Icc_self (by rwa [uIoc_of_le hpq] at hσ)
        rw [norm_mul]
        exact mul_le_mul (norm_cpow_neg_le_max hx hσ') (hT σ hσ') (norm_nonneg _)
          (le_max_of_le_left (Real.rpow_nonneg hx.le _))
    _ = C * (ε / (C + 1)) := by rw [hC]; ring
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

/-- **DLMF 2.5.35** (with 2.5.34 and 2.5.36): let `G` be analytic in a neighbourhood `U` of the
strip `p ≤ ℜz ≤ q` except for finitely many poles `S` in the open strip, equal to
`G_{jk}(z) = 𝓜f_j(1 − z) 𝓜h_k(z)` on `ℜz = p` (where the Parseval formula applies), with
`sup_{p ≤ σ ≤ q} |G(σ + iy)| → 0` as `y → ±∞` (2.5.34) and `G` integrable on the two lines. Then
`I_{jk}(x) = ∑_{p<ℜz<q} res[−x^{−z} G(z)] + E_{jk}(x)`,
`E_{jk}(x) = (2πi)⁻¹ ∫_{q−i∞}^{q+i∞} x^{−z} G(z) dz` (2.5.36). -/
theorem dlmf_2_5_35 {fj hk : ℝ → ℂ} {p q : ℝ} (hpq : p < q) (hf : MellinConvergent fj (1 - p))
    (hh : MellinConvergent hk p)
    (hint : VerticalIntegrable (mellin hk) p ∨ Integrable fun y : ℝ => mellin fj (1 - p - y * I))
    {x : ℝ} (hx : 0 < x) {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hstrip : {z : ℂ | z.re ∈ Icc p q} ⊆ U) {S : Finset ℂ} (hS : ∀ s ∈ S, p < s.re ∧ s.re < q)
    (hGd : DifferentiableOn ℂ G (U \ ↑S))
    (hGeq : ∀ y : ℝ, G (p + y * I) = mellinG fj hk (p + y * I))
    (h34 : ∀ ε > 0, ∀ᶠ y : ℝ in cocompact ℝ, ∀ σ ∈ Icc p q, ‖G (σ + y * I)‖ ≤ ε)
    (hGp : Integrable fun y : ℝ => G (p + y * I)) (hGq : Integrable fun y : ℝ => G (q + y * I))
    (R : ℂ → ℝ) (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ U ∧ ∀ t ∈ S, t ≠ s → R s ≤ dist t s) :
    mellinConvInt fj hk x =
      ∑ s ∈ S, residue (fun z => -((x : ℂ) ^ (-z) * G z)) s (R s) +
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((q : ℂ) + y * I)) * G (q + y * I) := by
  set F : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * G z with hF
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hFd : DifferentiableOn ℂ F (U \ ↑S) :=
    (differentiable_neg.const_cpow (Or.inl hx0)).differentiableOn.mul hGd
  -- integrability of `F` on the two lines: `x^{−z}` is bounded on each
  have hline : ∀ c : ℝ, (Integrable fun y : ℝ => G (c + y * I)) →
      Integrable fun y : ℝ => F (c + y * I) := fun c hc => by
    refine hc.bdd_mul (c := x ^ (-c)) ?_ (ae_of_all _ fun y => ?_)
    · exact (Continuous.const_cpow (by fun_prop) (Or.inl hx0)).aestronglyMeasurable
    · rw [norm_cpow_eq_rpow_re_of_pos hx]
      simp
  have hshift := lineIntegral_shift hpq hU hstrip hS hFd R hR
    (tendsto_horizontal_of_sup hx hpq.le h34 atTop atTop_le_cocompact)
    (by
      have := tendsto_horizontal_of_sup hx hpq.le h34 atBot atBot_le_cocompact
      have h' := this.comp tendsto_neg_atTop_atBot
      refine h'.congr' (Eventually.of_forall fun T => ?_)
      simp only [Function.comp, hF]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      rw [show ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) = σ - T * I by push_cast; ring])
    (hline p hGp) (hline q hGq)
  rw [dlmf_2_5_33 hf hh hint hx]
  have hres : ∀ s ∈ S, residue (fun z => -F z) s (R s) = -residue F s (R s) := fun s _ =>
    residue_neg F s (R s)
  rw [Finset.sum_congr rfl hres, Finset.sum_neg_distrib]
  have hp' : (∫ y : ℝ, (x : ℂ) ^ (-((p : ℂ) + y * I)) * mellinG fj hk (p + y * I)) =
      ∫ y : ℝ, F (p + y * I) :=
    integral_congr_ae (Eventually.of_forall fun y => by simp only [hF, hGeq])
  rw [hp']
  have hπ : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [hshift, mul_add, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
  ring

/-! ### 2.5.36: the error term -/

/-- `x^{−(q+iy)} = x^{−q} e^{−iy ln x}` for `x > 0`. -/
theorem cpow_neg_add_mul_I {x : ℝ} (hx : 0 < x) (q y : ℝ) :
    (x : ℂ) ^ (-((q : ℂ) + y * I)) =
      (x : ℂ) ^ (-(q : ℂ)) * cexp (I * ((-Real.log x : ℝ) : ℂ) * y) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0, ← exp_add, ← ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- **DLMF 2.5.36**: `E_{jk}(x) = (2πi)⁻¹ ∫_{q−i∞}^{q+i∞} x^{−z} G(z) dz = o(x^{−q})` as
`x → +∞`, by the Riemann–Lebesgue lemma (§1.14(i)). -/
theorem dlmf_2_5_36 (G : ℂ → ℂ) (q : ℝ) :
    IsLittleODLMF atTop
      (fun x : ℝ => (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((q : ℂ) + y * I)) * G (q + y * I))
      fun x : ℝ => (x : ℂ) ^ (-(q : ℂ)) := by
  unfold IsLittleODLMF
  have hRL : Tendsto (fun x : ℝ => (2 * π : ℂ)⁻¹ * (((√(2 * π) : ℝ) : ℂ) *
      dlmfFourier (fun y => G (q + y * I)) (-Real.log x))) atTop (𝓝 0) := by
    have := (dlmf_1_14_i_tendsto_zero fun y => G (q + y * I)).comp
      ((tendsto_neg_atTop_atBot.comp Real.tendsto_log_atTop).mono_right atBot_le_cocompact)
    simpa using (this.const_mul (((√(2 * π) : ℝ) : ℂ))).const_mul (2 * π : ℂ)⁻¹
  refine hRL.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hxq : (x : ℂ) ^ (-(q : ℂ)) ≠ 0 :=
    cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr hx.ne') _
  have hint : (∫ y : ℝ, (x : ℂ) ^ (-((q : ℂ) + y * I)) * G (q + y * I)) =
      (x : ℂ) ^ (-(q : ℂ)) * ∫ y : ℝ, G (q + y * I) * cexp (I * ((-Real.log x : ℝ) : ℂ) * y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [cpow_neg_add_mul_I hx]
    ring
  rw [hint, dlmfFourier, ← mul_assoc (((√(2 * π) : ℝ) : ℂ)), mul_inv_cancel₀ sqrt_two_pi_ne_zero,
    one_mul, mul_div_assoc, mul_div_cancel_left₀ _ hxq]

end Azurite.DLMF
