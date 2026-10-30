/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertExtension

/-!
# DLMF 1.14.45: duality and the theorem of M. Riesz and Pichorides

Duality (`denseBound_dual`) moves the dense bound from `q` to the conjugate exponent `p`. It
tests `Q₁ − Q₂` against `|ψ|^{p−2}ψ`, approximated in `L^q` by the dense class, and uses the
antisymmetry. With `A_p = tan(π/2p)` (`p ≤ 2`) or `cot(π/2p)` (`p ≥ 2`, `hilbertConstant`) this
proves **DLMF 1.14.45** (`dlmf_1_14_45`). DLMF prints the constant as `A_p`, where the integral
inequality needs `A_p^p`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real ENNReal

namespace Azurite.DLMF

/-- Pairing a dense-class difference with a single datum:
`|∫ (Q₁ − Q₂) P_e| ≤ A ‖P₁ − P₂‖_p ‖P_e‖_q`
when the dense bound holds at the conjugate exponent `q`. -/
theorem norm_integral_Q_mul_P_le {p q A : ℝ} (hpq : p.HolderConjugate q) (hDq : DenseBound q A)
    (d₁ d₂ e : DenseDatum) :
    ‖∫ x, (d₁.Q x - d₂.Q x) * e.P x‖ ≤
      (eLpNorm (fun x => d₁.P x - d₂.P x) (ENNReal.ofReal p) volume).toReal *
        (ENNReal.ofReal A * eLpNorm e.P (ENNReal.ofReal q) volume).toReal := by
  have hp1 := hpq.lt
  have hq1 := hpq.symm.lt
  have hanti : ∫ x, (d₁.Q x - d₂.Q x) * e.P x = -∫ x, (d₁.P x - d₂.P x) * e.Q x := by
    have i1 := (norm_integral_mul_le_holder hpq (d₁.memLp_Q hp1) (e.memLp_P hq1)).1
    have i2 := (norm_integral_mul_le_holder hpq (d₂.memLp_Q hp1) (e.memLp_P hq1)).1
    have i3 := (norm_integral_mul_le_holder hpq (d₁.memLp_P hp1) (e.memLp_Q hq1)).1
    have i4 := (norm_integral_mul_le_holder hpq (d₂.memLp_P hp1) (e.memLp_Q hq1)).1
    simp_rw [sub_mul]
    rw [integral_sub i1 i2, integral_sub i3 i4]
    have a1 := integral_conjPoisson_antisymm d₁.pos e.pos d₁.integrable e.integrable
    have a2 := integral_conjPoisson_antisymm d₂.pos e.pos d₂.integrable e.integrable
    simp only [DenseDatum.Q, DenseDatum.P] at a1 a2 ⊢
    rw [a1, a2]; ring
  rw [hanti, norm_neg]
  have hφ : MemLp (fun x => d₁.P x - d₂.P x) (ENNReal.ofReal p) :=
    (d₁.memLp_P hp1).sub (d₂.memLp_P hp1)
  refine (norm_integral_mul_le_holder hpq hφ (e.memLp_Q hq1)).2.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have h := hDq e DenseDatum.zero
  simp only [DenseDatum.zero_P, DenseDatum.zero_Q, Pi.zero_apply, sub_zero] at h
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (e.memLp_P hq1).eLpNorm_ne_top) h

/-- **Duality**: the dense bound at `q` gives the dense bound at the conjugate exponent `p`, with
the same constant (`‖ℋ‖_p = ‖ℋ‖_q`). Test `ψ = Q₁ − Q₂` against `k = |ψ|^{p−2} ψ ∈ L^q`,
approximated by `P_e`; by antisymmetry `∫ ψ P_e = −∫ (P₁ − P₂) Q_e`. -/
theorem denseBound_dual {p q A : ℝ} (hpq : p.HolderConjugate q) (hA : 0 ≤ A)
    (hDq : DenseBound q A) : DenseBound p A := by
  intro d₁ d₂
  have hp1 := hpq.lt
  have hq1 := hpq.symm.lt
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  set ψ : ℝ → ℂ := fun x => d₁.Q x - d₂.Q x with hψ
  set φ : ℝ → ℂ := fun x => d₁.P x - d₂.P x with hφ
  have hψm : MemLp ψ (ENNReal.ofReal p) := (d₁.memLp_Q hp1).sub (d₂.memLp_Q hp1)
  have hφm : MemLp φ (ENNReal.ofReal p) := (d₁.memLp_P hp1).sub (d₂.memLp_P hp1)
  set r : ℝ → ℝ := fun x => (ψ x).re with hr
  have hψr : ∀ x, ψ x = (r x : ℂ) := fun x => by
    simp only [hψ, hr]; rw [d₁.Q_real x, d₂.Q_real x]; simp
  have hnorm : ∀ x, ‖ψ x‖ = |r x| := fun x => by
    rw [hψr, Complex.norm_real, Real.norm_eq_abs]
  set I := ∫ x, ‖ψ x‖ ^ p with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  set N := (eLpNorm ψ (ENNReal.ofReal p) volume).toReal with hN
  set Φ := (eLpNorm φ (ENNReal.ofReal p) volume).toReal with hΦ
  have hNI : N = I ^ (1 / p) := eLpNorm_toReal_eq hp0 hψm
  -- the test function
  set kr : ℝ → ℝ := fun x => |r x| ^ (p - 2) * r x with hkr
  have hkn : ∀ x, |kr x| = |r x| ^ (p - 1) := fun x => by
    simp only [hkr]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rcases eq_or_ne (r x) 0 with h0 | h0
    · rw [h0, abs_zero, mul_zero, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
    · rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one (abs_pos.mpr h0).ne']
  have hkψ : ∀ x, ψ x * (kr x : ℂ) = ((‖ψ x‖ ^ p : ℝ) : ℂ) := fun x => by
    rw [hnorm, hψr, ← ofReal_mul]
    congr 1
    simp only [hkr]
    rcases eq_or_ne (r x) 0 with h0 | h0
    · rw [h0, abs_zero, Real.zero_rpow hp0.ne', mul_zero, zero_mul]
    · have ha : 0 < |r x| := abs_pos.mpr h0
      rw [← mul_assoc, mul_comm (r x), mul_assoc, ← sq, ← sq_abs, ← Real.rpow_natCast,
        ← Real.rpow_add ha]
      norm_num
  have hrm : AEStronglyMeasurable r volume :=
    Complex.continuous_re.comp_aestronglyMeasurable hψm.aestronglyMeasurable
  have hkrm : MemLp kr (ENNReal.ofReal q) := by
    have hm : AEStronglyMeasurable kr volume :=
      ((hrm.norm.aemeasurable.pow_const (p - 2)).aestronglyMeasurable.mul hrm).congr
        (ae_of_all _ fun x => by simp [hkr, Real.norm_eq_abs])
    refine (integrable_norm_rpow_iff hm (by simp [hq0]) ENNReal.ofReal_ne_top).mp ?_
    have hψi : Integrable fun x => ‖ψ x‖ ^ p := by
      have := (integrable_norm_rpow_iff hψm.aestronglyMeasurable (by simp [hp0])
        ENNReal.ofReal_ne_top).mpr hψm
      rwa [ENNReal.toReal_ofReal hp0.le] at this
    refine hψi.congr (ae_of_all _ fun x => ?_)
    simp only
    rw [ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs, hkn, hnorm,
      ← Real.rpow_mul (abs_nonneg _), hpq.sub_one_mul_conj]
  set kC : ℝ → ℂ := fun x => (kr x : ℂ) with hkC
  have hkCm : MemLp kC (ENNReal.ofReal q) := hkrm.ofReal
  have hkCnorm : (eLpNorm kC (ENNReal.ofReal q) volume).toReal = I ^ (1 / q) := by
    rw [eLpNorm_toReal_eq hq0 hkCm]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hkC]
    rw [Complex.norm_real, Real.norm_eq_abs, hkn, hnorm, ← Real.rpow_mul (abs_nonneg _),
      hpq.sub_one_mul_conj]
  have hψk : ∫ x, ψ x * kC x = (I : ℂ) := by
    simp only [hkC]
    simp_rw [hkψ]
    rw [integral_complex_ofReal]
  -- approximate `k` by the dense class at exponent `q`
  have happrox : ∀ m : ℕ, ∃ e : DenseDatum,
      eLpNorm (fun x => kC x - e.P x) (ENNReal.ofReal q) volume <
        ENNReal.ofReal ((1 / 2) ^ m) := fun m => by
    obtain ⟨g, hgc, hgs, b, hb, -, hlt⟩ := exists_poissonInt_approx
      (ENNReal.one_le_ofReal.mpr hq1.le) ENNReal.ofReal_ne_top hkrm (ε := (1 / 2) ^ m)
      (by positivity)
    exact ⟨⟨g, b, hgc, hgs, hb⟩, hlt⟩
  choose e he using happrox
  have hgeom : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    rwa [ENNReal.ofReal_zero] at this
  have hdlim : Tendsto (fun m => eLpNorm ((e m).P - kC) (ENNReal.ofReal q) volume) atTop
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom (fun n => zero_le)
      fun n => by rw [eLpNorm_sub_comm]; exact (he n).le
  have lim1 := tendsto_integral_mul_of_eLpNorm hpq.symm hψm (fun m => (e m).memLp_P hq1)
    hkCm hdlim
  have hδ : Tendsto (fun m => (eLpNorm ((e m).P - kC) (ENNReal.ofReal q) volume).toReal) atTop
      (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdlim
    rwa [ENNReal.toReal_zero] at this
  have hbound : ∀ m, ‖∫ x, ψ x * (e m).P x‖ ≤
      Φ * (A * (I ^ (1 / q) + (eLpNorm ((e m).P - kC) (ENNReal.ofReal q) volume).toReal)) :=
    fun m => by
      have h1 := norm_integral_Q_mul_P_le hpq hDq d₁ d₂ (e m)
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
      refine mul_le_mul_of_nonneg_left ?_ hA
      have htri : eLpNorm (e m).P (ENNReal.ofReal q) volume ≤
          eLpNorm kC (ENNReal.ofReal q) volume +
            eLpNorm ((e m).P - kC) (ENNReal.ofReal q) volume := by
        have : (e m).P = kC + ((e m).P - kC) := by abel
        conv_lhs => rw [this]
        exact eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq1.le)
      rw [← hkCnorm, ← ENNReal.toReal_add hkCm.eLpNorm_ne_top
        (((e m).memLp_P hq1).sub hkCm).eLpNorm_ne_top]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hkCm.eLpNorm_ne_top,
        (((e m).memLp_P hq1).sub hkCm).eLpNorm_ne_top⟩) htri
  have hlimb : Tendsto (fun m => Φ * (A * (I ^ (1 / q) +
      (eLpNorm ((e m).P - kC) (ENNReal.ofReal q) volume).toReal))) atTop
      (𝓝 (Φ * (A * (I ^ (1 / q) + 0)))) :=
    ((tendsto_const_nhds.add hδ).const_mul A).const_mul Φ
  have hIle : I ≤ Φ * A * I ^ (1 / q) := by
    have := le_of_tendsto_of_tendsto' lim1.norm hlimb hbound
    rw [hψk, Complex.norm_real, Real.norm_of_nonneg hI0, add_zero] at this
    linarith
  -- conclude `N ≤ A Φ`
  have hNle : N ≤ A * Φ := by
    rcases hI0.lt_or_eq with hIpos | hI0'
    · have hsum : I ^ (1 / p) * I ^ (1 / q) = I := by
        rw [← Real.rpow_add hIpos, one_div, one_div, hpq.inv_add_inv_eq_one, Real.rpow_one]
      have hq' : 0 < I ^ (1 / q) := Real.rpow_pos_of_pos hIpos _
      rw [hNI]
      have : I ^ (1 / p) * I ^ (1 / q) ≤ (A * Φ) * I ^ (1 / q) := by
        rw [hsum]; linarith
      exact le_of_mul_le_mul_right this hq'
    · rw [hNI, ← hI0', Real.zero_rpow (by positivity)]
      exact mul_nonneg hA ENNReal.toReal_nonneg
  calc eLpNorm (fun x => d₁.Q x - d₂.Q x) (ENNReal.ofReal p) volume = ENNReal.ofReal N := by
        rw [hN, ENNReal.ofReal_toReal hψm.eLpNorm_ne_top]
    _ ≤ ENNReal.ofReal (A * Φ) := ENNReal.ofReal_le_ofReal hNle
    _ = ENNReal.ofReal A * eLpNorm (fun x => d₁.P x - d₂.P x) (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_mul hA, hΦ, ENNReal.ofReal_toReal hφm.eLpNorm_ne_top]

/-! ### DLMF 1.14.45 -/

/-- DLMF's `A_p`: `tan(π/2p)` for `1 < p ≤ 2` and `cot(π/2p)` for `p ≥ 2` (Pichorides' sharp norm of
`ℋ` on `L^p`). -/
noncomputable def hilbertConstant (p : ℝ) : ℝ :=
  if p ≤ 2 then Real.tan (π / (2 * p)) else (Real.tan (π / (2 * p)))⁻¹

theorem hilbertConstant_nonneg {p : ℝ} (hp1 : 1 < p) : 0 ≤ hilbertConstant p := by
  have h := (pichoridesA_pos hp1).le
  rw [pichoridesA] at h
  unfold hilbertConstant
  split_ifs
  · exact h
  · exact inv_nonneg.mpr h

theorem denseBound_hilbertConstant {p : ℝ} (hp1 : 1 < p) : DenseBound p (hilbertConstant p) := by
  unfold hilbertConstant
  split_ifs with hp2
  · exact denseBound_of_le_two hp1 hp2
  · push Not at hp2
    have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
    set q := p.conjExponent with hq
    have hq1 : 1 < q := hpq.symm.lt
    have hqdef : q = p / (p - 1) := rfl
    have hq2 : q ≤ 2 := by
      rw [hqdef, div_le_iff₀ (by linarith)]; linarith
    have htan : Real.tan (π / (2 * q)) = (Real.tan (π / (2 * p)))⁻¹ := by
      rw [← Real.tan_pi_div_two_sub]
      congr 1
      rw [hqdef]
      field_simp
    have := denseBound_dual hpq (pichoridesA_pos hq1).le (denseBound_of_le_two hq1 hq2)
    rwa [pichoridesA, htan] at this

/-- **DLMF 1.14.45** (M. Riesz; sharp constant by Pichorides). If `f` is real and `|f(t)|^p`,
`p > 1`, is integrable on `(−∞, ∞)`, then `ℋf(x)` (1.14.41) exists for almost every `x`,
`|ℋf(x)|^p` is integrable, and `∫ |ℋf(x)|^p dx ≤ A_p^p ∫ |f(t)|^p dt` with
`A_p = tan(π/2p)` for `1 < p ≤ 2` and `cot(π/2p)` for `p ≥ 2`.

DLMF prints the constant as `A_p`; the inequality between integrals needs `A_p^p`, since `A_p`
is the operator norm `‖ℋ‖_{L^p → L^p}` (Pichorides 1972), and it is sharp. -/
theorem dlmf_1_14_45 {p : ℝ} (hp1 : 1 < p) {f : ℝ → ℝ} (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable fun t => |f t| ^ p) :
    (∀ᵐ x, ∃ L, HasHilbert (fun t => (f t : ℂ)) x L) ∧
      Integrable (fun x => ‖hilbert (fun t => (f t : ℂ)) x‖ ^ p) ∧
      ∫ x, ‖hilbert (fun t => (f t : ℂ)) x‖ ^ p ≤ hilbertConstant p ^ p * ∫ t, |f t| ^ p := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hfL : MemLp f (ENNReal.ofReal p) volume := by
    refine (integrable_norm_rpow_iff hfm hP0 ENNReal.ofReal_ne_top).mp ?_
    simpa [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hf
  obtain ⟨hae, hH, hle⟩ := hilbert_Lp_of_denseBound hp1 (hilbertConstant_nonneg hp1)
    (denseBound_hilbertConstant hp1) hfL
  set H := hilbert fun t => (f t : ℂ)
  have hHi : Integrable fun x => ‖H x‖ ^ p := by
    have := (integrable_norm_rpow_iff hH.aestronglyMeasurable hP0 ENNReal.ofReal_ne_top).mpr hH
    rwa [ENNReal.toReal_ofReal hp0.le] at this
  refine ⟨hae.mono fun x hx => ⟨_, hx⟩, hHi, ?_⟩
  set A := hilbertConstant p
  have hA := hilbertConstant_nonneg hp1
  rw [hH.eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top,
    hfL.eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le,
    ← ENNReal.ofReal_mul hA] at hle
  have hIf : 0 ≤ ∫ t, ‖f t‖ ^ p := integral_nonneg fun t => Real.rpow_nonneg (norm_nonneg _) _
  have hIH : 0 ≤ ∫ x, ‖H x‖ ^ p := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have h1 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have h2 := Real.rpow_le_rpow (by positivity) h1 hp0.le
  rw [← Real.rpow_mul hIH, inv_mul_cancel₀ hp0.ne', Real.rpow_one,
    Real.mul_rpow hA (by positivity), ← Real.rpow_mul hIf, inv_mul_cancel₀ hp0.ne',
    Real.rpow_one] at h2
  simpa [Real.norm_eq_abs] using h2

end Azurite.DLMF
