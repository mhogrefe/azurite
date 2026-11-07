/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section25Arcsin
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# DLMF 4.25.5 and 4.25.2

* `dlmf_4_25_5`: `e^{2a arccot z} = 1 + 2a/(z − a + (a² + 1)/(3z + (a² + 4)/(5z + ⋯)))` for every
  complex `a` and `z ∉ [−i, i]` (Figure 4.23.1(iv)).
* `dlmf_4_25_2`: `tan(az) = a tan z/(1 + (1 − a²)tan²z/(3 + (4 − a²)tan²z/(5 + ⋯)))` for complex
  `a`, `|ℜz| < ½π`, `az ≠ ±½π, ±(3/2)π, …`.

Method for 4.25.5 (Darboux): with `τ` the root of `1 − 2zτ − τ² = 0` with `|τ| < 1` (`expTau`),
the functions `G_ε = e^{εa(ψ(t) − ψ(0))}p^{−1/2}` (`expG`, `ε = ±1`; `p = 1 − 2zt − t²`,
`ψ′ = −p^{−1/2}`) satisfy an ODE whose Taylor recurrence is that of `Bᵣ` (`ε = 1`) and `Aᵣ`
(`ε = −1`) (`iteratedDeriv_expG_eq`). Both have the form
`(1 − t/τ)^{−1/2} k(t) + m(t)` with `k`, `m` analytic on `|t| < 1/|τ|` (`expG_decomp`), so
`G^{(r)}(0) τʳ/(r! cᵣ) → k(τ)` (`darboux_limit`), whence `Aᵣ/Bᵣ → e^{2aκ(0)}` with
`κ(0) = 2 arctan τ = arccot z` (`arctanInt_eq`, `two_mul_arctanD_expTau`).

4.25.2 is the Möbius image of 4.25.5 at `a ↦ ia`, `z ↦ cot z`, convergent by convergent
(`tanA_cf_eq`: `2i wʳPᵣ = Aᵣ − Bᵣ`, `2wʳQᵣ = Aᵣ + Bᵣ`, `w = cot z`).
-/

open Set Filter Topology Complex MeasureTheory Finset
open scoped Real Nat Interval

namespace Azurite.DLMF

/-! ### The root `τ` -/

/-- The two roots of `T² + 2zT − 1 = 0` have modulus `≠ 1` unless `z ∈ [−i, i]`. -/
theorem norm_ne_one_of_root {z T : ℂ} (hz : ∀ y : ℝ, |y| ≤ 1 → z ≠ I * y)
    (hT : T ^ 2 + 2 * z * T - 1 = 0) : ‖T‖ ≠ 1 := by
  intro h1
  have hT0 : T ≠ 0 := by rintro rfl; norm_num at hT
  have hconj : (starRingEnd ℂ) T = T⁻¹ := by
    have : T * (starRingEnd ℂ) T = 1 := by
      rw [mul_conj, normSq_eq_norm_sq, h1]; norm_num
    field_simp; linear_combination this
  have hzT : z = ((starRingEnd ℂ) T - T) / 2 := by
    rw [hconj]; field_simp; linear_combination hT
  have hzI : z = I * ((-T.im : ℝ) : ℂ) := by
    push_cast
    rw [hzT]; apply Complex.ext <;> simp; ring
  refine hz (-T.im) ?_ hzI
  rw [abs_neg]; exact (abs_im_le_norm T).trans h1.le

/-- `τ`: the root of `1 − 2zτ − τ² = 0` inside the unit disc. -/
noncomputable def expTau (z : ℂ) : ℂ :=
  if ‖-z + (z ^ 2 + 1) ^ (1 / 2 : ℂ)‖ < 1 then -z + (z ^ 2 + 1) ^ (1 / 2 : ℂ)
  else -z - (z ^ 2 + 1) ^ (1 / 2 : ℂ)

theorem expTau_spec {z : ℂ} (hz : ∀ y : ℝ, |y| ≤ 1 → z ≠ I * y) :
    1 - 2 * z * expTau z - expTau z ^ 2 = 0 ∧ ‖expTau z‖ < 1 ∧ expTau z ≠ 0 := by
  set s := (z ^ 2 + 1) ^ (1 / 2 : ℂ) with hs
  have hs2 : s ^ 2 = z ^ 2 + 1 := by rw [hs, one_div (2 : ℂ), cpow_ofNat_inv_pow]
  have h1 : (-z + s) ^ 2 + 2 * z * (-z + s) - 1 = 0 := by linear_combination hs2
  have h2 : (-z - s) ^ 2 + 2 * z * (-z - s) - 1 = 0 := by linear_combination hs2
  have hprod : (-z + s) * (-z - s) = -1 := by linear_combination -hs2
  have key : ∀ T : ℂ, T ^ 2 + 2 * z * T - 1 = 0 → ‖T‖ < 1 →
      1 - 2 * z * T - T ^ 2 = 0 ∧ ‖T‖ < 1 ∧ T ≠ 0 := fun T hT hT1 =>
    ⟨by linear_combination -hT, hT1, by rintro rfl; norm_num at hT⟩
  unfold expTau
  rw [← hs]
  split_ifs with h
  · exact key _ h1 h
  · refine key _ h2 ?_
    push Not at h
    have hne := norm_ne_one_of_root hz h1
    have hgt : 1 < ‖-z + s‖ := lt_of_le_of_ne h (Ne.symm hne)
    have := congrArg norm hprod
    rw [norm_mul, norm_neg, norm_one] at this
    nlinarith [norm_nonneg (-z - s)]

/-! ### The continued fraction -/

/-- `a₁ = 2a`, `aᵣ = a² + (r − 1)²`. -/
noncomputable def expCFa (a : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then 2 * a else a ^ 2 + ((r - 1 : ℕ) : ℂ) ^ 2

/-- `b₀ = 1`, `b₁ = z − a`, `bᵣ = (2r − 1) z`. -/
noncomputable def expCFb (a z : ℂ) (r : ℕ) : ℂ :=
  if r = 0 then 1 else if r = 1 then z - a else (2 * (r : ℂ) - 1) * z

theorem expCF_rec (a z : ℂ) (r : ℕ) :
    cfB (expCFa a) (expCFb a z) (r + 2) =
        (2 * (r : ℂ) + 3) * z * cfB (expCFa a) (expCFb a z) (r + 1) +
        (a ^ 2 + ((r : ℂ) + 1) ^ 2) * cfB (expCFa a) (expCFb a z) r ∧
      cfA (expCFa a) (expCFb a z) (r + 2) =
        (2 * (r : ℂ) + 3) * z * cfA (expCFa a) (expCFb a z) (r + 1) +
          (a ^ 2 + ((r : ℂ) + 1) ^ 2) * cfA (expCFa a) (expCFb a z) r := by
  have ha : expCFa a (r + 2) = a ^ 2 + ((r : ℂ) + 1) ^ 2 := by
    simp only [expCFa, show r + 2 ≠ 1 by omega, ↓reduceIte, show r + 2 - 1 = r + 1 by omega]
    push_cast; ring
  have hb : expCFb a z (r + 2) = (2 * (r : ℂ) + 3) * z := by
    simp only [expCFb, show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega, ↓reduceIte]
    push_cast; ring
  rw [cfB_succ_succ, cfA_succ_succ, ha, hb]
  exact ⟨rfl, rfl⟩

theorem expCF_init (a z : ℂ) :
    cfB (expCFa a) (expCFb a z) 0 = 1 ∧ cfB (expCFa a) (expCFb a z) 1 = z - a ∧
      cfA (expCFa a) (expCFb a z) 0 = 1 ∧ cfA (expCFa a) (expCFb a z) 1 = z + a := by
  simp [cfA, cfB, cfP, cfQ, expCFa, expCFb]
  ring

/-! ### Integrals of `(A(σ) + B(σ) t)^{−1/2}` -/

theorem norm_cpow_real_exp {x : ℂ} (hx : x ≠ 0) (e : ℝ) : ‖x ^ (e : ℂ)‖ = ‖x‖ ^ e := by
  rw [norm_cpow_of_ne_zero hx]; simp

theorem norm_cpow_le_of_re_ge {x : ℂ} {δ e : ℝ} (hδ : 0 < δ) (hx : δ ≤ x.re) (he : e ≤ 0) :
    ‖x ^ (e : ℂ)‖ ≤ δ ^ e := by
  have hx0 : x ≠ 0 := fun h => by rw [h, zero_re] at hx; linarith
  rw [norm_cpow_real_exp hx0]
  exact Real.rpow_le_rpow_of_nonpos hδ (hx.trans (re_le_norm x)) he

theorem mem_slitPlane_of_pos_re {x : ℂ} (hx : 0 < x.re) : x ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl hx)

/-- Differentiation of `t ↦ ∫₀¹ (A(σ) + B(σ) t)^{−1/2} dσ` where `ℜ(A + B t) ≥ δ > 0`. -/
theorem hasDerivAt_integral_rsqrt {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B)
    {t₀ : ℂ} {ε δ MB : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hre : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Metric.ball t₀ ε, δ ≤ (A σ + B σ * t).re)
    (hMB : ∀ σ ∈ Icc (0 : ℝ) 1, ‖B σ‖ ≤ MB) :
    HasDerivAt (fun t => ∫ σ in (0 : ℝ)..1, (A σ + B σ * t) ^ ((-1 / 2 : ℝ) : ℂ))
      (∫ σ in (0 : ℝ)..1, (-(1 / 2) : ℂ) * (A σ + B σ * t₀) ^ ((-3 / 2 : ℝ) : ℂ) * B σ) t₀ := by
  have hsub : ∀ σ ∈ Ι (0 : ℝ) 1, σ ∈ Icc (0 : ℝ) 1 := fun σ hσ => by
    rw [uIoc_of_le zero_le_one] at hσ; exact ⟨hσ.1.le, hσ.2⟩
  have hslit : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Metric.ball t₀ ε, A σ + B σ * t ∈ slitPlane :=
    fun σ hσ t ht => mem_slitPlane_of_pos_re (by linarith [hre σ hσ t ht])
  have hcont : ∀ t ∈ Metric.ball t₀ ε, ∀ e : ℂ,
      ContinuousOn (fun σ : ℝ => (A σ + B σ * t) ^ e) (Icc 0 1) := fun t ht e =>
    ContinuousOn.cpow_const (by fun_prop) fun σ hσ => hslit σ hσ t ht
  have h0 := Metric.mem_ball_self hε (x := t₀)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun t σ => (A σ + B σ * t) ^ ((-1 / 2 : ℝ) : ℂ))
    (F' := fun t σ => (-(1 / 2) : ℂ) * (A σ + B σ * t) ^ ((-3 / 2 : ℝ) : ℂ) * B σ)
    (x₀ := t₀) (bound := fun _ => 1 / 2 * δ ^ (-3 / 2 : ℝ) * MB) (Metric.ball_mem_nhds t₀ hε)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds t₀ hε) fun t ht =>
      ((hcont t ht _).mono fun σ hσ => hsub σ hσ).aestronglyMeasurable measurableSet_uIoc)
    ((hcont t₀ h0 _).intervalIntegrable_of_Icc zero_le_one)
    ((((continuousOn_const.mul (hcont t₀ h0 _)).mul hB.continuousOn).mono
      fun σ hσ => hsub σ hσ).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun σ hσ t ht => by
      have hσ' := hsub σ hσ
      rw [norm_mul, norm_mul, show ‖(-(1 / 2) : ℂ)‖ = 1 / 2 by norm_num]
      have h1 := norm_cpow_le_of_re_ge hδ (hre σ hσ' t ht) (by norm_num : (-3 / 2 : ℝ) ≤ 0)
      have h2 := hMB σ hσ'
      gcongr)
    intervalIntegrable_const
    (Eventually.of_forall fun σ hσ t ht => by
      have hσ' := hsub σ hσ
      have hd := (((hasDerivAt_id t).const_mul (B σ)).const_add (A σ)).cpow_const
        (c := ((-1 / 2 : ℝ) : ℂ)) (hslit σ hσ' t ht)
      convert hd using 1
      · rfl
      · rw [show ((-1 / 2 : ℝ) : ℂ) - 1 = ((-3 / 2 : ℝ) : ℂ) by push_cast; norm_num]
        simp only [id_eq]
        push_cast; ring)
  exact h.2

/-! ### `κ` -/

/-- The radicand `D(σ, t) = 1 + τ²(1 − σ²) + σ²τt`. -/
noncomputable def expD (τ : ℂ) (σ : ℝ) (t : ℂ) : ℂ :=
  1 + τ ^ 2 * (1 - (σ : ℂ) ^ 2) + (σ : ℂ) ^ 2 * τ * t

theorem expD_re_ge {τ t : ℂ} {ρ : ℝ} (ht : ‖t‖ ≤ ρ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    1 - max (‖τ‖ ^ 2) (‖τ‖ * ρ) ≤ (expD τ σ t).re := by
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hσ1 : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
  set M := max (‖τ‖ ^ 2) (‖τ‖ * ρ)
  have hn : ‖τ ^ 2 * (1 - (σ : ℂ) ^ 2) + (σ : ℂ) ^ 2 * τ * t‖ ≤ M := by
    have e1 : (1 - (σ : ℂ) ^ 2) = ((1 - σ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (σ : ℂ) ^ 2 = ((σ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), abs_of_nonneg hσ2, norm_pow]
    have h1 : ‖τ‖ ^ 2 ≤ M := le_max_left _ _
    have h2 : ‖τ‖ * ‖t‖ ≤ M :=
      (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans (le_max_right _ _)
    nlinarith
  have := re_le_norm (τ ^ 2 * (1 - (σ : ℂ) ^ 2) + (σ : ℂ) ^ 2 * τ * t)
  have he : expD τ σ t = 1 + (τ ^ 2 * (1 - (σ : ℂ) ^ 2) + (σ : ℂ) ^ 2 * τ * t) := by
    unfold expD; ring
  rw [he, add_re, one_re]
  have := neg_le_of_abs_le
    ((abs_re_le_norm (τ ^ 2 * (1 - (σ : ℂ) ^ 2) + (σ : ℂ) ^ 2 * τ * t)).trans hn)
  linarith

/-- `κ(t) = 2τ ∫₀¹ D(σ, t)^{−1/2} dσ`. -/
noncomputable def expKappa (τ t : ℂ) : ℂ :=
  2 * τ * ∫ σ in (0 : ℝ)..1, expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ)

theorem hasDerivAt_expKappa {τ t₀ : ℂ} (hτ : ‖τ‖ < 1) (ht₀ : ‖t₀‖ * ‖τ‖ < 1) :
    HasDerivAt (expKappa τ) (2 * τ * ∫ σ in (0 : ℝ)..1,
      (-(1 / 2) : ℂ) * expD τ σ t₀ ^ ((-3 / 2 : ℝ) : ℂ) * ((σ : ℂ) ^ 2 * τ)) t₀ := by
  obtain ⟨ε, hε, hερ⟩ : ∃ ε > 0, (‖t₀‖ + ε) * ‖τ‖ < 1 := by
    rcases eq_or_ne τ 0 with h | h
    · exact ⟨1, one_pos, by rw [h, norm_zero, mul_zero]; norm_num⟩
    · have hτ0 : 0 < ‖τ‖ := norm_pos_iff.mpr h
      refine ⟨(1 - ‖t₀‖ * ‖τ‖) / (2 * ‖τ‖), by
        apply div_pos (by linarith) (by positivity), ?_⟩
      field_simp; nlinarith
  set ρ := ‖t₀‖ + ε
  set δ := 1 - max (‖τ‖ ^ 2) (‖τ‖ * ρ)
  have hδ : 0 < δ := by
    have h1 : ‖τ‖ ^ 2 < 1 := by nlinarith [norm_nonneg τ]
    have h2 : ‖τ‖ * ρ < 1 := by linarith [mul_comm ‖τ‖ ρ]
    simp only [δ]; have := max_lt h1 h2; linarith
  have h := hasDerivAt_integral_rsqrt (A := fun σ => 1 + τ ^ 2 * (1 - (σ : ℂ) ^ 2))
    (B := fun σ => (σ : ℂ) ^ 2 * τ) (by fun_prop) (by fun_prop) (t₀ := t₀) (MB := ‖τ‖) hε hδ
    (fun σ hσ t ht => by
      have ht' : ‖t‖ ≤ ρ := by
        have := norm_le_norm_add_norm_sub' t t₀
        rw [Metric.mem_ball, dist_eq_norm] at ht
        simp only [ρ]; linarith [norm_sub_rev t t₀]
      exact expD_re_ge ht' hσ)
    (fun σ hσ => by
      rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.1]
      have : σ ^ 2 ≤ 1 := by nlinarith [hσ.1, hσ.2]
      calc σ ^ 2 * ‖τ‖ ≤ 1 * ‖τ‖ := by gcongr
        _ = ‖τ‖ := one_mul _)
  exact h.const_mul (2 * τ)

theorem expD_ofReal (τ t : ℂ) (σ : ℝ) :
    expD τ σ t = (fun s : ℂ => 1 + τ ^ 2 * (1 - s ^ 2) + s ^ 2 * τ * t) σ := rfl

theorem expD_continuous (τ t : ℂ) : Continuous fun σ : ℝ => expD τ σ t := by
  unfold expD; fun_prop

/-- `∫₀¹ D^{−1/2} + τ²(1 − t/τ) ∫₀¹ σ² D^{−3/2} = (1 + τt)^{−1/2}` (by parts in `σ`). -/
theorem expD_parts {τ t : ℂ} (hτ0 : τ ≠ 0) (hre : ∀ σ ∈ Icc (0 : ℝ) 1, 0 < (expD τ σ t).re) :
    (∫ σ in (0 : ℝ)..1, expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ)) +
      τ ^ 2 * (1 - t / τ) * ∫ σ in (0 : ℝ)..1, (σ : ℂ) ^ 2 * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ) =
      (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ) := by
  have hslit : ∀ σ ∈ Icc (0 : ℝ) 1, expD τ σ t ∈ slitPlane := fun σ hσ =>
    mem_slitPlane_of_pos_re (hre σ hσ)
  have hc1 : ContinuousOn (fun σ : ℝ => expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ)) (Icc 0 1) :=
    (expD_continuous τ t).continuousOn.cpow_const hslit
  have hc3 : ContinuousOn (fun σ : ℝ => (σ : ℂ) ^ 2 * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ)) (Icc 0 1) :=
    (by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) ^ 2).continuousOn.mul
      ((expD_continuous τ t).continuousOn.cpow_const hslit)
  have hd : ∀ σ ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun σ : ℝ => (σ : ℂ) * expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ))
      (expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ) +
        τ ^ 2 * (1 - t / τ) * ((σ : ℂ) ^ 2 * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ))) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le zero_le_one] at hσ
    have hD : HasDerivAt (fun s : ℂ => 1 + τ ^ 2 * (1 - s ^ 2) + s ^ 2 * τ * t)
        (-2 * (σ : ℂ) * τ ^ 2 + 2 * (σ : ℂ) * τ * t) (σ : ℂ) := by
      have := (((hasDerivAt_pow 2 (σ : ℂ)).const_sub 1).const_mul (τ ^ 2)).const_add 1 |>.add
        (((hasDerivAt_pow 2 (σ : ℂ)).mul_const τ).mul_const t)
      convert this using 1; push_cast; ring
    have hp := (hasDerivAt_id (σ : ℂ)).mul (hD.cpow_const (c := ((-1 / 2 : ℝ) : ℂ)) (hslit σ hσ))
    have h := hp.comp_ofReal
    convert h using 1
    · funext y; rfl
    show _ = 1 * expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ) + (σ : ℂ) * (((-1 / 2 : ℝ) : ℂ) *
      expD τ σ t ^ (((-1 / 2 : ℝ) : ℂ) - 1) * (-2 * (σ : ℂ) * τ ^ 2 + 2 * (σ : ℂ) * τ * t))
    rw [show ((-1 / 2 : ℝ) : ℂ) - 1 = ((-3 / 2 : ℝ) : ℂ) by push_cast; norm_num]
    have hD0 : expD τ σ t ≠ 0 := slitPlane_ne_zero (hslit σ hσ)
    have e : expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ) = expD τ σ t * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ) := by
      conv_lhs => rw [show ((-1 / 2 : ℝ) : ℂ) = 1 + ((-3 / 2 : ℝ) : ℂ) by push_cast; norm_num]
      rw [cpow_add _ _ hD0, cpow_one]
    field_simp
    push_cast
    ring
  have hint : IntervalIntegrable (fun σ : ℝ => expD τ σ t ^ ((-1 / 2 : ℝ) : ℂ) +
      τ ^ 2 * (1 - t / τ) * ((σ : ℂ) ^ 2 * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ))) volume 0 1 :=
    (hc1.intervalIntegrable_of_Icc zero_le_one).add
      ((hc3.intervalIntegrable_of_Icc zero_le_one).const_mul _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable_of_Icc zero_le_one)
    ((hc3.intervalIntegrable_of_Icc zero_le_one).const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  rw [hftc]
  simp [expD]

/-! ### `ψ` -/

/-- `ψ(t) = (1 − t/τ)^{1/2} κ(t)` (`= ∫ₜ^τ ds/√p`). -/
noncomputable def expPsi (τ t : ℂ) : ℂ := (1 - t / τ) ^ ((1 / 2 : ℝ) : ℂ) * expKappa τ t

theorem one_sub_div_re_pos {τ t : ℂ} (ht : ‖t‖ < ‖τ‖) : 0 < (1 - t / τ).re := by
  have hτ : 0 < ‖τ‖ := lt_of_le_of_lt (norm_nonneg _) ht
  have h : ‖t / τ‖ < 1 := by rw [norm_div, div_lt_one hτ]; exact ht
  have := neg_le_of_abs_le ((abs_re_le_norm (t / τ)).trans h.le)
  have h2 := (re_le_norm (t / τ)).trans_lt h
  simp only [sub_re, one_re]; linarith

theorem one_add_mul_re_pos {τ t : ℂ} (ht : ‖τ‖ * ‖t‖ < 1) : 0 < (1 + τ * t).re := by
  have h := (abs_re_le_norm (τ * t)).trans_lt (by rw [norm_mul]; exact ht)
  have := neg_lt_of_abs_lt h
  simp only [add_re, one_re]; linarith

theorem expD_re_pos_small {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ * ‖τ‖ < 1) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) : 0 < (expD τ σ t).re := by
  have h := expD_re_ge (τ := τ) (ρ := ‖t‖) le_rfl hσ
  have h1 : ‖τ‖ ^ 2 < 1 := by nlinarith [norm_nonneg τ]
  have h2 : ‖τ‖ * ‖t‖ < 1 := by linarith [mul_comm ‖t‖ ‖τ‖]
  have := max_lt h1 h2
  linarith

/-- `ψ′ = −(1 − t/τ)^{−1/2}(1 + τt)^{−1/2}` for `|t| < |τ|`. -/
theorem hasDerivAt_expPsi {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    HasDerivAt (expPsi τ)
      (-((1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) * (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ))) t := by
  have hτ0 : τ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) ht)
  have htt : ‖t‖ * ‖τ‖ < 1 := by nlinarith [norm_nonneg t, norm_nonneg τ]
  have hu := one_sub_div_re_pos ht
  have hu0 : 1 - t / τ ≠ 0 := fun h => by rw [h, zero_re] at hu; exact lt_irrefl _ hu
  have hU : HasDerivAt (fun t => (1 - t / τ) ^ ((1 / 2 : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) * (1 - t / τ) ^ (((1 / 2 : ℝ) : ℂ) - 1) * (-(1 / τ))) t := by
    have := ((hasDerivAt_id t).div_const τ).const_sub 1
    exact this.cpow_const (mem_slitPlane_of_pos_re hu) |>.congr_deriv (by simp [id])
  have hK := hasDerivAt_expKappa hτ htt
  have hP := expD_parts (t := t) hτ0 fun σ hσ => expD_re_pos_small hτ htt hσ
  have h := hU.mul hK
  unfold expPsi
  convert h using 1
  rw [show ((1 / 2 : ℝ) : ℂ) - 1 = ((-1 / 2 : ℝ) : ℂ) by push_cast; norm_num]
  have hhalf : (1 - t / τ) ^ ((1 / 2 : ℝ) : ℂ) =
      (1 - t / τ) * (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) := by
    conv_lhs => rw [show ((1 / 2 : ℝ) : ℂ) = 1 + ((-1 / 2 : ℝ) : ℂ) by push_cast; norm_num]
    rw [cpow_add _ _ hu0, cpow_one]
  rw [hhalf, expKappa, ← hP]
  rw [show (∫ σ in (0 : ℝ)..1,
        (-(1 / 2) : ℂ) * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ) * ((σ : ℂ) ^ 2 * τ)) =
      (-(1 / 2) * τ) * ∫ σ in (0 : ℝ)..1, (σ : ℂ) ^ 2 * expD τ σ t ^ ((-3 / 2 : ℝ) : ℂ) by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext σ; ring]
  field_simp
  push_cast
  ring

/-! ### The generating functions -/

/-- `Q = p^{−1/2} = (1 − t/τ)^{−1/2}(1 + τt)^{−1/2}`. -/
noncomputable def expQ (τ t : ℂ) : ℂ :=
  (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) * (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ)

/-- `r = Q′/Q = −p′/(2p)`. -/
noncomputable def expR (τ t : ℂ) : ℂ := 1 / (2 * τ - 2 * t) - τ / (2 * (1 + τ * t))

/-- `G_ε(t) = e^{εa(ψ(t) − ψ(0))} Q(t)`: `ε = 1` gives `∑ Bₙ tⁿ/n!`, `ε = −1` gives `∑ Aₙ tⁿ/n!`. -/
noncomputable def expG (ε a τ t : ℂ) : ℂ := exp (ε * a * (expPsi τ t - expPsi τ 0)) * expQ τ t

theorem small_ball_facts {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    τ ≠ 0 ∧ 0 < (1 - t / τ).re ∧ 0 < (1 + τ * t).re ∧ 2 * τ - 2 * t ≠ 0 ∧ 1 + τ * t ≠ 0 := by
  have hτ0 : τ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) ht)
  have hu := one_sub_div_re_pos ht
  have hw := one_add_mul_re_pos (τ := τ) (t := t) (by nlinarith [norm_nonneg t, norm_nonneg τ])
  refine ⟨hτ0, hu, hw, ?_, fun h => by rw [h, zero_re] at hw; exact lt_irrefl _ hw⟩
  intro h
  have : t = τ := by linear_combination -h / 2
  rw [this] at ht; exact lt_irrefl _ ht

theorem hasDerivAt_expQ {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    HasDerivAt (expQ τ) (expQ τ t * expR τ t) t := by
  obtain ⟨hτ0, hu, hw, h2, hw0⟩ := small_ball_facts hτ ht
  have hu0 : 1 - t / τ ≠ 0 := fun h => by rw [h, zero_re] at hu; exact lt_irrefl _ hu
  have hU := (((hasDerivAt_id t).div_const τ).const_sub 1).cpow_const
    (c := ((-1 / 2 : ℝ) : ℂ)) (mem_slitPlane_of_pos_re hu)
  have hW := (((hasDerivAt_id t).const_mul τ).const_add 1).cpow_const
    (c := ((-1 / 2 : ℝ) : ℂ)) (mem_slitPlane_of_pos_re hw)
  have h := hU.mul hW
  unfold expQ
  convert h using 1
  · funext s; rfl
  have e1 : (1 - t / τ) ^ (((-1 / 2 : ℝ) : ℂ) - 1) =
      (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) / (1 - t / τ) := by
    rw [cpow_sub _ _ hu0, cpow_one]
  have e2 : (1 + τ * t) ^ (((-1 / 2 : ℝ) : ℂ) - 1) =
      (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ) / (1 + τ * t) := by
    rw [cpow_sub _ _ hw0, cpow_one]
  simp only [id_eq]
  rw [e1, e2, expR]
  have h3 : τ - t ≠ 0 := fun h => h2 (by linear_combination 2 * h)
  have : (1 - t / τ) = (τ - t) / τ := by field_simp
  rw [this]
  field_simp
  push_cast
  ring

theorem expQ_sq {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    expQ τ t ^ 2 * ((1 - t / τ) * (1 + τ * t)) = 1 := by
  obtain ⟨hτ0, hu, hw, h2, hw0⟩ := small_ball_facts hτ ht
  have hu0 : 1 - t / τ ≠ 0 := fun h => by rw [h, zero_re] at hu; exact lt_irrefl _ hu
  have k : ∀ x : ℂ, x ≠ 0 → (x ^ ((-1 / 2 : ℝ) : ℂ)) ^ 2 * x = 1 := by
    intro x hx
    rw [← cpow_mul_nat, show ((-1 / 2 : ℝ) : ℂ) * ((2 : ℕ) : ℂ) = -1 by
      push_cast; norm_num, cpow_neg_one]
    field_simp
  unfold expQ
  have := k _ hu0; have := k _ hw0
  linear_combination (1 + τ * t) * ((1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ)) ^ 2 * k _ hu0 + k _ hw0

/-- `G′/G = −εaQ + r`. -/
noncomputable def expRR (ε a τ t : ℂ) : ℂ := -ε * a * expQ τ t + expR τ t

theorem hasDerivAt_expG {ε a τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    HasDerivAt (expG ε a τ) (expG ε a τ t * expRR ε a τ t) t := by
  have hP := hasDerivAt_expPsi hτ ht
  have he := ((hP.sub_const (expPsi τ 0)).const_mul (ε * a)).cexp
  have h := he.mul (hasDerivAt_expQ hτ ht)
  unfold expG
  convert h using 1
  simp only [expRR, expQ]
  ring

/-- `r′ = 2/(2τ − 2t)² + τ²/(2(1 + τt)²)`. -/
noncomputable def expR' (τ t : ℂ) : ℂ := 2 / (2 * τ - 2 * t) ^ 2 + τ ^ 2 / (2 * (1 + τ * t) ^ 2)

theorem hasDerivAt_expR {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    HasDerivAt (expR τ) (expR' τ t) t := by
  obtain ⟨hτ0, -, -, h2, hw0⟩ := small_ball_facts hτ ht
  have h1 := (((hasDerivAt_id t).const_mul 2).const_sub (2 * τ)).inv h2
  have h3 := ((((hasDerivAt_id t).const_mul τ).const_add 1).const_mul 2).inv
    (mul_ne_zero two_ne_zero hw0)
  have h := (h1.const_mul 1).sub (h3.const_mul τ)
  unfold expR
  convert h using 1
  · funext s; simp [div_eq_mul_inv]
  · simp only [expR', id]; field_simp; ring

theorem hasDerivAt_expRR {ε a τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    HasDerivAt (expRR ε a τ) (-ε * a * (expQ τ t * expR τ t) + expR' τ t) t :=
  ((hasDerivAt_expQ hτ ht).const_mul (-ε * a)).add (hasDerivAt_expR hτ ht)

/-- The ODE `p G″ + (3/2) p′ G′ − (a² + 1) G = 0`, `p = (1 − t/τ)(1 + τt)`, `ε² = 1`. -/
theorem expG_ode {ε a τ t : ℂ} (hε : ε ^ 2 = 1) (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    (1 + (τ - 1 / τ) * t - t ^ 2) * (expG ε a τ t * expRR ε a τ t * expRR ε a τ t +
        expG ε a τ t * (-ε * a * (expQ τ t * expR τ t) + expR' τ t)) +
      3 / 2 * ((τ - 1 / τ) - 2 * t) * (expG ε a τ t * expRR ε a τ t) -
      (a ^ 2 + 1) * expG ε a τ t = 0 := by
  obtain ⟨hτ0, -, -, h2, hw0⟩ := small_ball_facts hτ ht
  have hQ := expQ_sq hτ ht
  have hP : (1 - t / τ) * (1 + τ * t) = 1 + (τ - 1 / τ) * t - t ^ 2 := by field_simp; ring
  rw [hP] at hQ
  set P := 1 + (τ - 1 / τ) * t - t ^ 2
  have k1 : P * expR τ t = -((τ - 1 / τ) - 2 * t) / 2 := by
    simp only [P, expR]
    have h3 : τ - t ≠ 0 := fun h => h2 (by linear_combination 2 * h)
    field_simp; ring
  have k2 :
      P * expR τ t ^ 2 + P * expR' τ t + 3 / 2 * ((τ - 1 / τ) - 2 * t) * expR τ t - 1 = 0 := by
    simp only [P, expR, expR']
    have h3 : τ - t ≠ 0 := fun h => h2 (by linear_combination 2 * h)
    field_simp; ring
  simp only [expRR]
  linear_combination expG ε a τ t * (a ^ 2 * ε ^ 2 * hQ + a ^ 2 * hε -
    3 * ε * a * expQ τ t * k1 + k2)

/-! ### From the ODE to the recurrence -/

/-- `(zF)^{(n)}(0) = n F^{(n−1)}(0)`. -/
theorem iteratedDeriv_id_mul_zero' {F : ℂ → ℂ} {n : ℕ} (hF : ContDiffAt ℂ n F 0) :
    iteratedDeriv n (fun z => z * F z) 0 = n * iteratedDeriv (n - 1) F 0 := by
  have hid : ContDiffAt ℂ n (fun a : ℂ => a) 0 := contDiffAt_id
  rw [iteratedDeriv_fun_mul hid hF]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [iteratedDeriv_fun_id_zero]
  · rw [sum_eq_single 1 (fun i _ hi => by rw [iteratedDeriv_fun_id_zero]; simp [hi])
      (fun h => absurd (mem_range.mpr (by omega)) h)]
    rw [iteratedDeriv_fun_id_zero]; simp

/-- If `(1 + ct − t²) G″ + (3/2)(c − 2t) G′ − d G = 0` near `0` then
`G^{(m+2)}(0) = −c(m + 3/2) G^{(m+1)}(0) + (m(m + 2) + d) G^{(m)}(0)`. -/
theorem iteratedDeriv_rec_of_ode {G : ℂ → ℂ} {c d : ℂ} (hG : AnalyticAt ℂ G 0)
    (hode : (fun t => (1 + c * t - t ^ 2) * deriv (deriv G) t +
      3 / 2 * (c - 2 * t) * deriv G t - d * G t) =ᶠ[𝓝 0] fun _ => 0) (m : ℕ) :
    iteratedDeriv (m + 2) G 0 = -c * (m + 3 / 2) * iteratedDeriv (m + 1) G 0 +
      (m * (m + 2) + d) * iteratedDeriv m G 0 := by
  set H1 := deriv G
  set H2 := deriv (deriv G)
  have a1 : AnalyticAt ℂ H1 0 := hG.deriv
  have a2 : AnalyticAt ℂ H2 0 := hG.deriv.deriv
  have e : (fun t => (1 + c * t - t ^ 2) * H2 t + 3 / 2 * (c - 2 * t) * H1 t - d * G t) =
      fun t => (((H2 t + c * (t * H2 t)) - t * (t * H2 t)) + 3 / 2 * c * H1 t) -
        3 * (t * H1 t) - d * G t := by
    funext t; ring
  have h := hode.iteratedDeriv_eq m
  rw [e] at h
  have b1 : AnalyticAt ℂ (fun t => H2 t + c * (t * H2 t)) 0 := by fun_prop
  have b2 : AnalyticAt ℂ (fun t => H2 t + c * (t * H2 t) - t * (t * H2 t)) 0 := by fun_prop
  have b3 :
      AnalyticAt ℂ (fun t => H2 t + c * (t * H2 t) - t * (t * H2 t) + 3 / 2 * c * H1 t) 0 := by
    fun_prop
  have b4 : AnalyticAt ℂ (fun t => H2 t + c * (t * H2 t) - t * (t * H2 t) + 3 / 2 * c * H1 t -
    3 * (t * H1 t)) 0 := by fun_prop
  have d1 : AnalyticAt ℂ (fun t => t * H2 t) 0 := by fun_prop
  have d2 : AnalyticAt ℂ (fun t => t * (t * H2 t)) 0 := by fun_prop
  have d3 : AnalyticAt ℂ (fun t => t * H1 t) 0 := by fun_prop
  have g1 : AnalyticAt ℂ (fun t => d * G t) 0 := by fun_prop
  have g2 : AnalyticAt ℂ (fun t => 3 * (t * H1 t)) 0 := by fun_prop
  have g3 : AnalyticAt ℂ (fun t => 3 / 2 * c * H1 t) 0 := by fun_prop
  have g4 : AnalyticAt ℂ (fun t => c * (t * H2 t)) 0 := by fun_prop
  rw [iteratedDeriv_fun_sub b4.contDiffAt g1.contDiffAt,
    iteratedDeriv_fun_sub b3.contDiffAt g2.contDiffAt,
    iteratedDeriv_fun_add b2.contDiffAt g3.contDiffAt,
    iteratedDeriv_fun_sub b1.contDiffAt d2.contDiffAt,
    iteratedDeriv_fun_add a2.contDiffAt g4.contDiffAt,
    iteratedDeriv_const_mul _ d1.contDiffAt, iteratedDeriv_const_mul _ a1.contDiffAt,
    iteratedDeriv_const_mul _ d3.contDiffAt, iteratedDeriv_const_mul _ hG.contDiffAt,
    iteratedDeriv_id_mul_zero' a2.contDiffAt, iteratedDeriv_id_mul_zero' d1.contDiffAt,
    iteratedDeriv_id_mul_zero' a1.contDiffAt, iteratedDeriv_id_mul_zero' a2.contDiffAt] at h
  simp only [iteratedDeriv_const, ite_self] at h
  have hH2 : ∀ k, iteratedDeriv k H2 0 = iteratedDeriv (k + 2) G 0 := fun k => by
    simp only [H2, iteratedDeriv_succ']
  have hH1 : ∀ k, iteratedDeriv k H1 0 = iteratedDeriv (k + 1) G 0 := fun k => by
    simp only [H1, iteratedDeriv_succ']
  simp only [hH1, hH2] at h
  rcases m with _ | _ | m
  · simp at h ⊢; linear_combination h
  · simp at h ⊢; linear_combination h
  · simp only [Nat.add_sub_cancel] at h
    push_cast at h ⊢
    ring_nf at h ⊢
    linear_combination h

theorem expG_analyticAt {ε a τ : ℂ} (hτ : ‖τ‖ < 1) {t : ℂ} (ht : ‖t‖ < ‖τ‖) :
    AnalyticAt ℂ (expG ε a τ) t := by
  have hd : DifferentiableOn ℂ (expG ε a τ) (Metric.ball 0 ‖τ‖) := fun s hs =>
    (hasDerivAt_expG hτ (by simpa using hs)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using ht))

theorem expG_zero (ε a τ : ℂ) : expG ε a τ 0 = 1 := by
  simp [expG, expQ]

/-- The derivatives of `G_ε` at `0` satisfy the recurrence of the continued fraction. -/
theorem iteratedDeriv_expG_rec {ε a τ : ℂ} (hε : ε ^ 2 = 1) (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (m : ℕ) : iteratedDeriv (m + 2) (expG ε a τ) 0 =
      -(τ - 1 / τ) * (m + 3 / 2) * iteratedDeriv (m + 1) (expG ε a τ) 0 +
        (m * (m + 2) + (a ^ 2 + 1)) * iteratedDeriv m (expG ε a τ) 0 := by
  have hτp : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  have hball : Metric.ball (0 : ℂ) ‖τ‖ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hτp
  have h1 : deriv (expG ε a τ) =ᶠ[𝓝 0] fun t => expG ε a τ t * expRR ε a τ t :=
    Filter.eventually_of_mem hball fun t ht => (hasDerivAt_expG hτ (by simpa using ht)).deriv
  have h2 : deriv (deriv (expG ε a τ)) =ᶠ[𝓝 0] fun t => expG ε a τ t * expRR ε a τ t *
      expRR ε a τ t + expG ε a τ t * (-ε * a * (expQ τ t * expR τ t) + expR' τ t) := by
    have h1' : deriv (expG ε a τ) =ᶠ[𝓝 0] fun t => expG ε a τ t * expRR ε a τ t := h1
    filter_upwards [hball, h1'.eventually_nhds] with t ht ht'
    rw [Filter.EventuallyEq.deriv_eq ht']
    exact ((hasDerivAt_expG hτ (by simpa using ht)).mul
      (hasDerivAt_expRR hτ (by simpa using ht))).deriv
  refine iteratedDeriv_rec_of_ode (expG_analyticAt hτ (by simpa using hτp)) ?_ m
  filter_upwards [hball, h1, h2] with t ht e1 e2
  rw [e1, e2]
  exact expG_ode hε hτ (by simpa using ht)

theorem iteratedDeriv_expG_one {ε a τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) :
    iteratedDeriv 1 (expG ε a τ) 0 = -ε * a + (1 / τ - τ) / 2 := by
  rw [iteratedDeriv_one, (hasDerivAt_expG hτ (by simpa using norm_pos_iff.mpr hτ0)).deriv,
    expG_zero]
  simp [expRR, expQ, expR]
  field_simp

/-- `G₁^{(n)}(0) = Bₙ` and `G₋₁^{(n)}(0) = Aₙ`. -/
theorem iteratedDeriv_expG_eq {a z : ℂ} (hz : ∀ y : ℝ, |y| ≤ 1 → z ≠ I * y) (n : ℕ) :
    iteratedDeriv n (expG 1 a (expTau z)) 0 = cfB (expCFa a) (expCFb a z) n ∧
      iteratedDeriv n (expG (-1) a (expTau z)) 0 = cfA (expCFa a) (expCFb a z) n := by
  obtain ⟨hp, hτ, hτ0⟩ := expTau_spec hz
  set τ := expTau z
  have hc : -(τ - 1 / τ) = 2 * z := by field_simp; linear_combination hp
  have h1z : (1 / τ - τ) / 2 = z := by field_simp; linear_combination hp
  obtain ⟨i0, i1, j0, j1⟩ := expCF_init a z
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [expG_zero, i0, j0]
    | 1 =>
      rw [iteratedDeriv_expG_one hτ hτ0, iteratedDeriv_expG_one hτ hτ0, h1z, i1, j1]
      constructor <;> ring
    | m + 2 =>
      obtain ⟨r1, r2⟩ := expCF_rec a z m
      rw [iteratedDeriv_expG_rec (by norm_num) hτ hτ0, iteratedDeriv_expG_rec (by norm_num) hτ hτ0,
        (ih (m + 1) (by omega)).1, (ih (m + 1) (by omega)).2, (ih m (by omega)).1,
        (ih m (by omega)).2, r1, r2, hc]
      constructor <;> ring

/-! ### `cosh(a√x)` and `sinh(a√x)/(a√x)` -/

/-- `C(x) = ∑ (a²x)ⁿ/(2n)!` (`= cosh(a√x)`). -/
noncomputable def expC (a x : ℂ) : ℂ := ∑' n : ℕ, (a ^ 2 * x) ^ n / ((2 * n)! : ℂ)

/-- `S(x) = ∑ (a²x)ⁿ/(2n + 1)!` (`= sinh(a√x)/(a√x)`). -/
noncomputable def expS (a x : ℂ) : ℂ := ∑' n : ℕ, (a ^ 2 * x) ^ n / ((2 * n + 1)! : ℂ)

theorem norm_pow_div_factorial_le (w : ℂ) (n m : ℕ) (hm : n ≤ m) :
    ‖w ^ n / (m ! : ℂ)‖ ≤ ‖w‖ ^ n / n ! := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  gcongr

theorem summable_expC (a x : ℂ) : Summable fun n : ℕ => (a ^ 2 * x) ^ n / ((2 * n)! : ℂ) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖a ^ 2 * x‖) fun n =>
    norm_pow_div_factorial_le _ n (2 * n) (by omega)

theorem summable_expS (a x : ℂ) : Summable fun n : ℕ => (a ^ 2 * x) ^ n / ((2 * n + 1)! : ℂ) :=
  Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖a ^ 2 * x‖) fun n =>
    norm_pow_div_factorial_le _ n (2 * n + 1) (by omega)

/-- `e^{ay} = C(y²) + ay S(y²)`. -/
theorem exp_eq_expC_add (a y : ℂ) : exp (a * y) = expC a (y ^ 2) + a * y * expS a (y ^ 2) := by
  have he := NormedSpace.expSeries_div_hasSum_exp (a * y)
  rw [← Complex.exp_eq_exp_ℂ] at he
  have h1 : HasSum (fun k => (a * y) ^ (2 * k) / ((2 * k)! : ℂ)) (expC a (y ^ 2)) := by
    convert (summable_expC a (y ^ 2)).hasSum using 2 with k
    · rw [pow_mul]; ring
    · rfl
  have h2 : HasSum (fun k => (a * y) ^ (2 * k + 1) / ((2 * k + 1)! : ℂ))
      (a * y * expS a (y ^ 2)) := by
    have := ((summable_expS a (y ^ 2)).hasSum).mul_left (a * y)
    convert this using 2 with k
    · rw [pow_succ, pow_mul]; ring
    · rfl
  exact he.unique (h1.even_add_odd h2)

theorem differentiable_expC (a : ℂ) : Differentiable ℂ (expC a) := by
  intro x₀
  have hd : DifferentiableOn ℂ (expC a) (Metric.ball 0 (‖x₀‖ + 1)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n => (‖a‖ ^ 2 * (‖x₀‖ + 1)) ^ n / n !)
      (Real.summable_pow_div_factorial _) (fun n => by fun_prop) Metric.isOpen_ball fun n w hw => ?_
    refine (norm_pow_div_factorial_le _ n (2 * n) (by omega)).trans ?_
    rw [norm_mul, norm_pow]
    gcongr
    rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))

theorem differentiable_expS (a : ℂ) : Differentiable ℂ (expS a) := by
  intro x₀
  have hd : DifferentiableOn ℂ (expS a) (Metric.ball 0 (‖x₀‖ + 1)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun n => (‖a‖ ^ 2 * (‖x₀‖ + 1)) ^ n / n !)
      (Real.summable_pow_div_factorial _) (fun n => by fun_prop) Metric.isOpen_ball fun n w hw => ?_
    refine (norm_pow_div_factorial_le _ n (2 * n + 1) (by omega)).trans ?_
    rw [norm_mul, norm_pow]
    gcongr
    rw [Metric.mem_ball, dist_zero_right] at hw; exact hw.le
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))

theorem expC_zero (a : ℂ) : expC a 0 = 1 := by
  rw [expC, tsum_eq_single 0 (fun n hn => by simp [hn])]; simp

/-! ### The decomposition `G = (1 − t/τ)^{−1/2} k + m` -/

/-- `k_ε(t) = e^{−εaκ(0)}(1 + τt)^{−1/2} C((1 − t/τ)κ(t)²)`. -/
noncomputable def expK (ε a τ t : ℂ) : ℂ :=
  exp (-(ε * a) * expKappa τ 0) * (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ) *
    expC a ((1 - t / τ) * expKappa τ t ^ 2)

/-- `m_ε(t) = εa e^{−εaκ(0)}(1 + τt)^{−1/2} κ(t) S((1 − t/τ)κ(t)²)`. -/
noncomputable def expM (ε a τ t : ℂ) : ℂ :=
  ε * a * exp (-(ε * a) * expKappa τ 0) * (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ) * expKappa τ t *
    expS a ((1 - t / τ) * expKappa τ t ^ 2)

theorem expG_decomp {ε a τ t : ℂ} (hε : ε ^ 2 = 1) (hτ : ‖τ‖ < 1) (ht : ‖t‖ < ‖τ‖) :
    expG ε a τ t = (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) * expK ε a τ t + expM ε a τ t := by
  obtain ⟨hτ0, hu, -, -, -⟩ := small_ball_facts hτ ht
  have hu0 : 1 - t / τ ≠ 0 := fun h => by rw [h, zero_re] at hu; exact lt_irrefl _ hu
  have hpsi0 : expPsi τ 0 = expKappa τ 0 := by simp [expPsi]
  have hsq : ((1 - t / τ) ^ ((1 / 2 : ℝ) : ℂ)) ^ 2 = 1 - t / τ := by
    rw [← cpow_mul_nat, show ((1 / 2 : ℝ) : ℂ) * ((2 : ℕ) : ℂ) = 1 by push_cast; norm_num,
      cpow_one]
  have hprod : (1 - t / τ) ^ ((1 / 2 : ℝ) : ℂ) * (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) = 1 := by
    rw [← cpow_add _ _ hu0, show ((1 / 2 : ℝ) : ℂ) + ((-1 / 2 : ℝ) : ℂ) = 0 by push_cast; norm_num,
      cpow_zero]
  have hC : expC (ε * a) = expC a := by
    funext x; simp only [expC, mul_pow, hε, one_mul]
  have hS : expS (ε * a) = expS a := by
    funext x; simp only [expS, mul_pow, hε, one_mul]
  have he := exp_eq_expC_add (ε * a) (expPsi τ t)
  rw [hC, hS] at he
  have hpsi2 : expPsi τ t ^ 2 = (1 - t / τ) * expKappa τ t ^ 2 := by
    rw [expPsi, mul_pow, hsq]
  rw [hpsi2] at he
  unfold expG expK expM expQ
  rw [hpsi0, show ε * a * (expPsi τ t - expKappa τ 0) = -(ε * a) * expKappa τ 0 +
    ε * a * expPsi τ t by ring, exp_add, he]
  simp only [expPsi]
  linear_combination (exp (-(ε * a) * expKappa τ 0) * (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ) * ε * a *
    expKappa τ t * expS a ((1 - t / τ) * expKappa τ t ^ 2)) * hprod

theorem differentiableAt_expKappa {τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ * ‖τ‖ < 1) :
    DifferentiableAt ℂ (expKappa τ) t :=
  (hasDerivAt_expKappa hτ ht).differentiableAt

theorem differentiableAt_expK {ε a τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ * ‖τ‖ < 1) :
    DifferentiableAt ℂ (expK ε a τ) t := by
  have hk := differentiableAt_expKappa hτ ht
  have hw := one_add_mul_re_pos (τ := τ) (t := t) (by linarith [mul_comm ‖t‖ ‖τ‖])
  have hW : DifferentiableAt ℂ (fun t => (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ)) t :=
    (((differentiableAt_id.const_mul τ).const_add 1).cpow_const (mem_slitPlane_of_pos_re hw))
  unfold expK
  exact ((differentiableAt_const _).mul hW).mul ((differentiable_expC a).differentiableAt.comp t
    (((differentiableAt_const _).sub (differentiableAt_id.div_const τ)).mul (hk.pow 2)))

theorem differentiableAt_expM {ε a τ t : ℂ} (hτ : ‖τ‖ < 1) (ht : ‖t‖ * ‖τ‖ < 1) :
    DifferentiableAt ℂ (expM ε a τ) t := by
  have hk := differentiableAt_expKappa hτ ht
  have hw := one_add_mul_re_pos (τ := τ) (t := t) (by linarith [mul_comm ‖t‖ ‖τ‖])
  have hW : DifferentiableAt ℂ (fun t => (1 + τ * t) ^ ((-1 / 2 : ℝ) : ℂ)) t :=
    (((differentiableAt_id.const_mul τ).const_add 1).cpow_const (mem_slitPlane_of_pos_re hw))
  unfold expM
  exact (((differentiableAt_const _).mul hW).mul hk).mul
    ((differentiable_expS a).differentiableAt.comp t
    (((differentiableAt_const _).sub (differentiableAt_id.div_const τ)).mul (hk.pow 2)))

/-! ### The coefficients `cₙ = 1·3⋯(2n − 1)/(2·4⋯(2n))` -/

theorem arcsinCoeff_pos (n : ℕ) : 0 < arcsinCoeff n :=
  prod_pos fun i _ => by positivity

theorem arcsinCoeff_ge (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ arcsinCoeff n := by
  induction n with
  | zero => simp [arcsinCoeff]
  | succ n ih =>
    rw [arcsinCoeff_succ]
    calc 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) * ((2 * n + 1) / (2 * n + 2)) := by
          push_cast
          rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ arcsinCoeff n * ((2 * n + 1) / (2 * n + 2)) := by gcongr

theorem arcsinCoeff_add (N m : ℕ) :
    arcsinCoeff (N + m) = arcsinCoeff N *
      ∏ j ∈ range m, ((2 * ((N + j : ℕ) : ℝ) + 1) / (2 * ((N + j : ℕ) : ℝ) + 2)) := by
  unfold arcsinCoeff
  rw [prod_range_add]

theorem arcsinCoeff_mul_le (N m : ℕ) : arcsinCoeff N * arcsinCoeff m ≤ arcsinCoeff (N + m) := by
  rw [arcsinCoeff_add]
  gcongr
  · exact (arcsinCoeff_pos N).le
  · unfold arcsinCoeff
    refine prod_le_prod₀ (fun j _ => by positivity) fun j _ => ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast; nlinarith

theorem tendsto_arcsinCoeff_ratio (m : ℕ) :
    Tendsto (fun N => arcsinCoeff N / arcsinCoeff (N + m)) atTop (𝓝 1) := by
  have hf : ∀ j ∈ range m, Tendsto (fun N : ℕ =>
      (2 * ((N + j : ℕ) : ℝ) + 1) / (2 * ((N + j : ℕ) : ℝ) + 2)) atTop (𝓝 1) := by
    intro j _
    have h1 : Tendsto (fun N : ℕ => 1 / (2 * ((N + j : ℕ) : ℝ) + 2)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      refine tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop (by norm_num) ?_)
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat j)
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
    simp only [sub_zero] at this
    refine this.congr fun N => ?_
    field_simp
    ring
  have hp := tendsto_finsetProd (range m) hf
  simp only [prod_const_one] at hp
  have := hp.inv₀ one_ne_zero
  simp only [inv_one] at this
  refine this.congr fun N => ?_
  rw [arcsinCoeff_add, div_mul_cancel_left₀ (arcsinCoeff_pos N).ne']

/-! ### Darboux's method -/

/-- Cauchy's estimate for the Taylor coefficients at `0`. -/
theorem cauchy_coeff_bound {F : ℂ → ℂ} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R)) :
    ∃ C, 0 ≤ C ∧ ∀ n : ℕ, ‖(n ! : ℂ)⁻¹ * iteratedDeriv n F 0‖ ≤ C / ρ ^ n := by
  have hsub : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball hρR
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_bound_of_continuousOn
    (hF.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub))
  have hC0 : 0 ≤ C := by
    have hz : ((ρ : ℝ) : ℂ) ∈ Metric.sphere (0 : ℂ) ρ := by simp [abs_of_pos hρ]
    exact (norm_nonneg _).trans (hC _ hz)
  refine ⟨C, hC0, fun n => ?_⟩
  have hd : DiffContOnCl ℂ F (Metric.ball 0 ρ) :=
    (hF.mono (by rw [closure_ball 0 hρ.ne']; exact hsub)).diffContOnCl
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hd hC
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  calc (n ! : ℝ)⁻¹ * ‖iteratedDeriv n F 0‖ ≤ (n ! : ℝ)⁻¹ * (n ! * C / ρ ^ n) := by gcongr
    _ = C / ρ ^ n := by field_simp

theorem taylor_hasSum {F : ℂ → ℂ} {R : ℝ} (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    {t : ℂ} (ht : ‖t‖ < R) :
    HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ * iteratedDeriv n F 0 * t ^ n) (F t) := by
  have h := Complex.hasSum_taylorSeries_on_ball hF (by simpa using ht)
  simp only [sub_zero, smul_eq_mul] at h
  convert h using 2 with n; ring

/-- The Taylor coefficients of `(1 − t/τ)^{−1/2} K(t) + M(t)`. -/
theorem darboux_coeff {τ : ℂ} (hτ0 : τ ≠ 0) {R : ℝ} (hR : ‖τ‖ < R) {G K M : ℂ → ℂ}
    (hK : DifferentiableOn ℂ K (Metric.ball 0 R)) (hM : DifferentiableOn ℂ M (Metric.ball 0 R))
    (hGd : DifferentiableOn ℂ G (Metric.ball 0 ‖τ‖))
    (hG : ∀ t : ℂ, ‖t‖ < ‖τ‖ → G t = (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) * K t + M t) (n : ℕ) :
    (n ! : ℂ)⁻¹ * iteratedDeriv n G 0 = (∑ k ∈ range (n + 1), (arcsinCoeff k : ℂ) * τ⁻¹ ^ k *
      ((((n - k) ! : ℂ))⁻¹ * iteratedDeriv (n - k) K 0)) + (n ! : ℂ)⁻¹ * iteratedDeriv n M 0 := by
  have hτp : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (‖τ‖ + R) / 2 := ⟨_, rfl⟩
  have hρ1 : ‖τ‖ < ρ := by rw [hρdef]; linarith
  have hρ2 : ρ < R := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨CK, hCK0, hCK⟩ := cauchy_coeff_bound hρ0 hρ2 hK
  have key : ∀ t ∈ Metric.ball (0 : ℂ) ‖τ‖, HasSum (fun n : ℕ =>
      ((∑ k ∈ range (n + 1), (arcsinCoeff k : ℂ) * τ⁻¹ ^ k *
        ((((n - k) ! : ℂ))⁻¹ * iteratedDeriv (n - k) K 0)) +
        (n ! : ℂ)⁻¹ * iteratedDeriv n M 0) * t ^ n) (G t) := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right] at ht
    have hw : ‖t / τ‖ < 1 := by rw [norm_div, div_lt_one hτp]; exact ht
    have h1 := hasSum_one_sub_cpow_neg_half hw
    have h2 := taylor_hasSum hK (by linarith : ‖t‖ < R)
    have hs1 : Summable fun k => ‖(arcsinCoeff k : ℂ) * (t / τ) ^ k‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (arcsinCoeff_pos k)]
        calc arcsinCoeff k * ‖t / τ‖ ^ k ≤ 1 * ‖t / τ‖ ^ k := by
              gcongr; exact arcsinCoeff_le_one k
          _ = ‖t / τ‖ ^ k := one_mul _)
        (summable_geometric_of_lt_one (norm_nonneg _) hw)
    have hs2 : Summable fun m => ‖(m ! : ℂ)⁻¹ * iteratedDeriv m K 0 * t ^ m‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
        ((summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) hρ0.le) ((div_lt_one hρ0).mpr
          (by linarith : ‖t‖ < ρ))).mul_left CK)
      rw [norm_mul, norm_pow]
      calc ‖(m ! : ℂ)⁻¹ * iteratedDeriv m K 0‖ * ‖t‖ ^ m ≤ CK / ρ ^ m * ‖t‖ ^ m := by
            gcongr; exact hCK m
        _ = CK * (‖t‖ / ρ) ^ m := by rw [div_pow]; ring
    have hprod := hasSum_sum_range_mul_of_summable_norm hs1 hs2
    rw [h1.tsum_eq, h2.tsum_eq] at hprod
    have h3 := taylor_hasSum hM (by linarith : ‖t‖ < R)
    have hsum := hprod.add h3
    rw [hG t ht]
    convert hsum using 1
    · funext n
      rw [add_mul, sum_mul]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      rw [div_pow, ← pow_mul_pow_sub t hkn, inv_pow]
      ring
    · push_cast; ring_nf
  have hT : ∀ t ∈ Metric.ball (0 : ℂ) ‖τ‖,
      HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ * iteratedDeriv n G 0 * t ^ n) (G t) := fun t ht =>
    taylor_hasSum hGd (by simpa using ht)
  have := coeff_eq_of_hasSum hτp hT key
  exact congrFun this n

theorem arcsinCoeff_ratio_le {n m : ℕ} (hm : m ≤ n) :
    arcsinCoeff (n - m) / arcsinCoeff n ≤ m + 1 := by
  have h1 := arcsinCoeff_mul_le (n - m) m
  rw [Nat.sub_add_cancel hm] at h1
  have h2 := arcsinCoeff_ge m
  have hp := arcsinCoeff_pos n
  have hq := arcsinCoeff_pos m
  rw [div_le_iff₀ hp]
  have : arcsinCoeff (n - m) ≤ arcsinCoeff n / arcsinCoeff m := by
    rw [le_div_iff₀ hq]; exact h1
  calc arcsinCoeff (n - m) ≤ arcsinCoeff n / arcsinCoeff m := this
    _ ≤ arcsinCoeff n * (m + 1) := by
        rw [div_le_iff₀ hq]
        have : 1 ≤ arcsinCoeff m * ((m : ℝ) + 1) := by
          rw [one_div, inv_le_iff_one_le_mul₀ (by positivity)] at h2; linarith
        nlinarith
    _ = (m + 1) * arcsinCoeff n := by ring

theorem summable_succ_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun m : ℕ => ((m : ℝ) + 1) * r ^ m := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr)
  have h2 := summable_geometric_of_lt_one hr0 hr
  convert h1.add h2 using 1
  funext m; simp; ring

/-- **Darboux's method**: if `G = (1 − t/τ)^{−1/2} K + M` near `0` with `K`, `M` analytic on a
larger disc, then `G^{(n)}(0) τⁿ/(n! cₙ) → K(τ)`. -/
theorem darboux_limit {τ : ℂ} (hτ0 : τ ≠ 0) {R : ℝ} (hR : ‖τ‖ < R) {G K M : ℂ → ℂ}
    (hK : DifferentiableOn ℂ K (Metric.ball 0 R)) (hM : DifferentiableOn ℂ M (Metric.ball 0 R))
    (hGd : DifferentiableOn ℂ G (Metric.ball 0 ‖τ‖))
    (hG : ∀ t : ℂ, ‖t‖ < ‖τ‖ → G t = (1 - t / τ) ^ ((-1 / 2 : ℝ) : ℂ) * K t + M t) :
    Tendsto (fun n : ℕ => (n ! : ℂ)⁻¹ * iteratedDeriv n G 0 * τ ^ n / (arcsinCoeff n : ℂ))
      atTop (𝓝 (K τ)) := by
  have hτp : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (‖τ‖ + R) / 2 := ⟨_, rfl⟩
  have hρ1 : ‖τ‖ < ρ := by rw [hρdef]; linarith
  have hρ2 : ρ < R := by rw [hρdef]; linarith
  have hρ0 : 0 < ρ := by linarith
  set r := ‖τ‖ / ρ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one hρ0).mpr hρ1
  obtain ⟨CK, hCK0, hCK⟩ := cauchy_coeff_bound hρ0 hρ2 hK
  obtain ⟨CM, hCM0, hCM⟩ := cauchy_coeff_bound hρ0 hρ2 hM
  set κ : ℕ → ℂ := fun m => (m ! : ℂ)⁻¹ * iteratedDeriv m K 0 with hκ
  set μ : ℕ → ℂ := fun m => (m ! : ℂ)⁻¹ * iteratedDeriv m M 0 with hμ
  have hc : ∀ n, (arcsinCoeff n : ℂ) ≠ 0 := fun n => by exact_mod_cast (arcsinCoeff_pos n).ne'
  -- the main part via Tannery's theorem
  set F : ℕ → ℕ → ℂ := fun n m => if m ≤ n then
    ((arcsinCoeff (n - m) / arcsinCoeff n : ℝ) : ℂ) * (κ m * τ ^ m) else 0 with hF
  have hbound : ∀ n m, ‖F n m‖ ≤ CK * (((m : ℝ) + 1) * r ^ m) := by
    intro n m
    simp only [hF]
    split_ifs with hm
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos (arcsinCoeff_pos _) (arcsinCoeff_pos _)), norm_mul, norm_pow]
      have h1 := arcsinCoeff_ratio_le hm
      have h2 := hCK m
      calc arcsinCoeff (n - m) / arcsinCoeff n * (‖κ m‖ * ‖τ‖ ^ m)
          ≤ ((m : ℝ) + 1) * (CK / ρ ^ m * ‖τ‖ ^ m) := by gcongr
        _ = CK * (((m : ℝ) + 1) * r ^ m) := by rw [hr, div_pow]; ring
    · simp; positivity
  have hlim : ∀ m, Tendsto (fun n => F n m) atTop (𝓝 (κ m * τ ^ m)) := by
    intro m
    have h := (tendsto_arcsinCoeff_ratio m).comp (tendsto_sub_atTop_nat m)
    have h2 : Tendsto (fun n => arcsinCoeff (n - m) / arcsinCoeff n) atTop (𝓝 1) :=
      h.congr' (Filter.eventually_atTop.2 ⟨m, fun n hn => by
        simp only [Function.comp, Nat.sub_add_cancel hn]⟩)
    have h' : Tendsto (fun n => ((arcsinCoeff (n - m) / arcsinCoeff n : ℝ) : ℂ)) atTop (𝓝 1) := by
      have := (continuous_ofReal.tendsto 1).comp h2
      rw [ofReal_one] at this
      exact this
    have := h'.mul_const (κ m * τ ^ m)
    rw [one_mul] at this
    refine this.congr' (Filter.eventually_atTop.2 ⟨m, fun n hn => ?_⟩)
    simp only [hF, hn, ↓reduceIte]
  have hT := tendsto_tsum_of_dominated_convergence
    ((summable_succ_mul_geometric hr0 hr1).mul_left CK) hlim (Eventually.of_forall hbound)
  have hKτ := (taylor_hasSum hK hR).tsum_eq
  rw [show (∑' m, κ m * τ ^ m) = K τ from by simpa [hκ] using hKτ] at hT
  -- the remainder
  have hrem : Tendsto (fun n : ℕ => μ n * τ ^ n / (arcsinCoeff n : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => CM * (((n : ℝ) + 1) * r ^ n)) atTop (𝓝 0) := by
      have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
      have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
      have := (h1.add h2).const_mul CM
      simp only [add_zero, mul_zero] at this
      refine this.congr fun n => ?_
      ring
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (arcsinCoeff_pos n)]
    have h1 := arcsinCoeff_ge n
    have h2 := hCM n
    have hp := arcsinCoeff_pos n
    rw [div_le_iff₀ hp]
    calc ‖μ n‖ * ‖τ‖ ^ n ≤ CM / ρ ^ n * ‖τ‖ ^ n := by gcongr
      _ = CM * r ^ n := by rw [hr, div_pow]; ring
      _ ≤ CM * (((n : ℝ) + 1) * r ^ n) * arcsinCoeff n := by
          have : 1 ≤ ((n : ℝ) + 1) * arcsinCoeff n := by
            rw [one_div, inv_le_iff_one_le_mul₀ (by positivity)] at h1; linarith
          have hrn : 0 ≤ CM * r ^ n := by positivity
          nlinarith
  have hsum := hT.add hrem
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  rw [darboux_coeff hτ0 hR hK hM hGd hG n]
  rw [tsum_eq_sum (s := range (n + 1)) (fun m hm => by
    have : ¬ m ≤ n := fun h => hm (mem_range.mpr (by omega))
    simp only [hF, this, ↓reduceIte])]
  rw [add_mul, add_div, sum_mul, sum_div]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [hF, show n + 1 - 1 - k = n - k by omega, Nat.sub_le, ↓reduceIte,
    show n - (n - k) = k by omega, hκ]
  have hτk : τ ^ n = τ ^ k * τ ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  push_cast
  rw [hτk, inv_pow]
  field_simp [hc n, hc k, pow_ne_zero k hτ0]

/-! ### The value: `κ(0) = arctan(1/z)` -/

/-- `τ ∫₀¹ (1 + τ²(1 − σ²))^{−1/2} dσ` (`= arctan τ`). -/
noncomputable def arctanInt (τ : ℂ) : ℂ :=
  τ * ∫ σ in (0 : ℝ)..1, (1 + (1 - (σ : ℂ) ^ 2) * τ ^ 2) ^ ((-1 / 2 : ℝ) : ℂ)

theorem expKappa_zero (τ : ℂ) : expKappa τ 0 = 2 * arctanInt τ := by
  simp only [expKappa, arctanInt, expD, mul_zero, add_zero]
  rw [mul_assoc]; congr 2
  exact intervalIntegral.integral_congr fun σ _ => by ring_nf

theorem differentiableOn_arctanInt : DifferentiableOn ℂ arctanInt (Metric.ball 0 1) := by
  intro τ hτ
  rw [Metric.mem_ball, dist_zero_right] at hτ
  have hw : ‖τ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg τ]
  obtain ⟨ε, hε, hεw⟩ : ∃ ε > 0, ‖τ ^ 2‖ + ε < 1 := ⟨(1 - ‖τ ^ 2‖) / 2, by linarith, by linarith⟩
  have hH := hasDerivAt_integral_rsqrt (A := fun _ => 1) (B := fun σ => 1 - (σ : ℂ) ^ 2)
    (by fun_prop) (by fun_prop) (t₀ := τ ^ 2) (MB := 1) hε (δ := 1 - (‖τ ^ 2‖ + ε))
    (by linarith) (fun σ hσ t ht => by
      have hs : 0 ≤ 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
      have hs1 : 1 - σ ^ 2 ≤ 1 := by nlinarith [hσ.1]
      have htn : ‖t‖ ≤ ‖τ ^ 2‖ + ε := by
        rw [Metric.mem_ball, dist_eq_norm] at ht
        have := norm_le_norm_add_norm_sub' t (τ ^ 2)
        linarith
      have hn : ‖(1 - (σ : ℂ) ^ 2) * t‖ ≤ ‖τ ^ 2‖ + ε := by
        rw [show (1 : ℂ) - (σ : ℂ) ^ 2 = ((1 - σ ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
        calc (1 - σ ^ 2) * ‖t‖ ≤ 1 * ‖t‖ := by gcongr
          _ ≤ _ := by rw [one_mul]; exact htn
      have := neg_le_of_abs_le ((abs_re_le_norm ((1 - (σ : ℂ) ^ 2) * t)).trans hn)
      simp only [add_re, one_re]; linarith)
    (fun σ hσ => by
      rw [show (1 : ℂ) - (σ : ℂ) ^ 2 = ((1 - σ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hσ.1, hσ.2])]
      nlinarith [hσ.1])
  have hc : HasDerivAt (fun τ : ℂ => τ ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
  exact ((hasDerivAt_id τ).mul (hH.comp τ hc)).differentiableAt.differentiableWithinAt

theorem arctanInt_ofReal {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : arctanInt x = Real.arctan x := by
  have h1x : 0 < 1 + x ^ 2 := by positivity
  set s := √(1 + x ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr h1x
  have hs2 : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt h1x.le
  have hd : ∀ σ ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun σ => Real.arcsin (x * σ / s))
      (x * (1 / √(1 + (1 - σ ^ 2) * x ^ 2))) σ := by
    intro σ hσ
    have hlt : x * σ / s < 1 := by
      rw [div_lt_one hs0]
      have : x * σ < 1 * s := by
        have : x < s := by
          rw [hs, Real.lt_sqrt (by linarith [hx.1])]; nlinarith
        nlinarith [hσ.1, hσ.2, hx.1]
      linarith
    have hgt : -1 < x * σ / s := by
      have : 0 ≤ x * σ / s := div_nonneg (mul_nonneg hx.1.le hσ.1.le) hs0.le
      linarith
    have hl : HasDerivAt (fun σ => x * σ / s) (x / s) σ := by
      simpa using ((hasDerivAt_id σ).const_mul x).div_const s
    have h := (Real.hasDerivAt_arcsin hgt.ne' hlt.ne).comp σ hl
    convert h using 1
    · rfl
    have hpos : 0 < 1 - (x * σ / s) ^ 2 := by nlinarith
    have hrad : 1 + (1 - σ ^ 2) * x ^ 2 = s ^ 2 * (1 - (x * σ / s) ^ 2) := by
      have : s ^ 2 * (1 - (x * σ / s) ^ 2) = s ^ 2 - (x * σ) ^ 2 := by field_simp
      rw [this, hs2]; ring
    rw [hrad, Real.sqrt_mul (by positivity), Real.sqrt_sq hs0.le]
    field_simp
  have hpos : ∀ σ : ℝ, σ ∈ Icc (0 : ℝ) 1 → 0 < 1 + (1 - σ ^ 2) * x ^ 2 := fun σ hσ => by
    have : 0 ≤ 1 - σ ^ 2 := by nlinarith [hσ.1, hσ.2]
    positivity
  have hcd : ContinuousOn (fun σ : ℝ => x * (1 / √(1 + (1 - σ ^ 2) * x ^ 2))) (Icc 0 1) :=
    continuousOn_const.mul (continuousOn_const.div (by fun_prop) fun σ hσ =>
      (Real.sqrt_pos.mpr (hpos σ hσ)).ne')
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (f := fun σ => Real.arcsin (x * σ / s)) (by fun_prop) hd
    (hcd.intervalIntegrable_of_Icc zero_le_one)
  simp only [mul_one, mul_zero, zero_div, Real.arcsin_zero, sub_zero] at hftc
  rw [Real.arctan_eq_arcsin, ← hs, ← hftc, intervalIntegral.integral_const_mul, arctanInt]
  push_cast
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  rw [Set.uIcc_of_le zero_le_one] at hσ
  have hp := hpos σ hσ
  rw [show (1 : ℂ) + (1 - (σ : ℂ) ^ 2) * (x : ℂ) ^ 2 = ((1 + (1 - σ ^ 2) * x ^ 2 : ℝ) : ℂ) by
    push_cast; ring, show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow hp.le]
  congr 1
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hp.le]
  norm_num

theorem mem_arctanCut_of_norm_lt {τ : ℂ} (hτ : ‖τ‖ < 1) : τ ∈ arctanCut :=
  mem_arctanCut_of_norm_le hτ.le (fun h => by rw [h, norm_I] at hτ; exact lt_irrefl _ hτ)
    (fun h => by rw [h, norm_neg, norm_I] at hτ; exact lt_irrefl _ hτ)

/-- `τ∫₀¹(1 + (1 − σ²)τ²)^{−1/2} dσ = arctan τ` on the unit disc (identity theorem). -/
theorem arctanInt_eq {τ : ℂ} (hτ : ‖τ‖ < 1) : arctanInt τ = arctanD τ := by
  have hU : Metric.ball (0 : ℂ) 1 ⊆ arctanCut := fun t ht =>
    mem_arctanCut_of_norm_lt (by simpa using ht)
  have hf := differentiableOn_arctanInt.analyticOnNhd Metric.isOpen_ball
  have hg := (dlmf_4_15_F11.1.mono hU).analyticOnNhd Metric.isOpen_ball
  have h0 : ((1 / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real]; norm_num
  have hlim : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(continuous_ofReal.tendsto _).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun h => (ne_of_gt (show (1 / 2 : ℝ) < x from hx)) (ofReal_injective h)
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (1 / 2 : ℝ), arctanInt x = arctanD x := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    rw [arctanInt_ofReal ⟨by linarith [hx.1], hx.2⟩, arctanD_ofReal]
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_ball 0 1).isPreconnected h0
    (hlim.frequently hev.frequently) (by simpa using hτ)

theorem abs_re_arctan_lt {τ : ℂ} (hτ : ‖τ‖ < 1) : |(arctan τ).re| < π / 4 := by
  set w := τ * I
  have hw : ‖w‖ < 1 := by rw [norm_mul, norm_I, mul_one]; exact hτ
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [normSq_apply] at this
    nlinarith [norm_nonneg w]
  have h1w : 1 - w ≠ 0 := fun h => by
    rw [show w = 1 by linear_combination -h, norm_one] at hw; exact lt_irrefl _ hw
  have hre : 0 < ((1 + w) / (1 - w)).re := by
    rw [div_re]
    have hn : 0 < normSq (1 - w) := normSq_pos.mpr h1w
    simp only [add_re, one_re, sub_re, add_im, one_im, sub_im, zero_add, zero_sub]
    rw [← add_div]
    apply div_pos _ hn
    nlinarith
  have harg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hval : (arctan τ).re = arg ((1 + w) / (1 - w)) / 2 := by
    rw [arctan]
    simp [mul_re, log_im]
    ring
  rw [hval, abs_div, abs_two]
  linarith

theorem one_div_mem_arctanCut_of_seg {z : ℂ} (hz : ∀ y : ℝ, |y| ≤ 1 → z ≠ I * y) :
    z ≠ 0 ∧ 1 / z ∈ arctanCut := by
  refine one_div_mem_arctanCut ?_
  by_contra h
  push Not at h
  refine hz z.im h.2 ?_
  apply Complex.ext <;> simp [h.1]

/-- `2 arctan τ = arccot z`. -/
theorem two_mul_arctanD_expTau {z : ℂ} (hz : ∀ y : ℝ, |y| ≤ 1 → z ≠ I * y) :
    2 * arctanD (expTau z) = arccotD z := by
  obtain ⟨hp, hτ, hτ0⟩ := expTau_spec hz
  set τ := expTau z
  obtain ⟨hz0, hcut⟩ := one_div_mem_arctanCut_of_seg hz
  have hI : τ ≠ I := fun h => by rw [h, norm_I] at hτ; exact lt_irrefl _ hτ
  have hI' : τ ≠ -I := fun h => by rw [h, norm_neg, norm_I] at hτ; exact lt_irrefl _ hτ
  have hre := abs_re_arctan_lt hτ
  have hre2 : |(2 * arctan τ).re| < π / 2 := by
    rw [show (2 * arctan τ).re = 2 * (arctan τ).re by simp, abs_mul, abs_two]; linarith
  rw [abs_lt] at hre2
  have htan : tan (2 * arctan τ) = 1 / z := by
    rw [tan_two_mul, tan_arctan hI hI', show (1 : ℂ) - τ ^ 2 = 2 * z * τ by linear_combination hp]
    field_simp
  rw [arccotD, arctanD_eq (mem_arctanCut_of_norm_lt hτ), arctanD_eq hcut, ← htan,
    arctan_tan _ hre2.1 hre2.2.le]
  intro h
  have := congrArg re h
  rw [show ((π : ℂ) / 2).re = π / 2 by simp] at this
  linarith [hre2.2]

/-! ### 4.25.5 -/

theorem expK_self {ε a τ : ℂ} (hτ0 : τ ≠ 0) :
    expK ε a τ τ = exp (-(ε * a) * expKappa τ 0) * (1 + τ ^ 2) ^ ((-1 / 2 : ℝ) : ℂ) := by
  rw [expK, div_self hτ0, sub_self, zero_mul, expC_zero, mul_one, sq]

theorem expG_limit {ε a τ : ℂ} (hε : ε ^ 2 = 1) (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) :
    Tendsto (fun n : ℕ => (n ! : ℂ)⁻¹ * iteratedDeriv n (expG ε a τ) 0 * τ ^ n /
      (arcsinCoeff n : ℂ)) atTop (𝓝 (expK ε a τ τ)) := by
  have hpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ0
  have hR : ‖τ‖ < 1 / ‖τ‖ := by rw [lt_div_iff₀ hpos]; nlinarith
  have hball : ∀ t ∈ Metric.ball (0 : ℂ) (1 / ‖τ‖), ‖t‖ * ‖τ‖ < 1 := fun t ht => by
    rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hpos] at ht; exact ht
  exact darboux_limit hτ0 hR
    (fun t ht => (differentiableAt_expK hτ (hball t ht)).differentiableWithinAt)
    (fun t ht => (differentiableAt_expM hτ (hball t ht)).differentiableWithinAt)
    (fun t ht => (hasDerivAt_expG hτ (by simpa using ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => expG_decomp hε hτ ht)

/-- **DLMF 4.25.5**: `e^{2a arccot z} = 1 + 2a/(z − a + (a² + 1)/(3z + (a² + 4)/(5z + ⋯)))` for
every complex `a` and `z ∉ [−i, i]` (`arccot z = arctan(1/z)`, principal value). -/
theorem dlmf_4_25_5 (a : ℂ) {z : ℂ} (hz : ∀ y : ℝ, |y| ≤ 1 → z ≠ I * y) :
    (∀ᶠ r in atTop, cfB (expCFa a) (expCFb a z) r ≠ 0) ∧
      Tendsto (fun r => cfA (expCFa a) (expCFb a z) r / cfB (expCFa a) (expCFb a z) r) atTop
        (𝓝 (exp (2 * a * arccotD z))) := by
  obtain ⟨-, hτ, hτ0⟩ := expTau_spec hz
  have hB := (expG_limit (ε := 1) (a := a) (by norm_num) hτ hτ0).congr
    (fun n => by rw [(iteratedDeriv_expG_eq hz n).1])
  have hA := (expG_limit (ε := -1) (a := a) (by norm_num) hτ hτ0).congr
    (fun n => by rw [(iteratedDeriv_expG_eq hz n).2])
  set τ := expTau z
  have hsq : 1 + τ ^ 2 ≠ 0 := fun h => by
    have : ‖τ ^ 2‖ = 1 := by rw [show τ ^ 2 = -1 by linear_combination h, norm_neg, norm_one]
    rw [norm_pow] at this
    nlinarith [norm_nonneg τ]
  have hc : (1 + τ ^ 2) ^ ((-1 / 2 : ℝ) : ℂ) ≠ 0 := fun h => hsq ((cpow_eq_zero_iff _ _).mp h).1
  have hK1 : expK 1 a τ τ ≠ 0 := by rw [expK_self hτ0]; exact mul_ne_zero (exp_ne_zero _) hc
  have hf : ∀ n : ℕ, (n ! : ℂ)⁻¹ * τ ^ n / (arcsinCoeff n : ℂ) ≠ 0 := fun n =>
    div_ne_zero (mul_ne_zero (inv_ne_zero (by exact_mod_cast (Nat.factorial_pos n).ne'))
      (pow_ne_zero _ hτ0)) (by exact_mod_cast (arcsinCoeff_pos n).ne')
  have hre : ∀ (n : ℕ) (X : ℂ), (n ! : ℂ)⁻¹ * X * τ ^ n / (arcsinCoeff n : ℂ) =
      X * ((n ! : ℂ)⁻¹ * τ ^ n / (arcsinCoeff n : ℂ)) := fun n X => by ring
  refine ⟨(hB.eventually_ne hK1).mono fun n hn h => hn (by rw [h]; ring), ?_⟩
  have hlim := hA.div hB hK1
  have hval : expK (-1) a τ τ / expK 1 a τ τ = exp (2 * a * arccotD z) := by
    rw [expK_self hτ0, expK_self hτ0, mul_div_mul_right _ _ hc, ← exp_sub, expKappa_zero,
      arctanInt_eq hτ, ← two_mul_arctanD_expTau hz]
    congr 1; ring
  rw [hval] at hlim
  refine hlim.congr fun n => ?_
  simp only [Pi.div_apply, hre n]
  exact mul_div_mul_right _ _ (hf n)

/-! ### 4.25.2 -/

/-- `a₁ = a t`, `aᵣ = ((r − 1)² − a²) t²` (`t = tan z`); `bᵣ = 2r − 1` (`lg2b`). -/
noncomputable def tanACFa (a t : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then a * t else (((r - 1 : ℕ) : ℂ) ^ 2 - a ^ 2) * t ^ 2

/-- With `w = 1/t`, `c = ia`: `2i wʳ Pᵣ = Aᵣ − Bᵣ` and `2 wʳ Qᵣ = Aᵣ + Bᵣ`, where `Pᵣ/Qᵣ` are the
convergents of 4.25.2 and `Aᵣ/Bᵣ` those of 4.25.5. -/
theorem tanA_cf_eq (a t w : ℂ) (hwt : w * t = 1) (r : ℕ) :
    2 * I * w ^ r * cfA (tanACFa a t) (lg2b t) r =
        cfA (expCFa (I * a)) (expCFb (I * a) w) r - cfB (expCFa (I * a)) (expCFb (I * a) w) r ∧
      2 * w ^ r * cfB (tanACFa a t) (lg2b t) r =
        cfA (expCFa (I * a)) (expCFb (I * a) w) r + cfB (expCFa (I * a)) (expCFb (I * a) w) r := by
  obtain ⟨i0, i1, j0, j1⟩ := expCF_init (I * a) w
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 =>
      rw [i0, j0]
      simp [cfA, cfB, cfP, cfQ, lg2b]
      norm_num
    | 1 =>
      rw [i1, j1]
      simp [cfA, cfB, cfP, cfQ, lg2b, tanACFa]
      constructor
      · linear_combination 2 * I * a * hwt
      · ring
    | r + 2 =>
      obtain ⟨h0a, h0b⟩ := ih r (by omega)
      obtain ⟨h1a, h1b⟩ := ih (r + 1) (by omega)
      obtain ⟨eB, eA⟩ := expCF_rec (I * a) w r
      have ha : tanACFa a t (r + 2) = (((r : ℂ) + 1) ^ 2 - a ^ 2) * t ^ 2 := by
        simp only [tanACFa, show r + 2 ≠ 1 by omega, ↓reduceIte, show r + 2 - 1 = r + 1 by omega]
        push_cast; ring
      have hb : lg2b t (r + 2) = 2 * (r : ℂ) + 3 := by
        simp only [lg2b, show r + 2 ≠ 0 by omega, ↓reduceIte]; push_cast; ring
      rw [eA, eB, cfA_succ_succ, cfB_succ_succ, ha, hb]
      have hI2 : (I * a) ^ 2 = -a ^ 2 := by rw [mul_pow, I_sq]; ring
      rw [hI2]
      constructor
      · linear_combination (2 * (r : ℂ) + 3) * w * h1a + ((r + 1) ^ 2 - a ^ 2) * h0a +
          ((r + 1) ^ 2 - a ^ 2) * 2 * I * w ^ r * cfA (tanACFa a t) (lg2b t) r * (w * t + 1) * hwt
      · linear_combination (2 * (r : ℂ) + 3) * w * h1b + ((r + 1) ^ 2 - a ^ 2) * h0b +
          ((r + 1) ^ 2 - a ^ 2) * 2 * w ^ r * cfB (tanACFa a t) (lg2b t) r * (w * t + 1) * hwt

theorem exp_two_mul_I_ne_nonpos {z : ℂ} (hz : |z.re| < π / 2) {q : ℝ} (hq : q ≤ 0) :
    exp (2 * z * I) ≠ q := by
  intro h
  have him := congrArg im h
  have hre := congrArg re h
  rw [exp_im, ofReal_im] at him
  rw [exp_re, ofReal_re] at hre
  have hi : (2 * z * I).im = 2 * z.re := by simp
  have hr : (2 * z * I).re = -(2 * z.im) := by simp
  rw [hi] at him
  rw [hi, hr] at hre
  rw [abs_lt] at hz
  have hs : Real.sin (2 * z.re) = 0 :=
    (mul_eq_zero.mp him).resolve_left (Real.exp_pos _).ne'
  have h0 : 2 * z.re = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hs
  rw [h0, Real.cos_zero, mul_one] at hre
  linarith [Real.exp_pos (-(2 * z.im))]

/-- On the strip `|ℜz| < ½π`, `z ≠ 0`, the point `cot z` is off `[−i, i]`, and
`arccot(cot z) = z`. -/
theorem cot_strip {z : ℂ} (hz : |z.re| < π / 2) (hz0 : z ≠ 0) :
    (∀ y : ℝ, |y| ≤ 1 → 1 / tan z ≠ I * y) ∧ arccotD (1 / tan z) = z := by
  have hc : cos z ≠ 0 := by
    have := abs_lt.mp hz
    refine cos_ne_zero_of_arctan_bounds (fun h => ?_) this.1 this.2.le
    rw [h] at this
    have : (π / 2 : ℂ).re = π / 2 := by simp
    linarith [this ▸ (abs_lt.mp hz).2]
  have hseg : ∀ y : ℝ, |y| ≤ 1 → 1 / tan z ≠ I * y := by
    intro y hy h
    rw [tan_eq_sin_div_cos, one_div_div] at h
    by_cases hs : sin z = 0
    · obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp hs
      have hre : z.re = k * π := by rw [hk]; simp
      rw [hre, abs_mul, abs_of_pos Real.pi_pos] at hz
      have hk0 : k = 0 := by
        by_contra hk0
        have : (1 : ℝ) ≤ |(k : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
        nlinarith [Real.pi_pos]
      exact hz0 (by rw [hk, hk0]; simp)
    rw [div_eq_iff hs] at h
    rw [cos, sin] at h
    set E := exp (z * I)
    set F := exp (-z * I)
    have hEF : E * F = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
    have hE2 : exp (2 * z * I) = E * E := by rw [← exp_add]; ring_nf
    have h' : (E + F) / 2 = -(y : ℂ) * (F - E) / 2 := by
      rw [h]; ring_nf; rw [I_sq]; ring
    have key : E * E * (1 - y) + (1 + y) = 0 := by
      linear_combination 2 * E * h' - (1 + (y : ℂ)) * hEF
    obtain ⟨hy1, hy2⟩ := abs_le.mp hy
    have hy3 : y ≠ 1 := by
      rintro rfl
      norm_num at key
    have hy4 : 0 < 1 - y := by rcases hy2.lt_or_eq with h | h <;> [linarith; exact absurd h hy3]
    refine exp_two_mul_I_ne_nonpos hz (q := -(1 + y) / (1 - y))
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hy4.le) ?_
    have hy5 : (1 : ℂ) - y ≠ 0 := by exact_mod_cast hy4.ne'
    rw [hE2]
    push_cast
    field_simp
    linear_combination key
  refine ⟨hseg, ?_⟩
  obtain ⟨-, hcut⟩ := one_div_mem_arctanCut_of_seg hseg
  rw [one_div_one_div] at hcut
  rw [arccotD, one_div_one_div, arctanD_eq hcut]
  have := abs_lt.mp hz
  refine arctan_tan (fun h => ?_) this.1 this.2.le
  rw [h] at this
  have : (π / 2 : ℂ).re = π / 2 := by simp
  linarith [this ▸ (abs_lt.mp hz).2]

/-- `z = 0`: every convergent of 4.25.2 is `0/Qᵣ` with `Qᵣ ≠ 0`. -/
theorem tanA_cf_zero (a : ℂ) (r : ℕ) :
    cfA (tanACFa a 0) (lg2b 0) r = 0 ∧ cfB (tanACFa a 0) (lg2b 0) r ≠ 0 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [cfA, cfB, cfP, cfQ, lg2b]
    | 1 => simp [cfA, cfB, cfP, cfQ, lg2b, tanACFa]; norm_num
    | r + 2 =>
      have ha : tanACFa a 0 (r + 2) = 0 := by simp [tanACFa]
      have hb : lg2b (0 : ℂ) (r + 2) = 2 * (r : ℂ) + 3 := by
        simp only [lg2b, show r + 2 ≠ 0 by omega, ↓reduceIte]; push_cast; ring
      obtain ⟨h1a, h1b⟩ := ih (r + 1) (by omega)
      rw [cfA_succ_succ, cfB_succ_succ, ha, hb, h1a]
      refine ⟨by ring, ?_⟩
      rw [zero_mul, add_zero]
      exact mul_ne_zero (by norm_cast) h1b

theorem tan_eq_exp_ratio (u : ℂ) (hc : cos u ≠ 0) :
    exp (2 * (I * u)) + 1 ≠ 0 ∧ tan u = -I * (exp (2 * (I * u)) - 1) / (exp (2 * (I * u)) + 1) := by
  set E := exp (u * I)
  set F := exp (-u * I)
  have hEF : E * F = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have hE2 : exp (2 * (I * u)) = E * E := by rw [← exp_add]; ring_nf
  have hc' : E + F ≠ 0 := fun h => hc (by rw [cos]; simp [E, F] at h ⊢; rw [h])
  have hg : E * E + 1 ≠ 0 := by
    rw [show E * E + 1 = E * (E + F) by linear_combination -hEF]
    exact mul_ne_zero (exp_ne_zero _) hc'
  rw [hE2]
  refine ⟨hg, ?_⟩
  rw [tan_eq_sin_div_cos, sin, cos, div_eq_div_iff (by simpa [E, F] using
    (div_ne_zero hc' two_ne_zero)) hg]
  change (F - E) * I / 2 * (E * E + 1) = -I * (E * E - 1) * ((E + F) / 2)
  linear_combination E * I * hEF

/-- **DLMF 4.25.2**: `tan(az) = a tan z/(1 + (1 − a²)tan²z/(3 + (4 − a²)tan²z/(5 + ⋯)))` for
complex `a` and `|ℜz| < ½π`, `az ≠ ±½π, ±(3/2)π, …`. -/
theorem dlmf_4_25_2 (a : ℂ) {z : ℂ} (hz : |z.re| < π / 2)
    (haz : ∀ k : ℤ, a * z ≠ (2 * k + 1) * π / 2) :
    (∀ᶠ r in atTop, cfB (tanACFa a (tan z)) (lg2b (tan z)) r ≠ 0) ∧
      Tendsto (fun r => cfA (tanACFa a (tan z)) (lg2b (tan z)) r /
        cfB (tanACFa a (tan z)) (lg2b (tan z)) r) atTop (𝓝 (tan (a * z))) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [tan_zero, mul_zero, tan_zero]
    refine ⟨Eventually.of_forall fun r => (tanA_cf_zero a r).2, ?_⟩
    exact tendsto_const_nhds.congr fun r => by rw [(tanA_cf_zero a r).1, zero_div]
  obtain ⟨hseg, hcot⟩ := cot_strip hz hz0
  set t := tan z
  set w := 1 / t
  have ht0 : t ≠ 0 := fun h => hseg 0 (by simp) (by simp [w, h])
  have hwt : w * t = 1 := by simp [w, ht0]
  have hw0 : w ≠ 0 := by simp [w, ht0]
  obtain ⟨hB5, hT5⟩ := dlmf_4_25_5 (I * a) hseg
  rw [hcot] at hT5
  have hc : cos (a * z) ≠ 0 := fun h => by
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp h
    exact haz k hk
  obtain ⟨hg1, htan⟩ := tan_eq_exp_ratio (a * z) hc
  rw [show 2 * (I * a) * z = 2 * (I * (a * z)) by ring] at hT5
  set g := exp (2 * (I * (a * z)))
  have hlim := ((hT5.sub_const 1).const_mul (-I)).div (hT5.add_const 1) hg1
  rw [← htan] at hlim
  have hev := hB5.and ((hT5.add_const 1).eventually_ne hg1)
  set A := fun r => cfA (expCFa (I * a)) (expCFb (I * a) w) r
  set B := fun r => cfB (expCFa (I * a)) (expCFb (I * a) w) r
  have hQ : ∀ r, B r ≠ 0 → A r / B r + 1 ≠ 0 →
      cfB (tanACFa a t) (lg2b t) r ≠ 0 ∧
        cfA (tanACFa a t) (lg2b t) r / cfB (tanACFa a t) (lg2b t) r =
          -I * (A r / B r - 1) / (A r / B r + 1) := by
    intro r hB hAB
    obtain ⟨hp, hq⟩ := tanA_cf_eq a t w hwt r
    have hwr : w ^ r ≠ 0 := pow_ne_zero _ hw0
    have hsum : A r + B r ≠ 0 := by
      rw [show A r + B r = B r * (A r / B r + 1) by field_simp]
      exact mul_ne_zero hB hAB
    have hq0 : cfB (tanACFa a t) (lg2b t) r ≠ 0 := fun h => by
      rw [h, mul_zero] at hq; exact hsum hq.symm
    refine ⟨hq0, ?_⟩
    have hp' : cfA (tanACFa a t) (lg2b t) r = (A r - B r) / (2 * I * w ^ r) := by
      rw [eq_div_iff (by simp [hwr])]; linear_combination hp
    have hq' : cfB (tanACFa a t) (lg2b t) r = (A r + B r) / (2 * w ^ r) := by
      rw [eq_div_iff (by simp [hwr])]; linear_combination hq
    rw [hp', hq']
    field_simp
    ring_nf
    rw [I_sq]
    ring
  refine ⟨hev.mono fun r hr => (hQ r hr.1 hr.2).1, ?_⟩
  refine (tendsto_congr' (hev.mono fun r hr => (hQ r hr.1 hr.2).2.symm)).mp hlim

end Azurite.DLMF
