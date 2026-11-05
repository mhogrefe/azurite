/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8Other

/-!
# DLMF §3.8(v): Zeros of analytic functions — Halley's rule

* 3.8.12 (`halleyStep`): `z_{n+1} = zₙ − f(zₙ)/(f′(zₙ) − f″(zₙ)f(zₙ)/(2f′(zₙ)))`, equivalently
  `zₙ − 2ff′/(2f′² − ff″)` (`halleyStep_eq`).
* "This is useful when `f(z)` satisfies a second-order linear differential equation because of
  the ease of computing `f″(zₙ)`" (`halleyStep_ode`): for `f″ + pf′ + qf = 0` the rule needs only
  `f`, `f′`.
* "The rule converges locally and is cubically convergent" (`dlmf_3_8_v_halley`): at a simple
  zero, for `f″` Lipschitz near `ζ`, with `|e_{n+1}| ≤ K |eₙ|³`; in particular for `f ∈ C³`
  (`dlmf_3_8_v_halley_of_contDiffAt`, real or complex) and for analytic `f`
  (`dlmf_3_8_v_halley_analytic`). Ingredients: the second-order Taylor bound `taylor2_bound`, the
  error identity `halley_error`, and `iter_of_cube_bound`.
* Initial approximations by the phase principle or Rouché's theorem (§1.10(iv)): see
  `dlmf_1_10_9`, `dlmf_1_10_9_phase`, `dlmf_1_10_iv_rouche`. The references (Fabijonas and Olver,
  Segura, Gil et al.) are not formalized.
-/

open Filter Topology Set Metric

namespace Azurite.DLMF

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **DLMF 3.8.12**: Halley's rule. -/
noncomputable def halleyStep (f : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  z - f z / (deriv f z - deriv (deriv f) z * f z / (2 * deriv f z))

/-- 3.8.12 as `z − 2ff′/(2f′² − ff″)` (where `f′(z) ≠ 0`). -/
theorem halleyStep_eq {f : 𝕜 → 𝕜} {z : 𝕜} (h1 : deriv f z ≠ 0) :
    halleyStep f z = z - 2 * f z * deriv f z / (2 * deriv f z ^ 2 - f z * deriv (deriv f) z) := by
  rw [halleyStep]
  congr 1
  have h3 : deriv f z - deriv (deriv f) z * f z / (2 * deriv f z) =
      (2 * deriv f z ^ 2 - f z * deriv (deriv f) z) / (2 * deriv f z) := by
    field_simp
  rw [h3, div_div_eq_mul_div]
  ring

/-- For `f″ + pf′ + qf = 0` (a second-order linear differential equation), Halley's rule needs
only `f` and `f′`: `z − f/(f′ + (pf′ + qf)f/(2f′))`. -/
theorem halleyStep_ode {f : 𝕜 → 𝕜} {z p q : 𝕜}
    (hode : deriv (deriv f) z + p * deriv f z + q * f z = 0) :
    halleyStep f z = z - f z / (deriv f z + (p * deriv f z + q * f z) * f z / (2 * deriv f z)) := by
  rw [halleyStep, show deriv (deriv f) z = -(p * deriv f z + q * f z) by
    linear_combination hode]
  ring

/-- Second-order Taylor bound: for `f″` `L`-Lipschitz on `B(ζ, r)` and `z ∈ B(ζ, r/6)`,
`|f(ζ) − f(z) − f′(z)(ζ − z) − f″(z)(ζ − z)²/2| ≤ L |ζ − z|³`. -/
theorem taylor2_bound {f : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 f z)
    (hf' : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 (deriv f) z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r,
      ‖deriv (deriv f) w - deriv (deriv f) z‖ ≤ L * ‖w - z‖) {z : 𝕜} (hz : ‖z - ζ‖ < r / 6) :
    ‖f ζ - f z - deriv f z * (ζ - z) - deriv (deriv f) z * (ζ - z) ^ 2 / 2‖ ≤
      L * ‖ζ - z‖ ^ 3 := by
  set s := closedBall z ‖ζ - z‖
  have hzs : z ∈ s := mem_closedBall_self (norm_nonneg _)
  have hζs : ζ ∈ s := by rw [mem_closedBall, dist_eq_norm]
  have hnear : ∀ w ∈ s, ‖w - ζ‖ < r / 3 := fun w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 : ‖w - ζ‖ ≤ ‖w - z‖ + ‖z - ζ‖ := by
      calc ‖w - ζ‖ = ‖(w - z) + (z - ζ)‖ := by abel_nf
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev ζ z] at hw
    linarith
  have hsub : ∀ w ∈ s, w ∈ ball ζ r := fun w hw => by
    rw [mem_ball, dist_eq_norm]; have := hnear w hw; linarith [norm_nonneg (z - ζ)]
  set c1 := deriv f z
  set c2 := deriv (deriv f) z
  set h : 𝕜 → 𝕜 := fun w => f w - c1 * w - c2 * (w - z) ^ 2 / 2
  have hh : ∀ w ∈ s, HasDerivWithinAt h (deriv f w - c1 - c2 * (w - z)) s w := fun w hw => by
    have hq : HasDerivAt (fun w : 𝕜 => (w - z) ^ 2) (2 * (w - z)) w := by
      have := ((hasDerivAt_id w).sub_const z).mul ((hasDerivAt_id w).sub_const z)
      convert this using 1
      · funext x; simp only [id, Pi.mul_apply]; ring
      · simp only [id]; ring
    exact ((((hf w (hsub w hw)).hasDerivAt.sub ((hasDerivAt_id w).const_mul c1)).sub
      ((hq.const_mul c2).div_const 2)).congr_deriv (by simp; ring)).hasDerivWithinAt
  have hmvt := (convex_closedBall z ‖ζ - z‖).norm_image_sub_le_of_norm_hasDerivWithin_le hh
    (C := L * ‖ζ - z‖ ^ 2) (fun w hw => by
      have := lip_taylor hL0 hf' hL (hnear z hzs) (hnear w hw)
      have hw' := hw
      rw [mem_closedBall, dist_eq_norm] at hw'
      calc ‖deriv f w - c1 - c2 * (w - z)‖ ≤ L * ‖w - z‖ ^ 2 := this
        _ ≤ L * ‖ζ - z‖ ^ 2 := by gcongr) hzs hζs
  have e : h ζ - h z = f ζ - f z - c1 * (ζ - z) - c2 * (ζ - z) ^ 2 / 2 := by
    simp only [h]; ring
  rw [e] at hmvt
  calc _ ≤ L * ‖ζ - z‖ ^ 2 * ‖ζ - z‖ := hmvt
    _ = L * ‖ζ - z‖ ^ 3 := by ring

/-- The error identity of Halley's rule: with `e = z − ζ` and the Taylor remainder `T`,
`(H(z) − ζ)(2f′² − ff″) = e³f″²/2 + eTf″ + 2Tf′`. -/
theorem halley_error {f : 𝕜 → 𝕜} {ζ z : 𝕜} (hζ : f ζ = 0) (h1 : deriv f z ≠ 0)
    (h2 : 2 * deriv f z ^ 2 - f z * deriv (deriv f) z ≠ 0) :
    halleyStep f z - ζ =
      ((z - ζ) ^ 3 * deriv (deriv f) z ^ 2 / 2 +
        (z - ζ) * (f ζ - f z - deriv f z * (ζ - z) - deriv (deriv f) z * (ζ - z) ^ 2 / 2) *
          deriv (deriv f) z +
        2 * (f ζ - f z - deriv f z * (ζ - z) - deriv (deriv f) z * (ζ - z) ^ 2 / 2) *
          deriv f z) / (2 * deriv f z ^ 2 - f z * deriv (deriv f) z) := by
  rw [halleyStep_eq h1, eq_div_iff h2, hζ]
  field_simp
  ring

/-- A cubic error bound on a ball gives local convergence and 3.8.3 with `p = 3`. -/
theorem iter_of_cube_bound {E : Type*} [NormedAddCommGroup E] {T : E → E} {ζ : E} {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (h : ∀ z ∈ ball ζ δ, ‖T z - ζ‖ ≤ K * ‖z - ζ‖ ^ 3) :
    ConvergesLocally T ζ ∧ ∃ δ' > 0, ∀ z₀ ∈ ball ζ δ',
      (∀ n, ‖T^[n + 1] z₀ - ζ‖ ≤ K * ‖T^[n] z₀ - ζ‖ ^ 3) ∧
      ((∀ n, T^[n] z₀ ≠ ζ) → IsCubicConv (fun n => T^[n] z₀) ζ) := by
  set δ' := min δ (min 1 (1 / (2 * K + 1)))
  have hδ' : 0 < δ' := lt_min hδ (lt_min one_pos (by positivity))
  have hc : ∀ z ∈ ball ζ δ', ‖T z - ζ‖ ≤ 1 / 2 * ‖z - ζ‖ := fun z hz => by
    have hz' : ‖z - ζ‖ < δ' := by rwa [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z - ζ‖ * (2 * K + 1) ≤ 1 := by
      have := hz'.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      rwa [le_div_iff₀ (by positivity)] at this
    have h1' : ‖z - ζ‖ ≤ 1 := hz'.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h2 := h z (ball_subset_ball (min_le_left _ _) hz)
    have hn := norm_nonneg (z - ζ)
    have h3 : K * ‖z - ζ‖ ^ 3 ≤ K * ‖z - ζ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hn h1' (by norm_num)) hK
    nlinarith
  have hmem : ∀ z ∈ ball ζ δ', T z ∈ ball ζ δ' := fun z hz => by
    have := hc z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    linarith [norm_nonneg (z - ζ)]
  have hit : ∀ z₀ ∈ ball ζ δ', ∀ n, T^[n] z₀ ∈ ball ζ δ' := fun z₀ hz n => by
    induction n with
    | zero => exact hz
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmem _ ih
  refine ⟨(convergesLocally_of_contract hδ' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hc).1,
    δ', hδ', fun z₀ hz => ?_⟩
  have hq : ∀ n, ‖T^[n + 1] z₀ - ζ‖ ≤ K * ‖T^[n] z₀ - ζ‖ ^ 3 := fun n => by
    rw [Function.iterate_succ_apply']
    exact h _ (ball_subset_ball (min_le_left _ _) (hit z₀ hz n))
  refine ⟨hq, fun hne => ⟨K + 1, Eventually.of_forall fun n => ?_⟩⟩
  have hpos : 0 < ‖T^[n] z₀ - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
  rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖T^[n + 1] z₀ - ζ‖ ≤ K * ‖T^[n] z₀ - ζ‖ ^ 3 := hq n
    _ < (K + 1) * ‖T^[n] z₀ - ζ‖ ^ 3 := by gcongr; linarith

/-- The cubic error bound of Halley's rule near a simple zero. -/
theorem halley_cube_ball {f : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hf : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 f z)
    (hf' : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 (deriv f) z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r,
      ‖deriv (deriv f) w - deriv (deriv f) z‖ ≤ L * ‖w - z‖)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ z ∈ ball ζ δ, ‖halleyStep f z - ζ‖ ≤ K * ‖z - ζ‖ ^ 3 := by
  have hζr : ζ ∈ ball ζ r := mem_ball_self hr
  set m := ‖deriv f ζ‖
  have hm : 0 < m := norm_pos_iff.mpr hd
  set B := ‖deriv (deriv f) ζ‖ + L * r
  have hB : 0 ≤ B := by positivity
  have e1 : ∀ᶠ z in 𝓝 ζ, ‖deriv f z - deriv f ζ‖ < m / 2 := by
    have := (hf' ζ hζr).continuousAt.tendsto
    exact (tendsto_iff_norm_sub_tendsto_zero.mp this).eventually (gt_mem_nhds (by positivity))
  have e2 : ∀ᶠ z in 𝓝 ζ, ‖f z‖ < m ^ 2 / (4 * (B + 1)) := by
    have := (hf ζ hζr).continuousAt.tendsto
    rw [hζ] at this
    have := (tendsto_iff_norm_sub_tendsto_zero.mp this).eventually (gt_mem_nhds
      (show (0 : ℝ) < m ^ 2 / (4 * (B + 1)) by positivity))
    simpa using this
  have e3 : ∀ᶠ z in 𝓝 ζ, z ∈ ball ζ (r / 6) := ball_mem_nhds ζ (by positivity)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (e1.and (e2.and e3))
  set C := B ^ 2 / 2 + L * r * B + 3 * L * m
  refine ⟨δ, hδ, C / (m ^ 2 / 4), by positivity, fun z hz => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hball hz
  have hz6 : ‖z - ζ‖ < r / 6 := by rwa [mem_ball, dist_eq_norm] at h3
  have hzr : z ∈ ball ζ r := by rw [mem_ball, dist_eq_norm]; linarith
  -- bounds at `z`
  have hd1 : m / 2 ≤ ‖deriv f z‖ := by
    have := norm_sub_norm_le (deriv f ζ) (deriv f z)
    rw [norm_sub_rev] at this; linarith
  have hd2 : ‖deriv f z‖ ≤ 3 * m / 2 := by
    have := norm_add_le (deriv f ζ) (deriv f z - deriv f ζ)
    rw [add_sub_cancel] at this
    linarith
  have hB2 : ‖deriv (deriv f) z‖ ≤ B := by
    have h := hL z hzr ζ hζr
    have := norm_add_le (deriv (deriv f) ζ) (deriv (deriv f) z - deriv (deriv f) ζ)
    rw [add_sub_cancel] at this
    have hzr' : ‖z - ζ‖ ≤ r := by linarith [norm_nonneg (z - ζ)]
    have : L * ‖z - ζ‖ ≤ L * r := mul_le_mul_of_nonneg_left hzr' hL0
    simp only [B]; linarith
  have hfz : ‖f z‖ * B ≤ m ^ 2 / 4 := by
    have h' : ‖f z‖ ≤ m ^ 2 / (4 * (B + 1)) := h2.le
    rw [le_div_iff₀ (by positivity)] at h'
    nlinarith [norm_nonneg (f z)]
  have hD : m ^ 2 / 4 ≤ ‖2 * deriv f z ^ 2 - f z * deriv (deriv f) z‖ := by
    have := norm_sub_norm_le (2 * deriv f z ^ 2) (f z * deriv (deriv f) z)
    rw [norm_mul, norm_mul, norm_pow, RCLike.norm_two] at this
    have hff : ‖f z‖ * ‖deriv (deriv f) z‖ ≤ m ^ 2 / 4 :=
      (mul_le_mul_of_nonneg_left hB2 (norm_nonneg _)).trans hfz
    nlinarith
  have hD0 : 2 * deriv f z ^ 2 - f z * deriv (deriv f) z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hD; have : 0 < m ^ 2 / 4 := by positivity
    linarith
  have hd0 : deriv f z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hd1; linarith
  -- the error
  have hT := taylor2_bound hL0 hf hf' hL hz6
  set T := f ζ - f z - deriv f z * (ζ - z) - deriv (deriv f) z * (ζ - z) ^ 2 / 2
  rw [halley_error hζ hd0 hD0, norm_div]
  have hT' : ‖T‖ ≤ L * ‖z - ζ‖ ^ 3 := by rwa [norm_sub_rev ζ z] at hT
  set e := ‖z - ζ‖
  have he : 0 ≤ e := norm_nonneg _
  have her : e ≤ r := by linarith
  have hN : ‖(z - ζ) ^ 3 * deriv (deriv f) z ^ 2 / 2 + (z - ζ) * T * deriv (deriv f) z +
      2 * T * deriv f z‖ ≤ C * e ^ 3 := by
    refine norm_add₃_le.trans ?_
    simp only [norm_div, norm_mul, norm_pow, RCLike.norm_two]
    have a1 : e ^ 3 * ‖deriv (deriv f) z‖ ^ 2 / 2 ≤ e ^ 3 * B ^ 2 / 2 := by gcongr
    have a2 : e * ‖T‖ * ‖deriv (deriv f) z‖ ≤ e * (L * e ^ 3) * B := by gcongr
    have a3 : 2 * ‖T‖ * ‖deriv f z‖ ≤ 2 * (L * e ^ 3) * (3 * m / 2) := by gcongr
    have a4 : e * (L * e ^ 3) * B ≤ r * (L * e ^ 3) * B := by gcongr
    simp only [C]
    nlinarith
  rw [div_le_iff₀ (by linarith [show 0 < m ^ 2 / 4 by positivity] : 0 <
    ‖2 * deriv f z ^ 2 - f z * deriv (deriv f) z‖)]
  calc _ ≤ C * e ^ 3 := hN
    _ = C / (m ^ 2 / 4) * e ^ 3 * (m ^ 2 / 4) := by field_simp
    _ ≤ C / (m ^ 2 / 4) * e ^ 3 * ‖2 * deriv f z ^ 2 - f z * deriv (deriv f) z‖ := by
      gcongr

/-- **DLMF §3.8(v)**: Halley's rule 3.8.12 "converges locally and is cubically convergent" at a
simple zero `ζ` (for `f″` Lipschitz near `ζ`). The errors satisfy `|e_{n+1}| ≤ K |eₙ|³`, and 3.8.3
holds with `p = 3` whenever no iterate lands exactly on `ζ`. -/
theorem dlmf_3_8_v_halley {f : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hf : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 f z)
    (hf' : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 (deriv f) z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r,
      ‖deriv (deriv f) w - deriv (deriv f) z‖ ≤ L * ‖w - z‖)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ConvergesLocally (halleyStep f) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(halleyStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(halleyStep f)^[n] z₀ - ζ‖ ^ 3) ∧
      ((∀ n, (halleyStep f)^[n] z₀ ≠ ζ) → IsCubicConv (fun n => (halleyStep f)^[n] z₀) ζ) := by
  obtain ⟨δ, hδ, K, hK, hb⟩ := halley_cube_ball hr hL0 hf hf' hL hζ hd
  obtain ⟨hloc, δ', hδ', hit⟩ := iter_of_cube_bound hδ hK hb
  exact ⟨hloc, δ', hδ', K, hK, hit⟩

/-- `dlmf_3_8_v_halley` for `f` of class `C³` near `ζ`. -/
theorem dlmf_3_8_v_halley_of_contDiffAt {f : 𝕜 → 𝕜} {ζ : 𝕜} (hf : ContDiffAt 𝕜 3 f ζ)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ConvergesLocally (halleyStep f) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(halleyStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(halleyStep f)^[n] z₀ - ζ‖ ^ 3) ∧
      ((∀ n, (halleyStep f)^[n] z₀ ≠ ζ) → IsCubicConv (fun n => (halleyStep f)^[n] z₀) ζ) := by
  have h2 : ContDiffAt 𝕜 2 (deriv f) ζ :=
    (hf.fderiv_right (m := 2) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : 𝕜)))
  have h1 : ContDiffAt 𝕜 1 (deriv (deriv f)) ζ :=
    (h2.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : 𝕜)))
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hev : ∀ᶠ z in 𝓝 ζ, DifferentiableAt 𝕜 f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hev' : ∀ᶠ z in 𝓝 ζ, DifferentiableAt 𝕜 (deriv f) z :=
    (h2.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht (hev.and hev'))
  refine dlmf_3_8_v_halley hr K.coe_nonneg (fun z hz => (hrt hz).2.1)
    (fun z hz => (hrt hz).2.2) (fun w hw z hz => ?_) hζ hd
  have := hK.dist_le_mul w (hrt hw).1 z (hrt hz).1
  rwa [dist_eq_norm, dist_eq_norm] at this

/-- `dlmf_3_8_v_halley` for an analytic function `f` with a simple zero `ζ`. -/
theorem dlmf_3_8_v_halley_analytic {f : ℂ → ℂ} {ζ : ℂ} (hf : AnalyticAt ℂ f ζ)
    (hζ : f ζ = 0) (hd : deriv f ζ ≠ 0) :
    ConvergesLocally (halleyStep f) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(halleyStep f)^[n + 1] z₀ - ζ‖ ≤ K * ‖(halleyStep f)^[n] z₀ - ζ‖ ^ 3) ∧
      ((∀ n, (halleyStep f)^[n] z₀ ≠ ζ) → IsCubicConv (fun n => (halleyStep f)^[n] z₀) ζ) :=
  dlmf_3_8_v_halley_of_contDiffAt hf.contDiffAt hζ hd

end Azurite.DLMF
