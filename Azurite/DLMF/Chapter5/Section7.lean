/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section6Reciprocal
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# DLMF §5.7(ii) and 5.7.4: series for `ψ`

Formalizations of <https://dlmf.nist.gov/5.7> (part 1).

* 5.7.6, `ψ(z) = −γ + ∑_{k≥0} (1/(k + 1) − 1/(k + z)) = −γ − 1/z + ∑_{k≥1} z/(k(k + z))`,
  `z ≠ 0, −1, −2, …` (`dlmf_5_7_6`, `dlmf_5_7_6_alt`): the series is analytic off the poles
  (`analyticOnNhd_psiSeries`, a uniform `1/(k + 1)²` bound on small balls,
  `exists_norm_add_nat_ge`), equals `ψ + γ` on `(0, ∞)` (the limit form `tendsto_psiR_series`,
  §5.4), hence everywhere by the identity theorem.
* 5.7.7, `ψ(½ + ½z) − ψ(½z) = 2 ∑_{k≥0} (−1)ᵏ/(k + z)` (`dlmf_5_7_7`; the series converges
  conditionally, so this is the limit of its partial sums), `z ≠ 0, −1, −2, …`.
* 5.7.8, `ℑψ(1 + iy) = ∑_{k≥1} y/(k² + y²)` (`dlmf_5_7_8`).
* 5.7.4, `ψ(1 + z) = −γ + ∑_{k≥2} (−1)ᵏ ζ(k) z^{k−1}`, `|z| < 1` (`dlmf_5_7_4`; `ζ` is Mathlib's
  `riemannZeta`), by expanding each term of 5.7.6 geometrically and summing over `ℕ × ℕ`.

5.7.5 is in `Section7Zeta.lean`, 5.7.3 in `Section7Log.lean`, 5.7.1–5.7.2 in `Section7Recip.lean`.
-/

open Complex Filter Topology Set Finset
open scoped Real

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- The terms `1/(k + 1) − 1/(k + z)` of 5.7.6. -/
noncomputable def psiTerm (k : ℕ) (z : ℂ) : ℂ := 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)

/-- Near a point off the poles, `|w + k| ≥ c(k + 1)` uniformly. -/
theorem exists_norm_add_nat_ge {z₀ : ℂ} (hz₀ : z₀ ∉ gammaPoles) :
    ∃ r > 0, ∃ c > 0, ∀ w ∈ Metric.ball z₀ r, ∀ k : ℕ, c * ((k : ℝ) + 1) ≤ ‖w + k‖ := by
  have hne : gammaPoles.Nonempty := ⟨0, 0, by simp⟩
  set δ := Metric.infDist z₀ gammaPoles with hδdef
  have hδ : 0 < δ := (isClosed_gammaPoles.notMem_iff_infDist_pos hne).mp hz₀
  set R := ‖z₀‖ + δ with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨δ / 2, by positivity, min (δ / (4 * (R + 1))) (1 / 2), by positivity, fun w hw k => ?_⟩
  have hw' : dist w z₀ < δ / 2 := hw
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : δ / 2 ≤ ‖w + k‖ := by
    have hmem : (-(k : ℂ)) ∈ gammaPoles := ⟨k, rfl⟩
    have hle := Metric.infDist_le_dist_of_mem (x := z₀) hmem
    have htri := dist_triangle z₀ w (-(k : ℂ))
    rw [dist_eq_norm w (-(k : ℂ)), sub_neg_eq_add] at htri
    rw [← hδdef] at hle
    linarith [dist_comm z₀ w]
  have h2 : (k : ℝ) - R ≤ ‖w + k‖ := by
    have hw1 : ‖w‖ ≤ ‖z₀‖ + δ / 2 := by
      have := norm_sub_norm_le w z₀
      rw [← dist_eq_norm] at this
      linarith
    have hk : ‖(k : ℂ)‖ = k := by simp
    have := norm_sub_le (w + k) w
    rw [add_sub_cancel_left, hk] at this
    linarith
  rcases le_or_gt (k : ℝ) (2 * R + 1) with hk | hk
  · calc min (δ / (4 * (R + 1))) (1 / 2) * ((k : ℝ) + 1)
        ≤ δ / (4 * (R + 1)) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ δ / (4 * (R + 1)) * (2 * R + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ / 2 := by field_simp; ring
      _ ≤ ‖w + k‖ := h1
  · calc min (δ / (4 * (R + 1))) (1 / 2) * ((k : ℝ) + 1) ≤ 1 / 2 * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ (k : ℝ) - R := by linarith
      _ ≤ ‖w + k‖ := h2

theorem summable_inv_succ_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

theorem psiTerm_eq {k : ℕ} {w : ℂ} (hw : (k : ℂ) + w ≠ 0) :
    psiTerm k w = (w - 1) / (((k : ℂ) + 1) * ((k : ℂ) + w)) := by
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  unfold psiTerm
  field_simp
  ring

/-- A uniform bound on a small ball around a point off the poles. -/
theorem exists_psiTerm_bound {z₀ : ℂ} (hz₀ : z₀ ∉ gammaPoles) :
    ∃ r > 0, ∃ M : ℝ, ∀ w ∈ Metric.ball z₀ r, ∀ k : ℕ,
      ‖psiTerm k w‖ ≤ M * (1 / ((k : ℝ) + 1) ^ 2) ∧ (k : ℂ) + w ≠ 0 := by
  obtain ⟨r, hr, c, hc, h⟩ := exists_norm_add_nat_ge hz₀
  refine ⟨r, hr, (‖z₀‖ + r + 1) / c, fun w hw k => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hwk := h w hw k
  have hpos : 0 < ‖w + k‖ := lt_of_lt_of_le (by positivity) hwk
  have hne : (k : ℂ) + w ≠ 0 := by
    rw [add_comm]; exact norm_pos_iff.mp hpos
  refine ⟨?_, hne⟩
  rw [psiTerm_eq hne, norm_div, norm_mul, add_comm (k : ℂ) w]
  have hk1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  rw [hk1]
  have hw1 : ‖w - 1‖ ≤ ‖z₀‖ + r + 1 := by
    have := norm_sub_le w 1
    have h2 : ‖w‖ ≤ ‖z₀‖ + r := by
      have := norm_sub_norm_le w z₀
      rw [← dist_eq_norm] at this
      have : dist w z₀ < r := hw
      linarith
    simp at this
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc ‖w - 1‖ ≤ ‖z₀‖ + r + 1 := hw1
    _ = (‖z₀‖ + r + 1) / c * (1 / ((k : ℝ) + 1) ^ 2) * (((k : ℝ) + 1) * (c * ((k : ℝ) + 1))) := by
        field_simp
    _ ≤ (‖z₀‖ + r + 1) / c * (1 / ((k : ℝ) + 1) ^ 2) * (((k : ℝ) + 1) * ‖w + k‖) := by
        gcongr

theorem summable_psiTerm {z : ℂ} (hz : z ∉ gammaPoles) : Summable fun k => psiTerm k z := by
  obtain ⟨r, hr, M, h⟩ := exists_psiTerm_bound hz
  exact Summable.of_norm_bounded (summable_inv_succ_sq.mul_left M)
    fun k => (h z (Metric.mem_ball_self hr) k).1

/-- `∑_{k≥0} (1/(k + 1) − 1/(k + z))`. -/
noncomputable def psiSeries (z : ℂ) : ℂ := ∑' k, psiTerm k z

theorem analyticOnNhd_psiSeries : AnalyticOnNhd ℂ psiSeries gammaPolesᶜ := by
  intro z₀ hz₀
  obtain ⟨r, hr, M, h⟩ := exists_psiTerm_bound hz₀
  have hd : DifferentiableOn ℂ psiSeries (Metric.ball z₀ r) := by
    refine differentiableOn_tsum_of_summable_norm (summable_inv_succ_sq.mul_left M)
      (fun k => ?_) Metric.isOpen_ball fun k w hw => (h w hw k).1
    intro w hw
    have hne := (h w hw k).2
    unfold psiTerm
    exact ((differentiableAt_const _).sub ((differentiableAt_const _).div
      (by fun_prop) hne)).differentiableWithinAt
  exact hd.analyticAt (Metric.ball_mem_nhds z₀ hr)

/-- On `(0, ∞)`: `∑ (1/(k + 1) − 1/(k + x)) = ψ(x) + γ`. -/
theorem psiSeries_ofReal {x : ℝ} (hx : 0 < x) : psiSeries x = (psiR x + γ : ℝ) := by
  have hp : (x : ℂ) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by simpa using hx)
  have hS := (summable_psiTerm hp).hasSum.tendsto_sum_nat
  have hR : Tendsto (fun N : ℕ => ∑ k ∈ range N, psiTerm k x) atTop (𝓝 ((psiR x + γ : ℝ) : ℂ)) := by
    have h1 := (tendsto_psiR_series hx).add Real.tendsto_harmonic_sub_log
    have h2 := (continuous_ofReal.tendsto _).comp h1
    refine h2.congr fun N => ?_
    simp only [Function.comp, psiTerm, harmonic]
    push_cast
    rw [sum_sub_distrib]
    simp only [one_div]
    rw [show ∑ k ∈ range N, ((x : ℂ) + k)⁻¹ = ∑ k ∈ range N, ((k : ℂ) + x)⁻¹ from
      sum_congr rfl fun k _ => by rw [add_comm]]
    ring
  exact tendsto_nhds_unique hS hR

/-- **DLMF 5.7.6**: `ψ(z) = −γ + ∑_{k=0}^∞ (1/(k + 1) − 1/(k + z))`, `z ≠ 0, −1, −2, …`. -/
theorem dlmf_5_7_6 {z : ℂ} (hz : z ∉ gammaPoles) :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + z)) (digamma z + γ) := by
  have heq : Set.EqOn digamma (fun w => psiSeries w - γ) gammaPolesᶜ := by
    refine dlmf_5_2_2_analytic.eqOn_of_preconnected_of_frequently_eq
      (analyticOnNhd_psiSeries.sub analyticOnNhd_const) isPreconnected_compl_gammaPoles
      (z₀ := 1) (not_mem_gammaPoles_of_re_pos (by simp)) ?_
    have hlim : Tendsto (fun j : ℕ => (((1 : ℝ) + 1 / ((j : ℝ) + 1) : ℝ) : ℂ)) atTop
        (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
      · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
        rw [add_zero] at h0
        have := (continuous_ofReal.tendsto 1).comp h0
        rw [ofReal_one] at this
        exact this
      · intro h
        have := ofReal_injective (h.trans ofReal_one.symm)
        have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        linarith
    refine hlim.frequently (Frequently.of_forall fun j => ?_)
    have hx : (0 : ℝ) < 1 + 1 / ((j : ℝ) + 1) := by positivity
    rw [psiSeries_ofReal hx, digamma_ofReal]
    push_cast
    ring
  have h := heq hz
  simp only at h
  have hs := (summable_psiTerm hz).hasSum
  rw [show digamma z + γ = psiSeries z by rw [h]; ring]
  exact hs

/-- **DLMF 5.7.6**, first form: `ψ(z) = −γ − 1/z + ∑_{k=1}^∞ z/(k(k + z))`. -/
theorem dlmf_5_7_6_alt {z : ℂ} (hz : z ∉ gammaPoles) :
    HasSum (fun k : ℕ => z / (((k : ℂ) + 1) * ((k : ℂ) + 1 + z))) (digamma z + γ + 1 / z) := by
  have h0 := dlmf_5_7_6 hz
  have hz0 : z ≠ 0 := fun h => hz ⟨0, by simp [h]⟩
  have h1 := (hasSum_nat_add_iff' 1).mpr h0
  simp only [sum_range_one, Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at h1
  -- the telescoping series `∑ (1/(k + 1) − 1/(k + 2)) = 1`
  have hsum : Summable fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + 1) := by
    refine Summable.of_norm_bounded summable_inv_succ_sq fun k => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e : 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + 1)
        = ((1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) : ℝ) : ℂ) := by
      have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have h2 : (k : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
      have h3 : (k : ℂ) + 2 ≠ 0 := by
        rw [show (k : ℂ) + 2 = (k : ℂ) + 1 + 1 by ring]; exact h2
      push_cast
      field_simp
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have htel : HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + 1)) 1 := by
    have hlim : Tendsto (fun N : ℕ => ∑ k ∈ range N, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + 1)))
        atTop (𝓝 1) := by
      have hp : ∀ N : ℕ, ∑ k ∈ range N, (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 1 + 1))
          = 1 - (((1 / ((N : ℝ) + 1)) : ℝ) : ℂ) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih => rw [sum_range_succ, ih]; push_cast; ring
      have h := (continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h' := (tendsto_const_nhds (x := (1 : ℂ))).sub h
      rw [ofReal_zero, sub_zero] at h'
      exact h'.congr fun N => (hp N).symm
    have h := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
    convert hsum.hasSum using 1
    exact h.symm
  have h2 := h1.add htel
  convert h2 using 1
  · funext k
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hkz : (k : ℂ) + 1 + z ≠ 0 := by
      intro h
      apply hz
      exact ⟨k + 1, by push_cast; linear_combination -h⟩
    have hk2 : (k : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
    field_simp
    ring
  · field_simp
    ring

/-! ### 5.7.8 -/

/-- **DLMF 5.7.8**: `ℑψ(1 + iy) = ∑_{k=1}^∞ y/(k² + y²)`, `y` real. -/
theorem dlmf_5_7_8 (y : ℝ) :
    HasSum (fun k : ℕ => y / (((k : ℝ) + 1) ^ 2 + y ^ 2)) (digamma (1 + y * I)).im := by
  have hp : (1 + y * I) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by simp)
  have h := Complex.hasSum_im (dlmf_5_7_6 hp)
  rw [add_im, ofReal_im, add_zero] at h
  convert h using 1
  funext k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [show (k : ℂ) + (1 + y * I) = (((k : ℝ) + 1 : ℝ) : ℂ) + (y : ℂ) * I by push_cast; ring,
    show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
  rw [sub_im, div_im, div_im]
  simp only [one_re, one_im, ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im,
    normSq_apply, ofReal_re, ofReal_im]
  ring

/-! ### 5.7.7 -/

theorem tendsto_of_even_odd_cplx {u : ℕ → ℂ} {L : ℂ}
    (h0 : Tendsto (fun m => u (2 * m)) atTop (𝓝 L))
    (h1 : Tendsto (fun m => u (2 * m + 1)) atTop (𝓝 L)) : Tendsto u atTop (𝓝 L) := by
  intro s hs
  obtain ⟨M0, hM0⟩ := mem_atTop_sets.mp (h0 hs)
  obtain ⟨M1, hM1⟩ := mem_atTop_sets.mp (h1 hs)
  refine mem_atTop_sets.mpr ⟨2 * max M0 M1, fun N hN => ?_⟩
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' N
  · exact hM0 m (by omega)
  · exact hM1 m (by omega)

theorem sum_range_two_mul_pair (f : ℕ → ℂ) (m : ℕ) :
    ∑ k ∈ range (2 * m), f k = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-- **DLMF 5.7.7**: `ψ(½ + ½z) − ψ(½z) = 2 ∑_{k=0}^∞ (−1)ᵏ/(k + z)`, `z ≠ 0, −1, −2, …` (the series
converges conditionally: the partial sums converge). -/
theorem dlmf_5_7_7 {z : ℂ} (hz : z ∉ gammaPoles) :
    Tendsto (fun N : ℕ => 2 * ∑ k ∈ range N, (-1 : ℂ) ^ k / ((k : ℂ) + z)) atTop
      (𝓝 (digamma (1 / 2 + z / 2) - digamma (z / 2))) := by
  have hz' := not_mem_gammaPoles.mp hz
  have hne : ∀ k : ℕ, (k : ℂ) + z ≠ 0 := fun k h => hz' k (by linear_combination h)
  have ha : z / 2 ∉ gammaPoles := by
    rintro ⟨m, hm⟩
    exact hz' (2 * m) (by push_cast; linear_combination -2 * hm)
  have hb : 1 / 2 + z / 2 ∉ gammaPoles := by
    rintro ⟨m, hm⟩
    exact hz' (2 * m + 1) (by push_cast; linear_combination -2 * hm)
  have hD := (dlmf_5_7_6 hb).sub (dlmf_5_7_6 ha)
  rw [show digamma (1 / 2 + z / 2) + γ - (digamma (z / 2) + γ)
    = digamma (1 / 2 + z / 2) - digamma (z / 2) by ring] at hD
  have hE := hD.tendsto_sum_nat
  apply tendsto_of_even_odd_cplx
  · refine hE.congr fun m => ?_
    rw [sum_range_two_mul_pair, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    have h1 := hne (2 * j)
    have h2 := hne (2 * j + 1)
    push_cast at h1 h2
    have h3 : (j : ℂ) + (1 / 2 + z / 2) ≠ 0 := fun h => h2 (by linear_combination 2 * h)
    have h4 : (j : ℂ) + z / 2 ≠ 0 := fun h => h1 (by linear_combination 2 * h)
    rw [show (-1 : ℂ) ^ (2 * j + 1) = -1 by rw [pow_succ, pow_mul]; simp,
      show (-1 : ℂ) ^ (2 * j) = 1 by rw [pow_mul]; simp]
    push_cast
    field_simp
    ring
  · -- `P(2m + 1) = P(2m) + 2/(2m + z)`
    have hr : Tendsto (fun m : ℕ => (2 : ℂ) * ((-1 : ℂ) ^ (2 * m) / (((2 * m : ℕ) : ℂ) + z)))
        atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
      have hb : Tendsto (fun m : ℕ => 2 / (2 * (m : ℝ) - ‖z‖)) atTop (𝓝 0) := by
        have : Tendsto (fun m : ℕ => 2 * (m : ℝ) - ‖z‖) atTop atTop :=
          tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
        exact this.const_div_atTop 2 |>.congr fun m => rfl
      refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hb
      filter_upwards [eventually_gt_atTop ⌈‖z‖⌉₊] with m hm
      have hm' : ‖z‖ < m := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hm)
      have hpos : 0 < 2 * (m : ℝ) - ‖z‖ := by linarith
      rw [pow_mul, neg_one_sq, one_pow, norm_mul, norm_div, norm_one]
      have hge : 2 * (m : ℝ) - ‖z‖ ≤ ‖((2 * m : ℕ) : ℂ) + z‖ := by
        have := norm_sub_le (((2 * m : ℕ) : ℂ) + z) z
        rw [add_sub_cancel_right] at this
        have hn : ‖((2 * m : ℕ) : ℂ)‖ = 2 * m := by simp
        linarith
      rw [show ‖(2 : ℂ)‖ = 2 by simp]
      calc 2 * (1 / ‖((2 * m : ℕ) : ℂ) + z‖) = 2 / ‖((2 * m : ℕ) : ℂ) + z‖ := by ring
        _ ≤ 2 / (2 * (m : ℝ) - ‖z‖) := div_le_div_of_nonneg_left (by norm_num) hpos hge
    have h := hE.add hr
    rw [add_zero] at h
    refine h.congr fun m => ?_
    rw [sum_range_succ, mul_add, sum_range_two_mul_pair, mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have h1 := hne (2 * j)
    have h2 := hne (2 * j + 1)
    push_cast at h1 h2 ⊢
    have h3 : (j : ℂ) + (1 / 2 + z / 2) ≠ 0 := fun h => h2 (by linear_combination 2 * h)
    have h4 : (j : ℂ) + z / 2 ≠ 0 := fun h => h1 (by linear_combination 2 * h)
    rw [show (-1 : ℂ) ^ (2 * j + 1) = -1 by rw [pow_succ, pow_mul]; simp,
      show (-1 : ℂ) ^ (2 * j) = 1 by rw [pow_mul]; simp]
    field_simp
    ring

/-! ### 5.7.4 -/

/-- `ζ(k + 2) = ∑_{n≥0} 1/(n + 1)^{k+2}`. -/
theorem hasSum_zeta_add_two (j : ℕ) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (j + 2)) (riemannZeta (j + 2)) := by
  have hs : Summable fun n : ℕ => 1 / (n : ℂ) ^ (j + 2) := by
    refine Summable.of_norm ?_
    have := Real.summable_one_div_nat_pow.mpr (show 1 < j + 2 by omega)
    refine this.congr fun n => ?_
    simp
  have h := hs.hasSum
  rw [← show riemannZeta ((j + 2 : ℕ) : ℂ) = ∑' n : ℕ, 1 / (n : ℂ) ^ (j + 2) from
    zeta_nat_eq_tsum_of_gt_one (by omega)] at h
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simp only [sum_range_one, Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero,
    and_false, not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one]
    at h'
  push_cast at h'
  exact h'

/-- **DLMF 5.7.4**: `ψ(1 + z) = −γ + ∑_{k=2}^∞ (−1)ᵏ ζ(k) z^{k−1}`, `|z| < 1` (indexed by
`k = j + 2`). -/
theorem dlmf_5_7_4 {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ (j + 2) * riemannZeta (j + 2) * z ^ (j + 1))
      (digamma (1 + z) + γ) := by
  set f : ℕ × ℕ → ℂ := fun p => (-1 : ℂ) ^ p.2 * z ^ (p.2 + 1) / ((p.1 : ℂ) + 1) ^ (p.2 + 2)
    with hf
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  -- summability on `ℕ × ℕ`
  have hsum : Summable f := by
    have hg : Summable fun j : ℕ => ‖z‖ ^ j := summable_geometric_of_lt_one hz0 hz
    have hprod := summable_inv_succ_sq.mul_of_nonneg hg (fun k => by positivity)
      (fun j => by positivity)
    refine Summable.of_norm_bounded hprod fun p => ?_
    obtain ⟨k, j⟩ := p
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [show ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 by
      rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]]
    rw [div_le_iff₀ (by positivity)]
    calc ‖z‖ ^ (j + 1) ≤ ‖z‖ ^ j := pow_le_pow_of_le_one hz0 hz.le (by omega)
      _ = 1 / ((k : ℝ) + 1) ^ 2 * ‖z‖ ^ j * ((k : ℝ) + 1) ^ 2 := by field_simp
      _ ≤ 1 / ((k : ℝ) + 1) ^ 2 * ‖z‖ ^ j * ((k : ℝ) + 1) ^ (j + 2) := by
          gcongr
          omega
  -- inner sums over `j`: geometric
  have hj : ∀ k : ℕ, HasSum (fun j => f (k, j))
      (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + z))) := by
    intro k
    have hk : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hr : ‖-z / ((k : ℂ) + 1)‖ < 1 := by
      rw [norm_div, norm_neg, hk, div_lt_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (z / ((k : ℂ) + 1) ^ 2)
    have hkz : (k : ℂ) + (1 + z) ≠ 0 := by
      intro h
      have := congrArg norm h
      rw [norm_zero] at this
      have h2 : (k : ℝ) + 1 - ‖z‖ ≤ ‖(k : ℂ) + (1 + z)‖ := by
        have := norm_sub_le ((k : ℂ) + (1 + z)) z
        rw [show (k : ℂ) + (1 + z) - z = (k : ℂ) + 1 by ring, hk] at this
        linarith
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    convert hg using 1
    · funext j
      simp only [hf]
      rw [div_pow, neg_pow]
      field_simp
      ring
    · rw [show 1 - -z / ((k : ℂ) + 1) = ((k : ℂ) + (1 + z)) / ((k : ℂ) + 1) by
          field_simp; ring, inv_div]
      have hkz' : 1 + (k : ℂ) + z ≠ 0 := by rw [add_comm 1, add_assoc]; exact hkz
      field_simp
      ring
  -- inner sums over `k`: zeta values
  have hk : ∀ j : ℕ, HasSum (fun k => f (k, j))
      ((-1 : ℂ) ^ (j + 2) * riemannZeta (j + 2) * z ^ (j + 1)) := by
    intro j
    have := (hasSum_zeta_add_two j).mul_left ((-1 : ℂ) ^ j * z ^ (j + 1))
    convert this using 1
    · funext k
      simp only [hf]
      ring
    · rw [pow_add, neg_one_sq, mul_one]
      ring
  have hA := hsum.hasSum.prod_fiberwise hj
  have hB := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise
    (fun j => by simpa using hk j)
  have hp : (1 + z) ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by
    have := abs_re_le_norm z
    simp only [add_re, one_re]
    linarith [neg_abs_le z.re])
  have hval := (dlmf_5_7_6 hp).unique hA
  rw [hval]
  exact hB

end Azurite.DLMF

