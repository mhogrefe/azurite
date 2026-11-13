/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Good
import Azurite.DLMF.Chapter5.Section14Carlson
import Azurite.DLMF.Chapter5.Section14Mehta
import Azurite.DLMF.Chapter5.Section6Stirling

/-!
# DLMF 5.14.7: Dyson's integral

`(2π)^{−n} ∫_{[−π,π]ⁿ} ∏_{j<k} |e^{iθⱼ} − e^{iθₖ}|^{2b} dθ = Γ(1 + bn)/Γ(1 + b)ⁿ`, `ℜb > −1/n`.

At nonnegative integers this is Good's identity (`integral_dysonF_nat`). Both sides are
holomorphic for `ℜb > 0` and of exponential type; on the line `ℜb = 1` the integral is bounded and
the closed form grows like `e^{|ℑb|/2}` (Stirling: the factors `e^{∓nπ|ℑb|/2}` of `Γ(1 + nb)` and
`Γ(1 + b)ⁿ` cancel). Carlson's theorem (`carlson`) applied to `b ↦ D(b + 1) − R(b + 1)` gives the
identity on `ℜb ≥ 1`. Convergence on `ℜb > −1/n` follows from Landau's theorem
(`integrable_exp_of_taylor`) as for Selberg's integral, and analytic continuation finishes.
-/

open Finset MeasureTheory Filter Topology Complex

namespace Azurite.DLMF

/-! ### Growth of `Γ(1 + nb)/Γ(1 + b)ⁿ` -/

theorem norm_inv_Gamma_le_abs {w : ℂ} (hw : 1 ≤ w.re) :
    ‖(Gamma w)⁻¹‖ ≤ Real.exp (1 / 6) / Real.sqrt (2 * Real.pi) * ‖w‖ ^ (1 / 2 - w.re) *
      Real.exp (w.re + Real.pi / 2 * |w.im|) := by
  rcases le_total 0 w.im with h | h
  · rw [abs_of_nonneg h]; exact norm_inv_Gamma_le hw h
  · have h' := norm_inv_Gamma_le (w := (starRingEnd ℂ) w) (by simpa using hw)
      (by simpa using h)
    rw [Complex.Gamma_conj, ← map_inv₀, Complex.norm_conj, Complex.norm_conj] at h'
    rw [abs_of_nonpos h]
    simpa using h'

/-- `‖Γ(1 + nb)/Γ(1 + b)ⁿ‖ ≤ C e^{n(ln 2n + 1)ℜb} √(1 + n‖b‖)` for `ℜb ≥ 0`, `n ≥ 1`. -/
theorem norm_dysonRatio_le {n : ℕ} (hn : 1 ≤ n) {b : ℂ} (hb : 0 ≤ b.re) :
    ‖Gamma (1 + n * b) * ((Gamma (1 + b))⁻¹) ^ n‖ ≤
      Real.sqrt (2 * Real.pi) * (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n *
        Real.exp (1 / 6 + n) * Real.exp (n * (Real.log (2 * n) + 1) * b.re) *
          Real.sqrt (1 + n * ‖b‖) := by
  set w₁ : ℂ := 1 + n * b
  set w₂ : ℂ := 1 + b
  set x := b.re
  set y := b.im
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hw₁re : w₁.re = 1 + n * x := by simp [w₁, x]
  have hw₁im : w₁.im = n * y := by simp [w₁, y]
  have hw₂re : w₂.re = 1 + x := by simp [w₂, x]
  have hw₂im : w₂.im = y := by simp [w₂, y]
  have hw₁1 : 1 ≤ ‖w₁‖ := by
    have := Complex.re_le_norm w₁; rw [hw₁re] at this; nlinarith
  have hw₂1 : 1 ≤ ‖w₂‖ := by
    have := Complex.re_le_norm w₂; rw [hw₂re] at this; linarith
  have hw₁0 : w₁ ≠ 0 := fun h => by rw [h, norm_zero] at hw₁1; linarith
  have hπ := Real.pi_pos
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  -- the two Stirling bounds
  have hA := dlmf_5_6_9 (z := w₁) (by rw [hw₁re]; positivity) hw₁0
  have hA' : ‖Gamma w₁‖ ≤ Real.sqrt (2 * Real.pi) * ‖w₁‖ ^ (n * x + 1 / 2) *
      Real.exp (-(n * Real.pi * |y|) / 2) * Real.exp (1 / 6) := by
    refine hA.trans ?_
    rw [hw₁re, hw₁im, abs_mul, Nat.abs_cast]
    have : Real.exp (1 / 6 * ‖w₁‖⁻¹) ≤ Real.exp (1 / 6) := Real.exp_le_exp.mpr (by
      have := inv_le_one_of_one_le₀ hw₁1; nlinarith)
    rw [show (1 + n * x - 1 / 2 : ℝ) = n * x + 1 / 2 by ring,
      show -(Real.pi * (n * |y|)) / 2 = -(n * Real.pi * |y|) / 2 by ring]
    gcongr
  have hB := norm_inv_Gamma_le_abs (w := w₂) (by rw [hw₂re]; linarith)
  rw [hw₂re, hw₂im, show (1 / 2 - (1 + x) : ℝ) = -(1 / 2 + x) by ring] at hB
  -- combine
  have hmain : ‖Gamma w₁ * ((Gamma w₂)⁻¹) ^ n‖ ≤
      Real.sqrt (2 * Real.pi) * (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n *
        Real.exp (1 / 6 + n) * Real.exp (n * x) *
          (‖w₁‖ ^ (n * x + 1 / 2) * (‖w₂‖ ^ (-(1 / 2 + x))) ^ n) := by
    rw [norm_mul, norm_pow]
    calc ‖Gamma w₁‖ * ‖(Gamma w₂)⁻¹‖ ^ n
        ≤ (Real.sqrt (2 * Real.pi) * ‖w₁‖ ^ (n * x + 1 / 2) *
            Real.exp (-(n * Real.pi * |y|) / 2) * Real.exp (1 / 6)) *
          (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi) * ‖w₂‖ ^ (-(1 / 2 + x)) *
            Real.exp (1 + x + Real.pi / 2 * |y|)) ^ n := by
          gcongr
      _ = _ := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
          have e : Real.exp (-(n * Real.pi * |y|) / 2) * Real.exp (1 / 6) *
              Real.exp (n * (1 + x + Real.pi / 2 * |y|)) =
              Real.exp (1 / 6 + n) * Real.exp (n * x) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
          calc _ = Real.sqrt (2 * Real.pi) * (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n *
                (Real.exp (-(n * Real.pi * |y|) / 2) * Real.exp (1 / 6) *
                  Real.exp (n * (1 + x + Real.pi / 2 * |y|))) *
                (‖w₁‖ ^ (n * x + 1 / 2) * (‖w₂‖ ^ (-(1 / 2 + x))) ^ n) := by ring
            _ = _ := by rw [e]; ring
  -- the powers of the norms
  have hw12 : ‖w₁‖ ≤ 2 * n * ‖w₂‖ := by
    have : w₁ = n * w₂ - (n - 1) := by simp only [w₁, w₂]; ring
    calc ‖w₁‖ = ‖(n : ℂ) * w₂ - ((n : ℂ) - 1)‖ := by rw [this]
      _ ≤ ‖(n : ℂ) * w₂‖ + ‖(n : ℂ) - 1‖ := norm_sub_le _ _
      _ = n * ‖w₂‖ + (n - 1) := by
          rw [norm_mul, Complex.norm_natCast,
            show ((n : ℂ) - 1) = (((n - 1 : ℕ) : ℝ) : ℂ) by push_cast [Nat.cast_sub hn]; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
            Nat.cast_sub hn, Nat.cast_one]
      _ ≤ 2 * n * ‖w₂‖ := by nlinarith
  have hpow : ‖w₁‖ ^ (n * x + 1 / 2) * (‖w₂‖ ^ (-(1 / 2 + x))) ^ n ≤
      Real.exp (n * Real.log (2 * n) * x) * Real.sqrt (‖w₁‖) := by
    have hpos₂ : 0 < ‖w₂‖ := by linarith
    have hpos₁ : 0 < ‖w₁‖ := by linarith
    rw [Real.rpow_add hpos₁, ← Real.rpow_natCast, ← Real.rpow_mul hpos₂.le,
      ← Real.sqrt_eq_rpow]
    have h1 : ‖w₁‖ ^ (n * x) ≤ (2 * n) ^ (n * x) * ‖w₂‖ ^ (n * x) := by
      rw [← Real.mul_rpow (by positivity) hpos₂.le]
      exact Real.rpow_le_rpow hpos₁.le hw12 (by positivity)
    have h2 : ‖w₂‖ ^ (n * x) * ‖w₂‖ ^ (-(1 / 2 + x) * n) ≤ 1 := by
      rw [← Real.rpow_add hpos₂]
      exact Real.rpow_le_one_of_one_le_of_nonpos hw₂1 (by nlinarith)
    have h3 : (2 * (n : ℝ)) ^ (n * x) = Real.exp (n * Real.log (2 * n) * x) := by
      rw [Real.rpow_def_of_pos (by positivity)]; ring_nf
    have hs := Real.sqrt_nonneg ‖w₁‖
    calc ‖w₁‖ ^ (n * x) * Real.sqrt ‖w₁‖ * ‖w₂‖ ^ (-(1 / 2 + x) * n)
        ≤ (2 * n) ^ (n * x) * ‖w₂‖ ^ (n * x) * Real.sqrt ‖w₁‖ * ‖w₂‖ ^ (-(1 / 2 + x) * n) := by
          gcongr
      _ = (2 * n) ^ (n * x) * Real.sqrt ‖w₁‖ *
          (‖w₂‖ ^ (n * x) * ‖w₂‖ ^ (-(1 / 2 + x) * n)) := by ring
      _ ≤ (2 * n) ^ (n * x) * Real.sqrt ‖w₁‖ * 1 := by gcongr
      _ = _ := by rw [h3, mul_one]
  have hw₁b : ‖w₁‖ ≤ 1 + n * ‖b‖ := by
    calc ‖w₁‖ ≤ ‖(1 : ℂ)‖ + ‖(n : ℂ) * b‖ := norm_add_le _ _
      _ = 1 + n * ‖b‖ := by rw [norm_one, norm_mul, Complex.norm_natCast]
  calc ‖Gamma (1 + n * b) * ((Gamma (1 + b))⁻¹) ^ n‖
      ≤ Real.sqrt (2 * Real.pi) * (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n *
          Real.exp (1 / 6 + n) * Real.exp (n * x) *
          (Real.exp (n * Real.log (2 * n) * x) * Real.sqrt (‖w₁‖)) :=
        hmain.trans (by gcongr)
    _ ≤ Real.sqrt (2 * Real.pi) * (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n *
          Real.exp (1 / 6 + n) * Real.exp (n * x) *
          (Real.exp (n * Real.log (2 * n) * x) * Real.sqrt (1 + n * ‖b‖)) := by
        gcongr
    _ = _ := by
        rw [show Real.exp (n * (Real.log (2 * n) + 1) * x) =
          Real.exp (n * x) * Real.exp (n * Real.log (2 * n) * x) by
          rw [← Real.exp_add]; ring_nf]
        ring

/-! ### Dyson's integrand as an exponential -/

section Dyson

variable {n : ℕ}

/-- `‖e^{iθⱼ} − e^{iθₖ}‖`. -/
noncomputable def chordR (θ : Fin n → ℝ) (j k : Fin n) : ℝ :=
  ‖Complex.exp ((θ j : ℂ) * I) - Complex.exp ((θ k : ℂ) * I)‖

/-- `L(θ) = Σ_{j<k} 2 ln |e^{iθⱼ} − e^{iθₖ}|`. -/
noncomputable def dysonL (θ : Fin n → ℝ) : ℝ :=
  ∑ j, ∑ k ∈ Ioi j, 2 * Real.log (chordR θ j k)

/-- Dyson's integral `D(b)`. -/
noncomputable def dysonD (n : ℕ) (b : ℂ) : ℂ := ∫ θ in torusBox n, dysonF b θ

/-- `(2π)ⁿ Γ(1 + nb)/Γ(1 + b)ⁿ`. -/
noncomputable def dysonR (n : ℕ) (b : ℂ) : ℂ :=
  (2 * Real.pi : ℂ) ^ n * (Gamma (1 + n * b) * ((Gamma (1 + b))⁻¹) ^ n)

theorem chordR_le_two (θ : Fin n → ℝ) (j k : Fin n) : chordR θ j k ≤ 2 := by
  unfold chordR
  calc _ ≤ ‖Complex.exp ((θ j : ℂ) * I)‖ + ‖Complex.exp ((θ k : ℂ) * I)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]; norm_num

theorem measurable_dysonL : Measurable (dysonL (n := n)) := by
  unfold dysonL chordR; fun_prop

theorem measurable_dysonF (b : ℂ) : Measurable (dysonF (n := n) b) := by
  unfold dysonF; fun_prop

theorem dysonL_le (θ : Fin n → ℝ) : dysonL θ ≤ pairCount n * Real.log 4 := by
  unfold dysonL pairCount
  rw [Nat.cast_sum, sum_mul]
  refine sum_le_sum fun j _ => ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun k _ => ?_
  rw [show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
  rcases eq_or_lt_of_le (norm_nonneg (Complex.exp ((θ j : ℂ) * I) -
    Complex.exp ((θ k : ℂ) * I))) with h | h
  · rw [chordR, ← h, Real.log_zero]; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  · have := Real.log_le_log h (chordR_le_two θ j k); unfold chordR at this ⊢; linarith

theorem ae_chordR_ne_zero :
    ∀ᵐ θ ∂(volume.restrict (torusBox n)), ∀ j k : Fin n, j < k → chordR θ j k ≠ 0 := by
  filter_upwards [ae_torus_distinct] with θ hθ j k hjk
  unfold chordR
  rw [norm_ne_zero_iff, sub_ne_zero]
  exact hθ j k hjk.ne

theorem dysonF_eq_exp {θ : Fin n → ℝ} (hθ : ∀ j k : Fin n, j < k → chordR θ j k ≠ 0)
    (b : ℂ) : dysonF b θ = Complex.exp (b * dysonL θ) := by
  unfold dysonF dysonL
  rw [Complex.ofReal_sum, mul_sum, Complex.exp_sum]
  refine prod_congr rfl fun j _ => ?_
  rw [Complex.ofReal_sum, mul_sum, Complex.exp_sum]
  refine prod_congr rfl fun k hk => ?_
  have hr := hθ j k (mem_Ioi.mp hk)
  unfold chordR at hr ⊢
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr), ← Complex.ofReal_log (norm_nonneg _)]
  congr 1
  push_cast
  ring

theorem norm_dysonF_ae (b : ℂ) :
    ∀ᵐ θ ∂(volume.restrict (torusBox n)), ‖dysonF b θ‖ = Real.exp (b.re * dysonL θ) := by
  filter_upwards [ae_chordR_ne_zero] with θ hθ
  rw [dysonF_eq_exp hθ, Complex.norm_exp]
  simp

theorem volume_torusBox (n : ℕ) : (volume : Measure (Fin n → ℝ)).real (torusBox n) =
    (2 * Real.pi) ^ n := by
  rw [Measure.real, torusBox, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, prod_const, card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem volume_torusBox_lt_top (n : ℕ) : volume (torusBox n) < ⊤ :=
  (isCompact_torusBox n).measure_lt_top

/-- `‖D(b)‖ ≤ (2π)ⁿ 4^{P ℜb}` for `ℜb ≥ 0`. -/
theorem norm_dysonD_le {b : ℂ} (hb : 0 ≤ b.re) :
    ‖dysonD n b‖ ≤ Real.exp (b.re * (pairCount n * Real.log 4)) * (2 * Real.pi) ^ n := by
  rw [dysonD, ← volume_torusBox n]
  refine norm_setIntegral_le_of_norm_le_const_ae (volume_torusBox_lt_top n) ?_
  filter_upwards [norm_dysonF_ae b] with θ hθ
  rw [hθ]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (dysonL_le θ) hb)

theorem integrableOn_exp_dysonL_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (fun θ => Real.exp (s * dysonL (n := n) θ)) (torusBox n) := by
  refine Measure.integrableOn_of_bounded (M := Real.exp (s * (pairCount n * Real.log 4)))
    (volume_torusBox_lt_top n).ne ?_ ?_
  · exact (measurable_dysonL.const_mul s).exp.aestronglyMeasurable
  · filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (dysonL_le θ) hs)

/-- `D` is holomorphic on `ℜb > c` once `e^{sL}` is integrable for all `s > c`. -/
theorem differentiableOn_dysonD {c : ℝ}
    (hI : ∀ s : ℝ, c < s → IntegrableOn (fun θ => Real.exp (s * dysonL (n := n) θ)) (torusBox n)) :
    DifferentiableOn ℂ (dysonD n) {b | c < b.re} := by
  refine differentiableOn_integral_of_holo (F := fun b θ => dysonF b θ)
    (F' := fun b θ => dysonF b θ * dysonL θ) (fun z _ => (measurable_dysonF z).aestronglyMeasurable)
    (fun z _ => ((measurable_dysonF z).mul
      (Complex.measurable_ofReal.comp measurable_dysonL)).aestronglyMeasurable) ?_
  intro z₀ hz₀
  have hz₀' : c < z₀.re := hz₀
  set ε := (z₀.re - c) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  refine ⟨ε / 4, by positivity, fun z hz => ?_, fun θ => Real.exp ((z₀.re - ε) * dysonL θ) +
    Real.exp ((z₀.re + ε) * dysonL θ), ?_, ?_, ?_⟩
  · have h1 := Complex.abs_re_le_norm (z - z₀)
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Complex.sub_re] at h1
    show c < z.re
    have := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
    simp only [ε] at this; linarith
  · exact (hI _ (by simp only [ε]; linarith)).add (hI _ (by simp only [ε]; linarith))
  · filter_upwards [ae_chordR_ne_zero] with θ hθ z _
    have e : (fun b => dysonF b θ) = fun b => Complex.exp (b * dysonL θ) :=
      funext fun b => dysonF_eq_exp hθ b
    simp only [e, dysonF_eq_exp hθ z]
    simpa using ((hasDerivAt_id z).mul_const (dysonL θ : ℂ)).cexp
  · filter_upwards [ae_chordR_ne_zero] with θ hθ
    intro z hz
    have hzre : z₀.re - ε ≤ z.re ∧ z.re ≤ z₀.re + ε := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [Complex.sub_re] at h1
      have := abs_le.mp (h1.trans hz)
      constructor <;> linarith
    rw [dysonF_eq_exp hθ, Complex.norm_exp]
    have hre : (z * (dysonL θ : ℂ)).re = z.re * dysonL θ := by simp
    rw [hre]
    have h1 := Real.exp_pos ((z₀.re - ε) * dysonL θ)
    have h2 := Real.exp_pos ((z₀.re + ε) * dysonL θ)
    rcases le_total 0 (dysonL θ) with hL | hL
    · have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzre.2 hL); linarith
    · have := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hzre.1 hL); linarith

theorem differentiableOn_dysonR :
    DifferentiableOn ℂ (dysonR n) {b | -1 < (n : ℝ) * b.re} := by
  intro b hb
  have hb' : -1 < (n : ℝ) * b.re := hb
  have hG : DifferentiableAt ℂ Gamma (1 + n * b) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    have := congrArg Complex.re hm
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hinv : DifferentiableAt ℂ (fun b : ℂ => (Gamma (1 + b))⁻¹) b :=
    (Complex.differentiable_one_div_Gamma.comp (differentiable_const 1 |>.add differentiable_id))
      |>.differentiableAt |> fun h => by simpa [Function.comp_def] using h
  unfold dysonR
  refine (DifferentiableAt.const_mul (DifferentiableAt.mul ?_ (hinv.pow n)) _)
    |>.differentiableWithinAt
  exact hG.comp b ((differentiableAt_const _).add
    ((differentiableAt_const _).mul differentiableAt_id))

theorem dysonD_nat (k : ℕ) : dysonD n k = dysonR n k := by
  rw [dysonD, integral_dysonF_nat, dysonR,
    show (1 : ℂ) + n * k = ((n * k : ℕ) : ℂ) + 1 by push_cast; ring,
    show (1 : ℂ) + k = (k : ℂ) + 1 by ring, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, inv_pow, div_eq_mul_inv]

/-- The constant of `norm_dysonRatio_le`. -/
noncomputable def dysonK (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) * (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n * Real.exp (1 / 6 + n)

theorem dysonK_nonneg (n : ℕ) : 0 ≤ dysonK n := by unfold dysonK; positivity

theorem norm_dysonR_le (hn : 1 ≤ n) {b : ℂ} (hb : 0 ≤ b.re) :
    ‖dysonR n b‖ ≤ (2 * Real.pi) ^ n * dysonK n *
      Real.exp (n * (Real.log (2 * n) + 1) * b.re) * Real.sqrt (1 + n * ‖b‖) := by
  rw [dysonR, norm_mul, norm_pow, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]]
  have := norm_dysonRatio_le hn hb
  unfold dysonK
  calc _ ≤ (2 * Real.pi) ^ n * (Real.sqrt (2 * Real.pi) *
        (Real.exp (1 / 6) / Real.sqrt (2 * Real.pi)) ^ n * Real.exp (1 / 6 + n) *
        Real.exp (n * (Real.log (2 * n) + 1) * b.re) * Real.sqrt (1 + n * ‖b‖)) := by gcongr
    _ = _ := by ring

theorem sqrt_one_add_le_exp (t : ℝ) : Real.sqrt (1 + t) ≤ Real.exp (t / 2) := by
  rw [show Real.exp (t / 2) = Real.sqrt (Real.exp (t / 2) ^ 2) by
    rw [Real.sqrt_sq (Real.exp_pos _).le]]
  refine Real.sqrt_le_sqrt ?_
  rw [← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (t / 2) = t by ring]
  linarith [Real.add_one_le_exp t]

/-- **Carlson step**: `D(b) = R(b)` for `ℜb ≥ 1`. -/
theorem dysonD_eq_of_one_le (hn : 1 ≤ n) {b : ℂ} (hb : 1 ≤ b.re) : dysonD n b = dysonR n b := by
  set f : ℂ → ℂ := fun z => dysonD n (z + 1) - dysonR n (z + 1)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD0 : DifferentiableOn ℂ (dysonD n) {b | 0 < b.re} :=
    differentiableOn_dysonD fun s hs => integrableOn_exp_dysonL_of_nonneg hs.le
  have hf : DifferentiableOn ℂ f {z | -1 < z.re} := by
    have hadd : DifferentiableOn ℂ (fun z : ℂ => z + 1) {z | -1 < z.re} :=
      differentiable_id.add_const 1 |>.differentiableOn
    refine DifferentiableOn.sub (hD0.comp hadd fun z hz => ?_)
      (differentiableOn_dysonR.comp hadd fun z hz => ?_)
    · show 0 < (z + 1).re
      have : -1 < z.re := hz
      simp; linarith
    · show -1 < (n : ℝ) * (z + 1).re
      have : -1 < z.re := hz
      simp only [Complex.add_re, Complex.one_re]
      nlinarith
  have hz : ∀ k : ℕ, f k = 0 := fun k => by
    simp only [f]
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, dysonD_nat, sub_self]
  set c₁ : ℝ := n * (Real.log (2 * n) + 1)
  set P4 : ℝ := pairCount n * Real.log 4
  have hc₁ : 0 ≤ c₁ := by
    have : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
    positivity
  have hP4 : 0 ≤ P4 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hK := dysonK_nonneg n
  have h2π : 0 ≤ (2 * Real.pi) ^ n := by positivity
  have hexp : ∃ A B : ℝ, ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ A * Real.exp (B * ‖z‖) := by
    refine ⟨(2 * Real.pi) ^ n * (Real.exp P4 + dysonK n * Real.exp (c₁ + n)), P4 + c₁ + n,
      fun z hz' => ?_⟩
    have hbre : 0 ≤ (z + 1).re := by simp; linarith
    have hre : (z + 1).re ≤ ‖z‖ + 1 := by
      have := Complex.re_le_norm z; simp; linarith
    have hnb : ‖z + 1‖ ≤ ‖z‖ + 1 := by
      have := norm_add_le z 1; rwa [norm_one] at this
    have hz0 := norm_nonneg z
    have h1 := norm_dysonD_le (n := n) hbre
    have h2 := norm_dysonR_le hn hbre
    have hsq : Real.sqrt (1 + n * ‖z + 1‖) ≤ Real.exp (n * (‖z‖ + 1)) := by
      refine (sqrt_one_add_le_exp _).trans (Real.exp_le_exp.mpr ?_)
      have : (n : ℝ) * ‖z + 1‖ ≤ n * (‖z‖ + 1) := by gcongr
      have : 0 ≤ (n : ℝ) * ‖z + 1‖ := by positivity
      linarith
    have e1 : Real.exp ((z + 1).re * P4) ≤ Real.exp P4 * Real.exp ((P4 + c₁ + n) * ‖z‖) := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_; nlinarith
    have e2 : Real.exp (c₁ * (z + 1).re) * Real.exp (n * (‖z‖ + 1)) ≤
        Real.exp (c₁ + n) * Real.exp ((P4 + c₁ + n) * ‖z‖) := by
      rw [← Real.exp_add, ← Real.exp_add]; refine Real.exp_le_exp.mpr ?_; nlinarith
    calc ‖f z‖ ≤ ‖dysonD n (z + 1)‖ + ‖dysonR n (z + 1)‖ := norm_sub_le _ _
      _ ≤ Real.exp ((z + 1).re * P4) * (2 * Real.pi) ^ n +
          (2 * Real.pi) ^ n * dysonK n * Real.exp (c₁ * (z + 1).re) *
            Real.sqrt (1 + n * ‖z + 1‖) := add_le_add h1 h2
      _ ≤ Real.exp P4 * Real.exp ((P4 + c₁ + n) * ‖z‖) * (2 * Real.pi) ^ n +
          (2 * Real.pi) ^ n * dysonK n *
            (Real.exp (c₁ * (z + 1).re) * Real.exp (n * (‖z‖ + 1))) := by
          rw [mul_assoc ((2 * Real.pi) ^ n * dysonK n)]
          gcongr
      _ ≤ Real.exp P4 * Real.exp ((P4 + c₁ + n) * ‖z‖) * (2 * Real.pi) ^ n +
          (2 * Real.pi) ^ n * dysonK n *
            (Real.exp (c₁ + n) * Real.exp ((P4 + c₁ + n) * ‖z‖)) := by gcongr
      _ = _ := by ring
  have him : ∃ C c : ℝ, c < Real.pi ∧ ∀ y : ℝ, ‖f (y * I)‖ ≤ C * Real.exp (c * |y|) := by
    refine ⟨(2 * Real.pi) ^ n * (Real.exp P4 + dysonK n * Real.exp c₁ * Real.sqrt (1 + n)),
      1 / 2, by linarith [Real.pi_gt_three], fun y => ?_⟩
    have hre : ((y : ℂ) * I + 1).re = 1 := by simp
    have hnb : ‖(y : ℂ) * I + 1‖ ≤ 1 + |y| := by
      have := norm_add_le ((y : ℂ) * I) 1
      rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        at this
      linarith
    have h1 := norm_dysonD_le (n := n) (b := (y : ℂ) * I + 1) (by rw [hre]; norm_num)
    have h2 := norm_dysonR_le hn (b := (y : ℂ) * I + 1) (by rw [hre]; norm_num)
    rw [hre, one_mul] at h1
    rw [hre, mul_one] at h2
    have hsq : Real.sqrt (1 + n * ‖(y : ℂ) * I + 1‖) ≤ Real.sqrt (1 + n) * Real.exp (|y| / 2) := by
      calc Real.sqrt (1 + n * ‖(y : ℂ) * I + 1‖) ≤ Real.sqrt ((1 + n) * (1 + |y|)) := by
            refine Real.sqrt_le_sqrt ?_
            have := abs_nonneg y
            nlinarith
        _ = Real.sqrt (1 + n) * Real.sqrt (1 + |y|) := Real.sqrt_mul (by positivity) _
        _ ≤ Real.sqrt (1 + n) * Real.exp (|y| / 2) := by
            gcongr; exact sqrt_one_add_le_exp _
    have hE : 1 ≤ Real.exp (1 / 2 * |y|) := Real.one_le_exp (by positivity)
    calc ‖f (y * I)‖ ≤ ‖dysonD n (y * I + 1)‖ + ‖dysonR n (y * I + 1)‖ := norm_sub_le _ _
      _ ≤ Real.exp P4 * (2 * Real.pi) ^ n + (2 * Real.pi) ^ n * dysonK n * Real.exp c₁ *
          (Real.sqrt (1 + n) * Real.exp (|y| / 2)) := by
          refine add_le_add h1 (h2.trans ?_)
          gcongr
      _ ≤ Real.exp P4 * (2 * Real.pi) ^ n * Real.exp (1 / 2 * |y|) +
          (2 * Real.pi) ^ n * dysonK n * Real.exp c₁ *
          (Real.sqrt (1 + n) * Real.exp (1 / 2 * |y|)) := by
          rw [show |y| / 2 = 1 / 2 * |y| by ring]
          have : 0 ≤ Real.exp P4 * (2 * Real.pi) ^ n := by positivity
          nlinarith
      _ = _ := by ring
  have hc := carlson one_pos hf hz hexp him (b - 1) (by simp; linarith)
  simp only [f, sub_add_cancel] at hc
  exact sub_eq_zero.mp hc

theorem neg_one_div_lt_iff {m : ℝ} (hm : 0 < m) {x : ℝ} : -(1 / m) < x ↔ -1 < m * x := by
  rw [show -(1 / m) = -1 / m by ring, div_lt_iff₀ hm, mul_comm]

/-! ### Convergence on `ℜb > −1/n` (Landau's theorem) and continuation -/

/-- **Convergence** of Dyson's integral for real `s > −1/n`. -/
theorem integrableOn_exp_dysonL (hn : 1 ≤ n) {s : ℝ} (hs : -1 < (n : ℝ) * s) :
    IntegrableOn (fun θ => Real.exp (s * dysonL (n := n) θ)) (torusBox n) := by
  set P4 : ℝ := pairCount n * Real.log 4
  set μ := volume.restrict (torusBox n)
  set L₀ : (Fin n → ℝ) → ℝ := fun θ => dysonL θ - P4
  set g : (Fin n → ℝ) → ℝ := fun _ => 1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hLm : Measurable L₀ := measurable_dysonL.sub_const _
  have hgm : Measurable g := measurable_const
  have hL0 : ∀ᵐ θ ∂μ, L₀ θ ≤ 0 := ae_of_all _ fun θ => by
    simp only [L₀]; linarith [dysonL_le θ]
  have hg0 : ∀ᵐ θ ∂μ, 0 ≤ g θ := ae_of_all _ fun _ => zero_le_one
  have hI : ∀ σ : ℝ, 0 < σ → Integrable (fun θ => Real.exp (σ * L₀ θ) * g θ) μ := by
    intro σ hσ
    refine ((integrableOn_exp_dysonL_of_nonneg (n := n) hσ.le).mul_const
      (Real.exp (-(σ * P4)))).congr (ae_of_all _ fun θ => ?_)
    simp only [L₀, g, mul_one]
    rw [← Real.exp_add]; ring_nf
  set G : ℂ → ℂ := fun z => dysonR n z * Complex.exp (-(z * P4))
  set s' : ℝ := (s + -(1 / n)) / 2
  have hs1 : -(1 / (n : ℝ)) < s := (neg_one_div_lt_iff hn').mpr hs
  have hG : DifferentiableOn ℂ G (Metric.ball ((2 : ℝ) : ℂ) (2 - s')) := by
    refine (differentiableOn_dysonR.mono fun z hz => ?_).mul
      (Complex.differentiable_exp.comp (differentiable_id.mul_const _).neg).differentiableOn
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm _) hz)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at h1
    show -1 < (n : ℝ) * z.re
    have : -(1 / (n : ℝ)) < s' := by simp only [s']; linarith
    have h2 : -(1 / (n : ℝ)) < z.re := by linarith
    exact (neg_one_div_lt_iff hn').mp h2
  have hGF : G =ᶠ[nhds ((2 : ℝ) : ℂ)] momentF μ L₀ g 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < ((2 : ℝ) : ℂ).re by norm_num)] with z hz
    simp only [G, momentF, pow_zero, one_mul, g, Complex.ofReal_one, mul_one]
    rw [← dysonD_eq_of_one_le hn hz.le, dysonD, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [ae_chordR_ne_zero] with θ hθ
    rw [dysonF_eq_exp hθ, ← Complex.exp_add]
    congr 1
    simp only [L₀]
    push_cast
    ring
  have h := integrable_exp_of_taylor hLm hgm hL0 hg0 hI (s₀ := 2) two_pos hG hGF (s := s)
    (by simp only [s']; linarith)
  refine (h.mul_const (Real.exp (s * P4))).congr (ae_of_all _ fun θ => ?_)
  simp only [L₀, g, mul_one]
  rw [← Real.exp_add]; ring_nf

theorem differentiableOn_dysonD_full (hn : 1 ≤ n) :
    DifferentiableOn ℂ (dysonD n) {b | -(1 / (n : ℝ)) < b.re} := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact differentiableOn_dysonD fun s hs =>
    integrableOn_exp_dysonL hn ((neg_one_div_lt_iff hn').mp hs)

end Dyson

/-- **DLMF 5.14.7** (Dyson's integral) on DLMF's full range `ℜb > −1/n` (stated as `n ℜb > −1`):
`(2π)^{−n} ∫_{[−π,π]ⁿ} ∏_{1≤j<k≤n} |e^{iθⱼ} − e^{iθₖ}|^{2b} dθ₁⋯dθₙ = Γ(1 + bn)/Γ(1 + b)ⁿ`. -/
theorem dlmf_5_14_7 {n : ℕ} {b : ℂ} (hb : -1 < (n : ℝ) * b.re) :
    (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹ * ∫ θ in torusBox n,
      ∏ j, ∏ k ∈ Ioi j, ((‖Complex.exp ((θ j : ℂ) * I) -
        Complex.exp ((θ k : ℂ) * I)‖ : ℝ) : ℂ) ^ (2 * b) =
      Gamma (1 + b * n) / Gamma (1 + b) ^ n := by
  show (((2 * Real.pi) ^ n : ℝ) : ℂ)⁻¹ * dysonD n b = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ θ : Fin 0 → ℝ, dysonF b θ = 1 := fun θ => by simp [dysonF]
    simp only [dysonD, h0, integral_const_torusBox_zero]
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set U : Set ℂ := {b | -(1 / (n : ℝ)) < b.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hbU : b ∈ U := by
    exact (neg_one_div_lt_iff hn').mpr hb
  have hR : DifferentiableOn ℂ (dysonR n) U := differentiableOn_dysonR.mono fun z hz => by
    have h : -(1 / (n : ℝ)) < z.re := hz
    exact (neg_one_div_lt_iff hn').mp h
  have hf := (differentiableOn_dysonD_full (n := n) hn).sub hR
  have h2U : (2 : ℂ) ∈ U := by
    show -(1 / (n : ℝ)) < (2 : ℂ).re
    have : 0 < (n : ℝ)⁻¹ := by positivity
    simp; linarith
  have hz : (fun z => dysonD n z - dysonR n z) =ᶠ[nhds (2 : ℂ)] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    simp only [Pi.zero_apply]
    rw [dysonD_eq_of_one_le hn hz.le, sub_self]
  have h := (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt _).isPreconnected h2U hz hbU
  rw [sub_eq_zero.mp h, dysonR, inv_pow, mul_comm b, ← mul_assoc, Complex.ofReal_pow]
  rw [show (((2 * Real.pi : ℝ)) : ℂ) = (2 * Real.pi : ℂ) by push_cast; ring,
    inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0))),
    one_mul, div_eq_mul_inv, mul_comm (n : ℂ) b]

end Azurite.DLMF
