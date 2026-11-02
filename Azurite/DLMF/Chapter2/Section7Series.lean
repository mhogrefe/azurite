/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# DLMF §2.7(i): power series with a prescribed radius of convergence

Elementary facts about scalar power series `∑ aₛ (z − z₀)^s` used to build the Frobenius
solutions 2.7.4. A coefficient sequence `a` *has radius at least `R`* (`HasRadiusGE a R`) when
`‖aₛ‖ ρ^s` is bounded for every `ρ < R`; this is equivalent to absolute convergence on the ball
(`hasRadiusGE_of_summable`, `HasRadiusGE.summable_norm`), is preserved by termwise
differentiation (`shiftDeriv`, `HasRadiusGE.shift`), and gives termwise derivatives
(`HasRadiusGE.hasDerivAt`), the series for `(z − z₀) u′` and `(z − z₀)² u″`
(`HasRadiusGE.hasSum_natCast_mul`, `HasRadiusGE.hasSum_natCast_mul_sub_one`), and Cauchy
products (`hasSum_mul_powerSeriesSum`).
-/

open Filter Topology Set Complex Metric Finset

namespace Azurite.DLMF

/-- `‖aₛ‖ ρ^s` is bounded for every `0 < ρ < R`: the power series `∑ aₛ (z − z₀)^s` has radius
of convergence at least `R`. -/
def HasRadiusGE (a : ℕ → ℂ) (R : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < R → ∃ K : ℝ, ∀ s, ‖a s‖ * ρ ^ s ≤ K

/-- The coefficients `(s + 1) a_{s+1}` of the termwise derivative. -/
def shiftDeriv (a : ℕ → ℂ) (s : ℕ) : ℂ := (s + 1 : ℕ) * a (s + 1)

/-- The power series `∑ aₛ (z − z₀)^s`. -/
noncomputable def powerSeriesSum (a : ℕ → ℂ) (z₀ z : ℂ) : ℂ := ∑' s, a s * (z - z₀) ^ s

theorem powerSeriesSum_self (a : ℕ → ℂ) (z₀ : ℂ) : powerSeriesSum a z₀ z₀ = a 0 := by
  unfold powerSeriesSum
  rw [tsum_eq_single 0 fun s hs => by simp [hs]]
  simp

theorem hasRadiusGE_of_summable {a : ℕ → ℂ} {z₀ : ℂ} {R : ℝ}
    (h : ∀ z ∈ ball z₀ R, Summable fun s => ‖a s * (z - z₀) ^ s‖) : HasRadiusGE a R := by
  intro ρ hρ hρR
  have hz : z₀ + ρ ∈ ball z₀ R := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_of_nonneg hρ.le]
    exact hρR
  have hs := h _ hz
  refine ⟨∑' s, ‖a s * (z₀ + ρ - z₀) ^ s‖, fun s => ?_⟩
  refine le_trans (le_of_eq ?_) (hs.le_tsum s fun _ _ => norm_nonneg _)
  rw [add_sub_cancel_left, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hρ.le]

theorem HasRadiusGE.summable_norm {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R) {z₀ z : ℂ}
    (hz : z ∈ ball z₀ R) : Summable fun s => ‖a s * (z - z₀) ^ s‖ := by
  have hr : ‖z - z₀‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
  have hr0 : 0 ≤ ‖z - z₀‖ := norm_nonneg _
  set ρ := (‖z - z₀‖ + R) / 2 with hρ
  have hρ0 : 0 < ρ := by linarith
  have hρR : ρ < R := by linarith
  have hrρ : ‖z - z₀‖ < ρ := by linarith
  obtain ⟨K, hK⟩ := h ρ hρ0 hρR
  have hq : ‖z - z₀‖ / ρ < 1 := (div_lt_one hρ0).mpr hrρ
  have hq0 : 0 ≤ ‖z - z₀‖ / ρ := by positivity
  refine Summable.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => ?_)
    ((summable_geometric_of_lt_one hq0 hq).mul_left K)
  rw [norm_mul, norm_pow, div_pow]
  have hρs : 0 < ρ ^ s := pow_pos hρ0 s
  calc ‖a s‖ * ‖z - z₀‖ ^ s = ‖a s‖ * ρ ^ s * (‖z - z₀‖ ^ s / ρ ^ s) := by field_simp
    _ ≤ K * (‖z - z₀‖ ^ s / ρ ^ s) :=
      mul_le_mul_of_nonneg_right (hK s) (by positivity)

theorem HasRadiusGE.summable {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R) {z₀ z : ℂ}
    (hz : z ∈ ball z₀ R) : Summable fun s => a s * (z - z₀) ^ s :=
  (h.summable_norm hz).of_norm

theorem HasRadiusGE.shift {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R) :
    HasRadiusGE (shiftDeriv a) R := by
  intro ρ hρ hρR
  set ρ₂ := (ρ + R) / 2 with hρ₂
  have hρ₂0 : 0 < ρ₂ := by linarith
  have hρ₂R : ρ₂ < R := by linarith
  have hρρ₂ : ρ < ρ₂ := by linarith
  clear_value ρ₂
  obtain ⟨K, hK⟩ := h ρ₂ hρ₂0 hρ₂R
  have hq0 : 0 ≤ ρ / ρ₂ := by positivity
  have hq1 : ρ / ρ₂ < 1 := (div_lt_one hρ₂0).mpr hρρ₂
  have hsum := summable_norm_pow_mul_geometric_of_norm_lt_one 1 (r := ρ / ρ₂)
    (by rwa [Real.norm_of_nonneg hq0])
  refine ⟨K / ρ * ∑' n : ℕ, ‖(n : ℝ) ^ 1 * (ρ / ρ₂) ^ n‖, fun s => ?_⟩
  have hb : ((s + 1 : ℕ) : ℝ) * (ρ / ρ₂) ^ (s + 1) ≤
      ∑' n : ℕ, ‖(n : ℝ) ^ 1 * (ρ / ρ₂) ^ n‖ := by
    refine le_trans (le_of_eq ?_) (hsum.le_tsum (s + 1) fun _ _ => norm_nonneg _)
    rw [pow_one, Real.norm_of_nonneg (by positivity)]
  have hK' := hK (s + 1)
  have hKnn : 0 ≤ K / ρ := by
    have : 0 ≤ ‖a (s + 1)‖ * ρ₂ ^ (s + 1) := by positivity
    exact div_nonneg (this.trans hK') hρ.le
  rw [shiftDeriv, norm_mul, Complex.norm_natCast]
  calc ((s + 1 : ℕ) : ℝ) * ‖a (s + 1)‖ * ρ ^ s
      = ‖a (s + 1)‖ * ρ₂ ^ (s + 1) * (((s + 1 : ℕ) : ℝ) * (ρ / ρ₂) ^ (s + 1)) / ρ := by
        rw [div_pow]; field_simp; ring
    _ ≤ K * (((s + 1 : ℕ) : ℝ) * (ρ / ρ₂) ^ (s + 1)) / ρ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK' (by positivity)) hρ.le
    _ = K / ρ * (((s + 1 : ℕ) : ℝ) * (ρ / ρ₂) ^ (s + 1)) := by ring
    _ ≤ K / ρ * ∑' n : ℕ, ‖(n : ℝ) ^ 1 * (ρ / ρ₂) ^ n‖ := mul_le_mul_of_nonneg_left hb hKnn

/-- Termwise differentiation of a power series inside its disc of convergence. -/
theorem HasRadiusGE.hasDerivAt {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R) {z₀ z : ℂ}
    (hz : z ∈ ball z₀ R) :
    HasDerivAt (powerSeriesSum a z₀) (powerSeriesSum (shiftDeriv a) z₀ z) z := by
  have hr : ‖z - z₀‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
  have hr0 : 0 ≤ ‖z - z₀‖ := norm_nonneg _
  set ρ' := (2 * ‖z - z₀‖ + R) / 3 with hρ'
  set ρ := (‖z - z₀‖ + 2 * R) / 3 with hρ
  have hρ'0 : 0 < ρ' := by linarith
  have hρ'ρ : ρ' < ρ := by linarith
  have hρR : ρ < R := by linarith
  have hrρ' : ‖z - z₀‖ < ρ' := by linarith
  have hρ0 : 0 < ρ := by linarith
  clear_value ρ' ρ
  obtain ⟨K, hK⟩ := h ρ hρ0 hρR
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 0)
  have hq0 : 0 ≤ ρ' / ρ := by positivity
  have hq1 : ρ' / ρ < 1 := (div_lt_one hρ0).mpr hρ'ρ
  have hsum : Summable fun n : ℕ => K / ρ' * ‖(n : ℝ) ^ 1 * (ρ' / ρ) ^ n‖ :=
    (summable_norm_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_of_nonneg hq0])).mul_left _
  have hzt : z ∈ ball z₀ ρ' := by rwa [mem_ball, dist_eq_norm]
  have hbound : ∀ (s : ℕ), ∀ y ∈ ball z₀ ρ',
      ‖a s * (s * (y - z₀) ^ (s - 1))‖ ≤ K / ρ' * ‖(s : ℝ) ^ 1 * (ρ' / ρ) ^ s‖ := by
    intro s y hy
    have hy' : ‖y - z₀‖ < ρ' := by rwa [mem_ball, dist_eq_norm] at hy
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, pow_one,
      Real.norm_of_nonneg (by positivity)]
    rcases s with _ | s
    · simp
    · simp only [Nat.add_sub_cancel]
      have h1 : ‖a (s + 1)‖ ≤ K / ρ ^ (s + 1) := (le_div_iff₀ (pow_pos hρ0 _)).mpr (hK (s + 1))
      have h2 : ‖y - z₀‖ ^ s ≤ ρ' ^ s := pow_le_pow_left₀ (norm_nonneg _) hy'.le s
      calc ‖a (s + 1)‖ * (((s + 1 : ℕ) : ℝ) * ‖y - z₀‖ ^ s)
          ≤ K / ρ ^ (s + 1) * (((s + 1 : ℕ) : ℝ) * ρ' ^ s) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
              (div_nonneg hK0 (by positivity))
        _ = K / ρ' * (((s + 1 : ℕ) : ℝ) * (ρ' / ρ) ^ (s + 1)) := by
          rw [div_pow]; field_simp; ring
  have key := hasDerivAt_tsum_of_isPreconnected (t := ball z₀ ρ') (y₀ := z)
    (g := fun s y => a s * (y - z₀) ^ s) (g' := fun s y => a s * (s * (y - z₀) ^ (s - 1)))
    hsum isOpen_ball (convex_ball z₀ ρ').isPreconnected (fun s y _ => ?_) hbound hzt
    (h.summable hz) hzt
  · unfold powerSeriesSum
    convert key using 1
    have hsum' : Summable fun s : ℕ => a s * (s * (z - z₀) ^ (s - 1)) :=
      Summable.of_norm_bounded hsum fun s => hbound s z hzt
    rw [hsum'.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel, shiftDeriv]
    refine tsum_congr fun s => ?_
    push_cast
    ring
  · exact (((hasDerivAt_pow s (y - z₀)).comp y ((hasDerivAt_id y).sub_const z₀)).const_mul
      (a s)).congr_deriv (by simp)

theorem HasRadiusGE.continuousAt {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R) {z₀ z : ℂ}
    (hz : z ∈ ball z₀ R) : ContinuousAt (powerSeriesSum a z₀) z :=
  (h.hasDerivAt hz).continuousAt

/-- `(z − z₀) u′(z) = ∑ s aₛ (z − z₀)^s`. -/
theorem HasRadiusGE.hasSum_natCast_mul {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R) {z₀ z : ℂ}
    (hz : z ∈ ball z₀ R) :
    HasSum (fun n : ℕ => (n : ℂ) * a n * (z - z₀) ^ n)
      ((z - z₀) * powerSeriesSum (shiftDeriv a) z₀ z) := by
  have hs := (h.shift.summable hz).hasSum.mul_left (z - z₀)
  unfold powerSeriesSum
  rw [← hasSum_nat_add_iff' 1]
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  convert hs using 1
  funext n
  simp only [shiftDeriv]
  push_cast
  ring

/-- `(z − z₀)² u″(z) = ∑ s (s − 1) aₛ (z − z₀)^s`. -/
theorem HasRadiusGE.hasSum_natCast_mul_sub_one {a : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE a R)
    {z₀ z : ℂ} (hz : z ∈ ball z₀ R) :
    HasSum (fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1) * a n * (z - z₀) ^ n)
      ((z - z₀) ^ 2 * powerSeriesSum (shiftDeriv (shiftDeriv a)) z₀ z) := by
  have hs := (h.shift.hasSum_natCast_mul hz).mul_left (z - z₀)
  unfold powerSeriesSum at hs ⊢
  rw [← hasSum_nat_add_iff' 1]
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  convert hs using 1
  · funext n
    simp only [shiftDeriv]
    push_cast
    ring
  · ring

/-- Cauchy product of two absolutely convergent power series. -/
theorem hasSum_mul_powerSeriesSum {a b : ℕ → ℂ} {z₀ z : ℂ}
    (ha : Summable fun s => ‖a s * (z - z₀) ^ s‖) (hb : Summable fun s => ‖b s * (z - z₀) ^ s‖) :
    HasSum (fun n : ℕ => (∑ r ∈ range (n + 1), a (n - r) * b r) * (z - z₀) ^ n)
      (powerSeriesSum a z₀ z * powerSeriesSum b z₀ z) := by
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_norm
  unfold powerSeriesSum
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb]
  convert hsum.hasSum using 1
  funext n
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_mul]
  refine sum_congr rfl fun r hr => ?_
  have hr' : r ≤ n := mem_range_succ_iff.mp hr
  dsimp only
  rw [← pow_sub_mul_pow (z - z₀) hr']
  ring

end Azurite.DLMF
