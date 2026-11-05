/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8Newton
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.Nat.Prime.Int

/-!
# DLMF §3.8(iii): other methods

* Bisection (`bisectStep`): the intervals shrink to a zero, with error `(b − a)/2ⁿ`
  (`dlmf_3_8_iii_bisection`). **Imprecision**: "All zeros … can be computed" fails for zeros
  without a sign change. For `x (x − 1/3)²` on `[−1, 1]` the zero `1/3` is never bracketed
  (`dlmf_3_8_iii_bisection_misses`).
* Regula falsi: 3.8.6 (`rfPoint`, `dlmf_3_8_6`, inverse linear interpolation `rfPoint_interp`),
  the bracketing step (`rfStep`, `rfPoint_mem`, `rfStep_bracket`). Linear convergence with exact
  ratio `1 − f′(ξ)(b − ξ)/f(b) ∈ (0, 1)` for strictly convex `f` (`dlmf_3_8_iii_regula_falsi`;
  `not_mem_convIndices_of_ge`).
* Steffensen's method 3.8.7 (`steffStep`): local quadratic convergence over `ℝ` and `ℂ` at a
  fixed point with `φ′(ζ) ≠ 1` (`dlmf_3_8_7`, `dlmf_3_8_7_of_contDiffAt`; `lip_taylor`,
  `steffStep_eq`). **Imprecision**: the hypothesis `φ′(ζ) ≠ 1` is needed. For `φ(z) = z + z²` the
  convergence is only linear (`dlmf_3_8_7_erratum`).

The secant method is in `Section8Secant`.
-/

open Filter Topology Set Metric

namespace Azurite.DLMF

/-! ### Bisection -/

section Bisection

variable {f : ℝ → ℝ}

/-- One bisection step: keep the half `[a, m]` if `f(a) f(m) ≤ 0`, else `[m, b]`. -/
noncomputable def bisectStep (f : ℝ → ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  if f I.1 * f ((I.1 + I.2) / 2) ≤ 0 then (I.1, (I.1 + I.2) / 2) else ((I.1 + I.2) / 2, I.2)

theorem bisectStep_spec {I : ℝ × ℝ} (h : f I.1 * f I.2 ≤ 0) (hle : I.1 ≤ I.2) :
    f (bisectStep f I).1 * f (bisectStep f I).2 ≤ 0 ∧ I.1 ≤ (bisectStep f I).1 ∧
      (bisectStep f I).1 ≤ (bisectStep f I).2 ∧ (bisectStep f I).2 ≤ I.2 ∧
      (bisectStep f I).2 - (bisectStep f I).1 = (I.2 - I.1) / 2 := by
  unfold bisectStep
  split_ifs with hm
  · simp only; refine ⟨hm, le_rfl, by linarith, by linarith, by ring⟩
  · simp only
    push Not at hm
    refine ⟨?_, by linarith, by linarith, le_rfl, by ring⟩
    have h1 : 0 < f I.1 ^ 2 := by
      rcases eq_or_ne (f I.1) 0 with h0 | h0
      · rw [h0, zero_mul] at hm; exact absurd hm (lt_irrefl 0)
      · positivity
    nlinarith [mul_nonneg (le_of_lt hm) (neg_nonneg.mpr h)]

theorem bisect_iter (a b : ℝ) (hab : a ≤ b) (hf : f a * f b ≤ 0) (n : ℕ) :
    f ((bisectStep f)^[n] (a, b)).1 * f ((bisectStep f)^[n] (a, b)).2 ≤ 0 ∧
      a ≤ ((bisectStep f)^[n] (a, b)).1 ∧
      ((bisectStep f)^[n] (a, b)).1 ≤ ((bisectStep f)^[n] (a, b)).2 ∧
      ((bisectStep f)^[n] (a, b)).2 ≤ b ∧
      ((bisectStep f)^[n] (a, b)).2 - ((bisectStep f)^[n] (a, b)).1 = (b - a) / 2 ^ n ∧
      ((bisectStep f)^[n] (a, b)).1 ≤ ((bisectStep f)^[n + 1] (a, b)).1 ∧
      ((bisectStep f)^[n + 1] (a, b)).2 ≤ ((bisectStep f)^[n] (a, b)).2 := by
  induction n with
  | zero =>
    have := bisectStep_spec (f := f) (I := (a, b)) hf hab
    simp only [Function.iterate_zero, id]
    exact ⟨hf, le_rfl, hab, le_rfl, by simp, this.2.1, this.2.2.2.1⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := ih
    have hs := bisectStep_spec h1 h3
    rw [Function.iterate_succ_apply' _ (n + 1)]
    rw [Function.iterate_succ_apply']
    have hs2 := bisectStep_spec hs.1 hs.2.2.1
    refine ⟨hs.1, by linarith [hs.2.1], hs.2.2.1, by linarith [hs.2.2.2.1], ?_, hs2.2.1,
      hs2.2.2.2.1⟩
    rw [hs.2.2.2.2, h5, pow_succ]; field_simp

/-- **DLMF §3.8(iii), bisection**: if `f(a) f(b) ≤ 0` (in particular `< 0`), `a ≤ b` and `f` is
continuous on `[a, b]`, the bisection intervals `[aₙ, bₙ]` shrink to a zero `ξ ∈ [a, b]`, with
`|aₙ − ξ|, |bₙ − ξ| ≤ (b − a)/2ⁿ`: linear convergence with ratio `1/2`. -/
theorem dlmf_3_8_iii_bisection {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hf : f a * f b ≤ 0) : ∃ ξ ∈ Icc a b, f ξ = 0 ∧ ∀ n,
      ξ ∈ Icc ((bisectStep f)^[n] (a, b)).1 ((bisectStep f)^[n] (a, b)).2 ∧
      |((bisectStep f)^[n] (a, b)).1 - ξ| ≤ (b - a) / 2 ^ n ∧
      |((bisectStep f)^[n] (a, b)).2 - ξ| ≤ (b - a) / 2 ^ n := by
  set A : ℕ → ℝ := fun n => ((bisectStep f)^[n] (a, b)).1
  set B : ℕ → ℝ := fun n => ((bisectStep f)^[n] (a, b)).2
  have hit := bisect_iter (f := f) a b hab hf
  have hAmono : Monotone A := monotone_nat_of_le_succ fun n => (hit n).2.2.2.2.2.1
  have hBanti : Antitone B := antitone_nat_of_succ_le fun n => (hit n).2.2.2.2.2.2
  have hAB : ∀ m n, A m ≤ B n := fun m n => by
    rcases le_total m n with h | h
    · exact (hAmono h).trans (hit n).2.2.1
    · exact (hit m).2.2.1.trans (hBanti h)
  have hbdd : BddAbove (range A) := ⟨b, by rintro _ ⟨n, rfl⟩; exact (hAB n 0).trans (by simp [B])⟩
  set ξ := ⨆ n, A n
  have hAξ : ∀ n, A n ≤ ξ := fun n => le_ciSup hbdd n
  have hξB : ∀ n, ξ ≤ B n := fun n => ciSup_le fun m => hAB m n
  have hwidth : ∀ n, B n - A n = (b - a) / 2 ^ n := fun n => (hit n).2.2.2.2.1
  have hξI : ξ ∈ Icc a b := ⟨(hit 0).2.1.trans (hAξ 0), (hξB 0).trans (by simp [B])⟩
  have hw0 : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (b - a) |>.congr fun n => by rw [div_pow, one_pow]; ring
  have hA : Tendsto A atTop (𝓝 ξ) := tendsto_atTop_ciSup hAmono hbdd
  have hB : Tendsto B atTop (𝓝 ξ) := by
    have := hA.add hw0
    rw [add_zero] at this
    exact this.congr fun n => by rw [← hwidth n]; ring
  have hmemA : ∀ n, A n ∈ Icc a b := fun n => ⟨(hit n).2.1, (hit n).2.2.1.trans (hit n).2.2.2.1⟩
  have hmemB : ∀ n, B n ∈ Icc a b := fun n => ⟨(hit n).2.1.trans (hit n).2.2.1, (hit n).2.2.2.1⟩
  have hfA : Tendsto (fun n => f (A n)) atTop (𝓝 (f ξ)) :=
    (hc ξ hξI).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hA, Eventually.of_forall hmemA⟩)
  have hfB : Tendsto (fun n => f (B n)) atTop (𝓝 (f ξ)) :=
    (hc ξ hξI).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hB, Eventually.of_forall hmemB⟩)
  have hsq : f ξ * f ξ ≤ 0 :=
    le_of_tendsto (hfA.mul hfB) (Eventually.of_forall fun n => (hit n).1)
  refine ⟨ξ, hξI, by nlinarith [mul_self_nonneg (f ξ)], fun n => ⟨⟨hAξ n, hξB n⟩, ?_, ?_⟩⟩
  · rw [abs_of_nonpos (by linarith [hAξ n]), ← hwidth n]; linarith [hξB n]
  · rw [abs_of_nonneg (by linarith [hξB n]), ← hwidth n]; linarith [hAξ n]

/-- **DLMF §3.8(iii), imprecision**: "All zeros of `f` in the original interval `[a, b]` can be
computed to any predetermined accuracy" needs more than bisection: sign changes cannot detect
zeros of even multiplicity. For `f(x) = x (x − 1/3)²` on `[−1, 1]` (`f(−1) f(1) < 0`) the zero
`1/3` is never bracketed: every bisection interval after the first lies in `[−1, 0]`. -/
theorem dlmf_3_8_iii_bisection_misses :
    let f : ℝ → ℝ := fun x => x * (x - 1 / 3) ^ 2
    f (-1) * f 1 < 0 ∧ f (1 / 3) = 0 ∧ ∀ n, ((bisectStep f)^[n + 1] (-1, 1)).2 ≤ 0 := by
  intro f
  refine ⟨by norm_num [f], by norm_num [f], fun n => ?_⟩
  -- endpoints are dyadic, hence `≠ 1/3`
  have hdy : ∀ x : ℝ, (∃ k : ℤ, ∃ m : ℕ, x = k / 2 ^ m) → x ≠ 1 / 3 := by
    rintro x ⟨k, m, rfl⟩ h
    have h3 : (3 * k : ℝ) = 2 ^ m := by field_simp at h; linarith
    have h3' : (3 * k : ℤ) = 2 ^ m := by exact_mod_cast h3
    have : (3 : ℤ) ∣ 2 ^ m := ⟨k, h3'.symm⟩
    have := (Int.prime_three).dvd_of_dvd_pow this
    omega
  have hsign : ∀ x y : ℝ, x ≠ 1 / 3 → y ≠ 1 / 3 → (f x * f y ≤ 0 ↔ x * y ≤ 0) := by
    intro x y hx hy
    have hp : 0 < ((x - 1 / 3) * (y - 1 / 3)) ^ 2 := by
      have : (x - 1 / 3) * (y - 1 / 3) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)
      positivity
    have e : f x * f y = (x * y) * ((x - 1 / 3) * (y - 1 / 3)) ^ 2 := by simp only [f]; ring
    rw [e]
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  -- the iteration for `f` agrees with that for `id`, and stays in `[−1, 0]`
  have key : ∀ n, (∃ k : ℤ, ∃ m : ℕ, ((bisectStep f)^[n + 1] (-1, 1)).1 = k / 2 ^ m) ∧
      (∃ k : ℤ, ∃ m : ℕ, ((bisectStep f)^[n + 1] (-1, 1)).2 = k / 2 ^ m) ∧
      ((bisectStep f)^[n + 1] (-1, 1)).1 < 0 ∧ ((bisectStep f)^[n + 1] (-1, 1)).2 ≤ 0 ∧
      ((bisectStep f)^[n + 1] (-1, 1)).1 < ((bisectStep f)^[n + 1] (-1, 1)).2 := by
    intro n
    induction n with
    | zero =>
      have : bisectStep f (-1, 1) = (-1, 0) := by simp [bisectStep, f]
      simp only [zero_add, Function.iterate_one, this]
      exact ⟨⟨-1, 0, by simp⟩, ⟨0, 0, by simp⟩, by norm_num, le_rfl, by norm_num⟩
    | succ n ih =>
      obtain ⟨⟨k1, m1, h1⟩, ⟨k2, m2, h2⟩, hn1, hn2, hlt⟩ := ih
      rw [Function.iterate_succ_apply']
      set I := (bisectStep f)^[n + 1] (-1, 1)
      have hm : ∃ k : ℤ, ∃ m : ℕ, (I.1 + I.2) / 2 = k / 2 ^ m :=
        ⟨k1 * 2 ^ m2 + k2 * 2 ^ m1, m1 + m2 + 1, by
          rw [h1, h2]; push_cast; field_simp; ring⟩
      unfold bisectStep
      split_ifs with hc
      · exact ⟨⟨k1, m1, h1⟩, hm, hn1, by linarith, by linarith⟩
      · exact ⟨hm, ⟨k2, m2, h2⟩, by linarith, hn2, by linarith⟩
  exact (key n).2.2.2.1

end Bisection

/-! ### A lemma on orders of convergence -/

/-- If `|e_{n+1}| ≥ c |eₙ|` eventually with `c > 0`, `eₙ ≠ 0`, `eₙ → 0`, then 3.8.3 holds for no
`p > 1`. -/
theorem not_mem_convIndices_of_ge {E : Type*} [NormedAddCommGroup E] {z : ℕ → E} {ζ : E}
    {c : ℝ} (hc : 0 < c) (hge : ∀ᶠ n in atTop, c * ‖z n - ζ‖ ≤ ‖z (n + 1) - ζ‖)
    (hne : ∀ n, z n ≠ ζ) (hz : Tendsto z atTop (𝓝 ζ)) {p : ℝ} (hp : 1 < p) :
    p ∉ convIndices z ζ := by
  rintro ⟨A₀, hA₀⟩
  have he0 : Tendsto (fun n => ‖z n - ζ‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hz
  have ht : Tendsto (fun n => ‖z n - ζ‖ ^ (p - 1)) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (p - 1) (Or.inr (by linarith))).tendsto.comp he0
    simpa [Function.comp_def, Real.zero_rpow (by linarith : p - 1 ≠ 0)] using this
  obtain ⟨n, ⟨h1, h2⟩, h3⟩ := ((hA₀.and hge).and (ht.eventually (gt_mem_nhds
    (show 0 < c / (|A₀| + 1) by positivity)))).exists
  have hpos : 0 < ‖z n - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
  have hsplit : ‖z n - ζ‖ ^ p = ‖z n - ζ‖ ^ (p - 1) * ‖z n - ζ‖ := by
    rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
  have h4 : A₀ * ‖z n - ζ‖ ^ (p - 1) ≤ |A₀| * (c / (|A₀| + 1)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (norm_nonneg _) _)).trans
      (mul_le_mul_of_nonneg_left h3.le (abs_nonneg _))
  have h5 : |A₀| * (c / (|A₀| + 1)) < c := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg A₀]
  have h6 : c * ‖z n - ζ‖ < A₀ * ‖z n - ζ‖ ^ (p - 1) * ‖z n - ζ‖ := by
    rw [mul_assoc, ← hsplit]; exact lt_of_le_of_lt h2 h1
  nlinarith

/-! ### Regula falsi -/

section RegulaFalsi

variable {f : ℝ → ℝ}

/-- **DLMF 3.8.6**: `x₂ = (f₁x₀ − f₀x₁)/(f₁ − f₀)`. -/
noncomputable def rfPoint (f : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ := (f x₁ * x₀ - f x₀ * x₁) / (f x₁ - f x₀)

/-- **DLMF 3.8.6**: the two forms agree. -/
theorem dlmf_3_8_6 {x₀ x₁ : ℝ} (h : f x₁ ≠ f x₀) :
    x₁ - (x₁ - x₀) / (f x₁ - f x₀) * f x₁ = rfPoint f x₀ x₁ := by
  have h' : f x₁ - f x₀ ≠ 0 := sub_ne_zero.mpr h
  unfold rfPoint
  field_simp
  ring

/-- Inverse linear interpolation (§3.3(v)): `x₂` is the zero of the line through `(x₀, f₀)` and
`(x₁, f₁)`. -/
theorem rfPoint_interp {x₀ x₁ : ℝ} (hx : x₁ ≠ x₀) (h : f x₁ ≠ f x₀) :
    f x₀ + (f x₁ - f x₀) / (x₁ - x₀) * (rfPoint f x₀ x₁ - x₀) = 0 := by
  have h' : f x₁ - f x₀ ≠ 0 := sub_ne_zero.mpr h
  have hx' : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hx
  unfold rfPoint
  field_simp
  ring

/-- One step of regula falsi: continue with `x₂` and the endpoint at which `f` has the sign
opposite to `f(x₂)`. -/
noncomputable def rfStep (f : ℝ → ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  if f (rfPoint f I.1 I.2) * f I.1 < 0 then (I.1, rfPoint f I.1 I.2) else (rfPoint f I.1 I.2, I.2)

theorem rfPoint_mem {a b : ℝ} (hab : a < b) (h : f a * f b < 0) : rfPoint f a b ∈ Ioo a b := by
  have hne : f b - f a ≠ 0 := by intro h0; rw [sub_eq_zero.mp h0] at h; nlinarith [sq_nonneg (f a)]
  have e1 : rfPoint f a b - a = (b - a) * (-f a / (f b - f a)) := by
    unfold rfPoint; field_simp; ring
  have e2 : b - rfPoint f a b = (b - a) * (f b / (f b - f a)) := by
    unfold rfPoint; field_simp; ring
  have ht1 : 0 < -f a / (f b - f a) := by
    rcases lt_or_gt_of_ne hne with hd | hd
    · exact div_pos_of_neg_of_neg (by nlinarith) hd
    · exact div_pos (by nlinarith) hd
  have ht2 : 0 < f b / (f b - f a) := by
    rcases lt_or_gt_of_ne hne with hd | hd
    · exact div_pos_of_neg_of_neg (by nlinarith) hd
    · exact div_pos (by nlinarith) hd
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hab) ht1]
  · nlinarith [mul_pos (sub_pos.mpr hab) ht2]

/-- Regula falsi keeps a bracket: the new interval lies in the old one and `f` does not have the
same strict sign at both ends. -/
theorem rfStep_bracket {a b : ℝ} (hab : a < b) (h : f a * f b < 0) :
    a ≤ (rfStep f (a, b)).1 ∧ (rfStep f (a, b)).1 < (rfStep f (a, b)).2 ∧
      (rfStep f (a, b)).2 ≤ b ∧ f (rfStep f (a, b)).1 * f (rfStep f (a, b)).2 ≤ 0 := by
  have hc := rfPoint_mem hab h
  unfold rfStep
  split_ifs with hs
  · exact ⟨le_rfl, hc.1, hc.2.le, by simp only; linarith [mul_comm (f a) (f (rfPoint f a b))]⟩
  · push Not at hs
    refine ⟨hc.1.le, hc.2, le_rfl, ?_⟩
    simp only
    have : 0 < f a ^ 2 := by
      rcases eq_or_ne (f a) 0 with h0 | h0
      · rw [h0, zero_mul] at h; exact absurd h (lt_irrefl 0)
      · positivity
    nlinarith [mul_nonneg hs (neg_nonneg.mpr h.le)]

/-- **DLMF §3.8(iii), regula falsi: "The convergence is linear"**, for strictly convex `f` on
`[a, b]` with `f(a) < 0 < f(b)` and a differentiable zero `ξ`. The endpoint `b` stays fixed, the
other increases to `ξ`, and `(ξ − x_{n+1})/(ξ − xₙ) → C = 1 − f′(ξ)(b − ξ)/f(b) ∈ (0, 1)`. So the
convergence is linear and of no order `p > 1`. -/
theorem dlmf_3_8_iii_regula_falsi {a b ξ d : ℝ} (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hconv : StrictConvexOn ℝ (Icc a b) f) (ha : f a < 0) (hb : 0 < f b) (hξ : ξ ∈ Ioo a b)
    (hz : f ξ = 0) (hd : HasDerivAt f d ξ) :
    (∀ n, ((rfStep f)^[n] (a, b)).2 = b) ∧ Monotone (fun n => ((rfStep f)^[n] (a, b)).1) ∧
      (∀ n, ((rfStep f)^[n] (a, b)).1 < ξ) ∧
      Tendsto (fun n => ((rfStep f)^[n] (a, b)).1) atTop (𝓝 ξ) ∧
      0 < 1 - d * (b - ξ) / f b ∧ 1 - d * (b - ξ) / f b < 1 ∧
      Tendsto (fun n => (ξ - ((rfStep f)^[n + 1] (a, b)).1) / (ξ - ((rfStep f)^[n] (a, b)).1))
        atTop (𝓝 (1 - d * (b - ξ) / f b)) ∧
      IsLinearConv (fun n => ((rfStep f)^[n] (a, b)).1) ξ ∧
      ∀ p > 1, p ∉ convIndices (fun n => ((rfStep f)^[n] (a, b)).1) ξ := by
  have haS : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hbS : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hξS : ξ ∈ Icc a b := Ioo_subset_Icc_self hξ
  -- signs of `f`
  have hneg : ∀ x ∈ Icc a b, x < ξ → f x < 0 := by
    intro x hx hxξ
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact ha
    set θ := (ξ - x) / (ξ - a)
    have hθ0 : 0 < θ := div_pos (by linarith) (by linarith [hξ.1])
    have hθ1 : 0 < 1 - θ := by
      simp only [θ]; rw [sub_pos, div_lt_one (by linarith [hξ.1])]; linarith
    have hξa : ξ - a ≠ 0 := by linarith [hξ.1]
    have hpt : θ • a + (1 - θ) • ξ = x := by
      simp only [θ, smul_eq_mul]; field_simp; ring
    have := hconv.2 haS hξS (ne_of_lt hξ.1) hθ0 hθ1 (by ring)
    rw [hpt, smul_eq_mul, smul_eq_mul, hz, mul_zero, add_zero] at this
    nlinarith
  have hpos : ∀ x ∈ Icc a b, ξ < x → 0 < f x := by
    intro x hx hξx
    have := hconv.convexOn.slope_mono_adjacent haS hx hξ.1 hξx
    rw [hz] at this
    have h1 : 0 < (0 - f a) / (ξ - a) := div_pos (by linarith) (by linarith [hξ.1])
    have h3 : 0 < (f x - 0) / (x - ξ) := lt_of_lt_of_le h1 this
    rw [sub_zero] at h3
    exact (div_pos_iff_of_pos_right (by linarith)).mp h3
  -- the chord step from `[x, b]`, `x < ξ`
  have hstep : ∀ x ∈ Icc a b, x < ξ → x < rfPoint f x b ∧ rfPoint f x b < ξ ∧
      rfStep f (x, b) = (rfPoint f x b, b) := by
    intro x hx hxξ
    have hfx := hneg x hx hxξ
    have hmem := rfPoint_mem (f := f) (lt_trans hxξ hξ.2) (by nlinarith)
    set c := rfPoint f x b
    have hden : 0 < f b - f x := by linarith
    set θ := f b / (f b - f x)
    have hθ0 : 0 < θ := div_pos hb hden
    have hθ1 : 0 < 1 - θ := by
      simp only [θ]; rw [sub_pos, div_lt_one hden]; linarith
    have hpt : θ • x + (1 - θ) • b = c := by
      simp only [θ, c, rfPoint, smul_eq_mul]; field_simp; ring
    have hval : θ • f x + (1 - θ) • f b = 0 := by
      simp only [θ, smul_eq_mul]; field_simp; ring
    have hfc := hconv.2 hx hbS (ne_of_lt (lt_trans hxξ hξ.2)) hθ0 hθ1 (by ring)
    rw [hpt, hval] at hfc
    have hcξ : c < ξ := by
      by_contra h; push Not at h
      rcases eq_or_lt_of_le h with h' | h'
      · rw [← h', hz] at hfc; exact lt_irrefl 0 hfc
      · have := hpos c ⟨by linarith [hmem.1, hx.1], hmem.2.le⟩ h'; linarith
    refine ⟨hmem.1, hcξ, ?_⟩
    have : ¬ f c * f x < 0 := by nlinarith
    simp only [rfStep]
    split_ifs with h
    · exact absurd h this
    · rfl
  -- the iteration
  have hit : ∀ n, ((rfStep f)^[n] (a, b)).2 = b ∧ ((rfStep f)^[n] (a, b)).1 ∈ Icc a b ∧
      ((rfStep f)^[n] (a, b)).1 < ξ := by
    intro n
    induction n with
    | zero => exact ⟨rfl, haS, hξ.1⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [Function.iterate_succ_apply']
      have hI : (rfStep f)^[n] (a, b) = (((rfStep f)^[n] (a, b)).1, b) := by
        ext <;> simp [h1]
      obtain ⟨hlt, hcξ, he⟩ := hstep _ h2 h3
      rw [hI, he]
      exact ⟨rfl, ⟨by linarith [h2.1], by linarith [hξ.2]⟩, hcξ⟩
  set x : ℕ → ℝ := fun n => ((rfStep f)^[n] (a, b)).1
  have hxs : ∀ n, x (n + 1) = rfPoint f (x n) b := fun n => by
    simp only [x]
    rw [Function.iterate_succ_apply']
    have hI : (rfStep f)^[n] (a, b) = (((rfStep f)^[n] (a, b)).1, b) := by
      ext <;> simp [(hit n).1]
    rw [hI, (hstep _ (hit n).2.1 (hit n).2.2).2.2]
  have hmono : Monotone x := monotone_nat_of_le_succ fun n => by
    rw [hxs]; exact (hstep _ (hit n).2.1 (hit n).2.2).1.le
  have hbdd : BddAbove (range x) := ⟨ξ, by rintro _ ⟨n, rfl⟩; exact (hit n).2.2.le⟩
  set L := ⨆ n, x n
  have hxL : Tendsto x atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have hLξ : L ≤ ξ := ciSup_le fun n => (hit n).2.2.le
  have hLS : L ∈ Icc a b := ⟨(hit 0).2.1.1.trans (le_ciSup hbdd 0), by linarith [hξ.2]⟩
  have hfx : ∀ {y : ℝ} (hy : y ∈ Icc a b), Tendsto x atTop (𝓝 y) →
      Tendsto (fun n => f (x n)) atTop (𝓝 (f y)) := fun hy hxy =>
    (hcont _ hy).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hxy, Eventually.of_forall
      fun n => (hit n).2.1⟩)
  have hLeq : L = ξ := by
    by_contra hne
    have hLlt : L < ξ := lt_of_le_of_ne hLξ hne
    have hfL := hneg L hLS hLlt
    have hc : Tendsto (fun n => rfPoint f (x n) b) atTop (𝓝 (rfPoint f L b)) := by
      unfold rfPoint
      exact ((tendsto_const_nhds.mul hxL).sub ((hfx hLS hxL).mul tendsto_const_nhds)).div
        (tendsto_const_nhds.sub (hfx hLS hxL)) (by linarith)
    have h1 : Tendsto (fun n => x (n + 1)) atTop (𝓝 L) := hxL.comp (tendsto_add_atTop_nat 1)
    have h2 : rfPoint f L b = L := tendsto_nhds_unique (hc.congr fun n => (hxs n).symm) h1
    have := (hstep L hLS hLlt).1
    linarith
  rw [hLeq] at hxL
  -- the constant
  have hdpos : 0 < d := by
    have := hconv.slope_lt_of_hasDerivAt haS hξS hξ.1 hd
    rw [slope_def_field, hz] at this
    have : 0 < (0 - f a) / (ξ - a) := div_pos (by linarith) (by linarith [hξ.1])
    linarith
  have hdlt : d * (b - ξ) < f b := by
    have := hconv.lt_slope_of_hasDerivAt hξS hbS hξ.2 hd
    rw [slope_def_field, hz, sub_zero, lt_div_iff₀ (by linarith [hξ.2])] at this
    exact this
  have hC0 : 0 < 1 - d * (b - ξ) / f b := by
    rw [sub_pos, div_lt_one hb]; exact hdlt
  have hC1 : 1 - d * (b - ξ) / f b < 1 := by
    have : 0 < d * (b - ξ) / f b := div_pos (mul_pos hdpos (by linarith [hξ.2])) hb
    linarith
  -- the error ratio
  have hne : ∀ n, x n ≠ ξ := fun n => ne_of_lt (hit n).2.2
  have hratio : ∀ n, (ξ - x (n + 1)) / (ξ - x n) =
      (f b - f (x n) / (x n - ξ) * (b - ξ)) / (f b - f (x n)) := fun n => by
    rw [hxs]
    have h1 : f b - f (x n) ≠ 0 := by linarith [hneg _ (hit n).2.1 (hit n).2.2]
    have h2 : ξ - x n ≠ 0 := sub_ne_zero.mpr (hne n).symm
    have h3 : x n - ξ ≠ 0 := sub_ne_zero.mpr (hne n)
    unfold rfPoint
    field_simp
    ring
  have hslope : Tendsto (fun n => f (x n) / (x n - ξ)) atTop (𝓝 d) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp hd).comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxL, Eventually.of_forall hne⟩)
    refine h.congr fun n => ?_
    simp [Function.comp, slope_def_field, hz]
  have hf0 : Tendsto (fun n => f (x n)) atTop (𝓝 0) := by
    rw [← hz]; exact hfx hξS hxL
  have hlim : Tendsto (fun n => (ξ - x (n + 1)) / (ξ - x n)) atTop
      (𝓝 (1 - d * (b - ξ) / f b)) := by
    have := ((tendsto_const_nhds (x := f b)).sub (hslope.mul (tendsto_const_nhds (x := b - ξ)))).div
      ((tendsto_const_nhds (x := f b)).sub hf0) (show f b - 0 ≠ 0 by linarith)
    have heqC : (f b - d * (b - ξ)) / (f b - 0) = 1 - d * (b - ξ) / f b := by
      rw [sub_zero]; field_simp
    rw [heqC] at this
    exact this.congr fun n => (hratio n).symm
  refine ⟨fun n => (hit n).1, hmono, fun n => (hit n).2.2, hxL, hC0, hC1, hlim, ?_, ?_⟩
  · refine ⟨(1 - d * (b - ξ) / f b + 1) / 2, by linarith, ?_⟩
    filter_upwards [hlim.eventually (gt_mem_nhds (show 1 - d * (b - ξ) / f b <
      (1 - d * (b - ξ) / f b + 1) / 2 by linarith))] with n hn
    have hp := sub_pos.mpr (hit n).2.2
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm (x n),
      abs_of_pos (sub_pos.mpr (hit (n + 1)).2.2), abs_of_pos hp]
    rw [div_lt_iff₀ hp] at hn
    exact hn
  · intro p hp
    refine not_mem_convIndices_of_ge (c := (1 - d * (b - ξ) / f b) / 2) (by linarith) ?_ hne
      hxL hp
    filter_upwards [hlim.eventually (lt_mem_nhds (show (1 - d * (b - ξ) / f b) / 2 <
      1 - d * (b - ξ) / f b by linarith))] with n hn
    have hp' := sub_pos.mpr (hit n).2.2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm (x (n + 1)),
      abs_of_pos (sub_pos.mpr (hit (n + 1)).2.2), abs_of_pos hp']
    rw [lt_div_iff₀ hp'] at hn
    exact hn.le

end RegulaFalsi

/-! ### Steffensen's method -/

section Steffensen

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **DLMF 3.8.7**: `z_{n+1} = zₙ − (φ(zₙ) − zₙ)²/(φ(φ(zₙ)) − 2φ(zₙ) + zₙ)`. -/
noncomputable def steffStep (φ : 𝕜 → 𝕜) (z : 𝕜) : 𝕜 :=
  z - (φ z - z) ^ 2 / (φ (φ z) - 2 * φ z + z)

/-- Taylor's bound `|g(y) − g(x) − g′(x)(y − x)| ≤ L |y − x|²` for `g′` `L`-Lipschitz on
`B(ζ, r)` and `x, y ∈ B(ζ, r/3)`. -/
theorem lip_taylor {g : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hL0 : 0 ≤ L)
    (hg : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 g z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r, ‖deriv g w - deriv g z‖ ≤ L * ‖w - z‖) {x y : 𝕜}
    (hx : ‖x - ζ‖ < r / 3) (hy : ‖y - ζ‖ < r / 3) :
    ‖g y - g x - deriv g x * (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
  set s := closedBall x ‖y - x‖
  have hxs : x ∈ s := mem_closedBall_self (norm_nonneg _)
  have hys : y ∈ s := by rw [mem_closedBall, dist_eq_norm]
  have hsub : s ⊆ ball ζ r := fun w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖w - ζ‖ ≤ ‖w - x‖ + ‖x - ζ‖ := by
      calc ‖w - ζ‖ = ‖(w - x) + (x - ζ)‖ := by abel_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖y - x‖ ≤ ‖y - ζ‖ + ‖x - ζ‖ := by
      calc ‖y - x‖ = ‖(y - ζ) - (x - ζ)‖ := by abel_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hxr : x ∈ ball ζ r := hsub hxs
  set h : 𝕜 → 𝕜 := fun w => g w - deriv g x * w
  have hh : ∀ w ∈ s, HasDerivWithinAt h (deriv g w - deriv g x) s w := fun w hw =>
    (((hg w (hsub hw)).hasDerivAt.sub ((hasDerivAt_id w).const_mul (deriv g x))).congr_deriv
      (by simp)).hasDerivWithinAt
  have hmvt := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_hasDerivWithin_le hh
    (C := L * ‖y - x‖) (fun w hw => by
      have := hL w (hsub hw) x hxr
      rw [mem_closedBall, dist_eq_norm] at hw
      exact this.trans (mul_le_mul_of_nonneg_left hw hL0)) hxs hys
  have e : h y - h x = g y - g x - deriv g x * (y - x) := by simp only [h]; ring
  rw [e] at hmvt
  calc _ ≤ L * ‖y - x‖ * ‖y - x‖ := hmvt
    _ = L * ‖y - x‖ ^ 2 := by ring

/-- With `g = φ − id`, Steffensen's step is `z − g(z)²/(g(z + g(z)) − g(z))`. -/
theorem steffStep_eq (φ : 𝕜 → 𝕜) (z : 𝕜) :
    steffStep φ z = z - (φ z - z) ^ 2 /
      ((φ (z + (φ z - z)) - (z + (φ z - z))) - (φ z - z)) := by
  simp only [steffStep, add_sub_cancel]
  congr 2
  ring

/-- **DLMF §3.8(ii), 3.8.7**: Steffensen's method "converges locally and quadratically for both
`ℝ` and `ℂ`", at a fixed point `ζ` with `φ′(ζ) ≠ 1` and `φ′` Lipschitz near `ζ`
(the hypothesis `φ′(ζ) ≠ 1` is needed, `dlmf_3_8_7_erratum`). -/
theorem dlmf_3_8_7 {φ : 𝕜 → 𝕜} {ζ : 𝕜} {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hφ : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 φ z)
    (hL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r, ‖deriv φ w - deriv φ z‖ ≤ L * ‖w - z‖)
    (hfix : φ ζ = ζ) (h1 : deriv φ ζ ≠ 1) :
    ConvergesLocally (steffStep φ) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(steffStep φ)^[n + 1] z₀ - ζ‖ ≤ K * ‖(steffStep φ)^[n] z₀ - ζ‖ ^ 2) ∧
      ((∀ n, (steffStep φ)^[n] z₀ ≠ ζ) → IsQuadraticConv (fun n => (steffStep φ)^[n] z₀) ζ) := by
  set g : 𝕜 → 𝕜 := fun z => φ z - z
  have hgd : ∀ z ∈ ball ζ r, HasDerivAt g (deriv φ z - 1) z := fun z hz =>
    (hφ z hz).hasDerivAt.sub (hasDerivAt_id z)
  have hg : ∀ z ∈ ball ζ r, DifferentiableAt 𝕜 g z := fun z hz => (hgd z hz).differentiableAt
  have hgL : ∀ w ∈ ball ζ r, ∀ z ∈ ball ζ r, ‖deriv g w - deriv g z‖ ≤ L * ‖w - z‖ :=
    fun w hw z hz => by
      rw [(hgd w hw).deriv, (hgd z hz).deriv, sub_sub_sub_cancel_right]; exact hL w hw z hz
  have hg0 : g ζ = 0 := by simp [g, hfix]
  set D0 := deriv g ζ
  have hD0 : D0 = deriv φ ζ - 1 := (hgd ζ (mem_ball_self hr)).deriv
  set d := ‖D0‖
  have hd : 0 < d := norm_pos_iff.mpr (by rw [hD0]; exact sub_ne_zero.mpr h1)
  set M := 3 * d / 2
  set K := 4 * L * M * (1 + M) / d ^ 2
  have hK0 : 0 ≤ K := by positivity
  set δ := min (r / (3 * (1 + M))) (min (d / (4 * (L + 1))) (min (d / (4 * (L * M + 1)))
    (1 / (2 * (K + 1)))))
  have hM0 : 0 ≤ M := by positivity
  have hδ0 : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (by positivity)))
  have hδ1 : δ ≤ r / (3 * (1 + M)) := min_le_left _ _
  have hδ2 : δ ≤ d / (4 * (L + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ d / (4 * (L * M + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ4 : δ ≤ 1 / (2 * (K + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLδ : L * δ ≤ d / 4 := by
    calc L * δ ≤ L * (d / (4 * (L + 1))) := mul_le_mul_of_nonneg_left hδ2 hL0
      _ ≤ (L + 1) * (d / (4 * (L + 1))) := by gcongr; linarith
      _ = d / 4 := by field_simp
  have hLMδ : L * M * δ ≤ d / 4 := by
    calc L * M * δ ≤ L * M * (d / (4 * (L * M + 1))) :=
          mul_le_mul_of_nonneg_left hδ3 (by positivity)
      _ ≤ (L * M + 1) * (d / (4 * (L * M + 1))) := by gcongr; linarith
      _ = d / 4 := by field_simp
  have hKδ : K * δ ≤ 1 / 2 := by
    calc K * δ ≤ K * (1 / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hδ4 hK0
      _ ≤ (K + 1) * (1 / (2 * (K + 1))) := by gcongr; linarith
      _ = 1 / 2 := by field_simp
  have hδr : (1 + M) * δ ≤ r / 3 := by
    calc (1 + M) * δ ≤ (1 + M) * (r / (3 * (1 + M))) := mul_le_mul_of_nonneg_left hδ1 (by linarith)
      _ = r / 3 := by field_simp
  -- the pointwise estimate
  have key : ∀ z ∈ ball ζ δ, ‖steffStep φ z - ζ‖ ≤ K * ‖z - ζ‖ ^ 2 ∧
      ‖steffStep φ z - ζ‖ ≤ ‖z - ζ‖ / 2 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    set e := z - ζ
    have he3 : ‖e‖ < r / 3 := by nlinarith [norm_nonneg e]
    have hzr : z ∈ ball ζ r := by rw [mem_ball, dist_eq_norm]; linarith
    set D := deriv g z
    set G := g z
    have hDD : ‖D - D0‖ ≤ L * ‖e‖ := hgL z hzr ζ (mem_ball_self hr)
    have hLe : L * ‖e‖ ≤ d / 4 := le_trans (mul_le_mul_of_nonneg_left hz.le hL0) hLδ
    have hDlo : 3 * d / 4 ≤ ‖D‖ := by
      have := norm_sub_norm_le D0 (D0 - D)
      rw [sub_sub_cancel, norm_sub_rev] at this; linarith
    have hDhi : ‖D‖ ≤ 5 * d / 4 := by
      have := norm_le_insert' D D0
      have h' : ‖D‖ ≤ ‖D0‖ + ‖D - D0‖ := by
        calc ‖D‖ = ‖D0 + (D - D0)‖ := by abel_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    have hR1 : ‖G - D * e‖ ≤ L * ‖e‖ ^ 2 := by
      have := lip_taylor hL0 hg hgL (x := z) (y := ζ) he3 (by simp; positivity)
      rw [hg0] at this
      have e1 : (0 : 𝕜) - G - D * (ζ - z) = -(G - D * e) := by simp only [e]; ring
      rw [e1, norm_neg, norm_sub_rev ζ z] at this
      exact this
    have hGhi : ‖G‖ ≤ M * ‖e‖ := by
      have h' : ‖G‖ ≤ ‖D * e‖ + ‖G - D * e‖ := by
        calc ‖G‖ = ‖D * e + (G - D * e)‖ := by abel_nf
          _ ≤ _ := norm_add_le _ _
      rw [norm_mul] at h'
      have : L * ‖e‖ ^ 2 ≤ d / 4 * ‖e‖ := by nlinarith [norm_nonneg e]
      have : ‖D‖ * ‖e‖ ≤ 5 * d / 4 * ‖e‖ := mul_le_mul_of_nonneg_right hDhi (norm_nonneg e)
      simp only [M]; linarith
    have hGlo : d / 2 * ‖e‖ ≤ ‖G‖ := by
      have h' := norm_sub_norm_le (D * e) (D * e - G)
      rw [sub_sub_cancel, norm_sub_rev, norm_mul] at h'
      have : L * ‖e‖ ^ 2 ≤ d / 4 * ‖e‖ := by nlinarith [norm_nonneg e]
      have : 3 * d / 4 * ‖e‖ ≤ ‖D‖ * ‖e‖ := mul_le_mul_of_nonneg_right hDlo (norm_nonneg e)
      linarith
    set w := z + G
    have hw3 : ‖w - ζ‖ < r / 3 := by
      have h' : ‖w - ζ‖ ≤ ‖e‖ + ‖G‖ := by
        calc ‖w - ζ‖ = ‖e + G‖ := by simp only [w, e]; abel_nf
          _ ≤ _ := norm_add_le _ _
      have : (1 + M) * ‖e‖ < r / 3 := lt_of_lt_of_le
        (mul_lt_mul_of_pos_left hz (by linarith)) hδr
      nlinarith
    have hR2 : ‖g w - G - D * G‖ ≤ L * ‖G‖ ^ 2 := by
      have := lip_taylor hL0 hg hgL (x := z) (y := w) he3 hw3
      rwa [show w - z = G by simp only [w]; ring] at this
    have hS : steffStep φ z = z - G ^ 2 / (g w - G) := by
      rw [steffStep_eq]
    rcases eq_or_ne e 0 with he0 | he0
    · have hz' : z = ζ := sub_eq_zero.mp he0
      have hG0 : G = 0 := by simp only [G, hz', hg0]
      rw [hS, hG0, hz']
      simp [he0]
    have heP : 0 < ‖e‖ := norm_pos_iff.mpr he0
    have hGP : 0 < ‖G‖ := lt_of_lt_of_le (by positivity) hGlo
    set den := g w - G
    have hden : d / 2 * ‖G‖ ≤ ‖den‖ := by
      have h' := norm_sub_norm_le (D * G) (D * G - den)
      rw [sub_sub_cancel, norm_sub_rev, norm_mul] at h'
      have hR2' : ‖den - D * G‖ ≤ L * ‖G‖ ^ 2 := by simpa [den] using hR2
      have : L * ‖G‖ ^ 2 ≤ d / 4 * ‖G‖ := by
        have : L * ‖G‖ ≤ L * (M * ‖e‖) := mul_le_mul_of_nonneg_left hGhi hL0
        have : L * M * ‖e‖ ≤ d / 4 := le_trans (mul_le_mul_of_nonneg_left hz.le (by positivity))
          hLMδ
        nlinarith [norm_nonneg G]
      have : 3 * d / 4 * ‖G‖ ≤ ‖D‖ * ‖G‖ := mul_le_mul_of_nonneg_right hDlo (norm_nonneg G)
      linarith
    have hdenP : 0 < ‖den‖ := lt_of_lt_of_le (by positivity) hden
    have hden0 : den ≠ 0 := norm_pos_iff.mp hdenP
    have hnum : steffStep φ z - ζ = (-G * (G - D * e) + e * (den - D * G)) / den := by
      rw [hS, eq_div_iff hden0]
      simp only [e]
      field_simp
      ring
    have hnum' : ‖steffStep φ z - ζ‖ * ‖den‖ ≤ L * M * (1 + M) * ‖e‖ ^ 3 := by
      rw [hnum, norm_div, div_mul_cancel₀ _ hdenP.ne']
      have hR2' : ‖den - D * G‖ ≤ L * ‖G‖ ^ 2 := by simpa [den] using hR2
      calc ‖-G * (G - D * e) + e * (den - D * G)‖
          ≤ ‖G‖ * ‖G - D * e‖ + ‖e‖ * ‖den - D * G‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_neg]
        _ ≤ (M * ‖e‖) * (L * ‖e‖ ^ 2) + ‖e‖ * (L * (M * ‖e‖) ^ 2) := by
            gcongr
            exact hR2'.trans (by gcongr)
        _ = L * M * (1 + M) * ‖e‖ ^ 3 - L * M * ‖e‖ ^ 3 + L * M * ‖e‖ ^ 3 := by ring
        _ = L * M * (1 + M) * ‖e‖ ^ 3 := by ring
    have hquad : ‖steffStep φ z - ζ‖ ≤ K * ‖e‖ ^ 2 := by
      have hlow : d / 2 * (d / 2 * ‖e‖) ≤ ‖den‖ :=
        le_trans (mul_le_mul_of_nonneg_left hGlo (by positivity)) hden
      have : ‖steffStep φ z - ζ‖ * (d / 2 * (d / 2 * ‖e‖)) ≤ L * M * (1 + M) * ‖e‖ ^ 3 :=
        le_trans (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)) hnum'
      have hpos : 0 < d / 2 * (d / 2 * ‖e‖) := by positivity
      rw [← le_div_iff₀ hpos] at this
      refine this.trans (le_of_eq ?_)
      simp only [K]
      field_simp
      ring
    refine ⟨hquad, hquad.trans ?_⟩
    calc K * ‖e‖ ^ 2 = (K * ‖e‖) * ‖e‖ := by ring
      _ ≤ (K * δ) * ‖e‖ := by gcongr
      _ ≤ 1 / 2 * ‖e‖ := by gcongr
      _ = ‖e‖ / 2 := by ring
  have hmem : ∀ z₀ ∈ ball ζ δ, ∀ n, (steffStep φ)^[n] z₀ ∈ ball ζ δ := fun z₀ hz n => by
    induction n with
    | zero => exact hz
    | succ n ih =>
      rw [Function.iterate_succ_apply', mem_ball, dist_eq_norm]
      have := (key _ ih).2
      have h' : ‖(steffStep φ)^[n] z₀ - ζ‖ < δ := by rwa [mem_ball, dist_eq_norm] at ih
      linarith [norm_nonneg ((steffStep φ)^[n] z₀ - ζ)]
  refine ⟨(convergesLocally_of_contract hδ0 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    fun z hz => by have := (key z hz).2; linarith).1, δ, hδ0, K, hK0, fun z₀ hz => ?_⟩
  have hq : ∀ n, ‖(steffStep φ)^[n + 1] z₀ - ζ‖ ≤ K * ‖(steffStep φ)^[n] z₀ - ζ‖ ^ 2 :=
    fun n => by rw [Function.iterate_succ_apply']; exact (key _ (hmem z₀ hz n)).1
  refine ⟨hq, fun hne => ⟨K + 1, Eventually.of_forall fun n => ?_⟩⟩
  have hpos : 0 < ‖(steffStep φ)^[n] z₀ - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ‖(steffStep φ)^[n + 1] z₀ - ζ‖ ≤ K * ‖(steffStep φ)^[n] z₀ - ζ‖ ^ 2 := hq n
    _ < (K + 1) * ‖(steffStep φ)^[n] z₀ - ζ‖ ^ 2 := by gcongr; linarith

/-- `dlmf_3_8_7` for `φ` of class `C²` near `ζ` (real twice continuously differentiable or complex
analytic `φ`). -/
theorem dlmf_3_8_7_of_contDiffAt {φ : 𝕜 → 𝕜} {ζ : 𝕜} (hφ : ContDiffAt 𝕜 2 φ ζ) (hfix : φ ζ = ζ)
    (h1 : deriv φ ζ ≠ 1) :
    ConvergesLocally (steffStep φ) ζ ∧ ∃ δ > 0, ∃ K ≥ 0, ∀ z₀ ∈ ball ζ δ,
      (∀ n, ‖(steffStep φ)^[n + 1] z₀ - ζ‖ ≤ K * ‖(steffStep φ)^[n] z₀ - ζ‖ ^ 2) ∧
      ((∀ n, (steffStep φ)^[n] z₀ ≠ ζ) → IsQuadraticConv (fun n => (steffStep φ)^[n] z₀) ζ) := by
  have h2 : ContDiffAt 𝕜 1 (deriv φ) ζ :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : 𝕜)))
  obtain ⟨K, t, ht, hK⟩ := h2.exists_lipschitzOnWith
  have hev : ∀ᶠ z in 𝓝 ζ, DifferentiableAt 𝕜 φ z :=
    (hφ.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hev)
  refine dlmf_3_8_7 hr K.coe_nonneg (fun z hz => (hrt hz).2) (fun w hw z hz => ?_) hfix h1
  have := hK.dist_le_mul w (hrt hw).1 z (hrt hz).1
  rwa [dist_eq_norm, dist_eq_norm] at this

end Steffensen

/-- **DLMF §3.8(iii), imprecision in "It converges locally and quadratically"**: at a fixed point
with `φ′(ζ) = 1` the convergence is only linear. For `φ(z) = z + z²`, `ζ = 0`, the step is
`z(1 + z)/(2 + z)`, and from every `z₀ ∈ (0, 1]` the iteration converges to `0` with no order
`p > 1`. -/
theorem dlmf_3_8_7_erratum :
    let φ : ℝ → ℝ := fun z => z + z ^ 2
    φ 0 = 0 ∧ deriv φ 0 = 1 ∧ ∀ z₀ ∈ Ioc (0 : ℝ) 1,
      Tendsto (fun n => (steffStep φ)^[n] z₀) atTop (𝓝 0) ∧
      ∀ p > 1, p ∉ convIndices (fun n => (steffStep φ)^[n] z₀) 0 := by
  intro φ
  have hstep : ∀ z : ℝ, 0 < z → steffStep φ z = z * (1 + z) / (2 + z) := fun z hz => by
    have h1 : (2 : ℝ) + z ≠ 0 := by linarith
    have h2 : z ≠ 0 := hz.ne'
    simp only [steffStep, φ]
    have hden : z + z ^ 2 + (z + z ^ 2) ^ 2 - 2 * (z + z ^ 2) + z = z ^ 3 * (2 + z) := by ring
    rw [hden]
    field_simp
    ring
  have hd : deriv φ 0 = 1 := by
    have : HasDerivAt φ 1 0 :=
      ((hasDerivAt_id' (0 : ℝ)).add (hasDerivAt_pow 2 (0 : ℝ))).congr_deriv (by norm_num)
    exact this.deriv
  refine ⟨by simp [φ], hd, fun z₀ hz₀ => ?_⟩
  have hbd : ∀ n, 0 < (steffStep φ)^[n] z₀ ∧ (steffStep φ)^[n] z₀ ≤ (2 / 3) ^ n * z₀ ∧
      (steffStep φ)^[n] z₀ / 2 ≤ (steffStep φ)^[n + 1] z₀ := by
    intro n
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id, pow_zero, one_mul, zero_add, Function.iterate_one]
      refine ⟨hz₀.1, le_rfl, ?_⟩
      rw [hstep z₀ hz₀.1, le_div_iff₀ (by linarith [hz₀.1])]
      nlinarith [hz₀.1]
    | succ n ih =>
      obtain ⟨h1, h2, -⟩ := ih
      have hz1 : (steffStep φ)^[n] z₀ ≤ 1 := h2.trans (by
        calc (2 / 3 : ℝ) ^ n * z₀ ≤ 1 * 1 :=
              mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) hz₀.2 hz₀.1.le (by norm_num)
          _ = 1 := by norm_num)
      set y := (steffStep φ)^[n] z₀
      have hy : (steffStep φ)^[n + 1] z₀ = y * (1 + y) / (2 + y) := by
        rw [Function.iterate_succ_apply', hstep y h1]
      have hpos : 0 < y * (1 + y) / (2 + y) := by positivity
      have hle : y * (1 + y) / (2 + y) ≤ 2 / 3 * y := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      refine ⟨by rw [hy]; exact hpos, ?_, ?_⟩
      · rw [hy, pow_succ]; nlinarith
      · rw [Function.iterate_succ_apply' _ (n + 1), hy, hstep _ hpos, le_div_iff₀ (by positivity)]
        have : y * (1 + y) / (2 + y) ≤ 1 := by linarith
        nlinarith
  have hlim : Tendsto (fun n => (steffStep φ)^[n] z₀) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hbd n).1.le) (fun n => (hbd n).2.1) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num)).mul_const z₀
  refine ⟨hlim, fun p hp => not_mem_convIndices_of_ge (c := 1 / 2) (by norm_num)
    (Eventually.of_forall fun n => ?_) (fun n => (hbd n).1.ne') hlim hp⟩
  rw [sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hbd n).1,
    abs_of_pos (hbd (n + 1)).1]
  linarith [(hbd n).2.2]

end Azurite.DLMF
