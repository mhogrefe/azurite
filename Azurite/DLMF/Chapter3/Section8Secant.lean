/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section8Other
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# DLMF §3.8(iii): the secant method

* The mean value theorem for second divided differences, by Rolle's theorem twice (`rolle_three`,
  `slopeAt`, `dd2_mvt`). Hence the secant error
  `x₂ − ξ = (x₀ − ξ)(x₁ − ξ) f″(η)/(2f′(η′))` (`secant_error`).
* The iteration (`secantStep`, `secX`; it stops at an exact zero). Local convergence
  (`secant_local`, `secant_consts`). The order is exactly `φ = (1 + √5)/2` when `f″(ξ) ≠ 0`: with
  `Lₙ = log(|e_{n+2}|/|e_{n+1}|^φ)`, `L_{n+1} = log|cₙ| − Lₙ/φ` (`tendsto_of_contract_rec`), so
  `|e_{n+2}|/|e_{n+1}|^φ → |f″(ξ)/(2f′(ξ))|^{1/φ}` (`secant_order`, `dlmf_3_8_iii_secant`).
* Efficiency per function evaluation, `√2 < φ` (`secant_efficiency`). An `x₂` outside `[x₀, x₁]`
  (`secant_outside`).
-/

open Filter Topology Set Metric

namespace Azurite.DLMF

section Secant

variable {f f₁ f₂ : ℝ → ℝ} {ξ ρ : ℝ}

/-! ### Divided differences -/

/-- Rolle's theorem twice: a function with three zeros `u < v < w` whose second derivative
exists on `[u, w]` has a zero of the second derivative in `(u, w)`. -/
theorem rolle_three {q q₁ q₂ : ℝ → ℝ} {u v w : ℝ} (huv : u < v) (hvw : v < w)
    (hq : ∀ t ∈ Icc u w, HasDerivAt q (q₁ t) t) (hq₁ : ∀ t ∈ Icc u w, HasDerivAt q₁ (q₂ t) t)
    (h0 : q u = 0) (h1 : q v = 0) (h2 : q w = 0) : ∃ η ∈ Ioo u w, q₂ η = 0 := by
  obtain ⟨t₁, ht₁, hq₁t⟩ := exists_hasDerivAt_eq_zero huv
    (fun t ht => (hq t ⟨ht.1, ht.2.trans hvw.le⟩).continuousAt.continuousWithinAt)
    (h0.trans h1.symm) (fun t ht => hq t ⟨ht.1.le, (ht.2.trans hvw).le⟩)
  obtain ⟨t₂, ht₂, hq₂t⟩ := exists_hasDerivAt_eq_zero hvw
    (fun t ht => (hq t ⟨huv.le.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt)
    (h1.trans h2.symm) (fun t ht => hq t ⟨(huv.trans ht.1).le, ht.2.le⟩)
  have h12 : t₁ < t₂ := ht₁.2.trans ht₂.1
  obtain ⟨η, hη, hq₂η⟩ := exists_hasDerivAt_eq_zero h12
    (fun t ht => (hq₁ t ⟨(ht₁.1.trans_le ht.1).le,
      ht.2.trans ht₂.2.le⟩).continuousAt.continuousWithinAt)
    (hq₁t.trans hq₂t.symm)
    (fun t ht => hq₁ t ⟨(ht₁.1.trans ht.1).le, (ht.2.trans ht₂.2).le⟩)
  exact ⟨η, ⟨ht₁.1.trans hη.1, hη.2.trans ht₂.2⟩, hq₂η⟩

/-- The slope `f[t, ξ] = f(t)/(t − ξ)` (for `f(ξ) = 0`). -/
noncomputable def slopeAt (f : ℝ → ℝ) (ξ t : ℝ) : ℝ := f t / (t - ξ)

/-- **Mean value theorem for the second divided difference**: for distinct `x, y, ξ` within `m`
of `ξ` and `f(ξ) = 0`, `(f[y, ξ] − f[x, ξ])/(y − x) = f″(η)/2` for some `|η − ξ| ≤ m`. -/
theorem dd2_mvt (hf : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f₁ (f₂ t) t) (hξ : f ξ = 0) {x y : ℝ}
    (hx : |x - ξ| ≤ ρ) (hy : |y - ξ| ≤ ρ) (hxy : x ≠ y) (hxξ : x ≠ ξ) (hyξ : y ≠ ξ) :
    ∃ η, |η - ξ| ≤ max |x - ξ| |y - ξ| ∧
      (slopeAt f ξ y - slopeAt f ξ x) / (y - x) = f₂ η / 2 := by
  set m := max |x - ξ| |y - ξ|
  have hmρ : m ≤ ρ := max_le hx hy
  set K := (slopeAt f ξ y - slopeAt f ξ x) / (y - x)
  set q : ℝ → ℝ := fun t => f t - f x - slopeAt f ξ x * (t - x) - K * (t - x) * (t - ξ)
  have hxx : x - ξ ≠ 0 := sub_ne_zero.mpr hxξ
  have hyy : y - ξ ≠ 0 := sub_ne_zero.mpr hyξ
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have q0 : q x = 0 := by simp [q]
  have qξ : q ξ = 0 := by simp only [q, slopeAt, hξ]; field_simp; ring
  have qy : q y = 0 := by simp only [q, K, slopeAt]; field_simp; ring
  have hsub : Icc (ξ - m) (ξ + m) ⊆ Icc (ξ - ρ) (ξ + ρ) := Icc_subset_Icc (by linarith)
    (by linarith)
  have hq : ∀ t ∈ Icc (ξ - m) (ξ + m), HasDerivAt q
      (f₁ t - slopeAt f ξ x - K * ((t - ξ) + (t - x))) t := fun t ht => by
    have h1 := (((hf t (hsub ht)).sub_const (f x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul (slopeAt f ξ x))).sub
      ((((hasDerivAt_id t).sub_const x).const_mul K).mul ((hasDerivAt_id t).sub_const ξ))
    exact h1.congr_deriv (by simp; ring)
  have hq₁ : ∀ t ∈ Icc (ξ - m) (ξ + m), HasDerivAt
      (fun t => f₁ t - slopeAt f ξ x - K * ((t - ξ) + (t - x))) (f₂ t - 2 * K) t := fun t ht => by
    have h1 := ((hf₁ t (hsub ht)).sub_const (slopeAt f ξ x)).sub
      ((((hasDerivAt_id t).sub_const ξ).add ((hasDerivAt_id t).sub_const x)).const_mul K)
    exact h1.congr_deriv (by simp; ring)
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) (le_max_left _ _)
  have hxm : x ∈ Icc (ξ - m) (ξ + m) := by
    have hax : |x - ξ| ≤ m := le_max_left _ _
    rw [abs_le] at hax; exact ⟨by linarith, by linarith⟩
  have hym : y ∈ Icc (ξ - m) (ξ + m) := by
    have hay : |y - ξ| ≤ m := le_max_right _ _
    rw [abs_le] at hay; exact ⟨by linarith, by linarith⟩
  have hξm : ξ ∈ Icc (ξ - m) (ξ + m) := ⟨by linarith, by linarith⟩
  -- sort the three zeros
  have key : ∀ u v w : ℝ, u < v → v < w → u ∈ Icc (ξ - m) (ξ + m) → w ∈ Icc (ξ - m) (ξ + m) →
      q u = 0 → q v = 0 → q w = 0 → ∃ η, |η - ξ| ≤ m ∧ K = f₂ η / 2 := by
    intro u v w huv hvw hu hw h0 h1 h2
    have hsub' : Icc u w ⊆ Icc (ξ - m) (ξ + m) := Icc_subset_Icc hu.1 hw.2
    obtain ⟨η, hη, hη0⟩ := rolle_three huv hvw (fun t ht => hq t (hsub' ht))
      (fun t ht => hq₁ t (hsub' ht)) h0 h1 h2
    refine ⟨η, ?_, by linarith⟩
    rw [abs_le]; constructor <;> linarith [hη.1, hη.2, hu.1, hw.2]
  rcases lt_trichotomy x y with h1 | h1 | h1
  · rcases lt_trichotomy ξ x with h2 | h2 | h2
    · exact key ξ x y h2 h1 hξm hym qξ q0 qy
    · exact absurd h2.symm hxξ
    · rcases lt_trichotomy ξ y with h3 | h3 | h3
      · exact key x ξ y h2 h3 hxm hym q0 qξ qy
      · exact absurd h3.symm hyξ
      · exact key x y ξ h1 h3 hxm hξm q0 qy qξ
  · exact absurd h1 hxy
  · rcases lt_trichotomy ξ y with h2 | h2 | h2
    · exact key ξ y x h2 h1 hξm hxm qξ qy q0
    · exact absurd h2.symm hyξ
    · rcases lt_trichotomy ξ x with h3 | h3 | h3
      · exact key y ξ x h2 h3 hym hxm qy qξ q0
      · exact absurd h3.symm hxξ
      · exact key y x ξ h1 h3 hym hξm qy q0 qξ

/-- **The secant error**: `x₂ − ξ = (x₀ − ξ)(x₁ − ξ) · f″(η)/(2 f′(η′))` with `η, η′` within
`max(|x₀ − ξ|, |x₁ − ξ|)` of `ξ`. -/
theorem secant_error (hf : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f₁ (f₂ t) t) (hξ : f ξ = 0) {x y : ℝ}
    (hx : |x - ξ| ≤ ρ) (hy : |y - ξ| ≤ ρ) (hxy : x ≠ y) (hxξ : x ≠ ξ) (hyξ : y ≠ ξ)
    (hfxy : f y ≠ f x) :
    ∃ η η' : ℝ, |η - ξ| ≤ max |x - ξ| |y - ξ| ∧ |η' - ξ| ≤ max |x - ξ| |y - ξ| ∧
      rfPoint f x y - ξ = (x - ξ) * (y - ξ) * (f₂ η / 2) / f₁ η' := by
  obtain ⟨η, hη, hK⟩ := dd2_mvt hf hf₁ hξ hx hy hxy hxξ hyξ
  -- the mean value theorem for `f[x, y]`
  obtain ⟨η', hη', hfd⟩ : ∃ η', |η' - ξ| ≤ max |x - ξ| |y - ξ| ∧ f y - f x = f₁ η' * (y - x) := by
    have hI : ∀ t, min x y ≤ t → t ≤ max x y → t ∈ Icc (ξ - ρ) (ξ + ρ) := fun t h1 h2 => by
      rw [abs_le] at hx hy
      rcases le_total x y with h | h
      · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
        exact ⟨by linarith [hx.1], by linarith [hy.2]⟩
      · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
        exact ⟨by linarith [hy.1], by linarith [hx.2]⟩
    have hbd : ∀ t, min x y ≤ t → t ≤ max x y → |t - ξ| ≤ max |x - ξ| |y - ξ| := fun t h1 h2 => by
      rw [abs_le]
      rcases le_total x y with h | h
      · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
        constructor <;> nlinarith [le_abs_self (x - ξ), neg_abs_le (x - ξ), le_abs_self (y - ξ),
          neg_abs_le (y - ξ), le_max_left |x - ξ| |y - ξ|, le_max_right |x - ξ| |y - ξ|]
      · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
        constructor <;> nlinarith [le_abs_self (x - ξ), neg_abs_le (x - ξ), le_abs_self (y - ξ),
          neg_abs_le (y - ξ), le_max_left |x - ξ| |y - ξ|, le_max_right |x - ξ| |y - ξ|]
    rcases lt_or_gt_of_ne hxy with h | h
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f₁ h
        (fun t ht => (hf t (hI t (by rw [min_eq_left h.le]; exact ht.1)
          (by rw [max_eq_right h.le]; exact ht.2))).continuousAt.continuousWithinAt)
        (fun t ht => hf t (hI t (by rw [min_eq_left h.le]; exact ht.1.le)
          (by rw [max_eq_right h.le]; exact ht.2.le)))
      refine ⟨c, hbd c (by rw [min_eq_left h.le]; exact hc.1.le)
        (by rw [max_eq_right h.le]; exact hc.2.le), ?_⟩
      rw [hcd]; field_simp [sub_ne_zero.mpr h.ne']
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f₁ h
        (fun t ht => (hf t (hI t (by rw [min_eq_right h.le]; exact ht.1)
          (by rw [max_eq_left h.le]; exact ht.2))).continuousAt.continuousWithinAt)
        (fun t ht => hf t (hI t (by rw [min_eq_right h.le]; exact ht.1.le)
          (by rw [max_eq_left h.le]; exact ht.2.le)))
      refine ⟨c, hbd c (by rw [min_eq_right h.le]; exact hc.1.le)
        (by rw [max_eq_left h.le]; exact hc.2.le), ?_⟩
      rw [hcd]; field_simp [sub_ne_zero.mpr h.ne']; ring
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hf1 : f₁ η' ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hfd; exact hfxy (sub_eq_zero.mp hfd)
  refine ⟨η, η', hη, hη', ?_⟩
  rw [← hK]
  have hxx : x - ξ ≠ 0 := sub_ne_zero.mpr hxξ
  have hyy : y - ξ ≠ 0 := sub_ne_zero.mpr hyξ
  have hfd' : f y - f x ≠ 0 := sub_ne_zero.mpr hfxy
  have hf1' : f₁ η' = (f y - f x) / (y - x) := by rw [hfd]; field_simp
  rw [hf1']
  simp only [rfPoint, slopeAt]
  field_simp
  ring

/-! ### The iteration -/

/-- One secant step `(x_{n−1}, xₙ) ↦ (xₙ, x_{n+1})`, `x_{n+1}` by 3.8.6; the iteration stops at an
exact zero. -/
noncomputable def secantStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f p.2 = 0 then (p.2, p.2) else (p.2, rfPoint f p.1 p.2)

/-- The secant iterates `x₀, x₁, x₂, …`. -/
noncomputable def secX (f : ℝ → ℝ) (x₀ x₁ : ℝ) (n : ℕ) : ℝ := ((secantStep f)^[n] (x₀, x₁)).1

theorem secX_succ (f : ℝ → ℝ) (x₀ x₁ : ℝ) (n : ℕ) :
    secX f x₀ x₁ (n + 1) = ((secantStep f)^[n] (x₀, x₁)).2 := by
  simp only [secX]
  rw [Function.iterate_succ_apply']
  unfold secantStep
  split_ifs <;> rfl

/-- The local constants: on `[ξ − ρ₁, ξ + ρ₁]`, `|f′| ≥ |f′(ξ)|/2` and `|f″| ≤ B`. -/
theorem secant_consts (hρ : 0 < ρ)
    (hf₁ : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f₁ (f₂ t) t) (hc₂ : ContinuousAt f₂ ξ)
    (hd : f₁ ξ ≠ 0) :
    ∃ ρ₁ > 0, ρ₁ ≤ ρ ∧ ∀ t, |t - ξ| ≤ ρ₁ → |f₁ ξ| / 2 ≤ |f₁ t| ∧ |f₂ t| ≤ |f₂ ξ| + 1 := by
  have hξI : ξ ∈ Icc (ξ - ρ) (ξ + ρ) := ⟨by linarith, by linarith⟩
  have hc₁ : ContinuousAt f₁ ξ := (hf₁ ξ hξI).continuousAt
  obtain ⟨a, ha, h1⟩ := Metric.continuousAt_iff.mp hc₁ (|f₁ ξ| / 2) (by positivity)
  obtain ⟨b, hb, h2⟩ := Metric.continuousAt_iff.mp hc₂ 1 one_pos
  refine ⟨min ρ (min (a / 2) (b / 2)), lt_min hρ (lt_min (by linarith) (by linarith)),
    min_le_left _ _, fun t ht => ?_⟩
  have hta : dist t ξ < a := by
    rw [Real.dist_eq]; linarith [(min_le_right ρ _).trans (min_le_left (a / 2) (b / 2))]
  have htb : dist t ξ < b := by
    rw [Real.dist_eq]; linarith [(min_le_right ρ _).trans (min_le_right (a / 2) (b / 2))]
  have e1 := h1 hta
  have e2 := h2 htb
  rw [Real.dist_eq] at e1 e2
  constructor
  · have := abs_sub_abs_le_abs_sub (f₁ ξ) (f₁ t)
    rw [abs_sub_comm] at this; linarith
  · have := abs_sub_abs_le_abs_sub (f₂ t) (f₂ ξ); linarith

/-- **DLMF §3.8(iii), secant method: local convergence** at a simple zero (`f ∈ C²`): for
distinct starting values close to `ξ` the iterates converge to `ξ`, with
`|e_{n+2}| ≤ K |eₙ| |e_{n+1}|`. -/
theorem secant_local (hρ : 0 < ρ) (hf : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f₁ (f₂ t) t) (hc₂ : ContinuousAt f₂ ξ)
    (hξ : f ξ = 0) (hd : f₁ ξ ≠ 0) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ x₀ x₁, |x₀ - ξ| < δ → |x₁ - ξ| < δ → x₀ ≠ x₁ →
      Tendsto (secX f x₀ x₁) atTop (𝓝 ξ) ∧
      (∀ n, |secX f x₀ x₁ (n + 2) - ξ| ≤
        K * |secX f x₀ x₁ n - ξ| * |secX f x₀ x₁ (n + 1) - ξ|) ∧
      (∀ n, secX f x₀ x₁ (n + 1) ≠ ξ → secX f x₀ x₁ n ≠ secX f x₀ x₁ (n + 1)) ∧
      (∀ n, secX f x₀ x₁ (n + 1) ≠ ξ →
        secX f x₀ x₁ (n + 2) = rfPoint f (secX f x₀ x₁ n) (secX f x₀ x₁ (n + 1))) := by
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, hbd⟩ := secant_consts hρ hf₁ hc₂ hd
  set d := |f₁ ξ|
  have hd0 : 0 < d := abs_pos.mpr hd
  set K := (|f₂ ξ| + 1) / d
  have hK0 : 0 ≤ K := by positivity
  set δ := min ρ₁ (1 / (2 * (K + 1)))
  have hδ0 : 0 < δ := lt_min hρ₁ (by positivity)
  have hδ1 : δ ≤ ρ₁ := min_le_left _ _
  have hKδ : K * δ ≤ 1 / 2 := by
    calc K * δ ≤ K * (1 / (2 * (K + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK0
      _ ≤ (K + 1) * (1 / (2 * (K + 1))) := by gcongr; linarith
      _ = 1 / 2 := by field_simp
  have hI : ∀ t, |t - ξ| ≤ ρ₁ → t ∈ Icc (ξ - ρ) (ξ + ρ) := fun t ht => by
    rw [abs_le] at ht; exact ⟨by linarith, by linarith⟩
  -- `f` is injective near `ξ`
  have hinj : ∀ u v, |u - ξ| ≤ ρ₁ → |v - ξ| ≤ ρ₁ → u ≠ v → f u ≠ f v := by
    intro u v hu hv huv hfe
    have hseg : ∀ t, min u v ≤ t → t ≤ max u v → |t - ξ| ≤ ρ₁ := fun t h1 h2 => by
      rw [abs_le] at hu hv ⊢
      rcases le_total u v with h | h
      · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
        exact ⟨by linarith [hu.1], by linarith [hv.2]⟩
      · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
        exact ⟨by linarith [hv.1], by linarith [hu.2]⟩
    rcases lt_or_gt_of_ne huv with h | h
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f₁ h
        (fun t ht => (hf t (hI t (hseg t (by rw [min_eq_left h.le]; exact ht.1)
          (by rw [max_eq_right h.le]; exact ht.2)))).continuousAt.continuousWithinAt)
        (fun t ht => hf t (hI t (hseg t (by rw [min_eq_left h.le]; exact ht.1.le)
          (by rw [max_eq_right h.le]; exact ht.2.le))))
      rw [hfe, sub_self, zero_div] at hcd
      have := (hbd c (hseg c (by rw [min_eq_left h.le]; exact hc.1.le)
        (by rw [max_eq_right h.le]; exact hc.2.le))).1
      rw [hcd, abs_zero] at this; linarith
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f₁ h
        (fun t ht => (hf t (hI t (hseg t (by rw [min_eq_right h.le]; exact ht.1)
          (by rw [max_eq_left h.le]; exact ht.2)))).continuousAt.continuousWithinAt)
        (fun t ht => hf t (hI t (hseg t (by rw [min_eq_right h.le]; exact ht.1.le)
          (by rw [max_eq_left h.le]; exact ht.2.le))))
      rw [hfe, sub_self, zero_div] at hcd
      have := (hbd c (hseg c (by rw [min_eq_right h.le]; exact hc.1.le)
        (by rw [max_eq_left h.le]; exact hc.2.le))).1
      rw [hcd, abs_zero] at this; linarith
  -- one step
  have step : ∀ p : ℝ × ℝ, |p.1 - ξ| < δ → |p.2 - ξ| < δ → (p.2 = ξ ∨ p.1 ≠ p.2) →
      (secantStep f p).1 = p.2 ∧ |(secantStep f p).2 - ξ| ≤ K * |p.1 - ξ| * |p.2 - ξ| ∧
      ((secantStep f p).2 = ξ ∨ (secantStep f p).1 ≠ (secantStep f p).2) := by
    rintro ⟨x, y⟩ hx hy hxy
    simp only at hx hy hxy ⊢
    have hx1 : |x - ξ| ≤ ρ₁ := (hx.le.trans hδ1)
    have hy1 : |y - ξ| ≤ ρ₁ := (hy.le.trans hδ1)
    rcases eq_or_ne y ξ with rfl | hyξ
    · simp [secantStep, hξ]
    have hfy : f y ≠ 0 := fun h0 => hinj y ξ hy1 (by simp; exact hρ₁.le) hyξ (h0.trans hξ.symm)
    have hxy' : x ≠ y := hxy.resolve_left hyξ
    have hfxy : f y ≠ f x := fun h => hinj x y hx1 hy1 hxy' h.symm
    rw [show secantStep f (x, y) = (y, rfPoint f x y) by simp [secantStep, hfy]]
    refine ⟨rfl, ?_, ?_⟩
    · rcases eq_or_ne x ξ with rfl | hxξ
      · have : rfPoint f x y = x := by
          simp only [rfPoint, hξ, zero_mul, sub_zero]; field_simp
        rw [this, sub_self, abs_zero]; positivity
      obtain ⟨η, η', hη, hη', he⟩ := secant_error hf hf₁ hξ (hx1.trans hρ₁ρ) (hy1.trans hρ₁ρ)
        hxy' hxξ hyξ hfxy
      rw [he, abs_div, abs_mul, abs_mul, abs_div]
      have hm : max |x - ξ| |y - ξ| ≤ ρ₁ := max_le hx1 hy1
      have h1 := (hbd η' (hη'.trans hm)).1
      have h2 := (hbd η (hη.trans hm)).2
      have hpos : 0 < |f₁ η'| := lt_of_lt_of_le (by positivity) h1
      rw [div_le_iff₀ hpos]
      calc |x - ξ| * |y - ξ| * (|f₂ η| / |2|) ≤ |x - ξ| * |y - ξ| * ((|f₂ ξ| + 1) / 2) := by
            rw [abs_two]; gcongr
        _ = K * |x - ξ| * |y - ξ| * (d / 2) := by simp only [K]; field_simp
        _ ≤ K * |x - ξ| * |y - ξ| * |f₁ η'| := by gcongr
    · right
      intro h
      have : rfPoint f x y - y = -(f y * (y - x)) / (f y - f x) := by
        simp only [rfPoint]; field_simp [sub_ne_zero.mpr hfxy]; ring
      have h' : y = rfPoint f x y := h
      rw [← h', sub_self] at this
      have hfd : f y - f x ≠ 0 := sub_ne_zero.mpr hfxy
      have : f y * (y - x) = 0 := by
        rw [eq_comm, div_eq_zero_iff] at this
        rcases this with h' | h'
        · exact neg_eq_zero.mp h'
        · exact absurd h' hfd
      rcases mul_eq_zero.mp this with h' | h'
      · exact hfy h'
      · exact hxy' (sub_eq_zero.mp h').symm
  refine ⟨δ, hδ0, K, hK0, fun x₀ x₁ h0 h1 h01 => ?_⟩
  set S : ℕ → ℝ × ℝ := fun n => (secantStep f)^[n] (x₀, x₁)
  -- the invariant along the iteration
  have hinv : ∀ n, |(S n).1 - ξ| < δ ∧ |(S n).2 - ξ| < δ ∧
      |(S (n + 1)).2 - ξ| ≤ (1 / 2) ^ n * |(S 0).2 - ξ| ∧ ((S n).2 = ξ ∨ (S n).1 ≠ (S n).2) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨s1, s2, s3⟩ := step (x₀, x₁) h0 h1 (Or.inr h01)
      refine ⟨h0, h1, ?_, Or.inr h01⟩
      simp only [S, Function.iterate_zero, id, pow_zero, one_mul]
      refine s2.trans ?_
      calc K * |x₀ - ξ| * |x₁ - ξ| ≤ (K * δ) * |x₁ - ξ| := by gcongr
        _ ≤ 1 / 2 * |x₁ - ξ| := by gcongr
        _ ≤ |x₁ - ξ| := by linarith [abs_nonneg (x₁ - ξ)]
    | succ n ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih
      obtain ⟨s1, s2, s3⟩ := step (S n) i1 i2 i4
      have hSn : S (n + 1) = secantStep f (S n) := Function.iterate_succ_apply' _ _ _
      have i2' : |(S (n + 1)).2 - ξ| < δ := by
        rw [hSn]
        calc |(secantStep f (S n)).2 - ξ| ≤ K * |(S n).1 - ξ| * |(S n).2 - ξ| := s2
          _ ≤ (K * δ) * |(S n).2 - ξ| := by gcongr
          _ ≤ 1 / 2 * |(S n).2 - ξ| := by gcongr
          _ < δ := by linarith [abs_nonneg ((S n).2 - ξ)]
      have i1' : |(S (n + 1)).1 - ξ| < δ := by rw [hSn, s1]; exact i2
      obtain ⟨t1, t2, t3⟩ := step (S (n + 1)) i1' i2' (by rw [hSn]; exact s3)
      have hSn2 : S (n + 2) = secantStep f (S (n + 1)) := Function.iterate_succ_apply' _ _ _
      refine ⟨i1', i2', ?_, by rw [hSn]; exact s3⟩
      rw [hSn2]
      calc |(secantStep f (S (n + 1))).2 - ξ| ≤ K * |(S (n + 1)).1 - ξ| * |(S (n + 1)).2 - ξ| := t2
        _ ≤ (K * δ) * |(S (n + 1)).2 - ξ| := by gcongr
        _ ≤ 1 / 2 * ((1 / 2) ^ n * |(S 0).2 - ξ|) := by gcongr
        _ = (1 / 2) ^ (n + 1) * |(S 0).2 - ξ| := by ring
  have hX : ∀ n, secX f x₀ x₁ n = (S n).1 := fun n => rfl
  have hX1 : ∀ n, secX f x₀ x₁ (n + 1) = (S n).2 := fun n => secX_succ f x₀ x₁ n
  refine ⟨?_, fun n => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * |(S 0).2 - ξ|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul_const |(S 0).2 - ξ|
    rw [← tendsto_add_atTop_iff_nat 2]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [Real.norm_eq_abs, hX1]
    exact (hinv n).2.2.1
  · have hSn : S (n + 1) = secantStep f (S n) := Function.iterate_succ_apply' _ _ _
    rw [show n + 2 = (n + 1) + 1 by ring, hX1, hX1, hX, hSn]
    obtain ⟨s1, s2, -⟩ := step (S n) (hinv n).1 (hinv n).2.1 (hinv n).2.2.2
    exact s2
  · rw [hX1] at hn
    rw [hX, hX1]
    exact (hinv n).2.2.2.resolve_left hn
  · rw [hX1] at hn
    have hSn : S (n + 1) = secantStep f (S n) := Function.iterate_succ_apply' _ _ _
    have hfy : f (S n).2 ≠ 0 := fun h0 => hinj _ ξ ((hinv n).2.1.le.trans hδ1)
      (by simp; exact hρ₁.le) hn (h0.trans hξ.symm)
    rw [show n + 2 = (n + 1) + 1 by ring, hX1, hX1, hX, hSn]
    simp [secantStep, hfy]

/-! ### Order of convergence `(1 + √5)/2` -/

/-- A linear recurrence `L_{n+1} = a_{n+1} − κ Lₙ` with `0 ≤ κ < 1` and `aₙ → α` has
`Lₙ → α/(1 + κ)`. -/
theorem tendsto_of_contract_rec {L a : ℕ → ℝ} {α κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (ha : Tendsto a atTop (𝓝 α)) (hrec : ∀ n, L (n + 1) = a (n + 1) - κ * L n) :
    Tendsto L atTop (𝓝 (α / (1 + κ))) := by
  set M : ℕ → ℝ := fun n => L n - α / (1 + κ)
  have hM : ∀ n, M (n + 1) = (a (n + 1) - α) - κ * M n := fun n => by
    simp only [M, hrec]; field_simp; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp ha (ε * (1 - κ) / 2) (by nlinarith)
  have hbound : ∀ k, |M (N₀ + k)| ≤ ε / 2 + κ ^ k * |M N₀| := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      rw [← add_assoc, hM]
      have h1 := hN₀ (N₀ + k + 1) (by omega)
      rw [Real.dist_eq] at h1
      calc |(a (N₀ + k + 1) - α) - κ * M (N₀ + k)| ≤ |a (N₀ + k + 1) - α| + κ * |M (N₀ + k)| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hκ0]
        _ ≤ ε * (1 - κ) / 2 + κ * (ε / 2 + κ ^ k * |M N₀|) := by gcongr
        _ = ε / 2 + κ ^ (k + 1) * |M N₀| := by ring
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const
    |M N₀|).eventually (gt_mem_nhds (show (0 : ℝ) * |M N₀| < ε / 2 by simp; linarith)))
  refine ⟨N₀ + k₀, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N₀ + k := ⟨n - N₀, by omega⟩
  rw [dist_zero_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  show |M (N₀ + k)| < ε
  have := hk₀ k (by omega)
  linarith [hbound k]

open Real in
/-- **DLMF §3.8(iii), secant method: order `p = (1 + √5)/2`**. For iterates converging to a
simple zero `ξ` with `f″(ξ) ≠ 0` and never landing on `ξ`,
`|e_{n+2}|/|e_{n+1}|^φ → |f″(ξ)/(2f′(ξ))|^{1/φ}`. So 3.8.3 holds with `p = φ` and with no `p > φ`:
`φ` is the largest index. -/
theorem secant_order (hρ : 0 < ρ) (hf : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f₁ (f₂ t) t) (hc₂ : ContinuousAt f₂ ξ)
    (hξ : f ξ = 0) (hd : f₁ ξ ≠ 0) (h2 : f₂ ξ ≠ 0) {x : ℕ → ℝ}
    (hrec : ∀ n, x (n + 2) = rfPoint f (x n) (x (n + 1))) (hdist : ∀ n, x n ≠ x (n + 1))
    (hne : ∀ n, x n ≠ ξ) (hlim : Tendsto x atTop (𝓝 ξ)) :
    Tendsto (fun n => |x (n + 2) - ξ| / |x (n + 1) - ξ| ^ goldenRatio) atTop
      (𝓝 (|f₂ ξ / (2 * f₁ ξ)| ^ (1 / goldenRatio))) ∧
      goldenRatio ∈ convIndices x ξ ∧ ∀ p > goldenRatio, p ∉ convIndices x ξ := by
  set φ := goldenRatio
  set C := f₂ ξ / (2 * f₁ ξ)
  have hC : C ≠ 0 := div_ne_zero h2 (mul_ne_zero two_ne_zero hd)
  have hφ1 : 1 < φ := one_lt_goldenRatio
  have hφ0 : 0 < φ := goldenRatio_pos
  have hφsq : φ ^ 2 = φ + 1 := goldenRatio_sq
  have hinvφ : 1 / φ = φ - 1 := by field_simp; nlinarith
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, hbd⟩ := secant_consts hρ hf₁ hc₂ hd
  have he0 : Tendsto (fun n => |x n - ξ|) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
    simpa [Real.norm_eq_abs] using this
  have hepos : ∀ n, 0 < |x n - ξ| := fun n => abs_pos.mpr (sub_ne_zero.mpr (hne n))
  -- injectivity near `ξ`
  have hev : ∀ᶠ n in atTop, |x n - ξ| ≤ ρ₁ :=
    (he0.eventually (ge_mem_nhds hρ₁)).mono fun n hn => hn
  -- `c_n = e_{n+2}/(eₙ e_{n+1}) → C`
  set c : ℕ → ℝ := fun n => (x (n + 2) - ξ) / ((x n - ξ) * (x (n + 1) - ξ))
  have hc : Tendsto c atTop (𝓝 C) := by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => f₂ p.1 / 2 / f₁ p.2) (ξ, ξ) := by
      have hξI : ξ ∈ Icc (ξ - ρ) (ξ + ρ) := ⟨by linarith, by linarith⟩
      exact ((hc₂.comp continuousAt_fst).div_const 2).div
        ((hf₁ ξ hξI).continuousAt.comp continuousAt_snd) hd
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨γ, hγ, hγε⟩ := Metric.continuousAt_iff.mp hcont ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((hev.and ((he0.eventually (gt_mem_nhds (half_pos hγ))).and
      ((he0.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (half_pos hγ))))).and
      ((tendsto_add_atTop_nat 1).eventually hev))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨⟨h1, h3, h4⟩, h5⟩ := hN n hn
    simp only [Function.comp] at h4 h5
    -- the injectivity of `f` near `ξ` gives `f(x_{n+1}) ≠ f(xₙ)`
    have hfxy : f (x (n + 1)) ≠ f (x n) := by
      intro hfe
      have hseg : ∀ t, min (x n) (x (n + 1)) ≤ t → t ≤ max (x n) (x (n + 1)) → |t - ξ| ≤ ρ₁ :=
        fun t ht1 ht2 => by
          have a1 := abs_le.mp h1; have a2 := abs_le.mp h5
          rw [abs_le]
          rcases le_total (x n) (x (n + 1)) with h | h
          · rw [min_eq_left h] at ht1; rw [max_eq_right h] at ht2
            exact ⟨by linarith, by linarith⟩
          · rw [min_eq_right h] at ht1; rw [max_eq_left h] at ht2
            exact ⟨by linarith, by linarith⟩
      have hI : ∀ t, |t - ξ| ≤ ρ₁ → t ∈ Icc (ξ - ρ) (ξ + ρ) := fun t ht => by
        rw [abs_le] at ht; exact ⟨by linarith, by linarith⟩
      rcases lt_or_gt_of_ne (hdist n) with h | h
      · obtain ⟨c', hc', hcd⟩ := exists_hasDerivAt_eq_slope f f₁ h
          (fun t ht => (hf t (hI t (hseg t (by rw [min_eq_left h.le]; exact ht.1)
            (by rw [max_eq_right h.le]; exact ht.2)))).continuousAt.continuousWithinAt)
          (fun t ht => hf t (hI t (hseg t (by rw [min_eq_left h.le]; exact ht.1.le)
            (by rw [max_eq_right h.le]; exact ht.2.le))))
        rw [hfe, sub_self, zero_div] at hcd
        have := (hbd c' (hseg c' (by rw [min_eq_left h.le]; exact hc'.1.le)
          (by rw [max_eq_right h.le]; exact hc'.2.le))).1
        rw [hcd, abs_zero] at this; linarith [abs_pos.mpr hd]
      · obtain ⟨c', hc', hcd⟩ := exists_hasDerivAt_eq_slope f f₁ h
          (fun t ht => (hf t (hI t (hseg t (by rw [min_eq_right h.le]; exact ht.1)
            (by rw [max_eq_left h.le]; exact ht.2)))).continuousAt.continuousWithinAt)
          (fun t ht => hf t (hI t (hseg t (by rw [min_eq_right h.le]; exact ht.1.le)
            (by rw [max_eq_left h.le]; exact ht.2.le))))
        rw [hfe, sub_self, zero_div] at hcd
        have := (hbd c' (hseg c' (by rw [min_eq_right h.le]; exact hc'.1.le)
          (by rw [max_eq_left h.le]; exact hc'.2.le))).1
        rw [hcd, abs_zero] at this; linarith [abs_pos.mpr hd]
    obtain ⟨η, η', hη, hη', he⟩ := secant_error hf hf₁ hξ (h1.trans hρ₁ρ) (h5.trans hρ₁ρ)
      (hdist n) (hne n) (hne (n + 1)) hfxy
    have hcn : c n = f₂ η / 2 / f₁ η' := by
      simp only [c]
      rw [hrec, he]
      have := mul_ne_zero (sub_ne_zero.mpr (hne n)) (sub_ne_zero.mpr (hne (n + 1)))
      rw [div_eq_iff this]
      ring
    rw [hcn]
    have hm : max |x n - ξ| |x (n + 1) - ξ| < γ / 2 := max_lt h3 h4
    have := hγε (x := (η, η')) (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (by linarith) (by linarith))
    simpa [C, Real.dist_eq, div_div] using this
  -- logarithms
  set ℓ : ℕ → ℝ := fun n => Real.log |x n - ξ|
  have hcne : ∀ n, c n ≠ 0 := fun n => by
    simp only [c]
    exact div_ne_zero (sub_ne_zero.mpr (hne (n + 2)))
      (mul_ne_zero (sub_ne_zero.mpr (hne n)) (sub_ne_zero.mpr (hne (n + 1))))
  have hℓ : ∀ n, ℓ (n + 2) = Real.log |c n| + ℓ n + ℓ (n + 1) := fun n => by
    have : |x (n + 2) - ξ| = |c n| * |x n - ξ| * |x (n + 1) - ξ| := by
      simp only [c]
      rw [abs_div, abs_mul]
      field_simp [(hepos n).ne', (hepos (n + 1)).ne']
    simp only [ℓ]
    rw [this, Real.log_mul (mul_ne_zero (abs_pos.mpr (hcne n)).ne' (hepos n).ne')
      (hepos (n + 1)).ne', Real.log_mul (abs_pos.mpr (hcne n)).ne' (hepos n).ne']
  set Lg : ℕ → ℝ := fun n => ℓ (n + 2) - φ * ℓ (n + 1)
  have hLrec : ∀ n, Lg (n + 1) = Real.log |c (n + 1)| - (1 / φ) * Lg n := fun n => by
    simp only [Lg]
    rw [show n + 1 + 2 = (n + 1) + 2 by ring, hℓ (n + 1), hinvφ]
    rw [show n + 1 + 1 = n + 2 by ring]
    linear_combination (-ℓ (n + 1)) * hφsq
  have hlogc : Tendsto (fun n => Real.log |c n|) atTop (𝓝 (Real.log |C|)) :=
    (Real.continuousAt_log (abs_pos.mpr hC).ne').tendsto.comp hc.abs
  have hLlim : Tendsto Lg atTop (𝓝 (Real.log |C| / φ)) := by
    have := tendsto_of_contract_rec (L := Lg) (a := fun n => Real.log |c n|)
      (κ := 1 / φ) (by positivity) (by rw [div_lt_one hφ0]; exact hφ1) hlogc hLrec
    have e : 1 + 1 / φ = φ := by rw [hinvφ]; ring
    rwa [e] at this
  -- the ratio
  have hratio : ∀ n, |x (n + 2) - ξ| / |x (n + 1) - ξ| ^ φ = Real.exp (Lg n) := fun n => by
    simp only [Lg, ℓ]
    rw [Real.rpow_def_of_pos (hepos (n + 1)), Real.exp_sub, Real.exp_log (hepos (n + 2)),
      mul_comm (Real.log _) φ]
  set R := |C| ^ (1 / φ)
  have hR : R = Real.exp (Real.log |C| / φ) := by
    simp only [R]
    rw [Real.rpow_def_of_pos (abs_pos.mpr hC)]; ring_nf
  have hRpos : 0 < R := by rw [hR]; exact Real.exp_pos _
  have hlimR : Tendsto (fun n => |x (n + 2) - ξ| / |x (n + 1) - ξ| ^ φ) atTop (𝓝 R) := by
    rw [hR]
    exact (Real.continuous_exp.tendsto _).comp hLlim |>.congr fun n => (hratio n).symm
  refine ⟨hlimR, ⟨R + 1, ?_⟩, fun p hp => ?_⟩
  · -- `φ` is an index
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlimR.eventually (gt_mem_nhds (lt_add_one R)))
    refine eventually_atTop.mpr ⟨N + 1, fun m hm => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have := hN n (by omega)
    rw [div_lt_iff₀ (Real.rpow_pos_of_pos (hepos (n + 1)) _)] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact this
  · -- no `p > φ`
    rintro ⟨A₀, hA₀⟩
    have ht : Tendsto (fun n => |x (n + 1) - ξ| ^ (p - φ)) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (p - φ) (Or.inr (by linarith))).tendsto.comp
        (he0.comp (tendsto_add_atTop_nat 1))
      simpa [Function.comp_def, Real.zero_rpow (by linarith : p - φ ≠ 0)] using this
    obtain ⟨n, h1, h2, h3⟩ := ((((tendsto_add_atTop_nat 1).eventually hA₀)).and
      ((hlimR.eventually (lt_mem_nhds (half_lt_self hRpos))).and
      (ht.eventually (gt_mem_nhds (show 0 < R / 2 / (|A₀| + 1) by positivity))))).exists
    simp only [Real.norm_eq_abs] at h1
    have hp1 := hepos (n + 1)
    rw [lt_div_iff₀ (Real.rpow_pos_of_pos hp1 _)] at h2
    have hsplit : |x (n + 1) - ξ| ^ p = |x (n + 1) - ξ| ^ (p - φ) * |x (n + 1) - ξ| ^ φ := by
      rw [← Real.rpow_add hp1, sub_add_cancel]
    have hφpos : 0 < |x (n + 1) - ξ| ^ φ := Real.rpow_pos_of_pos hp1 _
    have h4 : R / 2 * |x (n + 1) - ξ| ^ φ < A₀ * (|x (n + 1) - ξ| ^ (p - φ) *
        |x (n + 1) - ξ| ^ φ) := by
      rw [← hsplit]; exact lt_trans h2 h1
    have h5 : A₀ * |x (n + 1) - ξ| ^ (p - φ) ≤ |A₀| * (R / 2 / (|A₀| + 1)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp1.le _)).trans
        (mul_le_mul_of_nonneg_left h3.le (abs_nonneg _))
    have h6 : |A₀| * (R / 2 / (|A₀| + 1)) < R / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg A₀]
    nlinarith

/-- **DLMF §3.8(iii), secant method**: "If the wanted zero `ξ` is simple, then the method
converges locally with order of convergence `p = (1 + √5)/2`" — for `f ∈ C²` near `ξ`. The
order is exactly `φ` (the largest index of 3.8.3) when `f″(ξ) ≠ 0` and no iterate lands on
`ξ`. -/
theorem dlmf_3_8_iii_secant (hρ : 0 < ρ) (hf : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f (f₁ t) t)
    (hf₁ : ∀ t ∈ Icc (ξ - ρ) (ξ + ρ), HasDerivAt f₁ (f₂ t) t) (hc₂ : ContinuousAt f₂ ξ)
    (hξ : f ξ = 0) (hd : f₁ ξ ≠ 0) :
    ∃ δ > 0, ∀ x₀ x₁, |x₀ - ξ| < δ → |x₁ - ξ| < δ → x₀ ≠ x₁ →
      Tendsto (secX f x₀ x₁) atTop (𝓝 ξ) ∧
      (f₂ ξ ≠ 0 → (∀ n, secX f x₀ x₁ n ≠ ξ) →
        Real.goldenRatio ∈ convIndices (secX f x₀ x₁) ξ ∧
        ∀ p > Real.goldenRatio, p ∉ convIndices (secX f x₀ x₁) ξ) := by
  obtain ⟨δ, hδ, K, -, hloc⟩ := secant_local hρ hf hf₁ hc₂ hξ hd
  refine ⟨δ, hδ, fun x₀ x₁ h0 h1 h01 => ?_⟩
  obtain ⟨hlim, -, hdist, hrec⟩ := hloc x₀ x₁ h0 h1 h01
  refine ⟨hlim, fun h2 hne => ?_⟩
  obtain ⟨-, hφ, hp⟩ := secant_order hρ hf hf₁ hc₂ hξ hd h2 (x := secX f x₀ x₁)
    (fun n => hrec n (hne (n + 1))) (fun n => hdist n (hne (n + 1))) hne hlim
  exact ⟨hφ, hp⟩

/-- "Because the method requires only one function evaluation per iteration, its numerical
efficiency is ultimately higher than that of Newton's method": per function evaluation the
secant method has order `φ`, Newton's method (two evaluations, order 2) `√2`, and `√2 < φ`. -/
theorem secant_efficiency : Real.sqrt 2 < Real.goldenRatio := by
  have h5 : (2.23 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 2 < 1.42 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold Real.goldenRatio
  linarith

/-- "There is no guaranteed convergence: the first approximation `x₂` may be outside
`[x₀, x₁]`": for `f(x) = x`, `x₀ = 1`, `x₁ = 2`, 3.8.6 gives `x₂ = 0`. -/
theorem secant_outside : rfPoint (fun x : ℝ => x) 1 2 = 0 ∧ (0 : ℝ) ∉ Icc 1 2 := by
  refine ⟨by norm_num [rfPoint], fun h => by norm_num at h⟩

end Secant

end Azurite.DLMF
