/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section37Log

/-!
# DLMF §4.37(v) Fundamental Property (inverse hyperbolic functions)

"With `k ∈ ℤ`, the general solutions of the equations `z = sinh w`, `z = cosh w`, `z = tanh w`
are respectively given by" 4.37.29–4.37.31.

* 4.37.26–4.37.31: `dlmf_4_37_29`, `dlmf_4_37_30`, `dlmf_4_37_31`. They rest on three general
  lemmas, `sinh_eq_iff_neg_one_zpow`, `cosh_eq_iff_pm` and `tanh_eq_iff_add_int_mul_pi_I` (if
  `sinh a = z`, respectively `cosh a = z`, `tanh a = z`, then the solutions of `z = sinh w` are
  `(−1)ᵏ a + kπi`, respectively `±a + 2kπi`, `a + kπi`), obtained from their §4.23(v)
  counterparts at `iw` (4.28.8–4.28.10).
* Off the cuts the principal values are used (`arcsinh` also at `±i`, `arccosh` also at `1`).
  On the cuts, where the principal value is two-valued, either side value of §4.37(iv) works
  (`dlmf_4_37_29_cut`, `dlmf_4_37_30_cut`, `dlmf_4_37_31_cut`, via `eq_of_side_limit` and
  `tanh_side_value`); this covers every `z ≠ ±1` in 4.37.31.
* `w = Arcsinh z`, `Arccosh z`, `Arctanh z`: the general values of §4.37(i) are these sets
  (`dlmf_4_37_29_gen`, `dlmf_4_37_30_gen`, `dlmf_4_37_31_gen`).
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-! ### General lemmas -/

theorem neg_one_zpow_neg_eq (k : ℤ) : (-1 : ℂ) ^ (-k) = (-1) ^ k := by
  rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]

/-- The solutions of `sinh w = sinh a` are `w = (−1)ᵏ a + kπi`. -/
theorem sinh_eq_iff_neg_one_zpow {a z : ℂ} (ha : sinh a = z) (w : ℂ) :
    sinh w = z ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k * a + k * π * I := by
  have key : sinh w = z ↔ sin (I * w) = I * z := by
    rw [dlmf_4_28_8]; exact ⟨fun h => by rw [h], fun h => mul_left_cancel₀ I_ne_zero h⟩
  rw [key, sin_eq_iff_neg_one_zpow (a := I * a) (by rw [dlmf_4_28_8, ha]) (I * w)]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [neg_one_zpow_neg_eq]; push_cast
    linear_combination (-I) * hk + (w - (-1 : ℂ) ^ k * a) * I_sq
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [neg_one_zpow_neg_eq]; push_cast
    linear_combination I * hk + ((k : ℂ) * π) * I_sq

/-- The solutions of `cosh w = cosh a` are `w = ±a + 2kπi`. -/
theorem cosh_eq_iff_pm {a z : ℂ} (ha : cosh a = z) (w : ℂ) :
    cosh w = z ↔ ∃ k : ℤ, w = a + 2 * k * π * I ∨ w = -a + 2 * k * π * I := by
  rw [← dlmf_4_28_9, cos_eq_iff_pm (a := I * a) (by rw [dlmf_4_28_9, ha]) (I * w)]
  constructor
  · rintro ⟨k, hk | hk⟩
    · refine ⟨-k, Or.inl ?_⟩; push_cast
      linear_combination (-I) * hk + (w - a) * I_sq
    · refine ⟨-k, Or.inr ?_⟩; push_cast
      linear_combination (-I) * hk + (w + a) * I_sq
  · rintro ⟨k, hk | hk⟩
    · refine ⟨-k, Or.inl ?_⟩; push_cast
      linear_combination I * hk + (2 * (k : ℂ) * π) * I_sq
    · refine ⟨-k, Or.inr ?_⟩; push_cast
      linear_combination I * hk + (2 * (k : ℂ) * π) * I_sq

/-- The solutions of `tanh w = tanh a` (`cosh a ≠ 0`, `w` not a pole) are `w = a + kπi`. -/
theorem tanh_eq_iff_add_int_mul_pi_I {a z : ℂ} (hc : cosh a ≠ 0) (ha : tanh a = z) (w : ℂ) :
    (cosh w ≠ 0 ∧ tanh w = z) ↔ ∃ k : ℤ, w = a + k * π * I := by
  have key : (cosh w ≠ 0 ∧ tanh w = z) ↔ (cos (I * w) ≠ 0 ∧ tan (I * w) = I * z) := by
    rw [dlmf_4_28_9, dlmf_4_28_10]
    exact and_congr_right fun _ => ⟨fun h => by rw [h], fun h => mul_left_cancel₀ I_ne_zero h⟩
  rw [key, tan_eq_iff_add_int_mul_pi (a := I * a) (by rwa [dlmf_4_28_9])
    (by rw [dlmf_4_28_10, ha]) (I * w)]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩; push_cast
    linear_combination (-I) * hk + (w - a) * I_sq
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩; push_cast
    linear_combination I * hk + ((k : ℂ) * π) * I_sq

/-- A one-sided limit `v` of a right inverse `F` of a continuous `G` satisfies `G v = x`. -/
theorem eq_of_side_limit {F G : ℂ → ℂ} {S : Set ℂ} {x v : ℂ} (hne : (𝓝[S] x).NeBot)
    (hF : Tendsto F (𝓝[S] x) (𝓝 v)) (hG : Continuous G) (hGF : ∀ z ∈ S, G (F z) = z) :
    G v = x :=
  apply_eq_of_tendsto nhdsWithin_le_nhds hF hG.continuousAt (eventually_nhdsWithin_of_forall hGF)

/-! ### Principal values -/

theorem sinh_arcsinhD_of {z : ℂ} (hz : z ∈ arcsinhCut ∨ z = I ∨ z = -I) :
    sinh (arcsinhD z) = z := by
  rcases hz with hz | rfl | rfl
  · exact sinh_arcsinhD hz
  · rw [(dlmf_4_37_17 (y := 0)).2, sinh_mul_I, sin_pi_div_two, one_mul]
  · rw [(dlmf_4_37_18 (y := 0)).2, sinh_neg, sinh_mul_I, sin_pi_div_two, one_mul]

theorem cosh_arccoshD_of {z : ℂ} (hz : z ∈ arccoshCut ∨ z = 1) : cosh (arccoshD z) = z := by
  rcases hz with hz | rfl
  · exact cosh_arccoshD hz
  · rw [arccoshD_one, cosh_zero]

theorem cosh_arctanhD_ne_zero {z : ℂ} (hz : z ∈ arctanhCut) : cosh (arctanhD z) ≠ 0 := by
  have h1 : I * z ≠ I := fun h => by
    have : z = 1 := mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm)
    rw [this] at hz; simp [arctanhCut] at hz
  have h2 : I * z ≠ -I := fun h => by
    have : z = -1 := mul_left_cancel₀ I_ne_zero (h.trans (by ring))
    rw [this] at hz; simp [arctanhCut] at hz
  rw [arctanhD_eq, arctanD_eq (I_mul_mem_arctanCut.mpr hz), neg_mul, cosh_neg, mul_comm,
    cosh_mul_I]
  exact cos_arctan_ne_zero _ h1 h2

/-- **DLMF 4.37.26, 4.37.29**: the general solution of `z = sinh w` is
`w = (−1)ᵏ arcsinh z + kπi`, `k ∈ ℤ` (`z` off the cuts, or `z = ±i`). -/
theorem dlmf_4_37_29 {z : ℂ} (hz : z ∈ arcsinhCut ∨ z = I ∨ z = -I) (w : ℂ) :
    sinh w = z ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k * arcsinhD z + k * π * I :=
  sinh_eq_iff_neg_one_zpow (sinh_arcsinhD_of hz) w

/-- **DLMF 4.37.27, 4.37.30**: the general solution of `z = cosh w` is
`w = ±arccosh z + 2kπi` (`z` off the cut, or `z = 1`). -/
theorem dlmf_4_37_30 {z : ℂ} (hz : z ∈ arccoshCut ∨ z = 1) (w : ℂ) :
    cosh w = z ↔ ∃ k : ℤ, w = arccoshD z + 2 * k * π * I ∨ w = -arccoshD z + 2 * k * π * I :=
  cosh_eq_iff_pm (cosh_arccoshD_of hz) w

/-- **DLMF 4.37.28, 4.37.31**: the general solution of `z = tanh w` is `w = arctanh z + kπi`
(`z` off the cuts; `w` not a pole of `tanh`). -/
theorem dlmf_4_37_31 {z : ℂ} (hz : z ∈ arctanhCut) (w : ℂ) :
    (cosh w ≠ 0 ∧ tanh w = z) ↔ ∃ k : ℤ, w = arctanhD z + k * π * I :=
  tanh_eq_iff_add_int_mul_pi_I (cosh_arctanhD_ne_zero hz) (tanh_arctanhD hz) w

/-- **DLMF 4.37.29** as sets: `Arcsinh z = {(−1)ᵏ arcsinh z + kπi}` (4.37.1 general values). -/
theorem dlmf_4_37_29_gen {z : ℂ} (hz : z ∈ arcsinhCut) :
    arcsinhGen z = {w | ∃ k : ℤ, w = (-1 : ℂ) ^ k * arcsinhD z + k * π * I} := by
  obtain ⟨h1, h2⟩ := arcsinhCut_ne hz
  ext w
  rw [mem_arcsinhGen_iff h1 h2, dlmf_4_37_29 (Or.inl hz)]
  rfl

/-- **DLMF 4.37.30** as sets: `Arccosh z = {±arccosh z + 2kπi}` (4.37.2 general values). -/
theorem dlmf_4_37_30_gen {z : ℂ} (hz : z ∈ arccoshCut) :
    arccoshGen z = {w | ∃ k : ℤ, w = arccoshD z + 2 * k * π * I ∨
      w = -arccoshD z + 2 * k * π * I} := by
  have h1 : z ≠ 1 := fun h => by rw [h] at hz; rcases hz with h | h <;> simp at h
  have h2 : z ≠ -1 := fun h => by rw [h] at hz; rcases hz with h | h <;> norm_num at h
  ext w
  rw [mem_arccoshGen_iff h1 h2, dlmf_4_37_30 (Or.inl hz)]
  rfl

/-- **DLMF 4.37.31** as sets: `Arctanh z = {arctanh z + kπi}` (4.37.3 general values). -/
theorem dlmf_4_37_31_gen {z : ℂ} (hz : z ∈ arctanhCut) :
    arctanhGen z = {w | ∃ k : ℤ, w = arctanhD z + k * π * I} := by
  ext w
  rw [mem_arctanhGen_iff, dlmf_4_37_31 hz]
  rfl

/-! ### On the cuts -/

/-- A one-sided limit `v` of `arctanh` at `x` (approached within the cut plane) satisfies
`cosh v ≠ 0` and `tanh v = x`. -/
theorem tanh_side_value {S : Set ℂ} {x v : ℂ} (hne : (𝓝[S] x).NeBot)
    (hF : Tendsto arctanhD (𝓝[S] x) (𝓝 v)) (hS : ∀ z ∈ S, z ∈ arctanhCut) :
    cosh v ≠ 0 ∧ tanh v = x := by
  have h1 : Tendsto (fun z => sinh (arctanhD z) - z * cosh (arctanhD z)) (𝓝[S] x)
      (𝓝 (sinh v - x * cosh v)) :=
    ((continuous_sinh.tendsto v).comp hF).sub
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul ((continuous_cosh.tendsto v).comp hF))
  have h0 : sinh v - x * cosh v = 0 := by
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hc := cosh_arctanhD_ne_zero (hS z hz)
    have ht := tanh_arctanhD (hS z hz)
    rw [tanh_eq_sinh_div_cosh, div_eq_iff hc] at ht
    linear_combination -ht
  have hc : cosh v ≠ 0 := fun h => by
    have := cosh_sq_sub_sinh_sq v
    have hs : sinh v = 0 := by linear_combination h0 + x * h
    rw [h, hs] at this; norm_num at this
  exact ⟨hc, by rw [tanh_eq_sinh_div_cosh, div_eq_iff hc]; linear_combination h0⟩


theorem neBot_re_pos (y : ℝ) : (𝓝[{z : ℂ | 0 < z.re}] ((y : ℂ) * I)).NeBot :=
  neBot_nhdsWithin_of_ray _ 1 fun t ht => by simpa using ht

theorem neBot_re_neg (y : ℝ) : (𝓝[{z : ℂ | z.re < 0}] ((y : ℂ) * I)).NeBot :=
  neBot_nhdsWithin_of_ray _ (-1) fun t ht => by simpa using ht

/-- On the cuts of `arcsinh` (`iy`, `|y| > 1`) both side values of 4.37.17–4.37.18 satisfy
`sinh = iy`, so 4.37.29 holds with either of them. -/
theorem dlmf_4_37_29_cut {y : ℝ} (w : ℂ) :
    (1 < y → (sinh w = y * I ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (π / 2 * I + (Real.log (√(y ^ 2 - 1) + y) : ℂ)) + k * π * I) ∧
      (sinh w = y * I ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (π / 2 * I - (Real.log (√(y ^ 2 - 1) + y) : ℂ)) + k * π * I)) ∧
    (y < -1 → (sinh w = y * I ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (-(π / 2 * I) + (Real.log (√(y ^ 2 - 1) - y) : ℂ)) + k * π * I) ∧
      (sinh w = y * I ↔ ∃ k : ℤ, w = (-1 : ℂ) ^ k *
        (-(π / 2 * I) - (Real.log (√(y ^ 2 - 1) - y) : ℂ)) + k * π * I)) := by
  have hR : ∀ z ∈ {z : ℂ | 0 < z.re}, sinh (arcsinhD z) = z := fun z hz =>
    sinh_arcsinhD (Or.inl (ne_of_gt hz))
  have hL : ∀ z ∈ {z : ℂ | z.re < 0}, sinh (arcsinhD z) = z := fun z hz =>
    sinh_arcsinhD (Or.inl (ne_of_lt hz))
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨e1, e2⟩ := (dlmf_4_37_17 (y := y)).1 hy
    exact ⟨sinh_eq_iff_neg_one_zpow (eq_of_side_limit (neBot_re_pos y) e1 continuous_sinh hR) w,
      sinh_eq_iff_neg_one_zpow (eq_of_side_limit (neBot_re_neg y) e2 continuous_sinh hL) w⟩
  · obtain ⟨e1, e2⟩ := (dlmf_4_37_18 (y := y)).1 hy
    exact ⟨sinh_eq_iff_neg_one_zpow (eq_of_side_limit (neBot_re_pos y) e1 continuous_sinh hR) w,
      sinh_eq_iff_neg_one_zpow (eq_of_side_limit (neBot_re_neg y) e2 continuous_sinh hL) w⟩

/-- On the cut of `arccosh` (`x ≤ 1`) both side values of 4.37.22–4.37.23 satisfy `cosh = x`,
so 4.37.30 holds with either of them. -/
theorem dlmf_4_37_30_cut {x : ℝ} (w : ℂ) :
    (x ∈ Ioc (-1 : ℝ) 1 →
      (cosh w = x ↔ ∃ k : ℤ, w = log (I * ((√(1 - x ^ 2) : ℝ) : ℂ) + x) + 2 * k * π * I ∨
        w = -log (I * ((√(1 - x ^ 2) : ℝ) : ℂ) + x) + 2 * k * π * I) ∧
      (cosh w = x ↔ ∃ k : ℤ, w = -log (I * ((√(1 - x ^ 2) : ℝ) : ℂ) + x) + 2 * k * π * I ∨
        w = - -log (I * ((√(1 - x ^ 2) : ℝ) : ℂ) + x) + 2 * k * π * I)) ∧
    (x ≤ -1 →
      (cosh w = x ↔ ∃ k : ℤ,
        w = (π * I + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ)) + 2 * k * π * I ∨
        w = -(π * I + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ)) + 2 * k * π * I) ∧
      (cosh w = x ↔ ∃ k : ℤ,
        w = (-(π * I) + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ)) + 2 * k * π * I ∨
        w = -(-(π * I) + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ)) + 2 * k * π * I)) := by
  have hU : ∀ z ∈ {w : ℂ | 0 < w.im}, cosh (arccoshD z) = z := fun z hz =>
    cosh_arccoshD (Or.inl (ne_of_gt hz))
  have hD : ∀ z ∈ {w : ℂ | w.im < 0}, cosh (arccoshD z) = z := fun z hz =>
    cosh_arccoshD (Or.inl (ne_of_lt hz))
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨e1, e2⟩ := dlmf_4_37_22 hx
    exact ⟨cosh_eq_iff_pm (eq_of_side_limit (neBot_upper x) e1 continuous_cosh hU) w,
      cosh_eq_iff_pm (eq_of_side_limit (neBot_lower x) e2 continuous_cosh hD) w⟩
  · obtain ⟨e1, e2⟩ := dlmf_4_37_23 hx
    exact ⟨cosh_eq_iff_pm (eq_of_side_limit (neBot_upper x) e1 continuous_cosh hU) w,
      cosh_eq_iff_pm (eq_of_side_limit (neBot_lower x) e2 continuous_cosh hD) w⟩

/-- On the cuts of `arctanh` (`|x| > 1`) both side values of 4.37.25 satisfy `tanh = x` (and
are not poles), so 4.37.31 holds with either of them. -/
theorem dlmf_4_37_31_cut {x : ℝ} (hx : 1 < |x|) (w : ℂ) :
    ((cosh w ≠ 0 ∧ tanh w = x) ↔ ∃ k : ℤ,
        w = (π / 2 * I + 1 / 2 * (Real.log ((x + 1) / (x - 1)) : ℂ)) + k * π * I) ∧
      ((cosh w ≠ 0 ∧ tanh w = x) ↔ ∃ k : ℤ,
        w = (-(π / 2 * I) + 1 / 2 * (Real.log ((x + 1) / (x - 1)) : ℂ)) + k * π * I) := by
  obtain ⟨e1, e2⟩ := dlmf_4_37_25 hx
  obtain ⟨c1, t1⟩ := tanh_side_value (neBot_upper x) e1 fun z (hz : 0 < z.im) => Or.inl hz.ne'
  obtain ⟨c2, t2⟩ := tanh_side_value (neBot_lower x) e2 fun z (hz : z.im < 0) => Or.inl hz.ne
  exact ⟨tanh_eq_iff_add_int_mul_pi_I c1 t1 w, tanh_eq_iff_add_int_mul_pi_I c2 t2 w⟩

end Azurite.DLMF
