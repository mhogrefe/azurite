/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# DLMF §4.3: Graphics

Formalizations of the mathematical content of the figures of <https://dlmf.nist.gov/4.3>.

* Figure 4.3.1: "Parallel tangent lines at `(1, 0)` and `(0, 1)`" (`dlmf_4_3_F1_tangents`: both
  slopes are `1`) and "the mirror symmetry across the line `y = x`, demonstrating the inverse
  relationship" (`dlmf_4_3_F1_mirror`).
* Figure 4.3.2, the conformal map `w = e^z`, `z = ln w`: the strip `−π < Im z < π` is mapped
  bijectively onto the `w`-plane cut along the negative real axis, with inverse the principal `ln`
  (`dlmf_4_3_F2_bijOn`, `dlmf_4_3_F2_inverse`), conformally (`dlmf_4_3_F2_conformal`); lines
  parallel to the real axis map onto rays (`dlmf_4_3_F2_rays`), lines parallel to the imaginary
  axis onto circles centered at the origin (`dlmf_4_3_F2_circles`); the labelled corresponding
  points `A`–`F` and `C̄`, `D̄`, `Ē`, with the edges `Im z = ±π` going to the two sides `x ± i0` of
  the cut (`dlmf_4_3_F2_points`, `dlmf_4_3_F2_edges`).
* Figures 4.3.3 and 4.3.4 (surfaces of `|ln(x + iy)|`, `|e^{x+iy}|` colored by phase): "There is
  a branch cut along the negative real axis" is `dlmf_4_2_i_discontinuous`; the height and phase
  of `e^{x+iy}` are `dlmf_4_2_22` and `dlmf_4_2_23` (§4.2).
-/

open Complex Set Filter Topology
open scoped Real

namespace Azurite.DLMF

/-! ### Figure 4.3.1 -/

/-- **Figure 4.3.1**: the tangents of `ln x` at `(1, 0)` and of `eˣ` at `(0, 1)` both have slope
`1`, so they are parallel. -/
theorem dlmf_4_3_F1_tangents :
    HasDerivAt Real.log 1 1 ∧ HasDerivAt Real.exp 1 0 ∧ Real.log 1 = 0 ∧ Real.exp 0 = 1 := by
  refine ⟨by simpa using Real.hasDerivAt_log one_ne_zero, by simpa using Real.hasDerivAt_exp 0,
    Real.log_one, Real.exp_zero⟩

/-- **Figure 4.3.1**: the graph of `eˣ` is the mirror image of the graph of `ln x` across
`y = x`. -/
theorem dlmf_4_3_F1_mirror (x y : ℝ) : y = Real.exp x ↔ 0 < y ∧ x = Real.log y := by
  constructor
  · rintro rfl; exact ⟨Real.exp_pos x, (Real.log_exp x).symm⟩
  · rintro ⟨hy, rfl⟩; exact (Real.exp_log hy).symm

/-! ### Figure 4.3.2 -/

/-- The strip `−π < Im z < π`. -/
def logStrip : Set ℂ := {z | -π < z.im ∧ z.im < π}

/-- **Figure 4.3.2**: `w = e^z` maps the strip `−π < Im z < π` bijectively onto the `w`-plane cut
along the negative real axis. -/
theorem dlmf_4_3_F2_bijOn : BijOn exp logStrip slitPlane := by
  refine ⟨fun z hz => ?_, fun z hz w hw h => ?_, fun w hw => ?_⟩
  · rw [mem_slitPlane_iff_arg]
    refine ⟨?_, exp_ne_zero z⟩
    rw [← log_im, log_exp hz.1 hz.2.le]
    exact hz.2.ne
  · rw [← log_exp hz.1 hz.2.le, ← log_exp hw.1 hw.2.le, h]
  · refine ⟨log w, ⟨by rw [log_im]; exact neg_pi_lt_arg w, ?_⟩, exp_log (slitPlane_ne_zero hw)⟩
    rw [log_im]
    exact lt_of_le_of_ne (arg_le_pi w) (mem_slitPlane_iff_arg.mp hw).1

/-- **Figure 4.3.2**: on the strip and the cut plane, `z = ln w` and `w = e^z` are inverse. -/
theorem dlmf_4_3_F2_inverse :
    (∀ z ∈ logStrip, log (exp z) = z) ∧ (∀ w ∈ slitPlane, exp (log w) = w) :=
  ⟨fun _ hz => log_exp hz.1 hz.2.le, fun _ hw => exp_log (slitPlane_ne_zero hw)⟩

/-- **Figure 4.3.2**: the map is conformal: `e^z` and `ln w` are holomorphic with nonvanishing
derivatives on the strip and on the cut plane. -/
theorem dlmf_4_3_F2_conformal :
    (∀ z, HasDerivAt exp (exp z) z ∧ exp z ≠ 0) ∧
      (∀ w ∈ slitPlane, HasDerivAt log w⁻¹ w ∧ w⁻¹ ≠ 0) :=
  ⟨fun z => ⟨hasDerivAt_exp z, exp_ne_zero z⟩,
    fun _ hw => ⟨hasDerivAt_log hw, inv_ne_zero (slitPlane_ne_zero hw)⟩⟩

/-- **Figure 4.3.2**: "Lines parallel to the real axis in the `z`-plane map onto rays in the
`w`-plane": `Im z = c` goes onto the open ray `{t e^{ic} : t > 0}`. -/
theorem dlmf_4_3_F2_rays (c : ℝ) :
    exp '' {z | z.im = c} = {w | ∃ t : ℝ, 0 < t ∧ w = t * exp (c * I)} := by
  ext w
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨Real.exp z.re, Real.exp_pos _, ?_⟩
    rw [ofReal_exp, ← exp_add, ← hz]
    congr 1; exact (re_add_im z).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Real.log t + c * I, by simp, ?_⟩
    rw [exp_add, ← ofReal_exp, Real.exp_log ht]

/-- **Figure 4.3.2**: "lines parallel to the imaginary axis in the `z`-plane map onto circles
centered at the origin": `Re z = c` goes onto the circle `|w| = e^c`. -/
theorem dlmf_4_3_F2_circles (c : ℝ) :
    exp '' {z | z.re = c} = {w | ‖w‖ = Real.exp c} := by
  ext w
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨z, rfl, rfl⟩; exact norm_exp z
  · intro hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw; exact (Real.exp_pos c).ne' hw.symm
    refine ⟨log w, ?_, exp_log hw0⟩
    rw [log_re, hw, Real.log_exp]

/-- **Figure 4.3.2**: the labelled corresponding points (`r` a real parameter): `A = 0 ↦ 1`,
`B = r ↦ e^r`, `F = −r ↦ e^{−r}`, `C, C̄ = r ± iπ ↦ −e^r`, `D, D̄ = ±iπ ↦ −1`,
`E, Ē = −r ± iπ ↦ −e^{−r}`. -/
theorem dlmf_4_3_F2_points (r : ℝ) :
    exp 0 = 1 ∧ exp r = Real.exp r ∧ exp (-r) = Real.exp (-r) ∧
      exp (r + π * I) = -Real.exp r ∧ exp (r - π * I) = -Real.exp r ∧
      exp (π * I) = -1 ∧ exp (-(π * I)) = -1 ∧
      exp (-r + π * I) = -Real.exp (-r) ∧ exp (-r - π * I) = -Real.exp (-r) := by
  have hp : exp (π * I) = -1 := exp_pi_mul_I
  have hm : exp (-(π * I)) = -1 := by rw [exp_neg, hp]; norm_num
  refine ⟨exp_zero, (ofReal_exp r).symm, by rw [← ofReal_neg, ofReal_exp], ?_, ?_, hp, hm, ?_,
    ?_⟩
  · rw [exp_add, hp, ← ofReal_exp]; ring
  · rw [sub_eq_add_neg, exp_add, hm, ← ofReal_exp]; ring
  · rw [exp_add, hp, ← ofReal_neg, ← ofReal_exp]; ring
  · rw [sub_eq_add_neg, exp_add, hm, ← ofReal_neg, ← ofReal_exp]; ring

/-- **Figure 4.3.2**: the edges `Im z = ±π` of the strip correspond to the two sides of the cut:
the upper and lower halves of the strip go into the upper and lower half-planes, and with the
closed definition 4.2.7, `ln(−e^s ± i0) = s ± iπ`. -/
theorem dlmf_4_3_F2_edges (s : ℝ) :
    (∀ z : ℂ, 0 < z.im → z.im < π → 0 < (exp z).im) ∧
      (∀ z : ℂ, -π < z.im → z.im < 0 → (exp z).im < 0) ∧
      Tendsto log (𝓝[{w | 0 < w.im}] (-Real.exp s : ℝ)) (𝓝 (s + π * I)) ∧
      Tendsto log (𝓝[{w | w.im < 0}] (-Real.exp s : ℝ)) (𝓝 (s - π * I)) := by
  have hneg : -Real.exp s < 0 := neg_neg_of_pos (Real.exp_pos s)
  have hlog : Real.log |-Real.exp s| = s := by
    rw [abs_neg, abs_of_pos (Real.exp_pos s), Real.log_exp]
  obtain ⟨h1, h2⟩ := dlmf_4_2_7 hneg
  rw [hlog] at h1 h2
  refine ⟨fun z h0 hπ => ?_, fun z hπ h0 => ?_, h1, h2⟩
  · rw [exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
  · rw [exp_im]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _)
      (Real.sin_neg_of_neg_of_neg_pi_lt h0 hπ)

end Azurite.DLMF
