/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# DLMF §4.32 Inequalities (hyperbolic functions, `x` real)

* 4.32.1 `cosh x ≤ (sinh x / x)³` (`x ≠ 0`; at `x = 0` the quotient is the removable value
  `1`): `dlmf_4_32_1`. Proof by power series: `4 sinh³ x − 4x³ cosh x = sinh 3x − 3 sinh x −
  4x³ cosh x` has the nonnegative coefficients `(3^{2n+1} − 3)/(2n+1)! − 4/(2n−2)!`
  (`three_pow_bound`).
* 4.32.2 `sin x cos x < tanh x < x`, `x > 0`: `dlmf_4_32_2` (`tanh_lt_self`; the left part by
  monotonicity on `(0, 1]` and `tanh x > ½` for `x > 1`).
* 4.32.3 `|cosh x − cosh y| ≥ |x − y| (sinh x sinh y)^{1/2}`, `x, y > 0`: `dlmf_4_32_3`
  (`cosh x − cosh y = 2 sinh((x+y)/2) sinh((x−y)/2)`).
* 4.32.4 `arctan x ≤ ½π tanh x`, `x ≥ 0`: `dlmf_4_32_4` (`tan(½π tanh x) − x` is nondecreasing,
  since `cos²(½πt) ≤ ½π(1 − t²)` for `0 ≤ t < 1`).
-/

open Set Filter Topology Real
open scoped Nat

namespace Azurite.DLMF

/-! ### 4.32.1 -/

/-- `4(2m+3)(2m+2)(2m+1) + 3 ≤ 3^{2m+3}`. -/
theorem three_pow_bound (m : ℕ) :
    4 * ((2 * m + 3) * (2 * m + 2) * (2 * m + 1)) + 3 ≤ 3 ^ (2 * m + 3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have e : 3 ^ (2 * (m + 1) + 3) = 9 * 3 ^ (2 * m + 3) := by ring
    have hp : 4 * ((2 * (m + 1) + 3) * (2 * (m + 1) + 2) * (2 * (m + 1) + 1)) + 3 ≤
        9 * (4 * ((2 * m + 3) * (2 * m + 2) * (2 * m + 1)) + 3) := by
      ring_nf; nlinarith
    rw [e]; linarith

/-- `x³ cosh x ≤ sinh³ x` for `x ≥ 0`. -/
theorem cube_mul_cosh_le_sinh_cube {x : ℝ} (hx : 0 ≤ x) : x ^ 3 * cosh x ≤ sinh x ^ 3 := by
  have h3 := Real.hasSum_sinh (3 * x)
  have h1 := Real.hasSum_sinh x
  have hc := Real.hasSum_cosh x
  -- `4x³ cosh x = ∑ c n`, `c 0 = 0`, `c (n+1) = 4 x^{2n+3}/(2n)!`
  set c : ℕ → ℝ := fun n => if n = 0 then 0 else 4 * x ^ (2 * n + 1) / ((2 * n - 2)! : ℝ)
  have hcs : HasSum c (4 * x ^ 3 * cosh x) := by
    have h : HasSum (fun n => c (n + 1)) (4 * x ^ 3 * cosh x) := by
      have := hc.mul_left (4 * x ^ 3)
      refine this.congr_fun fun n => ?_
      simp only [c, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        show 2 * (n + 1) - 2 = 2 * n by omega]
      ring
    have := (hasSum_nat_add_iff 1).mp h
    simpa [c] using this
  have hd := ((h3.sub (h1.mul_left 3)).sub hcs)
  have hval : sinh (3 * x) - 3 * sinh x - 4 * x ^ 3 * cosh x =
      4 * (sinh x ^ 3 - x ^ 3 * cosh x) := by
    rw [Real.sinh_three_mul]; ring
  rw [hval] at hd
  have hnn : 0 ≤ 4 * (sinh x ^ 3 - x ^ 3 * cosh x) := by
    refine hd.nonneg fun n => ?_
    rcases n with _ | m
    · simp [c]
    · simp only [c, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        show 2 * (m + 1) - 2 = 2 * m by omega, show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
      have hf : ((2 * m + 3)! : ℝ) = (2 * m + 3) * (2 * m + 2) * (2 * m + 1) * (2 * m)! := by
        rw [show 2 * m + 3 = (2 * m + 2) + 1 by ring, Nat.factorial_succ,
          show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast; ring
      have hb : (4 * ((2 * m + 3) * (2 * m + 2) * (2 * m + 1)) + 3 : ℝ) ≤ 3 ^ (2 * m + 3) := by
        exact_mod_cast three_pow_bound m
      have hfp : (0 : ℝ) < (2 * m)! := by exact_mod_cast Nat.factorial_pos _
      have hxp : 0 ≤ x ^ (2 * m + 3) := pow_nonneg hx _
      rw [hf, mul_pow]
      have hD : (0 : ℝ) < (2 * m + 3) * (2 * m + 2) * (2 * m + 1) * (2 * m)! := by positivity
      have key : (3 : ℝ) ^ (2 * m + 3) * x ^ (2 * m + 3) /
            ((2 * m + 3) * (2 * m + 2) * (2 * m + 1) * (2 * m)!) -
          3 * (x ^ (2 * m + 3) / ((2 * m + 3) * (2 * m + 2) * (2 * m + 1) * (2 * m)!)) -
          4 * x ^ (2 * m + 3) / (2 * m)! =
          x ^ (2 * m + 3) * ((3 ^ (2 * m + 3) - 3 - 4 * ((2 * m + 3) * (2 * m + 2) * (2 * m + 1)))
            / ((2 * m + 3) * (2 * m + 2) * (2 * m + 1) * (2 * m)!)) := by
        field_simp
      rw [key]
      exact mul_nonneg hxp (div_nonneg (by linarith) hD.le)
  linarith

/-- **DLMF 4.32.1**: `cosh x ≤ (sinh x / x)³` for real `x ≠ 0`. -/
theorem dlmf_4_32_1 {x : ℝ} (hx : x ≠ 0) : cosh x ≤ (sinh x / x) ^ 3 := by
  have key : ∀ y : ℝ, 0 < y → cosh y ≤ (sinh y / y) ^ 3 := fun y hy => by
    rw [div_pow, le_div_iff₀ (by positivity), mul_comm]
    exact cube_mul_cosh_le_sinh_cube hy.le
  rcases lt_or_gt_of_ne hx with h | h
  · have := key (-x) (by linarith)
    rwa [cosh_neg, sinh_neg, neg_div_neg_eq] at this
  · exact key x h

/-! ### 4.32.2 -/

theorem hasDerivAt_tanh' (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have hf : tanh = fun x => sinh x / cosh x := funext tanh_eq_sinh_div_cosh
  rw [hf]
  refine ((hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne').congr_deriv ?_
  rw [show cosh x * cosh x - sinh x * sinh x = 1 by rw [← sq, ← sq, cosh_sq]; ring]

theorem one_sub_tanh_sq (x : ℝ) : 1 - tanh x ^ 2 = 1 / cosh x ^ 2 := by
  have hc := (cosh_pos x).ne'
  have h := cosh_sq x
  rw [tanh_eq_sinh_div_cosh, div_pow]
  field_simp
  linear_combination h

/-- `tanh x < x` for `x > 0`. -/
theorem tanh_lt_self {x : ℝ} (hx : 0 < x) : tanh x < x := by
  have hmono : StrictMonoOn (fun x => x - tanh x) (Ici 0) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun y _ => ((hasDerivAt_id y).sub (hasDerivAt_tanh' y)).continuousAt.continuousWithinAt)
      (fun y _ => ((hasDerivAt_id y).sub (hasDerivAt_tanh' y)).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    have h1 : 1 < cosh y := one_lt_cosh.mpr (ne_of_gt hy)
    have : 1 / cosh y ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
  simp only [tanh_zero, sub_zero] at this
  linarith

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_nonneg (sinh_nonneg_iff.mpr hx) (cosh_pos x).le

/-- `tanh x > ½` for `x > 1`. -/
theorem half_lt_tanh {x : ℝ} (hx : 1 < x) : 1 / 2 < tanh x := by
  have hu : 2 < exp x := by linarith [add_one_le_exp x]
  have hv : exp (-x) < 1 / 2 := by
    rw [exp_neg, inv_lt_comm₀ (exp_pos x) (by norm_num)]; linarith
  rw [tanh_eq_sinh_div_cosh, lt_div_iff₀ (cosh_pos x), sinh_eq, cosh_eq]
  linarith

/-- **DLMF 4.32.2**: `sin x cos x < tanh x < x`, `x > 0`. -/
theorem dlmf_4_32_2 {x : ℝ} (hx : 0 < x) : sin x * cos x < tanh x ∧ tanh x < x := by
  refine ⟨?_, tanh_lt_self hx⟩
  rcases le_or_gt x 1 with h1 | h1
  · -- `g = tanh − sin cos` is strictly increasing on `[0, 1]`
    set g := fun x => tanh x - sin x * cos x
    have hg : ∀ y, HasDerivAt g (1 / cosh y ^ 2 - (cos y * cos y + sin y * -sin y)) y :=
      fun y => (hasDerivAt_tanh' y).sub ((hasDerivAt_sin y).mul (hasDerivAt_cos y))
    have hmono : StrictMonoOn g (Icc 0 1) := by
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
        (fun y _ => (hg y).continuousAt.continuousWithinAt) (fun y _ => (hg y).hasDerivWithinAt)
        ?_
      intro y hy
      rw [interior_Icc] at hy
      obtain ⟨hy0, hy1⟩ := hy
      have hs : y - y ^ 3 / 6 < sin y := sin_gt_sub_cube hy0
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hy3 : y ^ 3 ≤ y := by nlinarith
      have ht := tanh_lt_self hy0
      have ht0 := tanh_nonneg_of_nonneg hy0.le
      have hsc := sin_sq_add_cos_sq y
      rw [← one_sub_tanh_sq]
      nlinarith
    have := hmono (left_mem_Icc.mpr zero_le_one) ⟨hx.le, h1⟩ hx
    simp only [g, tanh_zero, sin_zero, zero_mul, sub_zero] at this
    linarith
  · have h2 : sin x * cos x ≤ 1 / 2 := by
      nlinarith [sq_nonneg (sin x - cos x), sin_sq_add_cos_sq x]
    linarith [half_lt_tanh h1]

/-! ### 4.32.3 -/

/-- **DLMF 4.32.3**: `|cosh x − cosh y| ≥ |x − y| (sinh x sinh y)^{1/2}`, `x, y > 0`. -/
theorem dlmf_4_32_3 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| * √(sinh x * sinh y) ≤ |cosh x - cosh y| := by
  set a := (x + y) / 2
  set b := (x - y) / 2
  have hxa : x = a + b := by simp only [a, b]; ring
  have hyb : y = a - b := by simp only [a, b]; ring
  have ha : 0 < sinh a := sinh_pos_iff.mpr (by simp only [a]; linarith)
  have hdiff : cosh x - cosh y = 2 * sinh a * sinh b := by
    rw [hxa, hyb, cosh_add, cosh_sub]; ring
  have hprod : sinh x * sinh y = sinh a ^ 2 - sinh b ^ 2 := by
    rw [hxa, hyb, sinh_add, sinh_sub]
    have h1 := cosh_sq a
    have h2 := cosh_sq b
    linear_combination (sinh a ^ 2) * h2 - (sinh b ^ 2) * h1
  have hsq : √(sinh x * sinh y) ≤ sinh a := by
    rw [hprod]
    calc √(sinh a ^ 2 - sinh b ^ 2) ≤ √(sinh a ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (sinh b)])
      _ = sinh a := Real.sqrt_sq ha.le
  have hb : |b| ≤ |sinh b| := by
    rw [abs_sinh]; exact self_le_sinh_iff.mpr (abs_nonneg b)
  have hxy : |x - y| = 2 * |b| := by
    rw [show x - y = 2 * b by simp only [b]; ring, abs_mul, abs_two]
  rw [hdiff, hxy, abs_mul, abs_mul, abs_two, abs_of_pos ha]
  have := Real.sqrt_nonneg (sinh x * sinh y)
  nlinarith [abs_nonneg b]

/-! ### 4.32.4 -/

theorem cos_sq_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    cos (π / 2 * t) ^ 2 ≤ π / 2 * (1 - t ^ 2) := by
  have hpi := pi_pos
  have hc0 : 0 ≤ cos (π / 2 * t) :=
    cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hc1 := cos_le_one (π / 2 * t)
  have hc : cos (π / 2 * t) ≤ π / 2 * (1 - t) := by
    rw [← sin_pi_div_two_sub, show π / 2 - π / 2 * t = π / 2 * (1 - t) by ring]
    exact sin_le (by nlinarith)
  nlinarith

/-- **DLMF 4.32.4**: `arctan x ≤ ½π tanh x`, `x ≥ 0`. -/
theorem dlmf_4_32_4 {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ 1 / 2 * π * tanh x := by
  have hpi := pi_pos
  have ht : ∀ y : ℝ, 0 ≤ y → 0 ≤ tanh y ∧ tanh y < 1 := fun y hy =>
    ⟨tanh_nonneg_of_nonneg hy, tanh_lt_one y⟩
  have hcos : ∀ y : ℝ, 0 ≤ y → 0 < cos (π / 2 * tanh y) := fun y hy => by
    obtain ⟨h0, h1⟩ := ht y hy
    exact cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  set G := fun y => tan (π / 2 * tanh y) - y
  have hG : ∀ y, 0 ≤ y → HasDerivAt G
      (1 / cos (π / 2 * tanh y) ^ 2 * (π / 2 * (1 / cosh y ^ 2)) - 1) y := fun y hy =>
    (((hasDerivAt_tan (hcos y hy).ne').comp y ((hasDerivAt_tanh' y).const_mul (π / 2))).sub
      (hasDerivAt_id y)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  have hmono : MonotoneOn G (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun y hy => (hG y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hG y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 := interior_subset hy
    obtain ⟨h0, h1⟩ := ht y hy0
    have hc := hcos y hy0
    have hb := cos_sq_le h0 h1
    rw [← one_sub_tanh_sq]
    have hc2 : 0 < cos (π / 2 * tanh y) ^ 2 := by positivity
    rw [sub_nonneg, one_div, ← div_eq_inv_mul, le_div_iff₀ hc2, one_mul]
    linarith
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [G, tanh_zero, mul_zero, tan_zero, sub_zero] at h
  obtain ⟨h0, h1⟩ := ht x hx
  have hθ : π / 2 * tanh x ∈ Ioo (-(π / 2)) (π / 2) := ⟨by nlinarith, by nlinarith⟩
  calc arctan x ≤ arctan (tan (π / 2 * tanh x)) := arctan_strictMono.monotone (by linarith)
    _ = π / 2 * tanh x := arctan_tan hθ.1 hθ.2
    _ = 1 / 2 * π * tanh x := by ring

end Azurite.DLMF
