/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# DLMF §4.5: Inequalities

Formalizations of <https://dlmf.nist.gov/4.5>.

* §4.5(i) Logarithms: 4.5.1, 4.5.2, 4.5.4, 4.5.5 (`dlmf_4_5_1`, `dlmf_4_5_2`, `dlmf_4_5_4`,
  `dlmf_4_5_5`); 4.5.3 with the constant `0.5828…`, the zero of `(3/2)x + ln(1 − x)` following `0`
  (`dlmf_4_5_3`, `zero_0_5828`); 4.5.6 from the Maclaurin series (`dlmf_4_5_6`).
* §4.5(ii) Exponentials: 4.5.7–4.5.12 (`x ≠ 0`) and "When `x = 0` the inequalities become
  equalities" (`dlmf_4_5_ii_zero`); 4.5.13; 4.5.14 with the constant `1.5936…`, the zero of
  `1 − x/2 − e^{−x}` following `0` (`dlmf_4_5_14`, `zero_1_5936`); 4.5.15, 4.5.16 from the
  Maclaurin series.

**Errata.** The strict inequalities 4.5.3 and 4.5.14 are stated for `0 < x ≤ 0.5828…` and
`0 < x ≤ 1.5936…`, but by the DLMF's own notes these right endpoints are zeros of the difference
of the two sides, so equality holds there (`dlmf_4_5_3_endpoint`, `dlmf_4_5_14_endpoint`); the
inequalities hold for `0 < x < 0.5828…` and `0 < x < 1.5936…`.

The constants are certified to the stated four decimals (`0.5828 < c < 0.5829`,
`1.5936 < d < 1.5937`) with Taylor polynomials of `exp` and their remainder bounds, evaluated over
`ℚ` by `decide +kernel`. Mitrinović (1964, 1970) and Bullen (1998) are references.
-/

open Complex Set Filter Topology
open scoped Real

namespace Azurite.DLMF

/-! ### §4.5(i) Logarithms -/

/-- **DLMF 4.5.1**: `x/(1 + x) < ln(1 + x) < x`, `x > −1`, `x ≠ 0`. -/
theorem dlmf_4_5_1 {x : ℝ} (hx : -1 < x) (hx0 : x ≠ 0) :
    x / (1 + x) < Real.log (1 + x) ∧ Real.log (1 + x) < x := by
  have hpos : 0 < 1 + x := by linarith
  refine ⟨?_, by linarith [Real.log_lt_sub_one_of_pos hpos (by intro h; apply hx0; linarith)]⟩
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hpos)
    (by intro h; apply hx0; field_simp at h; linarith)
  rw [Real.log_inv] at h
  have : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
  linarith

/-- **DLMF 4.5.2**: `x < −ln(1 − x) < x/(1 − x)`, `x < 1`, `x ≠ 0`. -/
theorem dlmf_4_5_2 {x : ℝ} (hx : x < 1) (hx0 : x ≠ 0) :
    x < -Real.log (1 - x) ∧ -Real.log (1 - x) < x / (1 - x) := by
  obtain ⟨h1, h2⟩ := dlmf_4_5_1 (x := -x) (by linarith) (neg_ne_zero.mpr hx0)
  rw [← sub_eq_add_neg] at h1 h2
  have : -x / (1 - x) = -(x / (1 - x)) := by ring
  constructor <;> linarith

/-- **DLMF 4.5.4**: `ln x ≤ x − 1`, `x > 0`. -/
theorem dlmf_4_5_4 {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx

/-- **DLMF 4.5.5**: `ln x ≤ a(x^{1/a} − 1)`, `a, x > 0`. -/
theorem dlmf_4_5_5 {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.log x ≤ a * (x ^ (1 / a) - 1) := by
  have h := dlmf_4_5_4 (Real.rpow_pos_of_pos hx (1 / a))
  rw [Real.log_rpow hx] at h
  have : Real.log x = a * (1 / a * Real.log x) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h ha.le

/-- The function `(3/2)x + ln(1 − x)` of 4.5.3. -/
noncomputable def f453 (x : ℝ) : ℝ := 3 / 2 * x + Real.log (1 - x)

/-- If `c ∈ (0, 1)` is a zero of `(3/2)x + ln(1 − x)`, the function is positive on `(0, c)`
(strict concavity of `ln`). -/
theorem f453_pos_of_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hc : f453 c = 0) {x : ℝ}
    (hx0 : 0 < x) (hxc : x < c) : 0 < f453 x := by
  set t := x / c
  have ht0 : 0 < t := div_pos hx0 hc0
  have ht1 : t < 1 := (div_lt_one hc0).mpr hxc
  have h := strictConcaveOn_log_Ioi.2 (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.mpr one_pos)
    (show 1 - c ∈ Ioi (0 : ℝ) from mem_Ioi.mpr (by linarith)) (show (1 : ℝ) ≠ 1 - c by linarith)
    (show 0 < 1 - t by linarith) ht0 (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at h
  have e : 1 - t + t * (1 - c) = 1 - x := by simp only [t]; field_simp; ring
  rw [e] at h
  have hlc : Real.log (1 - c) = -(3 / 2 * c) := by unfold f453 at hc; linarith
  rw [hlc] at h
  unfold f453
  have : t * -(3 / 2 * c) = -(3 / 2 * x) := by simp only [t]; field_simp
  linarith

/-! #### Taylor bounds for `exp` over `ℚ` -/

/-- `∑_{m<n} q^m/m!`. -/
def taylorQ (q : ℚ) (n : ℕ) : ℚ := ∑ m ∈ Finset.range n, q ^ m / m.factorial

/-- The remainder bound `|q|^n (n + 1)/(n! n)` of `Real.exp_bound`. -/
def taylorErrQ (q : ℚ) (n : ℕ) : ℚ := |q| ^ n * ((n + 1 : ℚ) / (n.factorial * n))

theorem exp_taylorQ {q : ℚ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    ((taylorQ q n - taylorErrQ q n : ℚ) : ℝ) ≤ Real.exp q ∧
      Real.exp q ≤ ((taylorQ q n + taylorErrQ q n : ℚ) : ℝ) := by
  have h := Real.exp_bound (x := (q : ℝ)) (by exact_mod_cast hq) hn
  have e1 : ∑ m ∈ Finset.range n, (q : ℝ) ^ m / m.factorial = ((taylorQ q n : ℚ) : ℝ) := by
    simp [taylorQ]
  have e2 : |(q : ℝ)| ^ n * ((n.succ : ℝ) / (n.factorial * n)) =
      ((taylorErrQ q n : ℚ) : ℝ) := by
    simp [taylorErrQ]
  rw [e1, e2] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  push_cast
  constructor <;> linarith

theorem f453_lo_check :
    taylorQ (-8742 / 10000) 12 + taylorErrQ (-8742 / 10000) 12 < 4172 / 10000 := by
  decide +kernel

theorem f453_hi_check :
    4171 / 10000 < taylorQ (-87435 / 100000) 12 - taylorErrQ (-87435 / 100000) 12 := by
  decide +kernel

theorem f453_at_lo : 0 < f453 0.5828 := by
  have h := (exp_taylorQ (q := -8742 / 10000) (by norm_num) (n := 12) (by norm_num)).2
  have hc := (Rat.cast_lt (K := ℝ)).mpr f453_lo_check
  have hexp : Real.exp (-0.8742) < 1 - 0.5828 := by
    have : ((-8742 / 10000 : ℚ) : ℝ) = -0.8742 := by norm_num
    rw [this] at h; norm_num at h hc ⊢; linarith
  have := (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexp
  unfold f453; norm_num at this ⊢; linarith

theorem f453_at_hi : f453 0.5829 < 0 := by
  have h := (exp_taylorQ (q := -87435 / 100000) (by norm_num) (n := 12) (by norm_num)).1
  have hc := (Rat.cast_lt (K := ℝ)).mpr f453_hi_check
  have hexp : 1 - 0.5829 < Real.exp (-0.87435) := by
    have : ((-87435 / 100000 : ℚ) : ℝ) = -0.87435 := by norm_num
    rw [this] at h; norm_num at h hc ⊢; linarith
  have := (Real.log_lt_iff_lt_exp (by norm_num)).mpr hexp
  unfold f453; norm_num at this ⊢; linarith

/-- The constant `0.5828…` of 4.5.3: the zero of `(3/2)x + ln(1 − x)` following `0`; it is the
only zero in `(0, 1)`, the function is positive on `(0, c)`, and `0.5828 < c < 0.5829`. -/
theorem zero_0_5828 :
    ∃ c : ℝ, 0.5828 < c ∧ c < 0.5829 ∧ f453 c = 0 ∧ (∀ x, 0 < x → x < c → 0 < f453 x) ∧
      ∀ c' ∈ Ioo (0 : ℝ) 1, f453 c' = 0 → c' = c := by
  have hcont : ContinuousOn f453 (Icc 0.5828 0.5829) := by
    unfold f453
    refine (continuousOn_const.mul continuousOn_id).add (ContinuousOn.log ?_ fun x hx => ?_)
    · exact (continuousOn_const.sub continuousOn_id)
    · have := hx.2; norm_num at this ⊢; linarith
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (by norm_num) hcont
    (show (0 : ℝ) ∈ Icc (f453 0.5829) (f453 0.5828) from ⟨f453_at_hi.le, f453_at_lo.le⟩)
  have hc1 : 0.5828 < c := lt_of_le_of_ne hc.1 (by rintro rfl; exact f453_at_lo.ne' hc0)
  have hc2 : c < 0.5829 := lt_of_le_of_ne hc.2 (by rintro rfl; exact f453_at_hi.ne hc0)
  have hpos : (0 : ℝ) < c := by linarith
  have hlt : c < 1 := by linarith
  refine ⟨c, hc1, hc2, hc0, fun x hx0 hxc => f453_pos_of_zero hpos hlt hc0 hx0 hxc, ?_⟩
  intro c' hc' hz
  rcases lt_trichotomy c' c with h | h | h
  · exact absurd hz (f453_pos_of_zero hpos hlt hc0 hc'.1 h).ne'
  · exact h
  · exact absurd hc0 (f453_pos_of_zero hc'.1 hc'.2 hz hpos h).ne'

/-- **DLMF 4.5.3**: `|ln(1 − x)| < (3/2)x` for `0 < x < 0.5828…` (`c` the zero of
`zero_0_5828`). -/
theorem dlmf_4_5_3 {c : ℝ} (hc : 0.5828 < c ∧ c < 0.5829 ∧ f453 c = 0 ∧
      (∀ x, 0 < x → x < c → 0 < f453 x) ∧ ∀ c' ∈ Ioo (0 : ℝ) 1, f453 c' = 0 → c' = c)
    {x : ℝ} (hx0 : 0 < x) (hxc : x < c) : |Real.log (1 - x)| < 3 / 2 * x := by
  have h := hc.2.2.2.1 x hx0 hxc
  have hneg : Real.log (1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
  rw [abs_of_neg hneg]
  unfold f453 at h
  linarith

/-- **Erratum to DLMF 4.5.3**: at `x = 0.5828…` itself the two sides are equal, so the strict
inequality fails at the endpoint of the stated range `0 < x ≤ 0.5828…`. -/
theorem dlmf_4_5_3_endpoint {c : ℝ} (hc : 0.5828 < c ∧ c < 0.5829 ∧ f453 c = 0 ∧
      (∀ x, 0 < x → x < c → 0 < f453 x) ∧ ∀ c' ∈ Ioo (0 : ℝ) 1, f453 c' = 0 → c' = c) :
    |Real.log (1 - c)| = 3 / 2 * c := by
  have hneg : Real.log (1 - c) < 0 := Real.log_neg (by linarith) (by linarith)
  rw [abs_of_neg hneg]
  have := hc.2.2.1
  unfold f453 at this
  linarith

/-- **DLMF 4.5.6**: `|ln(1 + z)| ≤ −ln(1 − |z|)`, `|z| < 1`. -/
theorem dlmf_4_5_6 {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have h1 := hasSum_taylorSeries_neg_log' (z := -z) (by rwa [norm_neg])
  rw [sub_neg_eq_add] at h1
  have h2 := Real.hasSum_pow_div_log_of_abs_lt_one (x := ‖z‖) (by rwa [abs_norm])
  have := h1.neg.norm_le_of_bounded h2 fun n => by
    rw [norm_neg, norm_div, norm_pow, norm_neg]
    norm_cast
  simpa using this

/-! ### §4.5(ii) Exponentials -/

/-- **DLMF 4.5.7**: `e^{−x/(1−x)} < 1 − x < e^{−x}`, `x < 1`, `x ≠ 0`. -/
theorem dlmf_4_5_7 {x : ℝ} (hx : x < 1) (hx0 : x ≠ 0) :
    Real.exp (-(x / (1 - x))) < 1 - x ∧ 1 - x < Real.exp (-x) := by
  obtain ⟨h1, h2⟩ := dlmf_4_5_2 hx hx0
  have hpos : 0 < 1 - x := by linarith
  constructor
  · have := Real.exp_lt_exp.mpr (show -(x / (1 - x)) < Real.log (1 - x) by linarith)
    rwa [Real.exp_log hpos] at this
  · have := Real.exp_lt_exp.mpr (show Real.log (1 - x) < -x by linarith)
    rwa [Real.exp_log hpos] at this

/-- **DLMF 4.5.8**: `1 + x < eˣ`, `x ≠ 0`. -/
theorem dlmf_4_5_8 {x : ℝ} (hx0 : x ≠ 0) : 1 + x < Real.exp x := by
  linarith [Real.add_one_lt_exp hx0]

/-- **DLMF 4.5.9**: `eˣ < 1/(1 − x)`, `x < 1`, `x ≠ 0`. -/
theorem dlmf_4_5_9 {x : ℝ} (hx : x < 1) (hx0 : x ≠ 0) : Real.exp x < 1 / (1 - x) := by
  have h := dlmf_4_5_8 (x := -x) (neg_ne_zero.mpr hx0)
  rw [Real.exp_neg, ← sub_eq_add_neg] at h
  rw [lt_div_iff₀ (by linarith)]
  have := Real.exp_pos x
  calc Real.exp x * (1 - x) < Real.exp x * (Real.exp x)⁻¹ := mul_lt_mul_of_pos_left h this
    _ = 1 := mul_inv_cancel₀ this.ne'

/-- **DLMF 4.5.10**: `x/(1 + x) < 1 − e^{−x} < x`, `x > −1`, `x ≠ 0`. -/
theorem dlmf_4_5_10 {x : ℝ} (hx : -1 < x) (hx0 : x ≠ 0) :
    x / (1 + x) < 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) < x := by
  have hpos : 0 < 1 + x := by linarith
  constructor
  · have h := dlmf_4_5_8 hx0
    have : Real.exp (-x) < 1 / (1 + x) := by
      rw [Real.exp_neg, lt_div_iff₀ hpos, mul_comm]
      calc (1 + x) * (Real.exp x)⁻¹ < Real.exp x * (Real.exp x)⁻¹ :=
            mul_lt_mul_of_pos_right h (inv_pos.mpr (Real.exp_pos x))
        _ = 1 := mul_inv_cancel₀ (Real.exp_pos x).ne'
    have e : x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
    linarith
  · have := dlmf_4_5_8 (x := -x) (neg_ne_zero.mpr hx0)
    linarith

/-- **DLMF 4.5.11**: `x < eˣ − 1 < x/(1 − x)`, `x < 1`, `x ≠ 0`. -/
theorem dlmf_4_5_11 {x : ℝ} (hx : x < 1) (hx0 : x ≠ 0) :
    x < Real.exp x - 1 ∧ Real.exp x - 1 < x / (1 - x) := by
  refine ⟨by linarith [dlmf_4_5_8 hx0], ?_⟩
  have h := dlmf_4_5_9 hx hx0
  have e : x / (1 - x) = 1 / (1 - x) - 1 := by field_simp [show (1 : ℝ) - x ≠ 0 by linarith]; ring
  linarith

/-- **DLMF 4.5.12**: `e^{x/(1+x)} < 1 + x`, `x > −1`, `x ≠ 0`. -/
theorem dlmf_4_5_12 {x : ℝ} (hx : -1 < x) (hx0 : x ≠ 0) : Real.exp (x / (1 + x)) < 1 + x := by
  have h := Real.exp_lt_exp.mpr (dlmf_4_5_1 hx hx0).1
  rwa [Real.exp_log (show 0 < 1 + x by linarith)] at h

/-- **DLMF §4.5(ii)**: "When `x = 0` the inequalities become equalities" (4.5.7–4.5.12). -/
theorem dlmf_4_5_ii_zero :
    Real.exp (-(0 / (1 - 0))) = 1 - 0 ∧ 1 - 0 = Real.exp (-0) ∧ 1 + 0 = Real.exp 0 ∧
      Real.exp 0 = 1 / (1 - 0) ∧ 0 / (1 + 0) = 1 - Real.exp (-0) ∧ 1 - Real.exp (-0) = 0 ∧
      0 = Real.exp 0 - 1 ∧ Real.exp 0 - 1 = 0 / (1 - 0) ∧ Real.exp (0 / (1 + 0)) = 1 + 0 := by
  norm_num

/-- **DLMF 4.5.13**: `e^{xy/(x+y)} < (1 + x/y)^y < eˣ`, `x, y > 0`. -/
theorem dlmf_4_5_13 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (x * y / (x + y)) < (1 + x / y) ^ y ∧ (1 + x / y) ^ y < Real.exp x := by
  have ht : 0 < x / y := div_pos hx hy
  obtain ⟨h1, h2⟩ := dlmf_4_5_1 (x := x / y) (by linarith) ht.ne'
  have hb : 0 < 1 + x / y := by linarith
  rw [Real.rpow_def_of_pos hb]
  constructor
  · apply Real.exp_lt_exp.mpr
    have e : x * y / (x + y) = y * (x / y / (1 + x / y)) := by field_simp; ring
    rw [e, mul_comm (Real.log _)]
    exact mul_lt_mul_of_pos_left h1 hy
  · apply Real.exp_lt_exp.mpr
    have e : x = y * (x / y) := by field_simp
    calc Real.log (1 + x / y) * y < x / y * y := mul_lt_mul_of_pos_right h2 hy
      _ = x := by field_simp

/-- The function `1 − x/2 − e^{−x}` of 4.5.14. -/
noncomputable def g4514 (x : ℝ) : ℝ := 1 - x / 2 - Real.exp (-x)

/-- If `d > 0` is a zero of `1 − x/2 − e^{−x}`, the function is positive on `(0, d)` (strict
convexity of `exp`). -/
theorem g4514_pos_of_zero {d : ℝ} (hd0 : 0 < d) (hd : g4514 d = 0) {x : ℝ} (hx0 : 0 < x)
    (hxd : x < d) : 0 < g4514 x := by
  set t := x / d
  have ht0 : 0 < t := div_pos hx0 hd0
  have ht1 : t < 1 := (div_lt_one hd0).mpr hxd
  have h := strictConvexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-d))
    (show (0 : ℝ) ≠ -d by linarith) (show 0 < 1 - t by linarith) ht0 (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have hed : Real.exp (-d) = 1 - d / 2 := by unfold g4514 at hd; linarith
  rw [hed, show t * -d = -x by simp only [t]; field_simp] at h
  unfold g4514
  have : 1 - t + t * (1 - d / 2) = 1 - x / 2 := by simp only [t]; field_simp; ring
  linarith

theorem g4514_lo_check :
    (taylorQ (-7968 / 10000) 12 + taylorErrQ (-7968 / 10000) 12) ^ 2 < 2032 / 10000 := by
  decide +kernel

theorem g4514_hi_check :
    0 ≤ taylorQ (-79685 / 100000) 12 - taylorErrQ (-79685 / 100000) 12 ∧
      20315 / 100000 < (taylorQ (-79685 / 100000) 12 - taylorErrQ (-79685 / 100000) 12) ^ 2 := by
  decide +kernel

theorem g4514_at_lo : 0 < g4514 1.5936 := by
  have h := (exp_taylorQ (q := -7968 / 10000) (by norm_num) (n := 12) (by norm_num)).2
  have hc := (Rat.cast_lt (K := ℝ)).mpr g4514_lo_check
  push_cast at hc
  have hq : ((-7968 / 10000 : ℚ) : ℝ) = -0.7968 := by norm_num
  rw [hq] at h
  have hsq : Real.exp (-1.5936) = Real.exp (-0.7968) ^ 2 := by
    rw [sq, ← Real.exp_add]; norm_num
  have : Real.exp (-0.7968) ^ 2 ≤
      ((taylorQ (-7968 / 10000) 12 + taylorErrQ (-7968 / 10000) 12 : ℚ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h 2
  unfold g4514
  norm_num at hc hsq this ⊢
  linarith

theorem g4514_at_hi : g4514 1.5937 < 0 := by
  have h := (exp_taylorQ (q := -79685 / 100000) (by norm_num) (n := 12) (by norm_num)).1
  obtain ⟨h0, hc⟩ := g4514_hi_check
  have h0' := (Rat.cast_nonneg (K := ℝ)).mpr h0
  have hc' := (Rat.cast_lt (K := ℝ)).mpr hc
  have hq : ((-79685 / 100000 : ℚ) : ℝ) = -0.79685 := by norm_num
  rw [hq] at h
  have hsq : Real.exp (-1.5937) = Real.exp (-0.79685) ^ 2 := by
    rw [sq, ← Real.exp_add]; norm_num
  have : ((taylorQ (-79685 / 100000) 12 - taylorErrQ (-79685 / 100000) 12 : ℚ) : ℝ) ^ 2 ≤
      Real.exp (-0.79685) ^ 2 := pow_le_pow_left₀ h0' h 2
  unfold g4514
  norm_num at hc' hsq this ⊢
  linarith

/-- The constant `1.5936…` of 4.5.14: the zero of `1 − x/2 − e^{−x}` following `0`; it is the only
positive zero, the function is positive on `(0, d)`, and `1.5936 < d < 1.5937`. -/
theorem zero_1_5936 :
    ∃ d : ℝ, 1.5936 < d ∧ d < 1.5937 ∧ g4514 d = 0 ∧ (∀ x, 0 < x → x < d → 0 < g4514 x) ∧
      ∀ d' : ℝ, 0 < d' → g4514 d' = 0 → d' = d := by
  have hcont : ContinuousOn g4514 (Icc 1.5936 1.5937) := by
    unfold g4514; fun_prop
  obtain ⟨d, hd, hd0⟩ := intermediate_value_Icc' (by norm_num) hcont
    (show (0 : ℝ) ∈ Icc (g4514 1.5937) (g4514 1.5936) from ⟨g4514_at_hi.le, g4514_at_lo.le⟩)
  have hd1 : 1.5936 < d := lt_of_le_of_ne hd.1 (by rintro rfl; exact g4514_at_lo.ne' hd0)
  have hd2 : d < 1.5937 := lt_of_le_of_ne hd.2 (by rintro rfl; exact g4514_at_hi.ne hd0)
  have hpos : (0 : ℝ) < d := by linarith
  refine ⟨d, hd1, hd2, hd0, fun x hx0 hxd => g4514_pos_of_zero hpos hd0 hx0 hxd, ?_⟩
  intro d' hd' hz
  rcases lt_trichotomy d' d with h | h | h
  · exact absurd hz (g4514_pos_of_zero hpos hd0 hd' h).ne'
  · exact h
  · exact absurd hd0 (g4514_pos_of_zero hd' hz hpos h).ne'

/-- **DLMF 4.5.14**: `e^{−x} < 1 − x/2` for `0 < x < 1.5936…` (`d` the zero of `zero_1_5936`). -/
theorem dlmf_4_5_14 {d : ℝ} (hd : 1.5936 < d ∧ d < 1.5937 ∧ g4514 d = 0 ∧
      (∀ x, 0 < x → x < d → 0 < g4514 x) ∧ ∀ d' : ℝ, 0 < d' → g4514 d' = 0 → d' = d)
    {x : ℝ} (hx0 : 0 < x) (hxd : x < d) : Real.exp (-x) < 1 - x / 2 := by
  have := hd.2.2.2.1 x hx0 hxd
  unfold g4514 at this
  linarith

/-- **Erratum to DLMF 4.5.14**: at `x = 1.5936…` itself the two sides are equal, so the strict
inequality fails at the endpoint of the stated range `0 < x ≤ 1.5936…`. -/
theorem dlmf_4_5_14_endpoint {d : ℝ} (hd : 1.5936 < d ∧ d < 1.5937 ∧ g4514 d = 0 ∧
      (∀ x, 0 < x → x < d → 0 < g4514 x) ∧ ∀ d' : ℝ, 0 < d' → g4514 d' = 0 → d' = d) :
    Real.exp (-d) = 1 - d / 2 := by
  have := hd.2.2.1
  unfold g4514 at this
  linarith

/-- **DLMF 4.5.15**: `¼|z| < |e^z − 1| < (7/4)|z|`, `0 < |z| < 1`. -/
theorem dlmf_4_5_15 {z : ℂ} (hz0 : 0 < ‖z‖) (hz1 : ‖z‖ < 1) :
    1 / 4 * ‖z‖ < ‖exp z - 1‖ ∧ ‖exp z - 1‖ < 7 / 4 * ‖z‖ := by
  have h := Complex.exp_bound (x := z) hz1.le (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one] at h
  norm_num at h
  have hr : ‖exp z - 1 - z‖ ≤ 3 / 4 * ‖z‖ ^ 2 := by
    have e : exp z - 1 - z = exp z - (1 + z) := by ring
    rw [e]; linarith
  have hsq : ‖z‖ ^ 2 < ‖z‖ := by nlinarith
  constructor
  · have := norm_sub_norm_le z (-(exp z - 1 - z))
    rw [norm_neg, sub_neg_eq_add] at this
    have e : z + (exp z - 1 - z) = exp z - 1 := by ring
    rw [e] at this
    nlinarith
  · have := norm_add_le z (exp z - 1 - z)
    have e : z + (exp z - 1 - z) = exp z - 1 := by ring
    rw [e] at this
    nlinarith

/-- **DLMF 4.5.16**: `|e^z − 1| ≤ e^{|z|} − 1 ≤ |z| e^{|z|}`, `z ∈ ℂ`. -/
theorem dlmf_4_5_16 (z : ℂ) :
    ‖exp z - 1‖ ≤ Real.exp ‖z‖ - 1 ∧ Real.exp ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
  constructor
  · have h1 := (hasSum_nat_add_iff' 1).mpr (dlmf_4_2_19 z)
    have h0 : HasSum (fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖z‖) := by
      rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp ‖z‖
    have h2 := (hasSum_nat_add_iff' 1).mpr h0
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h1 h2
    exact h1.norm_le_of_bounded h2 fun n => by
      rw [norm_div, norm_pow, Complex.norm_natCast]
  · have h := Real.add_one_le_exp (-‖z‖)
    rw [Real.exp_neg] at h
    have hp := Real.exp_pos ‖z‖
    have : 1 - ‖z‖ ≤ (Real.exp ‖z‖)⁻¹ := by linarith
    have h2 : (1 - ‖z‖) * Real.exp ‖z‖ ≤ 1 := by
      calc (1 - ‖z‖) * Real.exp ‖z‖ ≤ (Real.exp ‖z‖)⁻¹ * Real.exp ‖z‖ :=
            mul_le_mul_of_nonneg_right this hp.le
        _ = 1 := inv_mul_cancel₀ hp.ne'
    nlinarith

end Azurite.DLMF
