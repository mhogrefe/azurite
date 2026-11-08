/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section24
import Azurite.DLMF.Chapter4.Section36
import Azurite.DLMF.Chapter4.Section37Log

/-!
# DLMF §4.38 Inverse Hyperbolic Functions: Further Properties

## §4.38(i) Power Series

All principal values are the §4.37 ones (`arcsinhD`, `arccoshD`, `arctanhD`). As DLMF says,
4.38.4–4.38.7 follow from §4.24 (4.38.1 too): the formulas there are applied at `iz`.

* 4.38.1 (`|z| ≤ 1`, absolutely convergent): `dlmf_4_38_1`, from 4.24.1.
* 4.38.2 (`ℜz > 0`, `|z| > 1`), 4.38.3 (`|z| > 1`, off the cut): `dlmf_4_38_2`, `dlmf_4_38_3`.
  Both rest on `ln((1 + (1 + w)^{1/2})/2) = ∑_{n≥1} (−1)ⁿ⁺¹ (1·3⋯(2n − 1))/(2·4⋯(2n)) wⁿ/(2n)`,
  `|w| < 1` (`hasSum_log_half_one_add_sqrt`). The derivative `(1 − (1 + w)^{−1/2})/(2w)` is
  expanded by the binomial series (`halfSqrtSeries_eq`), then integrated term by term along
  `[0, w]` (DLMF's "expand and integrate", with the constant `ln 2` built in). The square roots are
  identified on polar images (`sqrt_sq_add_one_eq`: `(z² + 1)^{1/2} = z(1 + z⁻²)^{1/2}`,
  `coshRoot_eq_mul_sqrt`: `(z − 1)^{1/2}(z + 1)^{1/2} = z(1 − z⁻²)^{1/2}`, via `branch_eq_of_sq`),
  and `ln(2z·u) = ln(2z) + ln u` is checked through the arguments (`log_two_mul_mul`). On the cut
  `x < −1`, 4.38.3 gives the value from above (`dlmf_4_38_3_cut`; **imprecision**).
* 4.38.4 (`|z − 1| ≤ 2`, off the cut): `dlmf_4_38_4`, via the half-angle relation
  `arccosh z = 2 arcsinh(((z − 1)/2)^{1/2})` (`arccoshD_eq_two_mul_arcsinhD`, from 4.37.21 and
  4.37.16) and 4.38.1. DLMF's condition `ℜz > 0` is not needed; on the cut `−1 < x < 1` (which
  `ℜz > 0` partly includes) the formula gives the value from above (`dlmf_4_38_4_cut`;
  **imprecision**).
* 4.38.5 (`|z| ≤ 1`, `z ≠ ±1`): `dlmf_4_38_5` (partial sums), `dlmf_4_38_5_hasSum` (`|z| < 1`).
* 4.38.6 (`ℑz ≷ 0`, `|z| ≥ 1`): `dlmf_4_38_6`.
* 4.38.7 (`ℜ(z²) < ½`), 4.38.8: `dlmf_4_38_7`, `dlmf_4_38_8`.

## §4.38(ii) Derivatives

Each formula holds where the principal value is analytic (off its cuts). The signs `±` are
`σ = ±1`.

* 4.38.9, 4.38.11: `dlmf_4_38_9`, `dlmf_4_38_11` (4.24.9 at `iz`).
* 4.38.10 (`ℜz ≷ 0`): `dlmf_4_38_10`. The branch `coshRoot z = (z − 1)^{1/2}(z + 1)^{1/2}` of the
  4.37.2 integrand is `±(z² − 1)^{1/2}` (`coshRoot_eq_sqrt`, `coshRoot_eq_neg_sqrt`).
* 4.38.12 (`ℜz ≷ 0`): `dlmf_4_38_12`, via `z(1 + z⁻²)^{1/2} = ±(z² + 1)^{1/2}`
  (`mul_sqrt_one_add_inv_sq`, on the right half-plane).
* 4.38.13: `dlmf_4_38_13`, via `z coshRoot(1/z) = (1 − z²)^{1/2}` on the whole cut plane
  (`mul_coshRoot_one_div`; the cut plane is star-shaped about `½`, `starConvex_arcsechDomain`), so
  no sign condition is needed.
* 4.38.14: `dlmf_4_38_14`.

## §4.38(iii) Addition Formulas

DLMF: "every value of the left-hand side is a value of the right-hand side and vice versa. All
square roots have either possible value." The general values are the §4.37(i) sets `arcsinhGen`,
`arccoshGen`, `arctanhGen`, `arccothGen`; arguments at the branch points (`±i` for `Arcsinh`,
`±1` for `Arccosh`) are excluded. The sign `±` is `σ = ±1`. As for §4.24(iii):

* 4.38.16, 4.38.17, the first equality of 4.38.18, 4.38.19: set equalities `dlmf_4_38_16`,
  `dlmf_4_38_17`, `dlmf_4_38_18`, `dlmf_4_38_19`, transported from 4.24.14–4.24.17 by `w ↦ iw`
  (`mem_arcsinhGen_iff_I`, `mem_arccoshGen_iff_I`, `mem_arctanhGen_iff_I`).
* 4.38.15 and the second equality of 4.38.18 (**errata**, the counterparts of 4.24.13 and
  4.24.16): only "every value of the left-hand side is a value of the right-hand side" holds
  (`dlmf_4_38_15`, `dlmf_4_38_18_arccosh`). Counterexamples to the converse:
  `dlmf_4_38_15_converse_fails` (`0 ∈ Arcsinh(1·√2 + 1·(−√2))`, `∉ Arcsinh 1 + Arcsinh 1`) and
  `dlmf_4_38_18_arccosh_converse_fails` (`½πi ∈ Arccosh 0`, `∉ Arcsinh(−i/2) + Arccosh ½`).
-/

open Set Filter Topology Complex MeasureTheory Finset
open scoped Real Interval

namespace Azurite.DLMF

theorem I_pow_two_mul_add_one (n : ℕ) : I ^ (2 * n + 1) = (-1) ^ n * I := by
  rw [pow_succ, pow_mul, I_sq]

/-- **DLMF 4.38.1**: `arcsinh z = z − (1/2)(z³/3) + (1·3)/(2·4)(z⁵/5) − ⋯`, `|z| < 1` (in Lean
`|z| ≤ 1`, absolutely convergent), from 4.24.1 at `iz`. -/
theorem dlmf_4_38_1 {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ => (-1) ^ n * (arcsinCoeff n : ℂ) * z ^ (2 * n + 1) / (2 * n + 1))
      (arcsinhD z) := by
  have h := (dlmf_4_24_1 (z := I * z) (by rwa [norm_mul, norm_I, one_mul])).mul_left (-I)
  rw [← arcsinhD_eq] at h
  refine h.congr_fun fun n => ?_
  rw [mul_pow, I_pow_two_mul_add_one]
  ring_nf; rw [I_sq]; ring

/-- **DLMF 4.38.5**: `arctanh z = z + z³/3 + z⁵/5 + ⋯`, `|z| ≤ 1`, `z ≠ ±1` (partial sums;
conditionally convergent on `|z| = 1`), from 4.24.3 at `iz`. -/
theorem dlmf_4_38_5 {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) (h2 : z ≠ -1) :
    Tendsto (fun K => ∑ k ∈ range K, z ^ (2 * k + 1) / (2 * k + 1)) atTop
      (𝓝 (arctanhD z)) := by
  have hu1 : I * z ≠ I := fun h => h1 (mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm))
  have hu2 : I * z ≠ -I := fun h => h2 (mul_left_cancel₀ I_ne_zero (h.trans (by ring)))
  have h := (dlmf_4_24_3 (z := I * z) (by rwa [norm_mul, norm_I, one_mul]) hu1 hu2).const_mul (-I)
  rw [← arctanhD_eq] at h
  refine h.congr fun K => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_pow, I_pow_two_mul_add_one]
  have hk : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  generalize (-1 : ℂ) ^ k = ε at hk ⊢
  linear_combination (z ^ (2 * k + 1) / (2 * k + 1)) * hk +
    (-ε ^ 2 * z ^ (2 * k + 1) / (2 * k + 1)) * I_sq

/-- **DLMF 4.38.5** inside the unit disc (absolutely convergent). -/
theorem dlmf_4_38_5_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (2 * k + 1) / (2 * k + 1)) (arctanhD z) := by
  have h := (dlmf_4_24_3_hasSum (z := I * z) (by rwa [norm_mul, norm_I, one_mul])).mul_left (-I)
  rw [← arctanhD_eq] at h
  refine h.congr_fun fun k => ?_
  rw [mul_pow, I_pow_two_mul_add_one]
  have hk : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  generalize (-1 : ℂ) ^ k = ε at hk ⊢
  linear_combination (-(z ^ (2 * k + 1) / (2 * k + 1))) * hk +
    (ε ^ 2 * z ^ (2 * k + 1) / (2 * k + 1)) * I_sq

/-- **DLMF 4.38.6**: `arctanh z = ±½πi + 1/z + 1/(3z³) + 1/(5z⁵) + ⋯`, `ℑz ≷ 0`, `|z| ≥ 1`
(partial sums), from 4.24.4 at `iz`. The sign `±` is `σ = ±1`. -/
theorem dlmf_4_38_6 {z : ℂ} (hz : 1 ≤ ‖z‖) {σ : ℝ}
    (hσ : (0 < z.im ∧ σ = 1) ∨ (z.im < 0 ∧ σ = -1)) :
    Tendsto (fun K => σ * (π / 2) * I + ∑ k ∈ range K, 1 / ((2 * k + 1) * z ^ (2 * k + 1)))
      atTop (𝓝 (arctanhD z)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; norm_num at hz
  have hσ' : (0 < (I * z).re ∧ -σ = 1) ∨ ((I * z).re < 0 ∧ -σ = -1) := by
    simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub]
    rcases hσ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  have h := (dlmf_4_24_4 (z := I * z) (by rwa [norm_mul, norm_I, one_mul]) hσ').const_mul (-I)
  rw [← arctanhD_eq] at h
  refine h.congr fun K => ?_
  rw [mul_add, mul_sum]
  push_cast
  congr 1
  · ring
  refine sum_congr rfl fun k _ => ?_
  rw [mul_pow, I_pow_two_mul_add_one]
  have hk : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hd : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
  have hp : z ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ hz0
  rw [pow_succ]
  generalize (-1 : ℂ) ^ k = ε at hk ⊢
  have hε : ε ≠ 0 := fun h => by rw [h] at hk; norm_num at hk
  field_simp

/-- **DLMF 4.38.7**: `arctanh z = z/(1 − z²)(1 + (2/3)(z²/(z² − 1))
+ (2·4)/(3·5)(z²/(z² − 1))² + ⋯)`, `ℜ(z²) < ½`, from 4.24.5 at `iz`. -/
theorem dlmf_4_38_7 {z : ℂ} (hz : (z ^ 2).re < 1 / 2) :
    HasSum (fun n : ℕ => z / (1 - z ^ 2) * ((arctanEulerCoeff n : ℂ) * (z ^ 2 / (z ^ 2 - 1)) ^ n))
      (arctanhD z) := by
  have hw : -(1 / 2) < ((I * z) ^ 2).re := by
    rw [I_mul_sq_eq, neg_re]; linarith
  have h := (dlmf_4_24_5 hw).mul_left (-I)
  rw [← arctanhD_eq] at h
  refine h.congr_fun fun n => ?_
  have e1 : (I * z) ^ 2 / (1 + (I * z) ^ 2) = z ^ 2 / (z ^ 2 - 1) := by
    rw [I_mul_sq_eq, show (1 : ℂ) + -z ^ 2 = -(z ^ 2 - 1) by ring, neg_div_neg_eq]
  have e2 : -I * (I * z / ((I * z) ^ 2 + 1)) = z / (1 - z ^ 2) := by
    rw [I_mul_sq_eq, show -I * (I * z / (-z ^ 2 + 1)) = -(I * I) * (z / (1 - z ^ 2)) by ring,
      I_mul_I, neg_neg, one_mul]
  rw [e1, ← e2, mul_assoc]

/-- **DLMF 4.38.8**: the region `ℜ(z²) < ½` of 4.38.7 lies between the hyperbolas
`x² − y² = ½`. -/
theorem dlmf_4_38_8 (z : ℂ) : (z ^ 2).re < 1 / 2 ↔ z.re ^ 2 - z.im ^ 2 < 1 / 2 := by
  rw [sq z, mul_re, ← sq, ← sq]

/-! ### 4.38.4 -/

theorem arcsinhD_zero : arcsinhD 0 = 0 := by simp [arcsinhD]

/-- Half-angle relation `arccosh z = 2 arcsinh(((z − 1)/2)^{1/2})` (from 4.37.21 and 4.37.16). -/
theorem arccoshD_eq_two_mul_arcsinhD {z : ℂ} (hz : z ∈ arccoshCut ∨ z = 1) :
    arccoshD z = 2 * arcsinhD (((z - 1) / 2) ^ (1 / 2 : ℂ)) := by
  rcases hz with hz | rfl
  · set r := ((z - 1) / 2) ^ (1 / 2 : ℂ) with hr
    have hr2 : r ^ 2 = (z - 1) / 2 := sqrt_half_sq _
    have hre : r.re ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ : ∃ t : ℝ, r = t * I := ⟨r.im, Complex.ext (by simp [h0]) (by simp)⟩
      have hsq : (z - 1) / 2 = ((-(t ^ 2) : ℝ) : ℂ) := by
        rw [← hr2, ht, mul_pow, I_sq]; push_cast; ring
      have him : z.im = 0 := by
        have := congrArg im hsq
        rw [ofReal_im, Complex.div_ofNat_im, sub_im, one_im, sub_zero] at this; linarith
      have hre' : z.re ≤ 1 := by
        have := congrArg re hsq
        rw [ofReal_re, Complex.div_ofNat_re, sub_re, one_re] at this; nlinarith [sq_nonneg t]
      rcases hz with h | h
      · exact h him
      · linarith
    have hp : (r ^ 2 + 1) ^ (1 / 2 : ℂ) = ((z + 1) / 2) ^ (1 / 2 : ℂ) := by
      rw [hr2]; congr 1; ring
    rw [dlmf_4_37_21 (Or.inl hz), dlmf_4_37_16 (Or.inl (Or.inl hre)), hp]
  · rw [arccoshD_one, sub_self, zero_div, zero_cpow (by norm_num), arcsinhD_zero, mul_zero]

/-- The series side of 4.38.4: `2 arcsinh(((z − 1)/2)^{1/2}) = (2(z − 1))^{1/2}(1 + ∑ ⋯)` for
`|z − 1| ≤ 2` (4.38.1 at `((z − 1)/2)^{1/2}`). -/
theorem two_mul_arcsinhD_series {z : ℂ} (hz : ‖z - 1‖ ≤ 2) :
    Summable (fun n : ℕ => (-1) ^ n * (arccosCoeff n : ℂ) * (z - 1) ^ n) ∧
      2 * arcsinhD (((z - 1) / 2) ^ (1 / 2 : ℂ)) =
        (2 * (z - 1)) ^ (1 / 2 : ℂ) * ∑' n : ℕ, (-1) ^ n * (arccosCoeff n : ℂ) * (z - 1) ^ n := by
  set w := ((z - 1) / 2) ^ (1 / 2 : ℂ) with hw
  have hw2 : w ^ 2 = (z - 1) / 2 := sqrt_half_sq _
  have hwn : ‖w‖ ≤ 1 := by
    have h1 : ‖w‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hw2, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      linarith
    nlinarith [norm_nonneg w]
  have h2w : (2 * (z - 1)) ^ (1 / 2 : ℂ) = 2 * w := by
    have h4 : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [show 2 * (z - 1) = ((4 : ℝ) : ℂ) * ((z - 1) / 2) by push_cast; ring,
      ofReal_mul_cpow_half (by norm_num), h4]
    push_cast; rfl
  have hsum : Summable (fun n : ℕ => (-1) ^ n * (arccosCoeff n : ℂ) * (z - 1) ^ n) := by
    refine Summable.of_norm_bounded summable_arcsinCoeff fun n => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, arccosCoeff_eq,
      abs_of_nonneg (div_nonneg (arcsinCoeff_nonneg n) (by positivity))]
    calc arcsinCoeff n / (2 ^ n * (2 * n + 1)) * ‖z - 1‖ ^ n
        ≤ arcsinCoeff n / (2 ^ n * (2 * n + 1)) * 2 ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz n)
            (div_nonneg (arcsinCoeff_nonneg n) (by positivity))
      _ = arcsinCoeff n / (2 * n + 1) := by
          have : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp
  refine ⟨hsum, ?_⟩
  have h := (dlmf_4_38_1 hwn).mul_left 2
  rw [h2w, ← tsum_mul_left, ← h.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [arccosCoeff_eq, pow_succ, pow_mul, hw2, div_pow]
  push_cast
  have : (2 * (n : ℂ) + 1) ≠ 0 := by
    rw [show (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) by push_cast; ring]
    exact_mod_cast (show (2 * n + 1 : ℕ) ≠ 0 by omega)
  field_simp

/-- **DLMF 4.38.4**: `arccosh z = (2(z − 1))^{1/2}(1 + ∑_{n≥1} (−1)ⁿ (1·3·5⋯(2n − 1))/(2²ⁿ n!
(2n + 1)) (z − 1)ⁿ)`, `|z − 1| ≤ 2`, off the cut (and at `z = 1`). The `n = 0` term of the sum
is the leading `1`. DLMF's condition `ℜz > 0` is not needed off the cut; on the cut see
`dlmf_4_38_4_cut`. -/
theorem dlmf_4_38_4 {z : ℂ} (hz : z ∈ arccoshCut ∨ z = 1) (h2 : ‖z - 1‖ ≤ 2) :
    Summable (fun n : ℕ => (-1) ^ n * (arccosCoeff n : ℂ) * (z - 1) ^ n) ∧
      arccoshD z =
        (2 * (z - 1)) ^ (1 / 2 : ℂ) * ∑' n : ℕ, (-1) ^ n * (arccosCoeff n : ℂ) * (z - 1) ^ n := by
  obtain ⟨hs, he⟩ := two_mul_arcsinhD_series h2
  exact ⟨hs, by rw [arccoshD_eq_two_mul_arcsinhD hz, he]⟩

theorem tendsto_div_two_upper (a : ℝ) :
    Tendsto (fun u : ℂ => u / 2) (𝓝[{w | 0 < w.im}] (a : ℂ))
      (𝓝[{w | 0 < w.im}] ((a / 2 : ℝ) : ℂ)) := by
  have hc : Tendsto (fun u : ℂ => u / 2) (𝓝 (a : ℂ)) (𝓝 ((a / 2 : ℝ) : ℂ)) := by
    have : Continuous fun u : ℂ => u / 2 := by fun_prop
    simpa using this.tendsto (a : ℂ)
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u.im)
  show 0 < (u / 2).im
  rw [Complex.div_ofNat_im]; linarith

/-- **DLMF 4.38.4** on the cut `−1 < x < 1` (DLMF's `ℜz > 0` includes `0 < x < 1`): with the
principal `(2(x − 1))^{1/2} = i(2(1 − x))^{1/2}` the formula gives the value from above,
`arccosh(x + i0)`. -/
theorem dlmf_4_38_4_cut {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ))
      (𝓝 ((2 * ((x : ℂ) - 1)) ^ (1 / 2 : ℂ) *
        ∑' n : ℕ, (-1) ^ n * (arccosCoeff n : ℂ) * ((x : ℂ) - 1) ^ n)) := by
  have h2 : ‖(x : ℂ) - 1‖ ≤ 2 := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  rw [← (two_mul_arcsinhD_series h2).2]
  have ha : (x + -1) / 2 ≤ 0 := by linarith [hx.2]
  have hr : ((x : ℂ) - 1) / 2 = (((x + -1) / 2 : ℝ) : ℂ) := by push_cast; ring
  have ht := ((tendsto_sqrt_upper_nonpos ha).comp (tendsto_div_two_upper (x + -1))).comp
    (tendsto_add_real_side x (-1)).1
  rw [← ofReal_cpow_half_of_nonpos ha, ← hr] at ht
  have hcut : (((x : ℂ) - 1) / 2) ^ (1 / 2 : ℂ) ∈ arcsinhCut := by
    rw [hr, ofReal_cpow_half_of_nonpos ha]
    right
    have hs : √(-((x + -1) / 2)) < 1 := by
      rw [Real.sqrt_lt' one_pos]; linarith [hx.1]
    simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using hs
  have hc := ((hasDerivAt_arcsinhD hcut).continuousAt.tendsto.comp ht).const_mul 2
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z.im)
  simp only [Function.comp_apply]
  rw [arccoshD_eq_two_mul_arcsinhD (Or.inl (Or.inl hz.ne'))]
  congr 3; push_cast; ring

/-! ### 4.38.2–4.38.3 -/

/-- The power series of `(1 − (1 + u)^{−1/2})/(2u)` (`halfSqrtSeries_eq`). -/
noncomputable def halfSqrtSeries (u : ℂ) : ℂ :=
  ∑' n : ℕ, (-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * u ^ n / 2

theorem norm_halfSqrtSeries_term_le (n : ℕ) (u : ℂ) :
    ‖(-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * u ^ n / 2‖ ≤ ‖u‖ ^ n := by
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (arcsinCoeff_nonneg _),
    show ‖(2 : ℂ)‖ = 2 by norm_num]
  have h1 := arcsinCoeff_le_one (n + 1)
  have h2 : 0 ≤ ‖u‖ ^ n := by positivity
  nlinarith

theorem summable_halfSqrtSeries {u : ℂ} (hu : ‖u‖ < 1) :
    Summable fun n : ℕ => (-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * u ^ n / 2 :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg u) hu)
    fun n => norm_halfSqrtSeries_term_le n u

theorem halfSqrtSeries_eq {u : ℂ} (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    halfSqrtSeries u = (1 - (1 + u) ^ (-1 / 2 : ℂ)) / (2 * u) := by
  have h := hasSum_one_sub_cpow_neg_half (w := -u) (by rwa [norm_neg])
  rw [sub_neg_eq_add] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  have hc0 : arcsinCoeff 0 = 1 := by simp [arcsinCoeff]
  rw [sum_range_one, hc0] at h1
  have h2 := h1.mul_left (-1 / (2 * u))
  have h3 : HasSum (fun n : ℕ => (-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * u ^ n / 2)
      ((1 - (1 + u) ^ (-1 / 2 : ℂ)) / (2 * u)) := by
    convert h2 using 1
    · funext n; rw [neg_pow (a := u)]; field_simp; ring
    · push_cast; field_simp; ring
  exact h3.tsum_eq

theorem re_one_add_pos {v : ℂ} (hv : ‖v‖ < 1) : 0 < (1 + v).re := by
  have := abs_re_le_norm v
  rw [abs_le] at this
  rw [add_re, one_re]; linarith

theorem log_half_one_add_sqrt_mem {v : ℂ} (hv : ‖v‖ < 1) :
    1 + v ∈ slitPlane ∧ (1 + (1 + v) ^ (1 / 2 : ℂ)) / 2 ∈ slitPlane :=
  ⟨mem_slitPlane_iff.mpr (Or.inl (re_one_add_pos hv)), mem_slitPlane_iff.mpr (Or.inl (by
    rw [Complex.div_ofNat_re, add_re, one_re]; linarith [zero_le_re_cpow_half (1 + v)]))⟩

theorem continuousAt_log_half_one_add_sqrt {v : ℂ} (hv : ‖v‖ < 1) :
    ContinuousAt (fun v : ℂ => log ((1 + (1 + v) ^ (1 / 2 : ℂ)) / 2)) v := by
  obtain ⟨hsl, hq⟩ := log_half_one_add_sqrt_mem hv
  have h1 : ContinuousAt (fun v : ℂ => (1 + v) ^ (1 / 2 : ℂ)) v :=
    (continuousAt_cpow_const hsl).comp (f := fun v : ℂ => 1 + v) (by fun_prop)
  have h2 : ContinuousAt (fun v : ℂ => (1 + (1 + v) ^ (1 / 2 : ℂ)) / 2) v :=
    (continuousAt_const.add h1).div_const 2
  exact ContinuousAt.comp (g := log) (continuousAt_clog hq) h2

theorem hasDerivAt_log_half_one_add_sqrt {u : ℂ} (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    HasDerivAt (fun v : ℂ => log ((1 + (1 + v) ^ (1 / 2 : ℂ)) / 2)) (halfSqrtSeries u) u := by
  obtain ⟨hsl, hq⟩ := log_half_one_add_sqrt_mem hu
  have hR := ((hasDerivAt_id' u).const_add 1).cpow_const (c := (1 / 2 : ℂ)) hsl
  have hd := ((hR.const_add 1).div_const 2).clog hq
  convert hd using 1
  rw [halfSqrtSeries_eq hu hu0]
  have h0 : 1 + u ≠ 0 := slitPlane_ne_zero hsl
  set R := (1 + u) ^ (1 / 2 : ℂ) with hRdef
  have hQ : (1 + u) ^ (-1 / 2 : ℂ) = (1 + u) ^ (1 / 2 - 1 : ℂ) := by norm_num
  rw [hQ]
  set Q := (1 + u) ^ (1 / 2 - 1 : ℂ) with hQdef
  have hRQ : R * Q = 1 := by rw [hRdef, hQdef, ← cpow_add _ _ h0]; norm_num
  have hR2 : R ^ 2 = 1 + u := sqrt_half_sq _
  have h1R : 1 + R ≠ 0 := fun h => by
    have := congrArg re h
    rw [add_re, one_re, zero_re] at this; linarith [zero_le_re_cpow_half (1 + u)]
  field_simp
  linear_combination (-(1 + R)) * hRQ + Q * hR2

/-- `ln((1 + (1 + w)^{1/2})/2) = ∑_{n≥1} (−1)ⁿ⁺¹ (1·3⋯(2n − 1))/(2·4⋯(2n)) wⁿ/(2n)`, `|w| < 1`:
the derivative is `(1 − (1 + w)^{−1/2})/(2w)`, expanded by the binomial series and integrated term
by term along `[0, w]`. -/
theorem hasSum_log_half_one_add_sqrt {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * w ^ (n + 1) / (2 * (n + 1)))
      (log ((1 + (1 + w) ^ (1 / 2 : ℂ)) / 2)) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp only [add_zero, one_cpow, zero_pow (Nat.succ_ne_zero _), mul_zero, zero_div]
    norm_num
  set G : ℂ → ℂ := fun v => log ((1 + (1 + v) ^ (1 / 2 : ℂ)) / 2) with hG
  have hG0 : G 0 = 0 := by simp only [hG, add_zero, one_cpow]; norm_num
  have hball : ∀ s ∈ Icc (0 : ℝ) 1, ‖(s : ℂ) * w‖ < 1 := fun s hs => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [norm_nonneg w, hs.2]
  have hcont : ContinuousOn (fun s : ℝ => G (s * w)) (Icc 0 1) := fun s hs =>
    ((continuousAt_log_half_one_add_sqrt (hball s hs)).comp
      (f := fun s : ℝ => (s : ℂ) * w) (by fun_prop)).continuousWithinAt
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => G (s * w)) (halfSqrtSeries (s * w) * w) s := by
    intro s hs
    have hs0 : (s : ℂ) * w ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hs.1.ne') hw0
    have h := (hasDerivAt_log_half_one_add_sqrt (hball s (Ioo_subset_Icc_self hs)) hs0).comp
      (s : ℂ) (hasDerivAt_mul_const w)
    exact h.comp_ofReal
  have hcontS : ContinuousOn (fun s : ℝ => halfSqrtSeries (s * w) * w) (Icc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    unfold halfSqrtSeries
    refine continuousOn_tsum (u := fun n => ‖w‖ ^ n) (fun n => by fun_prop)
      (summable_geometric_of_lt_one (norm_nonneg w) hw) fun n s hs => ?_
    refine (norm_halfSqrtSeries_term_le n _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact pow_le_pow_left₀ (mul_nonneg hs.1 (norm_nonneg _))
      (by nlinarith [norm_nonneg w, hs.2]) n
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    (hcontS.intervalIntegrable_of_Icc zero_le_one)
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, hG0, sub_zero] at hftc
  have hts : HasSum (fun n : ℕ => ∫ s in (0 : ℝ)..1,
      (-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * w ^ (n + 1) / 2 * (s : ℂ) ^ n)
      (∫ s in (0 : ℝ)..1, halfSqrtSeries (s * w) * w) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖w‖ ^ (n + 1)) (fun n => by fun_prop) ?_ ?_ intervalIntegrable_const ?_
    · intro n
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le zero_le_one] at hs
      calc ‖(-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * w ^ (n + 1) / 2 * (s : ℂ) ^ n‖
          = ‖(-1) ^ n * (arcsinCoeff (n + 1) : ℂ) * ((s : ℂ) * w) ^ n / 2‖ * ‖w‖ := by
            rw [← norm_mul]; congr 1; rw [mul_pow, pow_succ]; ring
        _ ≤ ‖(s : ℂ) * w‖ ^ n * ‖w‖ :=
            mul_le_mul_of_nonneg_right (norm_halfSqrtSeries_term_le _ _) (norm_nonneg _)
        _ ≤ ‖w‖ ^ n * ‖w‖ := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ n)
              (norm_nonneg _)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
            nlinarith [norm_nonneg w, hs.2]
        _ = ‖w‖ ^ (n + 1) := (pow_succ _ _).symm
    · refine Eventually.of_forall fun s _ => ?_
      exact ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_right ‖w‖).congr fun n => by
        rw [pow_succ]
    · refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le zero_le_one] at hs
      have h := ((summable_halfSqrtSeries (hball s (Ioc_subset_Icc_self hs))).hasSum).mul_right w
      refine h.congr_fun fun n => ?_
      rw [mul_pow, pow_succ]; ring
  rw [hftc] at hts
  refine hts.congr_fun fun n => ?_
  rw [integral_ofReal_pow_mul]
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- Polar coordinates `(r, θ) ↦ r e^{iθ}`. -/
noncomputable def polarC (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * exp (p.2 * I)

theorem continuous_polarC : Continuous polarC := by unfold polarC; fun_prop

theorem isPreconnected_polarC_image (a b c : ℝ) :
    IsPreconnected (polarC '' (Ioi a ×ˢ Ioo b c)) :=
  (isPreconnected_Ioi.prod isPreconnected_Ioo).image _ continuous_polarC.continuousOn

theorem mem_polarC_image {z : ℂ} {a b c : ℝ} (hz : a < ‖z‖) (h1 : b < arg z) (h2 : arg z < c) :
    z ∈ polarC '' (Ioi a ×ˢ Ioo b c) :=
  ⟨(‖z‖, arg z), ⟨hz, h1, h2⟩, norm_mul_exp_arg_mul_I z⟩

theorem polarC_props {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    ‖polarC p‖ = p.1 ∧ (polarC p).re = p.1 * Real.cos p.2 ∧ (polarC p).im = p.1 * Real.sin p.2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [polarC, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hp]
  · rw [polarC, re_ofReal_mul, exp_ofReal_mul_I_re]
  · rw [polarC, im_ofReal_mul, exp_ofReal_mul_I_im]

theorem norm_one_div_sq_lt_one {z : ℂ} (hz : 1 < ‖z‖) : ‖1 / z ^ 2‖ < 1 := by
  rw [norm_div, norm_one, norm_pow, div_lt_one (by positivity)]
  nlinarith

theorem one_add_sqrt_ne_zero (v : ℂ) : 1 + v ^ (1 / 2 : ℂ) ≠ 0 := fun h => by
  have := congrArg re h
  rw [add_re, one_re, zero_re] at this; linarith [zero_le_re_cpow_half v]

theorem sqrt_eq_two_mul_sqrt {a b : ℝ} (h : a = 2 ^ 2 * b) : √a = 2 * √b := by
  rw [h, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- `(z² + 1)^{1/2} = z(1 + 1/z²)^{1/2}` for `ℜz > 0`, `|z| > 1`. -/
theorem sqrt_sq_add_one_eq {z : ℂ} (hre : 0 < z.re) (hz : 1 < ‖z‖) :
    (z ^ 2 + 1) ^ (1 / 2 : ℂ) = z * (1 + 1 / z ^ 2) ^ (1 / 2 : ℂ) := by
  set S := polarC '' (Ioi (1 : ℝ) ×ˢ Ioo (-(π / 2)) (π / 2)) with hS
  have hSp : ∀ w ∈ S, 0 < w.re ∧ 1 < ‖w‖ := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    have hp0 : (0 : ℝ) ≤ p.1 := by have : (1 : ℝ) < p.1 := hp1; linarith
    obtain ⟨hn, hr, -⟩ := polarC_props hp0
    refine ⟨?_, by rw [hn]; exact hp1⟩
    rw [hr]; exact mul_pos (by have : (1 : ℝ) < p.1 := hp1; linarith)
      (Real.cos_pos_of_mem_Ioo hp2)
  have hsl1 : ∀ w ∈ S, w ^ 2 + 1 ∈ slitPlane := fun w hw => by
    obtain ⟨hwr, -⟩ := hSp w hw
    rw [mem_slitPlane_iff]
    by_cases him : w.im = 0
    · left; rw [add_re, one_re, sq, mul_re, him]; nlinarith
    · right; rw [add_im, one_im, add_zero, sq, mul_im]
      intro h; apply him; nlinarith [mul_pos hwr hwr, sq_nonneg w.im]
  have hsl2 : ∀ w ∈ S, 1 + 1 / w ^ 2 ∈ slitPlane := fun w hw =>
    (log_half_one_add_sqrt_mem (norm_one_div_sq_lt_one (hSp w hw).2)).1
  have hw0 : ∀ w ∈ S, w ≠ 0 := fun w hw h => by
    have := (hSp w hw).2; rw [h, norm_zero] at this; linarith
  have hc1 : ContinuousOn (fun w : ℂ => (w ^ 2 + 1) ^ (1 / 2 : ℂ)) S := fun w hw =>
    (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ)) (f := fun w : ℂ => w ^ 2 + 1)
      (continuousAt_cpow_const (hsl1 w hw)) (by fun_prop)).continuousWithinAt
  have hc2 : ContinuousOn (fun w : ℂ => w * (1 + 1 / w ^ 2) ^ (1 / 2 : ℂ)) S := fun w hw => by
    have h1 : ContinuousAt (fun w : ℂ => 1 + 1 / w ^ 2) w :=
      continuousAt_const.add (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (hw0 w hw)))
    exact (continuousAt_id.mul (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ))
      (f := fun w : ℂ => 1 + 1 / w ^ 2) (continuousAt_cpow_const (hsl2 w hw))
        h1)).continuousWithinAt
  have hne : ∀ w ∈ S, w * (1 + 1 / w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := fun w hw =>
    mul_ne_zero (hw0 w hw) (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hsl2 w hw))))
  have hsq : ∀ w ∈ S, ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) ^ 2 =
      (w * (1 + 1 / w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 := fun w hw => by
    rw [sqrt_half_sq, mul_pow, sqrt_half_sq]
    have := pow_ne_zero 2 (hw0 w hw)
    rw [mul_add, mul_one, mul_one_div_cancel this]
  have h2 : ((2 : ℝ) : ℂ) ∈ S := ⟨(2, 0), ⟨by norm_num, by norm_num [Real.pi_pos]⟩, by
    simp [polarC]⟩
  have h0 : ((((2 : ℝ) : ℂ)) ^ 2 + 1) ^ (1 / 2 : ℂ) =
      ((2 : ℝ) : ℂ) * (1 + 1 / ((2 : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
    rw [show (((2 : ℝ) : ℂ)) ^ 2 + 1 = ((5 : ℝ) : ℂ) by push_cast; norm_num,
      show 1 + 1 / ((2 : ℝ) : ℂ) ^ 2 = ((5 / 4 : ℝ) : ℂ) by push_cast; norm_num,
      ofReal_cpow_half (by norm_num), ofReal_cpow_half (by norm_num), ← ofReal_mul,
      sqrt_eq_two_mul_sqrt (by norm_num : (5 : ℝ) = 2 ^ 2 * (5 / 4))]
  have hzS : z ∈ S := mem_polarC_image hz
    (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))).1
    (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))).2
  exact branch_eq_of_sq (isPreconnected_polarC_image _ _ _) hc1 hc2 hne hsq h2 h0 z hzS

/-- `(z² − 1)^{1/2}` in the form `coshRoot z = z(1 − 1/z²)^{1/2}`, `|z| > 1`, off the cut. -/
theorem coshRoot_eq_mul_sqrt {z : ℂ} (hzc : z ∈ arccoshCut) (hz : 1 < ‖z‖) :
    coshRoot z = z * (1 - 1 / z ^ 2) ^ (1 / 2 : ℂ) := by
  set S := polarC '' (Ioi (1 : ℝ) ×ˢ Ioo (-π) π) with hS
  have hSp : ∀ w ∈ S, w ∈ arccoshCut ∧ 1 < ‖w‖ := by
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    have hp1' : (1 : ℝ) < p.1 := hp1
    obtain ⟨hn, hr, hi⟩ := polarC_props (p := p) (by linarith)
    refine ⟨?_, by rw [hn]; exact hp1⟩
    by_cases h : Real.sin p.2 = 0
    · right
      rw [(Real.sin_eq_zero_iff_of_lt_of_lt hp2.1 hp2.2).mp h] at hr
      rw [hr, Real.cos_zero, mul_one]; exact hp1'
    · left; rw [hi]; exact mul_ne_zero (by linarith) h
  have hsl : ∀ w ∈ S, 1 - 1 / w ^ 2 ∈ slitPlane := fun w hw => by
    have := (log_half_one_add_sqrt_mem (v := -(1 / w ^ 2))
      (by rw [norm_neg]; exact norm_one_div_sq_lt_one (hSp w hw).2)).1
    rwa [← sub_eq_add_neg] at this
  have hw0 : ∀ w ∈ S, w ≠ 0 := fun w hw h => by
    have := (hSp w hw).2; rw [h, norm_zero] at this; linarith
  have hc1 : ContinuousOn coshRoot S := fun w hw =>
    (hasDerivAt_coshRoot (hSp w hw).1).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fun w : ℂ => w * (1 - 1 / w ^ 2) ^ (1 / 2 : ℂ)) S := fun w hw => by
    have h1 : ContinuousAt (fun w : ℂ => 1 - 1 / w ^ 2) w :=
      continuousAt_const.sub (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (hw0 w hw)))
    exact (continuousAt_id.mul (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ))
      (f := fun w : ℂ => 1 - 1 / w ^ 2) (continuousAt_cpow_const (hsl w hw))
        h1)).continuousWithinAt
  have hne : ∀ w ∈ S, w * (1 - 1 / w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := fun w hw =>
    mul_ne_zero (hw0 w hw) (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hsl w hw))))
  have hsq : ∀ w ∈ S, coshRoot w ^ 2 = (w * (1 - 1 / w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 := fun w hw => by
    rw [coshRoot_sq, mul_pow, sqrt_half_sq]
    have := pow_ne_zero 2 (hw0 w hw)
    rw [mul_sub, mul_one, mul_one_div_cancel this]
  have h2 : ((2 : ℝ) : ℂ) ∈ S := ⟨(2, 0), ⟨by norm_num, by norm_num [Real.pi_pos]⟩, by
    simp [polarC]⟩
  have h0 : coshRoot ((2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * (1 - 1 / ((2 : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
    rw [(coshRoot_ofReal (by norm_num : (1 : ℝ) ≤ 2)).1,
      show 1 - 1 / ((2 : ℝ) : ℂ) ^ 2 = ((3 / 4 : ℝ) : ℂ) by push_cast; norm_num,
      ofReal_cpow_half (by norm_num), ← ofReal_mul,
      sqrt_eq_two_mul_sqrt (by norm_num : (2 : ℝ) ^ 2 - 1 = 2 ^ 2 * (3 / 4))]
  have harg : arg z < π := lt_of_le_of_ne (arg_le_pi z) fun h => by
    obtain ⟨hre, him⟩ := arg_eq_pi_iff.mp h
    rcases hzc with h' | h'
    · exact h' him
    · linarith
  have hzS : z ∈ S := mem_polarC_image hz (neg_pi_lt_arg z) harg
  exact branch_eq_of_sq (isPreconnected_polarC_image _ _ _) hc1 hc2 hne hsq h2 h0 z hzS

theorem arg_cpow_half_props {v : ℂ} (hv : 0 < v.re) :
    v ≠ 0 ∧ (log v * (1 / 2)).im = arg v / 2 := by
  refine ⟨fun h => by rw [h, zero_re] at hv; exact lt_irrefl _ hv, ?_⟩
  simp [log_im, div_eq_mul_inv]

theorem im_cpow_half_nonpos {v : ℂ} (hv : 0 < v.re) (h : v.im ≤ 0) :
    (v ^ (1 / 2 : ℂ)).im ≤ 0 := by
  obtain ⟨hv0, him⟩ := arg_cpow_half_props hv
  rw [cpow_def_of_ne_zero hv0, exp_im, him]
  have ha : arg v ≤ 0 := by
    rw [arg_of_re_nonneg hv.le]
    exact Real.arcsin_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg h (norm_nonneg _))
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
      (by linarith [neg_pi_lt_arg v, Real.pi_pos]))

theorem im_cpow_half_nonneg {v : ℂ} (hv : 0 < v.re) (h : 0 ≤ v.im) :
    0 ≤ (v ^ (1 / 2 : ℂ)).im := by
  obtain ⟨hv0, him⟩ := arg_cpow_half_props hv
  rw [cpow_def_of_ne_zero hv0, exp_im, him]
  exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [arg_nonneg_iff.mpr h]) (by linarith [arg_le_pi v, Real.pi_pos]))

/-- `arg z + arg u ∈ (−π, π]` when `ℜu > 0` and either `ℜz ≥ 0` or `ℑu` does not have the sign
of `ℑz`. -/
theorem arg_add_arg_mem {z u : ℂ} (hu : 0 < u.re)
    (h : 0 ≤ z.re ∨ (0 < z.im ∧ u.im ≤ 0) ∨ (z.im < 0 ∧ 0 ≤ u.im)) :
    arg z + arg u ∈ Ioc (-π) π := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hπ := Real.pi_pos
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hz1, hz2⟩ := abs_le.mp (abs_arg_le_pi_div_two_iff.mpr h)
    constructor <;> linarith
  · have hz := arg_nonneg_iff.mpr h1.le
    have ha : arg u ≤ 0 := by
      rw [arg_of_re_nonneg hu.le]
      exact Real.arcsin_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg h2 (norm_nonneg _))
    constructor <;> linarith [arg_le_pi z]
  · have hz := arg_neg_iff.mpr h1
    have ha := arg_nonneg_iff.mpr h2
    constructor <;> linarith [neg_pi_lt_arg z]

theorem log_two_mul_mul {z u : ℂ} (hz : z ≠ 0) (hu : 0 < u.re)
    (h : 0 ≤ z.re ∨ (0 < z.im ∧ u.im ≤ 0) ∨ (z.im < 0 ∧ 0 ≤ u.im)) :
    log (2 * z * u) = log (2 * z) + log u := by
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, zero_re] at hu; exact lt_irrefl _ hu
  refine (log_mul_eq_add_log_iff (mul_ne_zero two_ne_zero hz) hu0).mpr ?_
  rw [show (2 : ℂ) * z = ((2 : ℝ) : ℂ) * z by norm_num, arg_real_mul _ two_pos]
  exact arg_add_arg_mem hu h

theorem re_half_one_add_sqrt_pos (v : ℂ) : 0 < ((1 + v ^ (1 / 2 : ℂ)) / 2).re := by
  rw [Complex.div_ofNat_re, add_re, one_re]; linarith [zero_le_re_cpow_half v]

theorem inv_sq_pow_term (z : ℂ) (n : ℕ) : (1 / z ^ 2) ^ (n + 1) = 1 / z ^ (2 * (n + 1)) := by
  rw [div_pow, one_pow, ← pow_mul]

/-- **DLMF 4.38.2**: `arcsinh z = ln(2z) + (1/2)(1/(2z²)) − (1·3)/(2·4)(1/(4z⁴))
+ (1·3·5)/(2·4·6)(1/(6z⁶)) − ⋯`, `ℜz > 0`, `|z| > 1`. The `n`-th term is that of `1/z^{2(n+1)}`. -/
theorem dlmf_4_38_2 {z : ℂ} (hre : 0 < z.re) (hz : 1 < ‖z‖) :
    HasSum (fun n : ℕ => (-1) ^ n * (arcsinCoeff (n + 1) : ℂ) / (2 * (n + 1) * z ^ (2 * (n + 1))))
      (arcsinhD z - log (2 * z)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  have hG := hasSum_log_half_one_add_sqrt (norm_one_div_sq_lt_one hz)
  have h1 : arcsinhD z = log (2 * z) + log ((1 + (1 + 1 / z ^ 2) ^ (1 / 2 : ℂ)) / 2) := by
    rw [dlmf_4_37_16 (Or.inl (Or.inl hre.ne')), sqrt_sq_add_one_eq hre hz,
      show z * (1 + 1 / z ^ 2) ^ (1 / 2 : ℂ) + z =
        2 * z * ((1 + (1 + 1 / z ^ 2) ^ (1 / 2 : ℂ)) / 2) by ring]
    exact log_two_mul_mul hz0 (re_half_one_add_sqrt_pos _) (Or.inl hre.le)
  rw [h1, add_sub_cancel_left]
  refine hG.congr_fun fun n => ?_
  rw [inv_sq_pow_term]
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have := pow_ne_zero (2 * (n + 1)) hz0
  field_simp

/-- **DLMF 4.38.3**: `arccosh z = ln(2z) − (1/2)(1/(2z²)) − (1·3)/(2·4)(1/(4z⁴))
− (1·3·5)/(2·4·6)(1/(6z⁶)) − ⋯`, `|z| > 1`, off the cut (for the cut see `dlmf_4_38_3_cut`). -/
theorem dlmf_4_38_3 {z : ℂ} (hzc : z ∈ arccoshCut) (hz : 1 < ‖z‖) :
    HasSum (fun n : ℕ => (arcsinCoeff (n + 1) : ℂ) / (2 * (n + 1) * z ^ (2 * (n + 1))))
      (log (2 * z) - arccoshD z) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  have hG := hasSum_log_half_one_add_sqrt (w := -(1 / z ^ 2))
    (by rw [norm_neg]; exact norm_one_div_sq_lt_one hz)
  rw [← sub_eq_add_neg] at hG
  set R := (1 - 1 / z ^ 2) ^ (1 / 2 : ℂ) with hR
  have hv : 0 < (1 - 1 / z ^ 2).re := by
    have := re_one_add_pos (v := -(1 / z ^ 2)) (by rw [norm_neg]; exact norm_one_div_sq_lt_one hz)
    rwa [← sub_eq_add_neg] at this
  have hvim : (1 - 1 / z ^ 2).im = 2 * z.re * z.im / normSq (z ^ 2) := by
    rw [sub_im, one_im, one_div, inv_im, sq, mul_im]; ring
  have hsign : 0 ≤ z.re ∨ (0 < z.im ∧ ((1 + R) / 2).im ≤ 0) ∨
      (z.im < 0 ∧ 0 ≤ ((1 + R) / 2).im) := by
    have hn : 0 < normSq (z ^ 2) := normSq_pos.mpr (pow_ne_zero 2 hz0)
    rw [Complex.div_ofNat_im, add_im, one_im, zero_add]
    rcases le_or_gt 0 z.re with h | h
    · exact Or.inl h
    have him : z.im ≠ 0 := hzc.resolve_right fun h' => by linarith
    rcases lt_or_gt_of_ne him with h' | h'
    · refine Or.inr (Or.inr ⟨h', ?_⟩)
      have := im_cpow_half_nonneg hv (by rw [hvim]; exact div_nonneg (by nlinarith) hn.le)
      linarith
    · refine Or.inr (Or.inl ⟨h', ?_⟩)
      have := im_cpow_half_nonpos hv (by
        rw [hvim]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hn.le)
      linarith
  have h1 : arccoshD z = log (2 * z) + log ((1 + R) / 2) := by
    rw [arccoshD_eq_log hzc, coshRoot_eq_mul_sqrt hzc hz, ← hR,
      show z + z * R = 2 * z * ((1 + R) / 2) by ring]
    exact log_two_mul_mul hz0 (re_half_one_add_sqrt_pos _) hsign
  rw [h1, sub_add_cancel_left]
  refine hG.neg.congr_fun fun n => ?_
  rw [neg_pow (1 / z ^ 2), inv_sq_pow_term, pow_succ]
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have := pow_ne_zero (2 * (n + 1)) hz0
  have hk : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  generalize (-1 : ℂ) ^ n = ε at hk ⊢
  field_simp
  linear_combination (-(arcsinCoeff (n + 1) : ℂ)) * hk

/-- **DLMF 4.38.3** on the cut `x < −1` (DLMF's `|z| > 1` includes it): with the principal
`ln(2x) = ln(−2x) + πi` the formula gives the value from above, `arccosh(x + i0)` (4.37.23). -/
theorem dlmf_4_38_3_cut {x : ℝ} (hx : x < -1) :
    Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ))
      (𝓝 (log (2 * x) -
        ∑' n : ℕ, (arcsinCoeff (n + 1) : ℂ) / (2 * (n + 1) * (x : ℂ) ^ (2 * (n + 1))))) := by
  have hy : ((-x : ℝ) : ℂ) ∈ arccoshCut := Or.inr (by rw [ofReal_re]; linarith)
  have hn : 1 < ‖((-x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have h := (dlmf_4_38_3 hy hn).tsum_eq
  have hev : ∀ n : ℕ, ((-x : ℝ) : ℂ) ^ (2 * (n + 1)) = (x : ℂ) ^ (2 * (n + 1)) := fun n => by
    push_cast; exact Even.neg_pow ⟨n + 1, by ring⟩ _
  simp only [hev] at h
  rw [h]
  have e1 : arccoshD ((-x : ℝ) : ℂ) = ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ) := by
    rw [arccoshD_ofReal (by linarith), Real.arcosh, neg_sq]; congr 2; ring
  have e2 : log (2 * (x : ℂ)) = log (2 * ((-x : ℝ) : ℂ)) + π * I := by
    have hneg : 2 * x < 0 := by linarith
    rw [show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by push_cast; ring,
      show 2 * ((-x : ℝ) : ℂ) = ((-(2 * x) : ℝ) : ℂ) by push_cast; ring]
    apply Complex.ext
    · rw [log_re, add_re, log_re, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg]
      simp
    · rw [log_im, add_im, log_im, arg_ofReal_of_neg hneg, arg_ofReal_of_nonneg (by linarith)]
      simp
  rw [e1, e2, show log (2 * ((-x : ℝ) : ℂ)) + π * I -
      (log (2 * ((-x : ℝ) : ℂ)) - ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ)) =
      π * I + ((Real.log (√(x ^ 2 - 1) - x) : ℝ) : ℂ) by ring]
  exact (dlmf_4_37_23 hx.le).1

/-! ## §4.38(ii) Derivatives -/

/-- **DLMF 4.38.9**: `d/dz arcsinh z = (1 + z²)^{−1/2}` (off the cuts). -/
theorem dlmf_4_38_9 {z : ℂ} (hz : z ∈ arcsinhCut) :
    HasDerivAt arcsinhD ((1 + z ^ 2) ^ (-1 / 2 : ℂ)) z := by
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  exact hasDerivAt_arcsinhD hz

theorem coshRoot_eq_neg_sqrt {z : ℂ} (hz : z ∈ arccoshCut) (hre : z.re < 0) :
    coshRoot z = -(z ^ 2 - 1) ^ (1 / 2 : ℂ) := by
  have him : z.im ≠ 0 := hz.resolve_right fun h => by linarith
  have hneg : -z ∈ arccoshCut := Or.inl (by simpa using him)
  have h := coshRoot_eq_sqrt hneg (by simp; linarith)
  rw [coshRoot_neg him, neg_sq] at h
  linear_combination -h

/-- **DLMF 4.38.10**: `d/dz arccosh z = ±(z² − 1)^{−1/2}`, `ℜz ≷ 0` (off the cut). The sign `±`
is `σ = ±1`. -/
theorem dlmf_4_38_10 {z : ℂ} (hz : z ∈ arccoshCut) {σ : ℝ}
    (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    HasDerivAt arccoshD (σ * (z ^ 2 - 1) ^ (-1 / 2 : ℂ)) z := by
  have h := hasDerivAt_arccoshD hz
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring, cpow_neg]
  rcases hσ with ⟨hre, rfl⟩ | ⟨hre, rfl⟩
  · rw [coshRoot_eq_sqrt hz hre] at h
    convert h using 1; push_cast; simp only [one_div, one_mul]
  · rw [coshRoot_eq_neg_sqrt hz hre] at h
    convert h using 1; push_cast; simp only [one_div, inv_neg]; ring

/-- **DLMF 4.38.11**: `d/dz arctanh z = 1/(1 − z²)` (off the cuts). -/
theorem dlmf_4_38_11 {z : ℂ} (hz : z ∈ arctanhCut) : HasDerivAt arctanhD (1 / (1 - z ^ 2)) z := by
  have he : arctanhD = fun w => -I * arctanD (I * w) := funext arctanhD_eq
  have h := ((dlmf_4_24_9 (I_mul_mem_arctanCut.mpr hz)).comp z
    ((hasDerivAt_id' z).const_mul I)).const_mul (-I)
  rw [he]
  convert h using 1
  · rfl
  rw [mul_one, I_mul_sq_eq, show (1 : ℂ) + -z ^ 2 = 1 - z ^ 2 by ring]
  linear_combination (1 / (1 - z ^ 2)) * I_sq

theorem sq_add_one_mem_slitPlane_right {w : ℂ} (hw : 0 < w.re) : w ^ 2 + 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left; rw [add_re, one_re, sq, mul_re, him]; nlinarith
  · right; rw [add_im, one_im, add_zero, sq, mul_im]
    intro h; apply him; nlinarith [mul_pos hw hw, sq_nonneg w.im]

theorem re_one_div_pos {w : ℂ} (hw : 0 < w.re) : 0 < (1 / w).re := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl _ hw
  rw [one_div, inv_re]; exact div_pos hw (normSq_pos.mpr hw0)

/-- `z(1 + 1/z²)^{1/2} = (z² + 1)^{1/2}` on the right half-plane. -/
theorem mul_sqrt_one_add_inv_sq {z : ℂ} (hre : 0 < z.re) :
    z * (1 + 1 / z ^ 2) ^ (1 / 2 : ℂ) = (z ^ 2 + 1) ^ (1 / 2 : ℂ) := by
  set S := {c : ℂ | 0 < c.re} with hS
  have hpre : IsPreconnected S := (convex_halfSpace_re_gt 0).isPreconnected
  have hw0 : ∀ w ∈ S, w ≠ 0 := fun w (hw : 0 < w.re) h => by
    rw [h, zero_re] at hw; exact lt_irrefl _ hw
  have hsl1 : ∀ w ∈ S, w ^ 2 + 1 ∈ slitPlane := fun w hw => sq_add_one_mem_slitPlane_right hw
  have hsl2 : ∀ w ∈ S, 1 + 1 / w ^ 2 ∈ slitPlane := fun w (hw : 0 < w.re) => by
    have := sq_add_one_mem_slitPlane_right (re_one_div_pos hw)
    rwa [div_pow, one_pow, add_comm] at this
  have hc1 : ContinuousOn (fun w : ℂ => w * (1 + 1 / w ^ 2) ^ (1 / 2 : ℂ)) S := fun w hw => by
    have h1 : ContinuousAt (fun w : ℂ => 1 + 1 / w ^ 2) w :=
      continuousAt_const.add (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (hw0 w hw)))
    exact (continuousAt_id.mul (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ))
      (f := fun w : ℂ => 1 + 1 / w ^ 2) (continuousAt_cpow_const (hsl2 w hw))
        h1)).continuousWithinAt
  have hc2 : ContinuousOn (fun w : ℂ => (w ^ 2 + 1) ^ (1 / 2 : ℂ)) S := fun w hw =>
    (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ)) (f := fun w : ℂ => w ^ 2 + 1)
      (continuousAt_cpow_const (hsl1 w hw)) (by fun_prop)).continuousWithinAt
  have hne : ∀ w ∈ S, (w ^ 2 + 1) ^ (1 / 2 : ℂ) ≠ 0 := fun w hw =>
    cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hsl1 w hw)))
  have hsq : ∀ w ∈ S, (w * (1 + 1 / w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 =
      ((w ^ 2 + 1) ^ (1 / 2 : ℂ)) ^ 2 := fun w hw => by
    rw [sqrt_half_sq, mul_pow, sqrt_half_sq]
    have := pow_ne_zero 2 (hw0 w hw)
    rw [mul_add, mul_one, mul_one_div_cancel this]
  have h1 : (1 : ℂ) ∈ S := by simp [hS]
  exact branch_eq_of_sq hpre hc1 hc2 hne hsq h1 (by norm_num) z hre

/-- **DLMF 4.38.12**: `d/dz arccsch z = ∓1/(z(1 + z²)^{1/2})`, `ℜz ≷ 0`. The sign `±` is
`σ = ±1`. -/
theorem dlmf_4_38_12 {z : ℂ} {σ : ℝ} (hσ : (0 < z.re ∧ σ = 1) ∨ (z.re < 0 ∧ σ = -1)) :
    HasDerivAt arccschD (-σ / (z * (1 + z ^ 2) ^ (1 / 2 : ℂ))) z := by
  have hre : z.re ≠ 0 := by rcases hσ with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  obtain ⟨hz0, hc⟩ := one_div_mem_arctanCut (Or.inl hre)
  have h := (hasDerivAt_arcsinhD hc).comp z ((hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_id z) hz0)
  set R := (1 + z ^ 2) ^ (1 / 2 : ℂ) with hR
  set S := (1 + (1 / z) ^ 2) ^ (1 / 2 : ℂ) with hSdef
  have hS : z * S = σ * R := by
    rw [hSdef, hR, div_pow, one_pow, add_comm (1 : ℂ) (z ^ 2)]
    rcases hσ with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [mul_sqrt_one_add_inv_sq h]; push_cast; ring
    · have := mul_sqrt_one_add_inv_sq (z := -z) (by rw [neg_re]; linarith)
      rw [neg_sq] at this
      push_cast; linear_combination -this
  have hR0 : R ≠ 0 := by
    refine cpow_ne_zero_iff.mpr (Or.inl fun h0 => hre ?_)
    have h1 : (z - I) * (z + I) = 0 := by linear_combination h0 - I_sq
    rcases mul_eq_zero.mp h1 with h1 | h1
    · rw [sub_eq_zero.mp h1, I_re]
    · rw [eq_neg_of_add_eq_zero_left h1, neg_re, I_re, neg_zero]
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by rcases hσ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hS' : S = σ * R / z := by rw [eq_div_iff hz0, mul_comm, hS]
  have hS0 : S ≠ 0 := by
    rw [hS']; refine div_ne_zero (mul_ne_zero ?_ hR0) hz0
    intro h0; rw [h0] at hσ2; norm_num at hσ2
  have hσ0 : (σ : ℂ) ≠ 0 := fun h0 => by rw [h0] at hσ2; norm_num at hσ2
  convert h using 1
  · rfl
  rw [hS']
  field_simp
  linear_combination -hσ2

theorem mem_arcsechDomain_props {w : ℂ} (hw : w.im ≠ 0 ∨ (0 < w.re ∧ w.re < 1)) :
    1 - w ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  have e1 : (1 - w ^ 2).re = 1 - w.re ^ 2 + w.im ^ 2 := by simp [sq]; ring
  have e2 : (1 - w ^ 2).im = -(2 * w.re * w.im) := by simp [sq]; ring
  by_cases h : w.re * w.im = 0
  · left; rw [e1]
    rcases mul_eq_zero.mp h with h | h
    · rw [h]; nlinarith [sq_nonneg w.im]
    · obtain ⟨h1, h2⟩ := hw.resolve_left (not_not.mpr h)
      rw [h]; nlinarith
  · right; rw [e2]; intro h'; apply h; linarith

/-- The domain of 4.38.13 is star-shaped about `½`. -/
theorem starConvex_arcsechDomain :
    StarConvex ℝ ((1 / 2 : ℝ) : ℂ) {w : ℂ | w.im ≠ 0 ∨ (0 < w.re ∧ w.re < 1)} := by
  intro w hw a b ha hb hab
  have hre : (a • ((1 / 2 : ℝ) : ℂ) + b • w).re = a / 2 + b * w.re := by
    simp [Complex.real_smul]; ring
  have him : (a • ((1 / 2 : ℝ) : ℂ) + b • w).im = b * w.im := by simp [Complex.real_smul]
  show (a • ((1 / 2 : ℝ) : ℂ) + b • w).im ≠ 0 ∨
    (0 < (a • ((1 / 2 : ℝ) : ℂ) + b • w).re ∧ (a • ((1 / 2 : ℝ) : ℂ) + b • w).re < 1)
  rw [hre, him]
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · right; rw [← hb0] at hab ⊢; rw [add_zero] at hab; rw [hab]; norm_num
  rcases hw with h | ⟨h1, h2⟩
  · left; exact mul_ne_zero hb0.ne' h
  · right; constructor <;> nlinarith

/-- `z coshRoot(1/z) = (1 − z²)^{1/2}` on the domain of 4.38.13 (no sign change). -/
theorem mul_coshRoot_one_div {z : ℂ} (hz : z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)) :
    z * coshRoot (1 / z) = (1 - z ^ 2) ^ (1 / 2 : ℂ) := by
  set S := {w : ℂ | w.im ≠ 0 ∨ (0 < w.re ∧ w.re < 1)} with hS
  have hh : ((1 / 2 : ℝ) : ℂ) ∈ S := Or.inr ⟨by simp, by simp; norm_num⟩
  have hpre : IsPreconnected S :=
    (starConvex_arcsechDomain.isPathConnected hh).isConnected.isPreconnected
  have hc1 : ContinuousOn (fun w : ℂ => w * coshRoot (1 / w)) S := fun w hw => by
    obtain ⟨hw0, hc⟩ := one_div_mem_arccoshCut hw
    have h1 : ContinuousAt (fun w : ℂ => 1 / w) w := continuousAt_const.div continuousAt_id hw0
    exact (continuousAt_id.mul (ContinuousAt.comp (g := coshRoot) (f := fun w : ℂ => 1 / w)
      (hasDerivAt_coshRoot hc).continuousAt h1)).continuousWithinAt
  have hc2 : ContinuousOn (fun w : ℂ => (1 - w ^ 2) ^ (1 / 2 : ℂ)) S := fun w hw =>
    (ContinuousAt.comp (g := fun x : ℂ => x ^ (1 / 2 : ℂ)) (f := fun w : ℂ => 1 - w ^ 2)
      (continuousAt_cpow_const (mem_arcsechDomain_props hw)) (by fun_prop)).continuousWithinAt
  have hne : ∀ w ∈ S, (1 - w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := fun w hw =>
    cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (mem_arcsechDomain_props hw)))
  have hsq : ∀ w ∈ S, (w * coshRoot (1 / w)) ^ 2 = ((1 - w ^ 2) ^ (1 / 2 : ℂ)) ^ 2 :=
    fun w hw => by
      rw [mul_pow, coshRoot_sq, sqrt_half_sq]
      have := pow_ne_zero 2 (one_div_mem_arccoshCut hw).1
      rw [div_pow, one_pow, mul_sub, mul_one, mul_one_div_cancel this]
  have h0 : ((1 / 2 : ℝ) : ℂ) * coshRoot (1 / ((1 / 2 : ℝ) : ℂ)) =
      (1 - ((1 / 2 : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
    rw [show 1 / ((1 / 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) by push_cast; norm_num,
      (coshRoot_ofReal (by norm_num : (1 : ℝ) ≤ 2)).1,
      show 1 - ((1 / 2 : ℝ) : ℂ) ^ 2 = ((3 / 4 : ℝ) : ℂ) by push_cast; norm_num,
      ofReal_cpow_half (by norm_num), ← ofReal_mul,
      sqrt_eq_two_mul_sqrt (by norm_num : (2 : ℝ) ^ 2 - 1 = 2 ^ 2 * (3 / 4))]
    congr 1; ring
  exact branch_eq_of_sq hpre hc1 hc2 hne hsq hh h0 z hz

/-- **DLMF 4.38.13**: `d/dz arcsech z = −1/(z(1 − z²)^{1/2})` (off the cuts
`(−∞, 0] ∪ [1, ∞)`; no sign condition is needed). -/
theorem dlmf_4_38_13 {z : ℂ} (hz : z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)) :
    HasDerivAt arcsechD (-1 / (z * (1 - z ^ 2) ^ (1 / 2 : ℂ))) z := by
  obtain ⟨hz0, hc⟩ := one_div_mem_arccoshCut hz
  have h := (hasDerivAt_arccoshD hc).comp z
    ((hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_id z) hz0)
  have hm := mul_coshRoot_one_div hz
  have hR0 : (1 - z ^ 2) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (mem_arcsechDomain_props hz)))
  have hC : coshRoot (1 / z) = (1 - z ^ 2) ^ (1 / 2 : ℂ) / z := by
    rw [eq_div_iff hz0, mul_comm, hm]
  convert h using 1
  · rfl
  rw [hC]
  field_simp
  ring

/-- **DLMF 4.38.14**: `d/dz arccoth z = 1/(1 − z²)` (off the cut `[−1, 1]`). -/
theorem dlmf_4_38_14 {z : ℂ} (hz : z.im ≠ 0 ∨ 1 < |z.re|) :
    HasDerivAt arccothD (1 / (1 - z ^ 2)) z := by
  obtain ⟨hz0, hc⟩ := one_div_mem_arcsinCut hz
  have h := (dlmf_4_38_11 hc).comp z ((hasDerivAt_const z (1 : ℂ)).div (hasDerivAt_id z) hz0)
  have h1 : 1 - z ^ 2 ≠ 0 := fun h0 => by
    have h2 : (z - 1) * (z + 1) = 0 := by linear_combination -h0
    rcases mul_eq_zero.mp h2 with h2 | h2
    · rw [sub_eq_zero.mp h2] at hz; norm_num at hz
    · rw [eq_neg_of_add_eq_zero_left h2] at hz; norm_num at hz
  have hz2 := pow_ne_zero 2 hz0
  have h2 : 1 - (1 / z) ^ 2 ≠ 0 := by
    rw [div_pow, one_pow, one_sub_div hz2]
    exact div_ne_zero (fun h0 => h1 (by linear_combination -h0)) hz2
  have h3 : z ^ 2 - 1 ≠ 0 := fun h0 => h1 (by linear_combination -h0)
  convert h using 1
  · rfl
  rw [div_pow, one_pow, one_sub_div hz2, one_div_div]
  field_simp
  ring

/-! ## §4.38(iii) Addition Formulas -/

theorem sign_hyp {σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (b : ℂ) :
    sinh (σ * b) = σ * sinh b ∧ cosh (σ * b) = cosh b ∧ σ * σ = 1 := by
  rcases hσ with rfl | rfl <;> simp [sinh_neg, cosh_neg]

/-- `w ∈ Arccosh z` iff `iw ∈ Arccos z` (`z ≠ ±1`, 4.28.9). -/
theorem mem_arccoshGen_iff_I {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arccoshGen z ↔ I * w ∈ arccosGen z := by
  rw [mem_arccoshGen_iff h1 h2, mem_arccosGen_iff h1 h2, dlmf_4_28_9]

theorem I_mul_ne_one_iff {z : ℂ} : I * z ≠ 1 ↔ z ≠ -I :=
  not_congr I_mul_eq_one_iff

theorem I_mul_ne_neg_one_iff {z : ℂ} : I * z ≠ -1 ↔ z ≠ I :=
  not_congr I_mul_eq_neg_one_iff

/-- **DLMF 4.38.15** (one inclusion): every value of `Arcsinh u ± Arcsinh v` is a value of
`Arcsinh(u(1 + v²)^{1/2} ± v(1 + u²)^{1/2})` for some choice of the square roots. The converse
fails (`dlmf_4_38_15_converse_fails`, erratum). The sign `±` is `σ = ±1`. -/
theorem dlmf_4_38_15 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ I) (hu2 : u ≠ -I)
    (hv1 : v ≠ I) (hv2 : v ≠ -I)
    (hR : ∀ r s : ℂ, r ^ 2 = 1 + v ^ 2 → s ^ 2 = 1 + u ^ 2 →
      u * r + σ * v * s ≠ I ∧ u * r + σ * v * s ≠ -I) :
    ∀ a ∈ arcsinhGen u, ∀ b ∈ arcsinhGen v, ∃ r s : ℂ, r ^ 2 = 1 + v ^ 2 ∧ s ^ 2 = 1 + u ^ 2 ∧
      a + σ * b ∈ arcsinhGen (u * r + σ * v * s) := by
  intro a ha b hb
  rw [mem_arcsinhGen_iff hu1 hu2] at ha
  rw [mem_arcsinhGen_iff hv1 hv2] at hb
  have hr : cosh b ^ 2 = 1 + v ^ 2 := by rw [cosh_sq, hb]; ring
  have hs : cosh a ^ 2 = 1 + u ^ 2 := by rw [cosh_sq, ha]; ring
  obtain ⟨h1, h2⟩ := hR _ _ hr hs
  refine ⟨cosh b, cosh a, hr, hs, ?_⟩
  obtain ⟨hsn, hcs, -⟩ := sign_hyp hσ b
  rw [mem_arcsinhGen_iff h1 h2, sinh_add, hsn, hcs, ha, hb]
  ring

theorem one_ne_I' : (1 : ℂ) ≠ I := fun h => by simpa using congrArg im h

theorem one_ne_neg_I' : (1 : ℂ) ≠ -I := fun h => by simpa using congrArg im h

/-- **Erratum to 4.38.15**: with `u = v = 1` and the roots `(1 + v²)^{1/2} = √2`,
`(1 + u²)^{1/2} = −√2`, `w = 0` is a value of `Arcsinh(u√2 + v(−√2)) = Arcsinh 0` but not a value
of `Arcsinh 1 + Arcsinh 1` (if `a + b = 0` then `sinh b = −sinh a`). -/
theorem dlmf_4_38_15_converse_fails :
    ((√2 : ℝ) : ℂ) ^ 2 = 1 + (1 : ℂ) ^ 2 ∧ (-((√2 : ℝ) : ℂ)) ^ 2 = 1 + (1 : ℂ) ^ 2 ∧
      (0 : ℂ) ∈ arcsinhGen (1 * ((√2 : ℝ) : ℂ) + 1 * -((√2 : ℝ) : ℂ)) ∧
      ¬ ∃ a ∈ arcsinhGen (1 : ℂ), ∃ b ∈ arcsinhGen (1 : ℂ), (0 : ℂ) = a + b := by
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨by rw [h2]; norm_num, by rw [neg_sq, h2]; norm_num, ?_, ?_⟩
  · rw [show 1 * ((√2 : ℝ) : ℂ) + 1 * -((√2 : ℝ) : ℂ) = 0 by ring,
      mem_arcsinhGen_iff (by simp [Complex.ext_iff]) (by simp [Complex.ext_iff]), sinh_zero]
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [mem_arcsinhGen_iff one_ne_I' one_ne_neg_I'] at ha hb
    rw [show b = -a by linear_combination -hab, sinh_neg, ha] at hb
    norm_num at hb

/-- **DLMF 4.38.16**: `Arccosh u ± Arccosh v = Arccosh(uv ± ((u² − 1)(v² − 1))^{1/2})` (as sets of
values, the square root taking either value), from 4.24.14 under `w ↦ iw`. -/
theorem dlmf_4_38_16 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ 1) (hu2 : u ≠ -1)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ R : ℂ, R ^ 2 = (u ^ 2 - 1) * (v ^ 2 - 1) → u * v + σ * R ≠ 1 ∧ u * v + σ * R ≠ -1) :
    {w | ∃ a ∈ arccoshGen u, ∃ b ∈ arccoshGen v, w = a + σ * b} =
      {w | ∃ R : ℂ, R ^ 2 = (u ^ 2 - 1) * (v ^ 2 - 1) ∧ w ∈ arccoshGen (u * v + σ * R)} := by
  have hsq : ∀ R : ℂ, (-R) ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) ↔ R ^ 2 = (u ^ 2 - 1) * (v ^ 2 - 1) :=
    fun R => by rw [neg_sq]; constructor <;> intro h <;> linear_combination h
  have hR' : ∀ R : ℂ, R ^ 2 = (1 - u ^ 2) * (1 - v ^ 2) →
      u * v - σ * R ≠ 1 ∧ u * v - σ * R ≠ -1 := fun R h => by
    have := hR (-R) (by rw [neg_sq]; linear_combination h)
    rwa [mul_neg, ← sub_eq_add_neg] at this
  have h := dlmf_4_24_14 hσ hu1 hu2 hv1 hv2 hR'
  ext w
  have hw := Set.ext_iff.mp h (I * w)
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨R', hR'2, hw'⟩ := hw.mp ⟨I * a, (mem_arccoshGen_iff_I hu1 hu2).mp ha, I * b,
      (mem_arccoshGen_iff_I hv1 hv2).mp hb, by ring⟩
    obtain ⟨h1, h2⟩ := hR' _ hR'2
    refine ⟨-R', by rw [neg_sq, hR'2]; ring, ?_⟩
    rw [mul_neg, ← sub_eq_add_neg, mem_arccoshGen_iff_I h1 h2]
    exact hw'
  · rintro ⟨R, hR2, hwR⟩
    obtain ⟨h1, h2⟩ := hR _ hR2
    obtain ⟨a', ha', b', hb', hab⟩ := hw.mpr ⟨-R, (hsq R).mpr hR2, by
      rw [mul_neg, sub_neg_eq_add, ← mem_arccoshGen_iff_I h1 h2]; exact hwR⟩
    refine ⟨-I * a', ?_, -I * b', ?_, ?_⟩
    · rw [mem_arccoshGen_iff_I hu1 hu2, I_mul_neg_I_mul]; exact ha'
    · rw [mem_arccoshGen_iff_I hv1 hv2, I_mul_neg_I_mul]; exact hb'
    · linear_combination (-I) * hab + w * I_sq

/-- **DLMF 4.38.17**: `Arctanh u ± Arctanh v = Arctanh((u ± v)/(1 ± uv))` (as sets of values), from
4.24.15 under `w ↦ iw`. -/
theorem dlmf_4_38_17 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hd : 1 + σ * u * v ≠ 0) :
    {w | ∃ a ∈ arctanhGen u, ∃ b ∈ arctanhGen v, w = a + σ * b} =
      arctanhGen ((u + σ * v) / (1 + σ * u * v)) := by
  have hd' : 1 - σ * (I * u) * (I * v) ≠ 0 := by
    rw [show 1 - σ * (I * u) * (I * v) = 1 + σ * u * v - σ * u * v * (I ^ 2 + 1) by ring, I_sq]
    simpa using hd
  have hv1' : I * v ≠ I := fun h => hv1 (mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm))
  have hv2' : I * v ≠ -I := fun h => hv2 (mul_left_cancel₀ I_ne_zero (h.trans (by ring)))
  have h := dlmf_4_24_15 hσ hv1' hv2' hd'
  have hd0 : 1 - σ * (I * u) * (I * v) = 1 + σ * u * v := by
    linear_combination (-σ * u * v) * I_sq
  have ht : I * ((u + σ * v) / (1 + σ * u * v)) =
      (I * u + σ * (I * v)) / (1 - σ * (I * u) * (I * v)) := by
    rw [hd0]; ring
  ext w
  show _ ↔ w ∈ arctanhGen _
  rw [mem_arctanhGen_iff_I, ht, ← h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨I * a, mem_arctanhGen_iff_I.mp ha, I * b, mem_arctanhGen_iff_I.mp hb, by ring⟩
  · rintro ⟨a', ha', b', hb', hab⟩
    refine ⟨-I * a', ?_, -I * b', ?_, ?_⟩
    · rw [mem_arctanhGen_iff_I, I_mul_neg_I_mul]; exact ha'
    · rw [mem_arctanhGen_iff_I, I_mul_neg_I_mul]; exact hb'
    · linear_combination (-I) * hab + w * I_sq

/-- **DLMF 4.38.18** (first equality):
`Arcsinh u ± Arccosh v = Arcsinh(uv ± ((1 + u²)(v² − 1))^{1/2})` (as sets of values, the square
root taking either value), from 4.24.16 under `w ↦ iw`. -/
theorem dlmf_4_38_18 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ I) (hu2 : u ≠ -I)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ R : ℂ, R ^ 2 = (1 + u ^ 2) * (v ^ 2 - 1) → u * v + σ * R ≠ I ∧ u * v + σ * R ≠ -I) :
    {w | ∃ a ∈ arcsinhGen u, ∃ b ∈ arccoshGen v, w = a + σ * b} =
      {w | ∃ R : ℂ, R ^ 2 = (1 + u ^ 2) * (v ^ 2 - 1) ∧ w ∈ arcsinhGen (u * v + σ * R)} := by
  have hmap : ∀ R' : ℂ, I * (u * v + σ * (-I * R')) = I * u * v + σ * R' := fun R' => by
    linear_combination (-σ * R') * I_sq
  have hsq : ∀ R' : ℂ, R' ^ 2 = (1 - (I * u) ^ 2) * (1 - v ^ 2) →
      (-I * R') ^ 2 = (1 + u ^ 2) * (v ^ 2 - 1) := fun R' h => by
    rw [mul_pow, neg_sq, I_sq, h, I_mul_sq_eq]; ring
  have hR' : ∀ R' : ℂ, R' ^ 2 = (1 - (I * u) ^ 2) * (1 - v ^ 2) →
      I * u * v + σ * R' ≠ 1 ∧ I * u * v + σ * R' ≠ -1 := fun R' h => by
    obtain ⟨h1, h2⟩ := hR _ (hsq R' h)
    rw [← hmap]
    exact ⟨I_mul_ne_one_iff.mpr h2, I_mul_ne_neg_one_iff.mpr h1⟩
  have h := dlmf_4_24_16 hσ (I_mul_ne_one_iff.mpr hu2) (I_mul_ne_neg_one_iff.mpr hu1) hv1 hv2 hR'
  ext w
  have hw := Set.ext_iff.mp h (I * w)
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨R', hR'2, hw'⟩ := hw.mp ⟨I * a, mem_arcsinhGen_iff_I.mp ha, I * b,
      (mem_arccoshGen_iff_I hv1 hv2).mp hb, by ring⟩
    refine ⟨-I * R', hsq R' hR'2, ?_⟩
    rw [mem_arcsinhGen_iff_I, hmap]
    exact hw'
  · rintro ⟨R, hR2, hwR⟩
    rw [mem_arcsinhGen_iff_I] at hwR
    have hR'2 : (I * R) ^ 2 = (1 - (I * u) ^ 2) * (1 - v ^ 2) := by
      rw [mul_pow, I_sq, hR2, I_mul_sq_eq]; ring
    obtain ⟨a', ha', b', hb', hab⟩ := hw.mpr ⟨I * R, hR'2, by
      rw [show I * u * v + σ * (I * R) = I * (u * v + σ * R) by ring]; exact hwR⟩
    refine ⟨-I * a', ?_, -I * b', ?_, ?_⟩
    · rw [mem_arcsinhGen_iff_I, I_mul_neg_I_mul]; exact ha'
    · rw [mem_arccoshGen_iff_I hv1 hv2, I_mul_neg_I_mul]; exact hb'
    · linear_combination (-I) * hab + w * I_sq

/-- **DLMF 4.38.18** (second equality, one inclusion): every value of `Arcsinh u ± Arccosh v` is
a value of `Arccosh(v(1 + u²)^{1/2} ± u(v² − 1)^{1/2})` for some choice of the square roots. The
converse fails (`dlmf_4_38_18_arccosh_converse_fails`, erratum). -/
theorem dlmf_4_38_18_arccosh {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hu1 : u ≠ I) (hu2 : u ≠ -I)
    (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hR : ∀ s r : ℂ, s ^ 2 = 1 + u ^ 2 → r ^ 2 = v ^ 2 - 1 →
      v * s + σ * u * r ≠ 1 ∧ v * s + σ * u * r ≠ -1) :
    ∀ a ∈ arcsinhGen u, ∀ b ∈ arccoshGen v, ∃ s r : ℂ, s ^ 2 = 1 + u ^ 2 ∧ r ^ 2 = v ^ 2 - 1 ∧
      a + σ * b ∈ arccoshGen (v * s + σ * u * r) := by
  intro a ha b hb
  rw [mem_arcsinhGen_iff hu1 hu2] at ha
  rw [mem_arccoshGen_iff hv1 hv2] at hb
  have hs : cosh a ^ 2 = 1 + u ^ 2 := by rw [cosh_sq, ha]; ring
  have hr : sinh b ^ 2 = v ^ 2 - 1 := by rw [← hb, cosh_sq]; ring
  obtain ⟨h1, h2⟩ := hR _ _ hs hr
  refine ⟨cosh a, sinh b, hs, hr, ?_⟩
  obtain ⟨hsn, hcs, -⟩ := sign_hyp hσ b
  rw [mem_arccoshGen_iff h1 h2, cosh_add, hsn, hcs, ha, hb]
  ring

/-- **Erratum to 4.38.18** (second equality): with `u = −i/2`, `v = ½` and the roots
`(1 + u²)^{1/2} = √3/2`, `(v² − 1)^{1/2} = −i√3/2`, `w = ½πi` is a value of
`Arccosh(v(1 + u²)^{1/2} + u(v² − 1)^{1/2}) = Arccosh 0` but not a value of
`Arcsinh(−i/2) + Arccosh ½` (`cosh(½πi − a) = −i sinh a = −½`). -/
theorem dlmf_4_38_18_arccosh_converse_fails :
    ((√3 / 2 : ℝ) : ℂ) ^ 2 = 1 + (-I / 2) ^ 2 ∧
      (-I * ((√3 / 2 : ℝ) : ℂ)) ^ 2 = (1 / 2 : ℂ) ^ 2 - 1 ∧
      (π / 2 * I) ∈ arccoshGen ((1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ) +
        (-I / 2) * (-I * ((√3 / 2 : ℝ) : ℂ))) ∧
      ¬ ∃ a ∈ arcsinhGen (-I / 2), ∃ b ∈ arccoshGen (1 / 2 : ℂ), π / 2 * I = a + b := by
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hn1 : (-I / 2 : ℂ) ≠ I := fun h => by
    have := congrArg im h; simp at this; norm_num at this
  have hn2 : (-I / 2 : ℂ) ≠ -I := fun h => by
    have := congrArg im h; simp at this; norm_num at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · push_cast; rw [div_pow, h3, div_pow, neg_sq, I_sq]; norm_num
  · push_cast; rw [mul_pow, neg_sq, I_sq, div_pow, h3]; norm_num
  · rw [show (1 / 2 : ℂ) * ((√3 / 2 : ℝ) : ℂ) + (-I / 2) * (-I * ((√3 / 2 : ℝ) : ℂ)) =
        ((√3 / 2 : ℝ) : ℂ) / 2 * (1 + I ^ 2) by ring, I_sq, add_neg_cancel, mul_zero,
      mem_arccoshGen_iff (by norm_num) (by norm_num), cosh_mul_I, ← ofReal_ofNat,
      ← ofReal_div, ← ofReal_cos, Real.cos_pi_div_two, ofReal_zero]
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [mem_arcsinhGen_iff hn1 hn2] at ha
    rw [mem_arccoshGen_iff (by norm_num) (by norm_num)] at hb
    rw [show b = π / 2 * I - a by linear_combination -hab, cosh_sub, cosh_mul_I, sinh_mul_I,
      ha, ← ofReal_ofNat, ← ofReal_div, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two] at hb
    have : (-1 / 2 : ℂ) = 1 / 2 := by push_cast at hb; linear_combination hb - (1 / 2) * I_sq
    norm_num at this

/-- **DLMF 4.38.19**: `Arctanh u ± Arccoth v = Arctanh((uv ± 1)/(v ± u))
= Arccoth((v ± u)/(uv ± 1))` (as sets of values), from 4.38.17 and 4.37.6. -/
theorem dlmf_4_38_19 {u v σ : ℂ} (hσ : σ = 1 ∨ σ = -1) (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hv2 : v ≠ -1) (hd : v + σ * u ≠ 0) :
    {w | ∃ a ∈ arctanhGen u, ∃ b ∈ arccothGen v, w = a + σ * b} =
        arctanhGen ((u * v + σ) / (v + σ * u)) ∧
      arctanhGen ((u * v + σ) / (v + σ * u)) = arccothGen ((v + σ * u) / (u * v + σ)) := by
  have h1 : 1 / v ≠ 1 := fun h => hv1 (by rw [div_eq_iff hv0] at h; linear_combination -h)
  have h2 : 1 / v ≠ -1 := fun h => hv2 (by rw [div_eq_iff hv0] at h; linear_combination h)
  have hd' : 1 + σ * u * (1 / v) ≠ 0 := by
    rw [show 1 + σ * u * (1 / v) = (v + σ * u) / v by field_simp]
    exact div_ne_zero hd hv0
  refine ⟨?_, by rw [arccothGen, one_div_div]⟩
  rw [show arccothGen v = arctanhGen (1 / v) from rfl, dlmf_4_38_17 hσ h1 h2 hd']
  congr 1
  field_simp

end Azurite.DLMF
