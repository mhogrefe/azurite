/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section19Log
import Azurite.DLMF.Chapter4.Section19Sec
import Azurite.DLMF.Chapter4.Section28

/-!
# DLMF §4.33 Maclaurin Series and Laurent Series (hyperbolic functions)

* 4.33.1, 4.33.2: `dlmf_4_33_1`, `dlmf_4_33_2` (Mathlib's series).
* 4.33.3: `tanh z = ∑_{n≥1} (2^{2n}(2^{2n} − 1)B_{2n}/(2n)!) z^{2n−1}`, `|z| < ½π`:
  `dlmf_4_33_3` (`tanhCoeff`), from 4.19.3 with `z ↦ iz`.
* "For expansions that correspond to (4.19.4)–(4.19.9), change `z` to `iz` and use
  (4.28.8)–(4.28.13)": `dlmf_4_33_csch` (`0 < |z| < π`), `dlmf_4_33_sech` (`|z| < ½π`, Euler
  numbers), `dlmf_4_33_coth` (`0 < |z| < π`), `dlmf_4_33_log_sinh` (`|z| < π`),
  `dlmf_4_33_log_cosh` (`|z| < ½π`), `dlmf_4_33_log_tanh` (`|z| < ½π`).

As in §4.19, the DLMF index `n ≥ 1` is written `n = m + 1`; `B_n` is Mathlib's `bernoulli`.
-/

open Set Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

/-- **DLMF 4.33.1**: `sinh z = z + z³/3! + z⁵/5! + ⋯`. -/
theorem dlmf_4_33_1 (z : ℂ) : HasSum (fun n : ℕ => z ^ (2 * n + 1) / (2 * n + 1)!) (sinh z) :=
  Complex.hasSum_sinh z

/-- **DLMF 4.33.2**: `cosh z = 1 + z²/2! + z⁴/4! + ⋯`. -/
theorem dlmf_4_33_2 (z : ℂ) : HasSum (fun n : ℕ => z ^ (2 * n) / (2 * n)!) (cosh z) :=
  Complex.hasSum_cosh z

theorem I_mul_pow_odd (z : ℂ) (m : ℕ) :
    (I * z) ^ (2 * m + 1) = (-1) ^ m * I * z ^ (2 * m + 1) := by
  rw [mul_pow, pow_succ, pow_mul, I_sq]

theorem I_mul_pow_even (z : ℂ) (m : ℕ) : (I * z) ^ (2 * m) = (-1) ^ m * z ^ (2 * m) := by
  rw [mul_pow, pow_mul, I_sq]

theorem norm_I_mul (z : ℂ) : ‖I * z‖ = ‖z‖ := by rw [norm_mul, norm_I, one_mul]

theorem neg_one_pow_mul_neg_one_pow (m : ℕ) (q : ℚ) : (-1) ^ m * ((-1) ^ m * q) = q := by
  rw [← mul_assoc, ← mul_pow]; norm_num

theorem neg_I_mul_odd (c z : ℂ) (m : ℕ) :
    -I * (c * (I * z) ^ (2 * m + 1)) = (-1) ^ m * c * z ^ (2 * m + 1) := by
  rw [I_mul_pow_odd]; linear_combination (-c * (-1) ^ m * z ^ (2 * m + 1)) * I_sq

theorem I_mul_odd (c z : ℂ) (m : ℕ) :
    I * (c * (I * z) ^ (2 * m + 1)) = -((-1) ^ m * c) * z ^ (2 * m + 1) := by
  rw [I_mul_pow_odd]; linear_combination (c * (-1) ^ m * z ^ (2 * m + 1)) * I_sq

/-- The coefficient of `z^{2m+1}` in 4.33.3 (`n = m + 1`): `2^{2n}(2^{2n} − 1)B_{2n}/(2n)!`. -/
def tanhCoeff (m : ℕ) : ℚ :=
  2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)!

theorem tanhCoeff_eq (m : ℕ) : tanhCoeff m = (-1) ^ m * tanCoeff m := by
  rw [tanCoeff, show (-1 : ℚ) ^ m * 2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) *
      bernoulli (2 * m + 2) / (2 * m + 2)! = (-1) ^ m * tanhCoeff m by rw [tanhCoeff]; ring,
    neg_one_pow_mul_neg_one_pow]

/-- **DLMF 4.33.3**: `tanh z = z − z³/3 + 2z⁵/15 − 17z⁷/315 + ⋯`, `|z| < ½π`. -/
theorem dlmf_4_33_3 {z : ℂ} (hz : ‖z‖ < π / 2) :
    HasSum (fun m : ℕ => (tanhCoeff m : ℂ) * z ^ (2 * m + 1)) (tanh z) := by
  have h := (dlmf_4_19_3 (z := I * z) (by rwa [norm_I_mul])).mul_left (-I)
  rw [← tanh_eq_neg_I_mul_tan] at h
  refine h.congr_fun fun m => ?_
  rw [neg_I_mul_odd, tanhCoeff_eq]
  push_cast; ring

/-! ### The expansions corresponding to 4.19.4–4.19.9 (`z ↦ iz`, 4.28.8–4.28.13) -/

theorem cschC_eq_I_mul (z : ℂ) : cschC z = I * cscC (I * z) := by
  rw [dlmf_4_28_11, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

theorem cothC_eq_I_mul (z : ℂ) : cothC z = I * cot (I * z) := by
  rw [dlmf_4_28_13, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

theorem I_div_I_mul (z : ℂ) : I * (1 / (I * z)) = 1 / z := by
  rw [mul_one_div, ← div_div, div_self I_ne_zero]

/-- The coefficient of `z^{2m+1}` in the `csch` expansion (`n = m + 1`):
`−2(2^{2n−1} − 1)B_{2n}/(2n)!`. -/
def cschCoeff (m : ℕ) : ℚ := -(2 * (2 ^ (2 * m + 1) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)!)

theorem cschCoeff_eq (m : ℕ) : cschCoeff m = -((-1) ^ m * cscCoeff m) := by
  rw [cscCoeff, show (-1 : ℚ) ^ m * 2 * (2 ^ (2 * m + 1) - 1) * bernoulli (2 * m + 2) /
      (2 * m + 2)! = (-1) ^ m * -cschCoeff m by rw [cschCoeff]; ring,
    neg_one_pow_mul_neg_one_pow, neg_neg]

/-- **DLMF §4.33** (from 4.19.4): `csch z = 1/z − z/6 + 7z³/360 − ⋯
+ (−2(2^{2n−1} − 1)B_{2n}/(2n)!) z^{2n−1} + ⋯`, `0 < |z| < π`. -/
theorem dlmf_4_33_csch {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) :
    HasSum (fun m : ℕ => (cschCoeff m : ℂ) * z ^ (2 * m + 1)) (cschC z - 1 / z) := by
  have h := (dlmf_4_19_4 (z := I * z) (mul_ne_zero I_ne_zero h0) (by rwa [norm_I_mul])).mul_left I
  rw [mul_sub, ← cschC_eq_I_mul, I_div_I_mul] at h
  refine h.congr_fun fun m => ?_
  rw [I_mul_odd, cschCoeff_eq]
  push_cast; ring

/-- The coefficient of `z^{2m+1}` in the `coth` expansion (`n = m + 1`): `2^{2n}B_{2n}/(2n)!`. -/
def cothCoeff (m : ℕ) : ℚ := 2 ^ (2 * m + 2) * bernoulli (2 * m + 2) / (2 * m + 2)!

theorem cothCoeff_eq (m : ℕ) : cothCoeff m = -((-1) ^ m * cotCoeff m) := by
  rw [cotCoeff, mul_neg, neg_neg, show (-1 : ℚ) ^ m * 2 ^ (2 * m + 2) * bernoulli (2 * m + 2) /
      (2 * m + 2)! = (-1) ^ m * cothCoeff m by rw [cothCoeff]; ring, neg_one_pow_mul_neg_one_pow]

/-- **DLMF §4.33** (from 4.19.6): `coth z = 1/z + z/3 − z³/45 + ⋯ + (2^{2n}B_{2n}/(2n)!) z^{2n−1}
+ ⋯`, `0 < |z| < π`. -/
theorem dlmf_4_33_coth {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) :
    HasSum (fun m : ℕ => (cothCoeff m : ℂ) * z ^ (2 * m + 1)) (cothC z - 1 / z) := by
  have h := (dlmf_4_19_6 (z := I * z) (mul_ne_zero I_ne_zero h0) (by rwa [norm_I_mul])).mul_left I
  rw [mul_sub, ← cothC_eq_I_mul, I_div_I_mul] at h
  refine h.congr_fun fun m => ?_
  rw [I_mul_odd, cothCoeff_eq]
  push_cast; ring

/-- The coefficient of `z^{2n}` in the `sech` expansion: `E_{2n}/(2n)!`. -/
noncomputable def sechCoeff (n : ℕ) : ℂ := eulerNumber (2 * n) / (2 * n)!

/-- **DLMF §4.33** (from 4.19.5): `sech z = 1 − z²/2 + 5z⁴/24 − ⋯ + (E_{2n}/(2n)!) z^{2n} + ⋯`,
`|z| < ½π`. -/
theorem dlmf_4_33_sech {z : ℂ} (hz : ‖z‖ < π / 2) :
    HasSum (fun n : ℕ => sechCoeff n * z ^ (2 * n)) (sechC z) := by
  have h := dlmf_4_19_5 (z := I * z) (by rwa [norm_I_mul])
  rw [dlmf_4_28_12] at h
  refine h.congr_fun fun n => ?_
  rw [I_mul_pow_even, secCoeff, sechCoeff, ← mul_assoc, mul_comm _ ((-1 : ℂ) ^ n), ← mul_div_assoc,
    ← mul_assoc, ← mul_pow]
  norm_num

/-- The coefficient of `z^{2n}` in `ln(sinh z/z)`: `2^{2n−1}B_{2n}/(n (2n)!)`. -/
def logSinhCoeff (n : ℕ) : ℚ := 2 ^ (2 * n - 1) * bernoulli (2 * n) / (n * (2 * n)!)

/-- The coefficient of `z^{2n}` in `ln cosh z`: `2^{2n−1}(2^{2n} − 1)B_{2n}/(n (2n)!)`. -/
def logCoshCoeff (n : ℕ) : ℚ :=
  2 ^ (2 * n - 1) * (2 ^ (2 * n) - 1) * bernoulli (2 * n) / (n * (2 * n)!)

/-- The coefficient of `z^{2n}` in `ln(tanh z/z)`: `−2^{2n}(2^{2n−1} − 1)B_{2n}/(n (2n)!)`. -/
def logTanhCoeff (n : ℕ) : ℚ :=
  -(2 ^ (2 * n) * (2 ^ (2 * n - 1) - 1) * bernoulli (2 * n) / (n * (2 * n)!))

theorem logSinhCoeff_eq (n : ℕ) : logSinhCoeff n = (-1) ^ n * logSinCoeff n := by
  rw [logSinCoeff, show (-1 : ℚ) ^ n * 2 ^ (2 * n - 1) * bernoulli (2 * n) / (n * (2 * n)!) =
    (-1) ^ n * logSinhCoeff n by rw [logSinhCoeff]; ring, neg_one_pow_mul_neg_one_pow]

theorem logCoshCoeff_eq (n : ℕ) : logCoshCoeff n = (-1) ^ n * logCosCoeff n := by
  rw [logCosCoeff, show (-1 : ℚ) ^ n * 2 ^ (2 * n - 1) * (2 ^ (2 * n) - 1) * bernoulli (2 * n) /
    (n * (2 * n)!) = (-1) ^ n * logCoshCoeff n by rw [logCoshCoeff]; ring,
    neg_one_pow_mul_neg_one_pow]

theorem logTanhCoeff_eq (m : ℕ) : logTanhCoeff (m + 1) = (-1) ^ (m + 1) * logTanCoeff (m + 1) := by
  rw [logTanCoeff, logTanhCoeff, show m + 1 - 1 = m by omega, pow_succ]
  have := neg_one_pow_mul_neg_one_pow m
    (2 ^ (2 * (m + 1)) * (2 ^ (2 * (m + 1) - 1) - 1) * bernoulli (2 * (m + 1)) /
      (((m + 1 : ℕ) : ℚ) * (2 * (m + 1))!))
  linear_combination this

theorem sinh_div_eq (z : ℂ) : sinh z / z = sin (I * z) / (I * z) := by
  rw [dlmf_4_28_8, mul_div_mul_left _ _ I_ne_zero]

theorem tanh_div_eq (z : ℂ) : tanh z / z = tan (I * z) / (I * z) := by
  rw [dlmf_4_28_10, mul_div_mul_left _ _ I_ne_zero]

/-- **DLMF §4.33** (from 4.19.7): `ln(sinh z/z) = ∑_{n≥1} (2^{2n−1}B_{2n}/(n (2n)!)) z^{2n}`,
`|z| < π`. -/
theorem dlmf_4_33_log_sinh {z : ℂ} (h1 : ‖z‖ < π) :
    HasSum (fun m : ℕ => (logSinhCoeff (m + 1) : ℂ) * z ^ (2 * (m + 1))) (log (sinh z / z)) := by
  have h := dlmf_4_19_7 (z := I * z) (by rwa [norm_I_mul])
  rw [← sinh_div_eq] at h
  refine h.congr_fun fun m => ?_
  rw [I_mul_pow_even, logSinhCoeff_eq]
  push_cast; ring

/-- **DLMF §4.33** (from 4.19.8):
`ln cosh z = ∑_{n≥1} (2^{2n−1}(2^{2n} − 1)B_{2n}/(n (2n)!)) z^{2n}`, `|z| < ½π`. -/
theorem dlmf_4_33_log_cosh {z : ℂ} (h1 : ‖z‖ < π / 2) :
    HasSum (fun m : ℕ => (logCoshCoeff (m + 1) : ℂ) * z ^ (2 * (m + 1))) (log (cosh z)) := by
  have h := dlmf_4_19_8 (z := I * z) (by rwa [norm_I_mul])
  rw [dlmf_4_28_9] at h
  refine h.congr_fun fun m => ?_
  rw [I_mul_pow_even, logCoshCoeff_eq]
  push_cast; ring

/-- **DLMF §4.33** (from 4.19.9):
`ln(tanh z/z) = ∑_{n≥1} (−2^{2n}(2^{2n−1} − 1)B_{2n}/(n (2n)!)) z^{2n}`, `|z| < ½π`. -/
theorem dlmf_4_33_log_tanh {z : ℂ} (h1 : ‖z‖ < π / 2) :
    HasSum (fun m : ℕ => (logTanhCoeff (m + 1) : ℂ) * z ^ (2 * (m + 1))) (log (tanh z / z)) := by
  have h := dlmf_4_19_9 (z := I * z) (by rwa [norm_I_mul])
  rw [← tanh_div_eq] at h
  refine h.congr_fun fun m => ?_
  rw [I_mul_pow_even, logTanhCoeff_eq]
  push_cast; ring

end Azurite.DLMF
