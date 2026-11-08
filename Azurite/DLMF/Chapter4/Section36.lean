/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section22
import Azurite.DLMF.Chapter4.Section28

/-!
# DLMF §4.36 Infinite Products and Partial Fractions (hyperbolic functions)

"Replace `z` by `iz` in §4.22": each formula is the corresponding §4.22 one at `w = iz`
(4.28.8–4.28.13). As in §4.22, products and sums over `n ≥ 1` are indexed by `n + 1`, and odd
numbers `2n − 1` by `2n + 1`, `n ≥ 0`.

* 4.36.1: `dlmf_4_36_1` (partial products converge for all `z`, multipliable, `sinh z = z ∏'`).
* 4.36.2: `dlmf_4_36_2` (all `z`).
* 4.36.3–4.36.5 (`z ≠ nπi`): `dlmf_4_36_3`, `dlmf_4_36_4` (sum over `n ∈ ℤ`), `dlmf_4_36_5`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

theorem I_mul_sq_eq (z : ℂ) : (I * z) ^ 2 = -z ^ 2 := by rw [mul_pow, I_sq]; ring

/-- **DLMF 4.36.1**: `sinh z = z ∏_{n≥1} (1 + z²/(n²π²))`. -/
theorem dlmf_4_36_1 (z : ℂ) :
    Tendsto (fun N : ℕ => z * ∏ n ∈ Finset.range N, (1 + z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)))
        atTop (𝓝 (sinh z)) ∧
      Multipliable (fun n : ℕ => 1 + z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)) ∧
      sinh z = z * ∏' n : ℕ, (1 + z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2)) := by
  obtain ⟨hT, hM, hE⟩ := dlmf_4_22_1 (I * z)
  have hterm : ∀ n : ℕ, 1 - (I * z) ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2) =
      1 + z ^ 2 / (((n : ℂ) + 1) ^ 2 * π ^ 2) := fun n => by rw [I_mul_sq_eq]; ring
  simp only [hterm] at hT hM hE
  have hs : sinh z = -I * sin (I * z) := by
    rw [dlmf_4_28_8, ← mul_assoc, neg_mul, I_mul_I]; ring
  refine ⟨?_, hM, ?_⟩
  · rw [hs]
    refine (hT.const_mul (-I)).congr fun N => ?_
    rw [← mul_assoc, ← mul_assoc, neg_mul, I_mul_I]; ring
  · rw [hs, hE, ← mul_assoc, ← mul_assoc, neg_mul, I_mul_I]; ring

/-- **DLMF 4.36.2**: `cosh z = ∏_{n≥1} (1 + 4z²/((2n − 1)²π²))`. -/
theorem dlmf_4_36_2 (z : ℂ) :
    HasProd (fun n : ℕ => 1 + 4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)) (cosh z) := by
  have h := dlmf_4_22_2 (I * z)
  rw [dlmf_4_28_9] at h
  have e : (fun n : ℕ => 1 - 4 * (I * z) ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2)) =
      fun n : ℕ => 1 + 4 * z ^ 2 / ((2 * (n : ℂ) + 1) ^ 2 * π ^ 2) := by
    funext n; rw [I_mul_sq_eq]; ring
  rwa [e] at h

/-- `z ≠ nπi` for all `n` gives `iz ≠ nπ` for all `n`. -/
theorem I_mul_ne_int_mul_pi {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π * I) :
    ∀ n : ℤ, I * z ≠ n * π := fun n h => by
  apply hz (-n)
  have : z = -I * (I * z) := by rw [← mul_assoc, neg_mul, I_mul_I]; ring
  rw [this, h]; push_cast; ring

/-- **DLMF 4.36.3**: `coth z = 1/z + 2z ∑_{n≥1} 1/(z² + n²π²)`, `z ≠ nπi`. -/
theorem dlmf_4_36_3 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π * I) :
    HasSum (fun n : ℕ => 1 / (z ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2)) ((cothC z - 1 / z) / (2 * z)) ∧
      cothC z = 1 / z + 2 * z * ∑' n : ℕ, 1 / (z ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2) := by
  have hz0 : z ≠ 0 := fun h => hz 0 (by simp [h])
  obtain ⟨h, -⟩ := dlmf_4_22_3 (I_mul_ne_int_mul_pi hz)
  have hS : HasSum (fun n : ℕ => 1 / (z ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2))
      ((cothC z - 1 / z) / (2 * z)) := by
    have h' := h.neg
    have hval : -((cot (I * z) - 1 / (I * z)) / (2 * (I * z))) = (cothC z - 1 / z) / (2 * z) := by
      rw [dlmf_4_28_13]
      field_simp
      ring_nf
      rw [I_sq]
      ring
    rw [hval] at h'
    refine h'.congr_fun fun n => ?_
    rw [I_mul_sq_eq, show -z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2 =
      -(z ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2) by ring, one_div_neg_eq_neg_one_div, neg_neg]
  refine ⟨hS, ?_⟩
  rw [hS.tsum_eq]
  field_simp
  ring

/-- **DLMF 4.36.4**: `csch² z = ∑_{n=−∞}^{∞} 1/(z − nπi)²`, `z ≠ nπi`. -/
theorem dlmf_4_36_4 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π * I) :
    HasSum (fun n : ℤ => 1 / (z - n * π * I) ^ 2) (cschC z ^ 2) := by
  have h := (dlmf_4_22_4 (I_mul_ne_int_mul_pi hz)).neg
  have hcsc : cscC (I * z) ^ 2 = -cschC z ^ 2 := by
    rw [dlmf_4_28_11, mul_pow, neg_sq, I_sq]; ring
  rw [hcsc, neg_neg] at h
  have h2 := (Equiv.neg ℤ).hasSum_iff.mpr h
  refine h2.congr_fun fun n => ?_
  simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
  have e : (I * z - -(n : ℂ) * π) ^ 2 = -(z - n * π * I) ^ 2 := by
    linear_combination (z ^ 2 + (n : ℂ) ^ 2 * π ^ 2) * I_sq
  rw [e, one_div_neg_eq_neg_one_div, neg_neg]

/-- **DLMF 4.36.5**: `csch z = 1/z + 2z ∑_{n≥1} (−1)ⁿ/(z² + n²π²)`, `z ≠ nπi`. -/
theorem dlmf_4_36_5 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n * π * I) :
    ∃ T : ℂ, HasSum (fun n : ℕ => (-1) ^ (n + 1) / (z ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2)) T ∧
      cschC z = 1 / z + 2 * z * T := by
  have hz0 : z ≠ 0 := fun h => hz 0 (by simp [h])
  obtain ⟨T, hT, hc⟩ := dlmf_4_22_5 (I_mul_ne_int_mul_pi hz)
  refine ⟨-T, hT.neg.congr_fun fun n => ?_, ?_⟩
  · rw [I_mul_sq_eq, show -z ^ 2 - ((n : ℂ) + 1) ^ 2 * π ^ 2 =
      -(z ^ 2 + ((n : ℂ) + 1) ^ 2 * π ^ 2) by ring, div_neg, neg_neg]
  · have h1 : cschC z = I * cscC (I * z) := by
      rw [dlmf_4_28_11, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
    rw [h1, hc]
    field_simp
    ring_nf
    rw [I_sq]
    ring

end Azurite.DLMF
