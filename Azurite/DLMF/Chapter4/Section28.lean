/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section14

/-!
# DLMF §4.28 Definitions and Periodicity (hyperbolic functions)

* 4.28.1–4.28.3: `dlmf_4_28_1`, `dlmf_4_28_2`, `dlmf_4_28_3` (Mathlib's `Complex.sinh`,
  `Complex.cosh`).
* 4.28.4–4.28.7: `dlmf_4_28_4` (`Complex.tanh`), `cschC`/`dlmf_4_28_5`, `sechC`/`dlmf_4_28_6`,
  `cothC`/`dlmf_4_28_7` (defined here, as DLMF does, from `sinh`, `cosh`, `tanh`).
* 4.28.8–4.28.13: relations to the trigonometric functions (`cscC`, `secC` of §4.14). They hold
  for every `z`, including the poles, where both sides are Lean's junk value `0`.
* Periodicity and zeros: `dlmf_4_28_sinh_periodic`, `dlmf_4_28_cosh_periodic`,
  `dlmf_4_28_tanh_periodic` (and the `k`-fold versions), `dlmf_4_28_sinh_zeros`,
  `dlmf_4_28_cosh_zeros`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 4.28.1**: `sinh z = (e^z − e^{−z})/2`. -/
theorem dlmf_4_28_1 (z : ℂ) : sinh z = (exp z - exp (-z)) / 2 := rfl

/-- **DLMF 4.28.2**: `cosh z = (e^z + e^{−z})/2`. -/
theorem dlmf_4_28_2 (z : ℂ) : cosh z = (exp z + exp (-z)) / 2 := rfl

/-- **DLMF 4.28.3**: `cosh z ± sinh z = e^{±z}`. -/
theorem dlmf_4_28_3 (z : ℂ) : cosh z + sinh z = exp z ∧ cosh z - sinh z = exp (-z) :=
  ⟨cosh_add_sinh z, cosh_sub_sinh z⟩

/-- **DLMF 4.28.4**: `tanh z = sinh z/cosh z`. -/
theorem dlmf_4_28_4 (z : ℂ) : tanh z = sinh z / cosh z := tanh_eq_sinh_div_cosh z

/-- **DLMF 4.28.5**: `csch z = 1/sinh z`. -/
noncomputable def cschC (z : ℂ) : ℂ := 1 / sinh z

/-- **DLMF 4.28.6**: `sech z = 1/cosh z`. -/
noncomputable def sechC (z : ℂ) : ℂ := 1 / cosh z

/-- **DLMF 4.28.7**: `coth z = 1/tanh z`. -/
noncomputable def cothC (z : ℂ) : ℂ := 1 / tanh z

theorem dlmf_4_28_5 (z : ℂ) : cschC z = 1 / sinh z := rfl

theorem dlmf_4_28_6 (z : ℂ) : sechC z = 1 / cosh z := rfl

theorem dlmf_4_28_7 (z : ℂ) : cothC z = 1 / tanh z := rfl

theorem cothC_eq_cosh_div_sinh (z : ℂ) : cothC z = cosh z / sinh z := by
  rw [cothC, tanh_eq_sinh_div_cosh, one_div_div]

/-! ### Relations to trigonometric functions -/

/-- **DLMF 4.28.8**: `sin(iz) = i sinh z`. -/
theorem dlmf_4_28_8 (z : ℂ) : sin (I * z) = I * sinh z := by
  rw [mul_comm, sin_mul_I, mul_comm]

/-- **DLMF 4.28.9**: `cos(iz) = cosh z`. -/
theorem dlmf_4_28_9 (z : ℂ) : cos (I * z) = cosh z := by
  rw [mul_comm, cos_mul_I]

/-- **DLMF 4.28.10**: `tan(iz) = i tanh z`. -/
theorem dlmf_4_28_10 (z : ℂ) : tan (I * z) = I * tanh z := by
  rw [mul_comm, tan_mul_I, mul_comm]

/-- **DLMF 4.28.11**: `csc(iz) = −i csch z`. -/
theorem dlmf_4_28_11 (z : ℂ) : cscC (I * z) = -I * cschC z := by
  rw [cscC, cschC, dlmf_4_28_8]
  rcases eq_or_ne (sinh z) 0 with h | h
  · simp [h]
  field_simp
  rw [I_sq]
  ring

/-- **DLMF 4.28.12**: `sec(iz) = sech z`. -/
theorem dlmf_4_28_12 (z : ℂ) : secC (I * z) = sechC z := by
  rw [secC, sechC, dlmf_4_28_9]

/-- **DLMF 4.28.13**: `cot(iz) = −i coth z`. -/
theorem dlmf_4_28_13 (z : ℂ) : cot (I * z) = -I * cothC z := by
  rw [cot_eq_cos_div_sin, cothC_eq_cosh_div_sinh, dlmf_4_28_8, dlmf_4_28_9]
  rcases eq_or_ne (sinh z) 0 with h | h
  · simp [h]
  field_simp
  rw [I_sq]
  ring

/-! ### Periodicity and zeros -/

/-- `sinh z = −i sin(iz)`. -/
theorem sinh_eq_neg_I_mul_sin (z : ℂ) : sinh z = -I * sin (I * z) := by
  rw [dlmf_4_28_8, ← mul_assoc, show -I * I = 1 by rw [neg_mul, ← sq, I_sq]; ring, one_mul]

/-- `tanh z = −i tan(iz)`. -/
theorem tanh_eq_neg_I_mul_tan (z : ℂ) : tanh z = -I * tan (I * z) := by
  rw [dlmf_4_28_10, ← mul_assoc, show -I * I = 1 by rw [neg_mul, ← sq, I_sq]; ring, one_mul]

/-- **DLMF §4.28**: `sinh` has period `2πi`. -/
theorem dlmf_4_28_sinh_periodic : Function.Periodic sinh (2 * π * I) := fun z => by
  rw [sinh_eq_neg_I_mul_sin, sinh_eq_neg_I_mul_sin, mul_add,
    show I * (2 * π * I) = -(2 * π) by rw [mul_comm, mul_assoc, I_mul_I]; ring, ← sub_eq_add_neg,
    sin_sub_two_pi]

/-- **DLMF §4.28**: `cosh` has period `2πi`. -/
theorem dlmf_4_28_cosh_periodic : Function.Periodic cosh (2 * π * I) := fun z => by
  rw [← dlmf_4_28_9, ← dlmf_4_28_9, mul_add,
    show I * (2 * π * I) = -(2 * π) by rw [mul_comm, mul_assoc, I_mul_I]; ring, ← sub_eq_add_neg,
    cos_sub_two_pi]

/-- **DLMF §4.28**: `tanh` has period `πi`. -/
theorem dlmf_4_28_tanh_periodic : Function.Periodic tanh (π * I) := fun z => by
  rw [tanh_eq_neg_I_mul_tan, tanh_eq_neg_I_mul_tan, mul_add,
    show I * (π * I) = -π by rw [mul_comm, mul_assoc, I_mul_I]; ring, ← sub_eq_add_neg,
    tan_periodic.sub_eq]

/-- `sinh(z + 2kπi) = sinh z`, `cosh(z + 2kπi) = cosh z`, `tanh(z + kπi) = tanh z`. -/
theorem dlmf_4_28_periodic_int (z : ℂ) (k : ℤ) :
    sinh (z + k * (2 * π * I)) = sinh z ∧ cosh (z + k * (2 * π * I)) = cosh z ∧
      tanh (z + k * (π * I)) = tanh z :=
  ⟨dlmf_4_28_sinh_periodic.int_mul k z, dlmf_4_28_cosh_periodic.int_mul k z,
    dlmf_4_28_tanh_periodic.int_mul k z⟩

/-- **DLMF §4.28**: the zeros of `sinh` are `ikπ`, `k ∈ ℤ`. -/
theorem dlmf_4_28_sinh_zeros (z : ℂ) : sinh z = 0 ↔ ∃ k : ℤ, z = I * (k * π) := by
  rw [sinh_eq_neg_I_mul_sin, mul_eq_zero, or_iff_right (neg_ne_zero.mpr I_ne_zero),
    sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have : z = -I * (I * z) := by rw [← mul_assoc, neg_mul, I_mul_I]; ring
    rw [this, hk]; push_cast; ring
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    rw [← mul_assoc, I_mul_I]; push_cast; ring

/-- **DLMF §4.28**: the zeros of `cosh` are `i(k + ½)π`, `k ∈ ℤ`. -/
theorem dlmf_4_28_cosh_zeros (z : ℂ) : cosh z = 0 ↔ ∃ k : ℤ, z = I * ((k + 1 / 2) * π) := by
  rw [← dlmf_4_28_9, dlmf_4_14_cos_zeros]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k - 1, ?_⟩
    have : z = -I * (I * z) := by rw [← mul_assoc, neg_mul, I_mul_I]; ring
    rw [this, hk]; push_cast; ring
  · rintro ⟨k, rfl⟩
    refine ⟨-k - 1, ?_⟩
    rw [← mul_assoc, I_mul_I]; push_cast; ring

end Azurite.DLMF
