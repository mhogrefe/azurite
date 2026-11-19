/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Div
import Azurite.AzFloat.Equiv.Agm
import Azurite.AzFloat.Equiv.Constants
import Azurite.AzFloat.Equiv.Div
import Azurite.BrentZimmermann.Chapter4.BrentSalamin

/-!
# Directed rounding above a float

Rounding down a real `r ≥ c`, where `c` is itself a float of the working precision, gives a
float in `[c, r]` (`roundVal_floor_ge`), with the instances for the sum, the product and the
square root (`addFloor_ge`, `mulFloor_ge`, `sqrtFloor_ge`), and the directed quotients
(`divFloor_spec`, `divCeiling_spec`).
-/

namespace Azurite.AzFloat

open Azurite.BZ RoundingTarget

theorem one_mem_floatSet (w : ℕ) [NeZero w] : ((1 : ℝ) : EReal) ∈ floatSet w := by
  have := mem_floatSet_mul_zpow w 1 0 (by rw [abs_one]; exact_mod_cast Nat.one_le_two_pow)
  simpa using this

theorem two_mem_floatSet (w : ℕ) [NeZero w] : ((2 : ℝ) : EReal) ∈ floatSet w := by
  have h : |(2 : ℤ)| ≤ 2 ^ w := by
    rw [abs_two]; exact_mod_cast Nat.pow_le_pow_right two_pos (NeZero.one_le)
  have := mem_floatSet_mul_zpow w 2 0 h
  simpa using this

/-- Rounding down a real `≥ c`, with `c` a float, gives a real in `[c, r]`. -/
theorem roundVal_floor_ge (w : ℕ) [NeZero w] {c r : ℝ} (hc : ((c : ℝ) : EReal) ∈ floatSet w)
    (hcr : c ≤ r) :
    ∃ v : ℝ, (roundVal w .Floor (some (r : EReal))).1.toVal = some (v : EReal) ∧ v ≤ r ∧ c ≤ v := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, ((v : ℝ) : EReal) = (roundFloor (floatSet w) r).val := by
    rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [(roundVal_coe w .Floor r).1]; exact congrArg some hv.symm
  · have := (isGreatest_roundFloor (floatSet w) r).1.2
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this
  · have := (isGreatest_roundFloor (floatSet w) r).2 ⟨hc, EReal.coe_le_coe_iff.mpr hcr⟩
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this

variable {u v : AzFloat} {uv vv : ℝ}

theorem addFloor_ge (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] {c : ℝ} (hc : ((c : ℝ) : EReal) ∈ floatSet w) (h : c ≤ uv + vv) :
    ∃ r : ℝ, (addPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv + vv ∧ c ≤ r := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_floor_ge w hc h

theorem mulFloor_ge (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] {c : ℝ} (hc : ((c : ℝ) : EReal) ∈ floatSet w) (h : c ≤ uv * vv) :
    ∃ r : ℝ, (mulPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv * vv ∧ c ≤ r := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_floor_ge w hc h

theorem sqrtFloor_ge (hu : u.toVal = some (uv : EReal)) (h0 : 0 ≤ uv) (w : ℕ) [NeZero w]
    {c : ℝ} (hc : ((c : ℝ) : EReal) ∈ floatSet w) (h : c ≤ Real.sqrt uv) :
    ∃ r : ℝ, (sqrtPrecRound u w .Floor).1.toVal = some (r : EReal) ∧ r ≤ Real.sqrt uv ∧ c ≤ r := by
  rw [sqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.sqrt_coe uv h0]
  exact roundVal_floor_ge w hc h

theorem divFloor_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : vv ≠ 0) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv / vv ∧
      (0 ≤ uv / vv → 0 ≤ r) := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0]
  exact roundVal_floor_spec w _

theorem divCeiling_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : vv ≠ 0) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv / vv ≤ r := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0]
  exact roundVal_ceiling_spec w _

end Azurite.AzFloat
