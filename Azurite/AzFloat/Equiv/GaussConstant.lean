/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GaussConstant
import Azurite.AzFloat.Equiv.Agm
import Azurite.AzFloat.Equiv.Constants
import Azurite.AzFloat.Equiv.Div
import Azurite.BrentZimmermann.Chapter4.BrentSalamin

/-!
# Equivalence: Gauss's constant

`gaussConstantPrecRound p mode` is `liftVal₀ (1/AGM(1, √2)) p mode` or the `NaN` fallback
(`gaussConstantPrecRound_eq_or`).  Besides the AGM enclosure, the proof keeps the lower bounds
`≥ 1` (`LowerGeOne`), so that the reciprocal `1/bLo` is a finite upper bound.  Also
`gaussConstant_eq_ellipticK`: `1/AGM(1, √2) = √2 K(1/√2)/π`.
-/

namespace Azurite.AzFloat

open Azurite.BZ RoundingTarget

theorem toVal_one' : one.toVal = some ((1 : ℝ) : EReal) := by
  rw [one, toVal_powerOf2]; simp

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
    ∃ r : ℝ, (divPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv / vv := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0]
  obtain ⟨r, hr, hle, -⟩ := roundVal_floor_spec w _
  exact ⟨r, hr, hle⟩

theorem divCeiling_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (hv0 : vv ≠ 0) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (divPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv / vv ≤ r := by
  rw [divPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.div_coe_coe uv vv hv0]
  exact roundVal_ceiling_spec w _

/-! ### Lower bounds at least one -/

/-- Both lower bounds are at least `1`. -/
def LowerGeOne (s : AgmBounds) : Prop :=
  (∃ v : ℝ, s.aLo.toVal = some (v : EReal) ∧ 1 ≤ v) ∧
    (∃ v : ℝ, s.bLo.toVal = some (v : EReal) ∧ 1 ≤ v)

theorem lowerGeOne_agmStep {s : AgmBounds} (w : ℕ) [NeZero w] (h : LowerGeOne s) :
    LowerGeOne (agmStep w s) := by
  obtain ⟨⟨al, hal, hal1⟩, ⟨bl, hbl, hbl1⟩⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr, -, hr2⟩ := addFloor_ge hal hbl w (two_mem_floatSet w) (by linarith)
    exact ⟨r / 2, toVal_half hr, by linarith⟩
  · obtain ⟨m, hm, -, hm1⟩ := mulFloor_ge hal hbl w (one_mem_floatSet w) (by nlinarith)
    obtain ⟨r, hr, -, hr1⟩ := sqrtFloor_ge hm (by linarith) w (one_mem_floatSet w)
      (by rw [Real.le_sqrt' one_pos]; linarith)
    exact ⟨r, hr, hr1⟩

theorem lowerGeOne_agmIter (w : ℕ) [NeZero w] :
    ∀ (fuel : ℕ) (s : AgmBounds), LowerGeOne s → LowerGeOne (agmIter w fuel s)
  | 0, _, h => h
  | fuel + 1, s, h => by
    rw [agmIter]
    split_ifs
    · exact h
    · exact lowerGeOne_agmIter w fuel _ (lowerGeOne_agmStep w h)

/-! ### The bracket -/

theorem sqrt_two_ne_one : Real.sqrt 2 ≠ 1 := by
  intro h
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h] at this
  norm_num at this

/-- The bracket encloses `G = 1/AGM(1, √2)`, with the lower end strictly below it. -/
theorem gaussApprox_spec (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, Rounds (gaussApprox w).1 lv ∧ Rounds (gaussApprox w).2 hv ∧
      lv ≤ (AGM 1 (Real.sqrt 2))⁻¹ ∧ (AGM 1 (Real.sqrt 2))⁻¹ ≤ hv ∧
      (lv = (AGM 1 (Real.sqrt 2))⁻¹ → hv = (AGM 1 (Real.sqrt 2))⁻¹) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs2ge : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt' one_pos]; norm_num
  have hM : 0 < AGM 1 (Real.sqrt 2) := AGM_one_pos hs2
  -- the enclosure of `√2`
  obtain ⟨v₂, hv₂, hv₂le, hv₂ge⟩ : ∃ v : ℝ, (sqrt2PrecRound w .Floor).1.toVal = some (v : EReal) ∧
      v ≤ Real.sqrt 2 ∧ 1 ≤ v := by
    rw [sqrt2PrecRound_eq_liftVal₀, liftVal₀]
    exact roundVal_floor_ge w (one_mem_floatSet w) hs2ge
  obtain ⟨v₂', hv₂', hv₂'ge⟩ : ∃ v : ℝ, (sqrt2PrecRound w .Ceiling).1.toVal = some (v : EReal) ∧
      Real.sqrt 2 ≤ v := by
    rw [sqrt2PrecRound_eq_liftVal₀, liftVal₀]
    exact roundVal_ceiling_spec w _
  have h₀ : Encloses 1 (Real.sqrt 2) 0 ⟨one, one, (sqrt2PrecRound w .Floor).1,
      (sqrt2PrecRound w .Ceiling).1⟩ :=
    encloses_init_bounds toVal_one' toVal_one' hv₂ hv₂' zero_le_one le_rfl le_rfl
      (by linarith) hv₂le hv₂'ge
  have hg₀ : LowerGeOne ⟨one, one, (sqrt2PrecRound w .Floor).1, (sqrt2PrecRound w .Ceiling).1⟩ :=
    ⟨⟨1, toVal_one', le_rfl⟩, ⟨v₂, hv₂, hv₂ge⟩⟩
  have h₁ := encloses_agmStep one_pos hs2 w h₀
  obtain ⟨m, hm, ⟨-, ⟨ah, hah, hahge⟩, ⟨bl, hbl, -, hblle⟩, -⟩⟩ :=
    encloses_agmIter one_pos hs2 w (w + 4) _ 1 h₁
  obtain ⟨-, ⟨bl', hbl', hbl'1⟩⟩ := lowerGeOne_agmIter w (w + 4) _ (lowerGeOne_agmStep w hg₀)
  have hbleq : bl' = bl := by
    have := hbl'.symm.trans hbl
    exact EReal.coe_eq_coe_iff.mp (Option.some_injective _ this)
  subst hbleq
  have hahgt : AGM 1 (Real.sqrt 2) < ah :=
    (AGM_lt_agmA one_pos hs2 sqrt_two_ne_one.symm hm).trans_le hahge
  have hblpos : 0 < bl' := by linarith
  have hblAGM : bl' ≤ AGM 1 (Real.sqrt 2) := hblle.trans (agmB_le_AGM one_pos hs2 hm)
  obtain ⟨lo, hlo, hlole⟩ := divFloor_spec toVal_one' hah (by linarith) w
  obtain ⟨hi, hhi, hhige⟩ := divCeiling_spec toVal_one' hbl' hblpos.ne' w
  have hlolt : lo < (AGM 1 (Real.sqrt 2))⁻¹ := by
    rw [one_div] at hlole
    exact hlole.trans_lt (inv_strictAnti₀ hM hahgt)
  refine ⟨lo, hi, ?_, ?_, hlolt.le, ?_, fun h => absurd h hlolt.ne⟩
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rwa [fval_of_toVal_coe hlo] at this
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rwa [fval_of_toVal_coe hhi] at this
  · rw [one_div] at hhige
    exact (inv_anti₀ hblpos hblAGM).trans hhige

/-- **Gauss's constant is correctly rounded, unless the fuel runs out.** -/
theorem gaussConstantPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gaussConstantPrecRound p mode
        = liftVal₀ (some (((AGM 1 (Real.sqrt 2))⁻¹ : ℝ) : EReal)) p mode ∨
      gaussConstantPrecRound p mode = (nan, .eq) := by
  unfold gaussConstantPrecRound liftVal₀
  rcases eq_or_ne (zivLoop gaussApprox p mode (agmFuel p) (p + zivGuardBits)) (nan, .eq)
    with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan p mode _ _ (fun w hw => by
      have : NeZero w := ⟨hw.ne'⟩
      exact gaussApprox_spec w) _ _ (by unfold zivGuardBits; omega) hz

/-- `G = 1/AGM(1, √2) = √2 K(1/√2)/π` (Gauss's theorem). -/
theorem gaussConstant_eq_ellipticK :
    (AGM 1 (Real.sqrt 2))⁻¹ = Real.sqrt 2 * ellipticK (1 / Real.sqrt 2) / Real.pi := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hb0 : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hM : 0 < AGM 1 (1 / Real.sqrt 2) := AGM_one_pos hb0
  have hAGM : AGM 1 (Real.sqrt 2) = Real.sqrt 2 * AGM 1 (1 / Real.sqrt 2) := by
    rw [AGM_comm 1 (1 / Real.sqrt 2), ← AGM_smul hs2 hb0 one_pos, mul_one,
      mul_one_div_cancel hs2.ne', AGM_comm]
  have hK := one_div_AGM_one hb0 salaminB0_lt_one.le
  rw [show Real.sqrt (1 - (1 / Real.sqrt 2) ^ 2) = 1 / Real.sqrt 2 from
    sqrt_one_sub_salaminB0_sq] at hK
  rw [hAGM, mul_inv, ← one_div (AGM 1 (1 / Real.sqrt 2)), hK]
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  rw [h2]

end Azurite.AzFloat
