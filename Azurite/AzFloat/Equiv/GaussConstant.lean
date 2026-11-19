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
import Azurite.AzFloat.Equiv.FloorGe
import Azurite.BrentZimmermann.Chapter4.BrentSalamin

/-!
# Equivalence: Gauss's constant

`gaussConstantPrecRound p mode` is `liftVal₀ (1/AGM(1, √2)) p mode`, unconditionally
(**`gaussConstantPrecRound_eq_liftVal₀`**: the constant is irrational by Chudnovsky's theorem and
the Ziv loop has a termination certificate, `Equiv/AgmConstants.lean`).  Besides the AGM enclosure, the proof keeps the lower bounds
`≥ 1` (`LowerGeOne`), so that the reciprocal `1/bLo` is a finite upper bound.  Also
`gaussConstant_eq_ellipticK`: `1/AGM(1, √2) = √2 K(1/√2)/π`.
-/

namespace Azurite.AzFloat

open Azurite.BZ RoundingTarget

variable {u v : AzFloat} {uv vv : ℝ}

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

/-- The bracket encloses `G = 1/AGM(1, √2)`, with the lower end nonnegative and strictly
below it. -/
theorem gaussBracket_spec (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, (gaussBracket w).1.toVal = some (lv : EReal) ∧
      (gaussBracket w).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv < (AGM 1 (Real.sqrt 2))⁻¹ ∧ (AGM 1 (Real.sqrt 2))⁻¹ ≤ hv := by
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
  obtain ⟨lo, hlo, hlole, hlo0⟩ := divFloor_spec toVal_one' hah (by linarith) w
  obtain ⟨hi, hhi, hhige⟩ := divCeiling_spec toVal_one' hbl' hblpos.ne' w
  have hlolt : lo < (AGM 1 (Real.sqrt 2))⁻¹ := by
    rw [one_div] at hlole
    exact hlole.trans_lt (inv_strictAnti₀ hM hahgt)
  refine ⟨lo, hi, hlo, hhi, hlo0 (div_nonneg zero_le_one (by linarith)), hlolt, ?_⟩
  rw [one_div] at hhige
  exact (inv_anti₀ hblpos hblAGM).trans hhige

/-- The bracket encloses `G = 1/AGM(1, √2)`, with the lower end strictly below it. -/
theorem gaussApprox_spec (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, Rounds (gaussApprox w).1 lv ∧ Rounds (gaussApprox w).2 hv ∧
      lv ≤ (AGM 1 (Real.sqrt 2))⁻¹ ∧ (AGM 1 (Real.sqrt 2))⁻¹ ≤ hv ∧
      (lv = (AGM 1 (Real.sqrt 2))⁻¹ → hv = (AGM 1 (Real.sqrt 2))⁻¹) := by
  obtain ⟨lo, hi, hlo, hhi, -, hlolt, hGhi⟩ := gaussBracket_spec w
  refine ⟨lo, hi, ?_, ?_, hlolt.le, hGhi, fun h => absurd h hlolt.ne⟩
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rwa [fval_of_toVal_coe hlo] at this
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rwa [fval_of_toVal_coe hhi] at this

/-- **Gauss's constant is correctly rounded**: it is irrational (`irrational_gauss`,
Chudnovsky's theorem) and the Ziv loop has a termination certificate. -/
theorem gaussConstantPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gaussConstantPrecRound p mode
      = liftVal₀ (some (((AGM 1 (Real.sqrt 2))⁻¹ : ℝ) : EReal)) p mode := by
  unfold gaussConstantPrecRound liftVal₀
  rw [dite_eq_right (NeZero.ne p)]
  exact zivLoopBacked_eq p mode gaussApprox (not_mem_floatSet_of_irrational p irrational_gauss)
    1 (fun w hw => Or.inl (by
      have : NeZero w := ⟨by omega⟩
      obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ := gaussApprox_spec w
      exact ⟨lv, hv, h1, h2, h3, h4⟩))
    _ _ (by unfold zivGuardBits; omega) (by unfold zivGuardBits; omega) _

/-- Gauss's constant is correctly rounded (the weaker form, kept for its users). -/
theorem gaussConstantPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gaussConstantPrecRound p mode
        = liftVal₀ (some (((AGM 1 (Real.sqrt 2))⁻¹ : ℝ) : EReal)) p mode ∨
      gaussConstantPrecRound p mode = (nan, .eq) :=
  Or.inl (gaussConstantPrecRound_eq_liftVal₀ p mode)

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
