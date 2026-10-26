/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBaseM1
import Azurite.AzFloat.Equiv.PowBase

/-!
# Equivalence: `u^x − 1` for a natural base

* `Spec.powBaseM1 u`: `Spec.powBase u` followed by the subtraction of `1`.
* `powBaseM1PrecRound_eq_liftVal :
  powBaseM1PrecRound u x p mode = liftVal (Spec.powBaseM1 u) x p mode`: `u^x − 1` is correctly
  rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

/-- Extended-real `u^a − 1`: `powBase u a` followed by the subtraction of `1`. -/
noncomputable def powBaseM1 (u : ℕ) (a : EReal) : Option EReal :=
  (powBase u a).map fun b => b - 1

theorem powBaseM1_coe (u : ℕ) (r : ℝ) :
    powBaseM1 u (r : EReal)
      = if u = 0 ∧ r < 0 then some ⊤ else some (((u : ℝ) ^ r - 1 : ℝ) : EReal) := by
  unfold powBaseM1
  rw [powBase_coe]
  split_ifs
  · rw [Option.map_some, ← EReal.coe_one, EReal.top_sub_coe]
  · rw [Option.map_some, ← EReal.coe_one, ← EReal.coe_sub]

@[simp] theorem powBaseM1_top (u : ℕ) :
    powBaseM1 u ⊤ = if u = 0 then some ((-1 : ℝ) : EReal) else if u = 1 then none
      else some ⊤ := by
  unfold powBaseM1
  rw [powBase_top]
  split_ifs <;> simp [← EReal.coe_one, ← EReal.coe_neg]

@[simp] theorem powBaseM1_bot (u : ℕ) :
    powBaseM1 u ⊥ = if u = 0 then some ⊤ else if u = 1 then none
      else some ((-1 : ℝ) : EReal) := by
  unfold powBaseM1
  rw [powBase_bot]
  split_ifs <;> simp [← EReal.coe_one, ← EReal.coe_neg]

end Spec

/-- `negOneRound` is the rounding of `−1`. -/
theorem negOneRound_eq (p : ℕ) [NeZero p] (mode : RoundingMode) :
    negOneRound p mode = roundVal p mode (some ((-1 : ℝ) : EReal)) := by
  unfold negOneRound
  have h1 : (-one).toVal = some ((-1 : ℝ) : EReal) := by
    rw [toVal_neg, toVal_one', Option.map_some, EReal.coe_neg]
  rw [ite_eq_right (NeZero.ne p), setPrecRound_eq_roundVal h1]

/-- **`u^x − 1` is correctly rounded.** -/
theorem powBaseM1PrecRound_eq_liftVal (u : UInt64) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    powBaseM1PrecRound u x p mode = liftVal (Spec.powBaseM1 u.toNat) x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;> by_cases h0 : u.toNat = 0 <;> by_cases h1 : u.toNat = 1 <;>
      simp [powBaseM1PrecRound, negOneRound_eq, h0, h1]
  | zero =>
    simp only [powBaseM1PrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.powBaseM1_coe, ite_eq_right (fun h => lt_irrefl _ h.2),
      Real.rpow_zero, sub_self, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [powBaseM1PrecRound, toVal_finite, Option.bind_some, Spec.powBaseM1_coe]
    by_cases h0 : u.toNat = 0
    · rw [dite_eq_left h0]
      cases s
      · have hneg : finiteVal false e m < 0 := by
          rw [finiteVal_false]; linarith [finiteVal_true_pos e hv]
        simp [h0, hneg]
      · have hpos := finiteVal_true_pos e hv
        simp [h0, not_lt.mpr hpos.le, Real.zero_rpow hpos.ne', negOneRound_eq]
    rw [dite_eq_right h0, ite_eq_right (fun h => h0 h.1)]
    by_cases h1 : u.toNat = 1
    · rw [dite_eq_left h1, h1, Nat.cast_one, Real.one_rpow, sub_self, EReal.coe_zero,
        roundVal_zero]
    · rw [dite_eq_right h1, dite_eq_right (NeZero.ne p)]
      have hu2 : 2 ≤ (AzNat.ofNat u.toNat).toNat := by rw [AzNat.toNat_ofNat]; omega
      split
      · rename_i r n hx
        obtain ⟨hr, hval⟩ := powBaseExact?_some _ _ hu2 (toVal_finite s e q m hv) hx
        rw [AzNat.toNat_ofNat] at hval
        obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec (AzNat.ofNat u.toNat) hu2
        rw [← hr] at hc2
        have hrR : (0 : ℝ) < (r.toNat : ℝ) ^ n.abs.toNat := by positivity
        rw [hval, toInt_eq_of_sign]
        split_ifs with hs
        · rw [zpow_natCast, subPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzNat, toVal_one',
            Option.bind_some, Option.bind_some, Spec.sub, ← EReal.coe_neg, Spec.add_coe_coe,
            AzNat.toNat_pow, Nat.cast_pow, sub_eq_add_neg]
        · rw [zpow_neg, zpow_natCast, divPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzInt,
            toVal_ofAzNat, Option.bind_some, Option.bind_some, AzNat.toNat_pow, Nat.cast_pow,
            Spec.div_coe_coe _ _ hrR.ne', AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_pow]
          have h1' : ((1 : AzInt)).toInt = 1 := rfl
          rw [h1']
          have hval' : ((1 - (r.toNat ^ n.abs.toNat : ℕ) : ℤ) : ℝ) / (r.toNat : ℝ) ^ n.abs.toNat
              = ((r.toNat : ℝ) ^ n.abs.toNat)⁻¹ - 1 := by
            push_cast
            field_simp
          rw [hval']
      · rename_i hx
        exact zivLoopCertified_eq_threshold p mode _ ((u.toNat : ℝ) ^ finiteVal s e m - 1) _
          (by unfold powBaseM1Start zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := powBaseM1Approx_spec (w := w) s e hv u
              (by omega)
              (AzNat.toNat_ofNat u.toNat ▸
                irrational_sub_one_of_powBaseExact?_none s e hv (AzNat.ofNat u.toNat) hu2
                  (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
              (by unfold powBaseM1Start at hw; omega)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
