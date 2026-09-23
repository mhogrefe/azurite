/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Int
import Azurite.Rounding.NatDivPow
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Bridge between `natBotSet` and `intSet` rounding

For nonnegative reals, `(round natBotSet mode x).val = (round intSet mode x).val`
as elements of `EReal`. Both targets agree pointwise on the ⌊·⌋ and ⌈·⌉ values
(via `Int.natCast_floor_eq_floor` and `Int.natCast_ceil_eq_ceil`), and both
tiebreakers prefer the even integer at midpoints — adjacent integers always
have different parity, so this resolves uniquely and consistently.

This bridge lets results proved against `natBotSet` (e.g. `AzNat.shiftRightRound`)
extend to `intSet` for nonnegative inputs without re-running the case analysis.
-/

namespace Azurite
open RoundingTarget

/-- Floor agrees on `natBotSet` and `intSet` for `x ≥ 0`. -/
lemma val_roundFloor_natBotSet_eq_intSet (x : ℝ) (hx : 0 ≤ x) :
    (roundFloor natBotSet x).val = (roundFloor intSet x).val := by
  rw [roundFloor_natBotSet_nonneg x hx, val_roundFloor_intSet]
  have h : ((⌊x⌋₊ : ℤ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.natCast_floor_eq_floor hx
  push_cast at h
  rw [h]

/-- Ceiling agrees on `natBotSet` and `intSet` for `x ≥ 0`. -/
lemma val_roundCeiling_natBotSet_eq_intSet (x : ℝ) (hx : 0 ≤ x) :
    (roundCeiling natBotSet x).val = (roundCeiling intSet x).val := by
  rw [roundCeiling_natBotSet, val_roundCeiling_intSet]
  have h : ((⌈x⌉₊ : ℤ) : ℝ) = ((⌈x⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.natCast_ceil_eq_ceil hx
  push_cast at h
  rw [h]

/-- Tiebreaker agreement: at adjacent integers (consecutive nats viewed in `intSet`),
the natBot and int tiebreakers agree on value. -/
private lemma natBot_int_tiebreak_value_agree {x : ℝ} (hx : 0 ≤ x)
    (Fn : ↥natBotSet) (Cn : ↥natBotSet) (Fi : ↥intSet) (Ci : ↥intSet)
    (hFn_val : Fn.val = ((⌊x⌋ : ℝ) : EReal))
    (hCn_val : Cn.val = ((⌈x⌉ : ℝ) : EReal))
    (hFi_val : Fi.val = ((⌊x⌋ : ℝ) : EReal))
    (hCi_val : Ci.val = ((⌈x⌉ : ℝ) : EReal)) :
    (RoundingTarget.tiebreak Fn Cn).val = (RoundingTarget.tiebreak Fi Ci).val := by
  -- Compute toInt and natBotToNat values.
  have hFi_int : toInt Fi = ⌊x⌋ := toInt_eq_of_val hFi_val.symm
  have hCi_int : toInt Ci = ⌈x⌉ := toInt_eq_of_val hCi_val.symm
  have hxc : 0 ≤ ⌈x⌉ := Int.ceil_nonneg hx
  have hxf : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have hF_nat_val : Fn.val = ((⌊x⌋.toNat : ℝ) : EReal) := by
    rw [hFn_val]
    have : ((⌊x⌋.toNat : ℤ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hxf
    push_cast at this; rw [this]
  have hC_nat_val : Cn.val = ((⌈x⌉.toNat : ℝ) : EReal) := by
    rw [hCn_val]
    have : ((⌈x⌉.toNat : ℤ) : ℝ) = ((⌈x⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hxc
    push_cast at this; rw [this]
  have hFn_natBot : natBotToNat Fn = ⌊x⌋.toNat :=
    natBotToNat_eq_of_nat_val ⌊x⌋.toNat Fn hF_nat_val
  have hCn_natBot : natBotToNat Cn = ⌈x⌉.toNat :=
    natBotToNat_eq_of_nat_val ⌈x⌉.toNat Cn hC_nat_val
  -- Parity equivalences.
  have hF_parity : Even (natBotToNat Fn) ↔ Even (toInt Fi) := by
    rw [hFn_natBot, hFi_int]
    rw [← Int.even_coe_nat ⌊x⌋.toNat, Int.toNat_of_nonneg hxf]
  have hC_parity : Even (natBotToNat Cn) ↔ Even (toInt Ci) := by
    rw [hCn_natBot, hCi_int]
    rw [← Int.even_coe_nat ⌈x⌉.toNat, Int.toNat_of_nonneg hxc]
  show (natBotTiebreak Fn Cn).val = (intTiebreak Fi Ci).val
  unfold natBotTiebreak intTiebreak
  by_cases hFE : Even (toInt Fi)
  · by_cases hCE : Even (toInt Ci)
    · -- Both even: only possible when ⌊x⌋ = ⌈x⌉ (x ∈ ℤ).
      have hFC_eq : ⌊x⌋ = ⌈x⌉ := by
        have hf_le_c : ⌊x⌋ ≤ ⌈x⌉ := Int.floor_le_ceil x
        rcases lt_or_eq_of_le hf_le_c with hlt | heq
        · have hle1 : ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
          have hsucc : ⌈x⌉ = ⌊x⌋ + 1 := by omega
          have hCnotE : ¬ Even (toInt Ci) := by
            rw [hCi_int, hsucc, Int.even_add_one]; exact not_not.mpr (hFi_int ▸ hFE)
          exact absurd hCE hCnotE
        · exact heq
      rw [ite_eq_left (hF_parity.mpr hFE)]
      have h1 : ¬ (Even (toInt Fi) ∧ ¬ Even (toInt Ci)) := fun ⟨_, h⟩ => h hCE
      have h2 : ¬ (Even (toInt Ci) ∧ ¬ Even (toInt Fi)) := fun ⟨_, h⟩ => h hFE
      rw [ite_eq_right h1, ite_eq_right h2]
      have h_int_eq : toInt Fi = toInt Ci := by rw [hFi_int, hCi_int, hFC_eq]
      have h3 : ¬ (toInt Fi).natAbs < (toInt Ci).natAbs := by
        rw [h_int_eq]; exact lt_irrefl _
      have h4 : ¬ (toInt Ci).natAbs < (toInt Fi).natAbs := by
        rw [h_int_eq]; exact lt_irrefl _
      rw [ite_eq_right h3, ite_eq_right h4]
      rw [hFn_val, hFi_val]
    · -- Fi even, Ci not even: int branch 1 fires (returns Fi).
      rw [ite_eq_left (hF_parity.mpr hFE)]
      rw [ite_eq_left ⟨hFE, hCE⟩]
      rw [hFn_val, hFi_val]
  · by_cases hCE : Even (toInt Ci)
    · -- Fi not even, Ci even: int branch 2 fires (returns Ci).
      have hFn_not : ¬ Even (natBotToNat Fn) := fun h => hFE (hF_parity.mp h)
      rw [ite_eq_right hFn_not, ite_eq_left (hC_parity.mpr hCE)]
      have h1 : ¬ (Even (toInt Fi) ∧ ¬ Even (toInt Ci)) := fun ⟨h, _⟩ => hFE h
      rw [ite_eq_right h1, ite_eq_left ⟨hCE, hFE⟩]
      rw [hCn_val, hCi_val]
    · -- Both not even: only possible when ⌊x⌋ = ⌈x⌉ (else parities differ).
      have hFC_eq : ⌊x⌋ = ⌈x⌉ := by
        have hf_le_c : ⌊x⌋ ≤ ⌈x⌉ := Int.floor_le_ceil x
        rcases lt_or_eq_of_le hf_le_c with hlt | heq
        · have hle1 : ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
          have hsucc : ⌈x⌉ = ⌊x⌋ + 1 := by omega
          have hCE' : Even (toInt Ci) := by
            rw [hCi_int, hsucc, Int.even_add_one]; exact hFi_int ▸ hFE
          exact absurd hCE' hCE
        · exact heq
      have hFn_not : ¬ Even (natBotToNat Fn) := fun h => hFE (hF_parity.mp h)
      have hCn_not : ¬ Even (natBotToNat Cn) := fun h => hCE (hC_parity.mp h)
      rw [ite_eq_right hFn_not, ite_eq_right hCn_not]
      have h1 : ¬ (Even (toInt Fi) ∧ ¬ Even (toInt Ci)) := fun ⟨h, _⟩ => hFE h
      have h2 : ¬ (Even (toInt Ci) ∧ ¬ Even (toInt Fi)) := fun ⟨h, _⟩ => hCE h
      rw [ite_eq_right h1, ite_eq_right h2]
      have h_int_eq : toInt Fi = toInt Ci := by rw [hFi_int, hCi_int, hFC_eq]
      have h3 : ¬ (toInt Fi).natAbs < (toInt Ci).natAbs := by
        rw [h_int_eq]; exact lt_irrefl _
      have h4 : ¬ (toInt Ci).natAbs < (toInt Fi).natAbs := by
        rw [h_int_eq]; exact lt_irrefl _
      rw [ite_eq_right h3, ite_eq_right h4]
      rw [hFn_val, hFi_val]

/-- For `x ≥ 0`, rounding against `natBotSet` and `intSet` give the same value. -/
theorem val_round_natBotSet_eq_intSet (mode : RoundingMode) (x : ℝ) (hx : 0 ≤ x) :
    (round natBotSet mode x).val = (round intSet mode x).val := by
  have hF := val_roundFloor_natBotSet_eq_intSet x hx
  have hC := val_roundCeiling_natBotSet_eq_intSet x hx
  cases mode with
  | Floor => exact hF
  | Ceiling => exact hC
  | Down =>
    show (if 0 ≤ x then roundFloor natBotSet x else roundCeiling natBotSet x).val =
         (if 0 ≤ x then roundFloor intSet x else roundCeiling intSet x).val
    rw [ite_eq_left hx, ite_eq_left hx]; exact hF
  | Up =>
    show (if 0 ≤ x then roundCeiling natBotSet x else roundFloor natBotSet x).val =
         (if 0 ≤ x then roundCeiling intSet x else roundFloor intSet x).val
    rw [ite_eq_left hx, ite_eq_left hx]; exact hC
  | Nearest =>
    show (let F := roundFloor natBotSet x
          let C := roundCeiling natBotSet x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val =
         (let F := roundFloor intSet x
          let C := roundCeiling intSet x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
    simp only
    set Fn : ↥natBotSet := roundFloor natBotSet x
    set Cn : ↥natBotSet := roundCeiling natBotSet x
    set Fi : ↥intSet := roundFloor intSet x
    set Ci : ↥intSet := roundCeiling intSet x
    have hFn_val : Fn.val = ((⌊x⌋ : ℝ) : EReal) := by
      change (roundFloor natBotSet x).val = _
      rw [hF, val_roundFloor_intSet]
    have hCn_val : Cn.val = ((⌈x⌉ : ℝ) : EReal) := by
      change (roundCeiling natBotSet x).val = _
      rw [hC, val_roundCeiling_intSet]
    have hFi_val : Fi.val = ((⌊x⌋ : ℝ) : EReal) := val_roundFloor_intSet x
    have hCi_val : Ci.val = ((⌈x⌉ : ℝ) : EReal) := val_roundCeiling_intSet x
    have hFn_eq_Fi : Fn.val = Fi.val := hFn_val.trans hFi_val.symm
    have hCn_eq_Ci : Cn.val = Ci.val := hCn_val.trans hCi_val.symm
    rw [hFn_eq_Fi, hCn_eq_Ci]
    rcases lt_trichotomy (((x : ℝ) : EReal) - Fi.val) (Ci.val - ((x : ℝ) : EReal))
      with h1 | h1 | h1
    · rw [show compare (((x : ℝ) : EReal) - Fi.val) (Ci.val - ((x : ℝ) : EReal)) = .lt
            from compare_lt_iff_lt.mpr h1]
      exact hFn_eq_Fi
    · rw [show compare (((x : ℝ) : EReal) - Fi.val) (Ci.val - ((x : ℝ) : EReal)) = .eq
            from compare_eq_iff_eq.mpr h1]
      exact natBot_int_tiebreak_value_agree hx Fn Cn Fi Ci hFn_val hCn_val hFi_val hCi_val
    · rw [show compare (((x : ℝ) : EReal) - Fi.val) (Ci.val - ((x : ℝ) : EReal)) = .gt
            from compare_gt_iff_gt.mpr h1]
      exact hCn_eq_Ci

end Azurite
