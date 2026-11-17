/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GdInv
import Azurite.AzFloat.GdInvRat
import Azurite.AzFloat.Equiv.ZivPair

/-!
# Equivalence: the inverse Gudermannian `gd⁻¹ x`

`Spec.gdInv : EReal → Option EReal` (undefined, i.e. `NaN`, outside `(−π/2, π/2)`) and
`gdInvPrecRound_eq_liftVal : gdInvPrecRound x p mode = liftVal Spec.gdInv x p mode` and
`gdInvRatPrecRound_eq : gdInvRatPrecRound q p mode = roundVal p mode (Spec.gdInv q)`, for
`p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real inverse Gudermannian: undefined outside `(−π/2, π/2)`. -/
noncomputable def gdInv (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ ∨ π / 2 ≤ |a.toReal| then none
  else some ((DLMF.gdInv a.toReal : ℝ) : EReal)

theorem gdInv_coe {r : ℝ} (hr : |r| < π / 2) :
    gdInv (r : EReal) = some ((DLMF.gdInv r : ℝ) : EReal) := by
  unfold gdInv
  rw [ite_eq_right (by
    rw [EReal.toReal_coe]
    exact not_or.mpr ⟨EReal.coe_ne_top r, not_or.mpr ⟨EReal.coe_ne_bot r, not_le.mpr hr⟩⟩),
    EReal.toReal_coe]

theorem gdInv_coe_of_le {r : ℝ} (hr : π / 2 ≤ |r|) : gdInv (r : EReal) = none := by
  unfold gdInv
  rw [ite_eq_left (by
    rw [EReal.toReal_coe]
    exact Or.inr (Or.inr hr))]

@[simp] theorem gdInv_top : gdInv ⊤ = none := by
  unfold gdInv
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem gdInv_bot : gdInv ⊥ = none := by
  unfold gdInv
  rw [ite_eq_left (Or.inr (Or.inl rfl))]

end Spec

/-- **The inverse Gudermannian is correctly rounded.** -/
theorem gdInvPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gdInvPrecRound x p mode = liftVal Spec.gdInv x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [gdInvPrecRound]
  | zero =>
    simp only [gdInvPrecRound, toVal_zero, Option.bind_some]
    have h0 : DLMF.gdInv 0 = 0 := by
      have := DLMF.gdInv_gd 0
      rwa [gd_zero] at this
    rw [← EReal.coe_zero, Spec.gdInv_coe (by simp [pi_pos]), h0, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [gdInvPrecRound, toVal_finite, Option.bind_some]
    set xv := finiteVal s e m with hxv
    have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
    have hneg : (!s) = true ↔ xv < 0 := finiteVal_neg_iff s e hv
    have hb := abs_finiteVal_bounds s e hv
    rw [← hxv] at hb
    have hdom := gdInvInDomain_iff s e hv
    rw [← hxv] at hdom
    by_cases hd : gdInvInDomain (finite s e q m hv) e q = true
    · rw [dite_eq_left hd, dite_eq_right (NeZero.ne p)]
      have hlt := hdom.mp hd
      rw [Spec.gdInv_coe hlt]
      split
      · next r hT =>
        have hc : e.sign = false ∧ max p q + zivGuardBits + 8 ≤ e.abs.toNat := by
          unfold tanTiny? at hT
          dsimp only at hT
          by_contra hc
          rw [ite_eq_right hc] at hT
          exact absurd hT (by simp)
        have hquarter := two_zpow_le_quarter hc.1 (by
          have := hc.2
          unfold zivGuardBits at this
          omega)
        rw [hxv, ← gdInvPatch_eq (by linarith [(abs_finiteVal_bounds s e hv).2] :
          |finiteVal s e m| ≤ 1 / 4)]
        exact tanTiny?_eq_of gdInvPatch_neg gdInvPatch_bounds hv p mode hT
      have hval := gdInv_eq_of_neg_iff hneg hlt
      refine zivLoopCertified_eq_or_none p mode _ (DLMF.gdInv xv)
        (not_mem_floatSet_of_irrational p
          (irrational_gdInv_of_toVal (toVal_finite s e q m hv) hx0 hlt))
        _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
      rw [hval]
      exact gdInvApprox_valid_or_none (!s) (toVal_finite s e q m hv) hb.2 hlt
        (by unfold zivGuardBits at hw; omega) p mode
    · rw [dite_eq_right hd]
      have hge : π / 2 ≤ |xv| := not_lt.mp fun h => hd (hdom.mpr h)
      rw [Spec.gdInv_coe_of_le hge, roundVal_none]

/-- **The inverse Gudermannian of a rational is correctly rounded.** -/
theorem gdInvRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gdInvRatPrecRound q p mode
      = roundVal p mode (Spec.gdInv (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold gdInvRatPrecRound
  by_cases h0 : q.num = 0
  · have h00 : DLMF.gdInv 0 = 0 := by
      have := DLMF.gdInv_gd 0
      rwa [gd_zero] at this
    rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0,
      Spec.gdInv_coe (by simp [pi_pos]), h00, EReal.coe_zero, roundVal_zero]
  · rw [dite_eq_right h0]
    have hdom := gdInvRatInDomain_iff q h0
    by_cases hd : gdInvRatInDomain q = true
    · rw [dite_eq_left hd, dite_eq_right hp]
      have hlt := hdom.mp hd
      rw [Spec.gdInv_coe hlt]
      split
      · next r hT =>
        have hr := tanTinyRat?_eq_of gdInvPatch_neg gdInvPatch_bounds q h0 hT
        have hc : (ratExpBound q).sign = false
            ∧ p + zivGuardBits + 8 ≤ (ratExpBound q).abs.toNat := by
          unfold tanTinyRat? at hT
          replace hT := eq_some_of_guardedBy hT
          unfold tanTinyCore? at hT
          dsimp only at hT
          by_contra hc
          rw [ite_eq_right hc] at hT
          cases hT
        have hlt2 : |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
          lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
        have hq := two_zpow_le_quarter hc.1 (by omega)
        rwa [gdInvPatch_eq (by linarith)] at hr
      refine zivLoopCertified_eq_or_none p mode _ (DLMF.gdInv (AzRat.toRat q : ℝ))
        (not_mem_floatSet_of_irrational p (irrational_gdInv_toRat q h0 hlt))
        _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
      exact gdInvRatApprox_valid_or_none q h0 hlt (by unfold zivGuardBits at hw; omega) p mode
    · rw [dite_eq_right hd]
      have hge : π / 2 ≤ |((AzRat.toRat q : ℚ) : ℝ)| := not_lt.mp fun h => hd (hdom.mpr h)
      rw [Spec.gdInv_coe_of_le hge, roundVal_none]

end Azurite.AzFloat
