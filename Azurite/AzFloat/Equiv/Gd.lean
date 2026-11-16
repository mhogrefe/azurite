/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.GdRat
import Azurite.AzFloat.Equiv.Atan2

/-!
# Equivalence: the Gudermannian `gd x`

`Spec.gd a = gd a` (`±π/2` at `±∞`) and
`gdPrecRound_eq_liftVal : gdPrecRound x p mode = liftVal Spec.gd x p mode` and
`gdRatPrecRound_eq : gdRatPrecRound q p mode = roundVal p mode (Spec.gd q)`, for `p ≠ 0`.
-/

open Real

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real Gudermannian: `±∞ ↦ ±π/2`. -/
noncomputable def gd (a : EReal) : Option EReal :=
  some (if a = ⊤ then ((π / 2 : ℝ) : EReal) else if a = ⊥ then ((-(π / 2) : ℝ) : EReal)
    else ((DLMF.gd a.toReal : ℝ) : EReal))

theorem gd_coe (r : ℝ) : gd (r : EReal) = some ((DLMF.gd r : ℝ) : EReal) := by
  unfold gd
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem gd_top : gd ⊤ = some ((π / 2 : ℝ) : EReal) := by
  unfold gd
  rw [ite_eq_left rfl]

@[simp] theorem gd_bot : gd ⊥ = some ((-(π / 2) : ℝ) : EReal) := by
  unfold gd
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- **The Gudermannian is correctly rounded.** -/
theorem gdPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gdPrecRound x p mode = liftVal Spec.gd x p mode := by
  unfold liftVal
  have hpi2 := fun (p : ℕ) [NeZero p] (m : RoundingMode) => piDiv2PrecRound_eq_liftVal₀ p m
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [gdPrecRound, toVal_infinity, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), signedRound_eq hpi2]
    cases s <;> simp
  | zero =>
    simp only [gdPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.gd_coe, gd_zero, EReal.coe_zero, roundVal_zero]
  | finite s e q m hv =>
    simp only [gdPrecRound, toVal_finite, Option.bind_some, Spec.gd_coe]
    rw [dite_eq_right (NeZero.ne p)]
    have hx0 := finiteVal_ne_zero s e hv
    have hb := abs_finiteVal_bounds s e hv
    have hneg : (!s) = true ↔ finiteVal s e m < 0 := finiteVal_neg_iff s e hv
    split
    · next r hT =>
      exact sinTiny?_eq_of gd_neg (fun _ ha => gd_lt_self ha) (fun _ ha => sub_cube_le_gd ha)
        hv p mode hT
    have hval := gd_eq_of_neg_iff hneg
    exact zivLoopCertified_eq_threshold' p mode _ (DLMF.gd (finiteVal s e m))
      (not_mem_floatSet_of_irrational p (irrational_gd_of_toVal (toVal_finite s e q m hv) hx0))
      _ (by unfold zivGuardBits; omega)
      (fun w _ => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := gdApprox_spec (!s)
          (toVal_finite s e q m hv) hx0 e hb.1 hb.2 w
        rw [← hval] at hlo hhi
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

/-- **The Gudermannian of a rational is correctly rounded.** -/
theorem gdRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gdRatPrecRound q p mode
      = roundVal p mode (Spec.gd (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  have hp := NeZero.ne p
  unfold gdRatPrecRound
  rw [Spec.gd_coe]
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, gd_zero, EReal.coe_zero,
      roundVal_zero]
  · rw [dite_eq_right h0, dite_eq_right hp]
    split
    · next r hT =>
      exact sinTinyRat?_eq_of gd_neg (fun _ ha => gd_lt_self ha) (fun _ ha => sub_cube_le_gd ha)
        q h0 hT
    exact zivLoopCertified_eq_threshold' p mode _ _
      (not_mem_floatSet_of_irrational p (irrational_gd_toRat q h0)) _
      (by unfold zivGuardBits; omega)
      (fun w _ => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := gdRatApprox_spec q h0 w
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) _

end Azurite.AzFloat
