/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhCosh
import Azurite.AzFloat.SinhCoshRat
import Azurite.AzFloat.Equiv.Sinh
import Azurite.AzFloat.Equiv.SinhRat
import Azurite.AzFloat.Equiv.Cosh

/-!
# Equivalence: `sinh` and `cosh` together

`sinhCoshPrecRound_eq :
  sinhCoshPrecRound x p mode = (sinhPrecRound x p mode, coshPrecRound x p mode)` (for every
`p`), `sinhCoshPrecRound_eq_liftVal`, `sinhCosh_eq`, and the rational versions
`sinhCoshRatPrecRound_eq`, `sinhCoshRatPrecRound_eq_roundVal`, `sinhCoshRat_eq`.
-/

namespace Azurite.AzFloat

/-- **The joint computation agrees with the separate ones.** -/
theorem sinhCoshPrecRound_eq (x : AzFloat) (p : ℕ) (mode : RoundingMode) :
    sinhCoshPrecRound x p mode = (sinhPrecRound x p mode, coshPrecRound x p mode) := by
  cases x with
  | nan => rfl
  | infinity s => rfl
  | zero => rfl
  | finite s e q m hv =>
    by_cases hp : p = 0
    · subst hp
      simp [sinhCoshPrecRound, sinhPrecRound, coshPrecRound]
    have : NeZero p := ⟨hp⟩
    simp only [sinhCoshPrecRound]
    rw [dite_eq_right hp]
    split
    · next hsT hcT =>
      have hx0 := finiteVal_ne_zero s e hv
      have hx := toVal_finite s e q m hv
      have hb := (abs_finiteVal_bounds s e hv).2
      rw [sinhPrecRound_eq_liftVal, coshPrecRound_eq_liftVal]
      unfold liftVal
      simp only [toVal_finite, Option.bind_some, Spec.sinh_coe, Spec.cosh_coe]
      refine zivLoopCertified₂_eq p mode _ (Real.sinh (finiteVal s e m))
        (Real.cosh (finiteVal s e m))
        (not_mem_floatSet_of_irrational p (irrational_sinh_of_toVal hx hx0))
        (not_mem_floatSet_of_irrational p (irrational_cosh_of_toVal hx hx0))
        _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
      have hw64 : 64 ≤ w := by unfold zivGuardBits at hw; omega
      obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, -⟩ :=
        sinhApprox_spec hx hx0 hb (finiteVal_neg_iff s e hv) hw64
      obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, -⟩ := sinhCoshApprox_spec_cosh (!s) hx hb hw64
      rw [← sinhCoshApprox_fst] at hl₁ hh₁
      exact ⟨l₁, h₁, l₂, h₂, hl₁, hh₁, a₁, b₁, hl₂, hh₂, a₂, b₂⟩
    · rfl

/-- **`sinh x` and `cosh x` are both correctly rounded.** -/
theorem sinhCoshPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinhCoshPrecRound x p mode = (liftVal Spec.sinh x p mode, liftVal Spec.cosh x p mode) := by
  rw [sinhCoshPrecRound_eq, sinhPrecRound_eq_liftVal, coshPrecRound_eq_liftVal]

/-- `sinhCosh x = (sinh x, cosh x)`. -/
theorem sinhCosh_eq (x : AzFloat) : sinhCosh x = (sinh x, cosh x) := by
  unfold sinhCosh sinh cosh
  rw [sinhCoshPrecRound_eq]

/-- **The joint rational computation agrees with the separate ones.** -/
theorem sinhCoshRatPrecRound_eq (q : AzRat) (p : ℕ) (mode : RoundingMode) :
    sinhCoshRatPrecRound q p mode = (sinhRatPrecRound q p mode, coshRatPrecRound q p mode) := by
  unfold sinhCoshRatPrecRound
  by_cases h0 : q.num = 0
  · rw [dite_eq_left h0]
  rw [dite_eq_right h0]
  by_cases hp : p = 0
  · rw [dite_eq_left hp]
  rw [dite_eq_right hp]
  have : NeZero p := ⟨hp⟩
  split
  · rw [sinhRatPrecRound_eq, coshRatPrecRound_eq, Spec.sinh_coe, Spec.cosh_coe]
    refine zivLoopCertified₂_eq p mode _ (Real.sinh (AzRat.toRat q : ℝ))
      (Real.cosh (AzRat.toRat q : ℝ))
      (not_mem_floatSet_of_irrational p (irrational_sinh_toRat q h0))
      (not_mem_floatSet_of_irrational p (irrational_cosh_toRat q h0))
      _ (by unfold zivGuardBits; omega) (fun w hw => ?_) _
    have hw64 : 64 ≤ w := by unfold zivGuardBits at hw; omega
    obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, -⟩ := sinhRatApprox_spec hw64 q h0
    obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, -⟩ := sinhCoshRatApprox_spec_cosh hw64 q h0
    rw [← sinhCoshRatApprox_fst] at hl₁ hh₁
    exact ⟨l₁, h₁, l₂, h₂, hl₁, hh₁, a₁, b₁, hl₂, hh₂, a₂, b₂⟩
  · rfl

/-- **`sinh q` and `cosh q` are both correctly rounded.** -/
theorem sinhCoshRatPrecRound_eq_roundVal (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sinhCoshRatPrecRound q p mode
      = (roundVal p mode (Spec.sinh (((AzRat.toRat q : ℚ) : ℝ) : EReal)),
        roundVal p mode (Spec.cosh (((AzRat.toRat q : ℚ) : ℝ) : EReal))) := by
  rw [sinhCoshRatPrecRound_eq, sinhRatPrecRound_eq, coshRatPrecRound_eq]

/-- `sinhCoshRat q p = (sinhRat q p, coshRat q p)`. -/
theorem sinhCoshRat_eq (q : AzRat) (p : ℕ) :
    sinhCoshRat q p = (sinhRat q p, coshRat q p) := by
  unfold sinhCoshRat sinhRat coshRat
  rw [sinhCoshRatPrecRound_eq]

end Azurite.AzFloat
