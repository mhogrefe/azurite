/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanPi
import Azurite.AzFloat.Equiv.TanWithPeriod
import Azurite.AzFloat.Equiv.TanRatWithPeriod

/-!
# Equivalence: `tan (π x)`

`Spec.tanPi : EReal → Option EReal` (undefined at `±∞`; at the half-integers the IEEE 754 poles:
`Spec.tanPi_int_add_half`), `tanPiPrecRound_eq_liftVal : tanPiPrecRound x p mode =
liftVal Spec.tanPi x p mode` and `tanPiRatPrecRound_eq : tanPiRatPrecRound q p mode =
roundVal p mode (Spec.tanPi q)`, for `p ≠ 0`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `tan (π a)` with the IEEE 754 poles: undefined (`NaN`) at `±∞`. -/
noncomputable def tanPi (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then none else some (tanPole (Real.pi * a.toReal))

theorem tanPi_coe (r : ℝ) : tanPi (r : EReal) = some (tanPole (Real.pi * r)) := by
  unfold tanPi
  rw [ite_eq_right (not_or.mpr ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩), EReal.toReal_coe]

@[simp] theorem tanPi_top : tanPi ⊤ = none := by
  unfold tanPi
  rw [ite_eq_left (Or.inl rfl)]

@[simp] theorem tanPi_bot : tanPi ⊥ = none := by
  unfold tanPi
  rw [ite_eq_left (Or.inr rfl)]

/-- IEEE 754: `tanPi (n + 1/2)` is `+∞` for an even integer `n` and `−∞` for an odd one. -/
theorem tanPi_int_add_half (n : ℤ) :
    tanPi (((n + 1 / 2 : ℝ)) : EReal) = some (if Even n then ⊤ else ⊥) := by
  rw [tanPi_coe, tanPole_pi_mul_int_add_half]

/-- `tan (π a)` is the period-`2` case of `tanWithPeriod`. -/
theorem tanWithPeriod_two (a : EReal) : tanWithPeriod a 2 = tanPi a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [tanWithPeriod_coe r (by norm_num), tanPi_coe]
    congr 2
    push_cast
    ring

end Spec

/-- **`tan (π x)` is correctly rounded**, with the IEEE 754 poles. -/
theorem tanPiPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tanPiPrecRound x p mode = liftVal Spec.tanPi x p mode := by
  unfold tanPiPrecRound liftVal
  rw [tanWithPeriodPrecRound_eq]
  congr 2
  funext a
  exact Spec.tanWithPeriod_two a

/-- **`tan (π q)` of a rational is correctly rounded**, with the IEEE 754 poles. -/
theorem tanPiRatPrecRound_eq (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    tanPiRatPrecRound q p mode
      = roundVal p mode (Spec.tanPi (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  unfold tanPiRatPrecRound
  rw [tanRatWithPeriodPrecRound_eq]
  exact congrArg _ (Spec.tanWithPeriod_two _)

end Azurite.AzFloat
