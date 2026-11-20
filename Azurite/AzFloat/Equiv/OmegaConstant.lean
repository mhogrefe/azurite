/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.OmegaConstant
import Azurite.AzFloat.Equiv.WrightOmega

/-!
## The omega constant is correctly rounded

`Ω = W₀(1) = ω(0)`: `wrightOmegaReal_zero`; the defining equations `lambertW0_one_mul_exp`
(`Ω e^Ω = 1`), `exp_neg_lambertW0_one` (`e^(−Ω) = Ω`), `lambertW0_one_add_log`
(`Ω + ln Ω = 0`); `lambertW0_one_pos`, `irrational_lambertW0_one`; and
**`omegaConstantPrecRound_eq`**: the result is `W₀(1)` correctly rounded, every precision and
mode, no fuel.
-/

namespace Azurite.AzFloat

open Azurite.DLMF Azurite.WrightOmega

theorem wrightOmegaReal_zero : wrightOmegaReal 0 = lambertW0 1 := by
  unfold wrightOmegaReal
  rw [Real.exp_zero]

theorem lambertW0_one_pos : 0 < lambertW0 1 := by
  rw [← wrightOmegaReal_zero]
  exact wrightOmegaReal_pos 0

/-- `Ω e^Ω = 1`. -/
theorem lambertW0_one_mul_exp : lambertW0 1 * Real.exp (lambertW0 1) = 1 := by
  have := wrightOmegaReal_mul_exp 0
  rwa [wrightOmegaReal_zero, Real.exp_zero] at this

/-- `e^(−Ω) = Ω`. -/
theorem exp_neg_lambertW0_one : Real.exp (-lambertW0 1) = lambertW0 1 := by
  rw [Real.exp_neg]
  exact (eq_inv_of_mul_eq_one_left lambertW0_one_mul_exp).symm

/-- `Ω + ln Ω = 0`. -/
theorem lambertW0_one_add_log : lambertW0 1 + Real.log (lambertW0 1) = 0 := by
  have h := congrArg Real.log exp_neg_lambertW0_one
  rw [Real.log_exp] at h
  linarith

/-- **The omega constant is irrational.** -/
theorem irrational_lambertW0_one : Irrational (lambertW0 1) := by
  have := irrational_wrightOmegaReal (r := 0) zero_ne_one
  rwa [Rat.cast_zero, wrightOmegaReal_zero] at this

/-- **The omega constant is correctly rounded.** -/
theorem omegaConstantPrecRound_eq (p : ℕ) [NeZero p] (mode : RoundingMode) :
    omegaConstantPrecRound p mode = roundVal p mode (some ((lambertW0 1 : ℝ) : EReal)) := by
  unfold omegaConstantPrecRound
  rw [wrightOmegaPrecRound_eq, liftVal, toVal_zero, Option.bind_some, ← EReal.coe_zero,
    Spec.wrightOmega_coe, wrightOmegaReal_zero]

end Azurite.AzFloat
