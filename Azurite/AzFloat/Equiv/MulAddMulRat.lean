/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulAddMulRat
import Azurite.AzFloat.Equiv.AddMulRat
import Azurite.AzFloat.Equiv.MulAddMul

/-!
# Equivalence: a product plus or minus a product with a rational factor

With `x·y` exact (`toVal_exactMul`) and `addMulRatPrecRound` correctly rounded,
`mulAddMulRatPrecRound_eq_liftVal₃` and `mulSubMulRatPrecRound_eq_liftVal₃` state one rounding
of `x·y ± z·w` (`Spec.mulAddMul`/`Spec.mulSubMul` at the rational `w`); the `Float` versions are
the binary64 rounding of the exact value.
-/

namespace Azurite.AzFloat

/-- The bind of an exact product commutes past a later bind. -/
theorem bind_product_left (h : EReal → EReal → Option EReal) (x y z : AzFloat) :
    ((x.toVal.bind fun a => y.toVal.bind fun b => Spec.mul a b).bind fun ab =>
        z.toVal.bind fun c => h ab c)
      = x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c =>
          (Spec.mul a b).bind fun ab => h ab c := by
  cases x.toVal <;> cases y.toVal <;> simp only [Option.bind_none, Option.bind_some]
  rename_i a b
  cases z.toVal <;> simp only [Option.bind_none, Option.bind_some]
  cases Spec.mul a b <;> rfl

/-- **`mulAddMulRatPrecRound` is correctly rounded**: one rounding of `x·y + z·w`. -/
theorem mulAddMulRatPrecRound_eq_liftVal₃ (x y z : AzFloat) (w : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulAddMulRatPrecRound x y z w p mode
      = liftVal₃ (fun a b c => Spec.mulAddMul a b c ((AzRat.toRat w : ℝ) : EReal))
          x y z p mode := by
  unfold mulAddMulRatPrecRound liftVal₃
  rw [addMulRatPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [toVal_exactMul, bind_product_left]
  rfl

/-- **`mulSubMulRatPrecRound` is correctly rounded**: one rounding of `x·y − z·w`. -/
theorem mulSubMulRatPrecRound_eq_liftVal₃ (x y z : AzFloat) (w : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulSubMulRatPrecRound x y z w p mode
      = liftVal₃ (fun a b c => Spec.mulSubMul a b c ((AzRat.toRat w : ℝ) : EReal))
          x y z p mode := by
  unfold mulSubMulRatPrecRound liftVal₃
  rw [subMulRatPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [toVal_exactMul, bind_product_left]
  rfl

/-! ### Through `Float` -/

/-- `mulAddMulRatFloat64` is the binary64 rounding of `x·y + z·w`. -/
theorem toVal_mulAddMulRatFloat64 (x y z : Float) (w : AzRat) :
    (mulAddMulRatFloat64 x y z w).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            Spec.mulAddMul a b c ((AzRat.toRat w : ℝ) : EReal)) :=
  toVal_emulate₃Rat mulAddMulRatPrecRound
    (fun a b c w => Spec.mulAddMul a b c ((AzRat.toRat w : ℝ) : EReal))
    (fun x y z w => mulAddMulRatPrecRound_eq_liftVal₃ x y z w 53 .Nearest) x y z w

/-- `mulSubMulRatFloat64` is the binary64 rounding of `x·y − z·w`. -/
theorem toVal_mulSubMulRatFloat64 (x y z : Float) (w : AzRat) :
    (mulSubMulRatFloat64 x y z w).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            Spec.mulSubMul a b c ((AzRat.toRat w : ℝ) : EReal)) :=
  toVal_emulate₃Rat mulSubMulRatPrecRound
    (fun a b c w => Spec.mulSubMul a b c ((AzRat.toRat w : ℝ) : EReal))
    (fun x y z w => mulSubMulRatPrecRound_eq_liftVal₃ x y z w 53 .Nearest) x y z w

end Azurite.AzFloat
