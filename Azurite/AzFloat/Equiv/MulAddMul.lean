/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulAddMul
import Azurite.AzFloat.Equiv.AddMul

/-!
# Equivalence: sums and differences of two products

With both products exact (`toVal_exactMul`), `mulAddMulPrecRound_eq_liftVal₄` and
`mulSubMulPrecRound_eq_liftVal₄` are the addition and subtraction specifications applied to the
products: one rounding of `x·y ± z·w` (`Spec.mulAddMul`, `Spec.mulSubMul`).  The `Float` versions
are the binary64 rounding of the exact value.
-/

namespace Azurite.AzFloat

namespace Spec

/-- The specification of `x·y + z·w`. -/
noncomputable def mulAddMul (a b c d : EReal) : Option EReal :=
  (mul a b).bind fun ab => (mul c d).bind fun cd => add ab cd

/-- The specification of `x·y − z·w`. -/
noncomputable def mulSubMul (a b c d : EReal) : Option EReal :=
  (mul a b).bind fun ab => (mul c d).bind fun cd => sub ab cd

end Spec

/-- Lift a function of four specification values to floats. -/
noncomputable def liftVal₄ (f : EReal → EReal → EReal → EReal → Option EReal)
    (x y z w : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  roundVal p mode (x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c =>
    w.toVal.bind fun d => f a b c d)

/-- The binds of two exact products commute past each other. -/
theorem bind_products (g : EReal → EReal → Option EReal) (x y z w : AzFloat) :
    ((x.toVal.bind fun a => y.toVal.bind fun b => Spec.mul a b).bind fun ab =>
        (z.toVal.bind fun c => w.toVal.bind fun d => Spec.mul c d).bind fun cd => g ab cd)
      = x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c => w.toVal.bind fun d =>
          (Spec.mul a b).bind fun ab => (Spec.mul c d).bind fun cd => g ab cd := by
  cases x.toVal <;> cases y.toVal <;> simp only [Option.bind_none, Option.bind_some]
  rename_i a b
  cases z.toVal <;> cases w.toVal <;> simp only [Option.bind_none, Option.bind_some]
  · cases Spec.mul a b <;> rfl
  · cases Spec.mul a b <;> rfl
  · cases Spec.mul a b <;> rfl

/-- **`mulAddMulPrecRound` is correctly rounded**: one rounding of `x·y + z·w`. -/
theorem mulAddMulPrecRound_eq_liftVal₄ (x y z w : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulAddMulPrecRound x y z w p mode = liftVal₄ Spec.mulAddMul x y z w p mode := by
  unfold mulAddMulPrecRound liftVal₄
  rw [addPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [toVal_exactMul, toVal_exactMul, bind_products Spec.add]
  rfl

/-- **`mulSubMulPrecRound` is correctly rounded**: one rounding of `x·y − z·w`. -/
theorem mulSubMulPrecRound_eq_liftVal₄ (x y z w : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    mulSubMulPrecRound x y z w p mode = liftVal₄ Spec.mulSubMul x y z w p mode := by
  unfold mulSubMulPrecRound liftVal₄
  rw [subPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [toVal_exactMul, toVal_exactMul, bind_products Spec.sub]
  rfl

/-! ### Through `Float` -/

/-- `mulAddMulFloat64` is the binary64 rounding of `x·y + z·w`. -/
theorem toVal_mulAddMulFloat64 (x y z w : Float) :
    (mulAddMulFloat64 x y z w).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            w.toModel.unpack.toVal.bind fun d => Spec.mulAddMul a b c d) :=
  toVal_emulate₄ mulAddMulPrecRound Spec.mulAddMul
    (fun x y z w => mulAddMulPrecRound_eq_liftVal₄ x y z w 53 .Nearest) x y z w

/-- `mulSubMulFloat64` is the binary64 rounding of `x·y − z·w`. -/
theorem toVal_mulSubMulFloat64 (x y z w : Float) :
    (mulSubMulFloat64 x y z w).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            w.toModel.unpack.toVal.bind fun d => Spec.mulSubMul a b c d) :=
  toVal_emulate₄ mulSubMulPrecRound Spec.mulSubMul
    (fun x y z w => mulSubMulPrecRound_eq_liftVal₄ x y z w 53 .Nearest) x y z w

end Azurite.AzFloat
