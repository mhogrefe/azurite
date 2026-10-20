/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMul
import Azurite.AzFloat.Equiv.Add
import Azurite.AzFloat.Equiv.Mul
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzFloat.Equiv.Float64Emulate

/-!
# Equivalence: fused multiply-add and multiply-subtract

`toVal_exactMul`: the value of `exactMul y z` is exactly `Spec.mul` of the values (the product
of two floats of precisions `q₁`, `q₂` is `k · 2^j` with `|k| < 2^(q₁+q₂)`, so it lies in
`floatSet (q₁ + q₂)` and rounding there is the identity).  Hence
`addMulPrecRound_eq_liftVal₃ : addMulPrecRound x y z p mode = liftVal₃ Spec.addMul x y z p mode`
(`Spec.addMul a b c = (Spec.mul b c).bind (Spec.add a)`), the same for `subMul`, and the `Float`
versions are the binary64 rounding of `x + y·z` (`toVal_addMulFloat64`).
-/

namespace Azurite.AzFloat

namespace Spec

/-- The specification of `x + y·z`. -/
noncomputable def addMul (a b c : EReal) : Option EReal := (mul b c).bind (add a)

/-- The specification of `x − y·z`. -/
noncomputable def subMul (a b c : EReal) : Option EReal := (mul b c).bind (sub a)

end Spec

/-- Lift a ternary function on specification values to floats. -/
noncomputable def liftVal₃ (f : EReal → EReal → EReal → Option EReal) (x y z : AzFloat)
    (p : ℕ) [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  roundVal p mode (x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c => f a b c)

/-! ### Rounding that loses nothing -/

/-- `roundVal` returns a float of the given value when that value is `NaN`, an infinity, or a
real in `floatSet p`. -/
theorem toVal_fst_roundVal (p : ℕ) [NeZero p] (mode : RoundingMode) (w : Option EReal)
    (h : ∀ r : ℝ, w = some (r : EReal) → ((r : ℝ) : EReal) ∈ floatSet p) :
    (roundVal p mode w).1.toVal = w := by
  cases w with
  | none => rfl
  | some e =>
    induction e using EReal.rec with
    | bot => rw [roundVal_of_toVal p mode (infinity false) ⊥ (Or.inr rfl) rfl]; rfl
    | coe r => exact (roundVal_of_mem p mode r (h r rfl)).1
    | top => rw [roundVal_of_toVal p mode (infinity true) ⊤ (Or.inr rfl) rfl]; rfl

theorem zero_mem_floatSet (p : ℕ) : (((0 : ℝ) : ℝ) : EReal) ∈ floatSet p :=
  ⟨zero, Or.inr rfl, rfl⟩

theorem exactProductPrec_pos (y z : AzFloat) : 0 < exactProductPrec y z := by
  unfold exactProductPrec
  rcases y with _ | _ | _ | ⟨_, _, p₁, _, h₁⟩ <;>
    rcases z with _ | _ | _ | ⟨_, _, p₂, _, h₂⟩ <;>
    simp only [precision?, Option.getD_some, Option.getD_none]
  all_goals
    first
    | omega
    | exact Nat.add_pos_left h₁.pos _

/-- **The exact product**: `exactMul` loses nothing, on every input. -/
theorem toVal_exactMul (y z : AzFloat) :
    (exactMul y z).toVal = y.toVal.bind fun b => z.toVal.bind fun c => Spec.mul b c := by
  unfold exactMul
  have : NeZero (exactProductPrec y z) := ⟨(exactProductPrec_pos y z).ne'⟩
  rw [mulPrecRound_eq_liftVal₂]
  unfold liftVal₂
  apply toVal_fst_roundVal
  intro r hr
  cases y with
  | nan => simp at hr
  | infinity s =>
    cases z with
    | nan => simp at hr
    | infinity t =>
      cases s <;> cases t <;> simp [Spec.mul, EReal.top_ne_zero, EReal.bot_ne_zero] at hr
    | zero => simp [Spec.mul] at hr
    | finite t e q m hv =>
      simp only [toVal_infinity, toVal_finite, Option.bind_some] at hr
      rw [Spec.mul_inf_coe s _ (finiteVal_ne_zero_of_valid t e hv)] at hr
      split_ifs at hr <;> simp at hr
  | zero =>
    cases z with
    | nan => simp at hr
    | infinity t => simp [Spec.mul] at hr
    | zero =>
      simp [Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot] at hr
      obtain rfl : r = 0 := by
        first | exact hr | exact hr.symm | exact EReal.coe_eq_zero.mp hr.symm
      exact zero_mem_floatSet _
    | finite t e q m hv =>
      simp [Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot] at hr
      obtain rfl : r = 0 := by
        first | exact hr | exact hr.symm | exact EReal.coe_eq_zero.mp hr.symm
      exact zero_mem_floatSet _
  | finite s e₁ p₁ m₁ h₁ =>
    cases z with
    | nan => simp at hr
    | infinity t =>
      simp only [toVal_infinity, toVal_finite, Option.bind_some] at hr
      rw [Spec.mul_coe_inf _ (finiteVal_ne_zero_of_valid s e₁ h₁) t] at hr
      split_ifs at hr <;> simp at hr
    | zero =>
      simp [Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot] at hr
      obtain rfl : r = 0 := by
        first | exact hr | exact hr.symm | exact EReal.coe_eq_zero.mp hr.symm
      exact zero_mem_floatSet _
    | finite t e₂ p₂ m₂ h₂ =>
      simp only [toVal_finite, Option.bind_some, Spec.mul_coe_coe, Option.some.injEq,
        EReal.coe_eq_coe_iff] at hr
      rw [← hr]
      have hq : exactProductPrec (finite s e₁ p₁ m₁ h₁) (finite t e₂ p₂ m₂ h₂)
          = p₁ + p₂ := rfl
      rw [hq]
      have : NeZero (p₁ + p₂) := ⟨by have := h₁.pos; omega⟩
      obtain ⟨k₁, hk₁, hk₁b⟩ := finiteVal_eq_int_mul_prec s e₁ h₁
      obtain ⟨k₂, hk₂, hk₂b⟩ := finiteVal_eq_int_mul_prec t e₂ h₂
      have hprod : finiteVal s e₁ m₁ * finiteVal t e₂ m₂
          = ((k₁ * k₂ : ℤ) : ℝ)
            * (2 : ℝ) ^ (e₁.toInt - p₁ + (e₂.toInt - p₂)) := by
        rw [hk₁, hk₂, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; push_cast; ring
      rw [hprod]
      apply mem_floatSet_mul_zpow
      rw [abs_mul, pow_add]
      exact (mul_le_mul hk₁b.le hk₂b.le (abs_nonneg _) (by positivity))

/-! ### The fused operations -/

/-- **`addMulPrecRound` is correctly rounded**: one rounding of `x + y·z`. -/
theorem addMulPrecRound_eq_liftVal₃ (x y z : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    addMulPrecRound x y z p mode = liftVal₃ Spec.addMul x y z p mode := by
  unfold addMulPrecRound liftVal₃
  rw [addPrecRound_eq_liftVal₂]
  unfold liftVal₂
  simp only [toVal_exactMul, Option.bind_assoc, Spec.addMul]

/-- **`subMulPrecRound` is correctly rounded**: one rounding of `x − y·z`. -/
theorem subMulPrecRound_eq_liftVal₃ (x y z : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    subMulPrecRound x y z p mode = liftVal₃ Spec.subMul x y z p mode := by
  unfold subMulPrecRound liftVal₃
  rw [subPrecRound_eq_liftVal₂]
  unfold liftVal₂
  simp only [toVal_exactMul, Option.bind_assoc, Spec.subMul]

/-! ### Through `Float` -/

/-- `addMulFloat64` is the binary64 rounding of `x + y·z`. -/
theorem toVal_addMulFloat64 (x y z : Float) :
    (addMulFloat64 x y z).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            Spec.addMul a b c) :=
  toVal_emulate₃ addMulPrecRound Spec.addMul
    (fun x y z => addMulPrecRound_eq_liftVal₃ x y z 53 .Nearest) x y z

/-- `subMulFloat64` is the binary64 rounding of `x − y·z`. -/
theorem toVal_subMulFloat64 (x y z : Float) :
    (subMulFloat64 x y z).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            Spec.subMul a b c) :=
  toVal_emulate₃ subMulPrecRound Spec.subMul
    (fun x y z => subMulPrecRound_eq_liftVal₃ x y z 53 .Nearest) x y z

end Azurite.AzFloat
