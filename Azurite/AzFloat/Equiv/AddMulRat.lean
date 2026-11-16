/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddMulRat
import Azurite.AzFloat.Equiv.Add
import Azurite.AzFloat.Equiv.AddMul
import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.MulRat
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzRat.Equiv.Mul

/-!
# Equivalence: fused multiply-add and multiply-subtract with a rational factor

`fusedMulRat_eq`: whenever the float–float operation is `liftVal₂ opE` and the float–rational
operation is `liftVal (fun a => opE a q)`, the fused operation is
`liftVal₂ (fun a b => (Spec.mul b z).bind (opE a))` — one rounding of `x ⊕ (y·z)`.  Hence
`addMulRatPrecRound_eq_liftVal₂` and `subMulRatPrecRound_eq_liftVal₂`, with the specifications
`Spec.addMul`/`Spec.subMul` of `Equiv/AddMul` at the rational `z`; the `Float` versions are the
binary64 rounding of `x ± y·z` (`toVal_addMulRatFloat64`, `toVal_subMulRatFloat64`).
-/

namespace Azurite.AzFloat

/-- **Rounding `x + c · 2^k` through the shifted `x`**: round `x · 2^(−k) + c` and shift the
result by `k`. -/
theorem shift_roundVal_add (x : AzFloat) (c : ℝ) (k : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (shiftLeft (roundVal p mode
        ((shiftLeft x (-k)).toVal.bind fun a => Spec.add a ((c : ℝ) : EReal))).1 k,
      (roundVal p mode
        ((shiftLeft x (-k)).toVal.bind fun a => Spec.add a ((c : ℝ) : EReal))).2)
      = roundVal p mode (x.toVal.bind fun a => Spec.add a ((c * 2 ^ k.toInt : ℝ) : EReal)) := by
  have h2k : (2 : ℝ) ^ (-k.toInt) * 2 ^ k.toInt = 1 := by
    rw [zpow_neg, inv_mul_cancel₀ (zpow_pos (by norm_num) _).ne']
  cases x with
  | nan => simp
  | infinity s =>
    have hbot : ∀ r : ℝ, Spec.add ⊥ ((r : ℝ) : EReal) = some ⊥ := fun r => by simp [Spec.add]
    have htop : ∀ r : ℝ, Spec.add ⊤ ((r : ℝ) : EReal) = some ⊤ := fun r => by simp [Spec.add]
    cases s
    · simp only [shiftLeft_infinity, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, hbot]
      simp
    · simp only [shiftLeft_infinity, toVal_infinity, ↓reduceIte, Option.bind_some, htop]
      simp
  | zero =>
    simp only [shiftLeft_zero, toVal_zero, Option.bind_some]
    rw [show (0 : EReal) = ((0 : ℝ) : EReal) by simp, Spec.add_coe_coe, Spec.add_coe_coe,
      zero_add, zero_add, roundVal_mul_two_zpow]
    rfl
  | finite s e q m hv =>
    simp only [shiftLeft_finite, toVal_finite, Option.bind_some, Spec.add_coe_coe]
    have h : finiteVal s e m + c * 2 ^ k.toInt
        = (finiteVal s (e + -k) m + c) * 2 ^ k.toInt := by
      rw [finiteVal_add, AzInt.toInt_neg, add_mul, mul_assoc, h2k, mul_one]
    rw [h, roundVal_mul_two_zpow]
    rfl

/-- The same for `x − c · 2^k`. -/
theorem shift_roundVal_sub (x : AzFloat) (c : ℝ) (k : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (shiftLeft (roundVal p mode
        ((shiftLeft x (-k)).toVal.bind fun a => Spec.sub a ((c : ℝ) : EReal))).1 k,
      (roundVal p mode
        ((shiftLeft x (-k)).toVal.bind fun a => Spec.sub a ((c : ℝ) : EReal))).2)
      = roundVal p mode (x.toVal.bind fun a => Spec.sub a ((c * 2 ^ k.toInt : ℝ) : EReal)) := by
  have h := shift_roundVal_add x (-c) k p mode
  simp only [Spec.sub, ← EReal.coe_neg, neg_mul] at h ⊢
  exact h

/-- The common shape is correctly rounded. -/
theorem fusedMulRat_eq (opF : AzFloat → AzFloat → ℕ → RoundingMode → AzFloat × Ordering)
    (opR : AzFloat → AzRat → ℕ → RoundingMode → AzFloat × Ordering)
    (opE : EReal → EReal → Option EReal)
    (hS : ∀ (x : AzFloat) (c : ℝ) (k : AzInt) (p : ℕ) [NeZero p] (mode : RoundingMode),
      (shiftLeft (roundVal p mode
          ((shiftLeft x (-k)).toVal.bind fun a => opE a ((c : ℝ) : EReal))).1 k,
        (roundVal p mode
          ((shiftLeft x (-k)).toVal.bind fun a => opE a ((c : ℝ) : EReal))).2)
        = roundVal p mode (x.toVal.bind fun a => opE a ((c * 2 ^ k.toInt : ℝ) : EReal)))
    (hF : ∀ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode),
      opF x y p mode = liftVal₂ opE x y p mode)
    (hR : ∀ (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode),
      opR x q p mode = liftVal (fun a => opE a ((AzRat.toRat q : ℝ) : EReal)) x p mode)
    (x y : AzFloat) (z : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    fusedMulRat opF opR x y z p mode
      = liftVal₂ (fun a b => (Spec.mul b ((AzRat.toRat z : ℝ) : EReal)).bind (opE a))
          x y p mode := by
  unfold fusedMulRat liftVal₂
  cases y with
  | nan =>
    simp only [toVal_nan, Option.bind_none]
    cases x.toVal <;> rfl
  | infinity s =>
    simp only [toVal_infinity, Option.bind_some]
    by_cases hz : z.num = 0
    · have hz0 : (AzRat.toRat z : ℝ) = 0 := (AzRat.toRat_eq_zero_iff z).mpr hz
      rw [ite_eq_left hz, hz0]
      have : Spec.mul (if s then ⊤ else ⊥) (((0 : ℝ) : ℝ) : EReal) = none := by
        cases s <;> simp [Spec.mul]
      rw [this]
      simp only [Option.bind_none]
      cases x.toVal <;> rfl
    · have hz0 : (AzRat.toRat z : ℝ) ≠ 0 := fun h => hz ((AzRat.toRat_eq_zero_iff z).mp h)
      rw [ite_eq_right hz, hF, liftVal₂, toVal_infinity, Spec.mul_inf_coe s _ hz0,
        ← sign_eq_decide_pos z hz]
  | zero =>
    simp only [toVal_zero]
    rw [hR, liftVal]
    have h0 : ((AzRat.toRat (0 : AzRat) : ℝ) : EReal) = ((0 : ℝ) : EReal) := by simp
    have : Spec.mul (0 : EReal) ((AzRat.toRat z : ℝ) : EReal) = some 0 := by
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) by simp, Spec.mul_coe_coe, zero_mul]
    simp only [this, Option.bind_some, h0, EReal.coe_zero]
  | finite s e q m hv =>
    simp only [toVal_finite, Option.bind_some, Spec.mul_coe_coe]
    have hm : m ≠ 0 := ne_zero_of_size_pos (by
      rw [hv.size_eq]; exact lt_of_lt_of_le hv.pos (le_alignedBits q))
    set k := e - (AzNat.ofNat m.size).toAzInt with hk
    have hkI : k.toInt = e.toInt - m.size := by
      rw [hk, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
    have hbase : (AzRat.toRat (AzInt.mkNorm s m).toAzRat : ℝ)
        = (((if s then (m.toNat : ℤ) else -(m.toNat : ℤ)) : ℤ) : ℝ) := by
      rw [AzRat.toRat_toAzRat_int]
      cases s <;> simp [AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false m hm]
    rw [hR, liftVal, hS, AzRat.toRat_mul, Rat.cast_mul, hbase, finiteVal_eq_int_mul, hkI]
    congr 2
    funext a
    congr 2
    ring

/-- **`addMulRatPrecRound` is correctly rounded**: one rounding of `x + y·z`. -/
theorem addMulRatPrecRound_eq_liftVal₂ (x y : AzFloat) (z : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    addMulRatPrecRound x y z p mode
      = liftVal₂ (fun a b => Spec.addMul a b ((AzRat.toRat z : ℝ) : EReal)) x y p mode :=
  fusedMulRat_eq _ _ Spec.add shift_roundVal_add
    (fun x y p _ mode => addPrecRound_eq_liftVal₂ x y p mode)
    (fun x q p _ mode => addRatPrecRound_eq_liftVal x q p mode) x y z p mode

/-- **`subMulRatPrecRound` is correctly rounded**: one rounding of `x − y·z`. -/
theorem subMulRatPrecRound_eq_liftVal₂ (x y : AzFloat) (z : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    subMulRatPrecRound x y z p mode
      = liftVal₂ (fun a b => Spec.subMul a b ((AzRat.toRat z : ℝ) : EReal)) x y p mode :=
  fusedMulRat_eq _ _ Spec.sub shift_roundVal_sub
    (fun x y p _ mode => subPrecRound_eq_liftVal₂ x y p mode)
    (fun x q p _ mode => subRatPrecRound_eq_liftVal x q p mode) x y z p mode

/-! ### Through `Float` -/

/-- `addMulRatFloat64` is the binary64 rounding of `x + y·z`. -/
theorem toVal_addMulRatFloat64 (x y : Float) (z : AzRat) :
    (addMulRatFloat64 x y z).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => Spec.addMul a b ((AzRat.toRat z : ℝ) : EReal)) :=
  toVal_emulate₂Rat addMulRatPrecRound
    (fun a b z => Spec.addMul a b ((AzRat.toRat z : ℝ) : EReal))
    (fun x y z => addMulRatPrecRound_eq_liftVal₂ x y z 53 .Nearest) x y z

/-- `subMulRatFloat64` is the binary64 rounding of `x − y·z`. -/
theorem toVal_subMulRatFloat64 (x y : Float) (z : AzRat) :
    (subMulRatFloat64 x y z).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => Spec.subMul a b ((AzRat.toRat z : ℝ) : EReal)) :=
  toVal_emulate₂Rat subMulRatPrecRound
    (fun a b z => Spec.subMul a b ((AzRat.toRat z : ℝ) : EReal))
    (fun x y z => subMulRatPrecRound_eq_liftVal₂ x y z 53 .Nearest) x y z

end Azurite.AzFloat
