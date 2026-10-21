/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Rem
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzZMod.Equiv.Pow

/-!
# Equivalence: the remainder

`remPrecRound_eq_liftVal₂ : remPrecRound x y p mode = liftVal₂ Spec.rem x y p mode`, where
`Spec.rem a b = a − b · trunc (a / b)` with `trunc` the integer rounding toward zero
(`round intSet .Down`), `NaN` for an infinite `a` or `b = 0`, and `a` for an infinite `b`.
The exact remainder (`toVal_remExact`) comes from the integer identity
`X − Y · (X / Y) = X mod Y` on the significands brought to a common exponent (`rem_scaled`),
with `AzNat.toNat_shiftLeftMod` for the shift-free reduction.
-/

namespace Azurite

open RoundingTarget

/-- `shiftLeftMod` computes `(a · 2^k) mod n`. -/
theorem AzNat.toNat_shiftLeftMod (a : AzNat) (k : ℕ) (n : AzNat) :
    (a.shiftLeftMod k n).toNat = a.toNat * 2 ^ k % n.toNat := by
  unfold AzNat.shiftLeftMod
  split_ifs with h
  · rw [h, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_zero, Nat.mod_zero]
  · have : NeZero n.toNat := ⟨fun h0 => h (AzNat.toNat_injective (by rw [h0]; rfl))⟩
    set z := AzZMod.ofAzNat n a * AzZMod.pow (AzZMod.ofAzNat n (AzNat.ofNat 2)) k with hz
    have hval : z.val.toNat = (AzZMod.toZMod z).val :=
      (ZMod.val_natCast_of_lt z.isLt).symm
    rw [hval, hz, AzZMod.toZMod_mul, AzZMod.toZMod_pow, AzZMod.toZMod_ofAzNat,
      AzZMod.toZMod_ofAzNat, AzNat.toNat_ofNat, ← Nat.cast_ofNat, ← Nat.cast_pow,
      ← Nat.cast_mul, ZMod.val_natCast]

namespace AzFloat

namespace Spec

open Classical in
/-- The specification of the remainder: `a − b · trunc (a / b)`, `NaN` for an infinite `a` or
`b = 0`, and `a` for an infinite `b`. -/
noncomputable def rem (a b : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ ∨ b = 0 then none
  else if b = ⊤ ∨ b = ⊥ then some a
  else some (((a.toReal - b.toReal * (toInt (round intSet .Down (a.toReal / b.toReal)) : ℝ))
    : ℝ) : EReal)

theorem rem_coe_coe (a b : ℝ) (hb : b ≠ 0) :
    rem a b = some (((a - b * (toInt (round intSet .Down (a / b)) : ℝ)) : ℝ) : EReal) := by
  unfold rem
  rw [ite_eq_right (by simp [EReal.coe_eq_zero, hb]), ite_eq_right (by simp), EReal.toReal_coe,
    EReal.toReal_coe]

end Spec

/-! ### Truncation -/

theorem toInt_round_down (v : ℝ) :
    toInt (round intSet .Down v) = if 0 ≤ v then ⌊v⌋ else ⌈v⌉ := by
  show toInt (if 0 ≤ v then roundFloor intSet v else roundCeiling intSet v) = _
  split_ifs
  · exact toInt_eq_of_val (val_roundFloor_intSet v).symm
  · exact toInt_eq_of_val (val_roundCeiling_intSet v).symm

/-- Truncation of a value below `1` in magnitude is `0`. -/
theorem toInt_round_down_of_abs_lt_one {v : ℝ} (hv : |v| < 1) :
    toInt (round intSet .Down v) = 0 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hv
  rw [toInt_round_down]
  split_ifs with h
  · exact Int.floor_eq_zero_iff.mpr ⟨h, h2⟩
  · exact Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- Truncation of `±(X / Y)` is `±(X / Y)` with natural division. -/
theorem toInt_round_down_sign_div (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (X Y : ℕ) (hY : 0 < Y) :
    (toInt (round intSet .Down (σ * ((X : ℝ) / Y))) : ℝ) = σ * ((X / Y : ℕ) : ℝ) := by
  have hq : (⌊(X : ℝ) / (Y : ℕ)⌋ : ℤ) = ((X / Y : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast, Int.floor_natCast]; rfl
  have hnn : (0 : ℝ) ≤ (X : ℝ) / Y := by positivity
  rcases hσ with rfl | rfl
  · rw [one_mul, one_mul, toInt_round_down, ite_eq_left hnn, hq]; rfl
  · rw [neg_one_mul, neg_one_mul, toInt_round_down]
    rcases eq_or_ne ((X : ℝ) / Y) 0 with h0 | h0
    · rw [h0, neg_zero, ite_eq_left le_rfl, Int.floor_zero]
      have : (X : ℝ) = 0 := by
        rcases div_eq_zero_iff.mp h0 with h | h
        · exact h
        · exact absurd h (by positivity)
      have hX : X = 0 := by exact_mod_cast this
      subst hX
      simp
    · have hneg : ¬ (0 : ℝ) ≤ -((X : ℝ) / Y) :=
        not_le.mpr (neg_neg_of_pos (lt_of_le_of_ne hnn (Ne.symm h0)))
      rw [ite_eq_right hneg, Int.ceil_neg, hq, Int.cast_neg, Int.cast_natCast]

/-- The remainder of `±X · 2^c` by `±Y · 2^c` is `±(X mod Y) · 2^c`, with the sign of the
dividend. -/
theorem rem_scaled (σx σy : ℝ) (hσx : σx = 1 ∨ σx = -1) (hσy : σy = 1 ∨ σy = -1)
    (X Y : ℕ) (hY : 0 < Y) (c : ℤ) :
    σx * X * (2 : ℝ) ^ c - σy * Y * (2 : ℝ) ^ c
        * (toInt (round intSet .Down ((σx * X * (2 : ℝ) ^ c) / (σy * Y * (2 : ℝ) ^ c))) : ℝ)
      = σx * ((X % Y : ℕ) : ℝ) * (2 : ℝ) ^ c := by
  have hY' : (Y : ℝ) ≠ 0 := by exact_mod_cast hY.ne'
  have h2 : (2 : ℝ) ^ c ≠ 0 := zpow_ne_zero _ two_ne_zero
  have hσy2 : σy * σy = 1 := by rcases hσy with rfl | rfl <;> norm_num
  have hσy0 : σy ≠ 0 := by rcases hσy with rfl | rfl <;> norm_num
  have hq : (σx * X * (2 : ℝ) ^ c) / (σy * Y * (2 : ℝ) ^ c)
      = (σx * σy) * ((X : ℝ) / Y) := by
    rw [div_eq_iff (mul_ne_zero (mul_ne_zero hσy0 hY') h2)]
    have hXY : (X : ℝ) / Y * Y = X := div_mul_cancel₀ _ hY'
    linear_combination (-(σx * ((X : ℝ) / Y) * Y * (2 : ℝ) ^ c)) * hσy2
      + (-(σx * (2 : ℝ) ^ c)) * hXY
  have hσ : σx * σy = 1 ∨ σx * σy = -1 := by
    rcases hσx with rfl | rfl <;> rcases hσy with rfl | rfl <;> norm_num
  rw [hq, toInt_round_down_sign_div _ hσ X Y hY]
  have hmod : ((X % Y : ℕ) : ℝ) = X - Y * ((X / Y : ℕ) : ℝ) := by
    have := Nat.mod_add_div X Y
    have h' : ((X % Y + Y * (X / Y) : ℕ) : ℝ) = X := by rw [this]
    push_cast at h'
    linarith
  rw [hmod]
  linear_combination (-(σx * Y * ((X / Y : ℕ) : ℝ) * (2 : ℝ) ^ c)) * hσy2

/-! ### The exact remainder -/

theorem sign_eq_one_or (s : Bool) : (if s then (1 : ℝ) else -1) = 1 ∨
    (if s then (1 : ℝ) else -1) = -1 := by
  cases s <;> simp

/-- A finite value as `±M · 2^a` with `a = e − size M` as an `AzInt` difference. -/
theorem finiteVal_eq_sign_mul (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal s e m = (if s then 1 else -1) * (m.toNat : ℝ)
      * (2 : ℝ) ^ (e - (AzNat.ofNat m.size).toAzInt).toInt := by
  unfold finiteVal
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]

/-- The value of `mkFinite s (c + size r) (size r) r`: `±r · 2^c` (zero for `r = 0`). -/
theorem toVal_mkFinite_scaled (s : Bool) (c : AzInt) (r : AzNat) :
    (mkFinite s (c + (AzNat.ofNat r.size).toAzInt) r.size r).toVal
      = some ((((if s then 1 else -1) * (r.toNat : ℝ) * (2 : ℝ) ^ c.toInt : ℝ)) : EReal) := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [mkFinite_zero, toVal_zero, AzNat.toNat_zero]; simp
  · rw [toVal_mkFinite s _ _ r hr, finiteVal_eq_sign_mul]
    congr 3
    rw [AzInt.toInt_sub, AzInt.toInt_add, toInt_toAzInt]
    ring_nf

/-- **The exact remainder**: `remExact` is `Spec.rem` on the values. -/
theorem toVal_remExact (x y : AzFloat) :
    (remExact x y).toVal = x.toVal.bind fun a => y.toVal.bind fun b => Spec.rem a b := by
  cases x with
  | nan => cases y <;> simp [remExact]
  | infinity s =>
    cases y with
    | nan => simp [remExact]
    | infinity t => cases s <;> cases t <;> simp [remExact, Spec.rem]
    | zero => cases s <;> simp [remExact, Spec.rem]
    | finite t e q m hv => cases s <;> simp [remExact, Spec.rem]
  | zero =>
    cases y with
    | nan => simp [remExact]
    | infinity t => cases t <;> simp [remExact, Spec.rem]
    | zero => simp [remExact, Spec.rem]
    | finite t e q m hv =>
      have hv0 : finiteVal t e m ≠ 0 := finiteVal_ne_zero_of_valid t e hv
      simp only [remExact, toVal_zero, toVal_finite, Option.bind_some]
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, Spec.rem_coe_coe _ _ hv0, zero_div,
        show (0 : ℝ) = ((0 : ℤ) : ℝ) from Int.cast_zero.symm, toInt_round_intCast]
      simp
  | finite sx ex qx mx hx =>
    cases y with
    | nan => simp [remExact]
    | infinity t => cases t <;> simp [remExact, Spec.rem]
    | zero => simp [remExact, Spec.rem]
    | finite sy ey qy my hy =>
      have hx0 : finiteVal sx ex mx ≠ 0 := finiteVal_ne_zero_of_valid sx ex hx
      have hy0 : finiteVal sy ey my ≠ 0 := finiteVal_ne_zero_of_valid sy ey hy
      simp only [toVal_finite, Option.bind_some]
      rw [Spec.rem_coe_coe _ _ hy0]
      have hmx : mx ≠ 0 := fun h => hx0 (by rw [finiteVal_eq_sign_mul, h]; simp)
      have hmy : my ≠ 0 := fun h => hy0 (by rw [finiteVal_eq_sign_mul, h]; simp)
      have hmxN : 0 < mx.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hmx)
      have hmyN : 0 < my.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hmy)
      show (if absLt (finite sx ex qx mx hx) (finite sy ey qy my hy).abs
          then finite sx ex qx mx hx else _).toVal = _
      by_cases hlt : absLt (finite sx ex qx mx hx) (finite sy ey qy my hy).abs = true
      · -- `|x| < |y|`: the remainder is `x`
        rw [ite_eq_left hlt, toVal_finite]
        have habs := (absLt_iff rfl (isFinite_of_toVal_coe
          (toVal_abs_of_isFinite (x := finite sy ey qy my hy) rfl))).mp hlt
        rw [fval_of_toVal_coe (toVal_abs_of_isFinite (x := finite sy ey qy my hy) rfl)] at habs
        simp only [fval] at habs
        have : |finiteVal sx ex mx / finiteVal sy ey my| < 1 := by
          rw [abs_div, div_lt_one (abs_pos.mpr hy0)]; exact habs
        rw [toInt_round_down_of_abs_lt_one this]
        simp
      · rw [ite_eq_right hlt]
        simp only []
        set ax := ex - (AzNat.ofNat mx.size).toAzInt with hax
        set ay := ey - (AzNat.ofNat my.size).toAzInt with hay
        have hvx := finiteVal_eq_sign_mul sx ex mx
        have hvy := finiteVal_eq_sign_mul sy ey my
        rw [← hax] at hvx
        rw [← hay] at hvy
        have hσx := sign_eq_one_or sx
        have hσy := sign_eq_one_or sy
        by_cases hle : ay ≤ ax
        · rw [ite_eq_left hle, toVal_mkFinite_scaled]
          set k := (ax - ay).abs.toNat with hk
          have hkI : (k : ℤ) = ax.toInt - ay.toInt := by
            rw [hk, AzInt.abs_toNat_eq, AzInt.toInt_sub,
              abs_of_nonneg (by have := (AzInt.le_iff_toInt_le ay ax).mp hle; omega)]
          have hsplit : (2 : ℝ) ^ ax.toInt = (2 : ℝ) ^ k * (2 : ℝ) ^ ay.toInt := by
            rw [← zpow_natCast, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), hkI]
            congr 1; ring
          rw [AzNat.toNat_shiftLeftMod]
          have := rem_scaled _ _ hσx hσy (mx.toNat * 2 ^ k) my.toNat hmyN ay.toInt
          push_cast at this
          have hX : (if sx then (1 : ℝ) else -1) * (mx.toNat : ℝ)
                * ((2 : ℝ) ^ k * 2 ^ ay.toInt)
              = (if sx then (1 : ℝ) else -1) * ((mx.toNat : ℝ) * 2 ^ k) * 2 ^ ay.toInt := by
            ring
          rw [hvx, hvy, hsplit, hX]
          exact congrArg (fun v : ℝ => some ((v : ℝ) : EReal)) this.symm
        · rw [ite_eq_right hle, toVal_mkFinite_scaled]
          set k := (ay - ax).abs.toNat with hk
          have hkI : (k : ℤ) = ay.toInt - ax.toInt := by
            rw [hk, AzInt.abs_toNat_eq, AzInt.toInt_sub,
              abs_of_nonneg (by
                have := (AzInt.le_iff_toInt_le ay ax).not.mp hle; push Not at this; omega)]
          have hsplit : (2 : ℝ) ^ ay.toInt = (2 : ℝ) ^ k * (2 : ℝ) ^ ax.toInt := by
            rw [← zpow_natCast, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), hkI]
            congr 1; ring
          rw [AzNat.toNat_mod, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
          have := rem_scaled _ _ hσx hσy mx.toNat (my.toNat * 2 ^ k) (by positivity) ax.toInt
          push_cast at this
          have hY : (if sy then (1 : ℝ) else -1) * (my.toNat : ℝ)
                * ((2 : ℝ) ^ k * 2 ^ ax.toInt)
              = (if sy then (1 : ℝ) else -1) * ((my.toNat : ℝ) * 2 ^ k) * 2 ^ ax.toInt := by
            ring
          rw [hvx, hvy, hsplit, hY]
          exact congrArg (fun v : ℝ => some ((v : ℝ) : EReal)) this.symm

/-- **The remainder is correctly rounded.** -/
theorem remPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    remPrecRound x y p mode = liftVal₂ Spec.rem x y p mode := by
  unfold remPrecRound liftVal₂
  rw [setPrecRound_eq_liftE]
  unfold liftE liftVal
  rw [toVal_remExact]
  cases x.toVal <;> simp

end AzFloat

end Azurite
