/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzInt.Equiv.Basic
import Mathlib.Data.EReal.Operations

/-!
# The value model of `AzFloat`

`toVal : AzFloat → Option EReal` is the specification every `AzFloat` operation is proven
against: `none` for `NaN`, `⊤`/`⊥` for `±∞`, and otherwise the exact real value.  `NaN`
propagation is `Option.bind`; the exceptional cases of the arithmetic (`∞ − ∞`, `0 · ∞`, …)
are spelled out by the specification functions of the operations, not by `EReal`'s own
conventions (Mathlib sets `⊤ + ⊥ = ⊥`).

This file: `toVal` itself, its values on the constructors and on `mkFinite`, and the sign
operations.
-/

namespace Azurite.AzFloat

/-- The real value of the finite representation `(sign, exponent, significand)`:
`(−1)^(¬sign) · m · 2^(exponent − m.size)`. -/
noncomputable def finiteVal (s : Bool) (e : AzInt) (m : AzNat) : ℝ :=
  (if s then 1 else -1) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size)

/-- The value model: `none` for `NaN`, `⊤`/`⊥` for `±∞`, the exact real otherwise. -/
noncomputable def toVal : AzFloat → Option EReal
  | nan => none
  | infinity s => some (if s then ⊤ else ⊥)
  | zero => some 0
  | finite s e _ m _ => some ((finiteVal s e m : ℝ) : EReal)

@[simp] theorem toVal_nan : toVal nan = none := rfl
@[simp] theorem toVal_infinity (s : Bool) :
    toVal (infinity s) = some (if s then ⊤ else ⊥) := rfl
@[simp] theorem toVal_zero : toVal zero = some 0 := rfl
@[simp] theorem toVal_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat)
    (h : FiniteValid p m) : toVal (finite s e p m h) = some ((finiteVal s e m : ℝ) : EReal) :=
  rfl

/-- On a valid representation the value is `± m · 2^(e − alignedBits p)`. -/
theorem finiteVal_eq_aligned (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (h : FiniteValid p m) :
    finiteVal s e m
      = (if s then 1 else -1) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - alignedBits p) := by
  unfold finiteVal
  rw [h.size_eq]

theorem toNat_ne_zero_of_ne_zero {m : AzNat} (hm : m ≠ 0) : m.toNat ≠ 0 :=
  fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))

theorem size_pos_of_ne_zero {m : AzNat} (hm : m ≠ 0) : 0 < m.size := by
  rw [← AzNat.size_toNat]
  exact Nat.size_pos.mpr (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hm))

@[simp] theorem size_zero : (0 : AzNat).size = 0 := by
  rw [← AzNat.size_toNat, AzNat.toNat_zero, Nat.size_zero]

theorem ne_zero_of_size_pos {m : AzNat} (h : 0 < m.size) : m ≠ 0 := by
  rintro rfl
  simp at h

theorem finiteVal_shiftLeft (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) (k : ℕ) :
    finiteVal s e (m.shiftLeft k) = finiteVal s e m := by
  unfold finiteVal
  have hm0 := toNat_ne_zero_of_ne_zero hm
  have hsize : (m.shiftLeft k).size = m.size + k := by
    rw [← AzNat.size_toNat, AzNat.toNat_shiftLeft, ← Nat.shiftLeft_eq, Nat.size_shiftLeft hm0,
      AzNat.size_toNat]
  rw [hsize, AzNat.toNat_shiftLeft]
  push_cast
  rw [show e.toInt - ((m.size : ℤ) + k) = (e.toInt - m.size) - k by ring,
    zpow_sub₀ (by norm_num), zpow_natCast]
  field_simp

/-- `mkFinite` does not change the value. -/
theorem toVal_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0) :
    toVal (mkFinite s e p m) = some ((finiteVal s e m : ℝ) : EReal) := by
  unfold mkFinite
  rw [dite_eq_right hm]
  simp only [toVal, finiteVal_shiftLeft s e m hm]

@[simp] theorem mkFinite_zero (s : Bool) (e : AzInt) (p : ℕ) : mkFinite s e p 0 = zero := by
  unfold mkFinite
  rw [dite_eq_left rfl]

theorem precision?_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0)
    (h : m.size ≤ p) : precision? (mkFinite s e p m) = some p := by
  unfold mkFinite
  rw [dite_eq_right hm]
  simp only [precision?, Nat.max_eq_left h]

theorem exponent?_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0) :
    exponent? (mkFinite s e p m) = some e := by
  unfold mkFinite
  rw [dite_eq_right hm]
  rfl

theorem sign?_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0) :
    sign? (mkFinite s e p m) = some s := by
  unfold mkFinite
  rw [dite_eq_right hm]
  rfl

/-! ### Sign operations -/

theorem finiteVal_not (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal (!s) e m = -finiteVal s e m := by
  unfold finiteVal
  cases s <;> simp

theorem toVal_neg (x : AzFloat) : toVal (-x) = (toVal x).map fun v => -v := by
  show toVal x.neg = _
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [neg, toVal]
  | zero => simp [neg, toVal]
  | finite s e p m h => simp [neg, toVal, finiteVal_not]

theorem finiteVal_true_eq_abs (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal true e m = |finiteVal s e m| := by
  unfold finiteVal
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, abs_neg]
    rw [abs_of_nonneg (by positivity)]
  · simp only [↓reduceIte, one_mul]
    rw [abs_of_nonneg (by positivity)]

theorem toVal_abs (x : AzFloat) : toVal x.abs = (toVal x).map fun v => max v (-v) := by
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [abs, toVal]
  | zero => simp [abs, toVal]
  | finite s e p m h =>
    simp only [abs, toVal, Option.map_some, Option.some.injEq]
    rw [finiteVal_true_eq_abs s, abs_eq_max_neg, EReal.coe_strictMono.monotone.map_max,
      EReal.coe_neg]

end Azurite.AzFloat
