/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzInt.Equiv.DivRound
import Azurite.AzInt.Equiv.Parity
import Azurite.AzInt.Equiv.ShiftRight
import Azurite.AzNat.Equiv.IsMultipleOfPow2
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzInt.Equiv.ShiftRight
import Mathlib.Analysis.Real.Sqrt
import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.AzNat.Equiv.Sub

/-!
# Correctness of addition and subtraction

The specification `Spec.add` is `EReal` addition with `∞ + (−∞)` undefined; the theorem
`addPrecRound_eq_liftVal₂` says `addPrecRound x y p mode = liftVal₂ Spec.add x y p mode`.
The proof goes through `roundScaled_eq_roundVal` (rounding an exact `±S · 2^w` is `roundVal`),
the exact near case, and the far case via `round_congr_cell`: two reals with no integer or
half-integer strictly between them round identically in every mode, with equal comparison
tags.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real addition, undefined (`NaN`) for `∞ + (−∞)`. -/
noncomputable def add (a b : EReal) : Option EReal :=
  if (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) then none else some (a + b)

/-- Extended-real subtraction. -/
noncomputable def sub (a b : EReal) : Option EReal := add a (-b)

open Classical in
/-- Extended-real multiplication, undefined (`NaN`) for `0 · (±∞)`. -/
noncomputable def mul (a b : EReal) : Option EReal :=
  if (a = 0 ∧ (b = ⊤ ∨ b = ⊥)) ∨ (b = 0 ∧ (a = ⊤ ∨ a = ⊥)) then none else some (a * b)

theorem add_coe_coe (x y : ℝ) : add (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
  unfold add
  rw [ite_eq_right (by simp), EReal.coe_add]

open Classical in
/-- Extended-real division: `∞ / ∞` and `0 / 0` are undefined (`NaN`); `a / 0 = ±∞` with the sign
of `a` (not Mathlib's `a / 0 = 0`); otherwise `EReal` division, whose `a / ∞ = 0` and
`∞ / a = ±∞` are the float conventions. -/
noncomputable def div (a b : EReal) : Option EReal :=
  if ((a = ⊤ ∨ a = ⊥) ∧ (b = ⊤ ∨ b = ⊥)) ∨ (a = 0 ∧ b = 0) then none
  else if b = 0 then some (if 0 < a then ⊤ else ⊥)
  else some (a / b)

theorem div_coe_coe (x y : ℝ) (hy : y ≠ 0) :
    div (x : EReal) (y : EReal) = some ((x / y : ℝ) : EReal) := by
  unfold div
  rw [ite_eq_right (by simp [hy]), ite_eq_right (by simpa using hy), EReal.coe_div]

theorem div_coe_zero (x : ℝ) (hx : x ≠ 0) :
    div (x : EReal) 0 = some (if 0 < x then ⊤ else ⊥) := by
  unfold div
  rw [ite_eq_right (by simp [hx]), ite_eq_left rfl]
  simp [EReal.coe_pos]

theorem div_inf_coe (s : Bool) (r : ℝ) (hr : r ≠ 0) :
    div (if s then ⊤ else ⊥) (r : EReal) = some (if (s == decide (0 < r)) then ⊤ else ⊥) := by
  unfold div
  rw [ite_eq_right (by cases s <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero, hr]),
    ite_eq_right (by simpa using hr)]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [decide_eq_false (not_lt.mpr h.le)]
    have h' : (r : EReal) < 0 := EReal.coe_neg'.mpr h
    cases s
    · simp [EReal.bot_div_of_neg_ne_bot h' (EReal.coe_ne_bot r)]
    · simp [EReal.top_div_of_neg_ne_bot h' (EReal.coe_ne_bot r)]
  · rw [decide_eq_true h]
    have h' : (0 : EReal) < r := EReal.coe_pos.mpr h
    cases s
    · simp [EReal.bot_div_of_pos_ne_top h' (EReal.coe_ne_top r)]
    · simp [EReal.top_div_of_pos_ne_top h' (EReal.coe_ne_top r)]

theorem div_inf_zero (s : Bool) : div (if s then ⊤ else ⊥) 0 = some (if s then ⊤ else ⊥) := by
  unfold div
  rw [ite_eq_right (by cases s <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero]), ite_eq_left rfl]
  cases s <;> simp [EReal.zero_lt_top]

theorem div_coe_inf (r : ℝ) (t : Bool) : div (r : EReal) (if t then ⊤ else ⊥) = some 0 := by
  unfold div
  rw [ite_eq_right (by cases t <;> simp),
    ite_eq_right (by cases t <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero])]
  cases t <;> simp [EReal.div_top, EReal.div_bot]

theorem div_zero_coe (r : ℝ) (hr : r ≠ 0) : div 0 (r : EReal) = some 0 := by
  unfold div
  rw [ite_eq_right (by simp [EReal.zero_ne_top, EReal.zero_ne_bot, hr]),
    ite_eq_right (by simpa using hr), EReal.zero_div]

theorem div_zero_inf (t : Bool) : div 0 (if t then ⊤ else ⊥) = some 0 := by
  unfold div
  rw [ite_eq_right (by cases t <;> simp [EReal.zero_ne_top, EReal.zero_ne_bot]),
    ite_eq_right (by cases t <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero])]
  cases t <;> simp [EReal.div_top, EReal.div_bot]

open Classical in
/-- Extended-real square root: undefined (`NaN`) on negatives (including `−∞`), `√∞ = ∞`. -/
noncomputable def sqrt (a : EReal) : Option EReal :=
  if a < 0 then none else if a = ⊤ then some ⊤ else some ((Real.sqrt a.toReal : ℝ) : EReal)

theorem sqrt_coe (r : ℝ) (hr : 0 ≤ r) : sqrt (r : EReal) = some ((Real.sqrt r : ℝ) : EReal) := by
  unfold sqrt
  rw [ite_eq_right (not_lt.mpr (EReal.coe_nonneg.mpr hr)), ite_eq_right (EReal.coe_ne_top r),
    EReal.toReal_coe]

theorem sqrt_coe_neg (r : ℝ) (hr : r < 0) : sqrt (r : EReal) = none := by
  unfold sqrt
  rw [ite_eq_left (EReal.coe_neg'.mpr hr)]

@[simp] theorem sqrt_top : sqrt ⊤ = some ⊤ := by
  unfold sqrt
  rw [ite_eq_right (not_lt.mpr le_top), ite_eq_left rfl]

@[simp] theorem sqrt_bot : sqrt ⊥ = none := by
  unfold sqrt
  rw [ite_eq_left EReal.bot_lt_zero]

@[simp] theorem sqrt_zero : sqrt 0 = some 0 := by
  rw [← EReal.coe_zero, sqrt_coe 0 le_rfl, Real.sqrt_zero]

open Classical in
/-- Extended-real reciprocal square root: undefined (`NaN`) on negatives (including `−∞`),
`0 ↦ ∞`, `∞ ↦ 0`. -/
noncomputable def rsqrt (a : EReal) : Option EReal :=
  if a < 0 then none else if a = 0 then some ⊤ else if a = ⊤ then some 0
  else some (((Real.sqrt a.toReal)⁻¹ : ℝ) : EReal)

theorem rsqrt_coe (r : ℝ) (hr : 0 < r) :
    rsqrt (r : EReal) = some (((Real.sqrt r)⁻¹ : ℝ) : EReal) := by
  unfold rsqrt
  rw [ite_eq_right (not_lt.mpr (EReal.coe_nonneg.mpr hr.le)),
    ite_eq_right (fun h => hr.ne' (EReal.coe_eq_zero.mp h)), ite_eq_right (EReal.coe_ne_top r),
    EReal.toReal_coe]

theorem rsqrt_coe_neg (r : ℝ) (hr : r < 0) : rsqrt (r : EReal) = none := by
  unfold rsqrt
  rw [ite_eq_left (EReal.coe_neg'.mpr hr)]

@[simp] theorem rsqrt_zero : rsqrt 0 = some ⊤ := by
  unfold rsqrt
  rw [ite_eq_right (lt_irrefl 0), ite_eq_left rfl]

@[simp] theorem rsqrt_top : rsqrt ⊤ = some 0 := by
  unfold rsqrt
  rw [ite_eq_right (not_lt.mpr le_top), ite_eq_right EReal.top_ne_zero, ite_eq_left rfl]

@[simp] theorem rsqrt_bot : rsqrt ⊥ = none := by
  unfold rsqrt
  rw [ite_eq_left EReal.bot_lt_zero]

theorem mul_coe_coe (x y : ℝ) : mul (x : EReal) (y : EReal) = some ((x * y : ℝ) : EReal) := by
  unfold mul
  rw [ite_eq_right (by simp), EReal.coe_mul]

theorem mul_inf_coe (s : Bool) (r : ℝ) (hr : r ≠ 0) :
    mul (if s then ⊤ else ⊥) (r : EReal) = some (if (s == decide (0 < r)) then ⊤ else ⊥) := by
  unfold mul
  rw [ite_eq_right (by cases s <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero, hr])]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [decide_eq_false (not_lt.mpr h.le)]
    cases s
    · simp [EReal.bot_mul_coe_of_neg h]
    · simp [EReal.top_mul_coe_of_neg h]
  · rw [decide_eq_true h]
    cases s
    · simp [EReal.bot_mul_coe_of_pos h]
    · simp [EReal.top_mul_coe_of_pos h]

theorem mul_coe_inf (r : ℝ) (hr : r ≠ 0) (t : Bool) :
    mul (r : EReal) (if t then ⊤ else ⊥) = some (if (decide (0 < r) == t) then ⊤ else ⊥) := by
  unfold mul
  rw [ite_eq_right (by cases t <;> simp [EReal.top_ne_zero, EReal.bot_ne_zero, hr])]
  rcases lt_or_gt_of_ne hr with h | h
  · rw [decide_eq_false (not_lt.mpr h.le)]
    cases t
    · simp [EReal.coe_mul_bot_of_neg h]
    · simp [EReal.coe_mul_top_of_neg h]
  · rw [decide_eq_true h]
    cases t
    · simp [EReal.coe_mul_bot_of_pos h]
    · simp [EReal.coe_mul_top_of_pos h]

end Spec

/-! ### Values with an arbitrary significand -/

/-- `finiteVal s e m` for any nonzero `m` lies in `[2^(e−1), 2^e)` in absolute value. -/
theorem abs_finiteVal_bounds' (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) :
    (2 : ℝ) ^ (e.toInt - 1) ≤ |finiteVal s e m| ∧ |finiteVal s e m| < (2 : ℝ) ^ e.toInt := by
  have hm0 := toNat_ne_zero_of_ne_zero hm
  have hlo : 2 ^ (m.size - 1) ≤ m.toNat := by
    rw [← Nat.lt_size, AzNat.size_toNat]; have := size_pos_of_ne_zero hm; omega
  have hhi : m.toNat < 2 ^ m.size := by rw [← Nat.size_le, AzNat.size_toNat]
  have hsz := size_pos_of_ne_zero hm
  have habs : |finiteVal s e m| = (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size) := by
    unfold finiteVal
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
    cases s <;> simp [abs_mul, abs_of_pos h2]
  rw [habs]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
  constructor
  · have hlo' : (2 : ℝ) ^ (m.size - 1) ≤ m.toNat := by exact_mod_cast hlo
    calc (2 : ℝ) ^ (e.toInt - 1)
        = (2 : ℝ) ^ ((m.size - 1 : ℕ) : ℤ) * 2 ^ (e.toInt - m.size) := by
          rw [← zpow_add₀ (by norm_num)]; congr 1; rw [Nat.cast_sub hsz]; ring
      _ ≤ (m.toNat : ℝ) * 2 ^ (e.toInt - m.size) := by
          rw [zpow_natCast]; exact mul_le_mul_of_nonneg_right hlo' h2.le
  · have hhi' : (m.toNat : ℝ) < (2 : ℝ) ^ m.size := by exact_mod_cast hhi
    calc (m.toNat : ℝ) * 2 ^ (e.toInt - m.size)
        < (2 : ℝ) ^ m.size * 2 ^ (e.toInt - m.size) := mul_lt_mul_of_pos_right hhi' h2
      _ = (2 : ℝ) ^ e.toInt := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring

theorem log_abs_finiteVal' (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) :
    Int.log 2 |finiteVal s e m| = e.toInt - 1 := by
  obtain ⟨hlo, hhi⟩ := abs_finiteVal_bounds' s e m hm
  have hpos : 0 < |finiteVal s e m| := lt_of_lt_of_le (zpow_pos (by norm_num) _) hlo
  apply le_antisymm
  · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by simpa using hhi)
    omega
  · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos).mp (by simpa using hlo)

theorem finiteVal_true_pos' (e : AzInt) (m : AzNat) (hm : m ≠ 0) : 0 < finiteVal true e m :=
  (finiteVal_pos_iff true e m hm).mpr rfl

theorem finiteVal_ne_zero' (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) :
    finiteVal s e m ≠ 0 := by
  intro h
  have := (abs_finiteVal_bounds' s e m hm).1
  rw [h, abs_zero] at this
  exact absurd this (not_le.mpr (zpow_pos (by norm_num) _))

theorem precScale_finiteVal' (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) (p : ℕ) :
    precScale 2 p (finiteVal s e m) = (2 : ℝ) ^ (e.toInt - p) := by
  unfold precScale
  rw [log_abs_finiteVal' s e m hm]
  push_cast
  congr 1
  ring

/-- `±S · 2^w` as a `finiteVal` at the exponent `w + |S|`. -/
theorem finiteVal_scaled (s : Bool) (S : AzNat) (w : AzInt) :
    finiteVal s (w + (AzNat.ofNat S.size).toAzInt) S
      = (if s then 1 else -1) * (S.toNat : ℝ) * (2 : ℝ) ^ w.toInt := by
  unfold finiteVal
  rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat, add_sub_cancel_right]

/-! ### Rounding an exact scaled integer -/

/-- `roundScaled` is `roundVal` of the exact value. -/
theorem roundScaled_eq_roundVal (s : Bool) (S : AzNat) (w : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    roundScaled s S w p mode
      = roundVal p mode (some (((if s then 1 else -1) * (S.toNat : ℝ) * (2 : ℝ) ^ w.toInt : ℝ)
          : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold roundScaled
  rw [ite_eq_right hp.ne']
  by_cases hS : S = 0
  · rw [ite_eq_left hS, hS]
    simp only [AzNat.toNat_zero, Nat.cast_zero, mul_zero, zero_mul, EReal.coe_zero]
    exact (roundVal_of_toVal p mode zero 0 (Or.inr rfl) rfl).symm
  · rw [ite_eq_right hS]
    simp only []
    set ex := w + (AzNat.ofNat S.size).toAzInt with hex
    have hval : finiteVal s ex S = (if s then 1 else -1) * (S.toNat : ℝ) * (2 : ℝ) ^ w.toInt :=
      finiteVal_scaled s S w
    rw [← hval]
    by_cases hle : S.size ≤ p
    · rw [ite_eq_left hle]
      symm
      refine roundVal_of_toVal p mode _ _ (Or.inl (precision?_mkFinite _ _ _ _ hS hle)) ?_
      rw [toVal_mkFinite _ _ _ _ hS]
    · rw [ite_eq_right hle]
      have hlt : p < S.size := not_le.mp hle
      have hexI : ex.toInt = w.toInt + S.size := by
        show (w + (AzNat.ofNat S.size).toAzInt).toInt = _
        rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]
      have hv0 : finiteVal s ex S ≠ 0 := finiteVal_ne_zero' s ex S hS
      have hscale : precScale 2 p (finiteVal s ex S) = (2 : ℝ) ^ (ex.toInt - p) :=
        precScale_finiteVal' s ex S hS p
      have hz : ((AzInt.mkNorm s S).toInt : ℝ) = (if s then 1 else -1) * (S.toNat : ℝ) := by
        rcases Bool.eq_false_or_eq_true s with hs | hs <;>
          simp [hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false S hS]
      have hvu : finiteVal s ex S / (2 : ℝ) ^ (ex.toInt - p)
          = ((AzInt.mkNorm s S).toInt : ℝ) / (2 : ℝ) ^ (S.size - p) := by
        rw [hval, hz, hexI]
        have h : (2 : ℝ) ^ w.toInt / 2 ^ (w.toInt + S.size - p) = 1 / (2 : ℝ) ^ (S.size - p) := by
          rw [div_eq_div_iff (zpow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero), one_mul,
            ← zpow_natCast, ← zpow_add₀ two_ne_zero]
          congr 1
          rw [Nat.cast_sub hlt.le]
          ring
        rw [mul_div_assoc, h]
        ring
      set v := finiteVal s ex S with hv_def
      set u : ℝ := (2 : ℝ) ^ (ex.toInt - p) with hu_def
      have hu : 0 < u := zpow_pos (by norm_num) _
      set r := AzInt.shiftRightRound (AzInt.mkNorm s S) mode (S.size - p) with hr_def
      have hr := AzInt.toInt_shiftRightRound (AzInt.mkNorm s S) mode (S.size - p)
      rw [← hvu, ← hr_def] at hr
      have hrI : toInt (round intSet mode (v / u)) = r.1.toInt := toInt_eq_of_val hr
      have hround : (round (floatSet p) mode v).val = (((r.1.toInt : ℝ) * u : ℝ) : EReal) := by
        rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hrI]
      obtain ⟨hlo, hhi⟩ := abs_div_precScale_bounds (b := 2) (p := p) v hv0
      rw [hscale] at hlo hhi
      obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds p hp mode (v / u) (by simpa using hlo)
        (by simpa using hhi)
      rw [hrI] at hb1 hb2
      have habs : (r.1.abs.toNat : ℤ) = |r.1.toInt| := by
        unfold AzInt.toInt; cases r.1.sign <;> simp
      have hlo' : 2 ^ (p - 1) ≤ r.1.abs.toNat := by
        have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ (r.1.abs.toNat : ℤ) := by rw [habs]; exact hb1
        exact_mod_cast this
      have hhi' : r.1.abs.toNat ≤ 2 ^ p := by
        have : (r.1.abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by rw [habs]; exact hb2
        exact_mod_cast this
      obtain ⟨hRval, hRprec⟩ := normalize_spec r.1 p hp ex hlo' hhi'
      have hR : (if r.1.abs.size = p + 1 then
            (mkFinite r.1.sign (ex + 1) p (r.1.abs.shiftRight 1), r.2)
          else (mkFinite r.1.sign ex p r.1.abs, r.2))
          = ((if r.1.abs.size = p + 1 then mkFinite r.1.sign (ex + 1) p (r.1.abs.shiftRight 1)
            else mkFinite r.1.sign ex p r.1.abs), r.2) := by
        split_ifs <;> rfl
      rw [hR]
      symm
      refine Prod.ext ?_ ?_
      · exact toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
          (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
      · show (roundVal p mode (some (v : EReal))).2 = r.2
        rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, hr_def,
          AzInt.snd_shiftRightRound, ← hr_def, ← hvu]
        conv_rhs => rw [← compare_mul_right_pos _ _ u hu, div_mul_cancel₀ _ hu.ne']

/-! ### Rounding is constant on cells -/

/-- Two reals strictly between the same consecutive multiples of `1/2` round to the same
integer in every mode (no tie can occur). -/
theorem toInt_round_intSet_congr (mode : RoundingMode) (m : ℤ) (y y' : ℝ)
    (hy : (m : ℝ) / 2 < y ∧ y < ((m : ℝ) + 1) / 2)
    (hy' : (m : ℝ) / 2 < y' ∧ y' < ((m : ℝ) + 1) / 2) :
    toInt (round intSet mode y) = toInt (round intSet mode y') := by
  set n : ℤ := m / 2 with hn
  have hn1 : 2 * n ≤ m := by omega
  have hn2 : m < 2 * n + 2 := by omega
  have hn1' : (n : ℝ) ≤ (m : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : n * 2 ≤ m)
  have hn2' : ((m : ℝ) + 1) / 2 ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (by omega : m + 1 ≤ (n + 1) * 2)
  have hfl : ∀ z : ℝ, (m : ℝ) / 2 < z → z < ((m : ℝ) + 1) / 2 → ⌊z⌋ = n := fun z h1 h2 =>
    Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  have hce : ∀ z : ℝ, (m : ℝ) / 2 < z → z < ((m : ℝ) + 1) / 2 → ⌈z⌉ = n + 1 := fun z h1 h2 =>
    Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hF : ∀ z : ℝ, toInt (roundFloor intSet z) = ⌊z⌋ := fun z =>
    toInt_eq_of_val (val_roundFloor_intSet z).symm
  have hC : ∀ z : ℝ, toInt (roundCeiling intSet z) = ⌈z⌉ := fun z =>
    toInt_eq_of_val (val_roundCeiling_intSet z).symm
  have hsign : 0 ≤ y ↔ 0 ≤ y' := by
    rcases le_or_gt 0 m with hm | hm
    · have : (0 : ℝ) ≤ m := by exact_mod_cast hm
      constructor <;> intro <;> linarith
    · have : (m : ℝ) + 1 ≤ 0 := by exact_mod_cast (by omega : m + 1 ≤ 0)
      constructor <;> intro <;> linarith
  -- the nearest case: the floor is nearer when `m` is even, the ceiling when it is odd
  have hnear : ∀ z : ℝ, (m : ℝ) / 2 < z → z < ((m : ℝ) + 1) / 2 →
      toInt (round intSet .Nearest z) = if Even m then n else n + 1 := by
    intro z h1 h2
    have hfz := hfl z h1 h2
    have hcz := hce z h1 h2
    show toInt (match compare (((z : ℝ) : EReal) - (roundFloor intSet z).val)
        ((roundCeiling intSet z).val - ((z : ℝ) : EReal)) with
      | .lt => roundFloor intSet z
      | .gt => roundCeiling intSet z
      | .eq => tiebreak (roundFloor intSet z) (roundCeiling intSet z)) = _
    rw [val_roundFloor_intSet, val_roundCeiling_intSet, hfz, hcz, ← EReal.coe_sub,
      ← EReal.coe_sub, compare_coe_coe]
    rcases Int.even_or_odd m with hev | hod
    · obtain ⟨q, hq⟩ := hev
      have hnq : n = q := by omega
      have hlt : z - (n : ℝ) < ((n + 1 : ℤ) : ℝ) - z := by
        have : (m : ℝ) = 2 * q := by exact_mod_cast (by omega : m = 2 * q)
        push_cast; rw [hnq]; linarith
      rw [compare_lt_iff_lt.mpr hlt]
      simp only [hF, hfz, ite_eq_left (show Even m from ⟨q, hq⟩)]
    · obtain ⟨q, hq⟩ := hod
      have hnq : n = q := by omega
      have hgt : ((n + 1 : ℤ) : ℝ) - z < z - (n : ℝ) := by
        have : (m : ℝ) = 2 * q + 1 := by exact_mod_cast hq
        push_cast; rw [hnq]; linarith
      rw [compare_gt_iff_gt.mpr hgt]
      simp only [hC, hcz, ite_eq_right (Int.not_even_iff_odd.mpr ⟨q, hq⟩)]
  cases mode with
  | Floor =>
    show toInt (roundFloor intSet y) = toInt (roundFloor intSet y')
    rw [hF, hF, hfl y hy.1 hy.2, hfl y' hy'.1 hy'.2]
  | Ceiling =>
    show toInt (roundCeiling intSet y) = toInt (roundCeiling intSet y')
    rw [hC, hC, hce y hy.1 hy.2, hce y' hy'.1 hy'.2]
  | Down =>
    show toInt (if 0 ≤ y then roundFloor intSet y else roundCeiling intSet y)
      = toInt (if 0 ≤ y' then roundFloor intSet y' else roundCeiling intSet y')
    by_cases h0 : 0 ≤ y
    · rw [ite_eq_left h0, ite_eq_left (hsign.mp h0), hF, hF, hfl y hy.1 hy.2, hfl y' hy'.1 hy'.2]
    · rw [ite_eq_right h0, ite_eq_right (fun h => h0 (hsign.mpr h)), hC, hC, hce y hy.1 hy.2,
        hce y' hy'.1 hy'.2]
  | Up =>
    show toInt (if 0 ≤ y then roundCeiling intSet y else roundFloor intSet y)
      = toInt (if 0 ≤ y' then roundCeiling intSet y' else roundFloor intSet y')
    by_cases h0 : 0 ≤ y
    · rw [ite_eq_left h0, ite_eq_left (hsign.mp h0), hC, hC, hce y hy.1 hy.2, hce y' hy'.1 hy'.2]
    · rw [ite_eq_right h0, ite_eq_right (fun h => h0 (hsign.mpr h)), hF, hF, hfl y hy.1 hy.2,
        hfl y' hy'.1 hy'.2]
  | Nearest => rw [hnear y hy.1 hy.2, hnear y' hy'.1 hy'.2]

/-- No integer lies strictly inside `(m/2, (m+1)/2)`, so every integer compares the same way
with two reals in that cell. -/
theorem compare_int_congr (m R : ℤ) (y y' : ℝ)
    (hy : (m : ℝ) / 2 < y ∧ y < ((m : ℝ) + 1) / 2)
    (hy' : (m : ℝ) / 2 < y' ∧ y' < ((m : ℝ) + 1) / 2) :
    compare (R : ℝ) y = compare (R : ℝ) y' := by
  rcases le_or_gt (2 * R) m with h | h
  · have hR : (R : ℝ) ≤ (m : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : R * 2 ≤ m)
    rw [compare_lt_iff_lt.mpr (by linarith), compare_lt_iff_lt.mpr (by linarith)]
  · have hR : ((m : ℝ) + 1) / 2 ≤ (R : ℝ) := by
      rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (by omega : m + 1 ≤ R * 2)
    rw [compare_gt_iff_gt.mpr (by linarith), compare_gt_iff_gt.mpr (by linarith)]

/-- Positive reals in the same open cell `(k·2^j, (k+1)·2^j)` with `k ≥ 1` have the same
binary logarithm: no power of two lies strictly inside such a cell. -/
theorem log_eq_of_cell (j k : ℤ) (hk : 1 ≤ k) (v v' : ℝ)
    (hv : (k : ℝ) * 2 ^ j < v ∧ v < ((k : ℝ) + 1) * 2 ^ j)
    (hv' : (k : ℝ) * 2 ^ j < v' ∧ v' < ((k : ℝ) + 1) * 2 ^ j) :
    Int.log 2 v = Int.log 2 v' := by
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) _
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < v := lt_of_lt_of_le (by positivity) hv.1.le
  have hpos' : 0 < v' := lt_of_lt_of_le (by positivity) hv'.1.le
  -- `2^i ≤ v ↔ 2^i ≤ v'` for every `i`
  have key : ∀ (a b : ℝ), (k : ℝ) * 2 ^ j < a → a < ((k : ℝ) + 1) * 2 ^ j →
      (k : ℝ) * 2 ^ j < b → b < ((k : ℝ) + 1) * 2 ^ j → ∀ i : ℤ,
      (2 : ℝ) ^ i ≤ a → (2 : ℝ) ^ i ≤ b := by
    intro a b ha1 ha2 hb1 hb2 i hi
    rcases le_or_gt j i with hji | hji
    · -- `2^i = 2^(i−j) · 2^j` with `2^(i−j)` an integer
      obtain ⟨d, hd⟩ : ∃ d : ℕ, i = j + d := ⟨(i - j).toNat, by omega⟩
      have hpow : (2 : ℝ) ^ i = ((2 ^ d : ℕ) : ℝ) * 2 ^ j := by
        rw [hd, zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
      rw [hpow] at hi ⊢
      rcases le_or_gt ((2 ^ d : ℕ) : ℤ) k with hdk | hdk
      · have : ((2 ^ d : ℕ) : ℝ) ≤ k := by exact_mod_cast hdk
        exact le_trans (mul_le_mul_of_nonneg_right this h2j.le) hb1.le
      · have : (k : ℝ) + 1 ≤ ((2 ^ d : ℕ) : ℝ) := by
          exact_mod_cast (by omega : k + 1 ≤ ((2 ^ d : ℕ) : ℤ))
        exact absurd hi (not_le.mpr (lt_of_lt_of_le ha2 (mul_le_mul_of_nonneg_right this h2j.le)))
    · have : (2 : ℝ) ^ i ≤ 2 ^ j := zpow_le_zpow_right₀ (by norm_num) hji.le
      calc (2 : ℝ) ^ i ≤ 2 ^ j := this
        _ ≤ (k : ℝ) * 2 ^ j := le_mul_of_one_le_left h2j.le hk'
        _ ≤ b := hb1.le
  have h1 : (2 : ℝ) ^ Int.log 2 v ≤ v := by
    simpa using Int.zpow_log_le_self (b := 2) (by norm_num) hpos
  have h1' : (2 : ℝ) ^ Int.log 2 v' ≤ v' := by
    simpa using Int.zpow_log_le_self (b := 2) (by norm_num) hpos'
  apply le_antisymm
  · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos').mp
      (by simpa using key v v' hv.1 hv.2 hv'.1 hv'.2 (Int.log 2 v) h1)
  · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos).mp
      (by simpa using key v' v hv'.1 hv'.2 hv.1 hv.2 (Int.log 2 v') h1')

/-- Rounding to precision `p` (and the comparison tag) is constant on an open cell
`(k·2^j, (k+1)·2^j)` whose width is at most half an ulp of the destination grid. -/
theorem roundVal_congr_cell (p : ℕ) [NeZero p] (mode : RoundingMode) (j k : ℤ) (v v' : ℝ)
    (hv : (k : ℝ) * 2 ^ j < v ∧ v < ((k : ℝ) + 1) * 2 ^ j)
    (hv' : (k : ℝ) * 2 ^ j < v' ∧ v' < ((k : ℝ) + 1) * 2 ^ j)
    (hlog : Int.log 2 |v| = Int.log 2 |v'|) (hj : j ≤ Int.log 2 |v| - p) :
    roundVal p mode (some (v : EReal)) = roundVal p mode (some (v' : EReal)) := by
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) _
  -- neither value is zero
  have hne : ∀ z : ℝ, (k : ℝ) * 2 ^ j < z → z < ((k : ℝ) + 1) * 2 ^ j → z ≠ 0 := by
    intro z h1 h2 hz
    rw [hz] at h1 h2
    rcases le_or_gt 0 k with hk | hk
    · have : (0 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    · have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (by omega : k + 1 ≤ 0)
      nlinarith
  have hv0 := hne v hv.1 hv.2
  have hv'0 := hne v' hv'.1 hv'.2
  set L := Int.log 2 |v| with hL
  set u : ℝ := (2 : ℝ) ^ (L - p + 1) with hu_def
  have hu : 0 < u := zpow_pos (by norm_num) _
  have hscale : precScale 2 p v = u := by
    show ((2 : ℕ) : ℝ) ^ (L - p + 1) = u
    rw [hu_def]; norm_num
  have hscale' : precScale 2 p v' = u := by
    show ((2 : ℕ) : ℝ) ^ (Int.log 2 |v'| - p + 1) = u
    rw [← hlog, hu_def]; norm_num
  -- the cell in units of `u`: between consecutive multiples of `1/2`
  obtain ⟨t, ht⟩ : ∃ t : ℕ, L - p - j = t := ⟨(L - p - j).toNat, by omega⟩
  set c : ℝ := (2 : ℝ) ^ t with hc_def
  have hc : 0 < c := by positivity
  have hu_eq : u = 2 ^ j * (2 * c) := by
    rw [hu_def, hc_def, ← zpow_natCast, show (2 : ℝ) * 2 ^ (t : ℤ) = 2 ^ ((t : ℤ) + 1) by
      rw [zpow_add_one₀ (by norm_num)]; ring, ← zpow_add₀ (by norm_num)]
    congr 1; omega
  set m : ℤ := k / (2 ^ t : ℤ) with hm
  have h2t : (0 : ℤ) < 2 ^ t := by positivity
  have hm1 : m * 2 ^ t ≤ k := Int.ediv_mul_le k (by positivity)
  have hm2 : k < (m + 1) * 2 ^ t := by
    have := Int.lt_ediv_add_one_mul_self k h2t; linarith
  have hcell : ∀ z : ℝ, (k : ℝ) * 2 ^ j < z → z < ((k : ℝ) + 1) * 2 ^ j →
      (m : ℝ) / 2 < z / u ∧ z / u < ((m : ℝ) + 1) / 2 := by
    intro z h1 h2
    have hm1' : (m : ℝ) * c ≤ k := by
      have : ((m * 2 ^ t : ℤ) : ℝ) ≤ k := by exact_mod_cast hm1
      push_cast at this; rwa [hc_def]
    have hm2' : (k : ℝ) + 1 ≤ ((m : ℝ) + 1) * c := by
      have : ((k + 1 : ℤ) : ℝ) ≤ (((m + 1) * 2 ^ t : ℤ) : ℝ) := by
        exact_mod_cast (by omega : k + 1 ≤ (m + 1) * 2 ^ t)
      push_cast at this; rwa [hc_def]
    constructor
    · rw [lt_div_iff₀ hu, hu_eq]
      calc (m : ℝ) / 2 * (2 ^ j * (2 * c)) = (m : ℝ) * c * 2 ^ j := by ring
        _ ≤ (k : ℝ) * 2 ^ j := mul_le_mul_of_nonneg_right hm1' h2j.le
        _ < z := h1
    · rw [div_lt_iff₀ hu, hu_eq]
      calc z < ((k : ℝ) + 1) * 2 ^ j := h2
        _ ≤ ((m : ℝ) + 1) * c * 2 ^ j := mul_le_mul_of_nonneg_right hm2' h2j.le
        _ = ((m : ℝ) + 1) / 2 * (2 ^ j * (2 * c)) := by ring
  have hy := hcell v hv.1 hv.2
  have hy' := hcell v' hv'.1 hv'.2
  have hR := toInt_round_intSet_congr mode m (v / u) (v' / u) hy hy'
  set R := toInt (round intSet mode (v / u)) with hR_def
  have hval : (round (floatSet p) mode v).val = (((R : ℝ) * u : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale]
  have hval' : (round (floatSet p) mode v').val = (((R : ℝ) * u : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v' hv'0, hscale', ← hR]
  refine Prod.ext ?_ ?_
  · rw [fst_roundVal, fst_roundVal, ofVal_some, ofVal_some]
    exact toVal_injective p (ofEReal_spec p mode v).1 (ofEReal_spec p mode v').1
      (by rw [(ofEReal_spec p mode v).2, (ofEReal_spec p mode v').2, hval, hval'])
  · show (match (ofEReal p mode v).toVal, some (v : EReal) with
        | some a, some b => compare a b
        | _, _ => .eq) = (match (ofEReal p mode v').toVal, some (v' : EReal) with
        | some a, some b => compare a b
        | _, _ => .eq)
    rw [(ofEReal_spec p mode v).2, (ofEReal_spec p mode v').2, hval, hval']
    simp only [compare_coe_coe]
    rw [← compare_mul_right_pos _ _ u⁻¹ (inv_pos.mpr hu), ← compare_mul_right_pos (R * u) v' u⁻¹
      (inv_pos.mpr hu), mul_inv_cancel_right₀ hu.ne', ← div_eq_mul_inv, ← div_eq_mul_inv]
    exact compare_int_congr m R (v / u) (v' / u) hy hy'

/-! ### Helpers on `AzInt` and values -/

theorem AzInt.toInt_min (a b : AzInt) : (min a b).toInt = min a.toInt b.toInt := by
  show (if a ≤ b then a else b).toInt = _
  split_ifs with h
  · rw [min_eq_left ((AzInt.le_iff_toInt_le a b).mp h)]
  · rw [min_eq_right (le_of_not_ge fun h' => h ((AzInt.le_iff_toInt_le a b).mpr h'))]

theorem AzInt.abs_toNat_sub (a b : AzInt) (h : b.toInt ≤ a.toInt) :
    (((a - b).abs.toNat : ℕ) : ℤ) = a.toInt - b.toInt := by
  rw [AzInt.abs_toNat_eq, AzInt.toInt_sub, abs_of_nonneg (by omega)]

theorem finiteVal_true_eq (e : AzInt) (m : AzNat) :
    finiteVal true e m = (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size) := by
  unfold finiteVal; simp

theorem finiteVal_sign (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal s e m = (if s then 1 else -1) * finiteVal true e m := by
  cases s
  · rw [finiteVal_false]; simp
  · simp

/-! ### Same-sign addition and subtraction of magnitudes -/

/-- The value `B = nb · 2^(eb − |nb|)` is below `2^eb` by at least `2^(eb − |nb|)`. -/
theorem finiteVal_true_le (e : AzInt) (m : AzNat) :
    finiteVal true e m + (2 : ℝ) ^ (e.toInt - m.size) ≤ (2 : ℝ) ^ e.toInt := by
  rw [finiteVal_true_eq]
  have hhi : m.toNat + 1 ≤ 2 ^ m.size := by
    have : m.toNat < 2 ^ m.size := by rw [← Nat.size_le, AzNat.size_toNat]
    omega
  have hhi' : (m.toNat : ℝ) + 1 ≤ (2 : ℝ) ^ m.size := by exact_mod_cast hhi
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
  calc (m.toNat : ℝ) * 2 ^ (e.toInt - m.size) + 2 ^ (e.toInt - m.size)
      = ((m.toNat : ℝ) + 1) * 2 ^ (e.toInt - m.size) := by ring
    _ ≤ (2 : ℝ) ^ m.size * 2 ^ (e.toInt - m.size) := mul_le_mul_of_nonneg_right hhi' h2.le
    _ = (2 : ℝ) ^ e.toInt := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring

/-- The far case of addition and subtraction: with `T = max |nb| p` and `0 < C < 2^(eb − T − 2)`,
`B ± C` and the representative `B ± 2^(eb − T − 3)` round identically at precision `p`. -/
theorem roundVal_far (p : ℕ) [NeZero p] (mode : RoundingMode) (s add : Bool) (eb : AzInt)
    (nb : AzNat) (hnb : nb ≠ 0) (T : ℕ) (hT : nb.size ≤ T) (hTp : p ≤ T) (C : ℝ) (hC0 : 0 < C)
    (hC : C < (2 : ℝ) ^ (eb.toInt - T - 2)) :
    roundVal p mode (some (((if s then 1 else -1) *
        (finiteVal true eb nb + (if add then C else -C)) : ℝ) : EReal))
      = roundVal p mode (some (((if s then 1 else -1) *
        (finiteVal true eb nb + (if add then 1 else -1) * (2 : ℝ) ^ (eb.toInt - T - 3)) : ℝ)
          : EReal)) := by
  set B := finiteVal true eb nb with hB
  set j : ℤ := eb.toInt - T - 2 with hj
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) _
  have hhalf : (2 : ℝ) ^ (eb.toInt - T - 3) = 2 ^ j / 2 := by
    rw [hj, show eb.toInt - T - 3 = (eb.toInt - T - 2) - 1 by ring, zpow_sub_one₀ (by norm_num)]
    ring
  -- `B` is `K · 2^j` for the integer `K = nb · 2^(T − |nb| + 2) ≥ 4`
  set K : ℤ := (nb.toNat : ℤ) * 2 ^ (T - nb.size + 2) with hK
  have hBK : B = (K : ℝ) * 2 ^ j := by
    rw [hB, finiteVal_true_eq, hK, hj]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 2
    push_cast
    rw [Nat.cast_sub hT]
    ring
  have hK4 : 4 ≤ K := by
    rw [hK]
    have h1 : (1 : ℤ) ≤ nb.toNat := by
      exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hnb)
    have h2 : (4 : ℤ) ≤ 2 ^ (T - nb.size + 2) := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (T - nb.size + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  -- bounds on the binary logarithm of everything in the cell
  have hBlo : (2 : ℝ) ^ (eb.toInt - 1) ≤ B := by
    have := (abs_finiteVal_bounds' true eb nb hnb).1
    rwa [abs_of_pos (finiteVal_true_pos' eb nb hnb)] at this
  have hjlt : (2 : ℝ) ^ j ≤ 2 ^ (eb.toInt - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hlog_lb : ∀ z : ℝ, (2 : ℝ) ^ (eb.toInt - 2) ≤ z → eb.toInt - 2 ≤ Int.log 2 z := fun z hz =>
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (lt_of_lt_of_le (by positivity) hz)).mp
      (by simpa using hz)
  -- membership in a cell from its left endpoint
  have cell_of : ∀ (k : ℤ) (L z : ℝ), (k : ℝ) * 2 ^ j = L → L < z → z < L + 2 ^ j →
      (k : ℝ) * 2 ^ j < z ∧ z < ((k : ℝ) + 1) * 2 ^ j := by
    intro k L z hk h1 h2
    rw [add_mul, one_mul, hk]
    exact ⟨h1, h2⟩
  have hKm : (((K - 1 : ℤ) : ℝ)) * 2 ^ j = B - 2 ^ j := by push_cast; rw [hBK]; ring
  have hKn : (((-(K + 1) : ℤ) : ℝ)) * 2 ^ j = -(B + 2 ^ j) := by push_cast; rw [hBK]; ring
  have hKn' : (((-K : ℤ) : ℝ)) * 2 ^ j = -B := by push_cast; rw [hBK]; ring
  have hBpos : 0 < B := finiteVal_true_pos' eb nb hnb
  have h2e2 : (0 : ℝ) < 2 ^ (eb.toInt - 2) := zpow_pos (by norm_num) _
  have h12 : (2 : ℝ) ^ (eb.toInt - 1) = 2 * 2 ^ (eb.toInt - 2) := by
    rw [show eb.toInt - 1 = (eb.toInt - 2) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring
  cases add with
  | true =>
    simp only [↓reduceIte, one_mul]
    have hv := cell_of K B (B + C) hBK.symm (by linarith) (by linarith)
    have hv' := cell_of K B (B + 2 ^ j / 2) hBK.symm (by linarith) (by linarith)
    have hlog : Int.log 2 |B + C| = Int.log 2 |B + 2 ^ j / 2| := by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      exact log_eq_of_cell j K (by omega) _ _ hv hv'
    have hjle : j ≤ Int.log 2 |B + C| - p := by
      rw [abs_of_pos (by linarith)]
      have := hlog_lb (B + C) (by linarith)
      omega
    rw [hhalf]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
      exact roundVal_congr_cell p mode j (-(K + 1)) _ _
        (cell_of _ _ _ hKn (by linarith) (by linarith))
        (cell_of _ _ _ hKn (by linarith) (by linarith))
        (by rw [abs_neg, abs_neg]; exact hlog) (by rw [abs_neg]; exact hjle)
    · simp only [↓reduceIte, one_mul]
      exact roundVal_congr_cell p mode j K _ _ hv hv' hlog hjle
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    have hv := cell_of (K - 1) (B - 2 ^ j) (B + -C) hKm (by linarith) (by linarith)
    have hv' := cell_of (K - 1) (B - 2 ^ j) (B + -(2 ^ j / 2)) hKm (by linarith) (by linarith)
    have hlog : Int.log 2 |B + -C| = Int.log 2 |B + -(2 ^ j / 2)| := by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      exact log_eq_of_cell j (K - 1) (by omega) _ _ hv hv'
    have hjle : j ≤ Int.log 2 |B + -C| - p := by
      rw [abs_of_pos (by linarith)]
      have := hlog_lb (B + -C) (by linarith)
      omega
    rw [hhalf]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
      exact roundVal_congr_cell p mode j (-K) _ _
        (cell_of _ _ _ hKn' (by linarith) (by linarith))
        (cell_of _ _ _ hKn' (by linarith) (by linarith))
        (by rw [abs_neg, abs_neg]; exact hlog) (by rw [abs_neg]; exact hjle)
    · simp only [↓reduceIte, one_mul]
      exact roundVal_congr_cell p mode j (K - 1) _ _ hv hv' hlog hjle

theorem toInt_far_scale (eb : AzInt) (T : ℕ) :
    (eb - (AzNat.ofNat (T + 3)).toAzInt).toInt = eb.toInt - T - 3 := by
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]; push_cast; ring

theorem far_gap (eb ec : AzInt) (T : ℕ) (h : (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec) :
    (T : ℤ) + 2 ≤ eb.toInt - ec.toInt := by
  have := (AzInt.le_iff_toInt_le _ _).mp h
  rw [toInt_toAzInt, AzNat.toNat_ofNat, AzInt.toInt_sub] at this
  push_cast at this
  exact this

/-- `C < 2^(e_c) ≤ 2^(e_b − T − 2)` in the far case. -/
theorem far_bound (eb ec : AzInt) (nc : AzNat) (hnc : nc ≠ 0) (T : ℕ)
    (h : (T : ℤ) + 2 ≤ eb.toInt - ec.toInt) :
    finiteVal true ec nc < (2 : ℝ) ^ (eb.toInt - T - 2) := by
  have := (abs_finiteVal_bounds' true ec nc hnc).2
  rw [abs_of_pos (finiteVal_true_pos' ec nc hnc)] at this
  exact lt_of_lt_of_le this (zpow_le_zpow_right₀ (by norm_num) (by omega))

/-- The representative `8·nb ± 1` at scale `e_b − T − 3`, as a real. -/
theorem far_representative (eb : AzInt) (nb : AzNat) (T : ℕ) (hT : nb.size ≤ T) :
    ((nb.shiftLeft (T - nb.size + 3)).toNat : ℝ) * (2 : ℝ) ^ (eb.toInt - T - 3)
      = finiteVal true eb nb := by
  rw [AzNat.toNat_shiftLeft, finiteVal_true_eq]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 2
  push_cast
  rw [Nat.cast_sub hT]
  ring

theorem alignShifts_eq (wb wc : AzInt) :
    alignShifts wb wc = (min wb wc, (wb - min wb wc).abs.toNat, (wc - min wb wc).abs.toNat) :=
  rfl

/-- A shifted significand on the common scale is the value. -/
theorem shifted_on_scale (e : AzInt) (n : AzNat) (k : ℕ) (w : AzInt)
    (hk : (k : ℤ) = (e - (AzNat.ofNat n.size).toAzInt).toInt - w.toInt) :
    ((n.shiftLeft k).toNat : ℝ) * (2 : ℝ) ^ w.toInt = finiteVal true e n := by
  rw [AzNat.toNat_shiftLeft, finiteVal_true_eq]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 2
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat] at hk
  omega

/-- `addMagnitudes` is `roundVal` of `±(B + C)`. -/
theorem addMagnitudes_eq (s : Bool) (eb : AzInt) (nb : AzNat) (hnb : nb ≠ 0) (ec : AzInt)
    (nc : AzNat) (hnc : nc ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    addMagnitudes s eb nb ec nc p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true eb nb + finiteVal true ec nc) : ℝ) : EReal)) := by
  unfold addMagnitudes
  simp only
  set T := max nb.size p with hT
  have hT1 : nb.size ≤ T := le_max_left _ _
  have hT2 : p ≤ T := le_max_right _ _
  by_cases hfar : (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec
  · rw [ite_eq_left hfar, roundScaled_eq_roundVal, AzNat.toNat_addUInt64, toInt_far_scale]
    have hS : (((nb.shiftLeft (T - nb.size + 3)).toNat + (1 : UInt64).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (eb.toInt - T - 3)
        = finiteVal true eb nb + 1 * (2 : ℝ) ^ (eb.toInt - T - 3) := by
      rw [UInt64.toNat_one]
      push_cast
      rw [add_mul, far_representative eb nb T hT1]
    rw [mul_assoc, hS]
    have := roundVal_far p mode s true eb nb hnb T hT1 hT2 _ (finiteVal_true_pos' ec nc hnc)
      (far_bound eb ec nc hnc T (far_gap eb ec T hfar))
    simp only [↓reduceIte] at this
    exact this.symm
  · rw [ite_eq_right hfar, alignShifts_eq]
    simp only
    set w := min (eb - (AzNat.ofNat nb.size).toAzInt) (ec - (AzNat.ofNat nc.size).toAzInt)
      with hw_def
    have hkb : (((eb - (AzNat.ofNat nb.size).toAzInt - w).abs.toNat : ℕ) : ℤ)
        = (eb - (AzNat.ofNat nb.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_left _ _)
    have hkc : (((ec - (AzNat.ofNat nc.size).toAzInt - w).abs.toNat : ℕ) : ℤ)
        = (ec - (AzNat.ofNat nc.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_right _ _)
    have hS : (((nb.shiftLeft (eb - (AzNat.ofNat nb.size).toAzInt - w).abs.toNat +
        nc.shiftLeft (ec - (AzNat.ofNat nc.size).toAzInt - w).abs.toNat).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ w.toInt = finiteVal true eb nb + finiteVal true ec nc := by
      rw [AzNat.toNat_add]
      push_cast
      rw [add_mul, shifted_on_scale eb nb _ _ hkb, shifted_on_scale ec nc _ _ hkc]
    rw [roundScaled_eq_roundVal, mul_assoc, hS]

/-- `subMagnitudes` is `roundVal` of `±(B − C)` when `C < B`. -/
theorem subMagnitudes_eq (s : Bool) (eb : AzInt) (nb : AzNat) (hnb : nb ≠ 0) (ec : AzInt)
    (nc : AzNat) (hnc : nc ≠ 0) (hlt : finiteVal true ec nc < finiteVal true eb nb) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    subMagnitudes s eb nb ec nc p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true eb nb - finiteVal true ec nc) : ℝ) : EReal)) := by
  unfold subMagnitudes
  simp only
  set T := max nb.size p with hT
  have hT1 : nb.size ≤ T := le_max_left _ _
  have hT2 : p ≤ T := le_max_right _ _
  by_cases hfar : (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec
  · rw [ite_eq_left hfar, roundScaled_eq_roundVal, AzNat.toNat_sub, toInt_far_scale]
    have hpos : 1 ≤ (nb.shiftLeft (T - nb.size + 3)).toNat := by
      rw [AzNat.toNat_shiftLeft]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (toNat_ne_zero_of_ne_zero hnb)
        (pow_ne_zero _ (by norm_num)))
    have hS : (((nb.shiftLeft (T - nb.size + 3)).toNat - (1 : AzNat).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (eb.toInt - T - 3)
        = finiteVal true eb nb + (-1) * (2 : ℝ) ^ (eb.toInt - T - 3) := by
      rw [AzNat.toNat_one, Nat.cast_sub hpos]
      push_cast
      rw [sub_mul, far_representative eb nb T hT1]
      ring
    rw [mul_assoc, hS]
    have := roundVal_far p mode s false eb nb hnb T hT1 hT2 _ (finiteVal_true_pos' ec nc hnc)
      (far_bound eb ec nc hnc T (far_gap eb ec T hfar))
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [← sub_eq_add_neg] at this
    exact this.symm
  · rw [ite_eq_right hfar, alignShifts_eq]
    simp only
    set w := min (eb - (AzNat.ofNat nb.size).toAzInt) (ec - (AzNat.ofNat nc.size).toAzInt)
      with hw_def
    set kb := (eb - (AzNat.ofNat nb.size).toAzInt - w).abs.toNat with hkb_def
    set kc := (ec - (AzNat.ofNat nc.size).toAzInt - w).abs.toNat with hkc_def
    have hkb : ((kb : ℕ) : ℤ) = (eb - (AzNat.ofNat nb.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_left _ _)
    have hkc : ((kc : ℕ) : ℤ) = (ec - (AzNat.ofNat nc.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_right _ _)
    have hB := shifted_on_scale eb nb kb w hkb
    have hC := shifted_on_scale ec nc kc w hkc
    have hle : (nc.shiftLeft kc).toNat ≤ (nb.shiftLeft kb).toNat := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
      have : ((nc.shiftLeft kc).toNat : ℝ) * 2 ^ w.toInt
          ≤ ((nb.shiftLeft kb).toNat : ℝ) * 2 ^ w.toInt := by
        rw [hB, hC]; exact hlt.le
      exact_mod_cast le_of_mul_le_mul_right this h2
    have hS : (((nb.shiftLeft kb - nc.shiftLeft kc).toNat : ℕ) : ℝ) * (2 : ℝ) ^ w.toInt
        = finiteVal true eb nb - finiteVal true ec nc := by
      rw [AzNat.toNat_sub, Nat.cast_sub hle, sub_mul, hB, hC]
    rw [roundScaled_eq_roundVal, mul_assoc, hS]

/-! ### Addition and subtraction are the lifted specifications -/

@[simp] theorem roundVal_top (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode (some ⊤) = (infinity true, .eq) :=
  roundVal_of_toVal p mode (infinity true) ⊤ (Or.inr rfl) rfl

@[simp] theorem roundVal_bot (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode (some ⊥) = (infinity false, .eq) :=
  roundVal_of_toVal p mode (infinity false) ⊥ (Or.inr rfl) rfl

@[simp] theorem roundVal_zero (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode (some 0) = (zero, .eq) :=
  roundVal_of_toVal p mode zero 0 (Or.inr rfl) rfl

namespace Spec

theorem add_zero_left (b : EReal) : add 0 b = some b := by
  unfold add
  rw [ite_eq_right (by simp), zero_add]

theorem add_zero_right (a : EReal) : add a 0 = some a := by
  unfold add
  rw [ite_eq_right (by simp), add_zero]

end Spec

theorem signed_sum_sub (s : Bool) (A B : ℝ) :
    (if s then 1 else -1) * A + (if !s then 1 else -1) * B
      = (if s then 1 else -1) * (A - B) := by
  cases s <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] <;> ring

theorem signed_sum_sub' (s : Bool) (A B : ℝ) :
    (if s then 1 else -1) * A + (if !s then 1 else -1) * B
      = (if !s then 1 else -1) * (B - A) := by
  cases s <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] <;> ring

/-- Addition is the float lift of `EReal` addition (`∞ + (−∞)` being `NaN`). -/
theorem addPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    addPrecRound x y p mode = liftVal₂ Spec.add x y p mode := by
  unfold liftVal₂
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t => cases s <;> cases t <;> simp [addPrecRound, Spec.add]
    | zero => cases s <;> simp [addPrecRound, Spec.add]
    | finite t e q m hv => cases s <;> simp [addPrecRound, Spec.add]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t => cases t <;> simp [addPrecRound, Spec.add]
    | zero =>
      rw [show addPrecRound zero zero p mode = setPrecRound zero p mode from rfl,
        setPrecRound_eq_liftE]
      unfold liftE liftVal
      simp [Spec.add_zero_left]
    | finite t e q m hv =>
      rw [show addPrecRound zero (finite t e q m hv) p mode
        = setPrecRound (finite t e q m hv) p mode from rfl, setPrecRound_eq_liftE]
      unfold liftE liftVal
      simp [Spec.add_zero_left]
  | finite s e₁ p₁ m₁ h₁ =>
    cases y with
    | nan => rfl
    | infinity t => cases t <;> simp [addPrecRound, Spec.add]
    | zero =>
      rw [show addPrecRound (finite s e₁ p₁ m₁ h₁) zero p mode
        = setPrecRound (finite s e₁ p₁ m₁ h₁) p mode from rfl, setPrecRound_eq_liftE]
      unfold liftE liftVal
      simp [Spec.add_zero_right]
    | finite t e₂ p₂ m₂ h₂ =>
      simp only [addPrecRound, toVal_finite, Option.bind_some, Spec.add_coe_coe]
      have hn₁ := coreSignificand_ne_zero h₁
      have hn₂ := coreSignificand_ne_zero h₂
      rw [finiteVal_eq_core s e₁ h₁, finiteVal_eq_core t e₂ h₂, finiteVal_sign s e₁,
        finiteVal_sign t e₂]
      by_cases hst : s = t
      · subst hst
        rw [ite_eq_left rfl, ← mul_add]
        by_cases hlt : AzInt.compare e₁ e₂ = .lt
        · rw [ite_eq_left hlt, addMagnitudes_eq s e₂ _ hn₂ e₁ _ hn₁, add_comm]
        · rw [ite_eq_right hlt, addMagnitudes_eq s e₁ _ hn₁ e₂ _ hn₂]
      · rw [ite_eq_right hst]
        have ht : t = !s := by cases s <;> cases t <;> simp_all
        subst ht
        split <;> rename_i hcmp
        · rw [compareMagnitude_eq e₁ h₁ e₂ h₂, compare_eq_iff_eq, finiteVal_eq_core true e₁ h₁,
            finiteVal_eq_core true e₂ h₂] at hcmp
          rw [hcmp, signed_sum_sub, sub_self, mul_zero, EReal.coe_zero, roundVal_zero]
        · rw [compareMagnitude_eq e₁ h₁ e₂ h₂, compare_gt_iff_gt, finiteVal_eq_core true e₁ h₁,
            finiteVal_eq_core true e₂ h₂] at hcmp
          rw [subMagnitudes_eq s e₁ _ hn₁ e₂ _ hn₂ hcmp, signed_sum_sub]
        · rw [compareMagnitude_eq e₁ h₁ e₂ h₂, compare_lt_iff_lt, finiteVal_eq_core true e₁ h₁,
            finiteVal_eq_core true e₂ h₂] at hcmp
          rw [subMagnitudes_eq (!s) e₂ _ hn₂ e₁ _ hn₁ hcmp, signed_sum_sub']

/-- Subtraction is the float lift of `EReal` subtraction. -/
theorem subPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    subPrecRound x y p mode = liftVal₂ Spec.sub x y p mode := by
  unfold subPrecRound
  rw [addPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [toVal_neg]
  congr 1
  cases toVal y <;> rfl

/-! ### Multiplication and squaring are the lifted specifications -/

@[simp] theorem roundVal_inf (p : ℕ) [NeZero p] (mode : RoundingMode) (b : Bool) :
    roundVal p mode (some (if b then ⊤ else ⊥)) = (infinity b, .eq) :=
  roundVal_of_toVal p mode (infinity b) _ (Or.inr rfl) rfl

theorem signed_mul (s t : Bool) :
    (if s then (1 : ℝ) else -1) * (if t then 1 else -1) = if (s == t) then 1 else -1 := by
  cases s <;> cases t <;> simp

theorem decide_pos_finiteVal (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) :
    decide (0 < finiteVal s e m) = s := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, finiteVal_pos_iff s e m hm]

/-- The exact product of two cores on the combined scale. -/
theorem mul_cores_scaled (e₁ : AzInt) {p₁ : ℕ} {m₁ : AzNat} (h₁ : FiniteValid p₁ m₁) (e₂ : AzInt)
    {p₂ : ℕ} {m₂ : AzNat} (h₂ : FiniteValid p₂ m₂) :
    (((coreSignificand p₁ m₁ * coreSignificand p₂ m₂).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (e₁ - (AzNat.ofNat p₁).toAzInt + (e₂ - (AzNat.ofNat p₂).toAzInt)).toInt
      = finiteVal true e₁ (coreSignificand p₁ m₁) * finiteVal true e₂ (coreSignificand p₂ m₂) := by
  rw [AzInt.toInt_add, AzInt.toInt_sub, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt,
    AzNat.toNat_ofNat, AzNat.toNat_ofNat, AzNat.toNat_mul, finiteVal_true_eq, finiteVal_true_eq,
    size_coreSignificand h₁, size_coreSignificand h₂, zpow_add₀ (by norm_num)]
  push_cast
  ring

/-- Multiplication is the float lift of `EReal` multiplication (`0 · (±∞)` being `NaN`). -/
theorem mulPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    mulPrecRound x y p mode = liftVal₂ Spec.mul x y p mode := by
  unfold liftVal₂
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t =>
      cases s <;> cases t <;>
        simp [mulPrecRound, Spec.mul, EReal.top_ne_zero, EReal.bot_ne_zero]
    | zero => cases s <;> simp [mulPrecRound, Spec.mul]
    | finite t e q m hv =>
      simp only [mulPrecRound, toVal_infinity, toVal_finite, Option.bind_some]
      rw [Spec.mul_inf_coe s _ (by
          rw [finiteVal_eq_core t e hv]
          exact finiteVal_ne_zero' t e _ (coreSignificand_ne_zero hv)),
        finiteVal_eq_core t e hv, decide_pos_finiteVal t e _ (coreSignificand_ne_zero hv),
        roundVal_inf]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t => cases t <;> simp [mulPrecRound, Spec.mul]
    | zero => simp [mulPrecRound, Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot]
    | finite t e q m hv => simp [mulPrecRound, Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot]
  | finite s e₁ p₁ m₁ h₁ =>
    cases y with
    | nan => rfl
    | infinity t =>
      simp only [mulPrecRound, toVal_infinity, toVal_finite, Option.bind_some]
      rw [Spec.mul_coe_inf _ (by
          rw [finiteVal_eq_core s e₁ h₁]
          exact finiteVal_ne_zero' s e₁ _ (coreSignificand_ne_zero h₁)) t,
        finiteVal_eq_core s e₁ h₁, decide_pos_finiteVal s e₁ _ (coreSignificand_ne_zero h₁),
        roundVal_inf]
    | zero => simp [mulPrecRound, Spec.mul, EReal.zero_ne_top, EReal.zero_ne_bot]
    | finite t e₂ p₂ m₂ h₂ =>
      simp only [mulPrecRound, toVal_finite, Option.bind_some, Spec.mul_coe_coe]
      rw [roundScaled_eq_roundVal, mul_assoc, mul_cores_scaled e₁ h₁ e₂ h₂,
        finiteVal_eq_core s e₁ h₁, finiteVal_eq_core t e₂ h₂, finiteVal_sign s e₁,
        finiteVal_sign t e₂, ← signed_mul, mul_mul_mul_comm]

/-- Squaring is the exact-value lift of `v ↦ v · v` (`EReal`'s `(±∞)² = ∞` needs no table). -/
theorem sqrPrecRound_eq_liftE (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrPrecRound x p mode = liftE (fun v => v * v) x p mode := by
  unfold liftE liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [sqrPrecRound]
  | zero => simp [sqrPrecRound]
  | finite s e q m hv =>
    simp only [sqrPrecRound, toVal_finite, Option.bind_some, ← EReal.coe_mul]
    have hS : (((AzNat.square (coreSignificand q m)).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (e - (AzNat.ofNat q).toAzInt + (e - (AzNat.ofNat q).toAzInt)).toInt
        = finiteVal s e m * finiteVal s e m := by
      rw [AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_square,
        finiteVal_eq_core s e hv, finiteVal_sign s e, finiteVal_true_eq, size_coreSignificand hv,
        zpow_add₀ (by norm_num)]
      push_cast
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
    rw [roundScaled_eq_roundVal, ite_eq_left rfl, one_mul, hS]

/-! ### Division is the lifted specification -/

theorem toNat_bounds_of_ne_zero (m : AzNat) (hm : m ≠ 0) :
    2 ^ (m.size - 1) ≤ m.toNat ∧ m.toNat < 2 ^ m.size := by
  have hm0 := toNat_ne_zero_of_ne_zero hm
  constructor
  · rw [← Nat.lt_size, AzNat.size_toNat]; have := size_pos_of_ne_zero hm; omega
  · rw [← Nat.size_le, AzNat.size_toNat]

theorem normalizeCarry_spec (r : AzInt) (p : ℕ) (hp : 0 < p) (e : AzInt)
    (hlo : 2 ^ (p - 1) ≤ r.abs.toNat) (hhi : r.abs.toNat ≤ 2 ^ p) :
    (normalizeCarry r e p).toVal = some (((r.toInt : ℝ) * (2 : ℝ) ^ (e.toInt - p) : ℝ) : EReal) ∧
    (normalizeCarry r e p).precision? = some p := by
  unfold normalizeCarry
  exact normalize_spec r p hp e hlo hhi

theorem signed_div (s t : Bool) (a b : ℝ) :
    ((if s then 1 else -1) * a) / ((if t then 1 else -1) * b)
      = (if (s == t) then 1 else -1) * (a / b) := by
  cases s <;> cases t <;> simp [neg_div, div_neg]

/-- The `p`-bit quotient scaling: with `g = p + p₂ − p₁ − [N₂ / 2^p₂ ≤ N₁ / 2^p₁]`,
`N₁ · 2^g / N₂ ∈ [2^(p−1), 2^p)`. -/
theorem quotient_scale_bounds (N₁ N₂ : ℝ) (p₁ p₂ p : ℕ)
    (h₁ : (2 : ℝ) ^ ((p₁ : ℤ) - 1) ≤ N₁ ∧ N₁ < (2 : ℝ) ^ (p₁ : ℤ))
    (h₂ : (2 : ℝ) ^ ((p₂ : ℤ) - 1) ≤ N₂ ∧ N₂ < (2 : ℝ) ^ (p₂ : ℤ)) (hge : Bool)
    (hcase : hge = true ↔ N₂ / (2 : ℝ) ^ (p₂ : ℤ) ≤ N₁ / (2 : ℝ) ^ (p₁ : ℤ)) :
    (2 : ℝ) ^ ((p : ℤ) - 1) ≤ N₁ * (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁ - (if hge then 1 else 0)) / N₂ ∧
      N₁ * (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁ - (if hge then 1 else 0)) / N₂ < (2 : ℝ) ^ (p : ℤ) := by
  set a : ℝ := (2 : ℝ) ^ (p₁ : ℤ) with ha_def
  set b : ℝ := (2 : ℝ) ^ (p₂ : ℤ) with hb_def
  set P : ℝ := (2 : ℝ) ^ ((p : ℤ) - 1) with hP_def
  have ha : (0 : ℝ) < a := zpow_pos (by norm_num) _
  have hb : (0 : ℝ) < b := zpow_pos (by norm_num) _
  have hP : (0 : ℝ) < P := zpow_pos (by norm_num) _
  have hP2 : (2 : ℝ) ^ (p : ℤ) = P * 2 := by
    rw [hP_def, ← zpow_add_one₀ (two_ne_zero)]; congr 1; ring
  have ha2 : a = (2 : ℝ) ^ ((p₁ : ℤ) - 1) * 2 := by
    rw [ha_def, ← zpow_add_one₀ (two_ne_zero)]; congr 1; ring
  have hb2 : b = (2 : ℝ) ^ ((p₂ : ℤ) - 1) * 2 := by
    rw [hb_def, ← zpow_add_one₀ (two_ne_zero)]; congr 1; ring
  have hN₁ : 0 < N₁ := lt_of_lt_of_le (zpow_pos (by norm_num) _) h₁.1
  have hN₂ : 0 < N₂ := lt_of_lt_of_le (zpow_pos (by norm_num) _) h₂.1
  rw [div_le_div_iff₀ hb ha] at hcase
  cases hge with
  | true =>
    have hle : N₂ * a ≤ N₁ * b := hcase.mp rfl
    simp only [↓reduceIte]
    have hg : (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁ - 1) = P * b / a := by
      rw [hP_def, ha_def, hb_def, ← zpow_add₀ (by norm_num), ← zpow_sub₀ (by norm_num)]
      congr 1; ring
    rw [hg]
    constructor
    · rw [le_div_iff₀ hN₂, show N₁ * (P * b / a) = P * (N₁ * b / a) by ring]
      exact mul_le_mul_of_nonneg_left ((le_div_iff₀ ha).mpr hle) hP.le
    · rw [div_lt_iff₀ hN₂, hP2, show N₁ * (P * b / a) = P * (N₁ * b / a) by ring,
        show P * 2 * N₂ = P * (2 * N₂) by ring]
      apply mul_lt_mul_of_pos_left _ hP
      rw [div_lt_iff₀ ha]
      have h1 : N₁ * b < a * b := mul_lt_mul_of_pos_right h₁.2 hb
      have h2 : a * (2 : ℝ) ^ ((p₂ : ℤ) - 1) ≤ a * N₂ := mul_le_mul_of_nonneg_left h₂.1 ha.le
      have h3 : a * b = 2 * (a * (2 : ℝ) ^ ((p₂ : ℤ) - 1)) := by rw [hb2]; ring
      linarith
  | false =>
    have hlt : N₁ * b < N₂ * a := by
      have h := fun h' => hcase.mpr h'
      by_contra hcon
      push Not at hcon
      exact absurd (h hcon) (by simp)
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]
    have hg : (2 : ℝ) ^ ((p : ℤ) + p₂ - p₁) = (2 : ℝ) ^ (p : ℤ) * b / a := by
      rw [ha_def, hb_def, ← zpow_add₀ (by norm_num), ← zpow_sub₀ (by norm_num)]
    rw [hg]
    constructor
    · rw [le_div_iff₀ hN₂, hP2, show N₁ * (P * 2 * b / a) = P * (2 * N₁ * b / a) by ring]
      apply mul_le_mul_of_nonneg_left _ hP.le
      rw [le_div_iff₀ ha]
      have h1 : N₂ * a ≤ b * a := mul_le_mul_of_nonneg_right h₂.2.le ha.le
      have h2 : b * (2 : ℝ) ^ ((p₁ : ℤ) - 1) ≤ b * N₁ := mul_le_mul_of_nonneg_left h₁.1 hb.le
      have h3 : b * a = 2 * (b * (2 : ℝ) ^ ((p₁ : ℤ) - 1)) := by rw [ha2]; ring
      linarith
    · rw [div_lt_iff₀ hN₂, show N₁ * ((2 : ℝ) ^ (p : ℤ) * b / a) = (2 : ℝ) ^ (p : ℤ) * (N₁ * b / a)
        by ring]
      apply mul_lt_mul_of_pos_left _ (zpow_pos (by norm_num) _)
      rw [div_lt_iff₀ ha]; exact hlt

/-- `divCores` on any two nonzero integers of the stated sizes, given the comparison flag,
rounds the exact quotient. -/
theorem divCores_eq_gen (s : Bool) (e₁ : AzInt) (n₁ : AzNat) (p₁ : ℕ) (hn₁0 : n₁ ≠ 0)
    (hs₁ : n₁.size = p₁) (e₂ : AzInt) (n₂ : AzNat) (p₂ : ℕ) (hn₂0 : n₂ ≠ 0) (hs₂ : n₂.size = p₂)
    (hge : Bool)
    (hcase : hge = true ↔
      (n₂.toNat : ℝ) / (2 : ℝ) ^ (p₂ : ℤ) ≤ (n₁.toNat : ℝ) / (2 : ℝ) ^ (p₁ : ℤ))
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    divCores s e₁ n₁ p₁ e₂ n₂ p₂ hge p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true e₁ n₁ / finiteVal true e₂ n₂) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hb₁ : (2 : ℝ) ^ ((p₁ : ℤ) - 1) ≤ (n₁.toNat : ℝ) ∧ (n₁.toNat : ℝ) < (2 : ℝ) ^ (p₁ : ℤ) := by
    obtain ⟨hlo, hhi⟩ := toNat_bounds_of_ne_zero n₁ hn₁0
    rw [hs₁] at hlo hhi
    have hp₁ : 0 < p₁ := hs₁ ▸ size_pos_of_ne_zero hn₁0
    constructor
    · rw [show (p₁ : ℤ) - 1 = ((p₁ - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hlo
    · rw [zpow_natCast]; exact_mod_cast hhi
  have hb₂ : (2 : ℝ) ^ ((p₂ : ℤ) - 1) ≤ (n₂.toNat : ℝ) ∧ (n₂.toNat : ℝ) < (2 : ℝ) ^ (p₂ : ℤ) := by
    obtain ⟨hlo, hhi⟩ := toNat_bounds_of_ne_zero n₂ hn₂0
    rw [hs₂] at hlo hhi
    have hp₂ : 0 < p₂ := hs₂ ▸ size_pos_of_ne_zero hn₂0
    constructor
    · rw [show (p₂ : ℤ) - 1 = ((p₂ - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hlo
    · rw [zpow_natCast]; exact_mod_cast hhi
  set N₁ : ℝ := (n₁.toNat : ℝ) with hN₁
  set N₂ : ℝ := (n₂.toNat : ℝ) with hN₂
  clear_value N₁ N₂
  have hN₁pos : 0 < N₁ := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb₁.1
  have hN₂pos : 0 < N₂ := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb₂.1
  -- unfold
  unfold divCores
  simp only []
  set g := (AzNat.ofNat (p + p₂)).toAzInt -
    (AzNat.ofNat (p₁ + (if hge then 1 else 0))).toAzInt with hg_def
  have hgI : g.toInt = (p : ℤ) + p₂ - p₁ - (if hge then 1 else 0) := by
    rw [hg_def, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
    cases hge <;> simp only [↓reduceIte, Bool.false_eq_true] <;> push_cast <;> ring
  clear_value g
  set A := if g.sign then n₁.shiftLeft g.abs.toNat else n₁ with hA_def
  set B := if g.sign then n₂ else n₂.shiftLeft g.abs.toNat with hB_def
  clear_value A B
  have hshift0 : ∀ (n : AzNat) (k : ℕ), n ≠ 0 → n.shiftLeft k ≠ 0 := by
    intro n k hn h
    have := congrArg AzNat.toNat h
    rw [AzNat.toNat_shiftLeft, AzNat.toNat_zero] at this
    exact Nat.mul_ne_zero (toNat_ne_zero_of_ne_zero hn) (pow_ne_zero _ two_ne_zero) this
  have hA0 : A ≠ 0 := by
    rw [hA_def]; split_ifs
    · exact hshift0 _ _ hn₁0
    · exact hn₁0
  have hB0 : 0 < B.toAzInt.abs.toNat := by
    show 0 < B.toNat
    apply Nat.pos_of_ne_zero
    apply toNat_ne_zero_of_ne_zero
    rw [hB_def]; split_ifs
    · exact hn₂0
    · exact hshift0 _ _ hn₂0
  have habsg : (g.abs.toNat : ℤ) = |g.toInt| := AzInt.abs_toNat_eq g
  have hAB : (A.toNat : ℝ) / (B.toNat : ℝ) = N₁ * (2 : ℝ) ^ g.toInt / N₂ := by
    by_cases hsg : g.sign = true
    · have hg0 : 0 ≤ g.toInt := (AzInt.sign_eq_true_iff g).mp hsg
      rw [hA_def, hB_def, ite_eq_left hsg, ite_eq_left hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((g.abs.toNat : ℕ) : ℤ) = g.toInt by rw [habsg, abs_of_nonneg hg0],
        ← hN₁, ← hN₂]
    · have hg0 : g.toInt < 0 := by
        have := (AzInt.sign_eq_true_iff g).not.mp hsg; push Not at this; exact this
      rw [hA_def, hB_def, ite_eq_right hsg, ite_eq_right hsg, AzNat.toNat_shiftLeft]
      push_cast
      rw [← zpow_natCast, show ((g.abs.toNat : ℕ) : ℤ) = -g.toInt by rw [habsg, abs_of_neg hg0],
        zpow_neg, ← hN₁, ← hN₂, div_eq_mul_inv, mul_inv, inv_inv, div_eq_mul_inv]
      ring
  -- the exact value
  set σ : ℝ := if s then 1 else -1 with hσ
  have hσ0 : σ ≠ 0 := by rw [hσ]; cases s <;> norm_num
  have hσabs : |σ| = 1 := by rw [hσ]; cases s <;> simp
  clear_value σ
  set w := e₁ - (AzNat.ofNat p₁).toAzInt - (e₂ - (AzNat.ofNat p₂).toAzInt) - g with hw_def
  have hwI : w.toInt = (e₁.toInt - p₁) - (e₂.toInt - p₂) - g.toInt := by
    rw [hw_def, AzInt.toInt_sub, AzInt.toInt_sub, AzInt.toInt_sub, AzInt.toInt_sub, toInt_toAzInt,
      toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  clear_value w
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := σ * (finiteVal true e₁ n₁ / finiteVal true e₂ n₂) with hv_def
  clear_value v
  have hv : v = σ * ((A.toNat : ℝ) / (B.toNat : ℝ)) * (2 : ℝ) ^ w.toInt := by
    rw [hv_def, hAB, finiteVal_true_eq, finiteVal_true_eq, hs₁, hs₂, ← hN₁, ← hN₂, hwI]
    have hsplit : (2 : ℝ) ^ (e₁.toInt - p₁)
        = 2 ^ ((e₁.toInt - p₁) - (e₂.toInt - p₂) - g.toInt) * 2 ^ g.toInt *
          2 ^ (e₂.toInt - p₂) := by
      rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]; congr 1; ring
    rw [hsplit]
    have h2 : (2 : ℝ) ^ (e₂.toInt - p₂) ≠ 0 := zpow_ne_zero _ (by norm_num)
    field_simp
  have hv0 : v ≠ 0 := by
    rw [hv_def]
    exact mul_ne_zero hσ0 (div_ne_zero (finiteVal_ne_zero' true e₁ n₁ hn₁0)
      (finiteVal_ne_zero' true e₂ n₂ hn₂0))
  -- the quotient lies in `[2^(p−1), 2^p)`
  obtain ⟨hqlo, hqhi⟩ := quotient_scale_bounds N₁ N₂ p₁ p₂ p hb₁ hb₂ hge hcase
  rw [← hgI, ← hAB] at hqlo hqhi
  have hABpos : 0 < (A.toNat : ℝ) / (B.toNat : ℝ) := lt_of_lt_of_le (zpow_pos (by norm_num) _) hqlo
  have habsv : |v| = (A.toNat : ℝ) / (B.toNat : ℝ) * (2 : ℝ) ^ w.toInt := by
    rw [hv, abs_mul, abs_mul, hσabs, one_mul, abs_of_pos hABpos, abs_of_pos h2w]
  have hvpos : 0 < |v| := by rw [habsv]; positivity
  have hlog : Int.log 2 |v| = w.toInt + p - 1 := by
    apply le_antisymm
    · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hvpos).mp (by
        rw [habsv, zpow_add₀ (by norm_num), mul_comm]
        exact mul_lt_mul_of_pos_left hqhi h2w)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hvpos).mp (by
        rw [habsv, show w.toInt + p - 1 = ((p : ℤ) - 1) + w.toInt by ring, zpow_add₀ (by norm_num)]
        exact mul_le_mul_of_nonneg_right hqlo h2w.le)
  have hscale : precScale 2 p v = (2 : ℝ) ^ w.toInt := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  -- the integer rounding is `AzInt.divRound`
  set qo := AzInt.divRound (AzInt.mkNorm s A) B.toAzInt mode with hqo
  clear_value qo
  have hz : ((AzInt.mkNorm s A).toInt : ℝ) = σ * (A.toNat : ℝ) := by
    rw [hσ]
    rcases Bool.eq_false_or_eq_true s with hs | hs <;>
      simp [hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false A hA0]
  have hyq : v / (2 : ℝ) ^ w.toInt
      = ((AzInt.mkNorm s A).toInt : ℝ) / (B.toAzInt.toInt : ℝ) := by
    rw [hv, mul_div_cancel_right₀ _ h2w.ne', hz, toInt_toAzInt, Int.cast_natCast, mul_div_assoc]
  have hr := AzInt.toInt_divRound (AzInt.mkNorm s A) B.toAzInt mode hB0
  rw [← hyq, ← hqo] at hr
  have hrI : toInt (round intSet mode (v / 2 ^ w.toInt)) = qo.1.toInt := toInt_eq_of_val hr
  have hround : (round (floatSet p) mode v).val
      = (((qo.1.toInt : ℝ) * 2 ^ w.toInt : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hrI]
  have hyabs : |v / (2 : ℝ) ^ w.toInt| = (A.toNat : ℝ) / (B.toNat : ℝ) := by
    rw [abs_div, habsv, abs_of_pos h2w, mul_div_cancel_right₀ _ h2w.ne']
  obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds p hp mode (v / 2 ^ w.toInt)
    (by rw [hyabs]; exact hqlo) (by rw [hyabs]; exact hqhi)
  rw [hrI] at hb1 hb2
  have habs : (qo.1.abs.toNat : ℤ) = |qo.1.toInt| := AzInt.abs_toNat_eq qo.1
  have hlo' : 2 ^ (p - 1) ≤ qo.1.abs.toNat := by
    have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ (qo.1.abs.toNat : ℤ) := by rw [habs]; exact hb1
    exact_mod_cast this
  have hhi' : qo.1.abs.toNat ≤ 2 ^ p := by
    have : (qo.1.abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by rw [habs]; exact hb2
    exact_mod_cast this
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec qo.1 p hp (w + (AzNat.ofNat p).toAzInt) hlo' hhi'
  have hep : (w + (AzNat.ofNat p).toAzInt).toInt - p = w.toInt := by
    rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; ring
  rw [hep] at hRval
  symm
  refine Prod.ext ?_ ?_
  · have hgoal : (roundVal p mode (some (v : EReal))).1
        = normalizeCarry qo.1 (w + (AzNat.ofNat p).toAzInt) p :=
      toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
        (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
    exact hgoal
  · show (roundVal p mode (some (v : EReal))).2 = qo.2
    rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, hqo,
      AzInt.snd_divRound _ _ _ hB0, ← hqo, ← hyq]
    conv_rhs => rw [← compare_mul_right_pos _ _ _ h2w, div_mul_cancel₀ _ h2w.ne']


/-- `divCores` with the comparison flag from the aligned significands rounds the exact quotient. -/
theorem divCores_eq (s : Bool) (e₁ : AzInt) {p₁ : ℕ} {m₁ : AzNat} (h₁ : FiniteValid p₁ m₁)
    (e₂ : AzInt) {p₂ : ℕ} {m₂ : AzNat} (h₂ : FiniteValid p₂ m₂) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    divCores s e₁ (coreSignificand p₁ m₁) p₁ e₂ (coreSignificand p₂ m₂) p₂
        (compareMagnitude 0 m₁ 0 m₂ != .lt) p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true e₁ (coreSignificand p₁ m₁) /
            finiteVal true e₂ (coreSignificand p₂ m₂)) : ℝ) : EReal)) := by
  apply divCores_eq_gen s e₁ _ p₁ (coreSignificand_ne_zero h₁) (size_coreSignificand h₁) e₂ _ p₂
    (coreSignificand_ne_zero h₂) (size_coreSignificand h₂)
  rw [bne_iff_ne, compareMagnitude_eq 0 h₁ 0 h₂, finiteVal_eq_core true 0 h₁,
    finiteVal_eq_core true 0 h₂, finiteVal_true_eq, finiteVal_true_eq, size_coreSignificand h₁,
    size_coreSignificand h₂, Ne, compare_lt_iff_lt, not_lt, show (0 : AzInt).toInt = 0 from rfl,
    zero_sub, zero_sub, zpow_neg, zpow_neg, ← div_eq_mul_inv, ← div_eq_mul_inv]

/-- `ofFractionRound` rounds the exact fraction. -/
theorem ofFractionRound_eq (s : Bool) (num den : AzNat) (hden : den ≠ 0) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ofFractionRound s num den p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          ((num.toNat : ℝ) / (den.toNat : ℝ)) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold ofFractionRound
  rw [ite_eq_right hp.ne']
  by_cases h0 : num = 0
  · rw [ite_eq_left h0, h0]
    simp only [AzNat.toNat_zero, Nat.cast_zero, zero_div, mul_zero, EReal.coe_zero]
    exact (roundVal_zero p mode).symm
  · rw [ite_eq_right h0]
    have ha : (0 : ℝ) < (2 : ℝ) ^ (num.size : ℤ) := zpow_pos (by norm_num) _
    have hb : (0 : ℝ) < (2 : ℝ) ^ (den.size : ℤ) := zpow_pos (by norm_num) _
    have hcase : (compare (num.shiftLeft den.size) (den.shiftLeft num.size) != .lt) = true ↔
        (den.toNat : ℝ) / (2 : ℝ) ^ (den.size : ℤ)
          ≤ (num.toNat : ℝ) / (2 : ℝ) ^ (num.size : ℤ) := by
      rw [bne_iff_ne,
        show compare (num.shiftLeft den.size) (den.shiftLeft num.size)
          = AzNat.compare (num.shiftLeft den.size) (den.shiftLeft num.size) from rfl,
        AzNat.compare_eq_compare_toNat, ← compare_natCast, AzNat.toNat_shiftLeft,
        AzNat.toNat_shiftLeft, Ne, compare_lt_iff_lt, not_lt, div_le_div_iff₀ hb ha]
      push_cast
      simp only [zpow_natCast]
    rw [divCores_eq_gen s _ num num.size h0 rfl _ den den.size hden rfl _ hcase p mode,
      finiteVal_true_eq, finiteVal_true_eq, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat, sub_self, sub_self, zpow_zero, mul_one, mul_one]

/-- Rounding a fraction agrees with rounding the rational it represents. -/
theorem fst_ofFractionRound (s : Bool) (num den : AzNat) (hden : den ≠ 0) (p : ℕ)
    (mode : RoundingMode) (q : AzRat)
    (hq : (AzRat.toRat q : ℝ) = (if s then 1 else -1) * ((num.toNat : ℝ) / (den.toNat : ℝ))) :
    (ofFractionRound s num den p mode).1 = (ofAzRatRound q p mode).1 := by
  by_cases hp : p = 0
  · subst hp
    unfold ofFractionRound ofAzRatRound
    rw [ite_eq_left rfl, ite_eq_left rfl]
  · have : NeZero p := ⟨hp⟩
    rw [ofFractionRound_eq s num den hden p mode, fst_roundVal, ofVal_some,
      ofAzRatRound_eq_ofEReal, hq]

/-- Division is the float lift of `Spec.div`. -/
theorem divPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    divPrecRound x y p mode = liftVal₂ Spec.div x y p mode := by
  unfold liftVal₂
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t => cases s <;> cases t <;> simp [divPrecRound, Spec.div]
    | zero =>
      simp only [divPrecRound, toVal_infinity, toVal_zero, Option.bind_some, Spec.div_inf_zero,
        roundVal_inf]
    | finite t e q m hv =>
      simp only [divPrecRound, toVal_infinity, toVal_finite, Option.bind_some]
      rw [Spec.div_inf_coe s _ (by
          rw [finiteVal_eq_core t e hv]
          exact finiteVal_ne_zero' t e _ (coreSignificand_ne_zero hv)),
        finiteVal_eq_core t e hv, decide_pos_finiteVal t e _ (coreSignificand_ne_zero hv),
        roundVal_inf]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t =>
      simp only [divPrecRound, toVal_infinity, toVal_zero, Option.bind_some, Spec.div_zero_inf,
        roundVal_zero]
    | zero => simp [divPrecRound, Spec.div]
    | finite t e q m hv =>
      simp only [divPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [Spec.div_zero_coe _ (by
          rw [finiteVal_eq_core t e hv]
          exact finiteVal_ne_zero' t e _ (coreSignificand_ne_zero hv)), roundVal_zero]
  | finite s e₁ p₁ m₁ h₁ =>
    have hx0 : finiteVal s e₁ m₁ ≠ 0 := by
      rw [finiteVal_eq_core s e₁ h₁]
      exact finiteVal_ne_zero' s e₁ _ (coreSignificand_ne_zero h₁)
    cases y with
    | nan => rfl
    | infinity t =>
      simp only [divPrecRound, toVal_infinity, toVal_finite, Option.bind_some, Spec.div_coe_inf,
        roundVal_zero]
    | zero =>
      simp only [divPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [Spec.div_coe_zero _ hx0, finiteVal_eq_core s e₁ h₁]
      simp only [finiteVal_pos_iff s e₁ _ (coreSignificand_ne_zero h₁), roundVal_inf]
    | finite t e₂ p₂ m₂ h₂ =>
      have hy0 : finiteVal t e₂ m₂ ≠ 0 := by
        rw [finiteVal_eq_core t e₂ h₂]
        exact finiteVal_ne_zero' t e₂ _ (coreSignificand_ne_zero h₂)
      simp only [divPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.div_coe_coe _ _ hy0, divCores_eq (s == t) e₁ h₁ e₂ h₂ p mode,
        finiteVal_eq_core s e₁ h₁, finiteVal_eq_core t e₂ h₂, finiteVal_sign s e₁,
        finiteVal_sign t e₂, signed_div]

/-! ### Square root is the lifted specification -/

/-- `compareScaled` compares `n · 2^t` with `c`. -/
theorem compareScaled_eq (n : AzNat) (t : AzInt) (c : AzNat) :
    compareScaled n t c = compare ((n.toNat : ℝ) * (2 : ℝ) ^ t.toInt) (c.toNat : ℝ) := by
  unfold compareScaled
  have habs : (t.abs.toNat : ℤ) = |t.toInt| := AzInt.abs_toNat_eq t
  by_cases hsg : t.sign = true
  · have hg0 : 0 ≤ t.toInt := (AzInt.sign_eq_true_iff t).mp hsg
    rw [ite_eq_left hsg]
    show AzNat.compare (n.shiftLeft t.abs.toNat) c = _
    rw [AzNat.compare_eq_compare_toNat, ← compare_natCast, AzNat.toNat_shiftLeft]
    push_cast
    rw [← zpow_natCast, show ((t.abs.toNat : ℕ) : ℤ) = t.toInt by rw [habs, abs_of_nonneg hg0]]
  · have hg0 : t.toInt < 0 := by
      have := (AzInt.sign_eq_true_iff t).not.mp hsg; push Not at this; exact this
    rw [ite_eq_right hsg]
    show AzNat.compare n (c.shiftLeft t.abs.toNat) = _
    rw [AzNat.compare_eq_compare_toNat, ← compare_natCast, AzNat.toNat_shiftLeft]
    push_cast
    rw [← zpow_natCast, show ((t.abs.toNat : ℕ) : ℤ) = -t.toInt by rw [habs, abs_of_neg hg0],
      zpow_neg]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ t.toInt := zpow_pos (by norm_num) _
    rcases lt_trichotomy ((n.toNat : ℝ) * (2 : ℝ) ^ t.toInt) (c.toNat : ℝ) with h | h | h
    · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((lt_mul_inv_iff₀ hpos).mpr h)]
    · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr ((eq_mul_inv_iff_mul_eq₀ hpos.ne').mpr h)]
    · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr ((mul_inv_lt_iff₀ hpos).mpr h)]

/-- `roundFromFloor` is integer rounding of a real `y ∈ [s, s+1)`, tag included. -/
theorem roundFromFloor_spec (y : ℝ) (s : AzNat) (exact : Bool) (cmpMid : Ordering)
    (mode : RoundingMode) (hlo : (s.toNat : ℝ) ≤ y) (hhi : y < s.toNat + 1)
    (hex : exact = true ↔ y = s.toNat) (hmid : cmpMid = compare y ((s.toNat : ℝ) + 1 / 2)) :
    toInt (round intSet mode y) = ((roundFromFloor s exact cmpMid mode).1.toNat : ℤ) ∧
    (roundFromFloor s exact cmpMid mode).2
      = compare (((roundFromFloor s exact cmpMid mode).1.toNat : ℕ) : ℝ) y := by
  have hF : toInt (roundFloor intSet y) = ⌊y⌋ := toInt_eq_of_val (val_roundFloor_intSet y).symm
  have hC : toInt (roundCeiling intSet y) = ⌈y⌉ :=
    toInt_eq_of_val (val_roundCeiling_intSet y).symm
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg _) hlo
  have hs1 : ((s.addUInt64 1).toNat : ℝ) = s.toNat + 1 := by
    rw [AzNat.toNat_addUInt64, UInt64.toNat_one]; push_cast; ring
  have hs1' : ((s.addUInt64 1).toNat : ℤ) = s.toNat + 1 := by
    rw [AzNat.toNat_addUInt64, UInt64.toNat_one]; push_cast; ring
  unfold roundFromFloor
  by_cases hexact : exact = true
  · rw [ite_eq_left hexact]
    have hy : y = s.toNat := hex.mp hexact
    have hfl : ⌊y⌋ = s.toNat := by rw [hy]; exact Int.floor_natCast _
    have hce : ⌈y⌉ = s.toNat := by rw [hy]; exact Int.ceil_natCast _
    refine ⟨?_, by show Ordering.eq = compare _ y; rw [hy, compare_eq_iff_eq.mpr rfl]⟩
    cases mode with
    | Floor => show toInt (roundFloor intSet y) = _; rw [hF, hfl]
    | Ceiling => show toInt (roundCeiling intSet y) = _; rw [hC, hce]
    | Down =>
      show toInt (if 0 ≤ y then roundFloor intSet y else roundCeiling intSet y) = _
      rw [ite_eq_left hy0, hF, hfl]
    | Up =>
      show toInt (if 0 ≤ y then roundCeiling intSet y else roundFloor intSet y) = _
      rw [ite_eq_left hy0, hC, hce]
    | Nearest =>
      show toInt (match compare (((y : ℝ) : EReal) - (roundFloor intSet y).val)
          ((roundCeiling intSet y).val - ((y : ℝ) : EReal)) with
        | .lt => roundFloor intSet y
        | .gt => roundCeiling intSet y
        | .eq => tiebreak (roundFloor intSet y) (roundCeiling intSet y)) = _
      rw [val_roundFloor_intSet, val_roundCeiling_intSet, hfl, hce, Int.cast_natCast,
        ← EReal.coe_sub, ← EReal.coe_sub, compare_coe_coe,
        compare_eq_iff_eq.mpr (show y - (s.toNat : ℝ) = (s.toNat : ℝ) - y by rw [hy])]
      show toInt (tiebreak (roundFloor intSet y) (roundCeiling intSet y)) = _
      rcases tiebreak_mem (roundFloor intSet y) (roundCeiling intSet y) with hT | hT <;> rw [hT]
      · rw [hF, hfl]
      · rw [hC, hce]
  · rw [ite_eq_right hexact]
    have hne : y ≠ s.toNat := fun h => hexact (hex.mpr h)
    have hlt : (s.toNat : ℝ) < y := lt_of_le_of_ne hlo (Ne.symm hne)
    have hfl : ⌊y⌋ = s.toNat := Int.floor_eq_iff.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    have hce : ⌈y⌉ = s.toNat + 1 :=
      Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have htagF : Ordering.lt = compare (s.toNat : ℝ) y := (compare_lt_iff_lt.mpr hlt).symm
    have htagC : Ordering.gt = compare (((s.addUInt64 1).toNat : ℕ) : ℝ) y := by
      rw [hs1]; exact (compare_gt_iff_gt.mpr hhi).symm
    cases mode with
    | Floor => exact ⟨by show toInt (roundFloor intSet y) = _; rw [hF, hfl], htagF⟩
    | Ceiling => exact ⟨by show toInt (roundCeiling intSet y) = _; rw [hC, hce, hs1'], htagC⟩
    | Down =>
      refine ⟨?_, htagF⟩
      show toInt (if 0 ≤ y then roundFloor intSet y else roundCeiling intSet y) = _
      rw [ite_eq_left hy0, hF, hfl]
    | Up =>
      refine ⟨?_, htagC⟩
      show toInt (if 0 ≤ y then roundCeiling intSet y else roundFloor intSet y) = _
      rw [ite_eq_left hy0, hC, hce, hs1']
    | Nearest =>
      have hcmp : compare (y - (s.toNat : ℝ)) (((s.toNat + 1 : ℤ) : ℝ) - y)
          = compare y ((s.toNat : ℝ) + 1 / 2) := by
        push_cast
        rcases lt_trichotomy y ((s.toNat : ℝ) + 1 / 2) with h | h | h
        · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by linarith)]
        · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (by linarith)]
        · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by linarith)]
      show toInt (match compare (((y : ℝ) : EReal) - (roundFloor intSet y).val)
          ((roundCeiling intSet y).val - ((y : ℝ) : EReal)) with
        | .lt => roundFloor intSet y
        | .gt => roundCeiling intSet y
        | .eq => tiebreak (roundFloor intSet y) (roundCeiling intSet y)) = _ ∧ _
      rw [val_roundFloor_intSet, val_roundCeiling_intSet, hfl, hce, Int.cast_natCast,
        ← EReal.coe_sub, ← EReal.coe_sub, compare_coe_coe, hcmp, ← hmid]
      cases cmpMid with
      | lt => exact ⟨by rw [hF, hfl], htagF⟩
      | gt => exact ⟨by rw [hC, hce, hs1'], htagC⟩
      | eq =>
        show toInt (intTiebreak (roundFloor intSet y) (roundCeiling intSet y)) = _ ∧ _
        unfold intTiebreak
        rw [hF, hC, hfl, hce]
        by_cases hodd : s.isOdd = true
        · have ho : Odd (s.toNat : ℤ) := (Int.odd_coe_nat _).mpr ((AzNat.isOdd_iff s).mp hodd)
          have hno : ¬ Even (s.toNat : ℤ) := Int.not_even_iff_odd.mpr ho
          have he1 : Even ((s.toNat : ℤ) + 1) := Int.even_add_one.mpr hno
          rw [ite_eq_right (fun h => hno h.1), ite_eq_left ⟨he1, hno⟩, ite_eq_left hodd]
          exact ⟨by rw [hC, hce, hs1'], htagC⟩
        · have hev : Even (s.toNat : ℤ) := by
            rcases Int.even_or_odd (s.toNat : ℤ) with h | h
            · exact h
            · exact absurd ((AzNat.isOdd_iff s).mpr ((Int.odd_coe_nat _).mp h)) hodd
          have hno1 : ¬ Even ((s.toNat : ℤ) + 1) := fun h => Int.even_add_one.mp h hev
          rw [ite_eq_left ⟨hev, hno1⟩, ite_eq_right hodd]
          exact ⟨by rw [hF, hfl], htagF⟩

/-- The truncated scaling `⌊n · 2^t⌋` as computed by a shift, with exactness. -/
theorem scaled_floor (n : AzNat) (t : AzInt) :
    ((if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat).toNat : ℝ)
        ≤ (n.toNat : ℝ) * (2 : ℝ) ^ t.toInt ∧
      (n.toNat : ℝ) * (2 : ℝ) ^ t.toInt
        < ((if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat).toNat : ℝ) + 1 ∧
      ((n.toNat : ℝ) * (2 : ℝ) ^ t.toInt
          = ((if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat).toNat : ℝ) ↔
        (t.sign || n.isMultipleOfPow2 t.abs.toNat) = true) := by
  have habs : (t.abs.toNat : ℤ) = |t.toInt| := AzInt.abs_toNat_eq t
  by_cases hsg : t.sign = true
  · have hg0 : 0 ≤ t.toInt := (AzInt.sign_eq_true_iff t).mp hsg
    rw [ite_eq_left hsg, AzNat.toNat_shiftLeft, hsg, Bool.true_or]
    push_cast
    rw [← zpow_natCast, show ((t.abs.toNat : ℕ) : ℤ) = t.toInt by rw [habs, abs_of_nonneg hg0]]
    exact ⟨le_rfl, by linarith, by simp⟩
  · have hg0 : t.toInt < 0 := by
      have := (AzInt.sign_eq_true_iff t).not.mp hsg; push Not at this; exact this
    have hsf : t.sign = false := by simpa using hsg
    rw [ite_eq_right hsg, AzNat.toNat_shiftRight, hsf, Bool.false_or,
      AzNat.isMultipleOfPow2_eq, decide_eq_true_eq]
    set k := t.abs.toNat with hk
    have hkI : (k : ℤ) = -t.toInt := by rw [hk, habs, abs_of_neg hg0]
    have h2k : (2 : ℝ) ^ t.toInt = ((2 ^ k : ℕ) : ℝ)⁻¹ := by
      push_cast
      rw [← zpow_natCast, hkI, zpow_neg, inv_inv]
    have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
    have hdiv := Nat.div_add_mod n.toNat (2 ^ k)
    have hmod := Nat.mod_lt n.toNat (by positivity : 0 < 2 ^ k)
    rw [h2k]
    set Q := n.toNat / 2 ^ k with hQ
    set R := n.toNat % 2 ^ k with hR
    have hn : (n.toNat : ℝ) = (2 ^ k : ℕ) * Q + R := by exact_mod_cast hdiv.symm
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have hRlt : (R : ℝ) < (2 ^ k : ℕ) := by exact_mod_cast hmod
    refine ⟨?_, ?_, ?_⟩
    · rw [hn, le_mul_inv_iff₀ hpos]; nlinarith
    · rw [hn, mul_inv_lt_iff₀ hpos]; nlinarith
    · constructor
      · intro h
        rw [hn, mul_inv_eq_iff_eq_mul₀ hpos.ne'] at h
        have : (R : ℝ) = 0 := by linarith
        have hR0' : R = 0 := by exact_mod_cast this
        exact Nat.dvd_of_mod_eq_zero hR0'
      · intro h
        have hR0' : R = 0 := by rw [hR]; exact Nat.mod_eq_zero_of_dvd h
        rw [hn, hR0', Nat.cast_zero, add_zero, mul_comm, inv_mul_cancel_left₀ hpos.ne']

/-- The square root of the exact value of a float at the right scale. -/
theorem sqrtCore_eq (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    sqrtCore e (coreSignificand q m) q p mode
      = roundVal p mode
          (some ((Real.sqrt (finiteVal true e (coreSignificand q m)) : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set n := coreSignificand q m with hn
  have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
  have hs : n.size = q := size_coreSignificand hv
  clear_value n
  have hb : (2 : ℝ) ^ ((q : ℤ) - 1) ≤ (n.toNat : ℝ) ∧ (n.toNat : ℝ) < (2 : ℝ) ^ (q : ℤ) := by
    obtain ⟨hlo, hhi⟩ := toNat_bounds_of_ne_zero n hn0
    rw [hs] at hlo hhi
    have hq : 0 < q := hv.pos
    constructor
    · rw [show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hlo
    · rw [zpow_natCast]; exact_mod_cast hhi
  set N : ℝ := (n.toNat : ℝ) with hN
  clear_value N
  have hNpos : 0 < N := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb.1
  unfold sqrtCore
  simp only []
  -- the parity of the exponent
  set δ : ℕ := if e.isOdd then 1 else 0 with hδ_def
  have hδ : (δ : ℤ) % 2 = e.toInt % 2 := by
    rw [hδ_def]
    rcases Int.even_or_odd e.toInt with h | h
    · have : e.isOdd = false := by
        cases hi : e.isOdd
        · rfl
        · exact absurd ((AzInt.isOdd_iff e).mp hi) (Int.not_odd_iff_even.mpr h)
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
      rw [Int.even_iff] at h; omega
    · rw [(AzInt.isOdd_iff e).mpr h]; simp only [↓reduceIte, Nat.cast_one]
      rw [Int.odd_iff] at h; omega
  have hδle : δ ≤ 1 := by rw [hδ_def]; split_ifs <;> omega
  clear_value δ
  -- the shift `t` and the exponent `w`
  set t : AzInt := (AzNat.ofNat (2 * p)).toAzInt - (AzNat.ofNat (q + δ)).toAzInt with ht_def
  have htI : t.toInt = 2 * (p : ℤ) - q - δ := by
    rw [ht_def, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]; push_cast; ring
  clear_value t
  set w' : AzInt := e - (AzNat.ofNat (2 * p)).toAzInt + (AzNat.ofNat δ).toAzInt with hw'_def
  have hw'I : w'.toInt = e.toInt - 2 * p + δ := by
    rw [hw'_def, AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
      AzNat.toNat_ofNat]; push_cast; ring
  clear_value w'
  set w := w'.shiftRight 1 with hw_def
  have hwI : 2 * w.toInt = w'.toInt := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w'.toInt = 2 * k := by
      refine ⟨w'.toInt / 2, ?_⟩
      have : w'.toInt % 2 = 0 := by rw [hw'I]; omega
      omega
    have h := AzInt.toInt_shiftRight w' 1
    rw [pow_one, hk, ← hw_def] at h
    have h2 : toInt (round intSet .Floor (((2 * k : ℤ) : ℝ) / 2)) = w.toInt := toInt_eq_of_val h
    rw [show toInt (round intSet .Floor (((2 * k : ℤ) : ℝ) / 2)) = ⌊((2 * k : ℤ) : ℝ) / 2⌋ from
      toInt_eq_of_val (val_roundFloor_intSet _).symm] at h2
    rw [show ((2 * k : ℤ) : ℝ) / 2 = (k : ℝ) by push_cast; ring, Int.floor_intCast] at h2
    rw [hk, ← h2]
  clear_value w
  have htw : t.toInt + 2 * w.toInt = e.toInt - q := by rw [hwI, hw'I, htI]; ring
  -- the scaled significand `M = N · 2^t` and its truncation
  set Mr : ℝ := N * (2 : ℝ) ^ t.toInt with hMr
  have hMr0 : 0 < Mr := by positivity
  obtain ⟨hMle, hMlt, hMex⟩ := scaled_floor n t
  rw [← hN] at hMle hMlt hMex
  set M := if t.sign then n.shiftLeft t.abs.toNat else n.shiftRight t.abs.toNat with hM_def
  clear_value M
  rw [← hMr] at hMle hMlt hMex
  -- bounds on `M`: `2^(2p−2) ≤ Mr < 2^(2p)`
  have hMlo : (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ Mr := by
    rw [hMr, htI]
    calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ 2 ^ ((q : ℤ) - 1) * 2 ^ (2 * (p : ℤ) - q - δ) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ ≤ N * 2 ^ (2 * (p : ℤ) - q - δ) :=
          mul_le_mul_of_nonneg_right hb.1 (zpow_pos (by norm_num) _).le
  have hMhi : Mr < (2 : ℝ) ^ (2 * (p : ℤ)) := by
    rw [hMr, htI]
    calc N * 2 ^ (2 * (p : ℤ) - q - δ) < 2 ^ (q : ℤ) * 2 ^ (2 * (p : ℤ) - q - δ) :=
          mul_lt_mul_of_pos_right hb.2 (zpow_pos (by norm_num) _)
      _ ≤ 2 ^ (2 * (p : ℤ)) := by
          rw [← zpow_add₀ (by norm_num)]
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the integer square root
  set sr := AzNat.sqrtRem M with hsr
  clear_value sr
  have hsN : sr.1.toNat = Nat.sqrt M.toNat := by rw [hsr]; exact AzNat.toNat_sqrtRem_fst M
  have hrN : sr.2.toNat = M.toNat - Nat.sqrt M.toNat * Nat.sqrt M.toNat := by
    rw [hsr]; exact AzNat.toNat_sqrtRem_snd M
  set y : ℝ := Real.sqrt Mr with hy_def
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hsq_le : Nat.sqrt M.toNat ^ 2 ≤ M.toNat := Nat.sqrt_le' _
  have hlt_sq : M.toNat < (Nat.sqrt M.toNat + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hlo : (sr.1.toNat : ℝ) ≤ y := by
    rw [hsN, hy_def]
    exact le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt hMle)
  have hhi : y < sr.1.toNat + 1 := by
    rw [hsN, hy_def]
    calc Real.sqrt Mr < Real.sqrt (M.toNat + 1) := Real.sqrt_lt_sqrt hMr0.le hMlt
      _ ≤ Nat.sqrt M.toNat + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          exact_mod_cast hlt_sq
  have hex : (decide (sr.2 = 0) && (t.sign || n.isMultipleOfPow2 t.abs.toNat)) = true ↔
      y = sr.1.toNat := by
    rw [Bool.and_eq_true, decide_eq_true_eq, ← hMex, hsN, hy_def,
      Real.sqrt_eq_iff_eq_sq hMr0.le (Nat.cast_nonneg _)]
    constructor
    · rintro ⟨hr, hM⟩
      have hr' : sr.2.toNat = 0 := by rw [hr]; rfl
      rw [hrN] at hr'
      have hM2 : M.toNat = Nat.sqrt M.toNat * Nat.sqrt M.toNat := by
        have := Nat.sqrt_le M.toNat; omega
      have hMs : (M.toNat : ℝ) = (Nat.sqrt M.toNat : ℝ) ^ 2 := by rw [sq]; exact_mod_cast hM2
      rw [hM, hMs]
    · intro h
      have hMle' : Mr ≤ (M.toNat : ℝ) := by
        rw [h]; exact_mod_cast hsq_le
      have hMeq : Mr = (M.toNat : ℝ) := le_antisymm hMle' hMle
      refine ⟨?_, hMeq⟩
      have : (M.toNat : ℝ) = (Nat.sqrt M.toNat : ℝ) ^ 2 := by rw [← hMeq, h]
      have hM2 : M.toNat = Nat.sqrt M.toNat * Nat.sqrt M.toNat := by
        have : (M.toNat : ℝ) = ((Nat.sqrt M.toNat * Nat.sqrt M.toNat : ℕ) : ℝ) := by
          rw [this]; push_cast; ring
        exact_mod_cast this
      apply AzNat.toNat_injective
      rw [hrN, AzNat.toNat_zero]
      exact Nat.sub_eq_zero_of_le hM2.le
  have hmid : compareScaled n (t + (AzNat.ofNat 2).toAzInt)
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1))
      = compare y ((sr.1.toNat : ℝ) + 1 / 2) := by
    have htt : (t + (AzNat.ofNat 2).toAzInt).toInt = t.toInt + 2 := by
      rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; push_cast; ring
    have hL : N * (2 : ℝ) ^ (t.toInt + 2) = Mr * 4 := by
      rw [hMr, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num]; ring
    have hRt : ((AzNat.square ((sr.1.shiftLeft 1).addUInt64 1)).toNat : ℝ)
        = ((sr.1.toNat : ℝ) + 1 / 2) ^ 2 * 4 := by
      rw [AzNat.toNat_square, AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft, UInt64.toNat_one]
      push_cast; ring
    rw [compareScaled_eq, htt, ← hN, hL, hRt, hy_def, compare_mul_right_pos _ _ _ (by norm_num)]
    have hmid_pos : (0 : ℝ) < (sr.1.toNat : ℝ) + 1 / 2 := by positivity
    rcases lt_trichotomy (Real.sqrt Mr) ((sr.1.toNat : ℝ) + 1 / 2) with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      rw [Real.sqrt_lt' hmid_pos] at h
      exact compare_lt_iff_lt.mpr h
    · rw [compare_eq_iff_eq.mpr h]
      rw [Real.sqrt_eq_iff_eq_sq hMr0.le hmid_pos.le] at h
      exact compare_eq_iff_eq.mpr h
    · rw [compare_gt_iff_gt.mpr h]
      rw [Real.lt_sqrt hmid_pos.le] at h
      exact compare_gt_iff_gt.mpr h
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y sr.1 _ _ mode hlo hhi hex hmid
  set ro := roundFromFloor sr.1 (decide (sr.2 = 0) && (t.sign || n.isMultipleOfPow2 t.abs.toNat))
    (compareScaled n (t + (AzNat.ofNat 2).toAzInt)
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1))) mode with hro
  clear_value ro
  -- the exact value and its logarithm
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := Real.sqrt (finiteVal true e n) with hv_def
  have hv : v = y * (2 : ℝ) ^ w.toInt := by
    rw [hv_def, hy_def, finiteVal_true_eq, hs, ← hN, ← htw, zpow_add₀ (by norm_num),
      show (2 : ℝ) ^ (2 * w.toInt) = (2 ^ w.toInt) ^ 2 by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
      ← mul_assoc, ← hMr, Real.sqrt_mul hMr0.le, Real.sqrt_sq h2w.le]
  clear_value v
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [hy_def, Real.le_sqrt (zpow_pos (by norm_num) _).le hMr0.le, ← zpow_natCast, ← zpow_mul]
    convert hMlo using 2; push_cast; ring
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [hy_def, Real.sqrt_lt' (zpow_pos (by norm_num) _), ← zpow_natCast, ← zpow_mul]
    convert hMhi using 2; push_cast; ring
  have hypos : 0 < y := lt_of_lt_of_le (zpow_pos (by norm_num) _) hylo
  have hv0 : v ≠ 0 := by rw [hv]; positivity
  have hvabs : |v| = y * (2 : ℝ) ^ w.toInt := by rw [hv, abs_of_pos (by positivity)]
  have hvpos : 0 < |v| := by rw [hvabs]; positivity
  have hlog : Int.log 2 |v| = w.toInt + p - 1 := by
    apply le_antisymm
    · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, zpow_add₀ (by norm_num), mul_comm]
        exact mul_lt_mul_of_pos_left hyhi h2w)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, show w.toInt + p - 1 = ((p : ℤ) - 1) + w.toInt by ring, zpow_add₀ (by norm_num)]
        exact mul_le_mul_of_nonneg_right hylo h2w.le)
  have hscale : precScale 2 p v = (2 : ℝ) ^ w.toInt := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  have hyv : v / (2 : ℝ) ^ w.toInt = y := by rw [hv, mul_div_cancel_right₀ _ h2w.ne']
  have hround : (round (floatSet p) mode v).val
      = ((((AzInt.mkNorm true ro.1).toInt : ℝ) * 2 ^ w.toInt : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hyv, hR,
      AzInt.toInt_mkNorm_true]
  -- bounds on the rounded integer
  obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds p hp mode y (by rw [abs_of_pos hypos]; exact hylo)
    (by rw [abs_of_pos hypos]; exact hyhi)
  rw [hR] at hb1 hb2
  have habsR : ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) = |(ro.1.toNat : ℤ)| := by
    rw [AzInt.abs_toNat_eq, AzInt.toInt_mkNorm_true]
  have hlo' : 2 ^ (p - 1) ≤ (AzInt.mkNorm true ro.1).abs.toNat := by
    have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) := by
      rw [habsR]; exact hb1
    exact_mod_cast this
  have hhi' : (AzInt.mkNorm true ro.1).abs.toNat ≤ 2 ^ p := by
    have : ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by
      rw [habsR]; exact hb2
    exact_mod_cast this
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec (AzInt.mkNorm true ro.1) p hp
    (w + (AzNat.ofNat p).toAzInt) hlo' hhi'
  have hep : (w + (AzNat.ofNat p).toAzInt).toInt - p = w.toInt := by
    rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; ring
  rw [hep] at hRval
  symm
  refine Prod.ext ?_ ?_
  · have hgoal : (roundVal p mode (some (v : EReal))).1
        = normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p :=
      toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
        (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
    exact hgoal
  · show (roundVal p mode (some (v : EReal))).2 = ro.2
    rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, htag, AzInt.toInt_mkNorm_true,
      Int.cast_natCast, hv, compare_mul_right_pos _ _ _ h2w]

/-- Square root is the float lift of `Spec.sqrt`. -/
theorem sqrtPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrtPrecRound x p mode = liftVal Spec.sqrt x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [sqrtPrecRound]
  | zero => simp [sqrtPrecRound]
  | finite s e q m hv =>
    cases s with
    | true =>
      simp only [sqrtPrecRound, toVal_finite, Option.bind_some, ↓reduceIte]
      rw [finiteVal_eq_core true e hv,
        Spec.sqrt_coe _ (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv)).le,
        sqrtCore_eq e hv p mode]
    | false =>
      simp only [sqrtPrecRound, toVal_finite, Option.bind_some, Bool.false_eq_true, ↓reduceIte]
      rw [finiteVal_eq_core false e hv, finiteVal_false,
        Spec.sqrt_coe_neg _ (neg_neg_iff_pos.mpr
          (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv))), roundVal_none]

/-! ### Reciprocal square root is the lifted specification -/

/-- `AzInt.shiftRight` by one is floor division by two. -/
theorem AzInt.toInt_shiftRight_one (z : AzInt) : (z.shiftRight 1).toInt = z.toInt / 2 := by
  have h := AzInt.toInt_shiftRight z 1
  rw [pow_one] at h
  have h2 : toInt (round intSet .Floor ((z.toInt : ℝ) / 2)) = (z.shiftRight 1).toInt :=
    toInt_eq_of_val h
  rw [show toInt (round intSet .Floor ((z.toInt : ℝ) / 2)) = ⌊(z.toInt : ℝ) / 2⌋ from
    toInt_eq_of_val (val_roundFloor_intSet _).symm] at h2
  rw [← h2]
  apply Int.floor_eq_iff.mpr
  constructor
  · rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : z.toInt / 2 * 2 ≤ z.toInt)
  · rw [div_lt_iff₀ (by norm_num)]; exact_mod_cast (by omega : z.toInt < (z.toInt / 2 + 1) * 2)

/-- The reciprocal square root of the exact value of a float, at the right scale. -/
theorem rsqrtCore_eq (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    rsqrtCore e (coreSignificand q m) q p mode
      = roundVal p mode
          (some (((Real.sqrt (finiteVal true e (coreSignificand q m)))⁻¹ : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  set n := coreSignificand q m with hn
  have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
  have hs : n.size = q := size_coreSignificand hv
  have hq : 0 < q := hv.pos
  clear_value n
  obtain ⟨hNlo, hNhi⟩ := toNat_bounds_of_ne_zero n hn0
  rw [hs] at hNlo hNhi
  have hb : (2 : ℝ) ^ ((q : ℤ) - 1) ≤ (n.toNat : ℝ) ∧ (n.toNat : ℝ) < (2 : ℝ) ^ (q : ℤ) := by
    constructor
    · rw [show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; exact_mod_cast hNlo
    · rw [zpow_natCast]; exact_mod_cast hNhi
  set N : ℝ := (n.toNat : ℝ) with hN
  have hNpos : 0 < N := lt_of_lt_of_le (zpow_pos (by norm_num) _) hb.1
  clear_value N
  unfold rsqrtCore
  simp only []
  -- the parity and the boundary flag
  set odd := e.isOdd with hodd_def
  have hodd : odd = true ↔ Odd e.toInt := by rw [hodd_def]; exact AzInt.isOdd_iff e
  set bnd := (odd && decide (n = (1 : AzNat).shiftLeft (q - 1))) with hbnd_def
  have hbnd : bnd = true ↔ (odd = true ∧ n.toNat = 2 ^ (q - 1)) := by
    rw [hbnd_def, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h2, AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, AzNat.toNat_injective ?_⟩
      rw [h2, AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul]
  clear_value odd bnd
  -- `D`, `f`, `w`
  set D : ℕ := (if odd then (if bnd then 2 * p + q - 3 else 2 * p + q - 1) else 2 * p + q - 2)
    with hD_def
  set f : AzInt := (if (!odd || bnd) then (1 : AzInt) else 0) - e.shiftRight 1 with hf_def
  have hfI : f.toInt = (if (!odd || bnd) then 1 else 0) - e.toInt / 2 := by
    rw [hf_def, AzInt.toInt_sub, AzInt.toInt_shiftRight_one]
    split_ifs <;> rfl
  clear_value f
  set w := f - (AzNat.ofNat p).toAzInt with hw_def
  have hwI : w.toInt = f.toInt - p := by
    rw [hw_def, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  clear_value w
  -- the key relation `D + 2w = q − e`, by cases
  have hkey : (D : ℤ) + 2 * w.toInt = q - e.toInt := by
    rw [hwI, hfI, hD_def]
    rcases Bool.eq_false_or_eq_true odd with ho | ho
    · -- odd
      have hmod : e.toInt % 2 = 1 := Int.odd_iff.mp (hodd.mp ho)
      rcases Bool.eq_false_or_eq_true bnd with hbo | hbo
      · simp only [ho, hbo, ↓reduceIte, Bool.not_true, Bool.false_or]
        push_cast [show 3 ≤ 2 * p + q by omega]
        omega
      · simp only [ho, hbo, ↓reduceIte, Bool.not_true, Bool.false_or, Bool.false_eq_true]
        push_cast [show 1 ≤ 2 * p + q by omega]
        omega
    · have hmod : e.toInt % 2 = 0 := by
        have hev : ¬ Odd e.toInt := fun h => by rw [← hodd] at h; simp [ho] at h
        rw [Int.not_odd_iff_even, Int.even_iff] at hev; exact hev
      simp only [ho, ↓reduceIte, Bool.not_false, Bool.true_or, Bool.false_eq_true]
      push_cast [show 2 ≤ 2 * p + q by omega]
      omega
  -- the scaled quotient `r = 2^D / N` and its bounds `2^(2p−2) ≤ r < 2^(2p)`
  set Mr : ℝ := (2 : ℝ) ^ (D : ℕ) / N with hMr
  have hMr0 : 0 < Mr := by positivity
  have hMlo : (2 : ℝ) ^ (2 * (p : ℤ) - 2) ≤ Mr := by
    rw [hMr, le_div_iff₀ hNpos, hD_def]
    rcases Bool.eq_false_or_eq_true odd with ho | ho
    · rcases Bool.eq_false_or_eq_true bnd with hbo | hbo
      · obtain ⟨-, hn2⟩ := hbnd.mp hbo
        have hN2 : N = (2 : ℝ) ^ ((q : ℤ) - 1) := by
          rw [hN, hn2, show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; push_cast; rfl
        rw [ho, hbo, ite_eq_left rfl, ite_eq_left rfl, hN2, ← zpow_natCast,
          ← zpow_add₀ (by norm_num)]
        apply zpow_le_zpow_right₀ (by norm_num)
        push_cast [show 3 ≤ 2 * p + q by omega]; omega
      · rw [ho, hbo, ite_eq_left rfl, ite_eq_right (by simp)]
        calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) * N ≤ 2 ^ (2 * (p : ℤ) - 2) * 2 ^ (q : ℤ) :=
              mul_le_mul_of_nonneg_left hb.2.le (zpow_pos (by norm_num) _).le
          _ ≤ (2 : ℝ) ^ (2 * p + q - 1 : ℕ) := by
              rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
              apply zpow_le_zpow_right₀ (by norm_num)
              push_cast [show 1 ≤ 2 * p + q by omega]; omega
    · rw [ho, ite_eq_right (by simp)]
      calc (2 : ℝ) ^ (2 * (p : ℤ) - 2) * N ≤ 2 ^ (2 * (p : ℤ) - 2) * 2 ^ (q : ℤ) :=
            mul_le_mul_of_nonneg_left hb.2.le (zpow_pos (by norm_num) _).le
        _ = (2 : ℝ) ^ (2 * p + q - 2 : ℕ) := by
            rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
            congr 1
            push_cast [show 2 ≤ 2 * p + q by omega]; ring
  have hMhi : Mr < (2 : ℝ) ^ (2 * (p : ℤ)) := by
    rw [hMr, div_lt_iff₀ hNpos, hD_def]
    rcases Bool.eq_false_or_eq_true odd with ho | ho
    · rcases Bool.eq_false_or_eq_true bnd with hbo | hbo
      · obtain ⟨-, hn2⟩ := hbnd.mp hbo
        have hN2 : N = (2 : ℝ) ^ ((q : ℤ) - 1) := by
          rw [hN, hn2, show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]; push_cast; rfl
        rw [ho, hbo, ite_eq_left rfl, ite_eq_left rfl, hN2, ← zpow_add₀ (by norm_num),
          ← zpow_natCast]
        apply zpow_lt_zpow_right₀ (by norm_num)
        push_cast [show 3 ≤ 2 * p + q by omega]; omega
      · -- `N > 2^(q−1)` strictly
        have hne : n.toNat ≠ 2 ^ (q - 1) := fun h => by
          have := hbnd.mpr ⟨ho, h⟩; rw [this] at hbo; exact Bool.noConfusion hbo
        have hNgt : (2 : ℝ) ^ ((q : ℤ) - 1) < N := by
          rcases lt_or_eq_of_le hb.1 with h | h
          · exact h
          · exfalso; apply hne
            have : (n.toNat : ℝ) = ((2 ^ (q - 1) : ℕ) : ℝ) := by
              rw [← hN, ← h, show (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) by omega, zpow_natCast]
              push_cast; rfl
            exact_mod_cast this
        rw [ho, hbo, ite_eq_left rfl, ite_eq_right (by simp)]
        calc (2 : ℝ) ^ (2 * p + q - 1 : ℕ) = 2 ^ (2 * (p : ℤ)) * 2 ^ ((q : ℤ) - 1) := by
              rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
              congr 1
              push_cast [show 1 ≤ 2 * p + q by omega]; ring
          _ < 2 ^ (2 * (p : ℤ)) * N := mul_lt_mul_of_pos_left hNgt (zpow_pos (by norm_num) _)
    · rw [ho, ite_eq_right (by simp)]
      calc (2 : ℝ) ^ (2 * p + q - 2 : ℕ) = 2 ^ (2 * (p : ℤ) - 1) * 2 ^ ((q : ℤ) - 1) := by
            rw [← zpow_add₀ (by norm_num), ← zpow_natCast]
            congr 1
            push_cast [show 2 ≤ 2 * p + q by omega]; ring
        _ ≤ 2 ^ (2 * (p : ℤ) - 1) * N :=
            mul_le_mul_of_nonneg_left hb.1 (zpow_pos (by norm_num) _).le
        _ < 2 ^ (2 * (p : ℤ)) * N := by
            apply mul_lt_mul_of_pos_right _ hNpos
            exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  -- the integer square root of `⌊r⌋`
  set pow := (1 : AzNat).shiftLeft D with hpow
  have hpowN : pow.toNat = 2 ^ D := by rw [hpow, AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul]
  clear_value pow
  set Q := pow / n with hQ
  have hQN : Q.toNat = 2 ^ D / n.toNat := by rw [hQ, AzNat.toNat_div, hpowN]
  clear_value Q
  have hQle : (Q.toNat : ℝ) ≤ Mr := by
    rw [hQN, hMr, le_div_iff₀ hNpos, hN]
    exact_mod_cast Nat.div_mul_le_self (2 ^ D) n.toNat
  have hQlt : Mr < Q.toNat + 1 := by
    rw [hQN, hMr, div_lt_iff₀ hNpos, hN]
    have := Nat.lt_div_mul_add (a := 2 ^ D) (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0))
    have h' : 2 ^ D < (2 ^ D / n.toNat + 1) * n.toNat := by
      have := Nat.div_add_mod (2 ^ D) n.toNat
      have := Nat.mod_lt (2 ^ D) (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0))
      nlinarith
    exact_mod_cast h'
  set sr := AzNat.sqrtRem Q with hsr
  clear_value sr
  have hsN : sr.1.toNat = Nat.sqrt Q.toNat := by rw [hsr]; exact AzNat.toNat_sqrtRem_fst Q
  set y : ℝ := Real.sqrt Mr with hy_def
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hsq_le : Nat.sqrt Q.toNat ^ 2 ≤ Q.toNat := Nat.sqrt_le' _
  have hlt_sq : Q.toNat < (Nat.sqrt Q.toNat + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hlo : (sr.1.toNat : ℝ) ≤ y := by
    rw [hsN, hy_def]
    exact le_trans Real.nat_sqrt_le_real_sqrt (Real.sqrt_le_sqrt hQle)
  have hhi : y < sr.1.toNat + 1 := by
    rw [hsN, hy_def]
    calc Real.sqrt Mr < Real.sqrt (Q.toNat + 1) := Real.sqrt_lt_sqrt hMr0.le hQlt
      _ ≤ Nat.sqrt Q.toNat + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          exact_mod_cast hlt_sq
  have hex : (compare (AzNat.square sr.1 * n) pow == .eq) = true ↔ y = sr.1.toNat := by
    rw [beq_iff_eq, show compare (AzNat.square sr.1 * n) pow = AzNat.compare _ _ from rfl,
      AzNat.compare_eq_compare_toNat, ← compare_natCast, compare_eq_iff_eq, AzNat.toNat_mul,
      AzNat.toNat_square, hpowN, hy_def, Real.sqrt_eq_iff_eq_sq hMr0.le (Nat.cast_nonneg _), hMr,
      div_eq_iff hNpos.ne', hN]
    push_cast
    constructor <;> intro h <;> linarith
  have hmid : compare ((1 : AzNat).shiftLeft (D + 2))
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n)
      = compare y ((sr.1.toNat : ℝ) + 1 / 2) := by
    rw [show compare ((1 : AzNat).shiftLeft (D + 2))
        (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n) = AzNat.compare _ _ from rfl,
      AzNat.compare_eq_compare_toNat, ← compare_natCast,
      AzNat.toNat_shiftLeft, AzNat.toNat_one, one_mul, AzNat.toNat_mul, AzNat.toNat_square,
      AzNat.toNat_addUInt64, AzNat.toNat_shiftLeft, UInt64.toNat_one]
    push_cast
    rw [← hN]
    have hmid_pos : (0 : ℝ) < (sr.1.toNat : ℝ) + 1 / 2 := by positivity
    have hL : (2 : ℝ) ^ (D + 2) = Mr * (4 * N) := by
      rw [hMr, pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_comm (4 : ℝ) N, ← mul_assoc,
        div_mul_cancel₀ _ hNpos.ne']
    have hRt : ((sr.1.toNat : ℝ) * 2 + 1) ^ 2 * N
        = ((sr.1.toNat : ℝ) + 1 / 2) ^ 2 * (4 * N) := by ring
    rw [hL, hRt, compare_mul_right_pos _ _ _ (by positivity), hy_def]
    rcases lt_trichotomy (Real.sqrt Mr) ((sr.1.toNat : ℝ) + 1 / 2) with h | h | h
    · rw [compare_lt_iff_lt.mpr h]
      rw [Real.sqrt_lt' hmid_pos] at h
      exact compare_lt_iff_lt.mpr h
    · rw [compare_eq_iff_eq.mpr h]
      rw [Real.sqrt_eq_iff_eq_sq hMr0.le hmid_pos.le] at h
      exact compare_eq_iff_eq.mpr h
    · rw [compare_gt_iff_gt.mpr h]
      rw [Real.lt_sqrt hmid_pos.le] at h
      exact compare_gt_iff_gt.mpr h
  obtain ⟨hR, htag⟩ := roundFromFloor_spec y sr.1 _ _ mode hlo hhi hex hmid
  set ro := roundFromFloor sr.1 (compare (AzNat.square sr.1 * n) pow == .eq)
    (compare ((1 : AzNat).shiftLeft (D + 2))
      (AzNat.square ((sr.1.shiftLeft 1).addUInt64 1) * n)) mode with hro
  clear_value ro
  -- the exact value `v = 1/√x = y · 2^w`
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
  set v : ℝ := (Real.sqrt (finiteVal true e n))⁻¹ with hv_def
  have hv : v = y * (2 : ℝ) ^ w.toInt := by
    rw [hv_def, hy_def, finiteVal_true_eq, hs, ← hN, ← Real.sqrt_inv, mul_inv,
      show ((2 : ℝ) ^ (e.toInt - q))⁻¹ = 2 ^ ((q : ℤ) - e.toInt) by
        rw [← zpow_neg]; congr 1; ring,
      show ((q : ℤ) - e.toInt) = D + 2 * w.toInt by rw [hkey], zpow_add₀ (by norm_num),
      show (2 : ℝ) ^ (2 * w.toInt) = (2 ^ w.toInt) ^ 2 by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
      zpow_natCast, ← mul_assoc, ← div_eq_inv_mul, ← hMr, Real.sqrt_mul hMr0.le,
      Real.sqrt_sq h2w.le]
  clear_value v
  have hylo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ y := by
    rw [hy_def, Real.le_sqrt (zpow_pos (by norm_num) _).le hMr0.le, ← zpow_natCast, ← zpow_mul]
    convert hMlo using 2; push_cast; ring
  have hyhi : y < (2 : ℝ) ^ (p : ℤ) := by
    rw [hy_def, Real.sqrt_lt' (zpow_pos (by norm_num) _), ← zpow_natCast, ← zpow_mul]
    convert hMhi using 2; push_cast; ring
  have hypos : 0 < y := lt_of_lt_of_le (zpow_pos (by norm_num) _) hylo
  have hv0 : v ≠ 0 := by rw [hv]; positivity
  have hvabs : |v| = y * (2 : ℝ) ^ w.toInt := by rw [hv, abs_of_pos (by positivity)]
  have hvpos : 0 < |v| := by rw [hvabs]; positivity
  have hlog : Int.log 2 |v| = w.toInt + p - 1 := by
    apply le_antisymm
    · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, zpow_add₀ (by norm_num), mul_comm]
        exact mul_lt_mul_of_pos_left hyhi h2w)
      omega
    · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hvpos).mp (by
        rw [hvabs, show w.toInt + p - 1 = ((p : ℤ) - 1) + w.toInt by ring, zpow_add₀ (by norm_num)]
        exact mul_le_mul_of_nonneg_right hylo h2w.le)
  have hscale : precScale 2 p v = (2 : ℝ) ^ w.toInt := by
    unfold precScale
    rw [hlog]
    push_cast
    congr 1
    ring
  have hyv : v / (2 : ℝ) ^ w.toInt = y := by rw [hv, mul_div_cancel_right₀ _ h2w.ne']
  have hround : (round (floatSet p) mode v).val
      = ((((AzInt.mkNorm true ro.1).toInt : ℝ) * 2 ^ w.toInt : ℝ) : EReal) := by
    rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hyv, hR,
      AzInt.toInt_mkNorm_true]
  obtain ⟨hb1, hb2⟩ := abs_toInt_round_bounds p hp mode y (by rw [abs_of_pos hypos]; exact hylo)
    (by rw [abs_of_pos hypos]; exact hyhi)
  rw [hR] at hb1 hb2
  have habsR : ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) = |(ro.1.toNat : ℤ)| := by
    rw [AzInt.abs_toNat_eq, AzInt.toInt_mkNorm_true]
  have hlo' : 2 ^ (p - 1) ≤ (AzInt.mkNorm true ro.1).abs.toNat := by
    have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) := by
      rw [habsR]; exact hb1
    exact_mod_cast this
  have hhi' : (AzInt.mkNorm true ro.1).abs.toNat ≤ 2 ^ p := by
    have : ((AzInt.mkNorm true ro.1).abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by
      rw [habsR]; exact hb2
    exact_mod_cast this
  obtain ⟨hRval, hRprec⟩ := normalizeCarry_spec (AzInt.mkNorm true ro.1) p hp
    (w + (AzNat.ofNat p).toAzInt) hlo' hhi'
  have hep : (w + (AzNat.ofNat p).toAzInt).toInt - p = w.toInt := by
    rw [AzInt.toInt_add, toInt_toAzInt, AzNat.toNat_ofNat]; ring
  rw [hep] at hRval
  symm
  refine Prod.ext ?_ ?_
  · have hgoal : (roundVal p mode (some (v : EReal))).1
        = normalizeCarry (AzInt.mkNorm true ro.1) (w + (AzNat.ofNat p).toAzInt) p :=
      toVal_injective p (ofEReal_spec p mode v).1 (Or.inl hRprec)
        (by rw [fst_roundVal, ofVal_some, (ofEReal_spec p mode v).2, hround, hRval])
    exact hgoal
  · show (roundVal p mode (some (v : EReal))).2 = ro.2
    rw [(roundVal_coe p mode v).2, hround, compare_coe_coe, htag, AzInt.toInt_mkNorm_true,
      Int.cast_natCast, hv, compare_mul_right_pos _ _ _ h2w]

/-- Reciprocal square root is the float lift of `Spec.rsqrt`. -/
theorem rsqrtPrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    rsqrtPrecRound x p mode = liftVal Spec.rsqrt x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [rsqrtPrecRound]
  | zero => simp [rsqrtPrecRound]
  | finite s e q m hv =>
    cases s with
    | true =>
      simp only [rsqrtPrecRound, toVal_finite, Option.bind_some, ↓reduceIte]
      rw [finiteVal_eq_core true e hv,
        Spec.rsqrt_coe _ (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv)),
        rsqrtCore_eq e hv p mode]
    | false =>
      simp only [rsqrtPrecRound, toVal_finite, Option.bind_some, Bool.false_eq_true, ↓reduceIte]
      rw [finiteVal_eq_core false e hv, finiteVal_false,
        Spec.rsqrt_coe_neg _ (neg_neg_iff_pos.mpr
          (finiteVal_true_pos' e _ (coreSignificand_ne_zero hv))), roundVal_none]

end Azurite.AzFloat
