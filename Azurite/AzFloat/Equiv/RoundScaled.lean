/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzFloat.RoundScaled
import Azurite.AzInt.Equiv.Parity
import Azurite.AzInt.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight

/-!
# Correctness of the shared rounding primitives

`roundScaled_eq_roundVal`: rounding an exact `±S · 2^w` is `roundVal`.  `roundVal_congr_cell`:
two reals with no point or midpoint of the destination grid strictly between them round
identically in every mode, with equal comparison tags (the lemma behind the far case of
addition and behind Ziv's strategy).  `normalizeCarry_spec`, `roundFromFloor_spec`, the special
values of `roundVal`, and value lemmas for finite floats with an arbitrary significand.
-/

namespace Azurite.AzFloat

open RoundingTarget

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

@[simp] theorem roundVal_top (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode (some ⊤) = (infinity true, .eq) :=
  roundVal_of_toVal p mode (infinity true) ⊤ (Or.inr rfl) rfl

@[simp] theorem roundVal_bot (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode (some ⊥) = (infinity false, .eq) :=
  roundVal_of_toVal p mode (infinity false) ⊥ (Or.inr rfl) rfl

@[simp] theorem roundVal_zero (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode (some 0) = (zero, .eq) :=
  roundVal_of_toVal p mode zero 0 (Or.inr rfl) rfl

@[simp] theorem roundVal_inf (p : ℕ) [NeZero p] (mode : RoundingMode) (b : Bool) :
    roundVal p mode (some (if b then ⊤ else ⊥)) = (infinity b, .eq) :=
  roundVal_of_toVal p mode (infinity b) _ (Or.inr rfl) rfl

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

theorem decide_pos_finiteVal (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) :
    decide (0 < finiteVal s e m) = s := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, finiteVal_pos_iff s e m hm]

end Azurite.AzFloat
