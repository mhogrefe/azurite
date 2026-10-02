/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzNat.Equiv.Add
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

theorem add_coe_coe (x y : ℝ) : add (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
  unfold add
  rw [ite_eq_right (by simp), EReal.coe_add]

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

end Azurite.AzFloat
