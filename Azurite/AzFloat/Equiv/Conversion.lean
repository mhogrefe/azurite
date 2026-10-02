/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Equiv.Basic
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Sub
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Shift
import Azurite.AzRat.Equiv.ToSci
import Azurite.Rounding.SciPrecision

/-!
# Correctness of the `AzFloat` conversions

* `toVal_ofAzNat`, `toVal_ofAzInt`: the exact conversions are exact.
* `toVal_of_toAzRat?`: `toAzRat?` returns the value.
* `toVal_ofAzRatRound`: `ofAzRatRound q p mode` is `round (precisionSet 2 p) mode (toRat q)`,
  the rounding of `q` to the numbers with at most `p` significant bits — the same target as
  `toSci` in base `2` with precision `p` (`Rounding/SciPrecision.lean`).  Its precision is `p`
  (`precision?_ofAzRatRound`) and its `Ordering` compares the result with `q`
  (`snd_ofAzRatRound`).
-/

namespace Azurite

instance : Fact (1 < 2) := ⟨by norm_num⟩

namespace AzFloat

open RoundingTarget

theorem toInt_toAzInt (n : AzNat) : n.toAzInt.toInt = n.toNat := rfl

/-! ### Exact conversions -/

theorem finiteVal_self (s : Bool) (m : AzNat) :
    finiteVal s (AzNat.ofNat m.size).toAzInt m = (if s then 1 else -1) * (m.toNat : ℝ) := by
  unfold finiteVal
  rw [toInt_toAzInt, AzNat.toNat_ofNat, sub_self, zpow_zero, mul_one]

theorem toVal_ofAzNat (n : AzNat) : toVal (ofAzNat n) = some ((n.toNat : ℝ) : EReal) := by
  unfold ofAzNat
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [toVal_mkFinite _ _ _ _ hn, finiteVal_self]
    simp

theorem toVal_ofAzInt (z : AzInt) : toVal (ofAzInt z) = some ((z.toInt : ℝ) : EReal) := by
  unfold ofAzInt
  by_cases hz : z.abs = 0
  · rw [hz, mkFinite_zero]
    have : z.toInt = 0 := by
      unfold AzInt.toInt
      rw [hz, AzNat.toNat_zero]
      cases z.sign <;> simp
    rw [this]
    simp
  · rw [toVal_mkFinite _ _ _ _ hz, finiteVal_self]
    congr 2
    unfold AzInt.toInt
    rcases Bool.eq_false_or_eq_true z.sign with hs | hs <;> simp [hs]

/-! ### `toAzRat?` -/

theorem toVal_of_toAzRat? (x : AzFloat) (r : AzRat) (h : x.toAzRat? = some r) :
    x.toVal = some ((AzRat.toRat r : ℝ) : EReal) := by
  cases x with
  | nan => simp [toAzRat?] at h
  | infinity s => simp [toAzRat?] at h
  | zero =>
    simp only [toAzRat?, Option.some.injEq] at h
    subst h
    simp
  | finite s e p m hv =>
    simp only [toAzRat?, Option.some.injEq] at h
    subst h
    rw [toVal_finite]
    congr 2
    have hm : m ≠ 0 := ne_zero_of_size_pos (by
      rw [hv.size_eq]; exact lt_of_lt_of_le hv.pos (le_alignedBits p))
    set d := e - (AzNat.ofNat m.size).toAzInt with hd
    have hdI : d.toInt = e.toInt - m.size := by
      rw [hd, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
    have hbase : (AzRat.toRat (AzInt.mkNorm s m).toAzRat : ℝ)
        = (if s then 1 else -1) * (m.toNat : ℝ) := by
      rw [AzRat.toRat_toAzRat_int]
      cases s <;> simp [AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false m hm]
    unfold finiteVal
    rw [← hdI]
    have hsgn : d.toInt = if d.sign then (d.abs.toNat : ℤ) else -(d.abs.toNat : ℤ) := rfl
    by_cases hs : d.sign = true
    · rw [ite_eq_left hs, AzRat.toRat_shiftLeft]
      push_cast
      rw [hbase, hsgn, ite_eq_left hs, zpow_natCast]
    · rw [ite_eq_right hs, AzRat.toRat_shiftRight]
      push_cast
      rw [hbase, hsgn, ite_eq_right hs, zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem isSome_toAzRat? (x : AzFloat) : x.toAzRat?.isSome = x.isFinite := by
  cases x <;> rfl

/-! ### Rounding a rational -/

/-- Floor and ceiling of a real of magnitude at least the integer `B ≥ 0` have magnitude at
least `B`. -/
theorem le_abs_floor_ceil (y : ℝ) (B : ℤ) (hB : 0 ≤ B) (hy : (B : ℝ) ≤ |y|) :
    B ≤ |⌊y⌋| ∧ B ≤ |⌈y⌉| := by
  rcases le_abs'.mp hy with h | h
  · -- y ≤ -B
    have h1 : ⌈y⌉ ≤ -B := Int.ceil_le.mpr (by push_cast; exact h)
    have h2 : ⌊y⌋ ≤ ⌈y⌉ := Int.floor_le_ceil y
    constructor
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonpos (by omega)]; omega
  · have h1 : B ≤ ⌊y⌋ := Int.le_floor.mpr h
    have h2 : ⌊y⌋ ≤ ⌈y⌉ := Int.floor_le_ceil y
    constructor
    · rw [abs_of_nonneg (by omega)]; exact h1
    · rw [abs_of_nonneg (by omega)]; omega

/-- The core of `ofAzRatRound` on a nonzero input: the result is `mkFinite` of a `p`-bit
significand whose value is the rounding to `precisionSet 2 p`. -/
theorem ofAzRatRound_spec (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h0 : q.num ≠ 0) :
    ∃ (s : Bool) (e' : ℤ) (n : AzNat),
      (ofAzRatRound q p mode).1 = mkFinite s (AzInt.ofInt e') p n ∧ n.size = p ∧
      ((finiteVal s (AzInt.ofInt e') n : ℝ) : EReal)
        = (RoundingTarget.round (precisionSet 2 p) mode (AzRat.toRat q : ℝ)).val ∧
      (ofAzRatRound q p mode).2
        = compare (finiteVal s (AzInt.ofInt e') n) (AzRat.toRat q : ℝ) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold ofAzRatRound
  rw [ite_eq_right hp.ne', ite_eq_right h0]
  simp only []
  set x : ℝ := (AzRat.toRat q : ℝ) with hx_def
  have hx : x ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have h2 : (2 : UInt64).toNat = 2 := rfl
  have hlog : AzRat.floorLogBaseAbs 2 q = Int.log 2 |x| := by
    rw [AzRat.floorLogBaseAbs_eq 2 (by decide) q h0, h2]
  set e := Int.log 2 |x| with he
  rw [hlog]
  set u := precScale 2 p x with hu_def
  have hu_eq : u = (2 : ℝ) ^ (e - p + 1) := by
    rw [hu_def]; unfold precScale; rw [← he]; norm_num
  have hu : 0 < u := by rw [hu_eq]; exact zpow_pos (by norm_num) _
  set sc : ℤ := (p : ℤ) - 1 - e with hsc
  have hpow : ((2 : UInt64).toNat : ℝ) ^ sc = u⁻¹ := by
    rw [h2, hu_eq, ← zpow_neg]; push_cast; congr 1; rw [hsc]; ring
  have hr := AzRat.toInt_scaledRound q 2 (by decide) sc mode
  rw [hpow, ← div_eq_mul_inv, ← hx_def] at hr
  have hrI : toInt (RoundingTarget.round intSet mode (x / u))
      = (AzRat.scaledRound q 2 sc mode).1.toInt :=
    toInt_eq_of_val hr
  set r := AzRat.scaledRound q 2 sc mode with hr_def
  -- bounds on the rounded integer: `2^(p-1) ≤ |r| ≤ 2^p`
  obtain ⟨hlo, hhi⟩ := abs_div_precScale_bounds (b := 2) (p := p) x hx
  rw [← hu_def] at hlo hhi
  have hlo' : (((2 ^ (p - 1) : ℕ) : ℤ) : ℝ) ≤ |x / u| := by
    push_cast
    rw [← zpow_natCast, Nat.cast_sub hp]
    simpa using hlo
  have hhi' : |x / u| < (((2 ^ p : ℕ) : ℤ) : ℝ) := by
    push_cast
    rw [← zpow_natCast]
    simpa using hhi
  have habs : (r.1.abs.toNat : ℤ) = |r.1.toInt| := by
    unfold AzInt.toInt; cases r.1.sign <;> simp
  have hbounds : (2 ^ (p - 1) : ℕ) ≤ r.1.abs.toNat ∧ r.1.abs.toNat ≤ 2 ^ p := by
    obtain ⟨hf1, hc1⟩ := le_abs_floor_ceil (x / u) _ (by positivity) hlo'
    obtain ⟨hf2, hc2⟩ := AzRat.floor_ceil_abs_le (x / u) _ hhi'
    rcases AzRat.toInt_round_intSet_eq_floor_or_ceil mode (x / u) with h | h <;> rw [hrI] at h
    · constructor
      · have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ (r.1.abs.toNat : ℤ) := by rw [habs, h]; exact hf1
        exact_mod_cast this
      · have : (r.1.abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by rw [habs, h]; exact hf2
        exact_mod_cast this
    · constructor
      · have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ (r.1.abs.toNat : ℤ) := by rw [habs, h]; exact hc1
        exact_mod_cast this
      · have : (r.1.abs.toNat : ℤ) ≤ ((2 ^ p : ℕ) : ℤ) := by rw [habs, h]; exact hc2
        exact_mod_cast this
  have hval : (RoundingTarget.round (precisionSet 2 p) mode x).val
      = (((r.1.toInt : ℝ) * u : ℝ) : EReal) := by
    rw [val_round_precisionSet mode x hx, hrI, ← hu_def]
  have hsign : (r.1.toInt : ℝ) = (if r.1.sign then 1 else -1) * (r.1.abs.toNat : ℝ) := by
    unfold AzInt.toInt; cases r.1.sign <;> simp
  have htag := AzRat.snd_scaledRound q 2 (by decide) sc mode
  rw [hpow, ← div_eq_mul_inv, ← hx_def, ← hr_def] at htag
  have hcmp : ∀ v : ℝ, v = (r.1.toInt : ℝ) * u →
      r.2 = compare v x := by
    intro v hv
    rw [htag, hv]
    rcases lt_trichotomy ((r.1.toInt : ℤ) : ℝ) (x / u) with h | h | h
    · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr]
      rwa [lt_div_iff₀ hu] at h
    · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr]
      rw [h, div_mul_cancel₀ _ hu.ne']
    · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr]
      rwa [div_lt_iff₀ hu] at h
  by_cases hsz : r.1.abs.size = p + 1
  · rw [ite_eq_left hsz]
    -- `n = 2^p`
    have hge : 2 ^ p ≤ r.1.abs.toNat := by
      rw [← Nat.lt_size, AzNat.size_toNat, hsz]; omega
    have hn : r.1.abs.toNat = 2 ^ p := le_antisymm hbounds.2 hge
    refine ⟨r.1.sign, e + 2, r.1.abs.shiftRight 1, rfl, ?_, ?_, ?_⟩
    · rw [← AzNat.size_toNat, AzNat.toNat_shiftRight, hn, pow_one, Nat.pow_div hp (by norm_num),
        Nat.size_pow]
      omega
    · rw [hval]
      congr 1
      unfold finiteVal
      rw [AzInt.toInt_ofInt, ← AzNat.size_toNat, AzNat.toNat_shiftRight, hn, pow_one,
        Nat.pow_div hp (by norm_num), Nat.size_pow, hsign, hn, hu_eq]
      push_cast
      rw [← zpow_natCast, ← zpow_natCast, Nat.cast_sub hp]
      rw [mul_assoc, mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      congr 2
      push_cast
      ring
    · apply hcmp
      unfold finiteVal
      rw [AzInt.toInt_ofInt, ← AzNat.size_toNat, AzNat.toNat_shiftRight, hn, pow_one,
        Nat.pow_div hp (by norm_num), Nat.size_pow, hsign, hn, hu_eq]
      push_cast
      rw [← zpow_natCast, ← zpow_natCast, Nat.cast_sub hp]
      rw [mul_assoc, mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      congr 2
      push_cast
      ring
  · rw [ite_eq_right hsz]
    have hsize : r.1.abs.size = p := by
      have h1 : r.1.abs.size ≤ p + 1 := by
        rw [← AzNat.size_toNat, Nat.size_le]
        calc r.1.abs.toNat ≤ 2 ^ p := hbounds.2
          _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 : p ≤ r.1.abs.size := by
        rw [← AzNat.size_toNat]
        have := Nat.lt_size.mpr hbounds.1
        omega
      omega
    refine ⟨r.1.sign, e + 1, r.1.abs, rfl, hsize, ?_, ?_⟩
    · rw [hval]
      congr 1
      unfold finiteVal
      rw [AzInt.toInt_ofInt, hsize, hsign, hu_eq]
      congr 2
      ring
    · apply hcmp
      unfold finiteVal
      rw [AzInt.toInt_ofInt, hsize, hsign, hu_eq]
      congr 2
      ring

/-- `ofAzRatRound q p mode` is the rounding of `q` to the numbers with at most `p`
significant bits. -/
theorem toVal_ofAzRatRound (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    toVal (ofAzRatRound q p mode).1
      = some (RoundingTarget.round (precisionSet 2 p) mode (AzRat.toRat q : ℝ)).val := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  by_cases h0 : q.num = 0
  · have hq : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr h0
    unfold ofAzRatRound
    rw [ite_eq_right hp.ne', ite_eq_left h0, hq,
      val_round_of_mem (precisionSet 2 p) mode (x := (0 : ℝ)) (Or.inl (by simp))]
    simp
  · obtain ⟨s, e', n, heq, hsize, hval, -⟩ := ofAzRatRound_spec q p mode h0
    have hn : n ≠ 0 := ne_zero_of_size_pos (hsize ▸ hp)
    rw [heq, toVal_mkFinite _ _ _ _ hn, hval]

/-- The precision of a rounded nonzero rational is the requested one. -/
theorem precision?_ofAzRatRound (q : AzRat) (p : ℕ) (hp : 0 < p) (mode : RoundingMode)
    (h0 : q.num ≠ 0) : precision? (ofAzRatRound q p mode).1 = some p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨s, e', n, heq, hsize, -, -⟩ := ofAzRatRound_spec q p mode h0
  have hn : n ≠ 0 := ne_zero_of_size_pos (hsize ▸ hp)
  rw [heq, precision?_mkFinite _ _ _ _ hn hsize.le]

/-- The `Ordering` returned by `ofAzRatRound` compares the result with the input. -/
theorem snd_ofAzRatRound (q : AzRat) (p : ℕ) (hp : 0 < p) (mode : RoundingMode) :
    ∃ v : ℝ, toVal (ofAzRatRound q p mode).1 = some (v : EReal) ∧
      (ofAzRatRound q p mode).2 = compare v (AzRat.toRat q : ℝ) := by
  by_cases h0 : q.num = 0
  · have hq : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr h0
    unfold ofAzRatRound
    rw [ite_eq_right hp.ne', ite_eq_left h0, hq]
    exact ⟨0, by simp, by simp⟩
  · have : NeZero p := ⟨hp.ne'⟩
    obtain ⟨s, e', n, heq, hsize, -, htag⟩ := ofAzRatRound_spec q p mode h0
    have hn : n ≠ 0 := ne_zero_of_size_pos (hsize ▸ hp)
    exact ⟨_, by rw [heq, toVal_mkFinite _ _ _ _ hn], htag⟩

theorem toVal_ofAzRat (q : AzRat) (p : ℕ) [NeZero p] :
    toVal (ofAzRat q p)
      = some (RoundingTarget.round (precisionSet 2 p) .Nearest (AzRat.toRat q : ℝ)).val :=
  toVal_ofAzRatRound q p .Nearest

end AzFloat

end Azurite
