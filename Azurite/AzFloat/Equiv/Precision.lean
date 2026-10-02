/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Precision
import Azurite.AzFloat.Equiv.Rounding
import Azurite.AzInt.Equiv.ShiftRightRound
import Azurite.AzNat.Equiv.ShiftRight

/-!
# Correctness of the precision changes

`setPrecRound_eq_liftE`: `setPrecRound x p mode = liftE id x p mode`, so re-rounding is the
lift of the identity (its value is `x` rounded to precision `p`, its tag the comparison with
`x`).  The shared core is `normalize_spec`: an integer `r` with `2^(p−1) ≤ |r| ≤ 2^p`, placed
at exponent `e` with the carry to `2^p` halved, is a float of precision `p` and value
`r · 2^(e − p)`.  Also `ulp?_spec` (the unit in the last place is `2^(e − p)`).
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The core significand -/

theorem toNat_eq_core_mul {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    m.toNat = (coreSignificand p m).toNat * 2 ^ (alignedBits p - p) := by
  unfold coreSignificand
  rw [AzNat.toNat_shiftRight]
  obtain ⟨c, hc⟩ := hv.dvd
  rw [hc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), mul_comm]

theorem size_coreSignificand {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    (coreSignificand p m).size = p := by
  obtain ⟨hlo, hhi⟩ := toNat_bounds_of_valid hv
  have hm := toNat_eq_core_mul hv
  have hB := le_alignedBits p
  have hp := hv.pos
  have hsplit : (2 : ℕ) ^ alignedBits p = 2 ^ p * 2 ^ (alignedBits p - p) := by
    rw [← pow_add]; congr 1; omega
  have hsplit' : (2 : ℕ) ^ (alignedBits p - 1) = 2 ^ (p - 1) * 2 ^ (alignedBits p - p) := by
    rw [← pow_add]; congr 1; omega
  rw [← AzNat.size_toNat]
  apply le_antisymm
  · rw [Nat.size_le]
    by_contra h
    push Not at h
    have : 2 ^ p * 2 ^ (alignedBits p - p) ≤ m.toNat := by
      rw [hm]; exact Nat.mul_le_mul_right _ h
    omega
  · have h : 2 ^ (p - 1) ≤ (coreSignificand p m).toNat := by
      rw [hsplit', hm] at hlo
      exact le_of_mul_le_mul_right hlo (Nat.two_pow_pos _)
    have := Nat.lt_size.mpr h
    omega

theorem coreSignificand_ne_zero {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    coreSignificand p m ≠ 0 :=
  ne_zero_of_size_pos (by rw [size_coreSignificand hv]; exact hv.pos)

/-- The value through the core significand: `± core · 2^(e − p)`. -/
theorem finiteVal_eq_core (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    finiteVal s e m = finiteVal s e (coreSignificand p m) := by
  rw [finiteVal_eq_aligned s e hv]
  unfold finiteVal
  rw [size_coreSignificand hv, toNat_eq_core_mul hv]
  have hB := le_alignedBits p
  push_cast
  rw [show (2 : ℝ) ^ (alignedBits p - p : ℕ) = (2 : ℝ) ^ ((alignedBits p : ℤ) - p) by
    rw [← zpow_natCast]; congr 1; rw [Nat.cast_sub hB]]
  have h2 : (2 : ℝ) ^ (e.toInt - p)
      = 2 ^ ((alignedBits p : ℤ) - p) * 2 ^ (e.toInt - alignedBits p) := by
    rw [← zpow_add₀ (by norm_num)]; congr 1; ring
  rw [h2]
  ring

/-! ### The exponent is the logarithm -/

theorem log_abs_finiteVal (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    Int.log 2 |finiteVal s e m| = e.toInt - 1 := by
  obtain ⟨hlo, hhi⟩ := abs_finiteVal_bounds s e hv
  have hpos : 0 < |finiteVal s e m| := lt_of_lt_of_le (zpow_pos (by norm_num) _) hlo
  apply le_antisymm
  · have h := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by simpa using hhi)
    omega
  · exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos).mp (by simpa using hlo)

theorem finiteVal_ne_zero (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    finiteVal s e m ≠ 0 := by
  intro h
  have := (abs_finiteVal_bounds s e hv).1
  rw [h, abs_zero] at this
  exact absurd this (not_le.mpr (zpow_pos (by norm_num) _))

/-- The local scale of a float's value at precision `p` is `2^(e − p)`. -/
theorem precScale_finiteVal (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (p : ℕ) : precScale 2 p (finiteVal s e m) = (2 : ℝ) ^ (e.toInt - p) := by
  unfold precScale
  rw [log_abs_finiteVal s e hv]
  push_cast
  congr 1
  ring

/-! ### Normalizing a rounded integer -/

/-- Floor and ceiling of `y` with `2^(p−1) ≤ |y| < 2^p` have magnitude in `[2^(p−1), 2^p]`. -/
theorem abs_toInt_round_bounds (p : ℕ) (hp : 0 < p) (mode : RoundingMode) (y : ℝ)
    (hlo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |y|) (hhi : |y| < (2 : ℝ) ^ (p : ℤ)) :
    ((2 ^ (p - 1) : ℕ) : ℤ) ≤ |toInt (round intSet mode y)| ∧
      |toInt (round intSet mode y)| ≤ ((2 ^ p : ℕ) : ℤ) := by
  have hlo' : (((2 ^ (p - 1) : ℕ) : ℤ) : ℝ) ≤ |y| := by
    push_cast; rw [← zpow_natCast, Nat.cast_sub hp]; simpa using hlo
  have hhi' : |y| < (((2 ^ p : ℕ) : ℤ) : ℝ) := by
    push_cast; rw [← zpow_natCast]; exact hhi
  obtain ⟨hf1, hc1⟩ := le_abs_floor_ceil y _ (by positivity) hlo'
  obtain ⟨hf2, hc2⟩ := AzRat.floor_ceil_abs_le y _ hhi'
  rcases AzRat.toInt_round_intSet_eq_floor_or_ceil mode y with h | h <;> rw [h]
  · exact ⟨hf1, hf2⟩
  · exact ⟨hc1, hc2⟩

/-- An integer `r` with `2^(p−1) ≤ |r| ≤ 2^p`, placed at exponent `e` (with a carry to `2^p`
halved and the exponent raised), is a float of precision `p` with value `r · 2^(e − p)`. -/
theorem normalize_spec (r : AzInt) (p : ℕ) (hp : 0 < p) (e : AzInt)
    (hlo : 2 ^ (p - 1) ≤ r.abs.toNat) (hhi : r.abs.toNat ≤ 2 ^ p) :
    (if r.abs.size = p + 1 then mkFinite r.sign (e + 1) p (r.abs.shiftRight 1)
      else mkFinite r.sign e p r.abs).toVal
        = some (((r.toInt : ℝ) * (2 : ℝ) ^ (e.toInt - p) : ℝ) : EReal) ∧
    (if r.abs.size = p + 1 then mkFinite r.sign (e + 1) p (r.abs.shiftRight 1)
      else mkFinite r.sign e p r.abs).precision? = some p := by
  have hsign : (r.toInt : ℝ) = (if r.sign then 1 else -1) * (r.abs.toNat : ℝ) := by
    unfold AzInt.toInt; cases r.sign <;> simp
  by_cases hsz : r.abs.size = p + 1
  · rw [ite_eq_left hsz]
    have hge : 2 ^ p ≤ r.abs.toNat := by
      rw [← Nat.lt_size, AzNat.size_toNat, hsz]; omega
    have hn : r.abs.toNat = 2 ^ p := le_antisymm hhi hge
    have hhalf : (r.abs.shiftRight 1).toNat = 2 ^ (p - 1) := by
      rw [AzNat.toNat_shiftRight, hn, pow_one, Nat.pow_div hp (by norm_num)]
    have hhalf_size : (r.abs.shiftRight 1).size = p := by
      rw [← AzNat.size_toNat, hhalf, Nat.size_pow]; omega
    have hne : r.abs.shiftRight 1 ≠ 0 := ne_zero_of_size_pos (hhalf_size ▸ hp)
    refine ⟨?_, precision?_mkFinite _ _ _ _ hne hhalf_size.le⟩
    rw [toVal_mkFinite _ _ _ _ hne]
    congr 2
    unfold finiteVal
    rw [hhalf_size, hhalf, AzInt.toInt_add, hsign, hn, show (1 : AzInt).toInt = 1 from rfl]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, Nat.cast_sub hp]
    rw [mul_assoc, mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
    congr 2
    push_cast
    ring
  · rw [ite_eq_right hsz]
    have hsize : r.abs.size = p := by
      have h1 : r.abs.size ≤ p + 1 := by
        rw [← AzNat.size_toNat, Nat.size_le]
        calc r.abs.toNat ≤ 2 ^ p := hhi
          _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 : p ≤ r.abs.size := by
        rw [← AzNat.size_toNat]
        have := Nat.lt_size.mpr hlo
        omega
      omega
    have hne : r.abs ≠ 0 := ne_zero_of_size_pos (hsize ▸ hp)
    refine ⟨?_, precision?_mkFinite _ _ _ _ hne hsize.le⟩
    rw [toVal_mkFinite _ _ _ _ hne]
    congr 2
    unfold finiteVal
    rw [hsize, hsign]

/-! ### `setPrecRound` is the lift of the identity -/

theorem compare_coe_coe (a b : ℝ) : compare (a : EReal) (b : EReal) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (EReal.coe_lt_coe_iff.mpr h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (EReal.coe_lt_coe_iff.mpr h)]

theorem compare_mul_right_pos (a b c : ℝ) (hc : 0 < c) : compare (a * c) (b * c) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (mul_lt_mul_of_pos_right h hc)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (mul_lt_mul_of_pos_right h hc)]

/-- Re-rounding to precision `p` is the lift of the identity. -/
theorem setPrecRound_eq_liftE (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    setPrecRound x p mode = liftE id x p mode := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  cases x with
  | nan => unfold setPrecRound; rw [ite_eq_right hp.ne']; rfl
  | infinity s =>
    unfold setPrecRound
    rw [ite_eq_right hp.ne']
    exact (roundVal_of_toVal p mode (infinity s) _ (Or.inr rfl) rfl).symm
  | zero =>
    unfold setPrecRound
    rw [ite_eq_right hp.ne']
    exact (roundVal_of_toVal p mode zero _ (Or.inr rfl) rfl).symm
  | finite s e q m hv =>
    unfold setPrecRound
    rw [ite_eq_right hp.ne']
    simp only []
    set n := coreSignificand q m with hn_def
    have hn_size : n.size = q := size_coreSignificand hv
    have hn : n ≠ 0 := coreSignificand_ne_zero hv
    have hval : finiteVal s e m = finiteVal s e n := finiteVal_eq_core s e hv
    show _ = roundVal p mode (some ((finiteVal s e m : ℝ) : EReal))
    by_cases hqp : q ≤ p
    · rw [ite_eq_left hqp]
      symm
      refine roundVal_of_toVal p mode _ _ (Or.inl (precision?_mkFinite _ _ _ _ hn ?_)) ?_
      · rw [hn_size]; exact hqp
      · rw [toVal_mkFinite _ _ _ _ hn, hval]
    · rw [ite_eq_right hqp]
      have hqp' : p < q := not_le.mp hqp
      have hv0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
      set u : ℝ := (2 : ℝ) ^ (e.toInt - p) with hu_def
      have hu : 0 < u := zpow_pos (by norm_num) _
      have hscale : precScale 2 p (finiteVal s e m) = u := precScale_finiteVal s e hv p
      have hz : ((AzInt.mkNorm s n).toInt : ℝ) = (if s then 1 else -1) * (n.toNat : ℝ) := by
        rcases Bool.eq_false_or_eq_true s with hs | hs <;>
          simp [hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false n hn]
      have hvu : finiteVal s e m / u = ((AzInt.mkNorm s n).toInt : ℝ) / (2 : ℝ) ^ (q - p) := by
        rw [hval, hz]
        unfold finiteVal
        rw [hn_size, hu_def]
        have h : (2 : ℝ) ^ (e.toInt - q) / 2 ^ (e.toInt - p) = 1 / (2 : ℝ) ^ (q - p) := by
          rw [div_eq_div_iff (zpow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero), one_mul,
            ← zpow_natCast, ← zpow_add₀ two_ne_zero]
          congr 1
          rw [Nat.cast_sub hqp'.le]
          ring
        rw [mul_div_assoc, h]
        ring
      set v := finiteVal s e m with hv_def
      set r := AzInt.shiftRightRound (AzInt.mkNorm s n) mode (q - p) with hr_def
      have hr := AzInt.toInt_shiftRightRound (AzInt.mkNorm s n) mode (q - p)
      rw [← hvu, ← hr_def] at hr
      have hrI : toInt (round intSet mode (v / u)) = r.1.toInt := toInt_eq_of_val hr
      have hround : (round (floatSet p) mode v).val = (((r.1.toInt : ℝ) * u : ℝ) : EReal) := by
        rw [val_round_floatSet, val_round_precisionSet mode v hv0, hscale, hrI]
      -- bounds on `r`
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
      obtain ⟨hRval, hRprec⟩ := normalize_spec r.1 p hp e hlo' hhi'
      have hR : (if r.1.abs.size = p + 1 then
            (mkFinite r.1.sign (e + 1) p (r.1.abs.shiftRight 1), r.2)
          else (mkFinite r.1.sign e p r.1.abs, r.2))
          = ((if r.1.abs.size = p + 1 then mkFinite r.1.sign (e + 1) p (r.1.abs.shiftRight 1)
            else mkFinite r.1.sign e p r.1.abs), r.2) := by
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

theorem setPrec_eq (x : AzFloat) (p : ℕ) [NeZero p] :
    setPrec x p = (liftE id x p .Nearest).1 := by
  unfold setPrec
  rw [setPrecRound_eq_liftE]

/-! ### Units in the last place -/

theorem ulp?_spec (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hv : FiniteValid p m) :
    ∃ y, ulp? (finite s e p m hv) = some y ∧
      y.toVal = some (((2 : ℝ) ^ (e.toInt - p) : ℝ) : EReal) ∧ y.precision? = some 1 := by
  refine ⟨_, rfl, ?_, ?_⟩
  · unfold powerOf2
    rw [toVal_mkFinite _ _ _ _ (by decide)]
    congr 2
    unfold finiteVal
    rw [AzInt.toInt_add, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
    simp only [↓reduceIte, one_mul, show (1 : AzNat).toNat = 1 from rfl, Nat.cast_one,
      show (1 : AzNat).size = 1 from rfl, show (1 : AzInt).toInt = 1 from rfl]
    congr 1
    ring
  · unfold powerOf2
    exact precision?_mkFinite _ _ _ _ (by decide) (by rfl)

end Azurite.AzFloat
