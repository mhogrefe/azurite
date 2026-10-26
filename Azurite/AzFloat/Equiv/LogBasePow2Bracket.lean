/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Log2Bracket
import Azurite.AzFloat.LogBasePow2Bracket

/-!
# The brackets of `log_{2^k} x` and `log_{2^k} q`: correctness

`divBracketByInt_spec`: dividing a bracket of `L` by a nonzero integer `k` gives a bracket of
`L / k`, strict when `L / k` is irrational, whose width is the original width `ε` plus
`4 (|L| + ε) 2^-w` for the directed roundings (`log2Lower_spec`/`log2Upper_spec` with the
constant divisor bracket `(|k|, |k|)`).  `logBasePow2Approx_spec` and
`logBasePow2RatApprox_spec` instantiate it on the `log₂` brackets of a float and of a rational
(the values are irrational by `irrational_logb_two_finiteVal`/`irrational_logb_two_toRat` and
`Irrational.div_intCast`), with the width bounds `logBasePow2Eps` and `logBasePow2RatEps`;
`logBasePow2Approx_isSome_exists` and `logBasePow2RatApprox_isSome_exists` are the Ziv
certificates.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- The width bound of `logBasePow2Approx`. -/
noncomputable def logBasePow2Eps (e : ℤ) (A : ℝ) (w : ℕ) : ℝ :=
  log2Eps e A w + 4 * (2 * A + log2Eps e A w) * (1 / 2 : ℝ) ^ w

theorem tendsto_logBasePow2Eps (e : ℤ) (A : ℝ) :
    Filter.Tendsto (logBasePow2Eps e A) Filter.atTop (nhds 0) := by
  have hL := tendsto_log2Eps e A
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => 2 * A) Filter.atTop (nhds (2 * A)) :=
    tendsto_const_nhds
  have := hL.add (((hA.add hL).const_mul 4).mul hu)
  simp only [mul_zero, add_zero] at this
  exact this

/-- The width bound of `logBasePow2RatApprox`. -/
noncomputable def logBasePow2RatEps (E : ℕ) (A : ℝ) (w : ℕ) : ℝ :=
  log2RatEps E A w + 4 * (2 * A + log2RatEps E A w) * (1 / 2 : ℝ) ^ w

theorem tendsto_logBasePow2RatEps (E : ℕ) (A : ℝ) :
    Filter.Tendsto (logBasePow2RatEps E A) Filter.atTop (nhds 0) := by
  have hL := tendsto_log2RatEps E A
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => 2 * A) Filter.atTop (nhds (2 * A)) :=
    tendsto_const_nhds
  have := hL.add (((hA.add hL).const_mul 4).mul hu)
  simp only [mul_zero, add_zero] at this
  exact this

theorem toInt_ne_zero_of_ne_zero {k : AzInt} (hk : k ≠ 0) : k.toInt ≠ 0 := by
  intro h
  apply hk
  have hdef : k.toInt = if k.sign then (k.abs.toNat : ℤ) else -(k.abs.toNat : ℤ) := rfl
  rw [hdef] at h
  have habs : k.abs.toNat = 0 := by split_ifs at h <;> omega
  have hzero : k.abs = 0 := AzNat.toNat_injective (by rw [habs, AzNat.toNat_zero])
  have hs : k.sign = true := k.zero_sign hzero
  rcases k with ⟨s, a, hz⟩
  simp only at hs hzero
  subst hs
  subst hzero
  rfl

theorem abs_toNat_cast (k : AzInt) : ((k.abs.toNat : ℕ) : ℝ) = |(k.toInt : ℝ)| := by
  rw [← Int.cast_abs, ← AzInt.abs_toNat_eq, Int.cast_natCast]

/-- `|log₂ x| ≤ 2 |ln x|`. -/
theorem abs_log_div_log_two_le (x : ℝ) : |Real.log x / Real.log 2| ≤ 2 * |Real.log x| := by
  rw [abs_div, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)),
    div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have := Real.log_two_gt_d9
  nlinarith [abs_nonneg (Real.log x)]

/-- Dividing a bracket of `L` by `k ≠ 0`: a bracket of `L / k`, strict for irrational `L / k`,
of width `ε + 4 (|L| + ε) 2^-w`. -/
theorem divBracketByInt_spec {w : ℕ} [NeZero w] {B : AzFloat × AzFloat} {lo hi L ε : ℝ}
    (hlo : B.1.toVal = some (lo : EReal)) (hhi : B.2.toVal = some (hi : EReal))
    (hlo1 : lo ≤ L) (hhi1 : L ≤ hi) (hwid : hi - lo ≤ ε) (k : AzInt) (hk : k ≠ 0)
    (hirr : Irrational (L / k.toInt)) :
    ∃ lv hv' : ℝ, Rounds (divBracketByInt B k w).1 lv ∧ Rounds (divBracketByInt B k w).2 hv' ∧
      lv < L / k.toInt ∧ L / k.toInt < hv' ∧
      hv' - lv ≤ ε + 4 * (|L| + ε) * (1 / 2 : ℝ) ^ w := by
  -- the divisor `|k| ≥ 1`
  set K := ofAzNat k.abs with hK_def
  have hK : K.toVal = some ((k.abs.toNat : ℝ) : EReal) := toVal_ofAzNat _
  have hkabs : ((k.abs.toNat : ℕ) : ℝ) = |(k.toInt : ℝ)| := abs_toNat_cast k
  have hk1 : (1 : ℝ) ≤ k.abs.toNat := by
    rw [hkabs]
    have : (1 : ℤ) ≤ |k.toInt| := Int.one_le_abs (toInt_ne_zero_of_ne_zero hk)
    rw [← Int.cast_abs]; exact_mod_cast this
  have hKpos : (0 : ℝ) < k.abs.toNat := by linarith
  obtain ⟨lo', hlo', hlo'1, hlo'2⟩ := log2Lower_spec w hlo hK hK hKpos le_rfl le_rfl hlo1
  obtain ⟨hi', hhi', hhi'1, hhi'2⟩ := log2Upper_spec w hhi hK hK hKpos le_rfl le_rfl hhi1
  rw [ite_self] at hlo' hhi'
  simp only [sub_self, mul_zero, sub_zero, add_zero] at hlo'2 hhi'2
  -- the width
  have hu : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hlo_abs : |lo| ≤ |L| + ε := by
    rw [abs_le]; constructor <;> linarith [le_abs_self L, neg_abs_le L]
  have hhi_abs : |hi| ≤ |L| + ε := by
    rw [abs_le]; constructor <;> linarith [le_abs_self L, neg_abs_le L]
  have hwid' : hi' - lo' ≤ ε + 4 * (|L| + ε) * (1 / 2 : ℝ) ^ w := by
    have h1 : hi / k.abs.toNat - lo / k.abs.toNat ≤ hi - lo := by
      rw [← sub_div, div_le_iff₀ hKpos]
      nlinarith [sub_nonneg.mpr (hlo1.trans hhi1)]
    have h2 : 2 * (|hi| / k.abs.toNat) * (1 / 2 : ℝ) ^ w
        + 2 * (|lo| / k.abs.toNat) * (1 / 2 : ℝ) ^ w
        ≤ 4 * (|L| + ε) * (1 / 2 : ℝ) ^ w := by
      have h3 : |hi| / k.abs.toNat ≤ |hi| := div_le_self (abs_nonneg _) hk1
      have h4 : |lo| / k.abs.toNat ≤ |lo| := div_le_self (abs_nonneg _) hk1
      nlinarith
    linarith
  -- the two signs
  unfold divBracketByInt
  simp only []
  rw [← hK_def]
  by_cases hs : k.sign = true
  · have hkpos : (0 : ℝ) < k.toInt := by
      have h0 := (AzInt.sign_eq_true_iff k).mp hs
      have hne := toInt_ne_zero_of_ne_zero hk
      exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne)
    have hkK : (k.abs.toNat : ℝ) = k.toInt := by rw [hkabs, abs_of_pos hkpos]
    rw [ite_eq_left hs]
    rw [hkK] at hlo'1 hhi'1
    refine ⟨lo', hi', ?_, ?_, ?_, ?_, hwid'⟩
    · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo')
      rw [fval_of_toVal_coe hlo'] at hR; exact hR
    · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi')
      rw [fval_of_toVal_coe hhi'] at hR; exact hR
    · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo'
      exact lt_of_le_of_ne hlo'1 fun h => hirr.ne_rat r (h.symm.trans hr)
    · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi'
      exact lt_of_le_of_ne hhi'1 fun h => hirr.ne_rat r (h.trans hr)
  · have hkneg : (k.toInt : ℝ) < 0 := by
      have := (AzInt.sign_eq_true_iff k).not.mp hs
      push Not at this
      exact_mod_cast this
    have hkK : (k.abs.toNat : ℝ) = -k.toInt := by rw [hkabs, abs_of_neg hkneg]
    rw [ite_eq_right hs]
    rw [hkK, div_neg] at hlo'1 hhi'1
    have hnlo : (-(divPrecRound B.2 K w .Ceiling).1).toVal = some ((-hi' : ℝ) : EReal) := by
      rw [toVal_neg, hhi', Option.map_some, EReal.coe_neg]
    have hnhi : (-(divPrecRound B.1 K w .Floor).1).toVal = some ((-lo' : ℝ) : EReal) := by
      rw [toVal_neg, hlo', Option.map_some, EReal.coe_neg]
    refine ⟨-hi', -lo', ?_, ?_, ?_, ?_, by linarith⟩
    · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
      rw [fval_of_toVal_coe hnlo] at hR; exact hR
    · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
      rw [fval_of_toVal_coe hnhi] at hR; exact hR
    · obtain ⟨r, hr⟩ := exists_rat_of_toVal hnlo
      exact lt_of_le_of_ne (by linarith) fun h => hirr.ne_rat r (h.symm.trans hr)
    · obtain ⟨r, hr⟩ := exists_rat_of_toVal hnhi
      exact lt_of_le_of_ne (by linarith) fun h => hirr.ne_rat r (h.trans hr)

/-! ### The float input -/

/-- The bracket encloses `log₂ x / k` strictly, with the width bound. -/
theorem logBasePow2Approx_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hnp : m.isPowerOfTwo = false) (k : AzInt) (hk : k ≠ 0) :
    ∃ lv hv' : ℝ, Rounds (logBasePow2Approx (finite true e q m hv) e k w).1 lv ∧
      Rounds (logBasePow2Approx (finite true e q m hv) e k w).2 hv' ∧
      lv < Real.log (finiteVal true e m) / Real.log 2 / k.toInt ∧
      Real.log (finiteVal true e m) / Real.log 2 / k.toInt < hv' ∧
      hv' - lv ≤ logBasePow2Eps e.toInt |Real.log (finiteVal true e m)| w := by
  have : NeZero w := ⟨by omega⟩
  have hirr : Irrational (Real.log (finiteVal true e m) / Real.log 2 / k.toInt) := by
    apply Irrational.div_intCast _ (toInt_ne_zero_of_ne_zero hk)
    rw [Real.log_div_log]
    exact irrational_logb_two_finiteVal e m (ne_zero_of_finiteValid e hv)
      (fun h => by rw [← AzNat.isPowerOfTwo_iff] at h; rw [h] at hnp; cases hnp)
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnBracket_spec hw e hv
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ := log2Quotients_spec hw ha hb haL hLb hwid
  obtain ⟨lv, hv', hl, hh, hlo', hhi', hw'⟩ :=
    divBracketByInt_spec (w := w) hlo hhi hlo1 hhi1 hwidth k hk hirr
  refine ⟨lv, hv', hl, hh, hlo', hhi', hw'.trans ?_⟩
  unfold logBasePow2Eps log2Eps
  have hu : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have := abs_log_div_log_two_le (finiteVal true e m)
  nlinarith

/-- The Ziv certificate for `log_{2^k} x`. -/
theorem logBasePow2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (e : AzInt)
    {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (hnp : m.isPowerOfTwo = false) (k : AzInt)
    (hk : k ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBasePow2Approx (finite true e q m hv) e k (w₀ * 2 ^ f)).1
      (logBasePow2Approx (finite true e q m hv) e k (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hirr : Irrational (Real.log (finiteVal true e m) / Real.log 2 / k.toInt) := by
    apply Irrational.div_intCast _ (toInt_ne_zero_of_ne_zero hk)
    rw [Real.log_div_log]
    exact irrational_logb_two_finiteVal e m (ne_zero_of_finiteValid e hv)
      (fun h => by rw [← AzNat.isPowerOfTwo_iff] at h; rw [h] at hnp; cases hnp)
  exact exists_isSome_of_irrational_threshold p mode (logBasePow2Approx (finite true e q m hv) e k)
    hirr (logBasePow2Eps e.toInt |Real.log (finiteVal true e m)|) (tendsto_logBasePow2Eps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBasePow2Approx_spec hw e hv hnp k hk
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The rational input -/

/-- The bracket encloses `log₂ q / k` strictly, with the width bound. -/
theorem logBasePow2RatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (hnp : q.isPowerOfTwo = false) (k : AzInt) (hk : k ≠ 0) :
    ∃ lv hv' : ℝ, Rounds (logBasePow2RatApprox q k w).1 lv ∧
      Rounds (logBasePow2RatApprox q k w).2 hv' ∧
      lv < Real.logb 2 (AzRat.toRat q : ℝ) / k.toInt ∧
      Real.logb 2 (AzRat.toRat q : ℝ) / k.toInt < hv' ∧
      hv' - lv ≤ logBasePow2RatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
        |Real.log (AzRat.toRat q : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  have hirr : Irrational (Real.logb 2 (AzRat.toRat q : ℝ) / k.toInt) :=
    Irrational.div_intCast (irrational_logb_two_toRat q hq hnp) (toInt_ne_zero_of_ne_zero hk)
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hqv0 hr1 hr2
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ := log2Quotients_spec hw ha hb haL hLb hwid
  rw [Real.log_div_log] at hlo1 hhi1
  obtain ⟨lv, hv', hl, hh, hlo', hhi', hw'⟩ :=
    divBracketByInt_spec (w := w) hlo hhi hlo1 hhi1 hwidth k hk hirr
  refine ⟨lv, hv', hl, hh, hlo', hhi', hw'.trans ?_⟩
  unfold logBasePow2RatEps log2RatEps
  have hu : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have := abs_log_div_log_two_le (AzRat.toRat q : ℝ)
  rw [Real.log_div_log] at this
  nlinarith

/-- The Ziv certificate for `log_{2^k} q`. -/
theorem logBasePow2RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (hnp : q.isPowerOfTwo = false) (k : AzInt) (hk : k ≠ 0)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBasePow2RatApprox q k (w₀ * 2 ^ f)).1
      (logBasePow2RatApprox q k (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBasePow2RatApprox q k)
    (Irrational.div_intCast (irrational_logb_two_toRat q hq hnp) (toInt_ne_zero_of_ne_zero hk))
    (logBasePow2RatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2) |Real.log (AzRat.toRat q : ℝ)|)
    (tendsto_logBasePow2RatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBasePow2RatApprox_spec hw q hq hnp k hk
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The bracket of `log_{2^k} (1 + x)` -/

/-- `logBasePow2P1Approx x k w` encloses `log₂ (1 + x) / k` strictly (given its irrationality),
with width at most `logBasePow2RatEps E |ln (1 + x)| w` (`w ≥ 64`, `x > −1`). -/
theorem logBasePow2P1Approx_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (k : AzInt) (hk : k ≠ 0)
    (hirr : Irrational (Real.logb 2 (1 + xv) / k.toInt)) :
    ∃ lv hv' : ℝ, Rounds (logBasePow2P1Approx x k w).1 lv ∧
      Rounds (logBasePow2P1Approx x k w).2 hv' ∧
      lv < Real.logb 2 (1 + xv) / k.toInt ∧ Real.logb 2 (1 + xv) / k.toInt < hv' ∧
      hv' - lv ≤ logBasePow2RatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hpos hf.le hf.ge
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ := log2Quotients_spec hw ha hb haL hLb hwid
  rw [Real.log_div_log] at hlo1 hhi1
  obtain ⟨lv, hv', hl, hh, hlo', hhi', hw'⟩ :=
    divBracketByInt_spec (w := w) hlo hhi hlo1 hhi1 hwidth k hk hirr
  refine ⟨lv, hv', hl, hh, hlo', hhi', hw'.trans ?_⟩
  unfold logBasePow2RatEps log2RatEps
  have hu : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have := abs_log_div_log_two_le (1 + xv)
  rw [Real.log_div_log] at this
  nlinarith

/-- The Ziv certificate for `log_{2^k} (1 + x)`. -/
theorem logBasePow2P1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (k : AzInt)
    (hk : k ≠ 0) (hirr : Irrational (Real.logb 2 (1 + xv) / k.toInt)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBasePow2P1Approx x k (w₀ * 2 ^ f)).1
      (logBasePow2P1Approx x k (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBasePow2P1Approx x k) hirr
    (logBasePow2RatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)|)
    (tendsto_logBasePow2RatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBasePow2P1Approx_spec hw hx hx1 k hk hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
