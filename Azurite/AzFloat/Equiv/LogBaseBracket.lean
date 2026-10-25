/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseBracket
import Azurite.AzFloat.Equiv.Log2Bracket
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzNat.Equiv.LogBase2

/-!
# The bracket of `log_b x`: correctness

`quotientBracket_spec`: the quotient of a bracket of `L` (width `ε`) by a bracket of `M`
(lower end at least `1/2`, width `δ`) encloses `L / M`, with width at most
`2 ε + 8 (|L| + ε) (δ + 2^-w)`, from the directed-division lemmas `log2Lower_spec`/
`log2Upper_spec`.  `lnBaseBracket_spec` is the bracket of `ln b` with the lower end clamped to
`1/2`.  `logBaseApprox_spec` encloses `ln x / ln b` strictly when that is irrational, with width
`logBaseEps e eb |ln x| w → 0`; `logBaseApprox_isSome_exists` is the Ziv certificate (both take
the irrationality as a hypothesis; it is established separately in `Equiv/LogBaseExact`).
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- The width bound of `quotientBracket`. -/
theorem quotientBracket_spec {w : ℕ} (hw : 64 ≤ w) {bx cd : AzFloat × AzFloat}
    {a bv c d L M ε δ : ℝ} (ha : bx.1.toVal = some (a : EReal))
    (hb : bx.2.toVal = some (bv : EReal))
    (hc : cd.1.toVal = some (c : EReal)) (hd : cd.2.toVal = some (d : EReal))
    (hc0 : 1 / 2 ≤ c) (hcM : c ≤ M) (hMd : M ≤ d) (hcd : d - c ≤ δ)
    (haL : a ≤ L) (hLb : L ≤ bv) (hwid : bv - a ≤ ε) :
    ∃ lo hi : ℝ, (quotientBracket bx cd w).1.toVal = some (lo : EReal) ∧
      (quotientBracket bx cd w).2.toVal = some (hi : EReal) ∧
      lo ≤ L / M ∧ L / M ≤ hi ∧
      hi - lo ≤ 2 * ε + 8 * (|L| + ε) * (δ + (1 / 2 : ℝ) ^ w) := by
  have : NeZero w := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hcpos : 0 < c := by linarith
  have hM0 : 0 < M := by linarith
  have hd0 : 0 < d := by linarith
  have hε0 : 0 ≤ ε := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hLa : L ≤ |L| := le_abs_self L
  have hLa' : -|L| ≤ L := neg_abs_le L
  have habs_a : |a| ≤ |L| + ε := by rw [abs_le]; constructor <;> linarith
  have habs_b : |bv| ≤ |L| + ε := by rw [abs_le]; constructor <;> linarith
  have hcd' : 1 / c - 1 / d ≤ 4 * δ := by
    rw [div_sub_div _ _ hcpos.ne' hd0.ne', div_le_iff₀ (by positivity)]
    have hprod : (1 / 2 : ℝ) * (1 / 2) ≤ c * d :=
      mul_le_mul hc0 (by linarith) (by norm_num) hcpos.le
    have := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 4 * δ)
    linarith
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := log2Lower_spec w ha hc hd hcpos hcM hMd haL
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := log2Upper_spec w hb hc hd hcpos hcM hMd hLb
  rw [← hu] at hlo2 hhi2
  have h2a : |a| / c ≤ 2 * |a| := by rw [div_le_iff₀ hcpos]; nlinarith [abs_nonneg a]
  have h2b : |bv| / c ≤ 2 * |bv| := by rw [div_le_iff₀ hcpos]; nlinarith [abs_nonneg bv]
  have h2ab : bv / c - a / c ≤ 2 * (bv - a) := by
    rw [← sub_div, div_le_iff₀ hcpos]; nlinarith
  have hqa : |a| * (1 / c - 1 / d) ≤ |a| * (4 * δ) := mul_le_mul_of_nonneg_left hcd' (abs_nonneg a)
  have hqb : |bv| * (1 / c - 1 / d) ≤ |bv| * (4 * δ) :=
    mul_le_mul_of_nonneg_left hcd' (abs_nonneg bv)
  have hra : 2 * (|a| / c) * u ≤ 2 * (2 * |a|) * u := by
    have := mul_le_mul_of_nonneg_right h2a hu0.le; linarith
  have hrb : 2 * (|bv| / c) * u ≤ 2 * (2 * |bv|) * u := by
    have := mul_le_mul_of_nonneg_right h2b hu0.le; linarith
  have hau : |a| * u ≤ (|L| + ε) * u := mul_le_mul_of_nonneg_right habs_a hu0.le
  have hbu : |bv| * u ≤ (|L| + ε) * u := mul_le_mul_of_nonneg_right habs_b hu0.le
  have haδ : |a| * δ ≤ (|L| + ε) * δ := mul_le_mul_of_nonneg_right habs_a hδ0
  have hbδ : |bv| * δ ≤ (|L| + ε) * δ := mul_le_mul_of_nonneg_right habs_b hδ0
  exact ⟨lo, hi, hlo, hhi, hlo1, hhi1, by nlinarith⟩

/-- The value of `halfFloat`. -/
theorem toVal_halfFloat : halfFloat.toVal = some (((1 / 2 : ℝ)) : EReal) := by
  unfold halfFloat
  rw [toVal_powerOf2, AzInt.toInt_neg, show (1 : AzInt).toInt = 1 from rfl]
  norm_num

/-- `clampHalf` raises a value to `1/2`. -/
theorem toVal_clampHalf (z : AzFloat) (v : ℝ) (hz : z.toVal = some (v : EReal)) :
    (clampHalf z).toVal = some ((max v (1 / 2) : ℝ) : EReal) := by
  unfold clampHalf
  rw [partialCompare_eq, hz, toVal_halfFloat]
  simp only [compare_coe_coe, beq_iff_eq, Option.some.injEq]
  split_ifs with h
  · rw [compare_lt_iff_lt] at h
    rw [toVal_halfFloat, max_eq_right h.le]
  · rw [compare_lt_iff_lt] at h
    push Not at h
    rw [hz, max_eq_left h]

/-- The base float is positive with value `b`. -/
theorem toVal_baseFloat (b : UInt64) : (baseFloat b).toVal = some ((b.toNat : ℝ) : EReal) := by
  unfold baseFloat
  rw [toVal_ofAzNat, AzNat.toNat_ofNat]

/-- The bracket of `ln b`: lower end at least `1/2`, width `lnEps eb w` with `eb` the exponent
of the base float. -/
theorem lnBaseBracket_spec {w : ℕ} (hw : 64 ≤ w) (b : UInt64) (hb : 2 ≤ b.toNat) :
    ∃ c d : ℝ, (lnBaseBracket b w).1.toVal = some (c : EReal) ∧
      (lnBaseBracket b w).2.toVal = some (d : EReal) ∧
      1 / 2 ≤ c ∧ c ≤ Real.log b.toNat ∧ Real.log b.toNat ≤ d ∧
      d - c ≤ lnEps ((baseFloat b).exponent?.getD 0).toInt w := by
  have hval := toVal_baseFloat b
  have hpos : (0 : ℝ) < b.toNat := by exact_mod_cast (by omega : 0 < b.toNat)
  have hlog : 1 / 2 ≤ Real.log b.toNat := by
    have h2 : (2 : ℝ) ≤ b.toNat := by exact_mod_cast hb
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) h2
    linarith
  unfold lnBaseBracket
  simp only []
  rcases hy : baseFloat b with _ | s | _ | ⟨s, e, q, m, hv⟩
  · rw [hy] at hval; simp at hval
  · rw [hy] at hval
    simp only [toVal_infinity, Option.some.injEq] at hval
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at hval
    · exact absurd hval (EReal.bot_ne_coe _)
    · exact absurd hval (EReal.top_ne_coe _)
  · rw [hy] at hval
    simp only [toVal_zero, Option.some.injEq] at hval
    exact absurd (EReal.coe_eq_zero.mp hval.symm) hpos.ne'
  · rw [hy] at hval
    simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hval
    cases s with
    | false =>
      exfalso
      rw [finiteVal_false] at hval
      have := finiteVal_true_pos e hv
      linarith
    | true =>
      simp only [exponent?, Option.getD_some]
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := lnBracket_spec hw e hv
      rw [hval] at hlo hhi
      refine ⟨max lv (1 / 2), hv', toVal_clampHalf _ _ hl, hh, le_max_right _ _,
        max_le hlo hlog, hhi, ?_⟩
      have := le_max_left lv (1 / 2)
      linarith

/-- The width bound of `logBaseApprox`. -/
noncomputable def logBaseEps (ex eb : ℤ) (A : ℝ) (w : ℕ) : ℝ :=
  2 * lnEps ex w + 8 * (A + lnEps ex w) * (lnEps eb w + (1 / 2 : ℝ) ^ w)

theorem tendsto_logBaseEps (ex eb : ℤ) (A : ℝ) :
    Filter.Tendsto (logBaseEps ex eb A) Filter.atTop (nhds 0) := by
  have hx := tendsto_lnEps ex
  have hb := tendsto_lnEps eb
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (hx.const_mul 2).add (((hA.add hx).const_mul 8).mul (hb.add hu))
  simp only [mul_zero, add_zero] at this
  exact this

/-- The bracket encloses `ln x / ln b` strictly (given irrationality), with the width bound. -/
theorem logBaseApprox_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (b : UInt64) (hb : 2 ≤ b.toNat)
    (hirr : Irrational (Real.log (finiteVal true e m) / Real.log b.toNat)) :
    ∃ lv hv' : ℝ, Rounds (logBaseApprox (finite true e q m hv) e b w).1 lv ∧
      Rounds (logBaseApprox (finite true e q m hv) e b w).2 hv' ∧
      lv < Real.log (finiteVal true e m) / Real.log b.toNat ∧
      Real.log (finiteVal true e m) / Real.log b.toNat < hv' ∧
      hv' - lv ≤ logBaseEps e.toInt ((baseFloat b).exponent?.getD 0).toInt
        |Real.log (finiteVal true e m)| w := by
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnBracket_spec hw e hv
  obtain ⟨c, d, hc, hd, hc0, hcM, hMd, hcd⟩ := lnBaseBracket_spec hw b hb
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ :=
    quotientBracket_spec hw ha hb' hc hd hc0 hcM hMd hcd haL hLb hwid
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne hlo1 fun h => hirr.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne hhi1 fun h => hirr.ne_rat r (h.trans hr)

/-- The Ziv certificate for `log_b x`. -/
theorem logBaseApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (e : AzInt)
    {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (b : UInt64) (hb : 2 ≤ b.toNat)
    (hirr : Irrational (Real.log (finiteVal true e m) / Real.log b.toNat)) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBaseApprox (finite true e q m hv) e b (w₀ * 2 ^ f)).1
      (logBaseApprox (finite true e q m hv) e b (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBaseApprox (finite true e q m hv) e b) hirr
    (logBaseEps e.toInt ((baseFloat b).exponent?.getD 0).toInt |Real.log (finiteVal true e m)|)
    (tendsto_logBaseEps _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBaseApprox_spec hw e hv b hb hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The rational bracket -/

/-- The width bound of `logBaseRatApprox`. -/
noncomputable def logBaseRatEps (E : ℕ) (eb : ℤ) (A : ℝ) (w : ℕ) : ℝ :=
  2 * lnRatEps E A w + 8 * (A + lnRatEps E A w) * (lnEps eb w + (1 / 2 : ℝ) ^ w)

theorem tendsto_logBaseRatEps (E : ℕ) (eb : ℤ) (A : ℝ) :
    Filter.Tendsto (logBaseRatEps E eb A) Filter.atTop (nhds 0) := by
  have hx := tendsto_lnRatEps E A
  have hb := tendsto_lnEps eb
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (hx.const_mul 2).add (((hA.add hx).const_mul 8).mul (hb.add hu))
  simp only [mul_zero, add_zero] at this
  exact this

/-- The bracket encloses `ln q / ln b` strictly (given irrationality), with the width bound. -/
theorem logBaseRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (b : UInt64) (hb : 2 ≤ b.toNat)
    (hirr : Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat)) :
    ∃ lv hv' : ℝ, Rounds (logBaseRatApprox q b w).1 lv ∧ Rounds (logBaseRatApprox q b w).2 hv' ∧
      lv < Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat ∧
      Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat < hv' ∧
      hv' - lv ≤ logBaseRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
        ((baseFloat b).exponent?.getD 0).toInt |Real.log (AzRat.toRat q : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hqv0 hr1 hr2
  obtain ⟨c, d, hc, hd, hc0, hcM, hMd, hcd⟩ := lnBaseBracket_spec hw b hb
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ :=
    quotientBracket_spec hw ha hb' hc hd hc0 hcM hMd hcd haL hLb hwid
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne hlo1 fun h => hirr.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne hhi1 fun h => hirr.ne_rat r (h.trans hr)

/-- The Ziv certificate for `log_b q`. -/
theorem logBaseRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (b : UInt64) (hb : 2 ≤ b.toNat)
    (hirr : Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat)) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBaseRatApprox q b (w₀ * 2 ^ f)).1
      (logBaseRatApprox q b (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBaseRatApprox q b) hirr
    (logBaseRatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
      ((baseFloat b).exponent?.getD 0).toInt |Real.log (AzRat.toRat q : ℝ)|)
    (tendsto_logBaseRatEps _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := logBaseRatApprox_spec hw q hq b hb hirr
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The `log_b (1 + x)` bracket -/

/-- The bracket encloses `ln (1 + x) / ln b` strictly (given irrationality), with the width
bound `logBaseRatEps` (the same as for a rational argument). -/
theorem logBaseP1Approx_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (b : UInt64) (hb : 2 ≤ b.toNat)
    (hirr : Irrational (Real.log (1 + xv) / Real.log b.toNat)) :
    ∃ lv hv : ℝ, Rounds (logBaseP1Approx x b w).1 lv ∧ Rounds (logBaseP1Approx x b w).2 hv ∧
      lv < Real.log (1 + xv) / Real.log b.toNat ∧ Real.log (1 + xv) / Real.log b.toNat < hv ∧
      hv - lv ≤ logBaseRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2)
        ((baseFloat b).exponent?.getD 0).toInt |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  obtain ⟨a, bv, ha, hb', haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hpos hf.le hf.ge
  obtain ⟨c, d, hc, hd, hc0, hcM, hMd, hcd⟩ := lnBaseBracket_spec hw b hb
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ :=
    quotientBracket_spec hw ha hb' hc hd hc0 hcM hMd hcd haL hLb hwid
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, hwidth⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR
  · obtain ⟨r', hr'⟩ := exists_rat_of_toVal hlo
    exact lt_of_le_of_ne hlo1 fun h => hirr.ne_rat r' (h.symm.trans hr')
  · obtain ⟨r', hr'⟩ := exists_rat_of_toVal hhi
    exact lt_of_le_of_ne hhi1 fun h => hirr.ne_rat r' (h.trans hr')

/-- The Ziv certificate for `log_b (1 + x)`. -/
theorem logBaseP1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv) (b : UInt64) (hb : 2 ≤ b.toNat)
    (hirr : Irrational (Real.log (1 + xv) / Real.log b.toNat)) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (logBaseP1Approx x b (w₀ * 2 ^ f)).1
      (logBaseP1Approx x b (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (logBaseP1Approx x b) hirr
    (logBaseRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) ((baseFloat b).exponent?.getD 0).toInt
      |Real.log (1 + xv)|)
    (tendsto_logBaseRatEps _ _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := logBaseP1Approx_spec hw hx hx1 b hb hirr
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-- `ln v / ln (2^k) = log₂ v / k`. -/
theorem log_div_log_two_pow (k : ℕ) (v : ℝ) :
    Real.log v / Real.log ((2 ^ k : ℕ) : ℝ) = Real.logb 2 v / k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, ← Real.log_div_log]
  ring

/-- For a power-of-two base `b = 2^k`, `log_b (1 + x)` is irrational when `1 + x` is not a power
of two (`onePlusPow2Exponent? = none`). -/
theorem irrational_log_div_log_one_add_of_pow2 (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (b : UInt64) (hb : 2 ≤ b.toNat) {k : ℕ}
    (hk : (AzNat.ofNat b.toNat).checkedLogBase2 = some k) {w : ℕ} (hw : 2 ≤ w)
    (h : onePlusPow2Exponent? (finite s e q m hv) w = none) :
    Irrational (Real.log (1 + finiteVal s e m) / Real.log b.toNat) := by
  have hbk : b.toNat = 2 ^ k := by
    have := (AzNat.checkedLogBase2_eq_some_iff _ k).mp hk
    rwa [AzNat.toNat_ofNat] at this
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hbk
    omega
  rw [hbk, log_div_log_two_pow]
  exact Irrational.div_natCast
    (irrational_logb_two_one_add_of_none (toVal_finite s e q m hv) hw (by linarith) h) hk1

end Azurite.AzFloat
