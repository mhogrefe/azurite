/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2Bracket
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.Size
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Equivalence: the bracket of `log₂ x`

* `irrational_logb_two_of_odd`: `log₂ n` is irrational for an odd `n ≠ 1` (if `log₂ n = p/q` then
  `n^q = 2^p`, impossible by parity); `irrational_logb_two_finiteVal`: hence `log₂ x` is
  irrational for a positive float whose significand is not a power of two.
* `finiteVal_true_of_isPowerOfTwo`: a float with a power-of-two significand is `2^(e−1)`.
* `log2Lower_spec`/`log2Upper_spec`: the sign-dependent directed quotients bound `ln x / ln 2`.
* `log2Approx_spec`, `log2Approx_isSome_exists`: enclosure, width `≤ log2Eps e |ln x| w`, and the
  Ziv certificate.
-/

namespace Azurite.AzFloat

/-! ### Irrationality -/

/-- `log₂ n` is irrational for an odd `n ≠ 1`. -/
theorem irrational_logb_two_of_odd {n : ℕ} (hodd : Odd n) (hn1 : n ≠ 1) :
    Irrational (Real.logb 2 n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hodd.pos
  rintro ⟨r, hr⟩
  have h2 : (2 : ℝ) ^ (r : ℝ) = n := by
    rw [hr]; exact Real.rpow_logb (by norm_num) (by norm_num) hnpos
  have hq0 : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hrq : (r : ℝ) * r.den = r.num := by rw [Rat.cast_def]; field_simp
  have h3 : (n : ℝ) ^ r.den = (2 : ℝ) ^ r.num := by
    rw [← h2, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hrq, Real.rpow_intCast]
  rcases le_or_gt 0 r.num with hp0 | hp0
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hp0
    rw [hk, zpow_natCast] at h3
    have h4 : n ^ r.den = 2 ^ k := by exact_mod_cast h3
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero, Nat.pow_eq_one] at h4
      rcases h4 with h | h
      · exact hn1 h
      · exact r.den_nz h
    · have heven : Even (n ^ r.den) := by
        rw [h4]; exact Nat.even_pow.mpr ⟨even_two, hkpos.ne'⟩
      rw [Nat.even_pow] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven.1
  · have h5 : (2 : ℝ) ^ r.num < 1 := zpow_lt_one_of_neg₀ (by norm_num) hp0
    have h6 : (1 : ℝ) ≤ (n : ℝ) ^ r.den := one_le_pow₀ (by exact_mod_cast hodd.pos)
    linarith

theorem logb_two_zpow (j : ℤ) : Real.logb 2 ((2 : ℝ) ^ j) = j := by
  rw [Real.logb, Real.log_zpow, mul_div_assoc, div_self (Real.log_pos one_lt_two).ne', mul_one]

/-- `log₂ x` is irrational for a positive float `x` whose significand is not a power of two. -/
theorem irrational_logb_two_finiteVal (e : AzInt) (m : AzNat) (hm : m ≠ 0)
    (hnp : ¬ m.toNat.isPowerOfTwo) : Irrational (Real.logb 2 (finiteVal true e m)) := by
  rw [finiteVal_true_eq]
  obtain ⟨k, n, hodd, hmn⟩ := Nat.exists_eq_two_pow_mul_odd (toNat_ne_zero_of_ne_zero hm)
  have hn1 : n ≠ 1 := by rintro rfl; exact hnp ⟨k, by rw [hmn, mul_one]⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hodd.pos.ne'
  rw [hmn]
  push_cast
  have h2k : (2 : ℝ) ^ k * n * 2 ^ (e.toInt - m.size)
      = n * 2 ^ ((k : ℤ) + (e.toInt - m.size)) := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]; ring
  rw [h2k, Real.logb_mul hn0 (zpow_ne_zero _ (by norm_num)), logb_two_zpow]
  exact (irrational_logb_two_of_odd hodd hn1).add_intCast _

/-- A float whose significand is a power of two is `2^(e−1)`. -/
theorem finiteVal_true_of_isPowerOfTwo (e : AzInt) (m : AzNat) (h : m.isPowerOfTwo = true) :
    finiteVal true e m = (2 : ℝ) ^ (e.toInt - 1) := by
  obtain ⟨k, hk⟩ := (AzNat.isPowerOfTwo_iff m).mp h
  have hsize : m.size = k + 1 := by rw [← AzNat.size_toNat, hk, Nat.size_pow]
  rw [finiteVal_true_eq, hk, hsize]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 1
  ring

/-- A valid significand is nonzero. -/
theorem ne_zero_of_finiteValid (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) : m ≠ 0 := by
  rintro rfl
  have := finiteVal_true_pos e hv
  rw [finiteVal_true_eq, AzNat.toNat_zero] at this
  simp at this

/-! ### The directed quotients -/

/-- The lower end: `⌊a/d⌋` if `a ≥ 0`, `⌊a/c⌋` if `a < 0`, is below `L/M` for `a ≤ L`,
`0 < c ≤ M ≤ d`, and loses at most `|a| (1/c − 1/d) + 2 (|a|/c) 2^(−w)` against `a/c`. -/
theorem log2Lower_spec (w : ℕ) [NeZero w] {xa xc xd : AzFloat} {a c d M L : ℝ}
    (ha : xa.toVal = some (a : EReal)) (hc : xc.toVal = some (c : EReal))
    (hd : xd.toVal = some (d : EReal)) (hc0 : 0 < c) (hcM : c ≤ M) (hMd : M ≤ d) (haL : a ≤ L) :
    ∃ lo : ℝ, (if xa.isNegative then (divPrecRound xa xc w .Floor).1
        else (divPrecRound xa xd w .Floor).1).toVal = some (lo : EReal) ∧
      lo ≤ L / M ∧
      a / c - |a| * (1 / c - 1 / d) - 2 * (|a| / c) * (1 / 2 : ℝ) ^ w ≤ lo := by
  have hM0 : 0 < M := hc0.trans_le hcM
  have hd0 : 0 < d := hM0.trans_le hMd
  have hcd : 0 ≤ 1 / c - 1 / d := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hc0 (hcM.trans hMd)
  obtain ⟨hneg, hnonneg⟩ := toVal_sign_of_isNegative ha
  cases hs : xa.isNegative
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have ha0 := hnonneg hs
    obtain ⟨lo, hlo, h1, h2⟩ := divFloor_abs ha hd hd0.ne' w
    refine ⟨lo, hlo, ?_, ?_⟩
    · calc lo ≤ a / d := h1
        _ ≤ a / M := div_le_div_of_nonneg_left ha0 hM0 hMd
        _ ≤ L / M := div_le_div_of_nonneg_right haL hM0.le
    · rw [abs_of_nonneg ha0]
      have e : a / d = a / c - a * (1 / c - 1 / d) := by field_simp; ring
      have h3 : |a / d| ≤ a / c := by
        rw [abs_of_nonneg (div_nonneg ha0 hd0.le)]
        exact div_le_div_of_nonneg_left ha0 hc0 (hcM.trans hMd)
      have h4 : 2 * |a / d| * (1 / 2 : ℝ) ^ w ≤ 2 * (a / c) * (1 / 2 : ℝ) ^ w := by
        have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w)
        linarith
      linarith
  · simp only [↓reduceIte]
    have haneg := hneg hs
    obtain ⟨lo, hlo, h1, h2⟩ := divFloor_abs ha hc hc0.ne' w
    refine ⟨lo, hlo, ?_, ?_⟩
    · calc lo ≤ a / c := h1
        _ ≤ a / M := by
          rw [div_le_div_iff₀ hc0 hM0]
          exact mul_le_mul_of_nonpos_left hcM haneg.le
        _ ≤ L / M := div_le_div_of_nonneg_right haL hM0.le
    · rw [abs_of_neg haneg]
      have h3 : |a / c| = -a / c := by rw [abs_div, abs_of_neg haneg, abs_of_pos hc0]
      have h4 : 0 ≤ -a * (1 / c - 1 / d) := mul_nonneg (by linarith) hcd
      rw [h3] at h2
      linarith

/-- The upper end: `⌈b/c⌉` if `b ≥ 0`, `⌈b/d⌉` if `b < 0`, is above `L/M` for `L ≤ b`,
`0 < c ≤ M ≤ d`, and exceeds `b/c` by at most `|b| (1/c − 1/d) + 2 (|b|/c) 2^(−w)`. -/
theorem log2Upper_spec (w : ℕ) [NeZero w] {xb xc xd : AzFloat} {b c d M L : ℝ}
    (hb : xb.toVal = some (b : EReal)) (hc : xc.toVal = some (c : EReal))
    (hd : xd.toVal = some (d : EReal)) (hc0 : 0 < c) (hcM : c ≤ M) (hMd : M ≤ d) (hLb : L ≤ b) :
    ∃ hi : ℝ, (if xb.isNegative then (divPrecRound xb xd w .Ceiling).1
        else (divPrecRound xb xc w .Ceiling).1).toVal = some (hi : EReal) ∧
      L / M ≤ hi ∧
      hi ≤ b / c + |b| * (1 / c - 1 / d) + 2 * (|b| / c) * (1 / 2 : ℝ) ^ w := by
  have hM0 : 0 < M := hc0.trans_le hcM
  have hd0 : 0 < d := hM0.trans_le hMd
  have hcd : 0 ≤ 1 / c - 1 / d := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hc0 (hcM.trans hMd)
  obtain ⟨hneg, hnonneg⟩ := toVal_sign_of_isNegative hb
  cases hs : xb.isNegative
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hb0 := hnonneg hs
    obtain ⟨hi, hhi, h1, h2⟩ := divCeiling_abs hb hc hc0.ne' w
    refine ⟨hi, hhi, ?_, ?_⟩
    · calc L / M ≤ b / M := div_le_div_of_nonneg_right hLb hM0.le
        _ ≤ b / c := div_le_div_of_nonneg_left hb0 hc0 hcM
        _ ≤ hi := h1
    · rw [abs_of_nonneg hb0]
      have h3 : |b / c| = b / c := abs_of_nonneg (div_nonneg hb0 hc0.le)
      have h4 : 0 ≤ b * (1 / c - 1 / d) := mul_nonneg hb0 hcd
      rw [h3] at h2
      linarith
  · simp only [↓reduceIte]
    have hbneg := hneg hs
    obtain ⟨hi, hhi, h1, h2⟩ := divCeiling_abs hb hd hd0.ne' w
    refine ⟨hi, hhi, ?_, ?_⟩
    · calc L / M ≤ b / M := div_le_div_of_nonneg_right hLb hM0.le
        _ ≤ b / d := by
          rw [div_le_div_iff₀ hM0 hd0]
          exact mul_le_mul_of_nonpos_left hMd hbneg.le
        _ ≤ hi := h1
    · rw [abs_of_neg hbneg]
      have e : b / d = b / c + (-b) * (1 / c - 1 / d) := by field_simp; ring
      have h3 : |b / d| ≤ -b / c := by
        rw [abs_div, abs_of_neg hbneg, abs_of_pos hd0]
        exact div_le_div_of_nonneg_left (by linarith) hc0 (hcM.trans hMd)
      have h4 : 2 * |b / d| * (1 / 2 : ℝ) ^ w ≤ 2 * (-b / c) * (1 / 2 : ℝ) ^ w := by
        have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w)
        linarith
      linarith

/-! ### The bracket -/

/-- The width bound of `log2Approx`: `A` bounds `|ln x|`. -/
noncomputable def log2Eps (e : ℤ) (A : ℝ) (w : ℕ) : ℝ :=
  5 * lnEps e w + 140 * (A + lnEps e w) * (1 / 2 : ℝ) ^ w

theorem tendsto_log2Eps (e : ℤ) (A : ℝ) :
    Filter.Tendsto (log2Eps e A) Filter.atTop (nhds 0) := by
  have hL := tendsto_lnEps e
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (hL.const_mul 5).add (((hA.add hL).const_mul 140).mul hu)
  simp only [mul_zero, add_zero] at this
  exact this

/-- `log2Approx x e w` encloses `ln x / ln 2` strictly (the significand of `x` not a power of two),
with width at most `log2Eps e |ln x| w` (`w ≥ 64`). -/
theorem log2Approx_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hnp : m.isPowerOfTwo = false) :
    ∃ lv hv' : ℝ, Rounds (log2Approx (finite true e q m hv) e w).1 lv ∧
      Rounds (log2Approx (finite true e q m hv) e w).2 hv' ∧
      lv < Real.log (finiteVal true e m) / Real.log 2 ∧
      Real.log (finiteVal true e m) / Real.log 2 < hv' ∧
      hv' - lv ≤ log2Eps e.toInt |Real.log (finiteVal true e m)| w := by
  have : NeZero w := ⟨by omega⟩
  have hirr : Irrational (Real.log (finiteVal true e m) / Real.log 2) := by
    rw [Real.log_div_log]
    exact irrational_logb_two_finiteVal e m (ne_zero_of_finiteValid e hv)
      (fun h => by rw [← AzNat.isPowerOfTwo_iff] at h; rw [h] at hnp; cases hnp)
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnBracket_spec hw e hv
  obtain ⟨c, d, hc, hd, hcM, hMd, hcd, hcpos⟩ := ln2Bracket_spec w
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hc5 : 1 / 5 ≤ c := hcpos (by omega)
  have hL1 := Real.log_two_gt_d9
  have hc0 : 0 < c := by linarith
  have hM0 : 0 < Real.log 2 := by linarith
  set L := Real.log (finiteVal true e m) with hL
  set ε := lnEps e.toInt w with hε
  have hε0 : 0 ≤ ε := by rw [hε]; unfold lnEps; positivity
  have hLa : L ≤ |L| := le_abs_self L
  have hLa' : -|L| ≤ L := neg_abs_le L
  have habs_a : |a| ≤ |L| + ε := by rw [abs_le]; constructor <;> linarith
  have habs_b : |b| ≤ |L| + ε := by rw [abs_le]; constructor <;> linarith
  have hcd' : 1 / c - 1 / d ≤ 60 * u := by
    have hd0 : 0 < d := by linarith
    rw [div_sub_div _ _ hc0.ne' hd0.ne', div_le_iff₀ (by positivity)]
    have hprod : (1 / 5 : ℝ) * (69 / 100) ≤ c * d :=
      mul_le_mul hc5 (by linarith) (by norm_num) hc0.le
    have := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 60 * u)
    linarith
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := log2Lower_spec w ha hc hd hc0 hcM hMd haL
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := log2Upper_spec w hb hc hd hc0 hcM hMd hLb
  rw [← hu] at hlo2 hhi2
  -- `|a|/c ≤ 5 |a|`, `(b − a)/c ≤ 5 (b − a)`
  have h5a : |a| / c ≤ 5 * |a| := by
    rw [div_le_iff₀ hc0]; nlinarith [abs_nonneg a]
  have h5b : |b| / c ≤ 5 * |b| := by
    rw [div_le_iff₀ hc0]; nlinarith [abs_nonneg b]
  have h5ab : b / c - a / c ≤ 5 * (b - a) := by
    rw [← sub_div, div_le_iff₀ hc0]; nlinarith
  have hqa : |a| * (1 / c - 1 / d) ≤ |a| * (60 * u) := mul_le_mul_of_nonneg_left hcd' (abs_nonneg a)
  have hqb : |b| * (1 / c - 1 / d) ≤ |b| * (60 * u) := mul_le_mul_of_nonneg_left hcd' (abs_nonneg b)
  have hra : 2 * (|a| / c) * u ≤ 2 * (5 * |a|) * u := by
    have := mul_le_mul_of_nonneg_right h5a hu0.le; linarith
  have hrb : 2 * (|b| / c) * u ≤ 2 * (5 * |b|) * u := by
    have := mul_le_mul_of_nonneg_right h5b hu0.le; linarith
  have hau : |a| * u ≤ (|L| + ε) * u := mul_le_mul_of_nonneg_right habs_a hu0.le
  have hbu : |b| * u ≤ (|L| + ε) * u := mul_le_mul_of_nonneg_right habs_b hu0.le
  refine ⟨lo, hi, ?_, ?_, ?_, ?_, ?_⟩
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
  · unfold log2Eps
    rw [← hε, ← hu]
    linarith

/-- The Ziv certificate for `log₂ x`. -/
theorem log2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (e : AzInt) {q : ℕ}
    {m : AzNat} (hv : FiniteValid q m) (hnp : m.isPowerOfTwo = false) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log2Approx (finite true e q m hv) e (w₀ * 2 ^ f)).1
      (log2Approx (finite true e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hirr : Irrational (Real.log (finiteVal true e m) / Real.log 2) := by
    rw [Real.log_div_log]
    exact irrational_logb_two_finiteVal e m (ne_zero_of_finiteValid e hv)
      (fun h => by rw [← AzNat.isPowerOfTwo_iff] at h; rw [h] at hnp; cases hnp)
  exact exists_isSome_of_irrational_threshold p mode (log2Approx (finite true e q m hv) e) hirr
    (log2Eps e.toInt |Real.log (finiteVal true e m)|) (tendsto_log2Eps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv', hl, hh, hlo, hhi, hwid⟩ := log2Approx_spec hw e hv hnp
      exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
