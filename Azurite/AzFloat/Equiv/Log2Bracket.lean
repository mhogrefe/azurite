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
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzRat.Equiv.LogBase2
import Azurite.AzRat.Equiv.Pow2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Equivalence: the bracket of `log₂ x`

* `irrational_logb_two_of_odd`: `log₂ n` is irrational for an odd `n ≠ 1` (if `log₂ n = p/q` then
  `n^q = 2^p`, impossible by parity); `irrational_logb_two_finiteVal`: hence `log₂ x` is
  irrational for a positive float whose significand is not a power of two.
* `finiteVal_true_of_isPowerOfTwo`: a float with a power-of-two significand is `2^(e−1)`.
* `log2Lower_spec`/`log2Upper_spec`, `log2Quotients_spec`: the sign-dependent directed quotients
  bound `L / ln 2` for any bracket `[a, b] ∋ L` of width `ε`, within `5ε + 140 (|L| + ε) 2^(−w)`.
* `log2Approx_spec`, `log2Approx_isSome_exists`: enclosure, width `≤ log2Eps e |ln x| w`, and the
  Ziv certificate, for a float; `irrational_logb_two_of_odd_div`, `irrational_logb_two_toRat`,
  `AzRat.toRat_of_isPowerOfTwo`, `log2RatApprox_spec`, `log2RatApprox_isSome_exists` for a rational.
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

/-- `log2Quotients b w` for a bracket `[a, bv] ∋ L` of width `≤ ε` encloses `L / ln 2`, within
`5ε + 140 (|L| + ε) 2^(−w)` (`w ≥ 64`). -/
theorem log2Quotients_spec {w : ℕ} (hw : 64 ≤ w) {b : AzFloat × AzFloat} {a bv L ε : ℝ}
    (ha : b.1.toVal = some (a : EReal)) (hb : b.2.toVal = some (bv : EReal)) (haL : a ≤ L)
    (hLb : L ≤ bv) (hwid : bv - a ≤ ε) :
    ∃ lo hi : ℝ, (log2Quotients b w).1.toVal = some (lo : EReal) ∧
      (log2Quotients b w).2.toVal = some (hi : EReal) ∧
      lo ≤ L / Real.log 2 ∧ L / Real.log 2 ≤ hi ∧
      hi - lo ≤ 5 * ε + 140 * (|L| + ε) * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨c, d, hc, hd, hcM, hMd, hcd, hcpos⟩ := ln2Bracket_spec w
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hc5 : 1 / 5 ≤ c := hcpos (by omega)
  have hL1 := Real.log_two_gt_d9
  have hc0 : 0 < c := by linarith
  have hM0 : 0 < Real.log 2 := by linarith
  have hε0 : 0 ≤ ε := by linarith
  have hLa : L ≤ |L| := le_abs_self L
  have hLa' : -|L| ≤ L := neg_abs_le L
  have habs_a : |a| ≤ |L| + ε := by rw [abs_le]; constructor <;> linarith
  have habs_b : |bv| ≤ |L| + ε := by rw [abs_le]; constructor <;> linarith
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
  have h5a : |a| / c ≤ 5 * |a| := by
    rw [div_le_iff₀ hc0]; nlinarith [abs_nonneg a]
  have h5b : |bv| / c ≤ 5 * |bv| := by
    rw [div_le_iff₀ hc0]; nlinarith [abs_nonneg bv]
  have h5ab : bv / c - a / c ≤ 5 * (bv - a) := by
    rw [← sub_div, div_le_iff₀ hc0]; nlinarith
  have hqa : |a| * (1 / c - 1 / d) ≤ |a| * (60 * u) := mul_le_mul_of_nonneg_left hcd' (abs_nonneg a)
  have hqb : |bv| * (1 / c - 1 / d) ≤ |bv| * (60 * u) :=
    mul_le_mul_of_nonneg_left hcd' (abs_nonneg bv)
  have hra : 2 * (|a| / c) * u ≤ 2 * (5 * |a|) * u := by
    have := mul_le_mul_of_nonneg_right h5a hu0.le; linarith
  have hrb : 2 * (|bv| / c) * u ≤ 2 * (5 * |bv|) * u := by
    have := mul_le_mul_of_nonneg_right h5b hu0.le; linarith
  have hau : |a| * u ≤ (|L| + ε) * u := mul_le_mul_of_nonneg_right habs_a hu0.le
  have hbu : |bv| * u ≤ (|L| + ε) * u := mul_le_mul_of_nonneg_right habs_b hu0.le
  exact ⟨lo, hi, hlo, hhi, hlo1, hhi1, by linarith⟩

/-- `log2Approx x e w` encloses `ln x / ln 2` strictly (the significand of `x` not a power of two),
with width at most `log2Eps e |ln x| w` (`w ≥ 64`). -/
theorem log2Approx_spec {w : ℕ} (hw : 64 ≤ w) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hnp : m.isPowerOfTwo = false) :
    ∃ lv hv' : ℝ, Rounds (log2Approx (finite true e q m hv) e w).1 lv ∧
      Rounds (log2Approx (finite true e q m hv) e w).2 hv' ∧
      lv < Real.log (finiteVal true e m) / Real.log 2 ∧
      Real.log (finiteVal true e m) / Real.log 2 < hv' ∧
      hv' - lv ≤ log2Eps e.toInt |Real.log (finiteVal true e m)| w := by
  have hirr : Irrational (Real.log (finiteVal true e m) / Real.log 2) := by
    rw [Real.log_div_log]
    exact irrational_logb_two_finiteVal e m (ne_zero_of_finiteValid e hv)
      (fun h => by rw [← AzNat.isPowerOfTwo_iff] at h; rw [h] at hnp; cases hnp)
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnBracket_spec hw e hv
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ := log2Quotients_spec hw ha hb haL hLb hwid
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

/-! ### The rational input -/

/-- `log₂ (n/d)` is irrational for odd coprime `n`, `d` not both `1`. -/
theorem irrational_logb_two_of_odd_div {n d : ℕ} (hn : Odd n) (hd : Odd d)
    (hcop : Nat.Coprime n d) (hne : ¬ (n = 1 ∧ d = 1)) :
    Irrational (Real.logb 2 ((n : ℝ) / d)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd.pos
  rintro ⟨r, hr⟩
  have h2 : (2 : ℝ) ^ (r : ℝ) = n / d := by
    rw [hr]; exact Real.rpow_logb (by norm_num) (by norm_num) (div_pos hnpos hdpos)
  have hq0 : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hrq : (r : ℝ) * r.den = r.num := by rw [Rat.cast_def]; field_simp
  have h3 : ((n : ℝ) / d) ^ r.den = (2 : ℝ) ^ r.num := by
    rw [← h2, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hrq, Real.rpow_intCast]
  have h4 : (n : ℝ) ^ r.den = (2 : ℝ) ^ r.num * (d : ℝ) ^ r.den := by
    rw [div_pow] at h3
    rw [← h3]
    field_simp
  have hqpos : r.den ≠ 0 := r.den_nz
  rcases le_or_gt 0 r.num with hp0 | hp0
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hp0
    rw [hk, zpow_natCast] at h4
    have h5 : n ^ r.den = 2 ^ k * d ^ r.den := by exact_mod_cast h4
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero, one_mul] at h5
      have hnd : n = d := Nat.pow_left_injective hqpos h5
      subst hnd
      have := (Nat.coprime_self n).mp hcop
      exact hne ⟨this, this⟩
    · have heven : Even (n ^ r.den) := by
        rw [h5]; exact (Nat.even_pow.mpr ⟨even_two, hkpos.ne'⟩).mul_right _
      rw [Nat.even_pow] at heven
      exact (Nat.not_even_iff_odd.mpr hn) heven.1
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, r.num = -(k : ℤ) := ⟨(-r.num).toNat, by omega⟩
    have hk1 : 0 < k := by omega
    rw [hk, zpow_neg, zpow_natCast] at h4
    have h6 : (n : ℝ) ^ r.den * 2 ^ k = (d : ℝ) ^ r.den := by rw [h4]; field_simp
    have h7 : n ^ r.den * 2 ^ k = d ^ r.den := by exact_mod_cast h6
    have heven : Even (d ^ r.den) := by
      rw [← h7]; exact (Nat.even_pow.mpr ⟨even_two, hk1.ne'⟩).mul_left _
    rw [Nat.even_pow] at heven
    exact (Nat.not_even_iff_odd.mpr hd) heven.1

/-- `log₂ (N/D)` is irrational for coprime `N`, `D` unless both are powers of two. -/
theorem irrational_logb_two_div {N D : ℕ} (hN : N ≠ 0) (hD : D ≠ 0) (hcop : Nat.Coprime N D)
    (hnp : ¬ (N.isPowerOfTwo ∧ D.isPowerOfTwo)) : Irrational (Real.logb 2 ((N : ℝ) / D)) := by
  obtain ⟨a, n, hn, hNn⟩ := Nat.exists_eq_two_pow_mul_odd hN
  obtain ⟨b, d, hd, hDd⟩ := Nat.exists_eq_two_pow_mul_odd hD
  have hcop' : Nat.Coprime n d :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ hDd.symm)
      (Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hNn.symm) hcop)
  have hne : ¬ (n = 1 ∧ d = 1) := by
    rintro ⟨rfl, rfl⟩
    exact hnp ⟨⟨a, by rw [hNn, mul_one]⟩, ⟨b, by rw [hDd, mul_one]⟩⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.pos.ne'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.pos.ne'
  rw [hNn, hDd]
  push_cast
  have e : (2 : ℝ) ^ a * n / (2 ^ b * d) = (n / d) * 2 ^ ((a : ℤ) - b) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
    field_simp
  rw [e, Real.logb_mul (div_ne_zero hn0 hd0) (zpow_ne_zero _ (by norm_num)), logb_two_zpow]
  exact (irrational_logb_two_of_odd_div hn hd hcop' hne).add_intCast _

/-- The value of a positive rational as a quotient of naturals. -/
theorem coe_toRat_eq_div_of_sign (q : AzRat) (hs : q.sign = true) :
    (AzRat.toRat q : ℝ) = (q.num.toNat : ℝ) / q.den.toNat := by
  rw [coe_toRat_eq, hs]; simp

/-- `log₂ q` is irrational for a positive rational `q` that is not a power of two. -/
theorem irrational_logb_two_toRat (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hnp : q.isPowerOfTwo = false) : Irrational (Real.logb 2 (AzRat.toRat q : ℝ)) := by
  have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  have h0 : q.num ≠ 0 := fun h => by
    rw [(AzRat.toRat_eq_zero_iff q).mpr h] at hqr; exact lt_irrefl _ hqr
  have hs : q.sign = true := by
    by_contra hs
    have := toRat_neg_of_sign q (Bool.eq_false_iff.mpr hs) h0
    linarith
  rw [coe_toRat_eq_div_of_sign q hs]
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  have hnp' : ¬ (q.num.toNat.isPowerOfTwo ∧ q.den.toNat.isPowerOfTwo) := by
    rintro ⟨h1, h2⟩
    have : q.isPowerOfTwo = true := (AzRat.isPowerOfTwo_iff q).mpr ⟨hs, h1, h2⟩
    rw [this] at hnp; cases hnp
  exact irrational_logb_two_div (toNat_ne_zero_of_ne_zero h0) (toNat_ne_zero_of_ne_zero q.den_nz)
    hcop hnp'

/-- A positive rational power of two is nonzero as a rational; a positive rational that is not
a power of two is not `1`. -/
theorem toRat_ne_one_of_not_isPowerOfTwo (q : AzRat) (hs : q.sign = true)
    (hnp : q.isPowerOfTwo = false) : AzRat.toRat q ≠ 1 := by
  intro h1
  have hden : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  have h1' : (AzRat.toRat q : ℝ) = 1 := by exact_mod_cast h1
  rw [coe_toRat_eq_div_of_sign q hs, div_eq_one_iff_eq hden.ne'] at h1'
  have heq : q.num.toNat = q.den.toNat := by exact_mod_cast h1'
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  rw [heq, Nat.coprime_self] at hcop
  have : q.isPowerOfTwo = true :=
    (AzRat.isPowerOfTwo_iff q).mpr
      ⟨hs, ⟨0, by rw [heq, hcop, pow_zero]⟩, ⟨0, by rw [hcop, pow_zero]⟩⟩
  rw [this] at hnp; cases hnp

/-- The width bound of `log2RatApprox`. -/
noncomputable def log2RatEps (E : ℕ) (A : ℝ) (w : ℕ) : ℝ :=
  5 * lnRatEps E A w + 140 * (A + lnRatEps E A w) * (1 / 2 : ℝ) ^ w

theorem tendsto_log2RatEps (E : ℕ) (A : ℝ) :
    Filter.Tendsto (log2RatEps E A) Filter.atTop (nhds 0) := by
  have hL := tendsto_lnRatEps E A
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hA : Filter.Tendsto (fun _ : ℕ => A) Filter.atTop (nhds A) := tendsto_const_nhds
  have := (hL.const_mul 5).add (((hA.add hL).const_mul 140).mul hu)
  simp only [mul_zero, add_zero] at this
  exact this

/-- `log2RatApprox q w` encloses `log₂ q` strictly (`q > 0` not a power of two), with width at most
`log2RatEps E |ln q| w` (`w ≥ 64`). -/
theorem log2RatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (hnp : q.isPowerOfTwo = false) :
    ∃ lv hv : ℝ, Rounds (log2RatApprox q w).1 lv ∧ Rounds (log2RatApprox q w).2 hv ∧
      lv < Real.logb 2 (AzRat.toRat q : ℝ) ∧ Real.logb 2 (AzRat.toRat q : ℝ) < hv ∧
      hv - lv ≤ log2RatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2)
        |Real.log (AzRat.toRat q : ℝ)| w := by
  have : NeZero w := ⟨by omega⟩
  have hirr := irrational_logb_two_toRat q hq hnp
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  have hqv0 : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [abs_of_pos hqv0] at hr2
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hqv0 hr1 hr2
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ := log2Quotients_spec hw ha hb haL hLb hwid
  rw [Real.log_div_log] at hlo1 hhi1
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

/-- The Ziv certificate for `log₂ q`. -/
theorem log2RatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (hq : (0 : ℚ) < AzRat.toRat q) (hnp : q.isPowerOfTwo = false) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log2RatApprox q (w₀ * 2 ^ f)).1 (log2RatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (log2RatApprox q)
    (irrational_logb_two_toRat q hq hnp)
    (log2RatEps (⌊2 * |Real.log (AzRat.toRat q : ℝ)|⌋₊ + 2) |Real.log (AzRat.toRat q : ℝ)|)
    (tendsto_log2RatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := log2RatApprox_spec hw q hq hnp
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### `log₂ (1 + x)` -/

/-- A positive rational that is not a power of two has an irrational `log₂`. -/
theorem irrational_logb_two_of_rat {v : ℝ} (hv : 0 < v) {r : ℚ} (hr : v = r)
    (hnp : ∀ j : ℤ, v ≠ 2 ^ j) : Irrational (Real.logb 2 v) := by
  have hr0 : 0 < r := by
    have : (0 : ℝ) < (r : ℝ) := hr ▸ hv
    exact_mod_cast this
  have hnum : 0 < r.num := Rat.num_pos.mpr hr0
  have hNeq : (r.num : ℝ) = (r.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_pos (by exact_mod_cast hnum)]
  have hv' : v = (r.num.natAbs : ℝ) / r.den := by rw [hr, Rat.cast_def, hNeq]
  have hN0 : r.num.natAbs ≠ 0 := (Int.natAbs_pos.mpr hnum.ne').ne'
  rw [hv']
  apply irrational_logb_two_div hN0 r.den_nz r.reduced
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  apply hnp ((a : ℤ) - b)
  rw [hv', ha, hb]
  push_cast
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]

/-- A float whose value is a power of two has a power-of-two significand. -/
theorem isPowerOfTwo_of_finiteVal_eq_zpow (e : AzInt) (m : AzNat) (j : ℤ)
    (h : finiteVal true e m = (2 : ℝ) ^ j) : m.isPowerOfTwo = true := by
  rw [finiteVal_true_eq] at h
  have hE : (2 : ℝ) ^ (e.toInt - m.size) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hm : (m.toNat : ℝ) = (2 : ℝ) ^ (j - (e.toInt - m.size)) := by
    rw [zpow_sub₀ (by norm_num), eq_div_iff hE, h]
  have ht : 0 ≤ j - (e.toInt - m.size) := by
    by_contra hlt
    have h1 : (2 : ℝ) ^ (j - (e.toInt - m.size)) < 1 := zpow_lt_one_of_neg₀ (by norm_num) (by omega)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (j - (e.toInt - m.size)) := zpow_pos (by norm_num) _
    have h3 : m.toNat < 1 := by exact_mod_cast (hm ▸ h1 : (m.toNat : ℝ) < 1)
    have h4 : (m.toNat : ℝ) = 0 := by exact_mod_cast Nat.lt_one_iff.mp h3
    linarith
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le ht
  rw [hn, zpow_natCast] at hm
  exact (AzNat.isPowerOfTwo_iff m).mpr ⟨n, by exact_mod_cast hm⟩

/-- The floor of `1 + x` at precision `w`, as a rounding of its value. -/
theorem toVal_onePlus_floor {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (w : ℕ)
    [NeZero w] :
    (addPrecRound one x w .Floor).1.toVal
      = some (RoundingTarget.round (floatSet w) .Floor (1 + xv)).val := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, toVal_one', hx, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact (roundVal_coe w .Floor _).1

theorem toVal_onePlus_ceiling {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (w : ℕ)
    [NeZero w] :
    (addPrecRound one x w .Ceiling).1.toVal
      = some (RoundingTarget.round (floatSet w) .Ceiling (1 + xv)).val := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, toVal_one', hx, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact (roundVal_coe w .Ceiling _).1

/-- `onePlusPow2Exponent? x w = some k` means `1 + x = 2^k`. -/
theorem onePlusPow2Exponent?_some {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (w : ℕ) [NeZero w] {k : AzInt} (h : onePlusPow2Exponent? x w = some k) :
    1 + xv = (2 : ℝ) ^ k.toInt := by
  obtain ⟨lo, hlo, hlo1, -⟩ := addFloor_abs toVal_one' hx w
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs toVal_one' hx w
  rcases hs : (addPrecRound one x w .Floor).1 with _ | s | _ | ⟨s, e', q', m', hv'⟩ <;>
    simp only [onePlusPow2Exponent?, hs] at h
  · cases h
  · cases h
  · cases h
  · cases s with
    | false => simp at h
    | true =>
      simp only at h
      split_ifs at h with hc
      rw [Option.some.injEq] at h
      subst h
      rw [Bool.and_eq_true] at hc
      obtain ⟨v, hv1, hv2⟩ := (eqIEEE_iff _ _).mp hc.1
      rw [hs, toVal_finite, Option.some.injEq] at hlo
      rw [toVal_finite, Option.some.injEq] at hv1
      rw [hhi, Option.some.injEq, ← hv1, EReal.coe_eq_coe_iff] at hv2
      rw [EReal.coe_eq_coe_iff] at hlo
      have h1 : 1 + xv = finiteVal true e' m' := by linarith
      rw [h1, finiteVal_true_of_isPowerOfTwo e' m' hc.2, AzInt.toInt_sub]
      rfl

/-- `onePlusPow2Exponent? x w = none` (with `w ≥ 2`, `1 + x > 0`) means `1 + x` is not a power of
two: a power of two is representable at precision `w`, so its floor and ceiling coincide and its
significand is a power of two. -/
theorem onePlusPow2Exponent?_none {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {w : ℕ} (hw : 2 ≤ w) (hpos : 0 < 1 + xv) (h : onePlusPow2Exponent? x w = none) (j : ℤ) :
    1 + xv ≠ (2 : ℝ) ^ j := by
  intro hj
  have : NeZero w := ⟨by omega⟩
  have hmem : ((1 + xv : ℝ) : EReal) ∈ floatSet w := by
    have := mem_floatSet_mul_zpow w 1 j (by rw [abs_one]; exact_mod_cast Nat.one_le_two_pow)
    rw [hj]
    simpa using this
  have hlo : (addPrecRound one x w .Floor).1.toVal = some ((1 + xv : ℝ) : EReal) := by
    rw [toVal_onePlus_floor hx w, RoundingTarget.val_round_of_mem _ _ hmem]
  have hhi : (addPrecRound one x w .Ceiling).1.toVal = some ((1 + xv : ℝ) : EReal) := by
    rw [toVal_onePlus_ceiling hx w, RoundingTarget.val_round_of_mem _ _ hmem]
  obtain ⟨e', q', m', hv', hs, hval⟩ := eq_finite_true_of_toVal_pos hlo hpos
  have heq : eqIEEE (addPrecRound one x w .Floor).1 (addPrecRound one x w .Ceiling).1 = true :=
    (eqIEEE_iff _ _).mpr ⟨_, hlo, hhi⟩
  have hpow : m'.isPowerOfTwo = true :=
    isPowerOfTwo_of_finiteVal_eq_zpow e' m' j (by rw [hval, hj])
  rw [hs] at heq
  simp only [onePlusPow2Exponent?, hs, heq, hpow, Bool.and_self, ↓reduceIte] at h
  exact absurd h (Option.some_ne_none _)

/-- `log₂ (1 + x)` is irrational when the exactness test fails. -/
theorem irrational_logb_two_one_add_of_none {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal))
    {w : ℕ} (hw : 2 ≤ w) (hpos : 0 < 1 + xv) (h : onePlusPow2Exponent? x w = none) :
    Irrational (Real.logb 2 (1 + xv)) := by
  obtain ⟨rx, hrx⟩ := exists_rat_of_toVal hx
  exact irrational_logb_two_of_rat hpos (r := 1 + rx) (by push_cast; rw [hrx])
    (onePlusPow2Exponent?_none hx hw hpos h)

/-- `log2p1Approx x w` encloses `log₂ (1 + x)` strictly (given its irrationality), with width at
most `log2RatEps E |ln (1 + x)| w` (`w ≥ 64`, `x > −1`). -/
theorem log2p1Approx_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv)
    (hirr : Irrational (Real.logb 2 (1 + xv))) :
    ∃ lv hv : ℝ, Rounds (log2p1Approx x w).1 lv ∧ Rounds (log2p1Approx x w).2 hv ∧
      lv < Real.logb 2 (1 + xv) ∧ Real.logb 2 (1 + xv) < hv ∧
      hv - lv ≤ log2RatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w := by
  have : NeZero w := ⟨by omega⟩
  have hpos : 0 < 1 + xv := by linarith
  obtain ⟨r, hr, hf⟩ := addFloor_err toVal_one' hx w hpos.le
  obtain ⟨a, b, ha, hb, haL, hLb, hwid⟩ := lnFloorBracket_spec hw hr hpos hf.le hf.ge
  obtain ⟨lo, hi, hlo, hhi, hlo1, hhi1, hwidth⟩ := log2Quotients_spec hw ha hb haL hLb hwid
  rw [Real.log_div_log] at hlo1 hhi1
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

/-- The Ziv certificate for `log₂ (1 + x)`. -/
theorem log2p1Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx1 : -1 < xv)
    (hirr : Irrational (Real.logb 2 (1 + xv))) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log2p1Approx x (w₀ * 2 ^ f)).1 (log2p1Approx x (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (log2p1Approx x) hirr
    (log2RatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)|) (tendsto_log2RatEps _ _) 64
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := log2p1Approx_spec hw hx hx1 hirr
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
