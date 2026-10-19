/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2Bracket
import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzFloat.Equiv.Constants
import Azurite.AzFloat.Equiv.DirectedRounding
import Azurite.AzNat.Equiv.AtanhSplit
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzInt.Equiv.Sub
import Azurite.Transcendental.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Equivalence: the bracket of `ln 2`

The exact ends `ln2Lo w ≤ ln 2 ≤ ln2Hi w` (`log_two_mem_Icc`) have width `≤ 2^(−w)`
(`ln2Hi_sub_ln2Lo`); each series `S` is enclosed by `seriesBracket` within relative errors
`6 · 2^(−k)` below and `8 · 2^(−k)` above (`seriesBracket_spec`), the tails are below `2^(−w−5)`,
and the float combination at `k = w + 8` gives `lv ≤ ln 2 ≤ hv` with `hv − lv ≤ 8 · 2^(−w)` and
`lv ≥ 1/5` from `w = 2` on (`ln2Bracket_spec`).  The ends are strictly inside since `ln 2` is
irrational and float values are rational (`exists_rat_of_toVal`, `ln2Approx_spec`); the Ziv
certificate is `ln2Approx_isSome_exists`.  The reciprocal bracket (`log2EBracket_spec`, width
`≤ 80 · 2^(−w)` for `w ≥ 2`) gives `log2EApprox_spec` and `log2EApprox_isSome_exists`.
-/

namespace Azurite.AzFloat

open Finset BZ

/-! ### Float values are rational -/

/-- The value of a finite float is a rational. -/
theorem exists_rat_of_toVal {x : AzFloat} {v : ℝ} (hx : x.toVal = some (v : EReal)) :
    ∃ r : ℚ, v = r := by
  have hfin : x.isFinite = true := isFinite_of_toVal_coe hx
  have hs : x.toAzRat?.isSome = true := by rw [isSome_toAzRat?]; exact hfin
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  have := toVal_of_toAzRat? x r hr
  rw [hx, Option.some.injEq, EReal.coe_eq_coe_iff] at this
  exact ⟨AzRat.toRat r, this⟩

/-! ### The exact ends -/

/-- The exact lower end `18 S₁ − 2 (S₂ + (4/3) t₂) + 8 S₃`. -/
noncomputable def ln2Lo (w : ℕ) : ℝ :=
  18 * ∑ k ∈ range (ln2N₁ w), atanhTerm 26 k
    - 2 * (∑ k ∈ range (ln2N₂ w), atanhTerm 4801 k + 4 / 3 * atanhTerm 4801 (ln2N₂ w))
    + 8 * ∑ k ∈ range (ln2N₃ w), atanhTerm 8749 k

/-- The exact upper end `18 (S₁ + (4/3) t₁) − 2 S₂ + 8 (S₃ + (4/3) t₃)`. -/
noncomputable def ln2Hi (w : ℕ) : ℝ :=
  18 * (∑ k ∈ range (ln2N₁ w), atanhTerm 26 k + 4 / 3 * atanhTerm 26 (ln2N₁ w))
    - 2 * ∑ k ∈ range (ln2N₂ w), atanhTerm 4801 k
    + 8 * (∑ k ∈ range (ln2N₃ w), atanhTerm 8749 k + 4 / 3 * atanhTerm 8749 (ln2N₃ w))

/-- `lo ≤ ln 2 ≤ hi`. -/
theorem ln2Lo_le_log_two_le (w : ℕ) : ln2Lo w ≤ Real.log 2 ∧ Real.log 2 ≤ ln2Hi w :=
  log_two_mem_Icc _ _ _

/-- The term counts satisfy `(2N+1)⌊lg q⌋ ≥ w + 6`. -/
theorem ln2N_spec (w : ℕ) :
    w + 6 ≤ (2 * ln2N₁ w + 1) * 4 ∧ w + 6 ≤ (2 * ln2N₂ w + 1) * 12 ∧
      w + 6 ≤ (2 * ln2N₃ w + 1) * 13 := by
  unfold ln2N₁ ln2N₂ ln2N₃
  omega

/-- `t_N(q) ≤ (1/2)^(w+6)` once `2^b ≤ q` and `(2N+1) b ≥ w + 6`. -/
theorem atanhTerm_le_half_pow {q b N w : ℕ} (hq : 2 ^ b ≤ q) (h : w + 6 ≤ (2 * N + 1) * b) :
    atanhTerm q N ≤ (1 / 2 : ℝ) ^ (w + 6) := by
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    exact_mod_cast this.trans hq
  have hqr : (2 : ℝ) ^ b ≤ q := by exact_mod_cast hq
  refine (atanhTerm_le hq1 N).trans ?_
  calc (1 / (q : ℝ)) ^ (2 * N + 1) ≤ (1 / (2 : ℝ) ^ b) ^ (2 * N + 1) := by
        gcongr
    _ = (1 / 2 : ℝ) ^ ((2 * N + 1) * b) := by rw [one_div_pow, ← pow_mul, mul_comm, one_div_pow]
    _ ≤ (1 / 2 : ℝ) ^ (w + 6) := pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- `hi − lo ≤ (1/2)^w`. -/
theorem ln2Hi_sub_ln2Lo (w : ℕ) : ln2Hi w - ln2Lo w ≤ (1 / 2 : ℝ) ^ w := by
  unfold ln2Lo ln2Hi
  obtain ⟨h1, h2, h3⟩ := ln2N_spec w
  have t1 := atanhTerm_le_half_pow (by norm_num : 2 ^ 4 ≤ 26) h1
  have t2 := atanhTerm_le_half_pow (by norm_num : 2 ^ 12 ≤ 4801) h2
  have t3 := atanhTerm_le_half_pow (by norm_num : 2 ^ 13 ≤ 8749) h3
  have hp : (1 / 2 : ℝ) ^ (w + 6) = (1 / 2 : ℝ) ^ w / 64 := by rw [pow_add]; norm_num; ring
  rw [hp] at t1 t2 t3
  simp only [Nat.cast_ofNat] at t1 t2 t3
  have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) w
  linarith

/-! ### The series brackets -/

/-- A partial sum of `atanh(1/q)` is at most `1/(q − 1)` (`log x ≤ x − 1`). -/
theorem sum_atanhTerm_le {q : ℝ} (hq : 2 ≤ q) (N : ℕ) :
    ∑ k ∈ range N, atanhTerm q k ≤ 1 / (q - 1) := by
  have hq1 : 1 < q := by linarith
  have hne : q - 1 ≠ 0 := by linarith
  have hpos : 0 < (q + 1) / (q - 1) := div_pos (by linarith) (by linarith)
  calc ∑ k ∈ range N, atanhTerm q k ≤ atanhInv q := sum_le_atanhInv hq N
    _ = Real.log ((q + 1) / (q - 1)) / 2 := atanhInv_eq hq1
    _ ≤ ((q + 1) / (q - 1) - 1) / 2 := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
    _ = 1 / (q - 1) := by field_simp; ring

/-- The denominator of a truncated series is nonzero (the series is positive). -/
theorem atanhNumDen_den_ne_zero {q : ℕ} (hq : 0 < q) {N : ℕ} (hN : 0 < N) :
    ((AzNat.atanhNumDen q N).2.toNat : ℝ) ≠ 0 := by
  intro h
  have := AzNat.atanhNumDen_eq hq N
  rw [h, div_zero] at this
  have hpos : 0 < ∑ k ∈ range N, atanhTerm q k :=
    sum_pos (fun k _ => atanhTerm_pos (by exact_mod_cast hq) k) (nonempty_range_iff.mpr hN.ne')
  exact hpos.ne this

/-- `seriesBracket` encloses the exact series `S` with relative errors `6 · 2^(−k)` below and
`8 · 2^(−k)` above (`k ≥ 4`). -/
theorem seriesBracket_spec {q : ℕ} (hq : 0 < q) {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : 4 ≤ k) :
    ∃ lv hv : ℝ, (seriesBracket (AzNat.atanhNumDen q N) k).1.toVal = some (lv : EReal) ∧
      (seriesBracket (AzNat.atanhNumDen q N) k).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv ≤ ∑ i ∈ range N, atanhTerm q i ∧
      (∑ i ∈ range N, atanhTerm q i) * (1 - 6 * (1 / 2 : ℝ) ^ k) ≤ lv ∧
      ∑ i ∈ range N, atanhTerm q i ≤ hv ∧
      hv ≤ (∑ i ∈ range N, atanhTerm q i) * (1 + 8 * (1 / 2 : ℝ) ^ k) := by
  have : NeZero k := ⟨by omega⟩
  set S := ∑ i ∈ range N, atanhTerm q i with hSdef
  set n : ℝ := ((AzNat.atanhNumDen q N).1.toNat : ℝ) with hndef
  set d : ℝ := ((AzNat.atanhNumDen q N).2.toNat : ℝ) with hddef
  have hSeq : n / d = S := AzNat.atanhNumDen_eq hq N
  have hd0 : 0 < d := lt_of_le_of_ne (Nat.cast_nonneg _) (atanhNumDen_den_ne_zero hq hN).symm
  have hn : n = S * d := by rw [← hSeq]; field_simp
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => (atanhTerm_pos (by exact_mod_cast hq) i).le
  have hn0 : 0 ≤ n := by rw [hn]; exact mul_nonneg hS0 hd0.le
  set x := (1 / 2 : ℝ) ^ k with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 16 := by
    calc x ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 16 := by norm_num
  obtain ⟨n₁, hn₁, hfn₁⟩ := setPrecFloor_err (toVal_ofAzNat (AzNat.atanhNumDen q N).1) hn0 k
  obtain ⟨d₁, hd₁, hcd₁⟩ := setPrecCeiling_err (toVal_ofAzNat (AzNat.atanhNumDen q N).2) hd0.le k
  obtain ⟨n₂, hn₂, hcn₂⟩ := setPrecCeiling_err (toVal_ofAzNat (AzNat.atanhNumDen q N).1) hn0 k
  obtain ⟨d₂, hd₂, hfd₂⟩ := setPrecFloor_err (toVal_ofAzNat (AzNat.atanhNumDen q N).2) hd0.le k
  have hd₁0 : 0 < d₁ := lt_of_lt_of_le hd0 hcd₁.ge
  have hd₂0 : 0 < d₂ := by
    have h0 : d ≤ d₂ + 2 * d * x := hfd₂.ge
    have h1 : 2 * d * x ≤ 2 * d * (1 / 16) := mul_le_mul_of_nonneg_left hx1 (by positivity)
    linarith
  obtain ⟨lv, hlv, hfl⟩ := divFloor_err hn₁ hd₁ hd₁0 hfn₁.nonneg k
  obtain ⟨hv, hhv, hcl⟩ := divCeiling_err hn₂ hd₂ hd₂0 (hn0.trans hcn₂.ge) k
  have hq1 : n₁ / d₁ ≤ S := by
    rw [← hSeq]; exact div_le_div₀ hn0 hfn₁.le hd0 hcd₁.ge
  have hq2 : S ≤ n₂ / d₂ := by
    rw [← hSeq]; exact div_le_div₀ (hn0.trans hcn₂.ge) hcn₂.ge hd₂0 hfd₂.le
  have hq1' : S * (1 - 4 * x) ≤ n₁ / d₁ := by
    rw [le_div_iff₀ hd₁0]
    have hc : 0 ≤ S * (1 - 4 * x) := mul_nonneg hS0 (by linarith)
    have h0 : d₁ ≤ d + 2 * d * x := hcd₁.le
    have h1 : S * (1 - 4 * x) * d₁ ≤ S * (1 - 4 * x) * (d + 2 * d * x) :=
      mul_le_mul_of_nonneg_left h0 hc
    have h2 : S * (1 - 4 * x) * (d + 2 * d * x) = S * d * (1 - 2 * x) - 8 * (S * d * (x * x)) := by
      ring
    have h3 : 0 ≤ S * d * (x * x) := mul_nonneg (mul_nonneg hS0 hd0.le) (mul_nonneg hx0.le hx0.le)
    have h4 : n ≤ n₁ + 2 * n * x := hfn₁.ge
    rw [hn] at h4
    linarith
  have hq2' : n₂ / d₂ ≤ S * (1 + 5 * x) := by
    rw [div_le_iff₀ hd₂0]
    have h0 : d ≤ d₂ + 2 * d * x := hfd₂.ge
    have h1 : S * (1 + 5 * x) * (d - 2 * d * x) ≤ S * (1 + 5 * x) * d₂ :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 (by linarith))
    have h2 : S * (1 + 5 * x) * (d - 2 * d * x)
        = S * d * (1 + 2 * x) + S * d * (x * (1 - 10 * x)) := by ring
    have h3 : 0 ≤ S * d * (x * (1 - 10 * x)) :=
      mul_nonneg (mul_nonneg hS0 hd0.le) (mul_nonneg hx0.le (by linarith))
    have h4 : n₂ ≤ n + 2 * n * x := hcn₂.le
    rw [hn] at h4
    linarith
  have hfl1 := hfl.le
  have hfl2 : n₁ / d₁ ≤ lv + 2 * (n₁ / d₁) * x := hfl.ge
  have hcl1 := hcl.ge
  have hcl2 : hv ≤ n₂ / d₂ + 2 * (n₂ / d₂) * x := hcl.le
  refine ⟨lv, hv, hlv, hhv, hfl.nonneg, hfl1.trans hq1, ?_, hq2.trans hcl1, ?_⟩
  · have h1 : S * (1 - 4 * x) * (1 - 2 * x) ≤ n₁ / d₁ * (1 - 2 * x) :=
      mul_le_mul_of_nonneg_right hq1' (by linarith)
    have h2 : S * (1 - 4 * x) * (1 - 2 * x) = S * (1 - 6 * x) + 8 * (S * (x * x)) := by ring
    have h3 : 0 ≤ S * (x * x) := mul_nonneg hS0 (mul_nonneg hx0.le hx0.le)
    linarith
  · have h1 : n₂ / d₂ * (1 + 2 * x) ≤ S * (1 + 5 * x) * (1 + 2 * x) :=
      mul_le_mul_of_nonneg_right hq2' (by linarith)
    have h2 : S * (1 + 5 * x) * (1 + 2 * x) = S * (1 + 8 * x) - S * (x * (1 - 10 * x)) := by ring
    have h3 : 0 ≤ S * (x * (1 - 10 * x)) := mul_nonneg hS0 (mul_nonneg hx0.le (by linarith))
    linarith

/-- The tail bound float `2^(−w−5)`. -/
theorem toVal_tail (w : ℕ) :
    (powerOf2 (-(AzNat.ofNat (w + 5)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (w + 5) : ℝ) : EReal) := by
  rw [toVal_powerOf2, AzInt.toInt_neg, toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg, zpow_natCast,
    one_div_pow, one_div]

/-! ### The float bracket -/

set_option maxHeartbeats 400000 in
/-- `ln2Bracket w` encloses `ln 2` with width at most `8 · 2^(−w)`, and its lower end is at least
`1/5` from `w = 2` on. -/
theorem ln2Bracket_spec (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, (ln2Bracket w).1.toVal = some (lv : EReal) ∧
      (ln2Bracket w).2.toVal = some (hv : EReal) ∧
      lv ≤ Real.log 2 ∧ Real.log 2 ≤ hv ∧ hv - lv ≤ 8 * (1 / 2 : ℝ) ^ w ∧
      (2 ≤ w → 1 / 5 ≤ lv) := by
  have hk : NeZero (w + 8) := ⟨by omega⟩
  have hw1 : 1 ≤ w := NeZero.one_le
  -- the exact ends and their tails
  have hlo := (ln2Lo_le_log_two_le w).1
  have hhi := (ln2Lo_le_log_two_le w).2
  have hwid := ln2Hi_sub_ln2Lo w
  unfold ln2Lo at hlo
  unfold ln2Hi at hhi
  unfold ln2Lo ln2Hi at hwid
  obtain ⟨hN1, hN2, hN3⟩ := ln2N_spec w
  have t1 := atanhTerm_le_half_pow (by norm_num : 2 ^ 4 ≤ 26) hN1
  have t2 := atanhTerm_le_half_pow (by norm_num : 2 ^ 12 ≤ 4801) hN2
  have t3 := atanhTerm_le_half_pow (by norm_num : 2 ^ 13 ≤ 8749) hN3
  simp only [Nat.cast_ofNat] at t1 t2 t3
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  -- the units
  set u := (1 / 2 : ℝ) ^ w with hu
  set uk := (1 / 2 : ℝ) ^ (w + 8) with huk
  set tv := (1 / 2 : ℝ) ^ (w + 5) with htv
  have hu0 : 0 < u := by positivity
  have huk0 : 0 < uk := by positivity
  have htv0 : 0 < tv := by positivity
  have hukU : uk = u / 256 := by rw [huk, hu, pow_add]; ring
  have htvU : tv = u / 32 := by rw [htv, hu, pow_add]; ring
  have hu1 : u ≤ 1 / 2 := by
    calc u ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw1
      _ = 1 / 2 := by norm_num
  have ht6 : (1 / 2 : ℝ) ^ (w + 6) = tv / 2 := by rw [htv, pow_add, pow_add]; ring
  rw [ht6] at t1 t2 t3
  -- the series
  set S₁ := ∑ k ∈ range (ln2N₁ w), atanhTerm 26 k with hS₁
  set S₂ := ∑ k ∈ range (ln2N₂ w), atanhTerm 4801 k with hS₂
  set S₃ := ∑ k ∈ range (ln2N₃ w), atanhTerm 8749 k with hS₃
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun i _ => (atanhTerm_pos (by norm_num) i).le
  have hS₂0 : 0 ≤ S₂ := sum_nonneg fun i _ => (atanhTerm_pos (by norm_num) i).le
  have hS₃0 : 0 ≤ S₃ := sum_nonneg fun i _ => (atanhTerm_pos (by norm_num) i).le
  have hS₁1 : S₁ ≤ 1 / 25 := by
    have := sum_atanhTerm_le (by norm_num : (2 : ℝ) ≤ 26) (ln2N₁ w); norm_num at this ⊢; exact this
  have hS₂1 : S₂ ≤ 1 / 4800 := by
    have := sum_atanhTerm_le (by norm_num : (2 : ℝ) ≤ 4801) (ln2N₂ w); norm_num at this ⊢
    exact this
  have hS₃1 : S₃ ≤ 1 / 8748 := by
    have := sum_atanhTerm_le (by norm_num : (2 : ℝ) ≤ 8749) (ln2N₃ w); norm_num at this ⊢
    exact this
  obtain ⟨l₁, h₁, hl₁, hh₁, hl₁0, hl₁S, hSl₁, hSh₁, hh₁S⟩ :=
    seriesBracket_spec (by norm_num : 0 < 26) (N := ln2N₁ w) (by unfold ln2N₁; omega)
      (k := w + 8) (by omega)
  obtain ⟨l₂, h₂, hl₂, hh₂, hl₂0, hl₂S, hSl₂, hSh₂, hh₂S⟩ :=
    seriesBracket_spec (by norm_num : 0 < 4801) (N := ln2N₂ w) (by unfold ln2N₂; omega)
      (k := w + 8) (by omega)
  obtain ⟨l₃, h₃, hl₃, hh₃, hl₃0, hl₃S, hSl₃, hSh₃, hh₃S⟩ :=
    seriesBracket_spec (by norm_num : 0 < 8749) (N := ln2N₃ w) (by unfold ln2N₃; omega)
      (k := w + 8) (by omega)
  push_cast at hl₁S hSl₁ hSh₁ hh₁S hl₂S hSl₂ hSh₂ hh₂S hl₃S hSl₃ hSh₃ hh₃S
  -- the constants
  have hc18 : (ofAzNat (AzNat.ofNat 18)).toVal = some ((18 : ℝ) : EReal) := by
    have := toVal_ofAzNat_ofNat 18; push_cast at this; exact this
  have hc8 : (ofAzNat (AzNat.ofNat 8)).toVal = some ((8 : ℝ) : EReal) := by
    have := toVal_ofAzNat_ofNat 8; push_cast at this; exact this
  have hc2 : (ofAzNat (AzNat.ofNat 2)).toVal = some ((2 : ℝ) : EReal) := by
    have := toVal_ofAzNat_ofNat 2; push_cast at this; exact this
  have ht := toVal_tail w
  -- magnitudes of the series ends
  have hl₁1 : l₁ ≤ 1 / 25 := hl₁S.trans hS₁1
  have hl₂1 : l₂ ≤ 1 / 4800 := hl₂S.trans hS₂1
  have hl₃1 : l₃ ≤ 1 / 8748 := hl₃S.trans hS₃1
  have huk1 : uk ≤ 1 / 512 := by rw [hukU]; linarith
  have htv1 : tv ≤ 1 / 64 := by rw [htvU]; linarith
  have hh₁1 : h₁ ≤ 1 / 24 := by
    have : S₁ * (1 + 8 * uk) ≤ 1 / 25 * (1 + 8 / 512) :=
      mul_le_mul hS₁1 (by linarith) (by linarith) (by norm_num)
    linarith
  have hh₂1 : h₂ ≤ 1 / 4000 := by
    have : S₂ * (1 + 8 * uk) ≤ 1 / 4800 * (1 + 8 / 512) :=
      mul_le_mul hS₂1 (by linarith) (by linarith) (by norm_num)
    linarith
  have hh₃1 : h₃ ≤ 1 / 8000 := by
    have : S₃ * (1 + 8 * uk) ≤ 1 / 8748 * (1 + 8 / 512) :=
      mul_le_mul hS₃1 (by linarith) (by linarith) (by norm_num)
    linarith
  have hh₁0 : 0 ≤ h₁ := hS₁0.trans hSh₁
  have hh₂0 : 0 ≤ h₂ := hS₂0.trans hSh₂
  have hh₃0 : 0 ≤ h₃ := hS₃0.trans hSh₃
  -- relative errors of the series as absolute ones (`S_i ≤ 1/6`)
  have hl₁e : S₁ - uk ≤ l₁ := by
    have : S₁ * (6 * uk) ≤ 1 / 25 * (6 * uk) := mul_le_mul_of_nonneg_right hS₁1 (by positivity)
    linarith
  have hl₂e : S₂ - uk ≤ l₂ := by
    have : S₂ * (6 * uk) ≤ 1 / 4800 * (6 * uk) := mul_le_mul_of_nonneg_right hS₂1 (by positivity)
    linarith
  have hl₃e : S₃ - uk ≤ l₃ := by
    have : S₃ * (6 * uk) ≤ 1 / 8748 * (6 * uk) := mul_le_mul_of_nonneg_right hS₃1 (by positivity)
    linarith
  have hh₁e : h₁ ≤ S₁ + uk := by
    have : S₁ * (8 * uk) ≤ 1 / 25 * (8 * uk) := mul_le_mul_of_nonneg_right hS₁1 (by positivity)
    linarith
  have hh₂e : h₂ ≤ S₂ + uk := by
    have : S₂ * (8 * uk) ≤ 1 / 4800 * (8 * uk) := mul_le_mul_of_nonneg_right hS₂1 (by positivity)
    linarith
  have hh₃e : h₃ ≤ S₃ + uk := by
    have : S₃ * (8 * uk) ≤ 1 / 8748 * (8 * uk) := mul_le_mul_of_nonneg_right hS₃1 (by positivity)
    linarith
  -- the lower end
  obtain ⟨a₁, ha₁, hfa₁⟩ := mulFloor_err hc18 hl₁ (w + 8) (mul_nonneg (by norm_num) hl₁0)
  obtain ⟨a₃, ha₃, hfa₃⟩ := mulFloor_err hc8 hl₃ (w + 8) (mul_nonneg (by norm_num) hl₃0)
  obtain ⟨p, hp, hfp⟩ := addFloor_err ha₁ ha₃ (w + 8) (add_nonneg hfa₁.nonneg hfa₃.nonneg)
  obtain ⟨m, hm, hcm⟩ := addCeiling_err hh₂ ht (w + 8) (add_nonneg hh₂0 htv0.le)
  obtain ⟨m2, hm2, hcm2⟩ := mulCeiling_err hc2 hm (w + 8)
    (mul_nonneg (by norm_num) ((add_nonneg hh₂0 htv0.le).trans hcm.ge))
  obtain ⟨lo, hlo', hlo1, hlo2⟩ := subFloor_abs hp hm2 (w + 8)
  have ea₁ : 18 * l₁ ≤ a₁ + 2 * 2 * uk := hfa₁.ge_of_le (by linarith)
  have ea₃ : 8 * l₃ ≤ a₃ + 2 * 2 * uk := hfa₃.ge_of_le (by linarith)
  have ea₁' : a₁ ≤ 18 * l₁ := hfa₁.le
  have ea₃' : a₃ ≤ 8 * l₃ := hfa₃.le
  have ep : a₁ + a₃ ≤ p + 2 * 2 * uk := hfp.ge_of_le (by linarith)
  have ep' : p ≤ a₁ + a₃ := hfp.le
  have em : m ≤ h₂ + tv + 2 * 2 * uk := hcm.le_of_le (by linarith)
  have em' : h₂ + tv ≤ m := hcm.ge
  have em2 : m2 ≤ 2 * m + 2 * 2 * uk := hcm2.le_of_le (by linarith)
  have em2' : 2 * m ≤ m2 := hcm2.ge
  have hlo2' : p - m2 ≤ lo + 2 * |p - m2| * uk := hlo2
  have habs1 : |p - m2| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hr1 : 2 * |p - m2| * uk ≤ 2 * 2 * uk := by
    have := mul_le_mul_of_nonneg_right habs1 huk0.le; linarith
  -- the upper end
  obtain ⟨m₁, hm₁, hcm₁⟩ := addCeiling_err hh₁ ht (w + 8) (add_nonneg hh₁0 htv0.le)
  obtain ⟨b₁, hb₁, hcb₁⟩ := mulCeiling_err hc18 hm₁ (w + 8)
    (mul_nonneg (by norm_num) ((add_nonneg hh₁0 htv0.le).trans hcm₁.ge))
  obtain ⟨m₃, hm₃, hcm₃⟩ := addCeiling_err hh₃ ht (w + 8) (add_nonneg hh₃0 htv0.le)
  obtain ⟨b₃, hb₃, hcb₃⟩ := mulCeiling_err hc8 hm₃ (w + 8)
    (mul_nonneg (by norm_num) ((add_nonneg hh₃0 htv0.le).trans hcm₃.ge))
  obtain ⟨qq, hqq, hcq⟩ := addCeiling_err hb₁ hb₃ (w + 8)
    (add_nonneg ((mul_nonneg (by norm_num) ((add_nonneg hh₁0 htv0.le).trans hcm₁.ge)).trans hcb₁.ge)
      ((mul_nonneg (by norm_num) ((add_nonneg hh₃0 htv0.le).trans hcm₃.ge)).trans hcb₃.ge))
  obtain ⟨c, hc, hfc⟩ := mulFloor_err hc2 hl₂ (w + 8) (mul_nonneg (by norm_num) hl₂0)
  obtain ⟨hi, hhi', hhi1, hhi2⟩ := subCeiling_abs hqq hc (w + 8)
  have em₁ : m₁ ≤ h₁ + tv + 2 * 2 * uk := hcm₁.le_of_le (by linarith)
  have em₁' : h₁ + tv ≤ m₁ := hcm₁.ge
  have eb₁ : b₁ ≤ 18 * m₁ + 2 * 2 * uk := hcb₁.le_of_le (by linarith)
  have eb₁' : 18 * m₁ ≤ b₁ := hcb₁.ge
  have em₃ : m₃ ≤ h₃ + tv + 2 * 2 * uk := hcm₃.le_of_le (by linarith)
  have em₃' : h₃ + tv ≤ m₃ := hcm₃.ge
  have eb₃ : b₃ ≤ 8 * m₃ + 2 * 2 * uk := hcb₃.le_of_le (by linarith)
  have eb₃' : 8 * m₃ ≤ b₃ := hcb₃.ge
  have eq₁ : qq ≤ b₁ + b₃ + 2 * 2 * uk := hcq.le_of_le (by linarith)
  have eq₁' : b₁ + b₃ ≤ qq := hcq.ge
  have ec : 2 * l₂ ≤ c + 2 * 2 * uk := hfc.ge_of_le (by linarith)
  have ec' : c ≤ 2 * l₂ := hfc.le
  have hhi2' : hi ≤ qq - c + 2 * |qq - c| * uk := hhi2
  have habs2 : |qq - c| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hr2 : 2 * |qq - c| * uk ≤ 2 * 2 * uk := by
    have := mul_le_mul_of_nonneg_right habs2 huk0.le; linarith
  -- assemble (`ln2Bracket w` unfolds to the two terms by `rfl`)
  refine ⟨lo, hi, hlo', hhi', ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · intro hw
    have hu2 : u ≤ 1 / 4 := by
      calc u ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
        _ = 1 / 4 := by norm_num
    linarith

/-- The two `Roundable`s round the two ends; the enclosure is strict (`ln 2` is irrational). -/
theorem ln2Approx_spec (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, Rounds (ln2Approx w).1 lv ∧ Rounds (ln2Approx w).2 hv ∧
      lv < Real.log 2 ∧ Real.log 2 < hv ∧ hv - lv ≤ 8 * (1 / 2 : ℝ) ^ w ∧
      (2 ≤ w → 1 / 5 ≤ lv) := by
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid, hpos⟩ := ln2Bracket_spec w
  refine ⟨lv, hv, ?_, ?_, ?_, ?_, hwid, hpos⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo fun h => irrational_log_two.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi fun h => irrational_log_two.ne_rat r (h.trans hr)

/-- **The termination certificate**: rounding `ln 2` to precision `p` is possible from some
working precision `w₀ · 2^f` on. -/
theorem ln2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (ln2Approx (w₀ * 2 ^ f)).1 (ln2Approx (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational p mode ln2Approx irrational_log_two (by norm_num : (0 : ℝ) ≤ 8)
    (fun w hw => by
      have : NeZero w := ⟨by omega⟩
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid, -⟩ := ln2Approx_spec w
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

/-! ### The reciprocal bracket for `log₂ e` -/

/-- `log2EBracket w` encloses `1/ln 2` with width at most `80 · 2^(−w)` for `w ≥ 2`. -/
theorem log2EBracket_spec {w : ℕ} (hw : 2 ≤ w) :
    ∃ lv hv : ℝ, (log2EBracket w).1.toVal = some (lv : EReal) ∧
      (log2EBracket w).2.toVal = some (hv : EReal) ∧
      lv ≤ (Real.log 2)⁻¹ ∧ (Real.log 2)⁻¹ ≤ hv ∧ hv - lv ≤ 80 * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨a, b, ha, hb, haL, hLb, hab, hapos⟩ := ln2Bracket_spec w
  have ha5 : 1 / 5 ≤ a := hapos hw
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have hL0 : 0 < Real.log 2 := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨lv, hlv, hfl⟩ := divFloor_err toVal_one' hb hb0 (by norm_num) w
  obtain ⟨hv, hhv, hcl⟩ := divCeiling_err toVal_one' ha ha0 (by norm_num) w
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  refine ⟨lv, hv, hlv, hhv, ?_, ?_, ?_⟩
  · calc lv ≤ 1 / b := hfl.le
      _ ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hL0 hLb
      _ = (Real.log 2)⁻¹ := one_div _
  · calc (Real.log 2)⁻¹ = 1 / Real.log 2 := (one_div _).symm
      _ ≤ 1 / a := one_div_le_one_div_of_le ha0 haL
      _ ≤ hv := hcl.ge
  · have h1a : 1 / a ≤ 5 := by rw [div_le_iff₀ ha0]; linarith
    have h1b : 1 / b ≤ 3 / 2 := by rw [div_le_iff₀ hb0]; linarith
    have hprod : (1 / 5 : ℝ) * (69 / 100) ≤ a * b :=
      mul_le_mul ha5 (by linarith) (by norm_num) ha0.le
    have hdiff : 1 / a - 1 / b ≤ 60 * u := by
      rw [div_sub_div _ _ ha0.ne' hb0.ne', div_le_iff₀ (by positivity)]
      have h3 : 60 * u * ((1 / 5 : ℝ) * (69 / 100)) ≤ 60 * u * (a * b) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      linarith
    have h4 := hfl.ge
    have h5 := hcl.le
    rw [← hu] at h4 h5
    have h6 : 2 * (1 / a) * u ≤ 2 * 5 * u := by
      have := mul_le_mul_of_nonneg_right h1a hu0.le; linarith
    have h7 : 2 * (1 / b) * u ≤ 2 * (3 / 2) * u := by
      have := mul_le_mul_of_nonneg_right h1b hu0.le; linarith
    linarith

theorem log2EApprox_spec {w : ℕ} (hw : 2 ≤ w) :
    ∃ lv hv : ℝ, Rounds (log2EApprox w).1 lv ∧ Rounds (log2EApprox w).2 hv ∧
      lv < (Real.log 2)⁻¹ ∧ (Real.log 2)⁻¹ < hv ∧ hv - lv ≤ 80 * (1 / 2 : ℝ) ^ w := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lv, hv, hlv, hhv, hlo, hhi, hwid⟩ := log2EBracket_spec hw
  have hirr : Irrational (Real.log 2)⁻¹ := irrational_log_two.inv
  refine ⟨lv, hv, ?_, ?_, ?_, ?_, hwid⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlv)
    rw [fval_of_toVal_coe hlv] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhv)
    rw [fval_of_toVal_coe hhv] at hR
    exact hR
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hlv
    exact lt_of_le_of_ne hlo fun h => hirr.ne_rat r (h.symm.trans hr)
  · obtain ⟨r, hr⟩ := exists_rat_of_toVal hhv
    exact lt_of_le_of_ne hhi fun h => hirr.ne_rat r (h.trans hr)

/-- The termination certificate for `log₂ e`: `1/ln 2` is irrational. -/
theorem log2EApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (log2EApprox (w₀ * 2 ^ f)).1 (log2EApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode log2EApprox irrational_log_two.inv
    (fun w => 80 * (1 / 2 : ℝ) ^ w)
    (by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (80 : ℝ)
      rwa [mul_zero] at this)
    2
    (fun w hw => by
      obtain ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩ := log2EApprox_spec hw
      exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, hwid⟩) w₀ hw₀

end Azurite.AzFloat
