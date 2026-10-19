/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2Bracket
import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzNat.Equiv.AtanhSplit
import Azurite.AzNat.Equiv.Pow
import Azurite.AzRat.Equiv.Add
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.Sub
import Azurite.Transcendental.Exp

/-!
# Equivalence: the bracket of `ln 2`

`ln2Bracket w = (lo, hi)` are exact rationals with `lo ≤ ln 2 ≤ hi` (`ln2Bracket_mem`, from
`log_two_mem_Icc`), `hi − lo ≤ 2^(−w)` (`ln2Bracket_width`), and `lo < ln 2` since `ln 2` is
irrational (`lo_lt_log_two`, Hermite's theorem via `irrational_log_two`).  The two `Roundable`s
of `ln2Approx w` round `lo`, `hi` (`ln2Approx_spec`).  Since `ln 2` is not a rounding boundary
(`log_two_not_boundary`) and the brackets shrink to it, rounding becomes possible at some
working precision `w₀ · 2^f` (`ln2Approx_isSome_exists`) — the termination certificate of the
constant.
-/

namespace Azurite.AzFloat

open Finset BZ

theorem toRat_ofAzNatPair (r : AzNat × AzNat) :
    AzRat.toRat (ofAzNatPair r) = (r.1.toNat : ℚ) / r.2.toNat := by
  rw [ofAzNatPair, AzRat.toRat_ofAzNats]

theorem toRat_atanhRat {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ((AzRat.toRat (atanhRat q N) : ℚ) : ℝ) = ∑ k ∈ range N, atanhTerm q k := by
  rw [atanhRat, toRat_ofAzNatPair]
  push_cast
  exact AzNat.atanhNumDen_eq hq N

theorem toRat_atanhTermRat (q N : ℕ) :
    ((AzRat.toRat (atanhTermRat q N) : ℚ) : ℝ) = atanhTerm q N := by
  rw [atanhTermRat, AzRat.toRat_ofAzNats, AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat,
    AzNat.toNat_ofNat, AzNat.toNat_ofNat, atanhTerm]
  push_cast
  ring

theorem toRat_ratNat (n : ℕ) : ((AzRat.toRat (ratNat n) : ℚ) : ℝ) = n := by
  rw [ratNat, AzRat.toRat_ofAzNats, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  push_cast
  ring

theorem toRat_fourThirds : ((AzRat.toRat fourThirds : ℚ) : ℝ) = 4 / 3 := by
  rw [fourThirds, AzRat.toRat_ofAzNats, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
  push_cast
  ring

/-- The lower end of the bracket. -/
theorem ln2Bracket_fst (w : ℕ) :
    ((AzRat.toRat (ln2Bracket w).1 : ℚ) : ℝ)
      = 18 * ∑ k ∈ range (ln2N₁ w), atanhTerm 26 k
        - 2 * (∑ k ∈ range (ln2N₂ w), atanhTerm 4801 k + 4 / 3 * atanhTerm 4801 (ln2N₂ w))
        + 8 * ∑ k ∈ range (ln2N₃ w), atanhTerm 8749 k := by
  simp only [ln2Bracket, AzRat.toRat_sub, AzRat.toRat_add, AzRat.toRat_mul]
  push_cast
  rw [toRat_atanhRat (by norm_num), toRat_atanhRat (by norm_num), toRat_atanhRat (by norm_num),
    toRat_atanhTermRat, toRat_ratNat, toRat_ratNat, toRat_ratNat, toRat_fourThirds]
  push_cast
  ring

/-- The upper end of the bracket. -/
theorem ln2Bracket_snd (w : ℕ) :
    ((AzRat.toRat (ln2Bracket w).2 : ℚ) : ℝ)
      = 18 * (∑ k ∈ range (ln2N₁ w), atanhTerm 26 k + 4 / 3 * atanhTerm 26 (ln2N₁ w))
        - 2 * ∑ k ∈ range (ln2N₂ w), atanhTerm 4801 k
        + 8 * (∑ k ∈ range (ln2N₃ w), atanhTerm 8749 k + 4 / 3 * atanhTerm 8749 (ln2N₃ w)) := by
  simp only [ln2Bracket, AzRat.toRat_sub, AzRat.toRat_add, AzRat.toRat_mul]
  push_cast
  rw [toRat_atanhRat (by norm_num), toRat_atanhRat (by norm_num), toRat_atanhRat (by norm_num),
    toRat_atanhTermRat, toRat_atanhTermRat, toRat_ratNat, toRat_ratNat, toRat_ratNat,
    toRat_fourThirds]
  push_cast
  ring

/-- `lo ≤ ln 2 ≤ hi`. -/
theorem ln2Bracket_mem (w : ℕ) :
    ((AzRat.toRat (ln2Bracket w).1 : ℚ) : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ ((AzRat.toRat (ln2Bracket w).2 : ℚ) : ℝ) := by
  rw [ln2Bracket_fst, ln2Bracket_snd]
  exact log_two_mem_Icc _ _ _

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
theorem ln2Bracket_width (w : ℕ) :
    ((AzRat.toRat (ln2Bracket w).2 : ℚ) : ℝ) - ((AzRat.toRat (ln2Bracket w).1 : ℚ) : ℝ)
      ≤ (1 / 2 : ℝ) ^ w := by
  rw [ln2Bracket_fst, ln2Bracket_snd]
  obtain ⟨h1, h2, h3⟩ := ln2N_spec w
  have t1 := atanhTerm_le_half_pow (by norm_num : 2 ^ 4 ≤ 26) h1
  have t2 := atanhTerm_le_half_pow (by norm_num : 2 ^ 12 ≤ 4801) h2
  have t3 := atanhTerm_le_half_pow (by norm_num : 2 ^ 13 ≤ 8749) h3
  have hp : (1 / 2 : ℝ) ^ (w + 6) = (1 / 2 : ℝ) ^ w / 64 := by rw [pow_add]; norm_num; ring
  rw [hp] at t1 t2 t3
  simp only [Nat.cast_ofNat] at t1 t2 t3
  have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) w
  linarith

/-- The two `Roundable`s round the two ends. -/
theorem ln2Approx_spec (w : ℕ) :
    Rounds (ln2Approx w).1 ((AzRat.toRat (ln2Bracket w).1 : ℚ) : ℝ) ∧
      Rounds (ln2Approx w).2 ((AzRat.toRat (ln2Bracket w).2 : ℚ) : ℝ) :=
  ⟨fun p _ mode => ofAzRatRound_eq_roundVal _ p mode,
    fun p _ mode => ofAzRatRound_eq_roundVal _ p mode⟩

/-- The lower end is strictly below `ln 2`, which is irrational. -/
theorem lo_lt_log_two (w : ℕ) : ((AzRat.toRat (ln2Bracket w).1 : ℚ) : ℝ) < Real.log 2 :=
  lt_of_le_of_ne (ln2Bracket_mem w).1 fun h => irrational_log_two ⟨_, h⟩

/-- `ln 2` is not a rounding boundary at any precision: boundaries are rational. -/
theorem log_two_not_boundary (p : ℕ) [NeZero p] :
    ((Real.log 2 : ℝ) : EReal) ∉ floatSet (p + 1) := by
  intro hB
  obtain ⟨M, k, hMk, -⟩ := boundary_repr p _ hB (Real.log_pos one_lt_two).ne'
  exact irrational_log_two ⟨M * (2 : ℚ) ^ k, by push_cast; exact hMk.symm⟩

/-- **The termination certificate**: rounding `ln 2` to precision `p` is possible from some
working precision `w₀ · 2^f` on, because the brackets shrink to the non-boundary `ln 2`. -/
theorem ln2Approx_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (ln2Approx (w₀ * 2 ^ f)).1 (ln2Approx (w₀ * 2 ^ f)).2 p
      mode).isSome = true := by
  have hv0 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hvB := log_two_not_boundary p
  obtain ⟨bm, bp, hbm, hbp, hbmv, hvbp, hgreatest, hleast, -, -⟩ :=
    adjacent_boundaries p (Real.log 2) hv0 hvB
  set D := min (Real.log 2 - bm) (bp - Real.log 2) with hD
  have hD0 : 0 < D := lt_min (by linarith) (by linarith)
  obtain ⟨f, hf⟩ := exists_pow_lt_of_lt_one hD0 (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨f, ?_⟩
  have hfw : (1 / 2 : ℝ) ^ (w₀ * 2 ^ f) ≤ (1 / 2 : ℝ) ^ f := by
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
    calc f ≤ 2 ^ f := Nat.lt_two_pow_self.le
      _ ≤ w₀ * 2 ^ f := Nat.le_mul_of_pos_left _ hw₀
  obtain ⟨hl, hh⟩ := ln2Approx_spec (w₀ * 2 ^ f)
  obtain ⟨hlo, hhi⟩ := ln2Bracket_mem (w₀ * 2 ^ f)
  have hwidth := ln2Bracket_width (w₀ * 2 ^ f)
  apply roundingPossible_isSome_of_no_boundary p mode hl hh (by linarith)
  refine no_boundary_of_dist p (Real.log 2) _ _ D hv0 hvB hlo hhi ?_ (by linarith)
  intro b hb hbne _
  rcases le_or_gt b (Real.log 2) with hble | hbgt
  · have := hgreatest b hb hble
    rw [abs_of_nonneg (by linarith)]
    calc D ≤ Real.log 2 - bm := min_le_left _ _
      _ ≤ Real.log 2 - b := by linarith
  · have := hleast b hb hbgt.le
    rw [abs_of_neg (by linarith)]
    calc D ≤ bp - Real.log 2 := min_le_right _ _
      _ ≤ -(Real.log 2 - b) := by linarith

end Azurite.AzFloat
