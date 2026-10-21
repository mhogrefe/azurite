/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Int
import Azurite.Rounding.IntNearest
import Azurite.Rounding.SciPrecision

/-!
# The integers representable at a binary precision, as a rounding target

`intPrecisionSet p` is the set of integers with at most `p` significant bits: the integers of
`precisionSet 2 p`.  Rounding a real to it in one step is what "round to an integer
representable at precision `p`" means: `10.5` rounded to nearest at `2` bits is `12`, the nearer
of the two-bit integers `8` and `12` — not `10` (the nearest integer) rounded again to `12`.

* Below `2^(p−1)` in magnitude every integer is representable, so the floor and ceiling are the
  integer floor and ceiling (`isGreatest_intPrecision_small`, `isLeast_intPrecision_small`) and
  rounding is integer rounding (`val_round_intPrecision_small`: `round intSet`, ties to even).
* From `2^(p−1)` on, the `p`-bit floor and ceiling are integers, so rounding is `p`-bit rounding
  (`val_round_intPrecision_large`: `round (precisionSet 2 p)`).

The tiebreak (`ipTiebreak`) is the parity rule of `precisionSet` at the local scale, floored at
`1`: on consecutive integers below `2^(p−1)` it picks the even integer, as `intSet` does, and
at or above `2^(p−1)` it is `precTiebreak`.
-/

namespace Azurite.RoundingTarget

open Int

instance : Fact (1 < 2) := ⟨by norm_num⟩

/-- The integers with at most `p` significant bits. -/
def intPrecisionSet (p : ℕ) : Set EReal :=
  {e | e ∈ precisionSet 2 p ∧ ∃ n : ℤ, ((n : ℝ) : EReal) = e}

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem int_mem_precisionSet (n : ℤ) (hn : |n| < 2 ^ p) :
    ((n : ℝ) : EReal) ∈ precisionSet 2 p := by
  rcases eq_or_ne n 0 with rfl | h0
  · exact Or.inl (by simp)
  · exact Or.inr ⟨n, 0, h0, by exact_mod_cast hn, by simp⟩

omit [NeZero p] in
theorem int_mem_intPrecisionSet (n : ℤ) (hn : |n| < 2 ^ p) :
    ((n : ℝ) : EReal) ∈ intPrecisionSet p :=
  ⟨int_mem_precisionSet n hn, n, rfl⟩

omit [NeZero p] in
theorem two_zpow_pred_eq (hp : 1 ≤ p) :
    (2 : ℝ) ^ ((p : ℤ) - 1) = ((2 ^ (p - 1) : ℤ) : ℝ) := by
  rw [show (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  norm_cast

omit [NeZero p] in
theorem two_pow_pred_lt (hp : 1 ≤ p) : (2 : ℤ) ^ (p - 1) < 2 ^ p :=
  pow_lt_pow_right₀ (by norm_num) (by omega)

/-! ### Floor and ceiling below `2^(p−1)` -/

theorem isGreatest_intPrecision_small (x : ℝ) (hx : |x| < (2 : ℝ) ^ ((p : ℤ) - 1)) :
    IsGreatest {s | s ∈ intPrecisionSet p ∧ s ≤ (x : EReal)} ((⌊x⌋ : ℝ) : EReal) := by
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [two_zpow_pred_eq hp] at hx
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  have hbound : |⌊x⌋| < 2 ^ p := by
    have hlo : -(2 ^ (p - 1) : ℤ) ≤ ⌊x⌋ :=
      Int.le_floor.mpr (by push_cast at h1 ⊢; linarith)
    have hhi : ⌊x⌋ < 2 ^ (p - 1) := Int.floor_lt.mpr h2
    have := two_pow_pred_lt (p := p) hp
    rw [abs_lt]; constructor <;> linarith
  refine ⟨⟨int_mem_intPrecisionSet ⌊x⌋ hbound, by exact_mod_cast Int.floor_le x⟩, ?_⟩
  rintro s ⟨⟨-, z, rfl⟩, hz⟩
  have : (z : ℝ) ≤ x := by exact_mod_cast hz
  exact_mod_cast Int.le_floor.mpr this

theorem isLeast_intPrecision_small (x : ℝ) (hx : |x| < (2 : ℝ) ^ ((p : ℤ) - 1)) :
    IsLeast {s | s ∈ intPrecisionSet p ∧ (x : EReal) ≤ s} ((⌈x⌉ : ℝ) : EReal) := by
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [two_zpow_pred_eq hp] at hx
  obtain ⟨h1, h2⟩ := abs_lt.mp hx
  have hbound : |⌈x⌉| < 2 ^ p := by
    have hlo : -(2 ^ (p - 1) : ℤ) < ⌈x⌉ := Int.lt_ceil.mpr (by push_cast at h1 ⊢; linarith)
    have hhi : ⌈x⌉ ≤ 2 ^ (p - 1) := Int.ceil_le.mpr h2.le
    have := two_pow_pred_lt (p := p) hp
    rw [abs_lt]; constructor <;> linarith
  refine ⟨⟨int_mem_intPrecisionSet ⌈x⌉ hbound, by exact_mod_cast Int.le_ceil x⟩, ?_⟩
  rintro s ⟨⟨-, z, rfl⟩, hz⟩
  have : x ≤ (z : ℝ) := by exact_mod_cast hz
  exact_mod_cast Int.ceil_le.mpr this

/-! ### Floor and ceiling from `2^(p−1)` on -/

omit [NeZero p] in
/-- From `2^(p−1)` on, the local scale of `precisionSet 2 p` is a natural power of two. -/
theorem precScale_eq_pow (x : ℝ) (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    ∃ k : ℕ, precScale 2 p x = (2 : ℝ) ^ k := by
  have hx0 : 0 < |x| := lt_of_lt_of_le (zpow_pos (by norm_num) _) hx
  have hlog : (p : ℤ) - 1 ≤ Int.log 2 |x| :=
    (Int.zpow_le_iff_le_log (by norm_num) hx0).mp (by simpa using hx)
  refine ⟨(Int.log 2 |x| - p + 1).toNat, ?_⟩
  unfold precScale
  rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  norm_num

omit [NeZero p] in
theorem ne_zero_of_two_zpow_le {x : ℝ} (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) : x ≠ 0 := by
  intro h
  rw [h, abs_zero] at hx
  exact absurd hx (not_le.mpr (zpow_pos (by norm_num) _))

theorem isGreatest_intPrecision_large (x : ℝ) (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    IsGreatest {s | s ∈ intPrecisionSet p ∧ s ≤ (x : EReal)}
      ((((⌊x / precScale 2 p x⌋ : ℝ) * precScale 2 p x : ℝ) : EReal)) := by
  obtain ⟨hmem, hge⟩ := isGreatest_precision (b := 2) (p := p) x (ne_zero_of_two_zpow_le hx)
  obtain ⟨k, hk⟩ := precScale_eq_pow x hx
  refine ⟨⟨⟨hmem.1, ⌊x / precScale 2 p x⌋ * 2 ^ k, ?_⟩, hmem.2⟩, ?_⟩
  · rw [hk]; push_cast; rfl
  · rintro s ⟨⟨hs, -⟩, hsx⟩
    exact hge ⟨hs, hsx⟩

theorem isLeast_intPrecision_large (x : ℝ) (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    IsLeast {s | s ∈ intPrecisionSet p ∧ (x : EReal) ≤ s}
      ((((⌈x / precScale 2 p x⌉ : ℝ) * precScale 2 p x : ℝ) : EReal)) := by
  obtain ⟨hmem, hle⟩ := isLeast_precision (b := 2) (p := p) x (ne_zero_of_two_zpow_le hx)
  obtain ⟨k, hk⟩ := precScale_eq_pow x hx
  refine ⟨⟨⟨hmem.1, ⌈x / precScale 2 p x⌉ * 2 ^ k, ?_⟩, hmem.2⟩, ?_⟩
  · rw [hk]; push_cast; rfl
  · rintro s ⟨⟨hs, -⟩, hsx⟩
    exact hle ⟨hs, hsx⟩

/-! ### The tiebreak and the instance -/

/-- The real value of an element. -/
noncomputable def ipToReal (a : ↥(intPrecisionSet p)) : ℝ :=
  precToReal (⟨a.val, a.2.1⟩ : ↥(precisionSet 2 p))

omit [NeZero p] in
theorem ipToReal_spec (a : ↥(intPrecisionSet p)) : ((ipToReal a : ℝ) : EReal) = a.val :=
  precToReal_spec _

omit [NeZero p] in
theorem ipToReal_eq_of_val {a : ↥(intPrecisionSet p)} {r : ℝ}
    (h : ((r : ℝ) : EReal) = a.val) :
    ipToReal a = r :=
  precToReal_eq_of_val h

/-- The scale of the parity rule: the local scale of the candidate nearer `0`, but at least `1`
(so that below `2^(p−1)` the parity is that of the integers themselves). -/
noncomputable def ipScale (a c : ↥(intPrecisionSet p)) : ℝ :=
  max (precScale 2 p (min |ipToReal a| |ipToReal c|)) 1

/-- The tiebreak: `precTiebreak`'s parity rule at the scale `ipScale`. -/
noncomputable def ipTiebreak (a c : ↥(intPrecisionSet p)) : ↥(intPrecisionSet p) :=
  if Even ⌊|ipToReal a| / ipScale a c⌋ ∧ ¬ Even ⌊|ipToReal c| / ipScale a c⌋ then a
  else if Even ⌊|ipToReal c| / ipScale a c⌋ ∧ ¬ Even ⌊|ipToReal a| / ipScale a c⌋ then c
  else if |ipToReal a| < |ipToReal c| then a
  else if |ipToReal c| < |ipToReal a| then c
  else a

omit [NeZero p] in
theorem ipTiebreak_mem (a c : ↥(intPrecisionSet p)) :
    ipTiebreak a c = a ∨ ipTiebreak a c = c := by
  unfold ipTiebreak
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

noncomputable instance intPrecisionRoundingTarget : RoundingTarget (intPrecisionSet p) where
  existsLeastGE x := by
    rcases lt_or_ge |x| ((2 : ℝ) ^ ((p : ℤ) - 1)) with h | h
    · exact ⟨_, isLeast_intPrecision_small x h⟩
    · exact ⟨_, isLeast_intPrecision_large x h⟩
  existsGreatestLE x := by
    rcases lt_or_ge |x| ((2 : ℝ) ^ ((p : ℤ) - 1)) with h | h
    · exact ⟨_, isGreatest_intPrecision_small x h⟩
    · exact ⟨_, isGreatest_intPrecision_large x h⟩
  tiebreak := ipTiebreak
  tiebreak_mem := ipTiebreak_mem

/-! ### Rounding below `2^(p−1)`: integer rounding -/

theorem val_roundFloor_intPrecision_small (x : ℝ) (hx : |x| < (2 : ℝ) ^ ((p : ℤ) - 1)) :
    (roundFloor (intPrecisionSet p) x).val = ((⌊x⌋ : ℝ) : EReal) :=
  (isGreatest_roundFloor _ x).unique (isGreatest_intPrecision_small x hx)

theorem val_roundCeiling_intPrecision_small (x : ℝ) (hx : |x| < (2 : ℝ) ^ ((p : ℤ) - 1)) :
    (roundCeiling (intPrecisionSet p) x).val = ((⌈x⌉ : ℝ) : EReal) :=
  (isLeast_roundCeiling _ x).unique (isLeast_intPrecision_small x hx)

/-- Below `2^(p−1)`, `ipScale` is `1`. -/
theorem ipScale_eq_one (a c : ↥(intPrecisionSet p))
    (h : min |ipToReal a| |ipToReal c| < (2 : ℝ) ^ ((p : ℤ) - 1)) : ipScale a c = 1 := by
  unfold ipScale
  apply max_eq_right
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hlog : Int.log 2 (min |ipToReal a| |ipToReal c|) ≤ (p : ℤ) - 1 := by
    rcases eq_or_ne (min |ipToReal a| |ipToReal c|) 0 with h0 | h0
    · rw [h0, Int.log_zero_right]; omega
    · have hpos : 0 < min |ipToReal a| |ipToReal c| :=
        lt_of_le_of_ne (le_min (abs_nonneg _) (abs_nonneg _)) h0.symm
      exact ((Int.lt_zpow_iff_log_lt (by norm_num) hpos).mp (by simpa using h)).le
  unfold precScale
  rw [abs_of_nonneg (le_min (abs_nonneg _) (abs_nonneg _))]
  calc ((2 : ℕ) : ℝ) ^ (Int.log 2 (min |ipToReal a| |ipToReal c|) - p + 1)
      ≤ ((2 : ℕ) : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 := zpow_zero _

/-- On a tie between consecutive integers below `2^(p−1)`, the tiebreak picks the even one. -/
theorem ipTiebreak_consecutive (a c : ↥(intPrecisionSet p)) (n : ℤ)
    (ha : a.val = ((n : ℝ) : EReal)) (hc : c.val = (((n + 1 : ℤ) : ℝ) : EReal))
    (hn : (n : ℝ) + 1 / 2 ∈
      Set.Ioo (-(2 : ℝ) ^ ((p : ℤ) - 1)) ((2 : ℝ) ^ ((p : ℤ) - 1))) :
    (ipTiebreak a c).val
      = if Even n then ((n : ℝ) : EReal) else (((n + 1 : ℤ) : ℝ) : EReal) := by
  have har : ipToReal a = n := ipToReal_eq_of_val ha.symm
  have hcr : ipToReal c = ((n + 1 : ℤ) : ℝ) := ipToReal_eq_of_val hc.symm
  have hscale : ipScale a c = 1 := by
    apply ipScale_eq_one
    rw [har, hcr]
    rcases le_or_gt 0 n with hn0 | hn0
    · calc min |(n : ℝ)| |((n + 1 : ℤ) : ℝ)| ≤ |(n : ℝ)| := min_le_left _ _
        _ = n := abs_of_nonneg (by exact_mod_cast hn0)
        _ < (2 : ℝ) ^ ((p : ℤ) - 1) := by linarith [hn.2]
    · calc min |(n : ℝ)| |((n + 1 : ℤ) : ℝ)| ≤ |((n + 1 : ℤ) : ℝ)| := min_le_right _ _
        _ = -((n : ℝ) + 1) := by
          rw [abs_of_nonpos (by push_cast; exact_mod_cast (show n + 1 ≤ 0 by omega))]; push_cast
          ring
        _ < (2 : ℝ) ^ ((p : ℤ) - 1) := by linarith [hn.1]
  have hfa : ⌊|ipToReal a| / ipScale a c⌋ = |n| := by
    rw [hscale, div_one, har, ← Int.cast_abs, Int.floor_intCast]
  have hfc : ⌊|ipToReal c| / ipScale a c⌋ = |n + 1| := by
    rw [hscale, div_one, hcr, ← Int.cast_abs, Int.floor_intCast]
  have hev : Even |n| ↔ Even n := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_even
  have hev' : Even |n + 1| ↔ Even (n + 1) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_even
  unfold ipTiebreak
  rw [hfa, hfc]
  by_cases he : Even n
  · rw [ite_eq_left ⟨hev.mpr he, fun h => (Int.even_add_one.mp (hev'.mp h)) he⟩, ha,
      ite_eq_left he]
  · rw [ite_eq_right (fun h => he (hev.mp h.1)),
      ite_eq_left ⟨hev'.mpr (Int.even_add_one.mpr he), fun h => he (hev.mp h)⟩, hc,
      ite_eq_right he]

/-- `intTiebreak` on consecutive integers picks the even one. -/
theorem intTiebreak_consecutive (a c : ↥intSet) (n : ℤ)
    (ha : a.val = ((n : ℝ) : EReal)) (hc : c.val = (((n + 1 : ℤ) : ℝ) : EReal)) :
    (intTiebreak a c).val
      = if Even n then ((n : ℝ) : EReal) else (((n + 1 : ℤ) : ℝ) : EReal) := by
  have hia : toInt a = n := toInt_eq_of_val ha.symm
  have hic : toInt c = n + 1 := toInt_eq_of_val hc.symm
  unfold intTiebreak
  rw [hia, hic]
  by_cases he : Even n
  · rw [ite_eq_left ⟨he, fun h => (Int.even_add_one.mp h) he⟩, ha, ite_eq_left he]
  · rw [ite_eq_right (fun h => he h.1), ite_eq_left ⟨Int.even_add_one.mpr he, he⟩, hc,
      ite_eq_right he]

/-- Below `2^(p−1)`, rounding to `intPrecisionSet p` is integer rounding. -/
theorem val_round_intPrecision_small (mode : RoundingMode) (x : ℝ)
    (hx : |x| < (2 : ℝ) ^ ((p : ℤ) - 1)) :
    (round (intPrecisionSet p) mode x).val = (round intSet mode x).val := by
  have hF := val_roundFloor_intPrecision_small x hx
  have hC := val_roundCeiling_intPrecision_small x hx
  have hFi := val_roundFloor_intSet x
  have hCi := val_roundCeiling_intSet x
  cases mode with
  | Floor => exact hF.trans hFi.symm
  | Ceiling => exact hC.trans hCi.symm
  | Down =>
    show (if 0 ≤ x then roundFloor _ x else roundCeiling _ x).val
      = (if 0 ≤ x then roundFloor intSet x else roundCeiling intSet x).val
    split_ifs
    · exact hF.trans hFi.symm
    · exact hC.trans hCi.symm
  | Up =>
    show (if 0 ≤ x then roundCeiling _ x else roundFloor _ x).val
      = (if 0 ≤ x then roundCeiling intSet x else roundFloor intSet x).val
    split_ifs
    · exact hC.trans hCi.symm
    · exact hF.trans hFi.symm
  | Nearest =>
    show (let F := roundFloor (intPrecisionSet p) x
          let C := roundCeiling (intPrecisionSet p) x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
      = (let F := roundFloor intSet x
          let C := roundCeiling intSet x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
    simp only []
    rw [hF, hC, hFi, hCi]
    rcases h : compare (((x : ℝ) : EReal) - ((⌊x⌋ : ℝ) : EReal))
        (((⌈x⌉ : ℝ) : EReal) - ((x : ℝ) : EReal)) with _ | _ | _
    · exact hF.trans hFi.symm
    · -- a tie
      rw [← EReal.coe_sub, ← EReal.coe_sub, compare_coe_coe, compare_eq_iff_eq] at h
      show (tiebreak (roundFloor (intPrecisionSet p) x) (roundCeiling (intPrecisionSet p) x)).val
        = (tiebreak (roundFloor intSet x) (roundCeiling intSet x)).val
      rcases eq_or_ne ⌊x⌋ ⌈x⌉ with heq | hne
      · have h1 : ∀ a : ↥(intPrecisionSet p), a = roundFloor (intPrecisionSet p) x ∨
            a = roundCeiling (intPrecisionSet p) x → a.val = ((⌊x⌋ : ℝ) : EReal) := by
          rintro a (rfl | rfl)
          · exact hF
          · rw [hC, heq]
        have h2 : ∀ a : ↥intSet, a = roundFloor intSet x ∨ a = roundCeiling intSet x →
            a.val = ((⌊x⌋ : ℝ) : EReal) := by
          rintro a (rfl | rfl)
          · exact hFi
          · rw [hCi, heq]
        rw [h1 _ (tiebreak_mem _ _), h2 _ (tiebreak_mem _ _)]
      · have hc1 : ⌈x⌉ = ⌊x⌋ + 1 :=
          le_antisymm (Int.ceil_le_floor_add_one x)
            (Int.add_one_le_iff.mpr (lt_of_le_of_ne (Int.floor_le_ceil x) hne))
        have hhalf : x = ⌊x⌋ + 1 / 2 := by
          rw [hc1] at h; push_cast at h; linarith
        have hmem : (⌊x⌋ : ℝ) + 1 / 2 ∈
            Set.Ioo (-(2 : ℝ) ^ ((p : ℤ) - 1)) ((2 : ℝ) ^ ((p : ℤ) - 1)) := by
          rw [← hhalf]; exact abs_lt.mp hx
        rw [hc1] at hC hCi
        show (ipTiebreak (roundFloor (intPrecisionSet p) x)
            (roundCeiling (intPrecisionSet p) x)).val
          = (intTiebreak (roundFloor intSet x) (roundCeiling intSet x)).val
        rw [ipTiebreak_consecutive _ _ ⌊x⌋ hF hC hmem,
          intTiebreak_consecutive _ _ ⌊x⌋ hFi hCi]
    · exact hC.trans hCi.symm

/-! ### Rounding from `2^(p−1)` on: `p`-bit rounding -/

theorem val_roundFloor_intPrecision_large (x : ℝ) (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    (roundFloor (intPrecisionSet p) x).val = (roundFloor (precisionSet 2 p) x).val := by
  rw [val_roundFloor_precision x (ne_zero_of_two_zpow_le hx)]
  exact (isGreatest_roundFloor _ x).unique (isGreatest_intPrecision_large x hx)

theorem val_roundCeiling_intPrecision_large (x : ℝ) (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    (roundCeiling (intPrecisionSet p) x).val = (roundCeiling (precisionSet 2 p) x).val := by
  rw [val_roundCeiling_precision x (ne_zero_of_two_zpow_le hx)]
  exact (isLeast_roundCeiling _ x).unique (isLeast_intPrecision_large x hx)

omit [NeZero p] in
/-- From `2^(p−1)` on, `ipScale` is the local scale. -/
theorem ipScale_eq_precScale (a c : ↥(intPrecisionSet p))
    (h : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ min |ipToReal a| |ipToReal c|) :
    ipScale a c = precScale 2 p (min |ipToReal a| |ipToReal c|) := by
  unfold ipScale
  apply max_eq_left
  have hpos : 0 < min |ipToReal a| |ipToReal c| := lt_of_lt_of_le (zpow_pos (by norm_num) _) h
  have hlog : (p : ℤ) - 1 ≤ Int.log 2 (min |ipToReal a| |ipToReal c|) :=
    (Int.zpow_le_iff_le_log (by norm_num) hpos).mp (by simpa using h)
  unfold precScale
  rw [abs_of_nonneg (le_min (abs_nonneg _) (abs_nonneg _))]
  calc (1 : ℝ) = ((2 : ℕ) : ℝ) ^ (0 : ℤ) := (zpow_zero _).symm
    _ ≤ ((2 : ℕ) : ℝ) ^ (Int.log 2 (min |ipToReal a| |ipToReal c|) - p + 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- From `2^(p−1)` on, the floor and ceiling have magnitude at least `2^(p−1)`. -/
theorem two_zpow_le_floor_ceil (x : ℝ) (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |ipToReal (roundFloor (intPrecisionSet p) x)| ∧
      (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |ipToReal (roundCeiling (intPrecisionSet p) x)| := by
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hF := isGreatest_roundFloor (intPrecisionSet p) x
  have hC := isLeast_roundCeiling (intPrecisionSet p) x
  have hFx : ipToReal (roundFloor (intPrecisionSet p) x) ≤ x := by
    have := hF.1.2; rw [← ipToReal_spec] at this; exact_mod_cast this
  have hxC : x ≤ ipToReal (roundCeiling (intPrecisionSet p) x) := by
    have := hC.1.2; rw [← ipToReal_spec] at this; exact_mod_cast this
  have hmemP : (((2 : ℝ) ^ ((p : ℤ) - 1) : ℝ) : EReal) ∈ intPrecisionSet p := by
    have := int_mem_intPrecisionSet (p := p) (2 ^ (p - 1))
      (by rw [abs_of_nonneg (by positivity)]; exact two_pow_pred_lt hp)
    rwa [two_zpow_pred_eq hp]
  have hmemN : (((-(2 : ℝ) ^ ((p : ℤ) - 1)) : ℝ) : EReal) ∈ intPrecisionSet p := by
    have := int_mem_intPrecisionSet (p := p) (-(2 ^ (p - 1)))
      (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact two_pow_pred_lt hp)
    rw [two_zpow_pred_eq hp]
    push_cast at this ⊢
    exact this
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx
    have hFlo : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ ipToReal (roundFloor (intPrecisionSet p) x) := by
      have := hF.2 ⟨hmemP, EReal.coe_le_coe_iff.mpr hx⟩
      rw [← ipToReal_spec] at this
      exact EReal.coe_le_coe_iff.mp this
    constructor
    · rw [abs_of_nonneg (le_trans (zpow_pos (by norm_num) _).le hFlo)]; exact hFlo
    · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg hx0] at hx
    have hChi : ipToReal (roundCeiling (intPrecisionSet p) x) ≤ -(2 : ℝ) ^ ((p : ℤ) - 1) := by
      have := hC.2 ⟨hmemN,
        EReal.coe_le_coe_iff.mpr (show x ≤ -(2 : ℝ) ^ ((p : ℤ) - 1) by linarith)⟩
      rw [← ipToReal_spec] at this
      exact EReal.coe_le_coe_iff.mp this
    constructor
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) ((p : ℤ) - 1)])]
      linarith

/-- From `2^(p−1)` on, rounding to `intPrecisionSet p` is rounding to `precisionSet 2 p`. -/
theorem val_round_intPrecision_large (mode : RoundingMode) (x : ℝ)
    (hx : (2 : ℝ) ^ ((p : ℤ) - 1) ≤ |x|) :
    (round (intPrecisionSet p) mode x).val = (round (precisionSet 2 p) mode x).val := by
  have hF := val_roundFloor_intPrecision_large x hx
  have hC := val_roundCeiling_intPrecision_large x hx
  cases mode with
  | Floor => exact hF
  | Ceiling => exact hC
  | Down =>
    show (if 0 ≤ x then roundFloor _ x else roundCeiling _ x).val
      = (if 0 ≤ x then roundFloor (precisionSet 2 p) x else roundCeiling (precisionSet 2 p) x).val
    split_ifs
    · exact hF
    · exact hC
  | Up =>
    show (if 0 ≤ x then roundCeiling _ x else roundFloor _ x).val
      = (if 0 ≤ x then roundCeiling (precisionSet 2 p) x else roundFloor (precisionSet 2 p) x).val
    split_ifs
    · exact hC
    · exact hF
  | Nearest =>
    show (let F := roundFloor (intPrecisionSet p) x
          let C := roundCeiling (intPrecisionSet p) x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
      = (let F := roundFloor (precisionSet 2 p) x
          let C := roundCeiling (precisionSet 2 p) x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
    simp only []
    rw [hF, hC]
    rcases h : compare (((x : ℝ) : EReal) - (roundFloor (precisionSet 2 p) x).val)
        ((roundCeiling (precisionSet 2 p) x).val - ((x : ℝ) : EReal)) with _ | _ | _
    · exact hF
    · -- a tie: both tiebreaks are the parity rule at the local scale
      show (ipTiebreak (roundFloor (intPrecisionSet p) x) (roundCeiling (intPrecisionSet p) x)).val
        = (precTiebreak (roundFloor (precisionSet 2 p) x)
            (roundCeiling (precisionSet 2 p) x)).val
      set F := roundFloor (intPrecisionSet p) x with hF_def
      set C := roundCeiling (intPrecisionSet p) x with hC_def
      set F' := roundFloor (precisionSet 2 p) x with hF'_def
      set C' := roundCeiling (precisionSet 2 p) x with hC'_def
      have hFr : ipToReal F = precToReal F' :=
        ipToReal_eq_of_val ((precToReal_spec F').trans hF.symm)
      have hCr : ipToReal C = precToReal C' :=
        ipToReal_eq_of_val ((precToReal_spec C').trans hC.symm)
      obtain ⟨h1, h2⟩ := two_zpow_le_floor_ceil x hx
      have hscale := ipScale_eq_precScale F C (le_min h1 h2)
      unfold ipTiebreak precTiebreak
      rw [hscale, hFr, hCr]
      split_ifs <;> first | exact hF | exact hC
    · exact hC

end Azurite.RoundingTarget
