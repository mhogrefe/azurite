/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.Equiv.DivMod
import Azurite.UInt64.DivRound
import Azurite.Rounding.NatDivPow

namespace UInt64
open Azurite Azurite.RoundingTarget

/-- For `n > 0`, `⌊v/n⌋₊ = v / n` (Nat division) when both are nat-cast to ℝ. -/
private lemma floor_nat_div_nat (v n : ℕ) :
    ⌊(v : ℝ) / (n : ℝ)⌋₊ = v / n := by
  have h : ((n : ℝ)) = (((n : ℕ)) : ℝ) := rfl
  rw [h, Nat.floor_div_natCast, Nat.floor_natCast]

/-- Ceiling of `v/n` when `n ∣ v`: equals `v / n` (Nat division). -/
private lemma ceil_nat_div_nat_of_dvd (v n : ℕ) (hn : 0 < n) (h : n ∣ v) :
    ⌈(v : ℝ) / (n : ℝ)⌉₊ = v / n := by
  obtain ⟨q, hq⟩ := h
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have heq : (v : ℝ) / (n : ℝ) = (q : ℝ) := by
    rw [hq]; push_cast; field_simp
  rw [heq, Nat.ceil_natCast, hq, Nat.mul_div_cancel_left q hn]

/-- Ceiling of `v/n` when `n ∤ v`: equals `v / n + 1`. -/
private lemma ceil_nat_div_nat_of_not_dvd (v n : ℕ) (hn : 0 < n) (h : ¬ n ∣ v) :
    ⌈(v : ℝ) / (n : ℝ)⌉₊ = v / n + 1 := by
  set q := v / n
  set r := v % n
  have hr_pos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) h
    · exact h0
  have hr_lt : r < n := Nat.mod_lt _ hn
  have hsum : q * n + r = v := Nat.div_add_mod' v n
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_value : (v : ℝ) / (n : ℝ) = (q : ℝ) + (r : ℝ) / (n : ℝ) := by
    have h1 : (v : ℝ) = (q : ℝ) * (n : ℝ) + (r : ℝ) := by
      have h2 : ((q * n + r : ℕ) : ℝ) = (q : ℝ) * (n : ℝ) + (r : ℝ) := by push_cast; ring
      rw [← h2, hsum]
    rw [h1]; field_simp
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    rw [h_value]
    have h_rn_le_one : (r : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn_real_pos]; exact_mod_cast Nat.le_of_lt hr_lt
    push_cast; linarith
  · apply Nat.lt_ceil.mpr
    rw [h_value]
    have h_rn_pos : (0 : ℝ) < (r : ℝ) / (n : ℝ) := by
      apply div_pos
      · exact_mod_cast hr_pos
      · exact hn_real_pos
    linarith

/-- Value component of `divRound`. -/
theorem divRound_fst (x y : UInt64) (mode : RoundingMode) :
    (x.divRound y mode).1 =
      if x % y == 0 then x / y
      else
        match mode with
        | .Floor | .Down => x / y
        | .Ceiling | .Up => x / y + 1
        | .Nearest =>
          match compare (y >>> 1) (x % y) with
          | .lt => x / y + 1
          | .gt => x / y
          | .eq =>
            if (y &&& 1 == 0) && ((x / y) &&& 1 == 1) then x / y + 1
            else x / y := by
  unfold divRound divMod
  cases mode <;> simp only [] <;> split_ifs <;>
    first | rfl | (cases compare (y >>> 1) (x % y) <;> rfl)

/-- Ordering component of `divRound`. -/
theorem divRound_snd (x y : UInt64) (mode : RoundingMode) :
    (x.divRound y mode).2 =
      if x % y == 0 then .eq
      else
        match mode with
        | .Floor | .Down => .lt
        | .Ceiling | .Up => .gt
        | .Nearest =>
          match compare (y >>> 1) (x % y) with
          | .lt => .gt
          | .gt => .lt
          | .eq =>
            if (y &&& 1 == 0) && ((x / y) &&& 1 == 1) then .gt
            else .lt := by
  unfold divRound divMod
  cases mode <;> simp only [] <;> split_ifs <;>
    first | rfl | (cases compare (y >>> 1) (x % y) <;> rfl)

/-- For nonzero divisor and nonzero remainder, `quotient + 1` does not overflow. -/
private lemma quotient_add_one_no_overflow (x y : UInt64) (hy : 0 < y.toNat)
    (hr : x.toNat % y.toNat ≠ 0) : x.toNat / y.toNat + 1 < 2 ^ 64 := by
  have hx_lt : x.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hr_pos : 0 < x.toNat % y.toNat := Nat.pos_of_ne_zero hr
  have hr_lt : x.toNat % y.toNat < y.toNat := Nat.mod_lt _ hy
  have hsum : x.toNat / y.toNat * y.toNat + x.toNat % y.toNat = x.toNat :=
    Nat.div_add_mod' x.toNat y.toNat
  have h_qmul : x.toNat / y.toNat * y.toNat < x.toNat := by omega
  have hq_lt : x.toNat / y.toNat < x.toNat := by
    have : x.toNat / y.toNat * 1 ≤ x.toNat / y.toNat * y.toNat := Nat.mul_le_mul_left _ hy
    omega
  omega

private lemma toNat_quotient_add_one (x y : UInt64) (hy : 0 < y.toNat)
    (hr : x.toNat % y.toNat ≠ 0) : ((x / y) + 1).toNat = x.toNat / y.toNat + 1 := by
  rw [_root_.UInt64.toNat_add, _root_.UInt64.toNat_div, show ((1 : UInt64).toNat = 1) from rfl]
  exact Nat.mod_eq_of_lt (quotient_add_one_no_overflow x y hy hr)

/-- `(y >>> 1).toNat = y.toNat / 2`. -/
private lemma toNat_shr_one (y : UInt64) : (y >>> 1).toNat = y.toNat / 2 := by
  rw [_root_.UInt64.toNat_shiftRight, show ((1 : UInt64).toNat = 1) from rfl,
      show ((1 : Nat) % 64 = 1) from rfl, Nat.shiftRight_eq_div_pow, pow_one]

/-- `(y &&& 1).toNat = y.toNat % 2`. -/
private lemma toNat_and_one (y : UInt64) : (y &&& 1).toNat = y.toNat % 2 := by
  rw [_root_.UInt64.toNat_and, show ((1 : UInt64).toNat = 1) from rfl,
      Nat.and_one_is_mod]

private lemma compare_uint64_lt {a b : UInt64} (h : a < b) : compare a b = .lt := by
  show (compareOfLessAndEq a b : Ordering) = .lt
  unfold compareOfLessAndEq; simp [h]

private lemma compare_uint64_gt {a b : UInt64} (h : b < a) : compare a b = .gt := by
  show (compareOfLessAndEq a b : Ordering) = .gt
  unfold compareOfLessAndEq
  rw [_root_.UInt64.lt_iff_toNat_lt] at h
  have h1 : ¬ a < b := by rw [_root_.UInt64.lt_iff_toNat_lt]; omega
  have h2 : a ≠ b := fun he => by rw [he] at h; omega
  simp [h1, h2]

private lemma compare_uint64_eq {a b : UInt64} (h : a = b) : compare a b = .eq := by
  show (compareOfLessAndEq a b : Ordering) = .eq
  unfold compareOfLessAndEq; simp [h]

/-- **Correctness of `UInt64.divRound`.**

For any rounding mode and nonzero divisor, the word-level `divRound` on `UInt64`
agrees with the abstract `round` of `x.toNat / y.toNat` against the rounding
target `natBotSet ⊆ EReal`. -/
theorem toNat_divRound (x y : UInt64) (mode : RoundingMode) (hy : 0 < y.toNat) :
    (((x.divRound y mode).1).toNat : EReal) =
      (round natBotSet mode ((x.toNat : ℝ) / (y.toNat : ℝ))).val := by
  set xn := x.toNat with hxn
  set yn := y.toNat with hyn
  set q := xn / yn with hq_def
  set r := xn % yn with hr_def
  have hr_lt : r < yn := Nat.mod_lt _ hy
  have hsum : q * yn + r = xn := Nat.div_add_mod' xn yn
  set t : ℝ := (xn : ℝ) / (yn : ℝ) with ht_def
  have hyn_real_pos : (0 : ℝ) < (yn : ℝ) := by exact_mod_cast hy
  have ht_nonneg : 0 ≤ t := by
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact le_of_lt hyn_real_pos
  have ht_decomp : t = (q : ℝ) + (r : ℝ) / (yn : ℝ) := by
    have h1 : (xn : ℝ) = (q : ℝ) * (yn : ℝ) + (r : ℝ) := by
      have h2 : ((q * yn + r : ℕ) : ℝ) = (q : ℝ) * (yn : ℝ) + (r : ℝ) := by push_cast; ring
      rw [← h2, hsum]
    rw [ht_def, h1]; field_simp
  have hfloor_t : ⌊t⌋₊ = q := floor_nat_div_nat xn yn
  set F := roundFloor natBotSet t with hF_def
  have hF_val : F.val = ((q : ℝ) : EReal) := by
    rw [hF_def, roundFloor_natBotSet_nonneg t ht_nonneg, hfloor_t]
  have hF_nat : natBotToNat F = q := natBotToNat_eq_of_nat_val q F hF_val
  have hquot_toNat : (x / y).toNat = q := by rw [_root_.UInt64.toNat_div]
  rw [divRound_fst]
  by_cases hr0 : r = 0
  · -- remainder = 0: t = q exactly.
    have hr_uint_zero : (x % y).toNat = 0 := by rw [_root_.UInt64.toNat_mod]; exact hr0
    have hr_eq_check : (x % y == 0) = true := by
      rw [beq_iff_eq]; exact _root_.UInt64.toNat_inj.mp (by rw [hr_uint_zero]; rfl)
    rw [ite_eq_left hr_eq_check]
    show ((x / y).toNat : EReal) = (round natBotSet mode t).val
    rw [hquot_toNat]
    have ht_eq_q : t = (q : ℝ) := by rw [ht_decomp, hr0]; push_cast; simp
    have hC_val : (roundCeiling natBotSet t).val = ((q : ℝ) : EReal) := by
      rw [roundCeiling_natBotSet, ht_eq_q, Nat.ceil_natCast]
    have hC_nat : natBotToNat (roundCeiling natBotSet t) = q :=
      natBotToNat_eq_of_nat_val q _ hC_val
    cases mode with
    | Floor =>
      show ((q : ℕ) : EReal) = F.val
      rw [hF_val]; push_cast; rfl
    | Ceiling =>
      show ((q : ℕ) : EReal) = (roundCeiling natBotSet t).val
      rw [hC_val]; push_cast; rfl
    | Down =>
      show ((q : ℕ) : EReal) =
        (if 0 ≤ t then roundFloor natBotSet t else roundCeiling natBotSet t).val
      rw [ite_eq_left ht_nonneg, ← hF_def, hF_val]; push_cast; rfl
    | Up =>
      show ((q : ℕ) : EReal) =
        (if 0 ≤ t then roundCeiling natBotSet t else roundFloor natBotSet t).val
      rw [ite_eq_left ht_nonneg, hC_val]; push_cast; rfl
    | Nearest =>
      show ((q : ℕ) : EReal) =
        (match compare ((t : EReal) - F.val) ((roundCeiling natBotSet t).val - (t : EReal)) with
         | .lt => F
         | .gt => roundCeiling natBotSet t
         | .eq => RoundingTarget.tiebreak F (roundCeiling natBotSet t)).val
      have hdF_eq_dC : (t : EReal) - F.val = (roundCeiling natBotSet t).val - (t : EReal) := by
        rw [hF_val, hC_val,
            show ((t : ℝ) : EReal) = (((q : ℕ) : ℝ) : EReal) from by rw [ht_eq_q]]
      rw [show compare ((t : EReal) - F.val)
              ((roundCeiling natBotSet t).val - (t : EReal)) = .eq from
            compare_eq_iff_eq.mpr hdF_eq_dC]
      show ((q : ℕ) : EReal) = (natBotTiebreak F (roundCeiling natBotSet t)).val
      unfold natBotTiebreak
      rw [hF_nat, hC_nat]
      split_ifs <;> rw [hF_val] <;> push_cast <;> rfl
  · -- remainder ≠ 0.
    have hr_uint_ne : (x % y).toNat ≠ 0 := by rw [_root_.UInt64.toNat_mod]; exact hr0
    have hr_eq_check : ¬ ((x % y == 0) = true) := by
      rw [beq_iff_eq]; intro he; apply hr_uint_ne; rw [he]; rfl
    rw [ite_eq_right hr_eq_check]
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
    have h_not_dvd : ¬ yn ∣ xn := fun hdvd => hr0 (Nat.mod_eq_zero_of_dvd hdvd)
    set C := roundCeiling natBotSet t with hC_def
    have hC_val : C.val = (((q + 1 : ℕ) : ℝ) : EReal) := by
      rw [hC_def, roundCeiling_natBotSet, ceil_nat_div_nat_of_not_dvd xn yn hy h_not_dvd]
    have hC_nat : natBotToNat C = q + 1 := natBotToNat_eq_of_nat_val (q + 1) C hC_val
    have hquot_succ_toNat : ((x / y) + 1).toNat = q + 1 :=
      toNat_quotient_add_one x y hy hr0
    -- dF and dC in real form.
    have h_real_F : t - ((q : ℕ) : ℝ) = (r : ℝ) / (yn : ℝ) := by
      rw [ht_decomp]; ring
    have hdF_real_eq : (t : EReal) - F.val = (((r : ℝ) / (yn : ℝ)) : EReal) := by
      rw [hF_val, ← EReal.coe_sub, h_real_F]
    have hyn_r_le_pre : r ≤ yn := le_of_lt hr_lt
    have h_real_C : ((q + 1 : ℕ) : ℝ) - t = ((yn - r : ℕ) : ℝ) / (yn : ℝ) := by
      rw [ht_decomp, Nat.cast_sub hyn_r_le_pre]
      have hyn_ne : (yn : ℝ) ≠ 0 := ne_of_gt hyn_real_pos
      push_cast
      field_simp
      ring
    have hdC_real_eq : C.val - (t : EReal) = ((((yn - r : ℕ) : ℝ) / (yn : ℝ)) : EReal) := by
      rw [hC_val, ← EReal.coe_sub, h_real_C]
    -- Comparison criteria via real arithmetic.
    have hyn_r_le : r ≤ yn := le_of_lt hr_lt
    have hdF_lt_dC_iff_real :
        (t : EReal) - F.val < C.val - (t : EReal) ↔ 2 * r < yn := by
      rw [hdF_real_eq, hdC_real_eq, EReal.coe_lt_coe_iff]
      have hyn_ne : (yn : ℝ) ≠ 0 := ne_of_gt hyn_real_pos
      rw [div_lt_div_iff₀ hyn_real_pos hyn_real_pos]
      push_cast [Nat.cast_sub hyn_r_le]
      constructor
      · intro h
        have h2 : (r : ℝ) < (yn : ℝ) - (r : ℝ) := by
          have h3 : (r : ℝ) * (yn : ℝ) < ((yn : ℝ) - (r : ℝ)) * (yn : ℝ) := by linarith
          exact (mul_lt_mul_iff_of_pos_right hyn_real_pos).mp h3
        have : (2 : ℝ) * r < yn := by linarith
        exact_mod_cast this
      · intro h
        have h2 : (2 : ℝ) * r < yn := by exact_mod_cast h
        have h3 : (r : ℝ) < (yn : ℝ) - (r : ℝ) := by linarith
        nlinarith
    have hdC_lt_dF_iff_real :
        C.val - (t : EReal) < (t : EReal) - F.val ↔ yn < 2 * r := by
      rw [hdF_real_eq, hdC_real_eq, EReal.coe_lt_coe_iff]
      have hyn_ne : (yn : ℝ) ≠ 0 := ne_of_gt hyn_real_pos
      rw [div_lt_div_iff₀ hyn_real_pos hyn_real_pos]
      push_cast [Nat.cast_sub hyn_r_le]
      constructor
      · intro h
        have h2 : ((yn : ℝ) - (r : ℝ)) < (r : ℝ) := by
          have h3 : ((yn : ℝ) - (r : ℝ)) * (yn : ℝ) < (r : ℝ) * (yn : ℝ) := by linarith
          exact (mul_lt_mul_iff_of_pos_right hyn_real_pos).mp h3
        have : (yn : ℝ) < 2 * (r : ℝ) := by linarith
        exact_mod_cast this
      · intro h
        have h2 : (yn : ℝ) < 2 * (r : ℝ) := by exact_mod_cast h
        have h3 : ((yn : ℝ) - (r : ℝ)) < (r : ℝ) := by linarith
        nlinarith
    cases mode with
    | Floor =>
      show ((x / y).toNat : EReal) = F.val
      rw [hquot_toNat, hF_val]; push_cast; rfl
    | Down =>
      show ((x / y).toNat : EReal) =
        (if 0 ≤ t then F else C).val
      rw [ite_eq_left ht_nonneg, hquot_toNat, hF_val]; push_cast; rfl
    | Ceiling =>
      show (((x / y) + 1).toNat : EReal) = C.val
      rw [hquot_succ_toNat, hC_val]; push_cast; rfl
    | Up =>
      show (((x / y) + 1).toNat : EReal) =
        (if 0 ≤ t then C else F).val
      rw [ite_eq_left ht_nonneg, hquot_succ_toNat, hC_val]; push_cast; rfl
    | Nearest =>
      -- Translate UInt64 comparisons to nat r/yn.
      have hhalfY_lt_iff : y >>> 1 < x % y ↔ yn < 2 * r := by
        rw [_root_.UInt64.lt_iff_toNat_lt, toNat_shr_one, _root_.UInt64.toNat_mod]
        change yn / 2 < r ↔ yn < 2 * r
        omega
      have hr_lt_imp : x % y < y >>> 1 → 2 * r < yn := by
        intro h
        rw [_root_.UInt64.lt_iff_toNat_lt, toNat_shr_one, _root_.UInt64.toNat_mod] at h
        have h' : r < yn / 2 := h
        omega
      have hyparity_iff : (y &&& 1 == 0) = true ↔ yn % 2 = 0 := by
        rw [beq_iff_eq]
        constructor
        · intro he
          have := congrArg _root_.UInt64.toNat he
          rw [toNat_and_one, show ((0 : UInt64).toNat = 0) from rfl] at this
          exact this
        · intro he
          apply _root_.UInt64.toNat_inj.mp
          rw [toNat_and_one]; exact he
      have hqparity_iff : ((x / y) &&& 1 == 1) = true ↔ q % 2 = 1 := by
        rw [beq_iff_eq]
        constructor
        · intro he
          have := congrArg _root_.UInt64.toNat he
          rw [toNat_and_one, _root_.UInt64.toNat_div, ← hq_def,
              show ((1 : UInt64).toNat = 1) from rfl] at this
          exact this
        · intro he
          apply _root_.UInt64.toNat_inj.mp
          rw [toNat_and_one, _root_.UInt64.toNat_div, ← hq_def,
              show ((1 : UInt64).toNat = 1) from rfl]
          exact he
      -- Goal LHS is now the match-chain at the value level. RHS is the round.Nearest branch.
      show ((match compare (y >>> 1) (x % y) with
             | .lt => x / y + 1
             | .gt => x / y
             | .eq =>
               if (y &&& 1 == 0) && ((x / y) &&& 1 == 1) then x / y + 1
               else x / y).toNat : EReal) =
        (match compare ((t : EReal) - F.val) (C.val - (t : EReal)) with
         | .lt => F
         | .gt => C
         | .eq => RoundingTarget.tiebreak F C).val
      by_cases h_gt : y >>> 1 < x % y
      · -- Round up.
        rw [compare_uint64_lt h_gt, hquot_succ_toNat]
        have hreal_gt : yn < 2 * r := hhalfY_lt_iff.mp h_gt
        have hdC_lt : C.val - (t : EReal) < (t : EReal) - F.val :=
          hdC_lt_dF_iff_real.mpr hreal_gt
        rw [show compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .gt from
              compare_gt_iff_gt.mpr hdC_lt]
        rw [hC_val]; push_cast; rfl
      · by_cases h_lt : x % y < y >>> 1
        · -- Round down (strict).
          rw [compare_uint64_gt h_lt, hquot_toNat]
          have hreal_lt : 2 * r < yn := hr_lt_imp h_lt
          have hdF_lt : (t : EReal) - F.val < C.val - (t : EReal) :=
            hdF_lt_dC_iff_real.mpr hreal_lt
          rw [show compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .lt from
                compare_lt_iff_lt.mpr hdF_lt]
          rw [hF_val]; push_cast; rfl
        · have h_eq : y >>> 1 = x % y := by
            rw [_root_.UInt64.lt_iff_toNat_lt, toNat_shr_one,
                _root_.UInt64.toNat_mod] at h_gt
            rw [_root_.UInt64.lt_iff_toNat_lt, toNat_shr_one,
                _root_.UInt64.toNat_mod] at h_lt
            apply _root_.UInt64.toNat_inj.mp
            rw [toNat_shr_one, _root_.UInt64.toNat_mod]
            omega
          rw [compare_uint64_eq h_eq]
          have hnot_gt : ¬ (yn < 2 * r) := fun hgt => h_gt (hhalfY_lt_iff.mpr hgt)
          -- We're at r = halfY. Sub-case on yn parity.
          have h_gt_unf : ¬ (yn / 2 < r) := by
            intro h
            apply h_gt
            rw [_root_.UInt64.lt_iff_toNat_lt, toNat_shr_one, _root_.UInt64.toNat_mod]
            exact h
          have h_lt_unf : ¬ (r < yn / 2) := by
            intro h
            apply h_lt
            rw [_root_.UInt64.lt_iff_toNat_lt, toNat_shr_one, _root_.UInt64.toNat_mod]
            exact h
          have hr_eq_half : r = yn / 2 := by omega
          by_cases hyn_par : yn % 2 = 0
          · -- yn even: 2r = yn, math is tie, alg uses parity.
            have hr_eq : 2 * r = yn := by omega
            have hdF_eq_dC : (t : EReal) - F.val = C.val - (t : EReal) := by
              rw [hdF_real_eq, hdC_real_eq]
              congr 1
              push_cast [Nat.cast_sub hyn_r_le]
              have hyn_ne : (yn : ℝ) ≠ 0 := ne_of_gt hyn_real_pos
              field_simp
              have h_real : (2 : ℝ) * (r : ℝ) = (yn : ℝ) := by exact_mod_cast hr_eq
              linarith
            rw [show compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .eq from
                  compare_eq_iff_eq.mpr hdF_eq_dC]
            show ((if (y &&& 1 == 0) && ((x / y) &&& 1 == 1) then x / y + 1 else x / y).toNat
                : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            have hyparity_true : (y &&& 1 == 0) = true := hyparity_iff.mpr hyn_par
            by_cases hq_par : q % 2 = 1
            · -- q odd: round up.
              have hqparity_true : ((x / y) &&& 1 == 1) = true := hqparity_iff.mpr hq_par
              rw [show ((y &&& 1 == 0) && ((x / y) &&& 1 == 1)) = true from by
                rw [hyparity_true, hqparity_true]; rfl]
              rw [ite_eq_left rfl, hquot_succ_toNat]
              have hq_odd : Odd q := ⟨q / 2, by omega⟩
              have hq_not_even : ¬ Even q := Nat.not_even_iff_odd.mpr hq_odd
              have hq1_even : Even (q + 1) := Odd.add_one hq_odd
              rw [ite_eq_right hq_not_even, ite_eq_left hq1_even, hC_val]; push_cast; rfl
            · -- q even: round down.
              have hq_mod : q % 2 = 0 := by omega
              have hq_even : Even q := by
                rcases Nat.even_or_odd q with he | ho
                · exact he
                · exfalso; rw [Nat.odd_iff] at ho; omega
              have hqparity_false : ¬ (((x / y) &&& 1 == 1) = true) := by
                rw [hqparity_iff]; omega
              have hqp_eq : ((x / y) &&& 1 == 1) = false := by
                cases h : ((x / y) &&& 1 == 1)
                · rfl
                · exact absurd h hqparity_false
              rw [show ((y &&& 1 == 0) && ((x / y) &&& 1 == 1)) = false from by
                rw [hqp_eq, Bool.and_false]]
              simp only [Bool.false_eq_true, ite_false]
              rw [hquot_toNat]
              rw [ite_eq_left hq_even, hF_val]; push_cast; rfl
          · -- yn odd: 2r = yn - 1 < yn, math returns F, alg returns q (y odd kills the &&).
            have hyn_odd : yn % 2 = 1 := by omega
            have hreal_lt : 2 * r < yn := by omega
            have hdF_lt : (t : EReal) - F.val < C.val - (t : EReal) :=
              hdF_lt_dC_iff_real.mpr hreal_lt
            rw [show compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .lt from
                  compare_lt_iff_lt.mpr hdF_lt]
            have hyparity_false : ¬ ((y &&& 1 == 0) = true) := by
              rw [hyparity_iff]; omega
            have hyp_eq : (y &&& 1 == 0) = false := by
              cases h : (y &&& 1 == 0)
              · rfl
              · exact absurd h hyparity_false
            rw [show ((y &&& 1 == 0) && ((x / y) &&& 1 == 1)) = false from by
              rw [hyp_eq]; rfl]
            simp only [Bool.false_eq_true, ite_false]
            rw [hquot_toNat, hF_val]; push_cast; rfl

/-! ### Ordering tag correctness

The second component of `divRound` records whether the rounded value is less than,
equal to, or greater than the true value `x.toNat / y.toNat`, viewed as a real. -/

/-- Bridge between the integer-scaled `Nat` compare and the real-valued compare with
division. Lets us prove ordering claims by Nat-arithmetic and read them off as
statements about `(n : ℝ)` vs `(m : ℝ) / (yn : ℝ)`. -/
private lemma compare_nat_mul_div_eq_compare_real_div (n m yn : ℕ) (hyn : 0 < yn) :
    compare (n * yn) m = compare ((n : ℝ)) ((m : ℝ) / (yn : ℝ)) := by
  have h2 : (0 : ℝ) < (yn : ℝ) := by exact_mod_cast hyn
  rcases lt_trichotomy (n * yn) m with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    refine (compare_lt_iff_lt.mpr ?_).symm
    rw [lt_div_iff₀ h2]; exact_mod_cast h
  · rw [compare_eq_iff_eq.mpr h]
    refine (compare_eq_iff_eq.mpr ?_).symm
    rw [eq_div_iff (ne_of_gt h2)]; exact_mod_cast h
  · rw [compare_gt_iff_gt.mpr h]
    refine (compare_gt_iff_gt.mpr ?_).symm
    rw [div_lt_iff₀ h2]; exact_mod_cast h

/-- **Ordering tag correctness for `UInt64.divRound`.**

The ordering in `(x.divRound y mode).2` records the relation between the rounded
value and the true real value `x.toNat / y.toNat`. -/
theorem snd_divRound (x y : UInt64) (mode : RoundingMode) (hy : 0 < y.toNat) :
    (x.divRound y mode).2 =
      compare (((x.divRound y mode).1.toNat : ℕ) : ℝ)
        ((x.toNat : ℝ) / (y.toNat : ℝ)) := by
  rw [← compare_nat_mul_div_eq_compare_real_div _ _ y.toNat hy,
      divRound_snd, divRound_fst]
  by_cases hr : (x % y == 0) = true
  · rw [ite_eq_left hr, ite_eq_left hr]
    have hr0 : x.toNat % y.toNat = 0 := by
      rw [beq_iff_eq] at hr
      have := congrArg _root_.UInt64.toNat hr
      rw [_root_.UInt64.toNat_mod, show ((0 : UInt64).toNat = 0) from rfl] at this
      exact this
    rw [_root_.UInt64.toNat_div]
    have heq : x.toNat / y.toNat * y.toNat = x.toNat := by
      have := Nat.div_add_mod' x.toNat y.toNat; omega
    rw [heq]
    show Ordering.eq = compareOfLessAndEq x.toNat x.toNat
    simp [compareOfLessAndEq]
  · rw [ite_eq_right hr, ite_eq_right hr]
    have hr0 : x.toNat % y.toNat ≠ 0 := by
      intro hr0
      apply hr
      rw [beq_iff_eq]
      apply _root_.UInt64.toNat_inj.mp
      rw [_root_.UInt64.toNat_mod, show ((0 : UInt64).toNat = 0) from rfl]
      exact hr0
    have hsum : x.toNat / y.toNat * y.toNat + x.toNat % y.toNat = x.toNat :=
      Nat.div_add_mod' x.toNat y.toNat
    have h_q_lt : x.toNat / y.toNat * y.toNat < x.toNat := by
      have : 0 < x.toNat % y.toNat := Nat.pos_of_ne_zero hr0; omega
    have h_q1_gt : x.toNat < (x.toNat / y.toNat + 1) * y.toNat := by
      have hr_lt : x.toNat % y.toNat < y.toNat := Nat.mod_lt _ hy
      have h1 : (x.toNat / y.toNat + 1) * y.toNat =
        x.toNat / y.toNat * y.toNat + y.toNat := by ring
      omega
    have h_compare_q : compare ((x / y).toNat * y.toNat) x.toNat = Ordering.lt := by
      rw [_root_.UInt64.toNat_div]
      show compareOfLessAndEq _ _ = Ordering.lt
      simp [compareOfLessAndEq, h_q_lt]
    have h_compare_q1 : compare (((x / y) + 1).toNat * y.toNat) x.toNat = Ordering.gt := by
      rw [toNat_quotient_add_one x y hy hr0]
      show compareOfLessAndEq _ _ = Ordering.gt
      have hnot_lt : ¬ ((x.toNat / y.toNat + 1) * y.toNat < x.toNat) :=
        Nat.not_lt.mpr (Nat.le_of_lt h_q1_gt)
      have hne : (x.toNat / y.toNat + 1) * y.toNat ≠ x.toNat := Nat.ne_of_gt h_q1_gt
      simp [compareOfLessAndEq, hnot_lt, hne]
    cases mode with
    | Floor => simp only []; exact h_compare_q.symm
    | Down => simp only []; exact h_compare_q.symm
    | Ceiling => simp only []; exact h_compare_q1.symm
    | Up => simp only []; exact h_compare_q1.symm
    | Nearest =>
      simp only []
      cases hcmp : compare (y >>> 1) (x % y) with
      | lt => exact h_compare_q1.symm
      | gt => exact h_compare_q.symm
      | eq =>
        split_ifs
        · exact h_compare_q1.symm
        · exact h_compare_q.symm

end UInt64
