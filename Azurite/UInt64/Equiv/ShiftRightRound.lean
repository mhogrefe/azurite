/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.Equiv.Basic
import Azurite.UInt64.Equiv.IsMultipleOfPow2
import Azurite.UInt64.Equiv.TestBit
import Azurite.UInt64.ShiftRightRound
import Azurite.Rounding.NatDivPow

namespace UInt64
open Azurite Azurite.RoundingTarget

/-- Correctness of `shiftRightSat`: acts as `u.toNat / 2^sh`, saturating to `0` for
shifts past the word size. -/
theorem toNat_shiftRightSat (u : UInt64) (sh : Nat) :
    (shiftRightSat u sh).toNat = u.toNat / 2 ^ sh := by
  unfold shiftRightSat
  by_cases hsh : sh < 64
  · rw [ite_eq_left hsh, _root_.UInt64.toNat_shiftRight]
    have hofNat : (_root_.UInt64.ofNat sh).toNat = sh := by
      show sh % 2 ^ 64 = sh
      exact Nat.mod_eq_of_lt (by omega)
    rw [hofNat, Nat.mod_eq_of_lt hsh, Nat.shiftRight_eq_div_pow]
  · rw [ite_eq_right hsh]
    show (0 : Nat) = u.toNat / 2 ^ sh
    push Not at hsh
    have hu_lt : u.toNat < 2 ^ sh :=
      lt_of_lt_of_le (_root_.UInt64.toNat_lt _)
        (Nat.pow_le_pow_right (by omega) hsh)
    rw [Nat.div_eq_of_lt hu_lt]

/-- For `sh ≥ 1`, `shiftRightSat u sh + 1` does not overflow, and matches
`u.toNat / 2 ^ sh + 1`. -/
theorem toNat_shiftRightSat_add_one (u : UInt64) (sh : Nat) (hsh : 0 < sh) :
    ((shiftRightSat u sh) + 1).toNat = u.toNat / 2 ^ sh + 1 := by
  rw [_root_.UInt64.toNat_add, toNat_shiftRightSat,
      show ((1 : UInt64).toNat = 1) from rfl]
  have hu_lt : u.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hbound : u.toNat / 2 ^ sh + 1 < 2 ^ 64 := by
    by_cases hsh64 : sh < 64
    · have h2 : (2 : ℕ) ^ sh ≥ 2 := by
        have h1 : (2 : ℕ) ^ 1 ≤ 2 ^ sh := Nat.pow_le_pow_right (by omega) hsh
        simpa using h1
      have h3 : u.toNat / 2 ^ sh ≤ u.toNat / 2 := Nat.div_le_div_left h2 (by omega)
      have h4 : u.toNat / 2 < 2 ^ 63 := by
        have : u.toNat < 2 ^ 64 := hu_lt
        omega
      have : u.toNat / 2 ^ sh < 2 ^ 63 := lt_of_le_of_lt h3 h4
      have h2pow : (2 : ℕ) ^ 63 + 1 ≤ 2 ^ 64 := by
        have : (2 : ℕ) ^ 63 * 2 = 2 ^ 64 := by norm_num
        omega
      omega
    · push Not at hsh64
      have hu_lt_pow : u.toNat < 2 ^ sh :=
        lt_of_lt_of_le hu_lt (Nat.pow_le_pow_right (by omega) hsh64)
      rw [Nat.div_eq_of_lt hu_lt_pow]
      omega
  exact Nat.mod_eq_of_lt hbound

/-- The value component of `shiftRightRound` (ignoring the ordering tag).
Agrees with the original shift-and-round logic: floor/down give the saturating shift,
ceil/up add `1` if not divisible, nearest rounds to even on ties. -/
theorem shiftRightRound_fst (u : UInt64) (mode : RoundingMode) (sh : Nat) :
    (u.shiftRightRound mode sh).1 =
      match mode with
      | .Floor | .Down => shiftRightSat u sh
      | .Ceiling | .Up =>
        if u.isMultipleOfPow2 sh then shiftRightSat u sh
        else shiftRightSat u sh + 1
      | .Nearest =>
        if sh = 0 then u
        else if u.testBit (sh - 1) then
          if u.isMultipleOfPow2 (sh - 1) then
            let shifted := shiftRightSat u sh
            if shifted &&& 1 == 1 then shifted + 1 else shifted
          else
            shiftRightSat u sh + 1
        else
          shiftRightSat u sh := by
  unfold shiftRightRound
  cases mode <;> simp only [] <;> split_ifs <;> rfl

/-- **Correctness of `UInt64.shiftRightRound`.**

For any rounding mode and shift amount, the word-level `shiftRightRound` on `UInt64`
agrees with the abstract `round` of `u.toNat / 2^sh` against the rounding target
`natBotSet ⊆ EReal`. -/
theorem toNat_shiftRightRound (u : UInt64) (mode : RoundingMode) (sh : Nat) :
    (((u.shiftRightRound mode sh).1).toNat : EReal) =
      (round natBotSet mode ((u.toNat : ℝ) / ((2 : ℝ) ^ sh))).val := by
  set x : ℝ := (u.toNat : ℝ) / ((2 : ℝ) ^ sh) with hx_def
  have hx_nonneg : 0 ≤ x := nat_div_pow_nonneg u.toNat sh
  have hfloor_x : ⌊x⌋₊ = u.toNat / 2 ^ sh := floor_nat_div_pow u.toNat sh
  -- The round-down value always matches `shiftRightSat`.
  have hfloor_side : ((shiftRightSat u sh).toNat : EReal) =
      (roundFloor natBotSet x).val := by
    rw [roundFloor_natBotSet_nonneg x hx_nonneg, toNat_shiftRightSat, ← hfloor_x]
    push_cast; rfl
  -- The ceiling value: conditional on divisibility.
  have hceil_side_of_dvd (h : 2 ^ sh ∣ u.toNat) :
      ((shiftRightSat u sh).toNat : EReal) = (roundCeiling natBotSet x).val := by
    rw [roundCeiling_natBotSet, toNat_shiftRightSat]
    rw [ceil_nat_div_pow_of_dvd u.toNat sh h]
    push_cast; rfl
  have hceil_side_of_not_dvd (h : ¬ 2 ^ sh ∣ u.toNat) (hsh : 0 < sh) :
      (((shiftRightSat u sh) + 1).toNat : EReal) =
        (roundCeiling natBotSet x).val := by
    rw [roundCeiling_natBotSet, toNat_shiftRightSat_add_one u sh hsh]
    rw [ceil_nat_div_pow_of_not_dvd u.toNat sh h]
    push_cast; rfl
  -- Helper: for Ceiling/Up, sh = 0 implies 2^0 = 1 divides everything.
  have hsh_pos_of_not_dvd (h : ¬ 2 ^ sh ∣ u.toNat) : 0 < sh := by
    rcases Nat.eq_zero_or_pos sh with hsh0 | hsh0
    · subst hsh0
      exfalso; apply h
      show (2 ^ 0 : ℕ) ∣ u.toNat
      rw [pow_zero]; exact one_dvd _
    · exact hsh0
  rw [shiftRightRound_fst]
  match mode with
  | .Floor =>
    rw [show round natBotSet RoundingMode.Floor x = roundFloor natBotSet x from rfl]
    exact hfloor_side
  | .Down =>
    rw [show round natBotSet RoundingMode.Down x =
      (if 0 ≤ x then roundFloor natBotSet x else roundCeiling natBotSet x) from rfl]
    rw [ite_eq_left hx_nonneg]
    exact hfloor_side
  | .Ceiling =>
    rw [show round natBotSet RoundingMode.Ceiling x = roundCeiling natBotSet x from rfl]
    by_cases h : 2 ^ sh ∣ u.toNat
    · have hb : u.isMultipleOfPow2 sh = true := (isMultipleOfPow2_iff _ _).mpr h
      rw [ite_eq_left hb]; exact hceil_side_of_dvd h
    · have hb : ¬ (u.isMultipleOfPow2 sh = true) := fun he => h ((isMultipleOfPow2_iff _ _).mp he)
      rw [ite_eq_right hb]; exact hceil_side_of_not_dvd h (hsh_pos_of_not_dvd h)
  | .Up =>
    rw [show round natBotSet RoundingMode.Up x =
      (if 0 ≤ x then roundCeiling natBotSet x else roundFloor natBotSet x) from rfl]
    rw [ite_eq_left hx_nonneg]
    by_cases h : 2 ^ sh ∣ u.toNat
    · have hb : u.isMultipleOfPow2 sh = true := (isMultipleOfPow2_iff _ _).mpr h
      rw [ite_eq_left hb]; exact hceil_side_of_dvd h
    · have hb : ¬ (u.isMultipleOfPow2 sh = true) := fun he => h ((isMultipleOfPow2_iff _ _).mp he)
      rw [ite_eq_right hb]; exact hceil_side_of_not_dvd h (hsh_pos_of_not_dvd h)
  | .Nearest =>
    -- Abbreviations for the roundFloor/roundCeiling candidates.
    set F := roundFloor natBotSet x with hF_def
    set C := roundCeiling natBotSet x with hC_def
    -- Unfold the `.Nearest` branch of `round`.
    have hRound :
        round natBotSet RoundingMode.Nearest x =
          match compare ((x : EReal) - F.val) (C.val - (x : EReal)) with
          | .lt => F
          | .gt => C
          | .eq => RoundingTarget.tiebreak F C := rfl
    rw [hRound]
    -- Key computed quantities.
    set q := u.toNat / 2 ^ sh with hq_def
    have hF_val : F.val = ((q : ℝ) : EReal) := by
      rw [hF_def, roundFloor_natBotSet_nonneg x hx_nonneg, hfloor_x]
    have hF_nat : natBotToNat F = q := natBotToNat_eq_of_nat_val q F hF_val
    -- Split on whether 2^sh divides u.toNat.
    by_cases hdvd : 2 ^ sh ∣ u.toNat
    · -- x = q exactly, so F.val = C.val and the result is tiebreak F C = F.
      have hx_eq_q : x = (q : ℝ) := by
        obtain ⟨k, hk⟩ := hdvd
        have hq_k : q = k := by
          rw [hq_def, hk]; exact Nat.mul_div_cancel_left k (Nat.two_pow_pos _)
        rw [hx_def, hk, hq_k]
        push_cast
        field_simp
      have hC_val : C.val = ((q : ℝ) : EReal) := by
        rw [hC_def, roundCeiling_natBotSet, hx_eq_q, Nat.ceil_natCast]
      have hC_nat : natBotToNat C = q := natBotToNat_eq_of_nat_val q C hC_val
      -- dF = dC = 0: neither strict inequality holds.
      have hdF_eq_dC : (x : EReal) - F.val = C.val - (x : EReal) := by
        rw [hF_val, hC_val, show ((x : ℝ) : EReal) = (((q : ℕ) : ℝ) : EReal) from by
          rw [hx_eq_q]]
      rw [show compare ((x : EReal) - F.val) (C.val - (x : EReal)) = .eq from
            compare_eq_iff_eq.mpr hdF_eq_dC]
      -- tiebreak F C returns F because F and C have the same natBotToNat.
      have htiebreak_F : RoundingTarget.tiebreak F C = F := by
        show natBotTiebreak F C = F
        unfold natBotTiebreak
        rw [hF_nat, hC_nat]
        by_cases hpar : Even q <;> simp [hpar]
      rw [htiebreak_F, hF_val]
      -- LHS computes to q (in either sh = 0 or sh > 0 branch).
      by_cases hsh0 : sh = 0
      · subst hsh0
        rw [ite_eq_left rfl]
        have hq_n : q = u.toNat := by simp [hq_def]
        rw [hq_n]; push_cast; rfl
      · rw [ite_eq_right hsh0]
        have hsh_pos : 0 < sh := Nat.pos_of_ne_zero hsh0
        -- testBit (sh-1) of u.toNat is false since 2^sh ∣ u.toNat and sh-1 < sh.
        have hbit_false : u.testBit (sh - 1) = false := by
          rw [testBit_eq_toNat_testBit]
          obtain ⟨k, hk⟩ := hdvd
          rw [hk, show 2 ^ sh * k = 2 ^ sh * k + 0 from by ring]
          rw [Nat.testBit_two_pow_mul_add k (Nat.two_pow_pos sh) (sh - 1)]
          simp [show sh - 1 < sh from by omega]
        have hcond_false : ¬ (u.testBit (sh - 1) = true) := by
          rw [hbit_false]; exact Bool.false_ne_true
        rw [ite_eq_right hcond_false]
        rw [toNat_shiftRightSat]
        push_cast; rfl
    · -- 2^sh ∤ u.toNat: sh > 0, and ⌈x⌉₊ = q + 1.
      have hsh_pos : 0 < sh := hsh_pos_of_not_dvd hdvd
      have hsh_ne : sh ≠ 0 := Nat.pos_iff_ne_zero.mp hsh_pos
      rw [ite_eq_right hsh_ne]
      -- Arithmetic setup.
      set r := u.toNat % 2 ^ sh with hr_def
      have hr_bound : r < 2 ^ sh := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hr_pos : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hdvd
        · exact h
      have hn_decomp : u.toNat = q * 2 ^ sh + r := nat_eq_mul_pow_add_mod u.toNat sh
      have h_two_pow : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
        conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
        rw [Nat.pow_succ]
      have hr_testBit : r.testBit (sh - 1) = u.toNat.testBit (sh - 1) := by
        rw [hr_def, Nat.testBit_mod_two_pow]
        simp [show sh - 1 < sh from by omega]
      have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
      -- Real-valued x = q + r/2^sh.
      have hx_eq : x = (q : ℝ) + (r : ℝ) / ((2 : ℝ) ^ sh) := by
        rw [hx_def]
        have hn_real : (u.toNat : ℝ) = (q : ℝ) * ((2 : ℝ) ^ sh) + (r : ℝ) := by
          rw [hn_decomp]; push_cast; ring
        rw [hn_real]; field_simp
      -- C.val = q + 1 since ⌈x⌉₊ = q + 1.
      have hceil : ⌈x⌉₊ = q + 1 := ceil_nat_div_pow_of_not_dvd u.toNat sh hdvd
      have hC_val : C.val = (((q + 1 : ℕ) : ℝ) : EReal) := by
        rw [hC_def, roundCeiling_natBotSet, hceil]
      have hC_nat : natBotToNat C = q + 1 := natBotToNat_eq_of_nat_val (q + 1) C hC_val
      -- dF and dC.
      have hdF_coe : (x : EReal) - F.val = (((x - q : ℝ)) : EReal) := by
        rw [hF_val, ← EReal.coe_sub]
      have hdC_coe : C.val - (x : EReal) = (((((q : ℝ) + 1) - x : ℝ)) : EReal) := by
        rw [hC_val]; push_cast; rfl
      have hdF_lt_dC_iff : ((x : EReal) - F.val < C.val - (x : EReal)) ↔
          x - q < (q : ℝ) + 1 - x := by
        rw [hdF_coe, hdC_coe, EReal.coe_lt_coe_iff]
      have hdC_lt_dF_iff : (C.val - (x : EReal) < (x : EReal) - F.val) ↔
          (q : ℝ) + 1 - x < x - q := by
        rw [hdF_coe, hdC_coe, EReal.coe_lt_coe_iff]
      -- Relate r vs 2^(sh-1) to x position.
      have h2pow_half_real : (2 : ℝ) ^ sh = 2 * 2 ^ (sh - 1) := by
        conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
        rw [pow_succ, mul_comm]
      have h2half_pos_real : (0 : ℝ) < 2 ^ (sh - 1) := pow_pos (by norm_num) _
      have hd_pos : (0 : ℝ) < 2 * 2 ^ (sh - 1) := by positivity
      have hdF_cmp_lt_iff : (x - q < (q : ℝ) + 1 - x) ↔ r < 2 ^ (sh - 1) := by
        rw [hx_eq, h2pow_half_real]
        constructor
        · intro h
          have h1 : (r : ℝ) / (2 * 2 ^ (sh - 1)) < 1 / 2 := by linarith
          have h2 : (r : ℝ) < (1 / 2) * (2 * 2 ^ (sh - 1)) :=
            (div_lt_iff₀ hd_pos).mp h1
          have hreal : (r : ℝ) < 2 ^ (sh - 1) := by linarith
          exact_mod_cast hreal
        · intro h
          have hreal : (r : ℝ) < 2 ^ (sh - 1) := by exact_mod_cast h
          have h1 : (r : ℝ) / (2 * 2 ^ (sh - 1)) < 1 / 2 := by
            rw [div_lt_iff₀ hd_pos]; linarith
          linarith
      have hdC_cmp_lt_iff : ((q : ℝ) + 1 - x < x - q) ↔ 2 ^ (sh - 1) < r := by
        rw [hx_eq, h2pow_half_real]
        constructor
        · intro h
          have h1 : (1 : ℝ) / 2 < (r : ℝ) / (2 * 2 ^ (sh - 1)) := by linarith
          have h2 : (1 / 2) * (2 * 2 ^ (sh - 1)) < (r : ℝ) :=
            (lt_div_iff₀ hd_pos).mp h1
          have hreal : ((2 : ℝ) ^ (sh - 1)) < (r : ℝ) := by linarith
          exact_mod_cast hreal
        · intro h
          have hreal : ((2 : ℝ) ^ (sh - 1)) < (r : ℝ) := by exact_mod_cast h
          have h1 : (1 : ℝ) / 2 < (r : ℝ) / (2 * 2 ^ (sh - 1)) := by
            rw [lt_div_iff₀ hd_pos]; linarith
          linarith
      -- Split on testBit (sh-1) of u.toNat.
      rw [testBit_eq_toNat_testBit]
      by_cases hbit : u.toNat.testBit (sh - 1) = true
      · -- testBit = true: r ≥ 2^(sh-1).
        rw [ite_eq_left hbit]
        have hr_bit : r.testBit (sh - 1) = true := hr_testBit ▸ hbit
        have hr_ge : 2 ^ (sh - 1) ≤ r :=
          (testBit_top_true_iff_half_le r sh hsh_pos hr_bound).mp hr_bit
        by_cases hmult : 2 ^ (sh - 1) ∣ u.toNat
        · -- r = 2^(sh-1): tie, tiebreak decides.
          have hmult_bool : u.isMultipleOfPow2 (sh - 1) = true :=
            (isMultipleOfPow2_iff _ _).mpr hmult
          rw [ite_eq_left hmult_bool]
          -- Show r = 2^(sh-1).
          have hr_dvd : 2 ^ (sh - 1) ∣ r := by
            rw [hr_def]
            have h2dvd : 2 ^ (sh - 1) ∣ 2 ^ sh := ⟨2, h_two_pow⟩
            exact (Nat.dvd_mod_iff h2dvd).mpr hmult
          have hr_eq : r = 2 ^ (sh - 1) :=
            eq_half_of_testBit_and_dvd r sh hsh_pos hr_bound hr_bit hr_dvd
          -- dF = dC (both equal 1/2 in real).
          have hdF_eq_dC_real : x - q = (q : ℝ) + 1 - x := by
            have h1 : ¬ (x - q < (q : ℝ) + 1 - x) := by rw [hdF_cmp_lt_iff]; omega
            have h2 : ¬ ((q : ℝ) + 1 - x < x - q) := by rw [hdC_cmp_lt_iff]; omega
            linarith
          have hdF_eq_dC : (x : EReal) - F.val = C.val - (x : EReal) := by
            rw [hdF_coe, hdC_coe, hdF_eq_dC_real]
          rw [show compare ((x : EReal) - F.val) (C.val - (x : EReal)) = .eq from
                compare_eq_iff_eq.mpr hdF_eq_dC]
          -- LHS: (shifted &&& 1 == 1) decides between q and q+1.
          -- `shifted &&& 1 == 1 ↔ shifted.toNat is odd ↔ q is odd`.
          have hbit0 : (shiftRightSat u sh &&& 1).toNat = q % 2 := by
            rw [_root_.UInt64.toNat_and, show ((1 : UInt64).toNat = 1) from rfl,
                Nat.and_one_is_mod, toNat_shiftRightSat]
          by_cases hqodd : q % 2 = 1
          · -- q odd ⇒ LHS = q + 1.
            have hq_odd : Odd q := ⟨q / 2, by omega⟩
            have hq_not_even : ¬ Even q := Nat.not_even_iff_odd.mpr hq_odd
            have hcheck_true : (shiftRightSat u sh &&& 1 == 1) = true := by
              rw [beq_iff_eq]
              apply _root_.UInt64.eq_of_toNat_eq
              rw [hbit0, hqodd]; rfl
            rw [ite_eq_left hcheck_true]
            rw [toNat_shiftRightSat_add_one u sh hsh_pos]
            show ((q + 1 : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q + 1 : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            have hq1_even : Even (q + 1) := Odd.add_one hq_odd
            rw [ite_eq_right hq_not_even, ite_eq_left hq1_even, hC_val]
            push_cast; rfl
          · -- q even ⇒ LHS = q.
            have hq_mod : q % 2 = 0 := by omega
            have hq_even : Even q := by
              rcases Nat.even_or_odd q with he | ho
              · exact he
              · exfalso; rw [Nat.odd_iff] at ho; omega
            have hcheck_false : ¬ ((shiftRightSat u sh &&& 1 == 1) = true) := by
              rw [beq_iff_eq]
              intro hcheck
              have := congrArg _root_.UInt64.toNat hcheck
              rw [hbit0, show ((1 : UInt64).toNat = 1) from rfl] at this
              omega
            rw [ite_eq_right hcheck_false]
            rw [toNat_shiftRightSat]
            show ((q : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            rw [ite_eq_left hq_even, hF_val]
            push_cast; rfl
        · -- r > 2^(sh-1): dC < dF, returns C.
          have hmult_cond_false : ¬ (u.isMultipleOfPow2 (sh - 1) = true) :=
            fun he => hmult ((isMultipleOfPow2_iff _ _).mp he)
          rw [ite_eq_right hmult_cond_false]
          -- r > 2^(sh-1).
          have hr_gt : 2 ^ (sh - 1) < r := by
            rcases lt_or_eq_of_le hr_ge with h | h
            · exact h
            · exfalso; apply hmult
              have hn_eq : u.toNat = q * 2 ^ sh + 2 ^ (sh - 1) := by
                rw [hn_decomp, ← h]
              rw [hn_eq]
              have h2dvd : 2 ^ (sh - 1) ∣ 2 ^ sh := ⟨2, h_two_pow⟩
              exact Nat.dvd_add (h2dvd.mul_left q) (dvd_refl _)
          have hdC_lt_real : ((q : ℝ) + 1 - x < x - q) := hdC_cmp_lt_iff.mpr hr_gt
          have hdC_lt : C.val - (x : EReal) < (x : EReal) - F.val :=
            hdC_lt_dF_iff.mpr hdC_lt_real
          rw [show compare ((x : EReal) - F.val) (C.val - (x : EReal)) = .gt from
                compare_gt_iff_gt.mpr hdC_lt]
          exact hceil_side_of_not_dvd hdvd hsh_pos
      · -- testBit = false: r < 2^(sh-1), dF < dC, returns F.
        rw [ite_eq_right hbit]
        have hbit_false : u.toNat.testBit (sh - 1) = false := by
          cases h : u.toNat.testBit (sh - 1)
          · rfl
          · exact absurd h hbit
        have hr_bit_false : r.testBit (sh - 1) = false := hr_testBit ▸ hbit_false
        have hr_lt : r < 2 ^ (sh - 1) :=
          (testBit_top_false_iff_lt_half r sh hsh_pos hr_bound).mp hr_bit_false
        have hdF_lt_real : (x - q < (q : ℝ) + 1 - x) := hdF_cmp_lt_iff.mpr hr_lt
        have hdF_lt : (x : EReal) - F.val < C.val - (x : EReal) :=
          hdF_lt_dC_iff.mpr hdF_lt_real
        rw [show compare ((x : EReal) - F.val) (C.val - (x : EReal)) = .lt from
              compare_lt_iff_lt.mpr hdF_lt]
        rw [toNat_shiftRightSat, hF_val]
        push_cast; rfl

/-! ### Ordering tag correctness

The second component of `shiftRightRound` records whether the rounded value is less
than, equal to, or greater than the true value `u.toNat / 2^sh`, viewed as a real.
This is the formulation that lifts cleanly to floating-point and ball arithmetic. -/

/-- Bridge between the integer-scaled `Nat` compare and the real-valued compare with
division. Lets us prove ordering claims by Nat-arithmetic and read them off as
statements about `(n : ℝ)` vs `(m : ℝ) / 2^sh`. -/
private lemma compare_nat_mul_pow_eq_compare_real_div (n m sh : ℕ) :
    compare (n * 2 ^ sh) m = compare ((n : ℝ)) ((m : ℝ) / 2 ^ sh) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
  rcases lt_trichotomy (n * 2 ^ sh) m with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    refine (compare_lt_iff_lt.mpr ?_).symm
    rw [lt_div_iff₀ h2]; exact_mod_cast h
  · rw [compare_eq_iff_eq.mpr h]
    refine (compare_eq_iff_eq.mpr ?_).symm
    rw [eq_div_iff (ne_of_gt h2)]; exact_mod_cast h
  · rw [compare_gt_iff_gt.mpr h]
    refine (compare_gt_iff_gt.mpr ?_).symm
    rw [div_lt_iff₀ h2]; exact_mod_cast h

/-- The ordering component of `shiftRightRound`, expressed case-by-case. Mirrors
`shiftRightRound_fst` — the pair of these lemmas recovers the original match form
of `shiftRightRound` after the `UInt64 × Ordering` refactor. -/
theorem shiftRightRound_snd (u : UInt64) (mode : RoundingMode) (sh : Nat) :
    (u.shiftRightRound mode sh).2 =
      match mode with
      | .Floor | .Down => if u.isMultipleOfPow2 sh then .eq else .lt
      | .Ceiling | .Up => if u.isMultipleOfPow2 sh then .eq else .gt
      | .Nearest =>
        if sh = 0 then .eq
        else if u.testBit (sh - 1) then
          if u.isMultipleOfPow2 (sh - 1) then
            if shiftRightSat u sh &&& 1 == 1 then .gt else .lt
          else
            .gt
        else
          if u.isMultipleOfPow2 sh then .eq else .lt := by
  unfold shiftRightRound
  cases mode <;> simp only [] <;> split_ifs <;> rfl

/-- When we return `shiftRightSat u sh`, the scaled-back comparison is `.eq` when
`u` is divisible by `2^sh` and `.lt` otherwise. -/
theorem compare_shiftRightSat_mul (u : UInt64) (sh : Nat) :
    compare ((shiftRightSat u sh).toNat * 2 ^ sh) u.toNat =
      (if u.isMultipleOfPow2 sh = true then Ordering.eq else Ordering.lt) := by
  rw [toNat_shiftRightSat]
  have h2pow : 0 < 2 ^ sh := Nat.two_pow_pos _
  have hu_decomp : u.toNat / 2 ^ sh * 2 ^ sh + u.toNat % 2 ^ sh = u.toNat :=
    Nat.div_add_mod' u.toNat (2 ^ sh)
  have hmult_iff : u.isMultipleOfPow2 sh = true ↔ u.toNat % 2 ^ sh = 0 := by
    rw [isMultipleOfPow2_iff]
    refine ⟨fun ⟨k, hk⟩ => ?_, Nat.dvd_of_mod_eq_zero⟩
    rw [hk]; exact Nat.mul_mod_right _ _
  by_cases hm : u.isMultipleOfPow2 sh = true
  · rw [ite_eq_left hm]
    have hr0 : u.toNat % 2 ^ sh = 0 := hmult_iff.mp hm
    have heq : u.toNat / 2 ^ sh * 2 ^ sh = u.toNat := by omega
    rw [heq]
    show compareOfLessAndEq u.toNat u.toNat = Ordering.eq
    simp [compareOfLessAndEq]
  · rw [ite_eq_right hm]
    have hr_ne : u.toNat % 2 ^ sh ≠ 0 := fun h => hm (hmult_iff.mpr h)
    have hr_pos : 0 < u.toNat % 2 ^ sh := Nat.pos_of_ne_zero hr_ne
    have hlt : u.toNat / 2 ^ sh * 2 ^ sh < u.toNat := by omega
    show compareOfLessAndEq _ u.toNat = Ordering.lt
    rw [compareOfLessAndEq, ite_eq_left hlt]

/-- When we return `shiftRightSat u sh + 1` (with `sh > 0`, so no overflow), the
scaled-back comparison is always `.gt`. -/
theorem compare_shiftRightSat_add_one_mul (u : UInt64) (sh : Nat) (hsh : 0 < sh) :
    compare ((shiftRightSat u sh + 1).toNat * 2 ^ sh) u.toNat = Ordering.gt := by
  rw [toNat_shiftRightSat_add_one u sh hsh]
  have h2pow : 0 < 2 ^ sh := Nat.two_pow_pos _
  have hu_decomp : u.toNat / 2 ^ sh * 2 ^ sh + u.toNat % 2 ^ sh = u.toNat :=
    Nat.div_add_mod' u.toNat (2 ^ sh)
  have hr_lt : u.toNat % 2 ^ sh < 2 ^ sh := Nat.mod_lt _ h2pow
  have hgt : u.toNat < (u.toNat / 2 ^ sh + 1) * 2 ^ sh := by
    have h1 : (u.toNat / 2 ^ sh + 1) * 2 ^ sh =
        u.toNat / 2 ^ sh * 2 ^ sh + 2 ^ sh := by ring
    omega
  show compareOfLessAndEq _ u.toNat = Ordering.gt
  rw [compareOfLessAndEq, ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt hgt)),
      ite_eq_right (Nat.ne_of_gt hgt)]

/-- When `u.testBit (sh - 1) = true` with `sh > 0`, `u` is not a multiple of `2^sh`
(bit `sh - 1` would have to be zero in a multiple of `2^sh`). -/
private theorem not_isMultipleOfPow2_of_testBit {u : UInt64} {sh : Nat}
    (hsh : 0 < sh) (h : u.testBit (sh - 1) = true) :
    ¬ u.isMultipleOfPow2 sh = true := by
  intro hm
  rw [isMultipleOfPow2_iff] at hm
  obtain ⟨k, hk⟩ := hm
  rw [testBit_eq_toNat_testBit] at h
  rw [hk, show 2 ^ sh * k = 2 ^ sh * k + 0 from by ring] at h
  rw [Nat.testBit_two_pow_mul_add k (Nat.two_pow_pos sh) (sh - 1)] at h
  simp [show sh - 1 < sh from by omega] at h

/-- **Ordering tag correctness for `shiftRightRound`.**

The ordering in `(shiftRightRound u mode sh).2` records the relation between the
rounded value and the true real value `u.toNat / 2^sh`. -/
theorem snd_shiftRightRound (u : UInt64) (mode : RoundingMode) (sh : Nat) :
    (u.shiftRightRound mode sh).2 =
      compare (((u.shiftRightRound mode sh).1.toNat : ℕ) : ℝ)
        ((u.toNat : ℝ) / 2 ^ sh) := by
  rw [← compare_nat_mul_pow_eq_compare_real_div, shiftRightRound_snd, shiftRightRound_fst]
  match mode with
  | .Floor =>
    simp only []
    rw [compare_shiftRightSat_mul]
  | .Down =>
    simp only []
    rw [compare_shiftRightSat_mul]
  | .Ceiling =>
    simp only []
    by_cases hm : u.isMultipleOfPow2 sh = true
    · rw [ite_eq_left hm, ite_eq_left hm, compare_shiftRightSat_mul, ite_eq_left hm]
    · rw [ite_eq_right hm, ite_eq_right hm]
      have hsh_pos : 0 < sh := by
        rcases Nat.eq_zero_or_pos sh with hsh0 | hsh0
        · subst hsh0
          exact absurd ((isMultipleOfPow2_iff u 0).mpr (by rw [pow_zero]; exact one_dvd _)) hm
        · exact hsh0
      rw [compare_shiftRightSat_add_one_mul u sh hsh_pos]
  | .Up =>
    simp only []
    by_cases hm : u.isMultipleOfPow2 sh = true
    · rw [ite_eq_left hm, ite_eq_left hm, compare_shiftRightSat_mul, ite_eq_left hm]
    · rw [ite_eq_right hm, ite_eq_right hm]
      have hsh_pos : 0 < sh := by
        rcases Nat.eq_zero_or_pos sh with hsh0 | hsh0
        · subst hsh0
          exact absurd ((isMultipleOfPow2_iff u 0).mpr (by rw [pow_zero]; exact one_dvd _)) hm
        · exact hsh0
      rw [compare_shiftRightSat_add_one_mul u sh hsh_pos]
  | .Nearest =>
    simp only []
    by_cases hsh0 : sh = 0
    · subst hsh0
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [pow_zero, Nat.mul_one]
      show Ordering.eq = compareOfLessAndEq u.toNat u.toNat
      simp [compareOfLessAndEq]
    · rw [ite_eq_right hsh0, ite_eq_right hsh0]
      have hsh_pos : 0 < sh := Nat.pos_of_ne_zero hsh0
      by_cases htb : u.testBit (sh - 1) = true
      · rw [ite_eq_left htb, ite_eq_left htb]
        have hnot_mult : ¬ u.isMultipleOfPow2 sh = true :=
          not_isMultipleOfPow2_of_testBit hsh_pos htb
        by_cases hm1 : u.isMultipleOfPow2 (sh - 1) = true
        · rw [ite_eq_left hm1, ite_eq_left hm1]
          by_cases hodd : (shiftRightSat u sh &&& 1 == 1) = true
          · rw [ite_eq_left hodd, ite_eq_left hodd, compare_shiftRightSat_add_one_mul u sh hsh_pos]
          · rw [ite_eq_right hodd, ite_eq_right hodd, compare_shiftRightSat_mul, ite_eq_right hnot_mult]
        · rw [ite_eq_right hm1, ite_eq_right hm1, compare_shiftRightSat_add_one_mul u sh hsh_pos]
      · rw [ite_eq_right htb, ite_eq_right htb, compare_shiftRightSat_mul]

end UInt64
