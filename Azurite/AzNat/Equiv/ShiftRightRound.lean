/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.IsMultipleOfPow2
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TestBit
import Azurite.AzNat.ShiftRightRound
import Azurite.Rounding.NatDivPow

namespace Azurite
open RoundingTarget

/-- The value component of `AzNat.shiftRightRound` (ignoring the ordering tag).
Agrees with the original shift-and-round logic. -/
theorem AzNat.shiftRightRound_fst (n : AzNat) (mode : RoundingMode) (sh : Nat) :
    (n.shiftRightRound mode sh).1 =
      match mode with
      | .Floor | .Down => n.shiftRight sh
      | .Ceiling | .Up =>
        if n.isMultipleOfPow2 sh then n.shiftRight sh
        else (n.shiftRight sh).addUInt64 1
      | .Nearest =>
        if sh = 0 then n
        else if n.testBit (sh - 1) then
          if n.isMultipleOfPow2 (sh - 1) then
            let shifted := n.shiftRight sh
            if shifted.isOdd then shifted.addUInt64 1 else shifted
          else
            (n.shiftRight sh).addUInt64 1
        else
          n.shiftRight sh := by
  unfold AzNat.shiftRightRound
  cases mode <;> simp only [] <;> split_ifs <;> rfl

/-- **Correctness of `shiftRightRound`.**

For any rounding mode and shift amount, the limb-level `shiftRightRound` on `AzNat`
agrees with the abstract `round` of `n.toNat / 2^sh` against the rounding target
`natBotSet ⊆ EReal`. -/
theorem AzNat.toNat_shiftRightRound (n : AzNat) (mode : RoundingMode) (sh : Nat) :
    (((n.shiftRightRound mode sh).1).toNat : EReal) =
      (round natBotSet mode ((n.toNat : ℝ) / ((2 : ℝ) ^ sh))).val := by
  set x : ℝ := (n.toNat : ℝ) / ((2 : ℝ) ^ sh) with hx_def
  have hx_nonneg : 0 ≤ x := nat_div_pow_nonneg n.toNat sh
  have hfloor_x : ⌊x⌋₊ = n.toNat / 2 ^ sh := floor_nat_div_pow n.toNat sh
  -- The round-down value always matches `shiftRight`.
  have hfloor_side : ((n.shiftRight sh).toNat : EReal) =
      (roundFloor natBotSet x).val := by
    rw [roundFloor_natBotSet_nonneg x hx_nonneg, AzNat.toNat_shiftRight, ← hfloor_x]
    push_cast; rfl
  -- The ceiling value: conditional on divisibility.
  have hceil_side_of_dvd (h : 2 ^ sh ∣ n.toNat) :
      ((n.shiftRight sh).toNat : EReal) = (roundCeiling natBotSet x).val := by
    rw [roundCeiling_natBotSet, AzNat.toNat_shiftRight]
    rw [ceil_nat_div_pow_of_dvd n.toNat sh h]
    push_cast; rfl
  have hceil_side_of_not_dvd (h : ¬ 2 ^ sh ∣ n.toNat) :
      (((n.shiftRight sh).addUInt64 1).toNat : EReal) =
        (roundCeiling natBotSet x).val := by
    rw [roundCeiling_natBotSet, AzNat.toNat_addUInt64, AzNat.toNat_shiftRight]
    rw [ceil_nat_div_pow_of_not_dvd n.toNat sh h]
    have h1 : ((1 : UInt64).toNat : ℕ) = 1 := rfl
    rw [h1]
    push_cast; rfl
  rw [AzNat.shiftRightRound_fst]
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
    rw [isMultipleOfPow2_eq]
    by_cases h : 2 ^ sh ∣ n.toNat
    · simp [h, hceil_side_of_dvd h]
    · simp [h, hceil_side_of_not_dvd h]
  | .Up =>
    rw [show round natBotSet RoundingMode.Up x =
      (if 0 ≤ x then roundCeiling natBotSet x else roundFloor natBotSet x) from rfl]
    rw [ite_eq_left hx_nonneg]
    rw [isMultipleOfPow2_eq]
    by_cases h : 2 ^ sh ∣ n.toNat
    · simp [h, hceil_side_of_dvd h]
    · simp [h, hceil_side_of_not_dvd h]
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
    set q := n.toNat / 2 ^ sh with hq_def
    have hF_val : F.val = ((q : ℝ) : EReal) := by
      rw [hF_def, roundFloor_natBotSet_nonneg x hx_nonneg, hfloor_x]
    have hF_nat : natBotToNat F = q := natBotToNat_eq_of_nat_val q F hF_val
    -- Split on whether 2^sh divides n.toNat.
    by_cases hdvd : 2 ^ sh ∣ n.toNat
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
      have hLHS_q : ((if sh = 0 then n
          else if n.testBit (sh - 1) then
              if n.isMultipleOfPow2 (sh - 1) then
                let shifted := n.shiftRight sh
                if shifted.isOdd then shifted.addUInt64 1 else shifted
              else (n.shiftRight sh).addUInt64 1
          else n.shiftRight sh).toNat : EReal) = ((q : ℝ) : EReal) := by
        by_cases hsh0 : sh = 0
        · subst hsh0
          rw [ite_eq_left rfl]
          have hq_n : q = n.toNat := by simp [hq_def]
          rw [hq_n]; push_cast; rfl
        · rw [ite_eq_right hsh0]
          have hsh_pos : 0 < sh := Nat.pos_of_ne_zero hsh0
          -- testBit (sh-1) of n.toNat is false since 2^sh ∣ n.toNat and sh-1 < sh.
          have hbit_false : n.testBit (sh - 1) = false := by
            rw [AzNat.testBit_eq_toNat_testBit]
            obtain ⟨k, hk⟩ := hdvd
            rw [hk, show 2 ^ sh * k = 2 ^ sh * k + 0 from by ring]
            rw [Nat.testBit_two_pow_mul_add k (Nat.two_pow_pos sh) (sh - 1)]
            simp [show sh - 1 < sh from by omega]
          have hcond_false : ¬ (n.testBit (sh - 1) = true) := by
            rw [hbit_false]; exact Bool.false_ne_true
          rw [ite_eq_right hcond_false]
          rw [AzNat.toNat_shiftRight]
          push_cast; rfl
      rw [hLHS_q]
    · -- 2^sh ∤ n.toNat: sh > 0, and ⌈x⌉₊ = q + 1.
      have hsh_pos : 0 < sh := by
        rcases Nat.eq_zero_or_pos sh with h | h
        · subst h
          exfalso; apply hdvd
          show (2 ^ 0 : ℕ) ∣ n.toNat
          rw [pow_zero]; exact one_dvd _
        · exact h
      have hsh_ne : sh ≠ 0 := Nat.pos_iff_ne_zero.mp hsh_pos
      rw [ite_eq_right hsh_ne]
      -- Arithmetic setup.
      set r := n.toNat % 2 ^ sh with hr_def
      have hr_bound : r < 2 ^ sh := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hr_pos : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hdvd
        · exact h
      have hn_decomp : n.toNat = q * 2 ^ sh + r := nat_eq_mul_pow_add_mod n.toNat sh
      have h_two_pow : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
        conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
        rw [Nat.pow_succ]
      have hr_testBit : r.testBit (sh - 1) = n.toNat.testBit (sh - 1) := by
        rw [hr_def, Nat.testBit_mod_two_pow]
        simp [show sh - 1 < sh from by omega]
      have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
      -- Real-valued x = q + r/2^sh.
      have hx_eq : x = (q : ℝ) + (r : ℝ) / ((2 : ℝ) ^ sh) := by
        rw [hx_def]
        have hn_real : (n.toNat : ℝ) = (q : ℝ) * ((2 : ℝ) ^ sh) + (r : ℝ) := by
          rw [hn_decomp]; push_cast; ring
        rw [hn_real]; field_simp
      -- C.val = q + 1 since ⌈x⌉₊ = q + 1.
      have hceil : ⌈x⌉₊ = q + 1 := ceil_nat_div_pow_of_not_dvd n.toNat sh hdvd
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
      -- Split on testBit (sh-1) of n.toNat.
      rw [AzNat.testBit_eq_toNat_testBit]
      by_cases hbit : n.toNat.testBit (sh - 1) = true
      · -- testBit = true: r ≥ 2^(sh-1).
        rw [ite_eq_left hbit]
        have hr_bit : r.testBit (sh - 1) = true := hr_testBit ▸ hbit
        have hr_ge : 2 ^ (sh - 1) ≤ r :=
          (testBit_top_true_iff_half_le r sh hsh_pos hr_bound).mp hr_bit
        by_cases hmult : 2 ^ (sh - 1) ∣ n.toNat
        · -- r = 2^(sh-1): tie, tiebreak decides.
          have hmult_bool : n.isMultipleOfPow2 (sh - 1) = true := by
            rw [AzNat.isMultipleOfPow2_eq]; exact decide_eq_true hmult
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
          -- LHS: shifted.isOdd decides between q and q+1.
          by_cases hodd : Odd (n.shiftRight sh).toNat
          · -- q odd ⇒ LHS = q + 1.
            have hq_odd : Odd q := by rw [AzNat.toNat_shiftRight] at hodd; exact hodd
            have hq_not_even : ¬ Even q := Nat.not_even_iff_odd.mpr hq_odd
            have hisOdd_true : (n.shiftRight sh).isOdd = true := by
              rw [AzNat.isOdd_iff, AzNat.toNat_shiftRight]; exact hq_odd
            rw [ite_eq_left hisOdd_true]
            rw [AzNat.toNat_addUInt64, AzNat.toNat_shiftRight]
            show ((q + (1 : UInt64).toNat : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q + (1 : UInt64).toNat : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            have hq1_even : Even (q + 1) := Odd.add_one hq_odd
            rw [ite_eq_right hq_not_even, ite_eq_left hq1_even, hC_val]
            rw [show (1 : UInt64).toNat = 1 from rfl]
            push_cast; ring_nf
          · -- q even ⇒ LHS = q.
            have hq_even : Even q := by
              rw [Nat.not_odd_iff_even, AzNat.toNat_shiftRight] at hodd; exact hodd
            have hisOdd_false : ¬ ((n.shiftRight sh).isOdd = true) := by
              rw [AzNat.isOdd_iff, AzNat.toNat_shiftRight, Nat.not_odd_iff_even]
              exact hq_even
            rw [ite_eq_right hisOdd_false]
            rw [AzNat.toNat_shiftRight]
            show ((q : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            rw [ite_eq_left hq_even, hF_val]
            push_cast; rfl
        · -- r > 2^(sh-1): dC < dF, returns C.
          have hmult_cond_false : ¬ (n.isMultipleOfPow2 (sh - 1) = true) := by
            rw [AzNat.isMultipleOfPow2_eq]
            intro heq
            exact hmult (of_decide_eq_true heq)
          rw [ite_eq_right hmult_cond_false]
          -- r > 2^(sh-1).
          have hr_gt : 2 ^ (sh - 1) < r := by
            rcases lt_or_eq_of_le hr_ge with h | h
            · exact h
            · exfalso; apply hmult
              have hn_eq : n.toNat = q * 2 ^ sh + 2 ^ (sh - 1) := by
                rw [hn_decomp, ← h]
              rw [hn_eq]
              have h2dvd : 2 ^ (sh - 1) ∣ 2 ^ sh := ⟨2, h_two_pow⟩
              exact Nat.dvd_add (h2dvd.mul_left q) (dvd_refl _)
          have hdC_lt_real : ((q : ℝ) + 1 - x < x - q) := hdC_cmp_lt_iff.mpr hr_gt
          have hdC_lt : C.val - (x : EReal) < (x : EReal) - F.val :=
            hdC_lt_dF_iff.mpr hdC_lt_real
          rw [show compare ((x : EReal) - F.val) (C.val - (x : EReal)) = .gt from
                compare_gt_iff_gt.mpr hdC_lt]
          rw [AzNat.toNat_addUInt64, AzNat.toNat_shiftRight, hC_val]
          show (((n.toNat / 2 ^ sh + (1 : UInt64).toNat : ℕ) : ℕ) : EReal) =
            (((q + 1 : ℕ) : ℝ) : EReal)
          rw [show (1 : UInt64).toNat = 1 from rfl]
          push_cast; rfl
      · -- testBit = false: r < 2^(sh-1), dF < dC, returns F.
        rw [ite_eq_right hbit]
        have hbit_false : n.toNat.testBit (sh - 1) = false := by
          cases h : n.toNat.testBit (sh - 1)
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
        rw [AzNat.toNat_shiftRight, hF_val]
        push_cast; rfl

/-! ### Ordering tag correctness

The second component of `AzNat.shiftRightRound` records whether the rounded value is
less than, equal to, or greater than the true real value `n.toNat / 2^sh`. -/

/-- The ordering component of `AzNat.shiftRightRound`, expressed case-by-case.
Mirrors `AzNat.shiftRightRound_fst` — together these recover the original match
form of `shiftRightRound` after the `AzNat × Ordering` refactor. -/
theorem AzNat.shiftRightRound_snd (n : AzNat) (mode : RoundingMode) (sh : Nat) :
    (n.shiftRightRound mode sh).2 =
      match mode with
      | .Floor | .Down => if n.isMultipleOfPow2 sh then .eq else .lt
      | .Ceiling | .Up => if n.isMultipleOfPow2 sh then .eq else .gt
      | .Nearest =>
        if sh = 0 then .eq
        else if n.testBit (sh - 1) then
          if n.isMultipleOfPow2 (sh - 1) then
            if (n.shiftRight sh).isOdd then .gt else .lt
          else
            .gt
        else
          if n.isMultipleOfPow2 sh then .eq else .lt := by
  unfold AzNat.shiftRightRound
  cases mode <;> simp only [] <;> split_ifs <;> rfl

/-- Bridge between the integer-scaled `Nat` compare and the real-valued compare with
division. -/
private lemma AzNat.compare_nat_mul_pow_eq_compare_real_div (a b sh : ℕ) :
    compare (a * 2 ^ sh) b = compare ((a : ℝ)) ((b : ℝ) / 2 ^ sh) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
  rcases lt_trichotomy (a * 2 ^ sh) b with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    refine (compare_lt_iff_lt.mpr ?_).symm
    rw [lt_div_iff₀ h2]; exact_mod_cast h
  · rw [compare_eq_iff_eq.mpr h]
    refine (compare_eq_iff_eq.mpr ?_).symm
    rw [eq_div_iff (ne_of_gt h2)]; exact_mod_cast h
  · rw [compare_gt_iff_gt.mpr h]
    refine (compare_gt_iff_gt.mpr ?_).symm
    rw [div_lt_iff₀ h2]; exact_mod_cast h

/-- When we return `n.shiftRight sh`, the scaled-back comparison is `.eq` when
`n` is divisible by `2^sh` and `.lt` otherwise. -/
theorem AzNat.compare_shiftRight_mul (n : AzNat) (sh : Nat) :
    compare ((n.shiftRight sh).toNat * 2 ^ sh) n.toNat =
      (if n.isMultipleOfPow2 sh = true then Ordering.eq else Ordering.lt) := by
  rw [AzNat.toNat_shiftRight]
  have h2pow : 0 < 2 ^ sh := Nat.two_pow_pos _
  have hu_decomp : n.toNat / 2 ^ sh * 2 ^ sh + n.toNat % 2 ^ sh = n.toNat :=
    Nat.div_add_mod' n.toNat (2 ^ sh)
  have hmult_iff : n.isMultipleOfPow2 sh = true ↔ n.toNat % 2 ^ sh = 0 := by
    rw [AzNat.isMultipleOfPow2_eq, decide_eq_true_eq]
    refine ⟨fun ⟨k, hk⟩ => ?_, Nat.dvd_of_mod_eq_zero⟩
    rw [hk]; exact Nat.mul_mod_right _ _
  by_cases hm : n.isMultipleOfPow2 sh = true
  · rw [ite_eq_left hm]
    have hr0 : n.toNat % 2 ^ sh = 0 := hmult_iff.mp hm
    have heq : n.toNat / 2 ^ sh * 2 ^ sh = n.toNat := by omega
    rw [heq]
    show compareOfLessAndEq n.toNat n.toNat = Ordering.eq
    simp [compareOfLessAndEq]
  · rw [ite_eq_right hm]
    have hr_ne : n.toNat % 2 ^ sh ≠ 0 := fun h => hm (hmult_iff.mpr h)
    have hr_pos : 0 < n.toNat % 2 ^ sh := Nat.pos_of_ne_zero hr_ne
    have hlt : n.toNat / 2 ^ sh * 2 ^ sh < n.toNat := by omega
    show compareOfLessAndEq _ n.toNat = Ordering.lt
    rw [compareOfLessAndEq, ite_eq_left hlt]

/-- When we return `(n.shiftRight sh).addUInt64 1`, the scaled-back comparison is
always `.gt` (note `AzNat` is unbounded, so no overflow side-condition is needed —
in contrast to the `UInt64` analogue). -/
theorem AzNat.compare_shiftRight_addUInt64_one_mul (n : AzNat) (sh : Nat) :
    compare (((n.shiftRight sh).addUInt64 1).toNat * 2 ^ sh) n.toNat = Ordering.gt := by
  rw [AzNat.toNat_addUInt64, AzNat.toNat_shiftRight, show (1 : UInt64).toNat = 1 from rfl]
  have h2pow : 0 < 2 ^ sh := Nat.two_pow_pos _
  have hu_decomp : n.toNat / 2 ^ sh * 2 ^ sh + n.toNat % 2 ^ sh = n.toNat :=
    Nat.div_add_mod' n.toNat (2 ^ sh)
  have hr_lt : n.toNat % 2 ^ sh < 2 ^ sh := Nat.mod_lt _ h2pow
  have hgt : n.toNat < (n.toNat / 2 ^ sh + 1) * 2 ^ sh := by
    have h1 : (n.toNat / 2 ^ sh + 1) * 2 ^ sh =
        n.toNat / 2 ^ sh * 2 ^ sh + 2 ^ sh := by ring
    omega
  show compareOfLessAndEq _ n.toNat = Ordering.gt
  rw [compareOfLessAndEq, ite_eq_right (Nat.not_lt.mpr (Nat.le_of_lt hgt)),
      ite_eq_right (Nat.ne_of_gt hgt)]

/-- When `n.testBit (sh - 1) = true` with `sh > 0`, `n` is not a multiple of `2^sh`. -/
private theorem AzNat.not_isMultipleOfPow2_of_testBit {n : AzNat} {sh : Nat}
    (hsh : 0 < sh) (h : n.testBit (sh - 1) = true) :
    ¬ n.isMultipleOfPow2 sh = true := by
  intro hm
  rw [AzNat.isMultipleOfPow2_eq, decide_eq_true_eq] at hm
  obtain ⟨k, hk⟩ := hm
  rw [AzNat.testBit_eq_toNat_testBit] at h
  rw [hk, show 2 ^ sh * k = 2 ^ sh * k + 0 from by ring] at h
  rw [Nat.testBit_two_pow_mul_add k (Nat.two_pow_pos sh) (sh - 1)] at h
  simp [show sh - 1 < sh from by omega] at h

/-- **Ordering tag correctness for `AzNat.shiftRightRound`.**

The ordering in `(n.shiftRightRound mode sh).2` records the relation between the
rounded value and the true real value `n.toNat / 2^sh`. -/
theorem AzNat.snd_shiftRightRound (n : AzNat) (mode : RoundingMode) (sh : Nat) :
    (n.shiftRightRound mode sh).2 =
      compare (((n.shiftRightRound mode sh).1.toNat : ℕ) : ℝ)
        ((n.toNat : ℝ) / 2 ^ sh) := by
  rw [← AzNat.compare_nat_mul_pow_eq_compare_real_div,
      AzNat.shiftRightRound_snd, AzNat.shiftRightRound_fst]
  match mode with
  | .Floor =>
    simp only []
    rw [AzNat.compare_shiftRight_mul]
  | .Down =>
    simp only []
    rw [AzNat.compare_shiftRight_mul]
  | .Ceiling =>
    simp only []
    by_cases hm : n.isMultipleOfPow2 sh = true
    · rw [ite_eq_left hm, ite_eq_left hm, AzNat.compare_shiftRight_mul, ite_eq_left hm]
    · rw [ite_eq_right hm, ite_eq_right hm]
      have hsh_pos : 0 < sh := by
        rcases Nat.eq_zero_or_pos sh with hsh0 | hsh0
        · subst hsh0
          rw [AzNat.isMultipleOfPow2_eq, decide_eq_true_eq, pow_zero] at hm
          exact absurd (one_dvd _) hm
        · exact hsh0
      rw [AzNat.compare_shiftRight_addUInt64_one_mul n sh]
  | .Up =>
    simp only []
    by_cases hm : n.isMultipleOfPow2 sh = true
    · rw [ite_eq_left hm, ite_eq_left hm, AzNat.compare_shiftRight_mul, ite_eq_left hm]
    · rw [ite_eq_right hm, ite_eq_right hm]
      have hsh_pos : 0 < sh := by
        rcases Nat.eq_zero_or_pos sh with hsh0 | hsh0
        · subst hsh0
          rw [AzNat.isMultipleOfPow2_eq, decide_eq_true_eq, pow_zero] at hm
          exact absurd (one_dvd _) hm
        · exact hsh0
      rw [AzNat.compare_shiftRight_addUInt64_one_mul n sh]
  | .Nearest =>
    simp only []
    by_cases hsh0 : sh = 0
    · subst hsh0
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [pow_zero, Nat.mul_one]
      show Ordering.eq = compareOfLessAndEq n.toNat n.toNat
      simp [compareOfLessAndEq]
    · rw [ite_eq_right hsh0, ite_eq_right hsh0]
      have hsh_pos : 0 < sh := Nat.pos_of_ne_zero hsh0
      by_cases htb : n.testBit (sh - 1) = true
      · rw [ite_eq_left htb, ite_eq_left htb]
        have hnot_mult : ¬ n.isMultipleOfPow2 sh = true :=
          AzNat.not_isMultipleOfPow2_of_testBit hsh_pos htb
        by_cases hm1 : n.isMultipleOfPow2 (sh - 1) = true
        · rw [ite_eq_left hm1, ite_eq_left hm1]
          by_cases hodd : (n.shiftRight sh).isOdd = true
          · rw [ite_eq_left hodd, ite_eq_left hodd,
              AzNat.compare_shiftRight_addUInt64_one_mul n sh]
          · rw [ite_eq_right hodd, ite_eq_right hodd, AzNat.compare_shiftRight_mul, ite_eq_right hnot_mult]
        · rw [ite_eq_right hm1, ite_eq_right hm1,
            AzNat.compare_shiftRight_addUInt64_one_mul n sh]
      · rw [ite_eq_right htb, ite_eq_right htb, AzNat.compare_shiftRight_mul]

end Azurite
