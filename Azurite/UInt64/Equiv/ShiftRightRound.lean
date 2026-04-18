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
  · rw [if_pos hsh, _root_.UInt64.toNat_shiftRight]
    have hofNat : (_root_.UInt64.ofNat sh).toNat = sh := by
      show sh % 2 ^ 64 = sh
      exact Nat.mod_eq_of_lt (by omega)
    rw [hofNat, Nat.mod_eq_of_lt hsh, Nat.shiftRight_eq_div_pow]
  · rw [if_neg hsh]
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

/-- **Correctness of `UInt64.shiftRightRound`.**

For any rounding mode and shift amount, the word-level `shiftRightRound` on `UInt64`
agrees with the abstract `round` of `u.toNat / 2^sh` against the rounding target
`natBotSet ⊆ EReal`. -/
theorem toNat_shiftRightRound (u : UInt64) (mode : RoundingMode) (sh : Nat) :
    ((u.shiftRightRound mode sh).toNat : EReal) =
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
  unfold shiftRightRound
  match mode with
  | .Floor =>
    rw [show round natBotSet RoundingMode.Floor x = roundFloor natBotSet x from rfl]
    exact hfloor_side
  | .Down =>
    rw [show round natBotSet RoundingMode.Down x =
      (if 0 ≤ x then roundFloor natBotSet x else roundCeiling natBotSet x) from rfl]
    rw [if_pos hx_nonneg]
    exact hfloor_side
  | .Ceiling =>
    rw [show round natBotSet RoundingMode.Ceiling x = roundCeiling natBotSet x from rfl]
    by_cases h : 2 ^ sh ∣ u.toNat
    · have hb : u.isMultipleOfPow2 sh = true := (isMultipleOfPow2_iff _ _).mpr h
      rw [if_pos hb]; exact hceil_side_of_dvd h
    · have hb : ¬ (u.isMultipleOfPow2 sh = true) := fun he => h ((isMultipleOfPow2_iff _ _).mp he)
      rw [if_neg hb]; exact hceil_side_of_not_dvd h (hsh_pos_of_not_dvd h)
  | .Up =>
    rw [show round natBotSet RoundingMode.Up x =
      (if 0 ≤ x then roundCeiling natBotSet x else roundFloor natBotSet x) from rfl]
    rw [if_pos hx_nonneg]
    by_cases h : 2 ^ sh ∣ u.toNat
    · have hb : u.isMultipleOfPow2 sh = true := (isMultipleOfPow2_iff _ _).mpr h
      rw [if_pos hb]; exact hceil_side_of_dvd h
    · have hb : ¬ (u.isMultipleOfPow2 sh = true) := fun he => h ((isMultipleOfPow2_iff _ _).mp he)
      rw [if_neg hb]; exact hceil_side_of_not_dvd h (hsh_pos_of_not_dvd h)
  | .Nearest =>
    -- Abbreviations for the roundFloor/roundCeiling candidates.
    set F := roundFloor natBotSet x with hF_def
    set C := roundCeiling natBotSet x with hC_def
    -- Unfold the `.Nearest` branch of `round`.
    have hRound :
        round natBotSet RoundingMode.Nearest x =
          (let dF : EReal := (x : EReal) - F.val
           let dC : EReal := C.val - (x : EReal)
           if dF < dC then F
           else if dC < dF then C
           else RoundingTarget.tiebreak F C) := rfl
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
      have hnot_lt1 : ¬ ((x : EReal) - F.val < C.val - (x : EReal)) := by
        rw [hdF_eq_dC]; exact lt_irrefl _
      have hnot_lt2 : ¬ (C.val - (x : EReal) < (x : EReal) - F.val) := by
        rw [hdF_eq_dC]; exact lt_irrefl _
      rw [if_neg hnot_lt1, if_neg hnot_lt2]
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
        rw [if_pos rfl]
        have hq_n : q = u.toNat := by simp [hq_def]
        rw [hq_n]; push_cast; rfl
      · rw [if_neg hsh0]
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
        rw [if_neg hcond_false]
        rw [toNat_shiftRightSat]
        push_cast; rfl
    · -- 2^sh ∤ u.toNat: sh > 0, and ⌈x⌉₊ = q + 1.
      have hsh_pos : 0 < sh := hsh_pos_of_not_dvd hdvd
      have hsh_ne : sh ≠ 0 := Nat.pos_iff_ne_zero.mp hsh_pos
      rw [if_neg hsh_ne]
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
        rw [if_pos hbit]
        have hr_bit : r.testBit (sh - 1) = true := hr_testBit ▸ hbit
        have hr_ge : 2 ^ (sh - 1) ≤ r :=
          (testBit_top_true_iff_half_le r sh hsh_pos hr_bound).mp hr_bit
        by_cases hmult : 2 ^ (sh - 1) ∣ u.toNat
        · -- r = 2^(sh-1): tie, tiebreak decides.
          have hmult_bool : u.isMultipleOfPow2 (sh - 1) = true :=
            (isMultipleOfPow2_iff _ _).mpr hmult
          rw [if_pos hmult_bool]
          -- Show r = 2^(sh-1).
          have hr_dvd : 2 ^ (sh - 1) ∣ r := by
            rw [hr_def]
            have h2dvd : 2 ^ (sh - 1) ∣ 2 ^ sh := ⟨2, h_two_pow⟩
            exact (Nat.dvd_mod_iff h2dvd).mpr hmult
          have hr_eq : r = 2 ^ (sh - 1) :=
            eq_half_of_testBit_and_dvd r sh hsh_pos hr_bound hr_bit hr_dvd
          -- dF = dC (both equal 1/2 in real).
          have hnot_dF_lt_dC_real : ¬ (x - q < (q : ℝ) + 1 - x) := by
            rw [hdF_cmp_lt_iff]; omega
          have hnot_dC_lt_dF_real : ¬ ((q : ℝ) + 1 - x < x - q) := by
            rw [hdC_cmp_lt_iff]; omega
          have hnot_dF_lt_dC : ¬ ((x : EReal) - F.val < C.val - (x : EReal)) :=
            fun h => hnot_dF_lt_dC_real (hdF_lt_dC_iff.mp h)
          have hnot_dC_lt_dF : ¬ (C.val - (x : EReal) < (x : EReal) - F.val) :=
            fun h => hnot_dC_lt_dF_real (hdC_lt_dF_iff.mp h)
          rw [if_neg hnot_dF_lt_dC, if_neg hnot_dC_lt_dF]
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
            rw [if_pos hcheck_true]
            rw [toNat_shiftRightSat_add_one u sh hsh_pos]
            show ((q + 1 : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q + 1 : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            have hq1_even : Even (q + 1) := Odd.add_one hq_odd
            rw [if_neg hq_not_even, if_pos hq1_even, hC_val]
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
            rw [if_neg hcheck_false]
            rw [toNat_shiftRightSat]
            show ((q : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            rw [if_pos hq_even, hF_val]
            push_cast; rfl
        · -- r > 2^(sh-1): dC < dF, returns C.
          have hmult_cond_false : ¬ (u.isMultipleOfPow2 (sh - 1) = true) :=
            fun he => hmult ((isMultipleOfPow2_iff _ _).mp he)
          rw [if_neg hmult_cond_false]
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
          have hnot_dF_lt_dC_real : ¬ (x - q < (q : ℝ) + 1 - x) := by linarith
          have hnot_dF_lt_dC : ¬ ((x : EReal) - F.val < C.val - (x : EReal)) :=
            fun h => hnot_dF_lt_dC_real (hdF_lt_dC_iff.mp h)
          have hdC_lt : C.val - (x : EReal) < (x : EReal) - F.val :=
            hdC_lt_dF_iff.mpr hdC_lt_real
          rw [if_neg hnot_dF_lt_dC, if_pos hdC_lt]
          exact hceil_side_of_not_dvd hdvd hsh_pos
      · -- testBit = false: r < 2^(sh-1), dF < dC, returns F.
        rw [if_neg hbit]
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
        rw [if_pos hdF_lt]
        rw [toNat_shiftRightSat, hF_val]
        push_cast; rfl

end UInt64
