import Azurite.AzNat.DivRound
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.Rounding.NatDivPow

namespace Azurite.AzNat
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
  apply Nat.le_antisymm
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
theorem divRound_fst (x y : AzNat) (mode : RoundingMode) :
    (x.divRound y mode).1 =
      if (x.divMod y).2.limbs.size = 0 then (x.divMod y).1
      else
        match mode with
        | .Floor | .Down => (x.divMod y).1
        | .Ceiling | .Up => (x.divMod y).1.addUInt64 1
        | .Nearest =>
          match Ord.compare (y >>> 1) (x.divMod y).2 with
          | .lt => (x.divMod y).1.addUInt64 1
          | .gt => (x.divMod y).1
          | .eq =>
            if y.isEven && (x.divMod y).1.isOdd then (x.divMod y).1.addUInt64 1
            else (x.divMod y).1 := by
  unfold divRound
  cases mode <;> simp only [] <;> split_ifs <;>
    first | rfl | (cases Ord.compare (y >>> 1) (x.divMod y).2 <;> rfl)

/-- Ordering component of `divRound`. -/
theorem divRound_snd (x y : AzNat) (mode : RoundingMode) :
    (x.divRound y mode).2 =
      if (x.divMod y).2.limbs.size = 0 then .eq
      else
        match mode with
        | .Floor | .Down => .lt
        | .Ceiling | .Up => .gt
        | .Nearest =>
          match Ord.compare (y >>> 1) (x.divMod y).2 with
          | .lt => .gt
          | .gt => .lt
          | .eq =>
            if y.isEven && (x.divMod y).1.isOdd then .gt
            else .lt := by
  unfold divRound
  cases mode <;> simp only [] <;> split_ifs <;>
    first | rfl | (cases Ord.compare (y >>> 1) (x.divMod y).2 <;> rfl)

/-- `(y >>> 1).toNat = y.toNat / 2`. -/
private lemma toNat_shiftRight_one (y : AzNat) : (y >>> 1).toNat = y.toNat / 2 := by
  show (y.shiftRight 1).toNat = y.toNat / 2
  rw [toNat_shiftRight, pow_one]

private lemma compare_aznat_lt {a b : AzNat} (h : a.toNat < b.toNat) :
    Ord.compare a b = .lt := by
  show compare a b = .lt
  rw [compare_eq_compare_toNat]; exact compare_Nat_eq_of_lt _ _ h

private lemma compare_aznat_gt {a b : AzNat} (h : b.toNat < a.toNat) :
    Ord.compare a b = .gt := by
  show compare a b = .gt
  rw [compare_eq_compare_toNat]; exact compare_Nat_eq_of_gt _ _ h

private lemma compare_aznat_eq {a b : AzNat} (h : a.toNat = b.toNat) :
    Ord.compare a b = .eq := by
  show compare a b = .eq
  rw [compare_eq_compare_toNat, h]
  show compareOfLessAndEq _ _ = _
  simp [compareOfLessAndEq]

/-- **Correctness of `AzNat.divRound`.**

For any rounding mode and nonzero divisor, the multi-precision `divRound` on `AzNat`
agrees with the abstract `round` of `x.toNat / y.toNat` against the rounding
target `natBotSet ⊆ EReal`. -/
theorem toNat_divRound (x y : AzNat) (mode : RoundingMode) (hy : 0 < y.toNat) :
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
  have hquot_toNat : (x.divMod y).1.toNat = q := by
    rw [← div_eq_divMod_fst]; show (x / y).toNat = q; rw [toNat_div]
  rw [divRound_fst]
  by_cases hr0 : r = 0
  · -- remainder = 0
    have hr_aznat_zero : (x.divMod y).2.toNat = 0 := by
      rw [← mod_eq_divMod_snd]; show (x % y).toNat = 0; rw [toNat_mod]; exact hr0
    have hr_size_zero : (x.divMod y).2.limbs.size = 0 := (toNat_eq_zero_iff _).mp hr_aznat_zero
    rw [ite_eq_left hr_size_zero]
    show ((x.divMod y).1.toNat : EReal) = (round natBotSet mode t).val
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
        (match Ord.compare ((t : EReal) - F.val) ((roundCeiling natBotSet t).val - (t : EReal)) with
         | .lt => F
         | .gt => roundCeiling natBotSet t
         | .eq => RoundingTarget.tiebreak F (roundCeiling natBotSet t)).val
      have hdF_eq_dC : (t : EReal) - F.val = (roundCeiling natBotSet t).val - (t : EReal) := by
        rw [hF_val, hC_val,
            show ((t : ℝ) : EReal) = (((q : ℕ) : ℝ) : EReal) from by rw [ht_eq_q]]
      rw [show Ord.compare ((t : EReal) - F.val)
              ((roundCeiling natBotSet t).val - (t : EReal)) = .eq from
            compare_eq_iff_eq.mpr hdF_eq_dC]
      show ((q : ℕ) : EReal) = (natBotTiebreak F (roundCeiling natBotSet t)).val
      unfold natBotTiebreak
      rw [hF_nat, hC_nat]
      split_ifs <;> rw [hF_val] <;> push_cast <;> rfl
  · -- remainder ≠ 0
    have hr_aznat_ne : (x.divMod y).2.toNat ≠ 0 := by
      rw [← mod_eq_divMod_snd]; show (x % y).toNat ≠ 0; rw [toNat_mod]; exact hr0
    have hr_size_ne : ¬ ((x.divMod y).2.limbs.size = 0) := by
      intro h; apply hr_aznat_ne; exact (toNat_eq_zero_iff _).mpr h
    rw [ite_eq_right hr_size_ne]
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
    have h_not_dvd : ¬ yn ∣ xn := fun hdvd => hr0 (Nat.mod_eq_zero_of_dvd hdvd)
    set C := roundCeiling natBotSet t with hC_def
    have hC_val : C.val = (((q + 1 : ℕ) : ℝ) : EReal) := by
      rw [hC_def, roundCeiling_natBotSet, ceil_nat_div_nat_of_not_dvd xn yn hy h_not_dvd]
    have hC_nat : natBotToNat C = q + 1 := natBotToNat_eq_of_nat_val (q + 1) C hC_val
    have hquot_succ_toNat : ((x.divMod y).1.addUInt64 1).toNat = q + 1 := by
      rw [toNat_addUInt64, hquot_toNat]; rfl
    have h_real_F : t - ((q : ℕ) : ℝ) = (r : ℝ) / (yn : ℝ) := by
      rw [ht_decomp]; ring
    have hdF_real_eq : (t : EReal) - F.val = (((r : ℝ) / (yn : ℝ)) : EReal) := by
      rw [hF_val, ← EReal.coe_sub, h_real_F]
    have hyn_r_le : r ≤ yn := le_of_lt hr_lt
    have h_real_C : ((q + 1 : ℕ) : ℝ) - t = ((yn - r : ℕ) : ℝ) / (yn : ℝ) := by
      rw [ht_decomp, Nat.cast_sub hyn_r_le]
      have hyn_ne : (yn : ℝ) ≠ 0 := ne_of_gt hyn_real_pos
      push_cast
      field_simp
      ring
    have hdC_real_eq : C.val - (t : EReal) = ((((yn - r : ℕ) : ℝ) / (yn : ℝ)) : EReal) := by
      rw [hC_val, ← EReal.coe_sub, h_real_C]
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
      show ((x.divMod y).1.toNat : EReal) = F.val
      rw [hquot_toNat, hF_val]; push_cast; rfl
    | Down =>
      show ((x.divMod y).1.toNat : EReal) =
        (if 0 ≤ t then F else C).val
      rw [ite_eq_left ht_nonneg, hquot_toNat, hF_val]; push_cast; rfl
    | Ceiling =>
      show (((x.divMod y).1.addUInt64 1).toNat : EReal) = C.val
      rw [hquot_succ_toNat, hC_val]; push_cast; rfl
    | Up =>
      show (((x.divMod y).1.addUInt64 1).toNat : EReal) =
        (if 0 ≤ t then C else F).val
      rw [ite_eq_left ht_nonneg, hquot_succ_toNat, hC_val]; push_cast; rfl
    | Nearest =>
      have hyhalf_toNat : (y >>> 1).toNat = yn / 2 := toNat_shiftRight_one y
      have hrem_toNat : (x.divMod y).2.toNat = r := by
        rw [← mod_eq_divMod_snd]; show (x % y).toNat = r; rw [toNat_mod]
      have hhalfY_lt_iff : (y >>> 1).toNat < (x.divMod y).2.toNat ↔ yn < 2 * r := by
        rw [hyhalf_toNat, hrem_toNat]; omega
      have hr_lt_imp : (x.divMod y).2.toNat < (y >>> 1).toNat → 2 * r < yn := by
        intro h
        rw [hyhalf_toNat, hrem_toNat] at h
        omega
      show ((match Ord.compare (y >>> 1) (x.divMod y).2 with
             | .lt => (x.divMod y).1.addUInt64 1
             | .gt => (x.divMod y).1
             | .eq =>
               if y.isEven && (x.divMod y).1.isOdd then (x.divMod y).1.addUInt64 1
               else (x.divMod y).1).toNat : EReal) =
        (match Ord.compare ((t : EReal) - F.val) (C.val - (t : EReal)) with
         | .lt => F
         | .gt => C
         | .eq => RoundingTarget.tiebreak F C).val
      by_cases h_gt : (y >>> 1).toNat < (x.divMod y).2.toNat
      · -- Round up
        rw [compare_aznat_lt h_gt, hquot_succ_toNat]
        have hreal_gt : yn < 2 * r := hhalfY_lt_iff.mp h_gt
        have hdC_lt : C.val - (t : EReal) < (t : EReal) - F.val :=
          hdC_lt_dF_iff_real.mpr hreal_gt
        rw [show Ord.compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .gt from
              compare_gt_iff_gt.mpr hdC_lt]
        rw [hC_val]; push_cast; rfl
      · by_cases h_lt : (x.divMod y).2.toNat < (y >>> 1).toNat
        · -- Round down (strict)
          rw [compare_aznat_gt h_lt, hquot_toNat]
          have hreal_lt : 2 * r < yn := hr_lt_imp h_lt
          have hdF_lt : (t : EReal) - F.val < C.val - (t : EReal) :=
            hdF_lt_dC_iff_real.mpr hreal_lt
          rw [show Ord.compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .lt from
                compare_lt_iff_lt.mpr hdF_lt]
          rw [hF_val]; push_cast; rfl
        · have h_eq : (y >>> 1).toNat = (x.divMod y).2.toNat := by omega
          rw [compare_aznat_eq h_eq]
          have h_half_eq_r : yn / 2 = r := by rw [← hyhalf_toNat, ← hrem_toNat]; exact h_eq
          have hr_eq_half : r = yn / 2 := h_half_eq_r.symm
          by_cases hyn_par : yn % 2 = 0
          · -- yn even: tie
            have hr_eq : 2 * r = yn := by omega
            have hdF_eq_dC : (t : EReal) - F.val = C.val - (t : EReal) := by
              rw [hdF_real_eq, hdC_real_eq]
              congr 1
              push_cast [Nat.cast_sub hyn_r_le]
              have hyn_ne : (yn : ℝ) ≠ 0 := ne_of_gt hyn_real_pos
              field_simp
              have h_real : (2 : ℝ) * (r : ℝ) = (yn : ℝ) := by exact_mod_cast hr_eq
              linarith
            rw [show Ord.compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .eq from
                  compare_eq_iff_eq.mpr hdF_eq_dC]
            show ((if y.isEven && (x.divMod y).1.isOdd then (x.divMod y).1.addUInt64 1
                   else (x.divMod y).1).toNat : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            have hy_isEven_true : y.isEven = true := by
              rw [isEven_iff]; exact (Nat.even_iff).mpr hyn_par
            by_cases hq_par : q % 2 = 1
            · -- q odd: round up
              have hq_isOdd : (x.divMod y).1.isOdd = true := by
                rw [isOdd_iff, hquot_toNat]; exact ⟨q / 2, by omega⟩
              rw [show (y.isEven && (x.divMod y).1.isOdd) = true from by
                rw [hy_isEven_true, hq_isOdd]; rfl]
              rw [ite_eq_left rfl, hquot_succ_toNat]
              have hq_odd : Odd q := ⟨q / 2, by omega⟩
              have hq_not_even : ¬ Even q := Nat.not_even_iff_odd.mpr hq_odd
              have hq1_even : Even (q + 1) := Odd.add_one hq_odd
              rw [ite_eq_right hq_not_even, ite_eq_left hq1_even, hC_val]; push_cast; rfl
            · -- q even: round down
              have hq_mod : q % 2 = 0 := by omega
              have hq_even : Even q := (Nat.even_iff).mpr hq_mod
              have hq_isOdd_false : (x.divMod y).1.isOdd = false := by
                cases h : (x.divMod y).1.isOdd
                · rfl
                · exfalso
                  rw [isOdd_iff, hquot_toNat] at h
                  rcases h with ⟨k, hk⟩; omega
              rw [show (y.isEven && (x.divMod y).1.isOdd) = false from by
                rw [hq_isOdd_false, Bool.and_false]]
              simp only [Bool.false_eq_true, ite_false]
              rw [hquot_toNat, ite_eq_left hq_even, hF_val]; push_cast; rfl
          · -- yn odd
            have hyn_odd : yn % 2 = 1 := by omega
            have hreal_lt : 2 * r < yn := by omega
            have hdF_lt : (t : EReal) - F.val < C.val - (t : EReal) :=
              hdF_lt_dC_iff_real.mpr hreal_lt
            rw [show Ord.compare ((t : EReal) - F.val) (C.val - (t : EReal)) = .lt from
                  compare_lt_iff_lt.mpr hdF_lt]
            have hy_isEven_false : y.isEven = false := by
              cases h : y.isEven
              · rfl
              · exfalso; rw [isEven_iff] at h
                rcases h with ⟨k, hk⟩; omega
            rw [show (y.isEven && (x.divMod y).1.isOdd) = false from by
              rw [hy_isEven_false]; rfl]
            simp only [Bool.false_eq_true, ite_false]
            rw [hquot_toNat, hF_val]; push_cast; rfl

/-! ### Ordering tag correctness -/

/-- Bridge between integer-scaled `Nat` compare and the real-valued compare with
division. -/
private lemma compare_nat_mul_div_eq_compare_real_div (n m yn : ℕ) (hyn : 0 < yn) :
    Ord.compare (n * yn) m = Ord.compare ((n : ℝ)) ((m : ℝ) / (yn : ℝ)) := by
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

/-- **Ordering tag correctness for `AzNat.divRound`.**

The ordering in `(x.divRound y mode).2` records the relation between the rounded
value and the true real value `x.toNat / y.toNat`. -/
theorem snd_divRound (x y : AzNat) (mode : RoundingMode) (hy : 0 < y.toNat) :
    (x.divRound y mode).2 =
      Ord.compare (((x.divRound y mode).1.toNat : ℕ) : ℝ)
        ((x.toNat : ℝ) / (y.toNat : ℝ)) := by
  rw [← compare_nat_mul_div_eq_compare_real_div _ _ y.toNat hy,
      divRound_snd, divRound_fst]
  have hquot_toNat : (x.divMod y).1.toNat = x.toNat / y.toNat := by
    rw [← div_eq_divMod_fst]
    show (x / y).toNat = x.toNat / y.toNat; rw [toNat_div]
  have hrem_toNat : (x.divMod y).2.toNat = x.toNat % y.toNat := by
    rw [← mod_eq_divMod_snd]; show (x % y).toNat = x.toNat % y.toNat; rw [toNat_mod]
  by_cases hr_size : (x.divMod y).2.limbs.size = 0
  · rw [ite_eq_left hr_size, ite_eq_left hr_size]
    have hr_aznat_zero : (x.divMod y).2.toNat = 0 := (toNat_eq_zero_iff _).mpr hr_size
    have hr0 : x.toNat % y.toNat = 0 := by rw [← hrem_toNat]; exact hr_aznat_zero
    rw [hquot_toNat]
    have heq : x.toNat / y.toNat * y.toNat = x.toNat := by
      have := Nat.div_add_mod' x.toNat y.toNat; omega
    rw [heq]
    show Ordering.eq = compareOfLessAndEq x.toNat x.toNat
    simp [compareOfLessAndEq]
  · rw [ite_eq_right hr_size, ite_eq_right hr_size]
    have hr_aznat_ne : (x.divMod y).2.toNat ≠ 0 := fun h => hr_size ((toNat_eq_zero_iff _).mp h)
    have hr0 : x.toNat % y.toNat ≠ 0 := by rw [← hrem_toNat]; exact hr_aznat_ne
    have hsum : x.toNat / y.toNat * y.toNat + x.toNat % y.toNat = x.toNat :=
      Nat.div_add_mod' x.toNat y.toNat
    have h_q_lt : x.toNat / y.toNat * y.toNat < x.toNat := by
      have : 0 < x.toNat % y.toNat := Nat.pos_of_ne_zero hr0; omega
    have h_q1_gt : x.toNat < (x.toNat / y.toNat + 1) * y.toNat := by
      have hr_lt : x.toNat % y.toNat < y.toNat := Nat.mod_lt _ hy
      have h1 : (x.toNat / y.toNat + 1) * y.toNat =
        x.toNat / y.toNat * y.toNat + y.toNat := by ring
      omega
    have h_compare_q : Ord.compare ((x.divMod y).1.toNat * y.toNat) x.toNat = Ordering.lt := by
      rw [hquot_toNat]
      show compareOfLessAndEq _ _ = Ordering.lt
      simp [compareOfLessAndEq, h_q_lt]
    have h_compare_q1 : Ord.compare (((x.divMod y).1.addUInt64 1).toNat * y.toNat) x.toNat
        = Ordering.gt := by
      rw [toNat_addUInt64, hquot_toNat,
          show ((1 : UInt64).toNat = 1) from rfl]
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
      cases hcmp : Ord.compare (y >>> 1) (x.divMod y).2 with
      | lt => exact h_compare_q1.symm
      | gt => exact h_compare_q.symm
      | eq =>
        split_ifs
        · exact h_compare_q1.symm
        · exact h_compare_q.symm

end Azurite.AzNat
