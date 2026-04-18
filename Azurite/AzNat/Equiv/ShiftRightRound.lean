import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.IsMultipleOfPow2
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TestBit
import Azurite.AzNat.ShiftRightRound
import Azurite.Rounding.Nat
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Semifield

namespace Azurite
open RoundingTarget

/-- Uniqueness of `roundFloor`: any witness to `IsGreatest {s ∈ S | s ≤ x} e` equals
the value produced by `roundFloor`. -/
private lemma roundFloor_val_of_isGreatest {S : Set EReal} [RoundingTarget S]
    {x : ℝ} {e : EReal} (h : IsGreatest {s | s ∈ S ∧ s ≤ (x : EReal)} e) :
    (roundFloor S x).val = e := by
  unfold roundFloor
  exact (existsGreatestLE (S := S) x).choose_spec.unique h

/-- Uniqueness of `roundCeiling`: any witness to `IsLeast {s ∈ S | x ≤ s} e` equals
the value produced by `roundCeiling`. -/
private lemma roundCeiling_val_of_isLeast {S : Set EReal} [RoundingTarget S]
    {x : ℝ} {e : EReal} (h : IsLeast {s | s ∈ S ∧ (x : EReal) ≤ s} e) :
    (roundCeiling S x).val = e := by
  unfold roundCeiling
  exact (existsLeastGE (S := S) x).choose_spec.unique h

/-- For any real `x`, `roundCeiling natBotSet x = ((⌈x⌉₊ : ℝ) : EReal)`. -/
private lemma roundCeiling_natBotSet (x : ℝ) :
    (roundCeiling natBotSet x).val = ((⌈x⌉₊ : ℝ) : EReal) := by
  apply roundCeiling_val_of_isLeast
  refine ⟨⟨Or.inr ⟨⌈x⌉₊, rfl⟩, ?_⟩, ?_⟩
  · exact_mod_cast Nat.le_ceil x
  · rintro s ⟨hmem, hge⟩
    rcases hmem with rfl | ⟨n, rfl⟩
    · exact absurd hge (not_le_of_gt (EReal.bot_lt_coe x))
    · have : x ≤ (n : ℝ) := by exact_mod_cast hge
      exact_mod_cast Nat.ceil_le.mpr this

/-- For nonneg real `x`, `roundFloor natBotSet x = ((⌊x⌋₊ : ℝ) : EReal)`. -/
private lemma roundFloor_natBotSet_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (roundFloor natBotSet x).val = ((⌊x⌋₊ : ℝ) : EReal) := by
  apply roundFloor_val_of_isGreatest
  refine ⟨⟨Or.inr ⟨⌊x⌋₊, rfl⟩, ?_⟩, ?_⟩
  · exact_mod_cast Nat.floor_le hx
  · rintro s ⟨hmem, hle⟩
    rcases hmem with rfl | ⟨n, rfl⟩
    · exact bot_le
    · have : (n : ℝ) ≤ x := by exact_mod_cast hle
      exact_mod_cast Nat.le_floor this

/-- The fractional argument `n.toNat / 2 ^ sh` is nonneg. -/
private lemma toNat_div_pow_nonneg (n : AzNat) (sh : Nat) :
    0 ≤ (n.toNat : ℝ) / ((2 : ℝ) ^ sh) := by
  apply div_nonneg
  · exact_mod_cast Nat.zero_le _
  · exact pow_nonneg (by norm_num) _

/-- Floor of `n.toNat / 2^sh` is nat division. -/
private lemma floor_toNat_div_pow (n : AzNat) (sh : Nat) :
    ⌊(n.toNat : ℝ) / ((2 : ℝ) ^ sh)⌋₊ = n.toNat / 2 ^ sh := by
  have h1 : ((2 : ℝ) ^ sh) = (((2 ^ sh : ℕ) : ℝ)) := by push_cast; rfl
  rw [h1, Nat.floor_div_natCast, Nat.floor_natCast]

/-- Ceiling of `n.toNat / 2^sh`, divisible case: equals nat division. -/
private lemma ceil_toNat_div_pow_of_dvd (n : AzNat) (sh : Nat)
    (h : 2 ^ sh ∣ n.toNat) :
    ⌈(n.toNat : ℝ) / ((2 : ℝ) ^ sh)⌉₊ = n.toNat / 2 ^ sh := by
  obtain ⟨q, hq⟩ := h
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
  have heq : (n.toNat : ℝ) / ((2 : ℝ) ^ sh) = (q : ℝ) := by
    rw [hq]; push_cast; field_simp
  rw [heq, Nat.ceil_natCast, hq, Nat.mul_div_cancel_left _ (Nat.two_pow_pos sh)]

/-- Ceiling of `n.toNat / 2^sh`, non-divisible case: equals nat division plus one. -/
private lemma ceil_toNat_div_pow_of_not_dvd (n : AzNat) (sh : Nat)
    (h : ¬ 2 ^ sh ∣ n.toNat) :
    ⌈(n.toNat : ℝ) / ((2 : ℝ) ^ sh)⌉₊ = n.toNat / 2 ^ sh + 1 := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ sh := pow_pos (by norm_num) _
  set q := n.toNat / 2 ^ sh with hq_def
  set r := n.toNat % 2 ^ sh with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def, Nat.pos_iff_ne_zero]
    intro heq
    exact h (Nat.dvd_of_mod_eq_zero heq)
  have hr_lt : r < 2 ^ sh := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hn : n.toNat = q * 2 ^ sh + r := by
    rw [hq_def, hr_def, Nat.mul_comm]
    exact (Nat.div_add_mod n.toNat (2 ^ sh)).symm
  have hfloor_lt : ((q : ℝ)) < (n.toNat : ℝ) / ((2 : ℝ) ^ sh) := by
    rw [lt_div_iff₀ h2pos, hn]
    push_cast
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
    linarith
  have hlt_ceil : (n.toNat : ℝ) / ((2 : ℝ) ^ sh) < (q + 1 : ℝ) := by
    rw [div_lt_iff₀ h2pos, hn]
    push_cast
    have : ((r : ℝ)) < ((2 : ℝ) ^ sh) := by
      have := hr_lt
      have h2 : ((2 ^ sh : ℕ) : ℝ) = ((2 : ℝ) ^ sh) := by push_cast; rfl
      rw [← h2]; exact_mod_cast this
    linarith
  have hfloor_eq : ⌊(n.toNat : ℝ) / ((2 : ℝ) ^ sh)⌋₊ = q := floor_toNat_div_pow n sh
  have hne : (n.toNat : ℝ) / ((2 : ℝ) ^ sh) ≠ (q : ℝ) := ne_of_gt hfloor_lt
  have hxnonneg : 0 ≤ (n.toNat : ℝ) / ((2 : ℝ) ^ sh) := toNat_div_pow_nonneg n sh
  have h1 : (q : ℝ) ≤ (n.toNat : ℝ) / ((2 : ℝ) ^ sh) := le_of_lt hfloor_lt
  have h2 : (n.toNat : ℝ) / ((2 : ℝ) ^ sh) ≤ ((q + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have h3 : ((q : ℕ) : ℝ) < (n.toNat : ℝ) / ((2 : ℝ) ^ sh) := hfloor_lt
  -- ⌈x⌉₊ ≤ q+1 and q+1 ≤ ⌈x⌉₊
  apply le_antisymm
  · exact Nat.ceil_le.mpr h2
  · have := Nat.add_one_le_ceil_iff (n := q)
      (a := (n.toNat : ℝ) / ((2 : ℝ) ^ sh))
    exact this.mpr h3

/-- If `s ∈ natBotSet` has real value `((q : ℝ) : EReal)` for some nat `q`,
then `natBotToNat s = q`. -/
private lemma natBotToNat_eq_of_nat_val (q : ℕ) (s : ↥natBotSet)
    (hs : s.val = ((q : ℝ) : EReal)) : natBotToNat s = q := by
  unfold natBotToNat
  have hex : ∃ n : ℕ, ((n : ℝ) : EReal) = s.val := ⟨q, hs.symm⟩
  rw [dif_pos hex]
  have h1 := hex.choose_spec
  have h2 : ((hex.choose : ℝ) : EReal) = ((q : ℝ) : EReal) := h1.trans hs
  exact_mod_cast h2

/-- For `v < 2^sh` with `sh > 0`: bit `sh-1` is false iff `v < 2^(sh-1)`. -/
private lemma testBit_top_false_iff_lt_half (v sh : ℕ) (hsh : 0 < sh) (hv : v < 2 ^ sh) :
    v.testBit (sh - 1) = false ↔ v < 2 ^ (sh - 1) := by
  refine ⟨?_, Nat.testBit_eq_false_of_lt⟩
  intro h
  by_contra hge
  push Not at hge
  have h_rem_lt : v - 2 ^ (sh - 1) < 2 ^ (sh - 1) := by
    have h_two_pow : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
      conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
      rw [Nat.pow_succ]
    omega
  have h_v_eq : v = 2 ^ (sh - 1) * 1 + (v - 2 ^ (sh - 1)) := by omega
  rw [h_v_eq, Nat.testBit_two_pow_mul_add _ h_rem_lt (sh - 1)] at h
  simp at h

/-- For `v < 2^sh` with `sh > 0`: bit `sh-1` is true iff `v ≥ 2^(sh-1)`. -/
private lemma testBit_top_true_iff_half_le (v sh : ℕ) (hsh : 0 < sh) (hv : v < 2 ^ sh) :
    v.testBit (sh - 1) = true ↔ 2 ^ (sh - 1) ≤ v := by
  rw [show (v.testBit (sh - 1) = true) ↔ ¬ v.testBit (sh - 1) = false from by
    cases v.testBit (sh - 1) <;> simp]
  rw [testBit_top_false_iff_lt_half v sh hsh hv]
  omega

/-- For `v < 2^sh` with `sh > 0`: if bit `sh-1` is true and `v` is a multiple of
`2^(sh-1)`, then `v = 2^(sh-1)`. -/
private lemma eq_half_of_testBit_and_dvd (v sh : ℕ) (hsh : 0 < sh) (hv : v < 2 ^ sh)
    (hbit : v.testBit (sh - 1) = true) (hdvd : 2 ^ (sh - 1) ∣ v) :
    v = 2 ^ (sh - 1) := by
  have hge : 2 ^ (sh - 1) ≤ v := (testBit_top_true_iff_half_le v sh hsh hv).mp hbit
  have h_two_pow : 2 ^ sh = 2 ^ (sh - 1) * 2 := by
    conv_lhs => rw [show sh = (sh - 1) + 1 from by omega]
    rw [Nat.pow_succ]
  obtain ⟨q, rfl⟩ := hdvd
  have hq_lt : q < 2 := by
    have h1 : 2 ^ (sh - 1) * q < 2 ^ (sh - 1) * 2 := by rw [← h_two_pow]; exact hv
    exact Nat.lt_of_mul_lt_mul_left h1
  have hq_pos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · exfalso; rw [hq0, Nat.mul_zero] at hge
      exact absurd hge (by simp)
    · exact hq0
  have : q = 1 := by omega
  rw [this, Nat.mul_one]

/-- Extract a limb of `n.toNat / 2^sh` decomposition. -/
private lemma toNat_eq_mul_pow_add_mod (n : AzNat) (sh : Nat) :
    n.toNat = (n.toNat / 2 ^ sh) * 2 ^ sh + n.toNat % 2 ^ sh := by
  conv_lhs => rw [← Nat.div_add_mod n.toNat (2 ^ sh)]
  ring

/-- **Correctness of `shiftRightRound`.**

For any rounding mode and shift amount, the limb-level `shiftRightRound` on `AzNat`
agrees with the abstract `round` of `n.toNat / 2^sh` against the rounding target
`natBotSet ⊆ EReal`. -/
theorem AzNat.toNat_shiftRightRound (n : AzNat) (mode : RoundingMode) (sh : Nat) :
    ((n.shiftRightRound mode sh).toNat : EReal) =
      (round natBotSet mode ((n.toNat : ℝ) / ((2 : ℝ) ^ sh))).val := by
  set x : ℝ := (n.toNat : ℝ) / ((2 : ℝ) ^ sh) with hx_def
  have hx_nonneg : 0 ≤ x := toNat_div_pow_nonneg n sh
  have hfloor_x : ⌊x⌋₊ = n.toNat / 2 ^ sh := floor_toNat_div_pow n sh
  -- The round-down value always matches `shiftRight`.
  have hfloor_side : ((n.shiftRight sh).toNat : EReal) =
      (roundFloor natBotSet x).val := by
    rw [roundFloor_natBotSet_nonneg x hx_nonneg, AzNat.toNat_shiftRight, ← hfloor_x]
    push_cast; rfl
  -- The ceiling value: conditional on divisibility.
  have hceil_side_of_dvd (h : 2 ^ sh ∣ n.toNat) :
      ((n.shiftRight sh).toNat : EReal) = (roundCeiling natBotSet x).val := by
    rw [roundCeiling_natBotSet, AzNat.toNat_shiftRight]
    rw [ceil_toNat_div_pow_of_dvd n sh h]
    push_cast; rfl
  have hceil_side_of_not_dvd (h : ¬ 2 ^ sh ∣ n.toNat) :
      (((n.shiftRight sh).addUInt64 1).toNat : EReal) =
        (roundCeiling natBotSet x).val := by
    rw [roundCeiling_natBotSet, AzNat.toNat_addUInt64, AzNat.toNat_shiftRight]
    rw [ceil_toNat_div_pow_of_not_dvd n sh h]
    have h1 : ((1 : UInt64).toNat : ℕ) = 1 := rfl
    rw [h1]
    push_cast; rfl
  unfold AzNat.shiftRightRound
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
    rw [isMultipleOfPow2_eq]
    by_cases h : 2 ^ sh ∣ n.toNat
    · simp [h, hceil_side_of_dvd h]
    · simp [h, hceil_side_of_not_dvd h]
  | .Up =>
    rw [show round natBotSet RoundingMode.Up x =
      (if 0 ≤ x then roundCeiling natBotSet x else roundFloor natBotSet x) from rfl]
    rw [if_pos hx_nonneg]
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
          (let dF : EReal := (x : EReal) - F.val
           let dC : EReal := C.val - (x : EReal)
           if dF < dC then F
           else if dC < dF then C
           else RoundingTarget.tiebreak F C) := rfl
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
      have hLHS_q : ((if sh = 0 then n
          else if n.testBit (sh - 1) then
              if n.isMultipleOfPow2 (sh - 1) then
                let shifted := n.shiftRight sh
                if shifted.isOdd then shifted.addUInt64 1 else shifted
              else (n.shiftRight sh).addUInt64 1
          else n.shiftRight sh).toNat : EReal) = ((q : ℝ) : EReal) := by
        by_cases hsh0 : sh = 0
        · subst hsh0
          rw [if_pos rfl]
          have hq_n : q = n.toNat := by simp [hq_def]
          rw [hq_n]; push_cast; rfl
        · rw [if_neg hsh0]
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
          rw [if_neg hcond_false]
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
      rw [if_neg hsh_ne]
      -- Arithmetic setup.
      set r := n.toNat % 2 ^ sh with hr_def
      have hr_bound : r < 2 ^ sh := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hr_pos : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hdvd
        · exact h
      have hn_decomp : n.toNat = q * 2 ^ sh + r := toNat_eq_mul_pow_add_mod n sh
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
      have hceil : ⌈x⌉₊ = q + 1 := ceil_toNat_div_pow_of_not_dvd n sh hdvd
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
        rw [if_pos hbit]
        have hr_bit : r.testBit (sh - 1) = true := hr_testBit ▸ hbit
        have hr_ge : 2 ^ (sh - 1) ≤ r :=
          (testBit_top_true_iff_half_le r sh hsh_pos hr_bound).mp hr_bit
        by_cases hmult : 2 ^ (sh - 1) ∣ n.toNat
        · -- r = 2^(sh-1): tie, tiebreak decides.
          have hmult_bool : n.isMultipleOfPow2 (sh - 1) = true := by
            rw [AzNat.isMultipleOfPow2_eq]; exact decide_eq_true hmult
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
          -- LHS: shifted.isOdd decides between q and q+1.
          by_cases hodd : Odd (n.shiftRight sh).toNat
          · -- q odd ⇒ LHS = q + 1.
            have hq_odd : Odd q := by rw [AzNat.toNat_shiftRight] at hodd; exact hodd
            have hq_not_even : ¬ Even q := Nat.not_even_iff_odd.mpr hq_odd
            have hisOdd_true : (n.shiftRight sh).isOdd = true := by
              rw [AzNat.isOdd_iff, AzNat.toNat_shiftRight]; exact hq_odd
            rw [if_pos hisOdd_true]
            rw [AzNat.toNat_addUInt64, AzNat.toNat_shiftRight]
            show ((q + (1 : UInt64).toNat : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q + (1 : UInt64).toNat : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            have hq1_even : Even (q + 1) := Odd.add_one hq_odd
            rw [if_neg hq_not_even, if_pos hq1_even, hC_val]
            rw [show (1 : UInt64).toNat = 1 from rfl]
            push_cast; ring_nf
          · -- q even ⇒ LHS = q.
            have hq_even : Even q := by
              rw [Nat.not_odd_iff_even, AzNat.toNat_shiftRight] at hodd; exact hodd
            have hisOdd_false : ¬ ((n.shiftRight sh).isOdd = true) := by
              rw [AzNat.isOdd_iff, AzNat.toNat_shiftRight, Nat.not_odd_iff_even]
              exact hq_even
            rw [if_neg hisOdd_false]
            rw [AzNat.toNat_shiftRight]
            show ((q : ℕ) : EReal) = (RoundingTarget.tiebreak F C).val
            show ((q : ℕ) : EReal) = (natBotTiebreak F C).val
            unfold natBotTiebreak
            rw [hF_nat, hC_nat]
            rw [if_pos hq_even, hF_val]
            push_cast; rfl
        · -- r > 2^(sh-1): dC < dF, returns C.
          have hmult_cond_false : ¬ (n.isMultipleOfPow2 (sh - 1) = true) := by
            rw [AzNat.isMultipleOfPow2_eq]
            intro heq
            exact hmult (of_decide_eq_true heq)
          rw [if_neg hmult_cond_false]
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
          have hnot_dF_lt_dC_real : ¬ (x - q < (q : ℝ) + 1 - x) := by linarith
          have hnot_dF_lt_dC : ¬ ((x : EReal) - F.val < C.val - (x : EReal)) :=
            fun h => hnot_dF_lt_dC_real (hdF_lt_dC_iff.mp h)
          have hdC_lt : C.val - (x : EReal) < (x : EReal) - F.val :=
            hdC_lt_dF_iff.mpr hdC_lt_real
          rw [if_neg hnot_dF_lt_dC, if_pos hdC_lt]
          rw [AzNat.toNat_addUInt64, AzNat.toNat_shiftRight, hC_val]
          show (((n.toNat / 2 ^ sh + (1 : UInt64).toNat : ℕ) : ℕ) : EReal) =
            (((q + 1 : ℕ) : ℝ) : EReal)
          rw [show (1 : UInt64).toNat = 1 from rfl]
          push_cast; rfl
      · -- testBit = false: r < 2^(sh-1), dF < dC, returns F.
        rw [if_neg hbit]
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
        rw [if_pos hdF_lt]
        rw [AzNat.toNat_shiftRight, hF_val]
        push_cast; rfl

end Azurite
