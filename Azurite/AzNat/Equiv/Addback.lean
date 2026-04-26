import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.SubMulLimbs

namespace Azurite.AzNat

/-! ### Correctness of `schoolbookDivModLimbs.addback` -/

/-- `schoolbookDivModLimbs.addback` preserves any prefix up to `loA`. -/
theorem schoolbookDivModLimbs.addback_toList_take_le (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : m0 ≤ loA) :
    (schoolbookDivModLimbs.addback a b loA loB n q borrow fuel hA hB).1.toList.take m0
      = a.toList.take m0 := by
  induction fuel generalizing a q borrow with
  | zero => rw [schoolbookDivModLimbs.addback]
  | succ fuel' ih =>
    rw [schoolbookDivModLimbs.addback]
    by_cases hb : borrow
    · simp only [hb, ↓reduceIte]
      rw [ih]
      show (addSameLengthLimbs a b loA loB n hA hB).1.toList.take m0 = a.toList.take m0
      exact addSameLengthLimbs.go_toList_take_le b loA loB n a 0 false hA hB m0
        (Nat.le_trans hm (Nat.le_add_right _ _))
    · simp [hb]

/-- `schoolbookDivModLimbs.addback` preserves the prefix of `a` up to `loA`. -/
theorem schoolbookDivModLimbs.addback_toList_take (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivModLimbs.addback a b loA loB n q borrow fuel hA hB).1.toList.take loA
      = a.toList.take loA :=
  schoolbookDivModLimbs.addback_toList_take_le a b loA loB n q borrow fuel hA hB loA
    (Nat.le_refl _)

/-- `schoolbookDivModLimbs.addback` preserves the suffix of `a` from `loA + n`. -/
theorem schoolbookDivModLimbs.addback_toList_drop (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivModLimbs.addback a b loA loB n q borrow fuel hA hB).1.toList.drop (loA + n)
      = a.toList.drop (loA + n) := by
  induction fuel generalizing a q borrow with
  | zero => rw [schoolbookDivModLimbs.addback]
  | succ fuel' ih =>
    rw [schoolbookDivModLimbs.addback]
    by_cases hb : borrow
    · simp only [hb, ↓reduceIte]
      rw [ih]
      show (addSameLengthLimbs a b loA loB n hA hB).1.toList.drop (loA + n)
        = a.toList.drop (loA + n)
      exact addSameLengthLimbs.go_toList_drop b loA loB n a 0 false hA hB
    · simp [hb]

/-- Correctness of `schoolbookDivModLimbs.addback`: the value of the `n`-limb slice
    plus a carry-flag-encoded high bit, plus `q * B`, is preserved. The
    precondition `borrow = true → fuel ≤ q.toNat` ensures `q` does not wrap
    around through `0` during the addback iterations. -/
theorem schoolbookDivModLimbs.addback_toNat (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (hq : borrow = true → fuel ≤ q.toNat) :
    let res := schoolbookDivModLimbs.addback a b loA loB n q borrow fuel hA hB
    ∃ b_out : Bool,
      toNatLimbsList ((res.1.toList.drop loA).take n)
        + (1 - b_out.toNat) * 2 ^ (64 * n)
        + res.2.toNat * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((a.toList.drop loA).take n)
        + (1 - borrow.toNat) * 2 ^ (64 * n)
        + q.toNat * toNatLimbsList ((b.toList.drop loB).take n) := by
  induction fuel generalizing a q borrow with
  | zero =>
    rw [schoolbookDivModLimbs.addback]
    exact ⟨borrow, rfl⟩
  | succ fuel' ih =>
    rw [schoolbookDivModLimbs.addback]
    by_cases hb : borrow
    · simp only [hb, ↓reduceIte]
      have hq_le : fuel' + 1 ≤ q.toNat := hq hb
      have hq_pos : 0 < q.toNat := by omega
      set r := addSameLengthLimbs a b loA loB n hA hB with hr_def
      have h_r_size : r.1.size = a.size := by
        rw [hr_def]; exact addSameLengthLimbs_size _ _ _ _ _ _ _
      have h_addback_hyp : loA + n ≤ r.1.size := by rw [h_r_size]; exact hA
      have h_addback :
          toNatLimbsList ((r.1.toList.drop loA).take n) + r.2.toNat * 2 ^ (64 * n)
            = toNatLimbsList ((a.toList.drop loA).take n)
              + toNatLimbsList ((b.toList.drop loB).take n) := by
        have h := addSameLengthLimbs_toNat a b loA loB n hA hB
        rw [← hr_def] at h
        simp only at h
        exact h
      have h_q_minus_one : (q - 1).toNat = q.toNat - 1 := by
        have h_one_toNat : (1 : UInt64).toNat = 1 := rfl
        have h_le : (1 : UInt64) ≤ q := by
          rw [_root_.UInt64.le_iff_toNat_le, h_one_toNat]
          omega
        rw [_root_.UInt64.toNat_sub_of_le _ _ h_le, h_one_toNat]
      have h_ih_hyp : (!r.2) = true → fuel' ≤ (q - 1).toNat := by
        intro _
        rw [h_q_minus_one]
        omega
      have h_ih := ih r.1 (q - 1) (!r.2) h_addback_hyp h_ih_hyp
      simp only at h_ih
      obtain ⟨b_out, h_eq⟩ := h_ih
      refine ⟨b_out, ?_⟩
      rw [h_eq, h_q_minus_one]
      set X := toNatLimbsList ((r.1.toList.drop loA).take n) with hX_def
      set Y := toNatLimbsList ((a.toList.drop loA).take n) with hY_def
      set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
      change X + (1 - (!r.2).toNat) * 2 ^ (64 * n) + (q.toNat - 1) * Z
            = Y + (1 - true.toNat) * 2 ^ (64 * n) + q.toNat * Z
      have h_neg_carry : (1 - (!r.2).toNat) * 2 ^ (64 * n) = r.2.toNat * 2 ^ (64 * n) := by
        cases r.2 <;> simp
      have h_true : (1 - (true).toNat) * 2 ^ (64 * n) = 0 := by simp
      rw [h_neg_carry, h_true]
      have h_q_split : q.toNat * Z = (q.toNat - 1) * Z + Z := by
        conv_lhs => rw [show q.toNat = (q.toNat - 1) + 1 from by omega]
        rw [Nat.add_mul, Nat.one_mul]
      rw [h_q_split]
      linarith
    · simp only [hb]
      exact ⟨false, rfl⟩

/-- Variant of `addback_toNat` specialized to `fuel = 2` with a value-based safety
    hypothesis suitable for the Knuth/Möller–Granlund two-correction setting.

    Replaces the uniform precondition `borrow = true → 2 ≤ q.toNat` with two
    finer conditions:

    * `h_safe1`: `borrow = true → 1 ≤ q.toNat` — prevents the first iteration's
      `q - 1` from wrapping.
    * `h_safe2`: `borrow = true → Y + Z < 2^(64·n) → 2 ≤ q.toNat` — when the
      first `addSameLengthLimbs` would not carry out (i.e., a second iteration
      will fire), `q.toNat ≥ 2` is required.

    The boundary case `q.toNat = 1, borrow = true, Y + Z ≥ 2^(64·n)` (one
    addback fires, second iteration skipped) — which the original
    `addback_toNat` cannot accept — is handled here. -/
theorem schoolbookDivModLimbs.addback_toNat_two
    (a b : Array UInt64) (loA loB n : Nat) (q : UInt64) (borrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (h_safe1 : borrow = true → 1 ≤ q.toNat)
    (h_safe2 : borrow = true →
                 toNatLimbsList ((a.toList.drop loA).take n)
                   + toNatLimbsList ((b.toList.drop loB).take n) < 2 ^ (64 * n) →
                 2 ≤ q.toNat) :
    let res := schoolbookDivModLimbs.addback a b loA loB n q borrow 2 hA hB
    ∃ b_out : Bool,
      toNatLimbsList ((res.1.toList.drop loA).take n)
        + (1 - b_out.toNat) * 2 ^ (64 * n)
        + res.2.toNat * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((a.toList.drop loA).take n)
        + (1 - borrow.toNat) * 2 ^ (64 * n)
        + q.toNat * toNatLimbsList ((b.toList.drop loB).take n) := by
  rw [schoolbookDivModLimbs.addback]
  by_cases hb : borrow
  · simp only [hb, ↓reduceIte]
    have hq_ge1 : 1 ≤ q.toNat := h_safe1 hb
    set r := addSameLengthLimbs a b loA loB n hA hB with hr_def
    have h_r_size : r.1.size = a.size := by
      rw [hr_def]; exact addSameLengthLimbs_size _ _ _ _ _ _ _
    have h_r_hyp : loA + n ≤ r.1.size := by rw [h_r_size]; exact hA
    have h_addSame :
        toNatLimbsList ((r.1.toList.drop loA).take n) + r.2.toNat * 2 ^ (64 * n)
          = toNatLimbsList ((a.toList.drop loA).take n)
            + toNatLimbsList ((b.toList.drop loB).take n) := by
      have h := addSameLengthLimbs_toNat a b loA loB n hA hB
      rw [← hr_def] at h
      simpa using h
    have h_q_minus_one : (q - 1).toNat = q.toNat - 1 := by
      have h_one : (1 : UInt64).toNat = 1 := rfl
      have h_le : (1 : UInt64) ≤ q := by
        rw [_root_.UInt64.le_iff_toNat_le, h_one]; omega
      rw [_root_.UInt64.toNat_sub_of_le _ _ h_le, h_one]
    have h_inner_safe : (!r.2) = true → 1 ≤ (q - 1).toNat := by
      intro h_neg
      have h_r2_false : r.2 = false := by
        cases h_c : r.2 with
        | false => rfl
        | true => simp [h_c] at h_neg
      have h_Ynew_lt :
          toNatLimbsList ((r.1.toList.drop loA).take n) < 2 ^ (64 * n) := by
        have h_pow := toNatLimbsList_lt_pow ((r.1.toList.drop loA).take n)
        have h_len : ((r.1.toList.drop loA).take n).length = n := by
          rw [List.length_take, List.length_drop, Array.length_toList, h_r_size]
          omega
        rw [h_len] at h_pow
        exact h_pow
      have h_lt :
          toNatLimbsList ((a.toList.drop loA).take n)
            + toNatLimbsList ((b.toList.drop loB).take n) < 2 ^ (64 * n) := by
        have h := h_addSame
        rw [h_r2_false] at h
        simp [show (false : Bool).toNat = 0 from rfl] at h
        omega
      have hq2 := h_safe2 hb h_lt
      rw [h_q_minus_one]; omega
    have h_inner :=
      schoolbookDivModLimbs.addback_toNat r.1 b loA loB n (q - 1) (!r.2) 1
        h_r_hyp hB h_inner_safe
    simp only at h_inner
    obtain ⟨b_out, h_eq⟩ := h_inner
    refine ⟨b_out, ?_⟩
    rw [h_eq, h_q_minus_one]
    set X := toNatLimbsList ((r.1.toList.drop loA).take n) with hX_def
    set Y := toNatLimbsList ((a.toList.drop loA).take n) with hY_def
    set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
    change X + (1 - (!r.2).toNat) * 2 ^ (64 * n) + (q.toNat - 1) * Z
          = Y + (1 - true.toNat) * 2 ^ (64 * n) + q.toNat * Z
    have h_neg_carry : (1 - (!r.2).toNat) * 2 ^ (64 * n) = r.2.toNat * 2 ^ (64 * n) := by
      cases r.2 <;> simp
    have h_true : (1 - (true).toNat) * 2 ^ (64 * n) = 0 := by simp
    rw [h_neg_carry, h_true]
    have h_q_split : q.toNat * Z = (q.toNat - 1) * Z + Z := by
      conv_lhs => rw [show q.toNat = (q.toNat - 1) + 1 from by omega]
      rw [Nat.add_mul, Nat.one_mul]
    rw [h_q_split]
    linarith
  · simp only [hb]
    exact ⟨false, rfl⟩

/-- Structural fact: when `borrow = false`, `addback` is a no-op: result = (a, q). -/
theorem schoolbookDivModLimbs.addback_borrow_false (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (fuel : Nat) (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    schoolbookDivModLimbs.addback a b loA loB n q false fuel hA hB = (a, q) := by
  cases fuel with
  | zero => rw [schoolbookDivModLimbs.addback]
  | succ fuel' => rw [schoolbookDivModLimbs.addback]; simp

/-- Strengthened version of `addback_toNat_two` that exposes additional
    structural facts about the result:

    * If the existential `b_out` is `true` AND `borrow = true`, then both
      addback iterations completed without a carry-out, so
      `Y + 2*Z < 2^(64*n)`.
    * If `b_out` is `false` AND `borrow = true`, then the post-addback
      low slice is strictly less than `Z` (because the last addback that
      fired overflowed, leaving a "small" non-negative remainder).

    These are key for the BZ correctness proof. -/
theorem schoolbookDivModLimbs.addback_toNat_two_strong
    (a b : Array UInt64) (loA loB n : Nat) (q : UInt64) (borrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (h_safe1 : borrow = true → 1 ≤ q.toNat)
    (h_safe2 : borrow = true →
                 toNatLimbsList ((a.toList.drop loA).take n)
                   + toNatLimbsList ((b.toList.drop loB).take n) < 2 ^ (64 * n) →
                 2 ≤ q.toNat) :
    let res := schoolbookDivModLimbs.addback a b loA loB n q borrow 2 hA hB
    ∃ b_out : Bool,
      (toNatLimbsList ((res.1.toList.drop loA).take n)
        + (1 - b_out.toNat) * 2 ^ (64 * n)
        + res.2.toNat * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((a.toList.drop loA).take n)
        + (1 - borrow.toNat) * 2 ^ (64 * n)
        + q.toNat * toNatLimbsList ((b.toList.drop loB).take n)) ∧
      (b_out = true → borrow = true →
        toNatLimbsList ((a.toList.drop loA).take n)
          + 2 * toNatLimbsList ((b.toList.drop loB).take n) < 2 ^ (64 * n)) ∧
      (b_out = false → borrow = true →
        toNatLimbsList ((res.1.toList.drop loA).take n)
          < toNatLimbsList ((b.toList.drop loB).take n)) := by
  -- We get the main equation from the existing `addback_toNat_two`.
  have h_main := schoolbookDivModLimbs.addback_toNat_two a b loA loB n q borrow hA hB h_safe1 h_safe2
  obtain ⟨b_out, h_eq⟩ := h_main
  refine ⟨b_out, h_eq, ?_, ?_⟩
  all_goals (
    intro _ h_borrow
    set Y := toNatLimbsList ((a.toList.drop loA).take n) with hY_def
    set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
    have hq_ge1 : 1 ≤ q.toNat := h_safe1 h_borrow
    set r := addSameLengthLimbs a b loA loB n hA hB with hr_def
    have h_r_size : r.1.size = a.size := by
      rw [hr_def]; exact addSameLengthLimbs_size _ _ _ _ _ _ _
    have h_r_hyp : loA + n ≤ r.1.size := by rw [h_r_size]; exact hA
    have h_addSame :
        toNatLimbsList ((r.1.toList.drop loA).take n) + r.2.toNat * 2 ^ (64 * n)
          = Y + Z := by
      have h := addSameLengthLimbs_toNat a b loA loB n hA hB
      rw [← hr_def] at h
      simpa using h
    have h_q_minus_one : (q - 1).toNat = q.toNat - 1 := by
      have h_one : (1 : UInt64).toNat = 1 := rfl
      have h_le : (1 : UInt64) ≤ q := by
        rw [_root_.UInt64.le_iff_toNat_le, h_one]; omega
      rw [_root_.UInt64.toNat_sub_of_le _ _ h_le, h_one]
    -- Unfold addback (fuel = 2) with borrow = true.
    have h_unfold1 :
        schoolbookDivModLimbs.addback a b loA loB n q true 2 hA hB
          = schoolbookDivModLimbs.addback r.1 b loA loB n (q - 1) (!r.2) 1 h_r_hyp hB := by
      conv_lhs => rw [schoolbookDivModLimbs.addback]
      simp only [if_true, ← hr_def]
    -- The (n)-limb slice bound for any array.
    have h_r_low_lt :
        toNatLimbsList ((r.1.toList.drop loA).take n) < 2 ^ (64 * n) := by
      have h_pow := toNatLimbsList_lt_pow ((r.1.toList.drop loA).take n)
      have h_len : ((r.1.toList.drop loA).take n).length = n := by
        rw [List.length_take, List.length_drop, Array.length_toList, h_r_size]
        omega
      rw [h_len] at h_pow
      exact h_pow)
  · -- First implication: b_out = true → Y + 2*Z < β^n.
    rename_i h_bout
    -- We show this by contraposition: assume Y + 2*Z ≥ β^n, then b_out = false.
    by_contra h_goal
    push Not at h_goal
    -- We compute b_out structurally.
    have h_bout_compute : b_out = false := by
      by_cases hr2 : r.2
      · -- r.2 = true: 1st addback overflowed. fixup.2 = q - 1, b_out = false (via inner no-op).
        have h_inner :
            schoolbookDivModLimbs.addback r.1 b loA loB n (q - 1) (!r.2) 1 h_r_hyp hB
              = (r.1, q - 1) := by
          rw [hr2]
          simp only [Bool.not_true]
          exact schoolbookDivModLimbs.addback_borrow_false _ _ _ _ _ _ _ _ _
        have h_res_eq : schoolbookDivModLimbs.addback a b loA loB n q borrow 2 hA hB = (r.1, q - 1) := by
          rw [show borrow = true from h_borrow, h_unfold1, h_inner]
        rw [h_res_eq] at h_eq
        simp only at h_eq
        rw [h_borrow] at h_eq
        simp only [Bool.toNat_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h_eq
        rw [h_q_minus_one] at h_eq
        rw [hr2] at h_addSame
        simp only [Bool.toNat_true, Nat.one_mul] at h_addSame
        have h_q_split : q.toNat * Z = (q.toNat - 1) * Z + Z := by
          conv_lhs => rw [show q.toNat = (q.toNat - 1) + 1 from by omega]
          rw [Nat.add_mul, Nat.one_mul]
        cases h_b : b_out
        · rfl
        · rw [h_b] at h_eq
          simp only [Bool.toNat_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h_eq
          have h_pow_pos : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
          omega
      · -- r.2 = false: 2 addbacks fire.
        have hr2_false : r.2 = false := by
          cases h_c : r.2 with
          | false => rfl
          | true => exact absurd h_c hr2
        have h_lt_first : Y + Z < 2 ^ (64 * n) := by
          rw [hr2_false] at h_addSame
          simp at h_addSame
          rw [← h_addSame]; exact h_r_low_lt
        have hq2 := h_safe2 h_borrow h_lt_first
        set r' := addSameLengthLimbs r.1 b loA loB n h_r_hyp hB with hr'_def
        have h_r'_size : r'.1.size = r.1.size := by
          rw [hr'_def]; exact addSameLengthLimbs_size _ _ _ _ _ _ _
        have h_r'_hyp : loA + n ≤ r'.1.size := by rw [h_r'_size]; exact h_r_hyp
        have h_addSame' :
            toNatLimbsList ((r'.1.toList.drop loA).take n) + r'.2.toNat * 2 ^ (64 * n)
              = toNatLimbsList ((r.1.toList.drop loA).take n) + Z := by
          have h := addSameLengthLimbs_toNat r.1 b loA loB n h_r_hyp hB
          rw [← hr'_def] at h
          simpa using h
        have h_q_minus_two : (q - 1 - 1).toNat = q.toNat - 2 := by
          have h_one : (1 : UInt64).toNat = 1 := rfl
          have h_le : (1 : UInt64) ≤ q - 1 := by
            rw [_root_.UInt64.le_iff_toNat_le, h_one, h_q_minus_one]; omega
          rw [_root_.UInt64.toNat_sub_of_le _ _ h_le, h_q_minus_one]
          omega
        have h_inner_unfold :
            schoolbookDivModLimbs.addback r.1 b loA loB n (q - 1) (!r.2) 1 h_r_hyp hB
              = schoolbookDivModLimbs.addback r'.1 b loA loB n (q - 1 - 1) (!r'.2) 0 h_r'_hyp hB := by
          rw [hr2_false]
          simp only [Bool.not_false]
          conv_lhs => rw [schoolbookDivModLimbs.addback]
          simp only [if_true, ← hr'_def]
        have h_inner_inner :
            schoolbookDivModLimbs.addback r'.1 b loA loB n (q - 1 - 1) (!r'.2) 0 h_r'_hyp hB
              = (r'.1, q - 1 - 1) := by
          rw [schoolbookDivModLimbs.addback]
        have h_res_eq : schoolbookDivModLimbs.addback a b loA loB n q borrow 2 hA hB = (r'.1, q - 1 - 1) := by
          rw [show borrow = true from h_borrow, h_unfold1, h_inner_unfold, h_inner_inner]
        rw [h_res_eq] at h_eq
        simp only at h_eq
        rw [h_borrow] at h_eq
        simp only [Bool.toNat_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h_eq
        rw [h_q_minus_two] at h_eq
        rw [hr2_false] at h_addSame
        simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h_addSame
        rw [h_addSame] at h_addSame'
        have h_q_split : q.toNat * Z = (q.toNat - 2) * Z + 2 * Z := by
          have h_q_eq : q.toNat = (q.toNat - 2) + 2 := by omega
          conv_lhs => rw [h_q_eq]
          rw [Nat.add_mul]
        cases h_b : b_out
        · rfl
        · rw [h_b] at h_eq
          simp only [Bool.toNat_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h_eq
          have h_r'_low_lt :
              toNatLimbsList ((r'.1.toList.drop loA).take n) < 2 ^ (64 * n) := by
            have h_pow := toNatLimbsList_lt_pow ((r'.1.toList.drop loA).take n)
            have h_len : ((r'.1.toList.drop loA).take n).length = n := by
              rw [List.length_take, List.length_drop, Array.length_toList, h_r'_size,
                  h_r_size]
              omega
            rw [h_len] at h_pow
            exact h_pow
          omega
    rw [h_bout_compute] at h_bout
    exact absurd h_bout (by decide)
  · -- Second implication: b_out = false → res.1.low < Z.
    rename_i h_bout
    -- Structurally: in subcase B1 (1st addback overflowed) or B2a (2nd overflowed),
    -- the result is < Z by direct algebraic check.
    by_cases hr2 : r.2
    · -- Subcase B1: r.2 = true, fixup = (r.1, q-1), b_out = false. res.1.low = r.1.low.
      -- We have r.1.low + β^n = Y + Z. So r.1.low = Y + Z - β^n.
      -- res.1.low < Z iff r.1.low < Z iff Y + Z - β^n < Z iff Y < β^n. ✓
      have h_inner :
          schoolbookDivModLimbs.addback r.1 b loA loB n (q - 1) (!r.2) 1 h_r_hyp hB
            = (r.1, q - 1) := by
        rw [hr2]
        simp only [Bool.not_true]
        exact schoolbookDivModLimbs.addback_borrow_false _ _ _ _ _ _ _ _ _
      have h_res_eq : schoolbookDivModLimbs.addback a b loA loB n q borrow 2 hA hB = (r.1, q - 1) := by
        rw [show borrow = true from h_borrow, h_unfold1, h_inner]
      rw [h_res_eq]
      simp only
      -- Goal: r.1.low < Z.
      rw [hr2] at h_addSame
      simp only [Bool.toNat_true, Nat.one_mul] at h_addSame
      -- h_addSame : r.1.low + β^n = Y + Z.
      have h_Y_lt : Y < 2 ^ (64 * n) := by
        have h_pow := toNatLimbsList_lt_pow ((a.toList.drop loA).take n)
        have h_len : ((a.toList.drop loA).take n).length = n := by
          rw [List.length_take, List.length_drop, Array.length_toList]
          omega
        rw [h_len] at h_pow
        exact h_pow
      omega
    · -- Subcase B2: r.2 = false, 2 addbacks fire.
      have hr2_false : r.2 = false := by
        cases h_c : r.2 with
        | false => rfl
        | true => exact absurd h_c hr2
      have h_lt_first : Y + Z < 2 ^ (64 * n) := by
        rw [hr2_false] at h_addSame
        simp at h_addSame
        rw [← h_addSame]; exact h_r_low_lt
      have hq2 := h_safe2 h_borrow h_lt_first
      set r' := addSameLengthLimbs r.1 b loA loB n h_r_hyp hB with hr'_def
      have h_r'_size : r'.1.size = r.1.size := by
        rw [hr'_def]; exact addSameLengthLimbs_size _ _ _ _ _ _ _
      have h_r'_hyp : loA + n ≤ r'.1.size := by rw [h_r'_size]; exact h_r_hyp
      have h_addSame' :
          toNatLimbsList ((r'.1.toList.drop loA).take n) + r'.2.toNat * 2 ^ (64 * n)
            = toNatLimbsList ((r.1.toList.drop loA).take n) + Z := by
        have h := addSameLengthLimbs_toNat r.1 b loA loB n h_r_hyp hB
        rw [← hr'_def] at h
        simpa using h
      have h_q_minus_two : (q - 1 - 1).toNat = q.toNat - 2 := by
        have h_one : (1 : UInt64).toNat = 1 := rfl
        have h_le : (1 : UInt64) ≤ q - 1 := by
          rw [_root_.UInt64.le_iff_toNat_le, h_one, h_q_minus_one]; omega
        rw [_root_.UInt64.toNat_sub_of_le _ _ h_le, h_q_minus_one]
        omega
      have h_inner_unfold :
          schoolbookDivModLimbs.addback r.1 b loA loB n (q - 1) (!r.2) 1 h_r_hyp hB
            = schoolbookDivModLimbs.addback r'.1 b loA loB n (q - 1 - 1) (!r'.2) 0 h_r'_hyp hB := by
        rw [hr2_false]
        simp only [Bool.not_false]
        conv_lhs => rw [schoolbookDivModLimbs.addback]
        simp only [if_true, ← hr'_def]
      have h_inner_inner :
          schoolbookDivModLimbs.addback r'.1 b loA loB n (q - 1 - 1) (!r'.2) 0 h_r'_hyp hB
            = (r'.1, q - 1 - 1) := by
        rw [schoolbookDivModLimbs.addback]
      have h_res_eq : schoolbookDivModLimbs.addback a b loA loB n q borrow 2 hA hB = (r'.1, q - 1 - 1) := by
        rw [show borrow = true from h_borrow, h_unfold1, h_inner_unfold, h_inner_inner]
      rw [h_res_eq]
      simp only
      -- Goal: r'.1.low < Z.
      -- From h_addSame' and hr2_false: r'.1.low + r'.2 * β^n = r.1.low + Z.
      -- From h_addSame with hr2_false: r.1.low = Y + Z, so r.1.low + Z = Y + 2*Z.
      rw [hr2_false] at h_addSame
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h_addSame
      rw [h_addSame] at h_addSame'
      -- h_addSame' : r'.1.low + r'.2 * β^n = Y + 2*Z.
      -- We need to show b_out = false, which means r'.2 = true (the LAST addback
      -- overflowed). Use h_eq to derive this.
      -- Actually, b_out = !r'.2 in this subcase. h_bout : b_out = false ⟹ r'.2 = true.
      -- We need to extract this from h_eq.
      rw [h_res_eq] at h_eq
      simp only at h_eq
      rw [h_borrow] at h_eq
      simp only [Bool.toNat_true, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h_eq
      rw [h_q_minus_two] at h_eq
      have h_q_split : q.toNat * Z = (q.toNat - 2) * Z + 2 * Z := by
        have h_q_eq : q.toNat = (q.toNat - 2) + 2 := by omega
        conv_lhs => rw [h_q_eq]
        rw [Nat.add_mul]
      -- h_eq : r'.1.low + (1 - b_out.toNat) * β^n + (q - 2) * Z = Y + q * Z.
      -- With b_out = false: r'.1.low + β^n + (q - 2) * Z = Y + q * Z.
      -- I.e., r'.1.low + β^n = Y + 2*Z. Combined with h_addSame': r'.2 * β^n = β^n, so r'.2 = true.
      rw [h_bout] at h_eq
      simp only [Bool.toNat_false, Nat.sub_zero, Nat.one_mul] at h_eq
      -- h_eq : r'.1.low + β^n + (q - 2) * Z = Y + q * Z.
      -- Combined with h_q_split: r'.1.low + β^n = Y + 2*Z.
      have h_r'_eq : toNatLimbsList ((r'.1.toList.drop loA).take n) + 2 ^ (64 * n) = Y + 2 * Z := by
        have h2Z : Y + Z + Z = Y + 2 * Z := by ring
        omega
      -- Goal: r'.1.low < Z.
      -- r'.1.low + β^n = Y + 2*Z. r'.1.low = Y + 2*Z - β^n.
      -- Need: Y + 2*Z - β^n < Z, i.e., Y + Z < β^n. ✓ (from h_lt_first).
      omega

/-! ### Structural lemmas for `schoolbookDivModLimbs.go` -/

/-- `schoolbookDivModLimbs.go` preserves the prefix of `a` up to `loA`. -/
theorem schoolbookDivModLimbs.go_toList_take (a b : Array UInt64) (loA loB n j : Nat)
    (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    (schoolbookDivModLimbs.go a b loA loB n j bn1 inv hA hB h_n_pos).toList.take loA
      = a.toList.take loA := by
  induction j generalizing a with
  | zero => rw [schoolbookDivModLimbs.go]
  | succ j ih =>
    rw [schoolbookDivModLimbs.go]
    rw [ih]
    rw [Array.toList_set, List.take_set_of_le (by omega : loA ≤ loA + n + j)]
    rw [schoolbookDivModLimbs.addback_toList_take_le _ _ _ _ _ _ _ _ _ _ loA
          (Nat.le_add_right _ _)]
    exact subMulLimbs_toList_take_le a b (loA + j) loB n _ _ hB loA
      (Nat.le_add_right _ _)

/-- `schoolbookDivModLimbs.addback` preserves any suffix from `loA + n` onward. -/
theorem schoolbookDivModLimbs.addback_toList_drop_ge (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : loA + n ≤ m0) :
    (schoolbookDivModLimbs.addback a b loA loB n q borrow fuel hA hB).1.toList.drop m0
      = a.toList.drop m0 := by
  have h_drop_split : ∀ (l : List UInt64),
      l.drop m0 = (l.drop (loA + n)).drop (m0 - (loA + n)) := fun l => by
    rw [List.drop_drop, Nat.add_sub_cancel' hm]
  rw [h_drop_split, schoolbookDivModLimbs.addback_toList_drop, ← h_drop_split]

/-- `schoolbookDivModLimbs.go` preserves the suffix of `a` from `loA + n + j`. -/
theorem schoolbookDivModLimbs.go_toList_drop (a b : Array UInt64) (loA loB n j : Nat)
    (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    (schoolbookDivModLimbs.go a b loA loB n j bn1 inv hA hB h_n_pos).toList.drop (loA + n + j)
      = a.toList.drop (loA + n + j) := by
  induction j generalizing a with
  | zero => rw [schoolbookDivModLimbs.go]
  | succ j ih =>
    rw [schoolbookDivModLimbs.go]
    -- After body: a' is the array passed to recursive `go ... j`.
    -- IH gives drop at (loA + n + j); we want drop at (loA + n + (j + 1)).
    have h_split : ∀ (l : List UInt64),
        l.drop (loA + n + (j + 1)) = (l.drop (loA + n + j)).drop 1 := fun l => by
      rw [List.drop_drop]
      congr 1
    rw [h_split, ih, ← h_split]
    -- a' = (addback (subMulLimbs ...).1 ...).1.set (loA + n + j) ...
    rw [Array.toList_set, List.drop_set,
        if_pos (by omega : loA + n + j < loA + n + (j + 1))]
    rw [schoolbookDivModLimbs.addback_toList_drop_ge _ _ (loA + j) _ _ _ _ _ _ _
          (loA + n + (j + 1)) (by omega)]
    rw [show loA + n + (j + 1) = (loA + j) + n + 1 from by ring]
    exact subMulLimbs_toList_drop a b (loA + j) loB n _ (by omega) hB

end Azurite.AzNat
