import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.SubMulLimbs

namespace Azurite.AzNat

/-! ### Correctness of `schoolbookDivMod.addback` -/

/-- `schoolbookDivMod.addback` preserves any prefix up to `loA`. -/
theorem schoolbookDivMod.addback_toList_take_le (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : m0 ≤ loA) :
    (schoolbookDivMod.addback a b loA loB n q borrow fuel hA hB).1.toList.take m0
      = a.toList.take m0 := by
  induction fuel generalizing a q borrow with
  | zero => rw [schoolbookDivMod.addback]
  | succ fuel' ih =>
    rw [schoolbookDivMod.addback]
    by_cases hb : borrow
    · simp only [hb, ↓reduceIte]
      rw [ih]
      show (addSameLengthLimbs a b loA loB n hA hB).1.toList.take m0 = a.toList.take m0
      exact addSameLengthLimbs.go_toList_take_le b loA loB n a 0 false hA hB m0
        (Nat.le_trans hm (Nat.le_add_right _ _))
    · simp [hb]

/-- `schoolbookDivMod.addback` preserves the prefix of `a` up to `loA`. -/
theorem schoolbookDivMod.addback_toList_take (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivMod.addback a b loA loB n q borrow fuel hA hB).1.toList.take loA
      = a.toList.take loA :=
  schoolbookDivMod.addback_toList_take_le a b loA loB n q borrow fuel hA hB loA
    (Nat.le_refl _)

/-- `schoolbookDivMod.addback` preserves the suffix of `a` from `loA + n`. -/
theorem schoolbookDivMod.addback_toList_drop (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (schoolbookDivMod.addback a b loA loB n q borrow fuel hA hB).1.toList.drop (loA + n)
      = a.toList.drop (loA + n) := by
  induction fuel generalizing a q borrow with
  | zero => rw [schoolbookDivMod.addback]
  | succ fuel' ih =>
    rw [schoolbookDivMod.addback]
    by_cases hb : borrow
    · simp only [hb, ↓reduceIte]
      rw [ih]
      show (addSameLengthLimbs a b loA loB n hA hB).1.toList.drop (loA + n)
        = a.toList.drop (loA + n)
      exact addSameLengthLimbs.go_toList_drop b loA loB n a 0 false hA hB
    · simp [hb]

/-- Correctness of `schoolbookDivMod.addback`: the value of the `n`-limb slice
    plus a carry-flag-encoded high bit, plus `q * B`, is preserved. The
    precondition `borrow = true → fuel ≤ q.toNat` ensures `q` does not wrap
    around through `0` during the addback iterations. -/
theorem schoolbookDivMod.addback_toNat (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (hq : borrow = true → fuel ≤ q.toNat) :
    let res := schoolbookDivMod.addback a b loA loB n q borrow fuel hA hB
    ∃ b_out : Bool,
      toNatLimbsList ((res.1.toList.drop loA).take n)
        + (1 - b_out.toNat) * 2 ^ (64 * n)
        + res.2.toNat * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((a.toList.drop loA).take n)
        + (1 - borrow.toNat) * 2 ^ (64 * n)
        + q.toNat * toNatLimbsList ((b.toList.drop loB).take n) := by
  induction fuel generalizing a q borrow with
  | zero =>
    rw [schoolbookDivMod.addback]
    exact ⟨borrow, rfl⟩
  | succ fuel' ih =>
    rw [schoolbookDivMod.addback]
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

/-! ### Structural lemmas for `schoolbookDivMod.go` -/

/-- `schoolbookDivMod.go` preserves the prefix of `a` up to `loA`. -/
theorem schoolbookDivMod.go_toList_take (a b : Array UInt64) (loA loB n j : Nat)
    (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    (schoolbookDivMod.go a b loA loB n j bn1 inv hA hB h_n_pos).toList.take loA
      = a.toList.take loA := by
  induction j generalizing a with
  | zero => rw [schoolbookDivMod.go]
  | succ j ih =>
    rw [schoolbookDivMod.go]
    rw [ih]
    rw [Array.toList_set, List.take_set_of_le (by omega : loA ≤ loA + n + j)]
    rw [schoolbookDivMod.addback_toList_take_le _ _ _ _ _ _ _ _ _ _ loA
          (Nat.le_add_right _ _)]
    exact subMulLimbs_toList_take_le a b (loA + j) loB n _ _ hB loA
      (Nat.le_add_right _ _)

/-- `schoolbookDivMod.addback` preserves any suffix from `loA + n` onward. -/
theorem schoolbookDivMod.addback_toList_drop_ge (a b : Array UInt64) (loA loB n : Nat)
    (q : UInt64) (borrow : Bool) (fuel : Nat)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : loA + n ≤ m0) :
    (schoolbookDivMod.addback a b loA loB n q borrow fuel hA hB).1.toList.drop m0
      = a.toList.drop m0 := by
  have h_drop_split : ∀ (l : List UInt64),
      l.drop m0 = (l.drop (loA + n)).drop (m0 - (loA + n)) := fun l => by
    rw [List.drop_drop, Nat.add_sub_cancel' hm]
  rw [h_drop_split, schoolbookDivMod.addback_toList_drop, ← h_drop_split]

/-- `schoolbookDivMod.go` preserves the suffix of `a` from `loA + n + j`. -/
theorem schoolbookDivMod.go_toList_drop (a b : Array UInt64) (loA loB n j : Nat)
    (bn1 inv : UInt64)
    (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size) (h_n_pos : 0 < n) :
    (schoolbookDivMod.go a b loA loB n j bn1 inv hA hB h_n_pos).toList.drop (loA + n + j)
      = a.toList.drop (loA + n + j) := by
  induction j generalizing a with
  | zero => rw [schoolbookDivMod.go]
  | succ j ih =>
    rw [schoolbookDivMod.go]
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
    rw [schoolbookDivMod.addback_toList_drop_ge _ _ (loA + j) _ _ _ _ _ _ _
          (loA + n + (j + 1)) (by omega)]
    rw [show loA + n + (j + 1) = (loA + j) + n + 1 from by ring]
    exact subMulLimbs_toList_drop a b (loA + j) loB n _ (by omega) hB

end Azurite.AzNat
