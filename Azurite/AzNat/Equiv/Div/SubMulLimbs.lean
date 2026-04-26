import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic
import Azurite.UInt64.Equiv.MulWithCarry
import Azurite.UInt64.Equiv.SubWithBorrow

namespace Azurite.AzNat

/-! ### Correctness of `subMulLimbs` -/

/-- `subMulLimbs.go` preserves any prefix up to `loA + k`. -/
theorem subMulLimbs.go_toList_take_le (b : Array UInt64) (loB n : Nat) (q : UInt64)
    (a : Array UInt64) (loA k : Nat) (mulCarry : UInt64) (subBorrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size)
    (m : Nat) (hm : m ≤ loA + k) :
    (subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).1.toList.take m
      = a.toList.take m := by
  induction h_sub : n - k generalizing a k mulCarry subBorrow with
  | zero =>
    have h_ge : n ≤ k := by omega
    rw [subMulLimbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ p ih =>
    have h_lt : k < n := by omega
    have h_rec : n - (k + 1) = p := by omega
    rw [subMulLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ _ (by omega) h_rec]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `subMulLimbs.go` preserves the prefix of `a` up to `loA + k`. -/
theorem subMulLimbs.go_toList_take (b : Array UInt64) (loB n : Nat) (q : UInt64)
    (a : Array UInt64) (loA k : Nat) (mulCarry : UInt64) (subBorrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).1.toList.take (loA + k)
      = a.toList.take (loA + k) :=
  subMulLimbs.go_toList_take_le b loB n q a loA k mulCarry subBorrow hA hB
    (loA + k) (Nat.le_refl _)

/-- `subMulLimbs.go` preserves the suffix of `a` from `loA + n`. -/
theorem subMulLimbs.go_toList_drop (b : Array UInt64) (loB n : Nat) (q : UInt64)
    (a : Array UInt64) (loA k : Nat) (mulCarry : UInt64) (subBorrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).1.toList.drop (loA + n)
      = a.toList.drop (loA + n) := by
  induction h_sub : n - k generalizing a k mulCarry subBorrow with
  | zero =>
    have h_ge : n ≤ k := by omega
    rw [subMulLimbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ p ih =>
    have h_lt : k < n := by omega
    rw [subMulLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    have h_rec : n - (k + 1) = p := by omega
    rw [ih _ _ _ _ _ h_rec]
    rw [Array.toList_set, List.drop_set]
    simp
    omega

/-- Invariant of `subMulLimbs.go` at step `k`. The slice from position `loA + k`
    of length `n - k`, with the final mul-carry and sub-borrow promoted to
    position `loA + n`, equals the modified slice plus `q * (b-slice)` plus the
    input mul-carry and sub-borrow. -/
private lemma subMulLimbs.go_correct (b : Array UInt64) (loB n : Nat) (q : UInt64)
    (a : Array UInt64) (loA k : Nat) (mulCarry : UInt64) (subBorrow : Bool)
    (hA : loA + n ≤ a.size) (hB : loB + n ≤ b.size) :
    toNatLimbsList ((a.toList.drop (loA + k)).take (n - k))
        + ((subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).2.1.toNat
            + (subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).2.2.toNat)
          * 2 ^ (64 * (n - k))
      = toNatLimbsList
          (((subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB).1.toList.drop
              (loA + k)).take (n - k))
        + q.toNat * toNatLimbsList ((b.toList.drop (loB + k)).take (n - k))
        + (mulCarry.toNat + subBorrow.toNat) := by
  induction h_sub : n - k generalizing a k mulCarry subBorrow with
  | zero =>
    have h_ge : n ≤ k := by omega
    have h_eq : subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB
              = (a, mulCarry, subBorrow) := by
      rw [subMulLimbs.go]; simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ p ih =>
    have h_lt : k < n := by omega
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    set mc := UInt64.mulWithCarry b[loB + k] q mulCarry with hmc_def
    set swb := UInt64.subWithBorrow a[loA + k] mc.2 subBorrow with hswb_def
    set diff := swb.1 with hdiff_def
    set newBorrow := swb.2 with hnb_def
    set newMulCarry := mc.1 with hnmc_def
    set a' := a.set (loA + k) diff with ha'_def
    have hA' : loA + n ≤ a'.size := by rw [ha'_def, Array.size_set]; exact hA
    have h_eq : subMulLimbs.go b loB n q a loA k mulCarry subBorrow hA hB
              = subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB := by
      conv_lhs => rw [subMulLimbs.go]
      simp [h_lt, hmc_def, hswb_def, hdiff_def, hnb_def, hnmc_def, ha'_def]
    have h_rec : n - (k + 1) = p := by omega
    have h_ih := ih a' (k + 1) newMulCarry newBorrow hA' h_rec
    have h_mc := UInt64.mulWithCarry_eq b[loB + k] q mulCarry
    rw [← hmc_def] at h_mc
    have h_swb_raw := UInt64.subWithBorrow_eq a[loA + k] mc.2 subBorrow
    rw [← hswb_def] at h_swb_raw
    -- Convert if-then-else to Bool.toNat.
    have h_subBorrow : subBorrow.toNat = (if subBorrow then 1 else 0 : Nat) := by
      cases subBorrow <;> simp
    have h_newBorrow : newBorrow.toNat = (if newBorrow then 1 else 0 : Nat) := by
      cases newBorrow <;> simp
    have h_swb : diff.toNat + mc.2.toNat + subBorrow.toNat
                = a[loA + k].toNat + newBorrow.toNat * 2 ^ 64 := by
      rw [h_subBorrow, h_newBorrow]; exact h_swb_raw
    have h_res_size : (subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry
                          newBorrow hA' hB).1.size = a.size := by
      rw [subMulLimbs.go_size, ha'_def, Array.size_set]
    have h_res_iA_size : loA + k <
        (subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB).1.size := by
      rw [h_res_size]; exact h_iA
    -- Final value at position loA + k is preserved as `diff`.
    have h_res_i :
        (subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry
            newBorrow hA' hB).1[loA + k]'h_res_iA_size = diff := by
      have h_prefix :=
        subMulLimbs.go_toList_take b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB
      have h_len_L : ((subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry
                        newBorrow hA' hB).1.toList).length = a.size := by
        rw [Array.length_toList]; exact h_res_size
      have h_i_lt_L_take :
          loA + k < ((subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry
                        newBorrow hA' hB).1.toList.take (loA + (k + 1))).length := by
        rw [List.length_take, h_len_L]; omega
      have h_i_lt_R_take : loA + k < (a'.toList.take (loA + (k + 1))).length := by
        rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
      have h_get_eq :
          ((subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry
              newBorrow hA' hB).1.toList.take (loA + (k + 1)))[loA + k]'h_i_lt_L_take
            = (a'.toList.take (loA + (k + 1)))[loA + k]'h_i_lt_R_take := by
        congr 1
      rw [List.getElem_take, List.getElem_take] at h_get_eq
      rw [← Array.getElem_toList h_res_iA_size, h_get_eq]
      have h_i_lt : loA + k < (a.set (loA + k) diff h_iA).toList.length := by
        rw [Array.length_toList, Array.size_set]; exact h_iA
      show (a.set (loA + k) diff h_iA).toList[loA + k]'h_i_lt = diff
      simp [Array.toList_set, List.getElem_set_self]
    have h_drop_eq : a'.toList.drop (loA + (k + 1)) = a.toList.drop (loA + (k + 1)) := by
      rw [ha'_def, Array.toList_set, List.drop_set]; simp
    rw [h_eq]
    have split_arr : ∀ (A : Array UInt64) (i m : Nat) (hi_size : i < A.size),
        toNatLimbsList ((A.toList.drop i).take (m + 1))
          = A[i].toNat + toNatLimbsList ((A.toList.drop (i + 1)).take m) * 2 ^ 64 := by
      intro A i m hi_size
      have h_lt_list : i < A.toList.length := hi_size
      rw [List.drop_eq_getElem_cons h_lt_list, List.take_succ_cons, toNatLimbsList_cons]
      rw [show A.toList[i] = A[i] from (Array.getElem_toList hi_size).symm]
      ring
    have h_len_split : n - k = (n - (k + 1)) + 1 := by omega
    rw [show p + 1 = n - k from h_sub.symm, h_len_split]
    rw [split_arr (subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB).1
                  (loA + k) (n - (k + 1)) h_res_iA_size]
    rw [h_res_i]
    rw [split_arr a (loA + k) (n - (k + 1)) h_iA]
    rw [split_arr b (loB + k) (n - (k + 1)) h_iB]
    have h_pow : (2 : Nat) ^ (64 * ((n - (k + 1)) + 1))
                = 2 ^ (64 * (n - (k + 1))) * 2 ^ 64 := by
      rw [show 64 * ((n - (k + 1)) + 1) = 64 * (n - (k + 1)) + 64 from by ring, Nat.pow_add]
    rw [h_pow]
    rw [show loA + k + 1 = loA + (k + 1) from by ring]
    rw [show loB + k + 1 = loB + (k + 1) from by ring]
    rw [← h_drop_eq]
    rw [← h_rec] at h_ih
    set P := toNatLimbsList ((a'.toList.drop (loA + (k + 1))).take (n - (k + 1))) with hP_def
    set Q := toNatLimbsList
        (((subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB).1.toList.drop
            (loA + (k + 1))).take (n - (k + 1))) with hQ_def
    set S := toNatLimbsList ((b.toList.drop (loB + (k + 1))).take (n - (k + 1))) with hS_def
    set R := (subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB).2.1.toNat
            + (subMulLimbs.go b loB n q a' loA (k + 1) newMulCarry newBorrow hA' hB).2.2.toNat
            with hR_def
    -- After substitutions, the goal should be:
    --   a[loA + k].toNat + P * 2^64 + R * (2^(64*(n-(k+1))) * 2^64)
    --   = diff.toNat + Q * 2^64 + q.toNat * (b[loB + k].toNat + S * 2^64)
    --     + (mulCarry.toNat + subBorrow.toNat)
    change a[loA + k].toNat + P * 2 ^ 64 + R * (2 ^ (64 * (n - (k + 1))) * 2 ^ 64)
        = diff.toNat + Q * 2 ^ 64
          + q.toNat * (b[loB + k].toNat + S * 2 ^ 64)
          + (mulCarry.toNat + subBorrow.toNat)
    -- IH: P + R * 2^(64*(n-(k+1))) = Q + q.toNat * S + (newMulCarry.toNat + newBorrow.toNat)
    -- h_mc: newMulCarry.toNat * 2^64 + mc.2.toNat = b[loB+k].toNat * q.toNat + mulCarry.toNat
    -- h_swb: diff.toNat + mc.2.toNat + subBorrow.toNat = a[loA+k].toNat + newBorrow.toNat * 2^64
    linear_combination (2 ^ 64) * h_ih + h_mc - h_swb

/-- `subMulLimbs` preserves any prefix up to `loA`. -/
theorem subMulLimbs_toList_take_le (a b : Array UInt64) (loA loB n : Nat) (q : UInt64)
    (hA : loA + n + 1 ≤ a.size) (hB : loB + n ≤ b.size)
    (m0 : Nat) (hm : m0 ≤ loA) :
    (subMulLimbs a b loA loB n q hA hB).1.toList.take m0 = a.toList.take m0 := by
  unfold subMulLimbs
  simp only []
  rw [Array.toList_set, List.take_set_of_le (Nat.le_trans hm (Nat.le_add_right _ _))]
  exact subMulLimbs.go_toList_take_le b loB n q a loA 0 0 false (by omega) hB m0
    (Nat.le_trans hm (Nat.le_add_right _ _))

/-- `subMulLimbs` preserves the suffix of `a` from `loA + n + 1`. -/
theorem subMulLimbs_toList_drop (a b : Array UInt64) (loA loB n : Nat) (q : UInt64)
    (hA : loA + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMulLimbs a b loA loB n q hA hB).1.toList.drop (loA + n + 1)
      = a.toList.drop (loA + n + 1) := by
  unfold subMulLimbs
  simp only []
  rw [Array.toList_set, List.drop_set, if_pos (Nat.lt_succ_self _)]
  have h_go_drop := subMulLimbs.go_toList_drop b loB n q a loA 0 0 false (by omega) hB
  have h_drop_split : ∀ (l : List UInt64),
      l.drop (loA + n + 1) = (l.drop (loA + n)).drop 1 := fun l => by
    rw [List.drop_drop]
  simp only [h_drop_split, h_go_drop]

/-- Correctness of `subMulLimbs`: the modified array contains the difference
    `a-slice - q * b-slice` in the low `n+1` limbs, with the final boolean
    indicating whether the multi-precision result went negative. -/
theorem subMulLimbs_toNat (a b : Array UInt64) (loA loB n : Nat) (q : UInt64)
    (hA : loA + n + 1 ≤ a.size) (hB : loB + n ≤ b.size) :
    toNatLimbsList ((a.toList.drop loA).take (n + 1))
      + (subMulLimbs a b loA loB n q hA hB).2.toNat * 2 ^ (64 * (n + 1))
      = toNatLimbsList
          (((subMulLimbs a b loA loB n q hA hB).1.toList.drop loA).take (n + 1))
        + q.toNat * toNatLimbsList ((b.toList.drop loB).take n) := by
  unfold subMulLimbs
  set r := subMulLimbs.go b loB n q a loA 0 0 false (by omega) hB with hr_def
  have h_r_size : r.1.size = a.size := by
    rw [hr_def]; exact subMulLimbs.go_size _ _ _ _ _ _ _ _ _ _ _
  have h_top_idx : loA + n < r.1.size := by rw [h_r_size]; omega
  set topVal := r.1[loA + n]'h_top_idx with htop_def
  set swb := UInt64.subWithBorrow topVal r.2.1 r.2.2 with hswb_def
  -- Inner invariant from go_correct (n - 0 = n, drop 0 is identity).
  have h_inner := subMulLimbs.go_correct b loB n q a loA 0 0 false (by omega) hB
  rw [← hr_def] at h_inner
  simp only [Nat.add_zero, Nat.sub_zero, Bool.toNat_false,
    show (0 : UInt64).toNat = 0 from rfl] at h_inner
  -- h_inner: ToNat(a[loA, loA+n)) + (r.2.1.toNat + r.2.2.toNat) * 2^(64n)
  --        = ToNat(r.1[loA, loA+n)) + q * ToNat(b[loB, loB+n)) + 0
  have h_iA_top : loA + n < a.size := by omega
  have split_arr : ∀ (A : Array UInt64) (i m : Nat) (hi_size : i + m < A.size),
      toNatLimbsList ((A.toList.drop i).take (m + 1))
        = toNatLimbsList ((A.toList.drop i).take m)
          + (A[i + m]'hi_size).toNat * 2 ^ (64 * m) := fun A i m hi_size =>
    toNatLimbsList_drop_take_succ A i m hi_size
  rw [split_arr a loA n h_iA_top]
  -- Goal now uses (r.1.set (loA + n) swb.1, swb.2). Show this directly.
  show toNatLimbsList ((a.toList.drop loA).take n)
        + (a[loA + n]'h_iA_top).toNat * 2 ^ (64 * n)
        + swb.2.toNat * 2 ^ (64 * (n + 1))
      = toNatLimbsList (((r.1.set (loA + n) swb.1).toList.drop loA).take (n + 1))
        + q.toNat * toNatLimbsList ((b.toList.drop loB).take n)
  -- Decompose set-array slice using split_arr.
  have h_set_size : (r.1.set (loA + n) swb.1).size = a.size := by
    rw [Array.size_set]; exact h_r_size
  have h_set_top : loA + n < (r.1.set (loA + n) swb.1).size := by rw [h_set_size]; omega
  rw [toNatLimbsList_drop_take_succ (r.1.set (loA + n) swb.1) loA n h_set_top]
  have h_take_unchanged :
      ((r.1.set (loA + n) swb.1).toList.drop loA).take n
        = (r.1.toList.drop loA).take n := by
    rw [Array.toList_set, List.drop_set]
    by_cases hlt : loA + n < loA
    · omega
    · simp only [hlt, ↓reduceIte]
      rw [List.take_set_of_le (by omega)]
  rw [h_take_unchanged]
  have h_get_set : (r.1.set (loA + n) swb.1)[loA + n]'h_set_top = swb.1 :=
    Array.getElem_set_self _
  rw [h_get_set]
  -- subWithBorrow_eq for the top adjustment.
  have h_subBorrow_top : r.2.2.toNat = (if r.2.2 then 1 else 0 : Nat) := by
    cases r.2.2 <;> simp
  have h_swb_top : swb.2.toNat = (if swb.2 then 1 else 0 : Nat) := by
    cases swb.2 <;> simp
  have h_swb_eq_raw := UInt64.subWithBorrow_eq topVal r.2.1 r.2.2
  rw [← hswb_def] at h_swb_eq_raw
  have h_swb_eq : swb.1.toNat + r.2.1.toNat + r.2.2.toNat
                = topVal.toNat + swb.2.toNat * 2 ^ 64 := by
    rw [h_subBorrow_top, h_swb_top]; exact h_swb_eq_raw
  -- Use suffix preservation to identify a[loA+n] = topVal = r.1[loA+n].
  have h_drop_n : r.1.toList.drop (loA + n) = a.toList.drop (loA + n) := by
    rw [hr_def]
    exact subMulLimbs.go_toList_drop b loB n q a loA 0 0 false (by omega) hB
  have h_anh : (a[loA + n]'h_iA_top).toNat = topVal.toNat := by
    rw [htop_def]
    have h_a_get : a[loA + n]'h_iA_top = (a.toList.drop (loA + n))[0]'(by
      rw [List.length_drop, Array.length_toList]; omega) := by
      rw [List.getElem_drop]; exact (Array.getElem_toList _).symm
    have h_r_get : r.1[loA + n]'h_top_idx = (r.1.toList.drop (loA + n))[0]'(by
      rw [List.length_drop, Array.length_toList, h_r_size]; omega) := by
      rw [List.getElem_drop]; exact (Array.getElem_toList _).symm
    rw [h_a_get, h_r_get]
    congr 1
    exact List.getElem_of_eq h_drop_n.symm _
  rw [h_anh]
  set X := toNatLimbsList ((a.toList.drop loA).take n) with hX_def
  set Y := toNatLimbsList ((r.1.toList.drop loA).take n) with hY_def
  set Z := toNatLimbsList ((b.toList.drop loB).take n) with hZ_def
  -- Reformulate h_inner in terms of X, Y, Z.
  have h_inner_eq : X + (r.2.1.toNat + r.2.2.toNat) * 2 ^ (64 * n)
                  = Y + q.toNat * Z := by
    have := h_inner
    show X + (r.2.1.toNat + r.2.2.toNat) * 2 ^ (64 * n) = Y + q.toNat * Z
    linarith
  have h_pow_succ : (2 : Nat) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    rw [show 64 * (n + 1) = 64 * n + 64 from by ring, Nat.pow_add]
  rw [h_pow_succ]
  -- Goal: X + topVal * β^n + swb.2 * β^n * β^64 = Y + swb.1 * β^n + q*Z
  -- h_inner_eq: X + (r.2.1 + r.2.2) * β^n = Y + q*Z
  -- h_swb_eq: swb.1 + r.2.1 + r.2.2 = topVal + swb.2 * β^64
  -- Multiply h_swb_eq by β^n: swb.1*β^n + (r.2.1+r.2.2)*β^n = topVal*β^n + swb.2*β^n*β^64
  -- Combining: goal follows.
  linear_combination h_inner_eq - 2 ^ (64 * n) * h_swb_eq

end Azurite.AzNat
