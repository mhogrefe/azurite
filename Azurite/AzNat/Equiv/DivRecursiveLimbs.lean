import Azurite.AzNat.DivRecursiveLimbs
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Div.Schoolbook
import Azurite.AzNat.Equiv.Div.DivModLimb2
import Azurite.AzNat.Equiv.Mul.ToomCook3

namespace Azurite.AzNat

/-!
## `toNat`-level correctness of slice-level `recursiveDivModLimbsAux`

This file proves the spec for the slice-style recursive divrem
defined in `DivRecursiveLimbs.lean`.  The spec mirrors
`schoolbookDivModLimbs_toNat`:

  Let `a`, `b` be limb arrays with `a[loA, loA+n+m)` the dividend,
  `b[loB, loB+n)` the (normalized) divisor.  After
  `recursiveDivModLimbsAux ... = (a', q_top)`:
    1. `a'[loA, loA+n)` (as toNat) is the remainder, `< b[loB, loB+n)`.
    2. The original dividend equals
       `((q_top * β^m + a'[loA+n, loA+n+m)) * b[loB, loB+n)) + a'[loA, loA+n)`.

The main results are:
  - `recursiveDivModLimbsAux_spec`: correctness of the core recursive
    helper, covering the base case, the chunking branch, and the
    divide-and-conquer branch (via `dc_full_bookkeeping` and the
    `afterFirstRec`/`afterSecondRec` conservation lemmas).
  - `recursiveDivModLimbsAux_preserves_outside`: array locations outside
    the dividend window are unchanged by the algorithm.
  - `recursiveDivModFast_toNat`: correctness of the AzNat-level wrapper.

Supporting lemmas proved in this file:
  - `sliceVal_split`, `sliceVal_eq_of_getElem_eq`, `sliceVal_divisor_bound`
  - `q_top_le_one_of_spec`, `chunking_algebra`
  - `writeSlice_get_inside`, `writeSlice_sliceVal`,
    `Array.replicate_sliceVal_zero`
  - `recursiveDivModLimbs.afterFirstRec_toNat`,
    `recursiveDivModLimbs.afterSecondRec_subAddback_toNat`,
    `recursiveDivModLimbs.afterSecondRec_assembly_toNat`

Dependencies from other files:
  - `addLimb_get_below/above`, `addSameLengthLimbs_get_outside`,
    `addGeqLimbs_get_outside` (in `AzNat/Add.lean`)
  - `subLimb_get_below/above`, `subSameLengthLimbs_get_outside`,
    `subGeqLimbs_get_outside` (in `AzNat/Sub.lean`)
  - `zeroFill_get_outside`, `writeSlice_get_outside`,
    `addbackLoop_get_outside`, `afterFirstRec_get_outside`,
    `afterSecondRec_get_outside` (in `AzNat/DivRecursiveLimbs.lean`)
  - `schoolbookDivModLimbs_toList_take`/`drop`/`_getElem_outside`
    (in `Equiv/Div/Schoolbook.lean`)
-/

/-! ### Pure-Nat helpers (moved from Equiv.DivRecursive) -/

/-- If `Q * B ≤ b`, `2^q ≤ B`, and `b < 2^p` with `q ≤ p`, then
    `Q < 2^(p − q)`. -/
lemma pow_quotient_lt (Q B b p q : Nat)
    (h_QB : Q * B ≤ b) (h_2q_le_B : 2 ^ q ≤ B)
    (h_b_lt : b < 2 ^ p) (h_qp : q ≤ p) : Q < 2 ^ (p - q) := by
  have h_Q_pow_q_le : Q * 2 ^ q ≤ b := by
    calc Q * 2 ^ q ≤ Q * B := Nat.mul_le_mul_left Q h_2q_le_B
      _ ≤ b := h_QB
  have h_Q_pow_q_lt : Q * 2 ^ q < 2 ^ p := lt_of_le_of_lt h_Q_pow_q_le h_b_lt
  have h_pow_eq : (2 : Nat) ^ p = 2 ^ (p - q) * 2 ^ q := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h_pow_eq] at h_Q_pow_q_lt
  exact Nat.lt_of_mul_lt_mul_right h_Q_pow_q_lt

/-- For `Q < 2 * 2^a`, `B₀ < 2^b`, and `2^(c-1) ≤ B` with `a + b ≤ c`
    and `1 ≤ c`: `Q * B₀ ≤ 4 * B`. -/
lemma quotient_low_times_le_4B (Q B₀ B a b c : Nat)
    (h_Q_lt : Q < 2 * 2 ^ a) (h_B₀_lt : B₀ < 2 ^ b)
    (h_B_ge : 2 ^ (c - 1) ≤ B) (h_abc : a + b ≤ c) (hc : 1 ≤ c) :
    Q * B₀ ≤ 4 * B := by
  have h_Q_le : Q ≤ 2 * 2 ^ a - 1 := by omega
  have h_B₀_le : B₀ ≤ 2 ^ b - 1 := by omega
  have h_mul_le : Q * B₀ ≤ (2 * 2 ^ a) * 2 ^ b := by
    calc Q * B₀ ≤ (2 * 2 ^ a - 1) * (2 ^ b - 1) := Nat.mul_le_mul h_Q_le h_B₀_le
      _ ≤ (2 * 2 ^ a) * 2 ^ b := by apply Nat.mul_le_mul <;> omega
  have h_pow_combine : (2 * 2 ^ a) * 2 ^ b = 2 * 2 ^ (a + b) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
  have h_pow_le : 2 * 2 ^ (a + b) ≤ 2 * 2 ^ c :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h_abc)
  have h_4B_eq : (4 : Nat) * 2 ^ (c - 1) = 2 * 2 ^ c := by
    have h_4 : (4 : Nat) = 2 ^ 2 := by rfl
    rw [h_4, ← Nat.pow_add]
    have h_exp : 2 + (c - 1) = c + 1 := by omega
    rw [h_exp]
    rw [Nat.pow_succ]; ring
  have h_4B : (4 : Nat) * 2 ^ (c - 1) ≤ 4 * B := Nat.mul_le_mul_left _ h_B_ge
  omega

/-- Shorthand: limb-list value of the slice `a[lo, lo+len)`. -/
@[reducible] def sliceVal (a : Array UInt64) (lo len : Nat) : Nat :=
  toNatLimbsList ((a.toList.drop lo).take len)

/-- Spec for `recursiveDivModLimbsAux`.  See file docstring for the
    informal statement. -/
structure RecursiveDivModLimbsSpec (a b : Array UInt64)
    (loA loB n m : Nat) (a' : Array UInt64) (q_top : UInt64) : Prop where
  /-- The remainder `a'[loA, loA+n)` is strictly below `b[loB, loB+n)`. -/
  rem_lt : sliceVal a' loA n < sliceVal b loB n
  /-- Dividend = Quotient × Divisor + Remainder, with quotient
      reconstructed from `(q_top, a'[loA+n, loA+n+m))`. -/
  div_eq : sliceVal a loA (n + m)
    = (q_top.toNat * 2 ^ (64 * m) + sliceVal a' (loA + n) m) * sliceVal b loB n
        + sliceVal a' loA n

/-- Conservation of `addbackLoop`: after the loop, the relevant slice's
    value has changed by `delta * B - end_carry * β^highLen`, where
    `delta = cnt` is the number of iterations executed and
    `end_carry ∈ {0, 1}` tracks whether the cumulative addition produced
    an overflow (which happens exactly when the loop terminated by
    consuming the borrow, vs. by fuel exhaustion).

    For our usage with `fuel = 5` and the MCA bound, fuel is always
    sufficient, but stating the lemma without an `end_carry` term would
    require a `fuel_sufficient` hypothesis. -/
theorem addbackLoop_toNat (a b : Array UInt64) (loA loB n k highLen : Nat)
    (borrow : Bool) (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen) :
    let res := addbackLoop a b loA loB n k highLen borrow fuel
      hA hB h_n_le h_n_pos h_high_pos
    ∃ end_carry : Nat, end_carry ≤ 1 ∧
      toNatLimbsList ((a.toList.drop (loA + k)).take highLen)
        + res.2 * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((res.1.toList.drop (loA + k)).take highLen)
        + end_carry * 2 ^ (64 * highLen) := by
  induction fuel generalizing a borrow with
  | zero =>
    refine ⟨0, by omega, ?_⟩
    unfold addbackLoop
    simp
  | succ fuel' ih =>
    unfold addbackLoop
    by_cases h_b : borrow
    · simp only [h_b, ↓reduceIte]
      set r := addGeqLimbs a b (loA + k) highLen loB n
        (by omega) hB h_n_le h_high_pos h_n_pos with hr_def
      have h_addGeq := addGeqLimbs_toNat a b (loA + k) highLen loB n
        (by omega) hB h_n_le h_high_pos h_n_pos
      simp only at h_addGeq
      rw [← hr_def] at h_addGeq
      -- h_addGeq : sliceVal r.1 (loA + k) highLen + r.2.toNat * β^highLen
      --          = sliceVal a (loA + k) highLen + sliceVal b loB n
      have h_r_size := addGeqLimbs_size a b (loA + k) highLen loB n
        (by omega) hB h_n_le h_high_pos h_n_pos
      rw [← hr_def] at h_r_size
      obtain ⟨end_carry', h_ec'_le, h_ih⟩ := ih r.1 (!r.2)
        (by rw [h_r_size]; exact hA)
      -- h_ih : sliceVal r.1 (loA + k) highLen + cnt' * B
      --      = sliceVal final.1 (loA + k) highLen + end_carry' * β^highLen
      set inner := addbackLoop r.1 b loA loB n k highLen (!r.2) fuel' _ hB
        h_n_le h_n_pos h_high_pos
      -- inner is the recursive call's result; we need ∃ end_carry, ...
      -- Case split on r.2: in the carry-out case, the next iteration's borrow
      -- is false and returns immediately, giving inner = (r.1, 0).
      rcases h_b2 : r.2 with _ | _
      all_goals first
        | (-- r.2 = false: !r.2 = true, recursive call continues; use IH.
           refine ⟨end_carry', h_ec'_le, ?_⟩
           show toNatLimbsList ((a.toList.drop (loA + k)).take highLen)
               + (inner.2 + 1) * toNatLimbsList ((b.toList.drop loB).take n)
             = toNatLimbsList ((inner.1.toList.drop (loA + k)).take highLen)
               + end_carry' * 2 ^ (64 * highLen)
           have h_B_add : (inner.2 + 1) * toNatLimbsList ((b.toList.drop loB).take n)
               = inner.2 * toNatLimbsList ((b.toList.drop loB).take n)
                 + toNatLimbsList ((b.toList.drop loB).take n) := by ring
           rw [h_B_add]
           have h_r2_zero : r.2.toNat = 0 := by rw [h_b2]; rfl
           rw [h_r2_zero] at h_addGeq
           linarith)
        | (-- r.2 = true: !r.2 = false, recursive call returns (r.1, 0) directly.
           have h_inner_eq : inner = (r.1, 0) := by
             show (addbackLoop r.1 b loA loB n k highLen (!r.2) fuel' _ _ _ _ _) = (r.1, 0)
             rw [h_b2]
             show addbackLoop r.1 b loA loB n k highLen false fuel' _ _ _ _ _ = (r.1, 0)
             cases fuel' <;> unfold addbackLoop <;> simp
           refine ⟨1, by omega, ?_⟩
           rw [show inner.1 = r.1 from by rw [h_inner_eq]]
           rw [show inner.2 = 0 from by rw [h_inner_eq]]
           have h_r2_one : r.2.toNat = 1 := by rw [h_b2]; rfl
           rw [h_r2_one] at h_addGeq
           show toNatLimbsList ((a.toList.drop (loA + k)).take highLen)
               + (0 + 1) * toNatLimbsList ((b.toList.drop loB).take n)
             = toNatLimbsList ((r.1.toList.drop (loA + k)).take highLen)
               + 1 * 2 ^ (64 * highLen)
           linarith)
    · simp only [h_b]
      refine ⟨0, by omega, ?_⟩
      simp

theorem decrementSlice_toNat (a : Array UInt64) (lo : Nat) (d : Nat)
    (hlo : lo ≤ a.size) (h_pos : lo < a.size) :
    toNatLimbsList ((a.toList.drop lo).take (a.size - lo))
        + (subLimb a lo a.size (UInt64.ofNat d) hlo (Nat.le_refl _)).2.toNat
          * 2 ^ (64 * (a.size - lo))
      = toNatLimbsList (((decrementSlice a lo d hlo).toList.drop lo).take
          (a.size - lo)) + (UInt64.ofNat d).toNat := by
  unfold decrementSlice
  exact subLimb_toNat a lo a.size (UInt64.ofNat d) hlo (Nat.le_refl _) h_pos

/-- When `d ≤ val` and `d < 2^64`, decrementing `a` at offset `lo = 0` by `d`
    gives a slice value of `val - d`. -/
theorem decrementSlice_val_eq (a : Array UInt64) (d : Nat)
    (h_pos : 0 < a.size)
    (h_d_lt : d < 2 ^ 64)
    (h_d_le : d ≤ toNatLimbsList ((a.toList.drop 0).take (a.size - 0))) :
    toNatLimbsList (((decrementSlice a 0 d (Nat.zero_le _)).toList.drop 0).take
        (a.size - 0))
      = toNatLimbsList ((a.toList.drop 0).take (a.size - 0)) - d := by
  have h_dec := decrementSlice_toNat a 0 d (Nat.zero_le _) h_pos
  have h_d_u64 : (UInt64.ofNat d).toNat = d := by
    show d % UInt64.size = d
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_d_u64] at h_dec
  -- h_dec: original + borrow * β^len = decremented + d
  set borrow := (subLimb a 0 a.size (UInt64.ofNat d) (Nat.zero_le _) (Nat.le_refl _)).2.toNat
    with h_borrow_def
  have h_borrow_le : borrow ≤ 1 := by
    simp only [h_borrow_def]
    cases (subLimb a 0 a.size (UInt64.ofNat d) _ _).2 <;> simp
  -- Show borrow = 0 from d ≤ original.
  -- If borrow ≥ 1: from h_dec, original + β^len ≤ original + borrow * β^len = decremented + d.
  -- So decremented ≥ original + β^len - d ≥ β^len (since d ≤ original).
  -- But decremented < β^len (it's a slice of len limbs). Contradiction.
  have h_borrow_zero : borrow = 0 := by
    by_contra h_ne
    have h_b1 : borrow ≥ 1 := by omega
    -- decremented + d = original + borrow * β^len ≥ original + β^len
    have h_lower : toNatLimbsList (((decrementSlice a 0 d (Nat.zero_le _)).toList.drop 0).take
        (a.size - 0)) + d
        ≥ toNatLimbsList ((a.toList.drop 0).take (a.size - 0))
          + 2 ^ (64 * (a.size - 0)) := by
      have : borrow * 2 ^ (64 * (a.size - 0)) ≥ 1 * 2 ^ (64 * (a.size - 0)) :=
        Nat.mul_le_mul_right _ h_b1
      linarith
    -- decremented ≥ original + β^len - d ≥ β^len
    have h_dec_ge : toNatLimbsList (((decrementSlice a 0 d (Nat.zero_le _)).toList.drop 0).take
        (a.size - 0)) ≥ 2 ^ (64 * (a.size - 0)) := by omega
    -- But decremented < β^len.
    have h_dec_lt : toNatLimbsList (((decrementSlice a 0 d (Nat.zero_le _)).toList.drop 0).take
        (a.size - 0)) < 2 ^ (64 * (a.size - 0)) := by
      have h_len : (((decrementSlice a 0 d (Nat.zero_le _)).toList.drop 0).take
          (a.size - 0)).length = a.size - 0 := by
        rw [List.length_take, List.length_drop, Array.length_toList,
          decrementSlice_size]; omega
      have := toNatLimbsList_lt_pow (((decrementSlice a 0 d (Nat.zero_le _)).toList.drop 0).take
          (a.size - 0))
      rwa [h_len] at this
    omega
  rw [h_borrow_zero, Nat.zero_mul, Nat.add_zero] at h_dec; omega

/-- Splitting a slice at offset `k`: low `k` limbs + high `len − k` limbs. -/
theorem sliceVal_split (a : Array UInt64) (lo len k : Nat)
    (hk : k ≤ len) (hbound : lo + len ≤ a.size) :
    sliceVal a lo len
      = sliceVal a lo k + sliceVal a (lo + k) (len - k) * 2 ^ (64 * k) := by
  unfold sliceVal
  have h_len_a : a.toList.length = a.size := Array.length_toList
  have h_split :
      (a.toList.drop lo).take len
        = (a.toList.drop lo).take k ++ (a.toList.drop (lo + k)).take (len - k) := by
    conv_lhs => rw [show len = k + (len - k) from by omega]
    rw [List.take_add, List.drop_drop]
  rw [h_split, toNatLimbsList_append]
  have h_drop_len : (a.toList.drop lo).length = a.size - lo := by
    rw [List.length_drop, h_len_a]
  have h_low_len : ((a.toList.drop lo).take k).length = k := by
    rw [List.length_take, h_drop_len]; omega
  rw [h_low_len]; ring

/-- Two arrays agreeing element-wise on `[lo, lo + len)` (with `len` in
    bounds for both) have equal `sliceVal` on that range.  Used by the
    chunking branch to push `addLimb` preservation up to the slice level. -/
theorem sliceVal_eq_of_getElem_eq (a1 a2 : Array UInt64) (lo len : Nat)
    (h_bound1 : lo + len ≤ a1.size) (h_bound2 : lo + len ≤ a2.size)
    (h_get : ∀ (k : Nat) (h_k : k < len),
      a1[lo + k]'(by omega) = a2[lo + k]'(by omega)) :
    sliceVal a1 lo len = sliceVal a2 lo len := by
  unfold sliceVal
  congr 1
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, Array.length_toList]; omega
  · intro k h1 _
    have h_k : k < len := by
      simp [List.length_take, List.length_drop, Array.length_toList] at h1
      omega
    rw [List.getElem_take, List.getElem_take]
    rw [List.getElem_drop, List.getElem_drop]
    have := h_get k h_k
    simpa [Array.getElem_toList] using this

private theorem toNatLimbsList_replicate_zero (n : Nat) :
    toNatLimbsList (List.replicate n (0 : UInt64)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show toNatLimbsList ((0 : UInt64) :: List.replicate k (0 : UInt64)) = 0
    rw [toNatLimbsList_cons, ih]; simp

/-- The `sliceVal` of any slice of an all-zero replicate is `0`. -/
theorem Array.replicate_sliceVal_zero (n lo len : Nat) :
    toNatLimbsList
      (((Array.replicate n (0 : UInt64)).toList.drop lo).take len) = 0 := by
  have h_take : (((Array.replicate n (0 : UInt64)).toList.drop lo).take len)
      = List.replicate (min len (n - lo)) (0 : UInt64) := by
    rw [Array.toList_replicate, List.drop_replicate, List.take_replicate]
  rw [h_take]
  exact toNatLimbsList_replicate_zero _

/-- `writeSlice` makes the targeted slice equal the source's slice
    (in toNat-list terms). -/
theorem writeSlice_sliceVal (a src : Array UInt64) (loA loS len : Nat)
    (hA : loA + len ≤ a.size) (hS : loS + len ≤ src.size) :
    toNatLimbsList (((writeSlice a src loA loS len 0 hA hS).toList.drop loA).take len)
      = toNatLimbsList ((src.toList.drop loS).take len) := by
  apply congrArg
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, Array.length_toList,
      writeSlice_size]
    omega
  · intro k h1 _
    have h_k : k < len := by
      simp [List.length_take, List.length_drop, Array.length_toList,
        writeSlice_size] at h1
      omega
    rw [List.getElem_take, List.getElem_take]
    rw [List.getElem_drop, List.getElem_drop]
    rw [Array.getElem_toList, Array.getElem_toList]
    -- Goal: writeSlice a src loA loS len 0 hA hS [loA + k] = src[loS + k]
    have h_ws := writeSlice_get_inside a src loA loS len 0 hA hS (loA + k)
      (by omega) (by omega) (by omega)
    rw [h_ws]
    congr 1; omega

/-- From the conservation equation `U + borrow * β + D = V + S + ec * β`
    with `U + D < β` (LHS bounded) AND `V + S < β` (RHS bounded),
    both `(0,1)` and `(1,0)` are impossible.  So `borrow = ec`. -/
theorem borrow_eq_endcarry_of_bounds
    (U D V S β borrow ec : Nat)
    (h_eq : U + borrow * β + D = V + S + ec * β)
    (h_UD : U + D < β)
    (h_VS : V + S < β)
    (h_borrow : borrow ≤ 1) (h_ec : ec ≤ 1) :
    borrow = ec := by
  -- After subst, omega can handle the linear arithmetic.
  rcases Nat.eq_or_lt_of_le (Nat.zero_le borrow) with rfl | hb1
  · -- borrow = 0. Need ec = 0.
    simp at h_eq  -- removes 0 * β
    rcases Nat.eq_or_lt_of_le (Nat.zero_le ec) with rfl | he1
    · rfl
    · have : ec = 1 := by omega
      subst this; simp at h_eq; omega  -- U + D = V + S + β, contradicts h_UD
  · -- borrow ≥ 1, so borrow = 1.
    have hb : borrow = 1 := by omega
    subst hb; simp at h_eq  -- U + β + D = V + S + ec * β
    rcases Nat.eq_or_lt_of_le (Nat.zero_le ec) with rfl | he1
    · simp at h_eq; omega  -- U + β + D = V + S, contradicts h_VS (V + S ≥ β)
    · omega

/-- afterFirstRec preserves positions below `loA + k` (where `k = m / 2`).
    All internal sub-operations (zeroFill, subGeqLimbs, addbackLoop) operate
    on `[loA + k, loA + n + m)`, leaving `[loA, loA + k)` untouched. -/
theorem recursiveDivModLimbs.afterFirstRec_sliceVal_below_k
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) (lo len : Nat)
    (h_bound : lo + len ≤ a.size) (h_below : lo + len ≤ loA + m / 2) :
    sliceVal (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).1 lo len = sliceVal a lo len := by
  apply sliceVal_eq_of_getElem_eq _ _ lo len
    (by rw [recursiveDivModLimbs.afterFirstRec_size]; exact h_bound) h_bound
  intro j h_j
  show (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
    h_n_pos hA hB h_m_le_n h_m_ge_2).1[lo + j]'(by
      rw [recursiveDivModLimbs.afterFirstRec_size]; omega) = a[lo + j]
  unfold recursiveDivModLimbs.afterFirstRec
  simp only
  -- Chain: addbackLoop preserves (lo+j < loA+k), subGeqLimbs preserves,
  -- zeroFill preserves.
  set k := m / 2
  have h_pos_below : lo + j < loA + k := by omega
  rw [addbackLoop_get_outside _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lo + j)
    (Or.inl (by omega))
    (by rw [subGeqLimbs_size, zeroFill_size]; omega)]
  rw [subGeqLimbs_get_outside _ _ _ _ _ _ _ _ _ _ _ (lo + j)
    (Or.inl (by omega))
    (by rw [zeroFill_size]; omega)]
  exact zeroFill_get_outside a (loA + n + k) (loA + n + m) (lo + j)
    (Or.inl (by omega)) (by omega)

/-- Conservation of `afterFirstRec`: combines `zeroFill`, `mulLimbs`,
    `subGeqLimbs`, and `addbackLoop` conservations into a single
    algebraic identity relating the input and output slice values.

    Let `Q₁ := q1_arr.toNat = q_top_1 * β^(m-k) + sliceVal a (loA+n+k) (m-k)`,
    `B := sliceVal b loB n`, `B₀ := sliceVal b loB k`.  Then for some
    existential borrow/end_carry pair (both ≤ 1), the conservation
    `sliceVal a (loA + k) n + borrow * β^(n+m-k) + delta1 * B =
       sliceVal a4 (loA + k) (n + m - k) + Q₁ * B₀ + end_carry * β^(n+m-k)`
    holds, where `(a4, _, delta1) = afterFirstRec ...`.

    The proof composes the existing conservation lemmas for the four
    sub-steps.  Full chaining is deferred; this is the next concrete
    step toward closing the D&C body of `recursiveDivModLimbsAux_spec`. -/
theorem recursiveDivModLimbs.afterFirstRec_toNat
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    let res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2
    let k := m / 2
    let q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
    ∃ borrow end_carry : Nat, borrow ≤ 1 ∧ end_carry ≤ 1 ∧
      toNatLimbsList ((a.toList.drop (loA + k)).take n)
        + borrow * 2 ^ (64 * (n + m - k))
        + res.2.2 * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((res.1.toList.drop (loA + k)).take (n + m - k))
        + toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
        + end_carry * 2 ^ (64 * (n + m - k)) := by
  -- Unfold to expose the let chain.
  show ∃ _, _
  unfold recursiveDivModLimbs.afterFirstRec
  simp only
  set k := m / 2
  have h_k_pos : 0 < k := by omega
  have h_2k_le_n : 2 * k ≤ n := by omega
  -- Variables matching the function body.
  set q1_low := a.extract (loA + n + k) (loA + n + m) with hq1_low_def
  set q1_arr := q1_low.push q_top_1 with hq1_arr_def
  have h_q1_low_size : q1_low.size = m - k := by
    rw [hq1_low_def]; rw [Array.size_extract]; omega
  have h_q1_size : q1_arr.size = m - k + 1 := by
    rw [hq1_arr_def, Array.size_push, h_q1_low_size]
  set a2 := zeroFill a (loA + n + k) (loA + n + m) with ha2_def
  have h_a2_size : a2.size = a.size := zeroFill_size _ _ _
  set q1_b0 := mulLimbs q1_arr b 0 (m - k + 1) loB k
    (by rw [h_q1_size]; omega) (by omega) with hq1_b0_def
  have h_q1_b0_size_ge : m + 1 ≤ q1_b0.size := by
    rw [hq1_b0_def]
    have := mulLimbs_size_ge q1_arr b 0 (m - k + 1) loB k
      (by rw [h_q1_size]; omega) (by omega)
    omega
  set subRes := subGeqLimbs a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    (by rw [h_a2_size]; omega) (by omega)
    (by omega) (by omega) (by omega) with h_subRes_def
  set a3 := subRes.1 with ha3_def
  set borrow1 := subRes.2 with hbor1_def
  -- Apply subGeqLimbs_toNat: relates a2's and a3's slices via borrow1.
  have h_subGeq := subGeqLimbs_toNat a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    (by rw [h_a2_size]; omega) (by omega) (by omega) (by omega) (by omega)
  simp only at h_subGeq
  rw [← h_subRes_def] at h_subGeq
  -- h_subGeq : sliceVal a2 (loA + k) (n + m - k) + borrow1.toNat * β^(n+m-k)
  --          = sliceVal a3 (loA + k) (n + m - k) + sliceVal q1_b0 0 (m + 1)
  -- Apply addbackLoop_toNat: gives end_carry.
  have h_a3_size : a3.size = a.size := by
    rw [ha3_def, h_subRes_def]
    exact (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a2_size
  obtain ⟨end_carry, h_ec_le, h_addback⟩ := addbackLoop_toNat a3 b loA loB n k
    (n + m - k) borrow1 5 (by rw [h_a3_size]; omega) hB (by omega) h_n_pos
    (by omega)
  -- h_addback : sliceVal a3 (loA + k) (n + m - k) + delta * B
  --           = sliceVal a4 (loA + k) (n + m - k) + end_carry * β^(n+m-k)
  -- (A) Reduce sliceVal a2 (loA + k) (n + m - k) to sliceVal a (loA + k) n.
  have h_a2_eq : toNatLimbsList ((a2.toList.drop (loA + k)).take (n + m - k))
      = toNatLimbsList ((a.toList.drop (loA + k)).take n) := by
    -- Decompose a2's slice at offset n.
    have h_split : sliceVal a2 (loA + k) (n + m - k)
        = sliceVal a2 (loA + k) n
          + sliceVal a2 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
      have h := sliceVal_split a2 (loA + k) (n + m - k) n (by omega)
        (by rw [h_a2_size]; omega)
      have h_idx : loA + k + n = loA + n + k := by ring
      have h_diff : (n + m - k) - n = m - k := by omega
      rw [h_idx, h_diff] at h
      exact h
    -- a2's [loA + k, loA + n + k) is unchanged from a.
    have h_low_eq : sliceVal a2 (loA + k) n = sliceVal a (loA + k) n := by
      apply sliceVal_eq_of_getElem_eq a2 a (loA + k) n
        (by rw [h_a2_size]; omega) (by omega)
      intro j h_j
      exact zeroFill_get_outside a (loA + n + k) (loA + n + m) (loA + k + j)
        (Or.inl (by omega)) (by omega)
    -- a2's [loA + n + k, loA + n + m) is zeroed.
    have h_high_zero : sliceVal a2 (loA + n + k) (m - k) = 0 := by
      show toNatLimbsList ((a2.toList.drop (loA + n + k)).take (m - k)) = 0
      have := zeroFill_sliceVal_zero a (loA + n + k) (m - k) (by omega)
      have h_eq : loA + n + k + (m - k) = loA + n + m := by omega
      rw [h_eq] at this
      exact this
    -- Combine.
    show sliceVal a2 (loA + k) (n + m - k) = sliceVal a (loA + k) n
    rw [h_split, h_low_eq, h_high_zero]; ring
  -- (B) Reduce sliceVal q1_b0 0 (m + 1) to q1_arr.toNat * B₀.
  have h_B_bound : toNatLimbsList q1_arr.toList
        * toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * (m + 1)) := by
    have h_q1 : toNatLimbsList q1_arr.toList < 2 ^ (64 * (m - k + 1)) := by
      have h := toNatLimbsList_lt_pow q1_arr.toList
      have h_len : q1_arr.toList.length = m - k + 1 := by
        rw [Array.length_toList]; exact h_q1_size
      rw [h_len] at h; exact h
    have h_b : toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * k) := by
      have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
      have h_len : ((b.toList.drop loB).take k).length = k := by
        rw [List.length_take, List.length_drop, Array.length_toList]; omega
      rw [h_len] at h; exact h
    calc toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
        < 2 ^ (64 * (m - k + 1)) * 2 ^ (64 * k) :=
          Nat.mul_lt_mul_of_lt_of_le h_q1 (Nat.le_of_lt h_b) (Nat.two_pow_pos _)
      _ = 2 ^ (64 * (m - k + 1) + 64 * k) := by rw [Nat.pow_add]
      _ = 2 ^ (64 * (m + 1)) := by congr 1; omega
  -- toNatLimbsList q1_b0.toList = q1_arr.toNat * B₀.
  have h_q1_b0_total : toNatLimbsList q1_b0.toList
      = toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k) := by
    have h := mulLimbs_toNat q1_arr b 0 (m - k + 1) loB k
      (by rw [h_q1_size]; omega) (by omega)
    rw [← hq1_b0_def] at h
    have h_q1_take : (q1_arr.toList.drop 0).take (m - k + 1) = q1_arr.toList := by
      rw [List.drop_zero]; rw [List.take_of_length_le]
      rw [Array.length_toList]; rw [h_q1_size]
    rw [h_q1_take] at h
    exact h
  -- sliceVal q1_b0 0 (m + 1) = toNatLimbsList q1_b0.toList (since high limbs are 0).
  have h_q1_b0_slice : toNatLimbsList ((q1_b0.toList.drop 0).take (m + 1))
      = toNatLimbsList q1_b0.toList := by
    rw [List.drop_zero]
    -- Decompose q1_b0.toList into take (m+1) ++ drop (m+1).
    have h_split : q1_b0.toList
        = q1_b0.toList.take (m + 1) ++ q1_b0.toList.drop (m + 1) := by
      simp [List.take_append_drop]
    have h_decomp : toNatLimbsList q1_b0.toList
        = toNatLimbsList (q1_b0.toList.drop (m + 1)) * 2 ^ (64 * (m + 1))
          + toNatLimbsList (q1_b0.toList.take (m + 1)) := by
      conv_lhs => rw [h_split]
      rw [toNatLimbsList_append]
      have h_take_len : (q1_b0.toList.take (m + 1)).length = m + 1 := by
        rw [List.length_take, Array.length_toList]; omega
      rw [h_take_len]
    -- toNatLimbsList q1_b0.toList < β^(m+1).
    have h_lt : toNatLimbsList q1_b0.toList < 2 ^ (64 * (m + 1)) := by
      rw [h_q1_b0_total]; exact h_B_bound
    -- From decomp: toNatLimbsList (drop (m+1)) = 0.
    have h_drop_zero : toNatLimbsList (q1_b0.toList.drop (m + 1)) = 0 := by
      by_contra h_ne
      have h_pos : 0 < toNatLimbsList (q1_b0.toList.drop (m + 1)) :=
        Nat.pos_of_ne_zero h_ne
      have h_mul_ge : 2 ^ (64 * (m + 1))
          ≤ toNatLimbsList (q1_b0.toList.drop (m + 1)) * 2 ^ (64 * (m + 1)) :=
        Nat.le_mul_of_pos_left _ h_pos
      omega
    rw [h_decomp, h_drop_zero]; ring
  -- Final composition.
  refine ⟨borrow1.toNat, end_carry, ?_, h_ec_le, ?_⟩
  · cases borrow1 <;> decide
  · -- Combine h_subGeq, h_addback, h_a2_eq, h_q1_b0_total, h_q1_b0_slice.
    rw [h_a2_eq] at h_subGeq
    rw [h_q1_b0_slice, h_q1_b0_total] at h_subGeq
    linarith

/-- Conservation of `afterSecondRec`'s subtract-addback core (steps before
    the Q assembly).  Parallels `afterFirstRec_toNat` but with different
    offsets (subGeqLimbs at `loA` with length `n + m`, addbackLoop at
    `loA + 0`).  Tracks `a8` (post-addback, before Q-write).

    Let `Q₀ := q0_arr.toNat = q_top_0 * β^k + sliceVal a (loA + n) k`,
    `B := sliceVal b loB n`, `B₀ := sliceVal b loB k`.  Then for some
    existential borrow/end_carry pair (both ≤ 1):
    `sliceVal a loA n + sliceVal a (loA + n + k) (m - k) * β^(n + k)
        + borrow * β^(n + m) + delta0 * B
      = sliceVal a8 loA (n + m) + Q₀ * B₀ + end_carry * β^(n + m)`.

    The full `afterSecondRec_toNat` (including Q assembly via writeSlice
    + addSameLengthLimbs) is built on top of this. -/
theorem recursiveDivModLimbs.afterSecondRec_subAddback_toNat
    (a b : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    let k := m / 2
    let q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
    let a6 := zeroFill a (loA + n) (loA + n + k)
    let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
    let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [zeroFill_size]; omega) (by
        show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k _ _).size
        have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
        omega)
      (by omega) (by omega) (by omega)
    let a7 := subRes2.1
    let borrow0 := subRes2.2
    let adj2 := addbackLoop a7 b loA loB n 0 (n + m) borrow0 5
      (by
        have h_a7_size : a7.size = a.size := by
          show subRes2.1.size = a.size
          exact (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _)
        rw [h_a7_size]; omega)
      hB (by omega) h_n_pos (by omega)
    ∃ borrow end_carry : Nat, borrow ≤ 1 ∧ end_carry ≤ 1 ∧
      toNatLimbsList ((a.toList.drop loA).take n)
        + toNatLimbsList ((a.toList.drop (loA + n + k)).take (m - k))
          * 2 ^ (64 * (n + k))
        + borrow * 2 ^ (64 * (n + m))
        + adj2.2 * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((adj2.1.toList.drop loA).take (n + m))
        + toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
        + end_carry * 2 ^ (64 * (n + m)) := by
  show ∃ _, _
  set k := m / 2
  have h_k_pos : 0 < k := by omega
  have h_2k_le_n : 2 * k ≤ n := by omega
  set q0_low := a.extract (loA + n) (loA + n + k) with hq0_low_def
  set q0_arr := q0_low.push q_top_0 with hq0_arr_def
  have h_q0_low_size : q0_low.size = k := by
    rw [hq0_low_def, Array.size_extract]; omega
  have h_q0_size : q0_arr.size = k + 1 := by
    rw [hq0_arr_def, Array.size_push, h_q0_low_size]
  set a6 := zeroFill a (loA + n) (loA + n + k) with ha6_def
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  set q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
    (by rw [h_q0_size]; omega) (by omega) with hq0_b0_def
  have h_q0_b0_size_ge : 2 * k + 1 ≤ q0_b0.size := by
    rw [hq0_b0_def]
    have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
      (by rw [h_q0_size]; omega) (by omega)
    omega
  set subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    (by rw [h_a6_size]; omega) (by omega)
    (by omega) (by omega) (by omega) with h_subRes2_def
  set a7 := subRes2.1
  set borrow0 := subRes2.2
  have h_subGeq := subGeqLimbs_toNat a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    (by rw [h_a6_size]; omega) (by omega) (by omega) (by omega) (by omega)
  simp only at h_subGeq
  rw [← h_subRes2_def] at h_subGeq
  have h_a7_size : a7.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_size
  obtain ⟨end_carry, h_ec_le, h_addback⟩ := addbackLoop_toNat a7 b loA loB n 0
    (n + m) borrow0 5 (by rw [h_a7_size]; omega) hB (by omega) h_n_pos
    (by omega)
  -- (A) Reduce sliceVal a6 loA (n + m).  a6 zeros [loA + n, loA + n + k).
  -- Decompose at offset n: low n unchanged from a; high (m) breaks into
  -- [loA + n, loA + n + k) (zeroed) and [loA + n + k, loA + n + m) (unchanged).
  have h_a6_eq : toNatLimbsList ((a6.toList.drop loA).take (n + m))
      = toNatLimbsList ((a.toList.drop loA).take n)
        + toNatLimbsList ((a.toList.drop (loA + n + k)).take (m - k))
          * 2 ^ (64 * (n + k)) := by
    have h_split1 : sliceVal a6 loA (n + m) = sliceVal a6 loA n
        + sliceVal a6 (loA + n) m * 2 ^ (64 * n) := by
      have h := sliceVal_split a6 loA (n + m) n (by omega)
        (by rw [h_a6_size]; omega)
      have h_diff : n + m - n = m := by omega
      rw [h_diff] at h; exact h
    have h_split2 : sliceVal a6 (loA + n) m = sliceVal a6 (loA + n) k
        + sliceVal a6 (loA + n + k) (m - k) * 2 ^ (64 * k) := by
      have h := sliceVal_split a6 (loA + n) m k (by omega)
        (by rw [h_a6_size]; omega)
      have h_idx : loA + n + k = loA + n + k := rfl
      exact h
    -- a6's [loA, loA + n) unchanged from a.
    have h_low_eq : sliceVal a6 loA n = sliceVal a loA n := by
      apply sliceVal_eq_of_getElem_eq a6 a loA n
        (by rw [h_a6_size]; omega) (by omega)
      intro j h_j
      exact zeroFill_get_outside a (loA + n) (loA + n + k) (loA + j)
        (Or.inl (by omega)) (by omega)
    -- a6's [loA + n, loA + n + k) is zeroed.
    have h_zero : sliceVal a6 (loA + n) k = 0 := by
      show toNatLimbsList ((a6.toList.drop (loA + n)).take k) = 0
      have := zeroFill_sliceVal_zero a (loA + n) k (by omega)
      have h_eq : loA + n + k = loA + n + k := rfl
      exact this
    -- a6's [loA + n + k, loA + n + m) unchanged from a.
    have h_high_eq : sliceVal a6 (loA + n + k) (m - k)
        = sliceVal a (loA + n + k) (m - k) := by
      apply sliceVal_eq_of_getElem_eq a6 a (loA + n + k) (m - k)
        (by rw [h_a6_size]; omega) (by omega)
      intro j h_j
      exact zeroFill_get_outside a (loA + n) (loA + n + k) (loA + n + k + j)
        (Or.inr (by omega)) (by omega)
    show sliceVal a6 loA (n + m)
        = sliceVal a loA n
          + sliceVal a (loA + n + k) (m - k) * 2 ^ (64 * (n + k))
    rw [h_split1, h_split2, h_low_eq, h_zero, h_high_eq]
    have h_pow_split : (2 : Nat) ^ (64 * (n + k)) = 2 ^ (64 * k) * 2 ^ (64 * n) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h_pow_split]; ring
  -- (B) Reduce sliceVal q0_b0 0 (2k + 1) to Q₀ * B₀.
  have h_B_bound : toNatLimbsList q0_arr.toList
        * toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * (2 * k + 1)) := by
    have h_q0 : toNatLimbsList q0_arr.toList < 2 ^ (64 * (k + 1)) := by
      have h := toNatLimbsList_lt_pow q0_arr.toList
      have h_len : q0_arr.toList.length = k + 1 := by
        rw [Array.length_toList]; exact h_q0_size
      rw [h_len] at h; exact h
    have h_b : toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * k) := by
      have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
      have h_len : ((b.toList.drop loB).take k).length = k := by
        rw [List.length_take, List.length_drop, Array.length_toList]; omega
      rw [h_len] at h; exact h
    calc toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
        < 2 ^ (64 * (k + 1)) * 2 ^ (64 * k) :=
          Nat.mul_lt_mul_of_lt_of_le h_q0 (Nat.le_of_lt h_b) (Nat.two_pow_pos _)
      _ = 2 ^ (64 * (k + 1) + 64 * k) := by rw [Nat.pow_add]
      _ = 2 ^ (64 * (2 * k + 1)) := by congr 1; omega
  have h_q0_b0_total : toNatLimbsList q0_b0.toList
      = toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k) := by
    have h := mulLimbs_toNat q0_arr b 0 (k + 1) loB k
      (by rw [h_q0_size]; omega) (by omega)
    rw [← hq0_b0_def] at h
    have h_q0_take : (q0_arr.toList.drop 0).take (k + 1) = q0_arr.toList := by
      rw [List.drop_zero]; rw [List.take_of_length_le]
      rw [Array.length_toList]; rw [h_q0_size]
    rw [h_q0_take] at h
    exact h
  have h_q0_b0_slice : toNatLimbsList ((q0_b0.toList.drop 0).take (2 * k + 1))
      = toNatLimbsList q0_b0.toList := by
    rw [List.drop_zero]
    have h_split : q0_b0.toList
        = q0_b0.toList.take (2 * k + 1) ++ q0_b0.toList.drop (2 * k + 1) := by
      simp [List.take_append_drop]
    have h_decomp : toNatLimbsList q0_b0.toList
        = toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) * 2 ^ (64 * (2 * k + 1))
          + toNatLimbsList (q0_b0.toList.take (2 * k + 1)) := by
      conv_lhs => rw [h_split]
      rw [toNatLimbsList_append]
      have h_take_len : (q0_b0.toList.take (2 * k + 1)).length = 2 * k + 1 := by
        rw [List.length_take, Array.length_toList]; omega
      rw [h_take_len]
    have h_lt : toNatLimbsList q0_b0.toList < 2 ^ (64 * (2 * k + 1)) := by
      rw [h_q0_b0_total]; exact h_B_bound
    have h_drop_zero : toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) = 0 := by
      by_contra h_ne
      have h_pos : 0 < toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) :=
        Nat.pos_of_ne_zero h_ne
      have h_mul_ge : 2 ^ (64 * (2 * k + 1))
          ≤ toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) * 2 ^ (64 * (2 * k + 1)) :=
        Nat.le_mul_of_pos_left _ h_pos
      omega
    rw [h_decomp, h_drop_zero]; ring
  refine ⟨borrow0.toNat, end_carry, ?_, h_ec_le, ?_⟩
  · cases borrow0 <;> decide
  · rw [h_a6_eq] at h_subGeq
    rw [h_q0_b0_slice, h_q0_b0_total] at h_subGeq
    -- h_addback uses `loA + 0` while h_subGeq uses `loA`; normalize.
    simp only [Nat.add_zero] at h_addback
    linarith

/-- MCA two-stage conservation chaining: if `A = Q₁' * B * β_k + A'` (first
    adjust) and `A' = Q₀' * B + R` (second adjust), then
    `A = (Q₁' * β_k + Q₀') * B + R`. -/
theorem dc_algebra (A B β_k Q₁' A' Q₀' R : Nat)
    (h_step1 : A = Q₁' * (B * β_k) + A')
    (h_step2 : A' = Q₀' * B + R) :
    A = (Q₁' * β_k + Q₀') * B + R := by
  rw [h_step1, h_step2]; ring

/-- MCA single-stage conservation: if `A + delta * C = Q * C + A'` and
    `delta ≤ Q`, then `A = (Q - delta) * C + A'`.  This is the core
    algebraic step used in both MCA adjust stages. -/
theorem mca_step_nat (A Q delta C A' : Nat)
    (h_delta_le : delta ≤ Q)
    (h_eq : A + delta * C = Q * C + A') :
    A = (Q - delta) * C + A' := by
  have h1 : (Q - delta) * C = Q * C - delta * C := Nat.sub_mul Q delta C
  have h2 : delta * C ≤ Q * C := Nat.mul_le_mul_right C h_delta_le
  omega

/-- Bridge from afterFirstRec_toNat's conservation to the clean MCA form.
    Given: A = A_top * β_2k + A_low, A_top = Q₁ * B₁ + R₁, B = B₁ * β_k + B₀,
    and the adjust conservation (with borrow = end_carry canceling), derive:
    `A + delta * (B * β_k) = Q₁ * (B * β_k) + A'`
    where `A' = A_low_lo + V₁ * β_k` (the reduced dividend). -/
theorem mca_bridge_step1
    (A_low_lo A_low_hi R₁ V₁ Q₁ B B₁ B₀ delta1 β_k β_2k : Nat)
    (h_B : B = B₁ * β_k + B₀)
    (h_β_2k : β_2k = β_k * β_k)
    (h_adjust : A_low_hi + R₁ * β_k + delta1 * B = V₁ + Q₁ * B₀) :
    (A_low_lo + A_low_hi * β_k + (Q₁ * B₁ + R₁) * β_2k) + delta1 * (B * β_k)
      = Q₁ * (B * β_k) + (A_low_lo + V₁ * β_k) := by
  have h_QB : Q₁ * (B * β_k) = Q₁ * B₁ * β_2k + Q₁ * B₀ * β_k := by
    rw [h_B, h_β_2k]; ring
  -- Multiply h_adjust by β_k to get the key relation.
  have h_mul : (A_low_hi + R₁ * β_k + delta1 * B) * β_k
      = (V₁ + Q₁ * B₀) * β_k := congrArg (· * β_k) h_adjust
  rw [h_QB, h_β_2k]; nlinarith [h_mul]

/-- Bridge for stage 2: derive `A' + delta0 * B = Q₀ * B + R` from the
    second IH's `a4_mid = Q₀ * B₁ + R₀` and afterSecondRec_subAddback's
    conservation.  `A'` is decomposed as `A_lo + a4_mid * β_k + V_hi * β_nk`.

    The proof multiplies the conservation by β_k and uses `B = B₁*β_k + B₀`
    to combine Q₀*B₁*β_k + Q₀*B₀ = Q₀*B. -/
theorem mca_bridge_step2
    (A_lo R₀ V_hi Q₀ R B B₁ B₀ delta0 β_k β_nk : Nat)
    (h_B : B = B₁ * β_k + B₀)
    (h_adjust : A_lo + R₀ * β_k + V_hi * β_nk + delta0 * B
      = R + Q₀ * B₀) :
    (A_lo + (Q₀ * B₁ + R₀) * β_k + V_hi * β_nk) + delta0 * B
      = Q₀ * B + R := by
  rw [h_B]; nlinarith [h_adjust]

/-- Parametrized D&C body div_eq: given the two clean stage conservations
    as Nat equalities + delta bounds, derive A = Q' * B + R.
    This is just `dc_algebra` + `mca_step_nat` × 2, packaged. -/
theorem dc_body_div_eq
    (A B Q₁ delta1 A' Q₀ delta0 R β_k : Nat)
    (h_bridge1 : A + delta1 * (B * β_k) = Q₁ * (B * β_k) + A')
    (h_bridge2 : A' + delta0 * B = Q₀ * B + R)
    (h_d1 : delta1 ≤ Q₁) (h_d0 : delta0 ≤ Q₀) :
    A = ((Q₁ - delta1) * β_k + (Q₀ - delta0)) * B + R := by
  have h1 := mca_step_nat A Q₁ delta1 (B * β_k) A' h_d1 h_bridge1
  have h2 := mca_step_nat A' Q₀ delta0 B R h_d0 h_bridge2
  exact dc_algebra A B β_k (Q₁ - delta1) A' (Q₀ - delta0) R h1 h2

/-- Derive h_bridge1 from conservation + decomposition (parametrized).
    Takes the clean conservation `U₁ + delta1*B = V₁ + Q₁*B₀` and the
    decomposition `A = A_lo + (Q₁*B₁ + R₁) * β_2k + A_lo_hi * β_k`,
    `A' = A_lo + V₁ * β_k`, produces bridge1 form. -/
theorem derive_bridge1
    (A A_lo A_lo_hi R₁ Q₁ B₁ B₀ B V₁ A' delta1 β_k β_2k : Nat)
    (h_B : B = B₁ * β_k + B₀)
    (h_β : β_2k = β_k * β_k)
    (h_A : A = A_lo + A_lo_hi * β_k + (Q₁ * B₁ + R₁) * β_2k)
    (h_A' : A' = A_lo + V₁ * β_k)
    (h_adj : A_lo_hi + R₁ * β_k + delta1 * B = V₁ + Q₁ * B₀) :
    A + delta1 * (B * β_k) = Q₁ * (B * β_k) + A' := by
  rw [h_A, h_A']
  have := mca_bridge_step1 A_lo A_lo_hi R₁ V₁ Q₁ B B₁ B₀ delta1 β_k β_2k
    h_B h_β h_adj
  linarith

/-- Derive h_bridge2 from second conservation + decomposition (parametrized). -/
theorem derive_bridge2
    (A' A_lo R₀ Q₀ B₁ B₀ B V_hi R delta0 β_k β_nk : Nat)
    (h_B : B = B₁ * β_k + B₀)
    (h_A' : A' = A_lo + (Q₀ * B₁ + R₀) * β_k + V_hi * β_nk)
    (h_adj : A_lo + R₀ * β_k + V_hi * β_nk + delta0 * B = R + Q₀ * B₀) :
    A' + delta0 * B = Q₀ * B + R := by
  rw [h_A']
  exact mca_bridge_step2 A_lo R₀ V_hi Q₀ R B B₁ B₀ delta0 β_k β_nk h_B h_adj

/-- S6 helper: combines `A' = A_lo + V₁ * β_k`, `V₁ split`, second IH,
    and preservation into the decomposed form needed by `dc_full_bookkeeping`.

    Takes: A'_val (= sliceVal a4 loA (n+m)), A_lo, V₁, β_k, β_n, β_nk,
           Q₀_val (the push-assembled quotient), B₁, R₀, V_hi.
    Hypotheses give the chain of equalities.
    Conclusion: A'_val = A_lo + (Q₀_val * B₁ + R₀) * β_k + V_hi * β_nk. -/
private theorem s6_decomp_helper
    (A'_val A_lo V₁ Q₀_val B₁ R₀ V_hi V_hi' β_k β_n β_nk : Nat)
    (h_A'_val : A'_val = A_lo + V₁ * β_k)
    (h_V₁_split : V₁ = (Q₀_val * B₁ + R₀) + V_hi' * β_n)
    (h_V_hi : V_hi' = V_hi)
    (h_β : β_nk = β_n * β_k) :
    A'_val = A_lo + (Q₀_val * B₁ + R₀) * β_k + V_hi * β_nk := by
  subst h_V_hi; rw [h_A'_val, h_V₁_split, h_β]; ring

/-- Full D&C bookkeeping: takes all decompositions, IH specs, and
    conservation equations as pure Nat hypotheses and derives
    `A = ((Q₁ - delta1) * β_k + (Q₀ - delta0)) * B + R`.
    Composes derive_bridge1, derive_bridge2, and dc_body_div_eq. -/
theorem dc_full_bookkeeping
    (A A_lo A_lo_hi A_top B B₁ B₀ Q₁ R₁ delta1 V₁ A' : Nat)
    (Q₀ R₀ V_hi delta0 R β_k β_2k β_nk : Nat)
    (h_B : B = B₁ * β_k + B₀)
    (h_β : β_2k = β_k * β_k)
    (h_A : A = A_lo + A_lo_hi * β_k + A_top * β_2k)
    (h_first : A_top = Q₁ * B₁ + R₁)
    (h_adj1 : A_lo_hi + R₁ * β_k + delta1 * B = V₁ + Q₁ * B₀)
    (h_A' : A' = A_lo + V₁ * β_k)
    (h_A'_decomp : A' = A_lo + (Q₀ * B₁ + R₀) * β_k + V_hi * β_nk)
    (h_adj2 : A_lo + R₀ * β_k + V_hi * β_nk + delta0 * B = R + Q₀ * B₀)
    (h_d1 : delta1 ≤ Q₁) (h_d0 : delta0 ≤ Q₀) :
    A = ((Q₁ - delta1) * β_k + (Q₀ - delta0)) * B + R := by
  have h_A_subst : A = A_lo + A_lo_hi * β_k + (Q₁ * B₁ + R₁) * β_2k := by
    rw [h_A, h_first]
  have h_bridge1 := derive_bridge1 A A_lo A_lo_hi R₁ Q₁ B₁ B₀ B V₁ A' delta1
    β_k β_2k h_B h_β h_A_subst h_A' h_adj1
  have h_bridge2 := derive_bridge2 A' A_lo R₀ Q₀ B₁ B₀ B V_hi R delta0 β_k β_nk
    h_B h_A'_decomp h_adj2
  exact dc_body_div_eq A B Q₁ delta1 A' Q₀ delta0 R β_k h_bridge1 h_bridge2 h_d1 h_d0

/-- When `addGeqLimbs` produces carry, the output slice < the addend.
    Follows from: `result + β^highLen = old + B`, with `old < β^highLen`. -/
theorem addGeqLimbs_lt_of_carry (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB)
    (h_carry : (addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).2 = true) :
    sliceVal (addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1 loA lenA
      < sliceVal b loB lenB := by
  have h := addGeqLimbs_toNat a b loA lenA loB lenB hA hB h_ge h_posA h_posB
  simp only at h
  rw [h_carry] at h
  simp at h
  -- h: result + 2^(64*lenA) = old + B (in toNatLimbsList form).
  -- old < 2^(64*lenA) (limb bound).
  have h_a_lt : toNatLimbsList ((a.toList.drop loA).take lenA) < 2 ^ (64 * lenA) := by
    have h_bound := toNatLimbsList_lt_pow ((a.toList.drop loA).take lenA)
    have h_len : ((a.toList.drop loA).take lenA).length = lenA := by
      rw [List.length_take, List.length_drop, Array.length_toList]; omega
    rw [h_len] at h_bound; exact h_bound
  -- result = old + B - 2^(64*lenA) < B.
  show toNatLimbsList _ < toNatLimbsList _
  linarith

/-- When `addbackLoop` terminates with `end_carry = 1` (which happens when
    `borrow = true` and fuel is sufficient), the final slice value < B.
    Proof: the last addGeqLimbs produced carry, so `addGeqLimbs_lt_of_carry`
    gives the bound. -/
theorem addbackLoop_result_lt (a b : Array UInt64) (loA loB n k highLen : Nat)
    (borrow : Bool) (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen)
    (h_borrow : borrow = true)
    (h_fuel : 0 < fuel) :
    let res := addbackLoop a b loA loB n k highLen borrow fuel
      hA hB h_n_le h_n_pos h_high_pos
    ∃ end_carry : Nat, end_carry ≤ 1 ∧
      (end_carry = 1 →
        sliceVal res.1 (loA + k) highLen < sliceVal b loB n) := by
  induction fuel generalizing a borrow with
  | zero => omega
  | succ fuel' ih =>
    unfold addbackLoop
    rw [h_borrow]; simp only [↓reduceIte]
    set r := addGeqLimbs a b (loA + k) highLen loB n
      (by omega) hB h_n_le h_high_pos h_n_pos
    -- r.2: carry from this addGeqLimbs call.
    rcases h_r2 : r.2 with _ | _
    · -- r.2 = false: !r.2 = true → recursive call continues.
      simp only [Bool.not_false]
      -- Use IH on recursive call (with borrow = true, fuel = fuel').
      rcases fuel' with _ | fuel''
      · -- fuel' = 0: the recursive call is addbackLoop ... true 0 = (a, 0).
        -- No carry at this level.  Return end_carry = 0.
        unfold addbackLoop; simp
        exact ⟨0, by omega, by intro h; omega⟩
      · -- fuel' = succ fuel'': use IH.
        obtain ⟨ec, h_ec_le, h_ec_lt⟩ := ih r.1 true
          (by rw [addGeqLimbs_size]; exact hA) rfl (by omega)
        exact ⟨ec, h_ec_le, h_ec_lt⟩
    · -- r.2 = true: !r.2 = false → recursive call returns immediately.
      simp only [Bool.not_true]
      -- The recursive call with borrow = false returns (r.1, 0).
      cases fuel' with
      | zero => unfold addbackLoop; simp; exact ⟨1, by omega, fun _ =>
          addGeqLimbs_lt_of_carry a b (loA + k) highLen loB n
            (by omega) hB h_n_le h_high_pos h_n_pos h_r2⟩
      | succ _ => unfold addbackLoop; simp; exact ⟨1, by omega, fun _ =>
          addGeqLimbs_lt_of_carry a b (loA + k) highLen loB n
            (by omega) hB h_n_le h_high_pos h_n_pos h_r2⟩

/-- Combined conservation + bound for addbackLoop: gives BOTH the
    conservation equation AND the carry-implies-lt bound with a SINGLE
    end_carry (avoiding the separate-existential issue from using
    addbackLoop_toNat and addbackLoop_result_lt independently). -/
theorem addbackLoop_delta_le (a b : Array UInt64) (loA loB n k highLen : Nat)
    (borrow : Bool) (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen) :
    (addbackLoop a b loA loB n k highLen borrow fuel
      hA hB h_n_le h_n_pos h_high_pos).2 ≤ fuel := by
  induction fuel generalizing a borrow with
  | zero => simp [addbackLoop]
  | succ fuel' ih =>
    unfold addbackLoop
    by_cases h : borrow
    · simp only [h, ↓reduceIte]
      have h_r_size : (addGeqLimbs a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos).1.size = a.size :=
        addGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _
      have := ih (addGeqLimbs a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos).1
        (!(addGeqLimbs a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos).2)
        (by rw [h_r_size]; exact hA)
      omega
    · simp [h]

/-- Existential uniqueness for addbackLoop's end_carry: given the
    conservation `A + delta * B = result + ec * β` with `result < β`
    and `A + delta * B < 2 * β` (from limb bounds), `ec` is unique. -/
theorem addbackLoop_ec_unique (A delta_B result β ec1 ec2 : Nat)
    (h1 : A + delta_B = result + ec1 * β)
    (h2 : A + delta_B = result + ec2 * β)
    (_ : ec1 ≤ 1) (_ : ec2 ≤ 1) (h_β_pos : 0 < β) :
    ec1 = ec2 := by
  have h_mul_eq : ec1 * β = ec2 * β := by omega
  exact Nat.eq_of_mul_eq_mul_right h_β_pos h_mul_eq

theorem addbackLoop_combined (a b : Array UInt64) (loA loB n k highLen : Nat)
    (fuel : Nat)
    (hA : loA + k + highLen ≤ a.size) (hB : loB + n ≤ b.size)
    (h_n_le : n ≤ highLen) (h_n_pos : 0 < n) (h_high_pos : 0 < highLen)
    (h_borrow : Bool) (h_fuel : h_borrow = true → 0 < fuel) :
    let res := addbackLoop a b loA loB n k highLen h_borrow fuel
      hA hB h_n_le h_n_pos h_high_pos
    ∃ end_carry : Nat, end_carry ≤ 1 ∧
      toNatLimbsList ((a.toList.drop (loA + k)).take highLen)
        + res.2 * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList ((res.1.toList.drop (loA + k)).take highLen)
        + end_carry * 2 ^ (64 * highLen)
      ∧ (end_carry = 1 →
          sliceVal res.1 (loA + k) highLen < sliceVal b loB n)
      ∧ (end_carry = 0 → h_borrow = true → res.2 = fuel) := by
  induction fuel generalizing a h_borrow with
  | zero =>
    cases h_borrow
    · exact ⟨0, by omega, by simp [addbackLoop], by intro; omega, by intro _ _; simp [addbackLoop]⟩
    · exact absurd (h_fuel rfl) (by omega)
  | succ fuel' ih =>
    cases h_b : h_borrow with
    | false => exact ⟨0, by omega, by simp [addbackLoop], by intro; omega, by intro _ h; exact absurd h (by decide)⟩
    | true =>
      -- One iteration: r := addGeqLimbs ...; recurse on (!r.2).
      simp only [addbackLoop, ↓reduceIte]
      -- Get addGeqLimbs facts.
      have h_addGeq := addGeqLimbs_toNat a b (loA + k) highLen loB n
        (by omega) hB h_n_le h_high_pos h_n_pos
      simp only at h_addGeq
      have h_r_size := addGeqLimbs_size a b (loA + k) highLen loB n
        (by omega) hB h_n_le h_high_pos h_n_pos
      -- Case split on carry.
      cases h_r2 : (addGeqLimbs a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos).2 with
      | false =>
        -- No carry: !false = true. Recurse with borrow = true.
        simp only [Bool.not_false]
        rw [show (addGeqLimbs a b (loA + k) highLen loB n
            (by omega) hB h_n_le h_high_pos h_n_pos).2.toNat = 0 from by
          rw [h_r2]; rfl] at h_addGeq
        -- Apply IH (need fuel' > 0; handle fuel' = 0 separately).
        have h_hA' : loA + k + highLen ≤ (addGeqLimbs a b (loA + k) highLen loB n
            (by omega) hB h_n_le h_high_pos h_n_pos).1.size := by
          rw [h_r_size]; linarith
        rcases fuel' with _ | fuel''
        · -- fuel' = 0: inner addbackLoop with borrow=true, fuel=0 returns (r.1, 0).
          simp only [addbackLoop]
          exact ⟨0, Nat.zero_le _, by simp; linarith,
            fun h => absurd h (by omega), fun _ _ => by simp⟩
        · -- fuel' = succ: IH applies.
          obtain ⟨ec, h_ec_le, h_inner, h_lt, h_delta_fuel⟩ :=
            ih _ h_hA' true (by intro; omega)
          refine ⟨ec, h_ec_le, ?_, h_lt, ?_⟩
          · show toNatLimbsList _ + _ = toNatLimbsList _ + _
            linarith
          · intro h_ec0 _
            have := h_delta_fuel h_ec0 rfl
            omega
      | true =>
        -- Carry: !true = false. Inner loop returns (r.1, 0).
        simp only [Bool.not_true]
        -- Inner addbackLoop with borrow=false returns immediately.
        have h_inner_eq : ∀ (hA' : loA + k + highLen ≤ (addGeqLimbs a b
            (loA + k) highLen loB n (by omega) hB h_n_le h_high_pos h_n_pos).1.size),
            addbackLoop (addGeqLimbs a b (loA + k) highLen loB n
              (by omega) hB h_n_le h_high_pos h_n_pos).1
              b loA loB n k highLen false fuel' hA' hB h_n_le h_n_pos h_high_pos
            = ((addGeqLimbs a b (loA + k) highLen loB n
              (by omega) hB h_n_le h_high_pos h_n_pos).1, 0) := by
          intro hA'
          cases fuel' with
          | zero => simp only [addbackLoop]
          | succ n => simp only [addbackLoop, Bool.false_eq_true, ↓reduceIte]
        rw [show (addGeqLimbs a b (loA + k) highLen loB n
            (by omega) hB h_n_le h_high_pos h_n_pos).2.toNat = 1 from by
          rw [h_r2]; rfl] at h_addGeq
        have h_lt := addGeqLimbs_lt_of_carry a b (loA + k) highLen loB n
          (by omega) hB h_n_le h_high_pos h_n_pos h_r2
        have h_hA' : loA + k + highLen ≤ (addGeqLimbs a b (loA + k) highLen loB n
            (by omega) hB h_n_le h_high_pos h_n_pos).1.size := by
          rw [h_r_size]; linarith
        rw [h_inner_eq h_hA']
        -- Goal: ∃ ec ≤ 1, conservation ∧ bound. Result = (r.1, 0+1).
        refine ⟨1, by omega, ?_, fun _ => h_lt, by intro h; omega⟩
        -- Conservation: a + 1 * B = r.1 + 1 * β.
        simp only; linarith

/-- MCA fuel sufficiency: from the conservation equation
    `U + borrow * β + D = V + S + ec * β` with `U + D < β`
    (so case (0,1) is impossible) AND with the addbackLoop_combined
    guarantee that `ec = 1 → V < B` (so `V + S < B + S ≤ 5B < β`
    ruling out case (1,0)), derive `borrow = ec`.

    The `h_ec1_bound` hypothesis bridges the two: when ec=1, V is
    small enough to force borrow=1 via borrow_eq_endcarry_of_bounds. -/

private theorem stage2_UD_lt_beta (A_low A_high delta B n k m : Nat)
    (h_low : A_low < 2 ^ (64 * n))
    (h_high : A_high < 2 ^ (64 * (m - k)))
    (h_B : B < 2 ^ (64 * n))
    (h_delta : delta ≤ 5)
    (h_k_pos : 0 < k) (h_mk_pos : 0 < m - k) :
    A_low + A_high * 2 ^ (64 * (n + k)) + delta * B < 2 ^ (64 * (n + m)) := by
  have h_high_bound : A_high * 2 ^ (64 * (n + k)) + 2 ^ (64 * (n + k))
      ≤ 2 ^ (64 * (n + m)) := by
    have h_le : A_high + 1 ≤ 2 ^ (64 * (m - k)) := by omega
    have h_mul : (A_high + 1) * 2 ^ (64 * (n + k))
        ≤ 2 ^ (64 * (m - k)) * 2 ^ (64 * (n + k)) :=
      Nat.mul_le_mul_right _ h_le
    have h_pow : 2 ^ (64 * (m - k)) * 2 ^ (64 * (n + k)) = 2 ^ (64 * (n + m)) := by
      rw [← Nat.pow_add]; congr 1; omega
    linarith [Nat.add_mul A_high 1 (2 ^ (64 * (n + k)))]
  have h_D_bound : delta * B < 6 * 2 ^ (64 * n) := by
    calc delta * B ≤ 5 * B := Nat.mul_le_mul_right _ h_delta
      _ < 5 * 2 ^ (64 * n) := Nat.mul_lt_mul_of_pos_left h_B (by omega)
      _ ≤ 6 * 2 ^ (64 * n) := by omega
  have h_6n_le_nk : 6 * 2 ^ (64 * n) ≤ 2 ^ (64 * (n + k)) := by
    have h7 : (7 : Nat) ≤ 2 ^ (64 * k) := by
      calc (7 : Nat) ≤ 2 ^ 3 := by decide
        _ ≤ 2 ^ (64 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    calc 6 * 2 ^ (64 * n) ≤ 7 * 2 ^ (64 * n) := by omega
      _ ≤ 2 ^ (64 * k) * 2 ^ (64 * n) := Nat.mul_le_mul_right _ h7
      _ = 2 ^ (64 * (n + k)) := by rw [← Nat.pow_add]; congr 1; omega
  nlinarith

theorem mca_fuel_sufficiency
    (U D V S β_val borrow ec : Nat)
    (h_eq : U + borrow * β_val + D = V + S + ec * β_val)
    (h_borrow : borrow ≤ 1) (h_ec : ec ≤ 1)
    (h_UD : U + D < β_val)
    (h_impossible : ec = 0 → borrow = 1 → False) :
    borrow = ec := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le ec) with rfl | he1
  · simp at h_eq
    rcases Nat.eq_or_lt_of_le (Nat.zero_le borrow) with rfl | hb1
    · rfl
    · exact (h_impossible rfl (by omega)).elim
  · have hec : ec = 1 := by omega
    subst hec; simp at h_eq
    rcases Nat.eq_or_lt_of_le (Nat.zero_le borrow) with rfl | hb1
    · simp at h_eq; omega
    · omega

/-- Clean conservation for `afterFirstRec`: no borrow/end_carry terms.
    Mirrors `mca_step_conservation` from the AzNat-level proof. -/
theorem recursiveDivModLimbs.afterFirstRec_spec
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_Q_B0_le : toNatLimbsList ((a.extract (loA + n + m / 2) (loA + n + m)).push
        q_top_1).toList * toNatLimbsList ((b.toList.drop loB).take (m / 2))
      ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n)) :
    let res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2
    let k := m / 2
    toNatLimbsList ((a.toList.drop (loA + k)).take n)
      + res.2.2 * toNatLimbsList ((b.toList.drop loB).take n)
    = toNatLimbsList ((res.1.toList.drop (loA + k)).take (n + m - k))
      + toNatLimbsList ((a.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
        * toNatLimbsList ((b.toList.drop loB).take k) := by
  show toNatLimbsList _ + _ = toNatLimbsList _ + _
  unfold recursiveDivModLimbs.afterFirstRec; simp only
  set k := m / 2
  set q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
  have h_q1_size : q1_arr.size = m - k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a2 := zeroFill a (loA + n + k) (loA + n + m)
  have h_a2_size : a2.size = a.size := zeroFill_size _ _ _
  have h_q1_hA : 0 + (m - k + 1) ≤ q1_arr.size := by rw [h_q1_size]; omega
  have h_loB_k : loB + k ≤ b.size := by have := h_m_le_n; omega
  set q1_b0 := mulLimbs q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k
  have h_q1_b0_size : m + 1 ≤ q1_b0.size := by
    show m + 1 ≤ (mulLimbs q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k).size
    have := mulLimbs_size_ge q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k; omega
  have h_subGeq_hA : loA + k + (n + m - k) ≤ a2.size := by rw [h_a2_size]; omega
  have h_subGeq_hB : 0 + (m + 1) ≤ q1_b0.size := by omega
  -- subGeqLimbs
  have h_subGeq := subGeqLimbs_toNat a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  simp only at h_subGeq
  set subRes := subGeqLimbs a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a3_size : subRes.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a2_size
  -- Named hypotheses for addbackLoop arguments
  have h_ab_hA : loA + k + (n + m - k) ≤ subRes.1.size := by rw [h_a3_size]; omega
  have h_ab_n_le : n ≤ n + m - k := by omega
  have h_ab_high : 0 < n + m - k := by omega
  -- addbackLoop_combined (with ec=0→delta=fuel)
  obtain ⟨ec, h_ec_le, h_addback, h_lt, h_delta_fuel⟩ :=
    addbackLoop_combined subRes.1 b loA loB n k (n + m - k) 5
      h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
      subRes.2 (fun _ => by omega)
  -- (A) h_a2_eq + h_q1_b0 (same structure as afterFirstRec_toNat).
  have h_a2_eq : toNatLimbsList ((a2.toList.drop (loA + k)).take (n + m - k))
      = toNatLimbsList ((a.toList.drop (loA + k)).take n) := by
    have h_split : sliceVal a2 (loA + k) (n + m - k)
        = sliceVal a2 (loA + k) n
          + sliceVal a2 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
      have h := sliceVal_split a2 (loA + k) (n + m - k) n (by omega)
        (by rw [h_a2_size]; omega)
      have h_idx : loA + k + n = loA + n + k := by ring
      have h_diff : (n + m - k) - n = m - k := by omega
      rw [h_idx, h_diff] at h; exact h
    have h_low_eq : sliceVal a2 (loA + k) n = sliceVal a (loA + k) n := by
      apply sliceVal_eq_of_getElem_eq a2 a (loA + k) n
        (by rw [h_a2_size]; omega) (by omega)
      intro j h_j
      exact zeroFill_get_outside a (loA + n + k) (loA + n + m) (loA + k + j)
        (Or.inl (by omega)) (by omega)
    have h_high_zero : sliceVal a2 (loA + n + k) (m - k) = 0 := by
      show toNatLimbsList ((a2.toList.drop (loA + n + k)).take (m - k)) = 0
      have := zeroFill_sliceVal_zero a (loA + n + k) (m - k) (by omega)
      have h_eq : loA + n + k + (m - k) = loA + n + m := by omega
      rw [h_eq] at this; exact this
    show sliceVal a2 (loA + k) (n + m - k) = sliceVal a (loA + k) n
    rw [h_split, h_low_eq, h_high_zero]; ring
  have h_q1_b0_slice : toNatLimbsList ((q1_b0.toList.drop 0).take (m + 1))
      = toNatLimbsList q1_arr.toList
        * toNatLimbsList ((b.toList.drop loB).take k) := by
    simp only [List.drop_zero]
    have h_q1_b0_total : toNatLimbsList q1_b0.toList
        = toNatLimbsList q1_arr.toList
          * toNatLimbsList ((b.toList.drop loB).take k) := by
      have h := mulLimbs_toNat q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k
      simp only [List.drop_zero] at h
      have h_q1_take : (q1_arr.toList).take (m - k + 1) = q1_arr.toList := by
        rw [List.take_of_length_le]; rw [Array.length_toList]; omega
      rw [h_q1_take] at h; exact h
    have h_B_bound : toNatLimbsList q1_arr.toList
          * toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * (m + 1)) := by
      have h_q1 : toNatLimbsList q1_arr.toList < 2 ^ (64 * (m - k + 1)) := by
        have h := toNatLimbsList_lt_pow q1_arr.toList
        have h_len : q1_arr.toList.length = m - k + 1 := by
          rw [Array.length_toList]; exact h_q1_size
        rw [h_len] at h; exact h
      have h_b : toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * k) := by
        have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
        have h_len : ((b.toList.drop loB).take k).length = k := by
          rw [List.length_take, List.length_drop, Array.length_toList]; omega
        rw [h_len] at h; exact h
      calc toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
          < 2 ^ (64 * (m - k + 1)) * 2 ^ (64 * k) :=
            Nat.mul_lt_mul_of_lt_of_le h_q1 (Nat.le_of_lt h_b) (Nat.two_pow_pos _)
        _ = 2 ^ (64 * (m + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    have h_lt : toNatLimbsList q1_b0.toList < 2 ^ (64 * (m + 1)) := by
      rw [h_q1_b0_total]; exact h_B_bound
    have h_split : q1_b0.toList
        = q1_b0.toList.take (m + 1) ++ q1_b0.toList.drop (m + 1) :=
      (List.take_append_drop (m + 1) q1_b0.toList).symm
    have h_decomp : toNatLimbsList q1_b0.toList
        = toNatLimbsList (q1_b0.toList.drop (m + 1)) * 2 ^ (64 * (m + 1))
          + toNatLimbsList (q1_b0.toList.take (m + 1)) := by
      conv_lhs => rw [h_split]
      rw [toNatLimbsList_append]
      have h_take_len : (q1_b0.toList.take (m + 1)).length = m + 1 := by
        rw [List.length_take, Array.length_toList]; omega
      rw [h_take_len]
    have h_high_zero : toNatLimbsList (q1_b0.toList.drop (m + 1)) = 0 := by
      by_contra h_ne
      have h_ge1 : 1 ≤ toNatLimbsList (q1_b0.toList.drop (m + 1)) :=
        Nat.one_le_iff_ne_zero.mpr h_ne
      have h_lower : 2 ^ (64 * (m + 1))
          ≤ toNatLimbsList (q1_b0.toList.drop (m + 1)) * 2 ^ (64 * (m + 1)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      linarith
    rw [← h_q1_b0_total]; rw [h_decomp, h_high_zero]; ring
  -- (B) Rewrite h_subGeq to use a and q1_arr.
  rw [h_a2_eq] at h_subGeq; rw [h_q1_b0_slice] at h_subGeq
  -- h_subGeq: U + borrow*β = V_sub + Q₁*B₀.
  -- h_addback: V_sub + delta*B = result + ec*β.
  -- (C) Combine into full conservation.
  have h_full : toNatLimbsList ((a.toList.drop (loA + k)).take n)
      + subRes.2.toNat * 2 ^ (64 * (n + m - k))
      + (addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2
        * toNatLimbsList ((b.toList.drop loB).take n)
    = toNatLimbsList (((addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k)).take (n + m - k))
      + toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
      + ec * 2 ^ (64 * (n + m - k)) := by linarith
  -- (D) Prove borrow = ec using mca_fuel_sufficiency.
  have h_borrow_eq_ec : subRes.2.toNat = ec :=
    mca_fuel_sufficiency _ _ _ _ _ _ _ h_full (by cases subRes.2 <;> decide) h_ec_le
      (by -- h_UD: U + D < β = 2^(64*(n+m-k)).
        have h_U := toNatLimbsList_lt_pow ((a.toList.drop (loA + k)).take n)
        have h_B := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
        have h_delta := addbackLoop_delta_le subRes.1 b loA loB n k (n + m - k) subRes.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
        simp [List.length_take, List.length_drop] at h_U h_B
        have h_n_take : min n (a.size - (loA + k)) = n := by omega
        have h_n_take2 : min n (b.size - loB) = n := by omega
        rw [h_n_take] at h_U; rw [h_n_take2] at h_B
        have h_mk_pos : 0 < m - k := by omega
        have h_pow_ge : 2 ^ (64 * n) ≥ 1 := Nat.one_le_two_pow
        have h64mk : (2 : Nat) ^ (64 * (m - k)) ≥ 2 ^ 64 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have h64_ge7 : (2 : Nat) ^ 64 ≥ 7 := by norm_num
        have h_pow_eq : 2 ^ (64 * n) * 2 ^ (64 * (m - k)) = 2 ^ (64 * (n + m - k)) := by
          rw [← Nat.pow_add]; congr 1; omega
        nlinarith)
      (by -- h_impossible: ec=0 → borrow=1 → False.
        intro h_ec0 h_bor1
        have h_bor_bool : subRes.2 = true := by
          cases h : subRes.2
          · simp [Bool.toNat, h] at h_bor1
          · rfl
        have h_delta5 := h_delta_fuel h_ec0 h_bor_bool
        have h_result_lt := toNatLimbsList_lt_pow
          ((addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
            h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k) |>.take (n + m - k))
        have h_res_size : (addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
            h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.size = subRes.1.size :=
          addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _
        have h_take_len : ((addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
            h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k) |>.take (n + m - k)).length
            = n + m - k := by
          simp [List.length_take, List.length_drop, h_res_size, h_a3_size]; omega
        rw [h_take_len] at h_result_lt
        simp only [h_ec0, Nat.zero_mul, Nat.add_zero, h_bor1, Nat.one_mul, h_delta5] at h_full
        linarith)
  -- (E) Cancel borrow/ec and derive clean conservation.
  rw [h_borrow_eq_ec] at h_full
  linarith

set_option maxHeartbeats 800000 in
/-- The full (n+m-k)-limb addbackLoop result inside `afterFirstRec` is
    strictly less than B.  Unlike stage 2, this needs NO `h_ec0_bound`
    hypothesis: the bound is self-contained from the first IH's rem_lt.
    ec=1: direct from addbackLoop_combined's h_lt.
    ec=0, borrow=false: result ≤ zeroed value = sliceVal a (loA+k) n < B₁·β_k ≤ B.
    ec=0, borrow=true: exfalso (5·B ≤ q1b0 ≤ 4·B). -/
theorem recursiveDivModLimbs.afterFirstRec_result_lt_B
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_Q_B0_le : toNatLimbsList ((a.extract (loA + n + m / 2) (loA + n + m)).push
        q_top_1).toList * toNatLimbsList ((b.toList.drop loB).take (m / 2))
      ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n))
    (h_IH_rem_lt : sliceVal a (loA + 2 * (m / 2)) (n - m / 2)
      < sliceVal b (loB + m / 2) (n - m / 2)) :
    let res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2
    let k := m / 2
    sliceVal res.1 (loA + k) (n + m - k) < sliceVal b loB n := by
  show _ < _
  unfold recursiveDivModLimbs.afterFirstRec; simp only
  set k := m / 2
  set q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
  have h_q1_size : q1_arr.size = m - k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a2 := zeroFill a (loA + n + k) (loA + n + m)
  have h_a2_size : a2.size = a.size := zeroFill_size _ _ _
  have h_q1_hA : 0 + (m - k + 1) ≤ q1_arr.size := by rw [h_q1_size]; omega
  have h_loB_k : loB + k ≤ b.size := by have := h_m_le_n; omega
  set q1_b0 := mulLimbs q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k
  have h_q1_b0_size : m + 1 ≤ q1_b0.size := by
    show m + 1 ≤ (mulLimbs q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k).size
    have := mulLimbs_size_ge q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k; omega
  have h_subGeq_hA : loA + k + (n + m - k) ≤ a2.size := by rw [h_a2_size]; omega
  have h_subGeq_hB : 0 + (m + 1) ≤ q1_b0.size := by omega
  set subRes := subGeqLimbs a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a3_size : subRes.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a2_size
  have h_ab_hA : loA + k + (n + m - k) ≤ subRes.1.size := by rw [h_a3_size]; omega
  have h_ab_n_le : n ≤ n + m - k := by omega
  have h_ab_high : 0 < n + m - k := by omega
  obtain ⟨ec, h_ec_le, h_addback, h_lt, h_delta_fuel⟩ :=
    addbackLoop_combined subRes.1 b loA loB n k (n + m - k) 5
      h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
      subRes.2 (fun _ => by omega)
  set adj := addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
    h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
  rcases Nat.eq_or_lt_of_le (Nat.zero_le ec) with h_ec0 | h_ec1
  · -- ec = 0
    have hec : ec = 0 := h_ec0.symm; subst hec
    simp only [Nat.zero_mul, Nat.add_zero] at h_addback
    -- Conservation: input + adj.2 * B = output
    have h_cons : sliceVal subRes.1 (loA + k) (n + m - k) + adj.2 * sliceVal b loB n
        = sliceVal adj.1 (loA + k) (n + m - k) := h_addback
    cases h_borrow : subRes.2 with
    | false =>
      -- borrow = false: addbackLoop returns input unchanged, delta = 0
      have h_adj2 : adj.2 = 0 := by
        show (addbackLoop subRes.1 b loA loB n k (n + m - k) subRes.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2 = 0
        rw [h_borrow]; unfold addbackLoop; simp
      rw [h_adj2, Nat.zero_mul, Nat.add_zero] at h_cons
      rw [← h_cons]
      -- subGeqLimbs with borrow=false: a2_val = subRes_val + q1b0_val
      have h_subGeq := subGeqLimbs_toNat a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
        h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
      simp only at h_subGeq
      have h_borrow_zero : subRes.2.toNat = 0 := by rw [h_borrow]; rfl
      rw [h_borrow_zero, Nat.zero_mul, Nat.add_zero] at h_subGeq
      -- h_subGeq: a2_val = subRes_val + q1b0_val
      -- So subRes_val ≤ a2_val
      have h_le_a2 : sliceVal subRes.1 (loA + k) (n + m - k)
          ≤ sliceVal a2 (loA + k) (n + m - k) := by linarith
      -- a2_val = sliceVal a (loA+k) n (zeroed high part)
      have h_a2_eq : sliceVal a2 (loA + k) (n + m - k)
          = sliceVal a (loA + k) n := by
        have h_split : sliceVal a2 (loA + k) (n + m - k)
            = sliceVal a2 (loA + k) n
              + sliceVal a2 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
          have h := sliceVal_split a2 (loA + k) (n + m - k) n (by omega)
            (by rw [h_a2_size]; omega)
          have h_idx : loA + k + n = loA + n + k := by ring
          have h_diff : (n + m - k) - n = m - k := by omega
          rw [h_idx, h_diff] at h; exact h
        have h_low_eq : sliceVal a2 (loA + k) n = sliceVal a (loA + k) n := by
          apply sliceVal_eq_of_getElem_eq a2 a (loA + k) n
            (by rw [h_a2_size]; omega) (by omega)
          intro j h_j
          exact zeroFill_get_outside a (loA + n + k) (loA + n + m) (loA + k + j)
            (Or.inl (by omega)) (by omega)
        have h_high_zero : sliceVal a2 (loA + n + k) (m - k) = 0 := by
          have := zeroFill_sliceVal_zero a (loA + n + k) (m - k) (by omega)
          have h_eq : loA + n + k + (m - k) = loA + n + m := by omega
          rw [h_eq] at this; exact this
        rw [h_split, h_low_eq, h_high_zero]; ring
      -- Now: subRes_val ≤ sliceVal a (loA+k) n. Show sliceVal a (loA+k) n < B.
      -- sliceVal a (loA+k) n = sliceVal a (loA+k) k + R₁ * β_k
      -- where R₁ = sliceVal a (loA+2k) (n-k) < B₁ = sliceVal b (loB+k) (n-k)
      -- and sliceVal a (loA+k) k < β_k.
      -- So sliceVal a (loA+k) n ≤ (β_k - 1) + (B₁ - 1) * β_k = B₁*β_k - 1 < B₁*β_k ≤ B.
      have h_a_split : sliceVal a (loA + k) n
          = sliceVal a (loA + k) k + sliceVal a (loA + 2 * k) (n - k) * 2 ^ (64 * k) := by
        have h := sliceVal_split a (loA + k) n k (by omega) (by omega)
        rw [show loA + k + k = loA + 2 * k from by ring] at h; exact h
      have h_lo_lt : sliceVal a (loA + k) k < 2 ^ (64 * k) := by
        have h := toNatLimbsList_lt_pow ((a.toList.drop (loA + k)).take k)
        have h_len : ((a.toList.drop (loA + k)).take k).length = k := by
          rw [List.length_take, List.length_drop, Array.length_toList]; omega
        rw [h_len] at h; exact h
      have h_B1_pos : 0 < sliceVal b (loB + k) (n - k) := by
        have : sliceVal a (loA + 2 * k) (n - k) < sliceVal b (loB + k) (n - k) :=
          h_IH_rem_lt
        omega
      have h_a_lt_B : sliceVal a (loA + k) n < sliceVal b loB n := by
        have h_B_decomp' : sliceVal b loB n
            = sliceVal b (loB + k) (n - k) * 2 ^ (64 * k) + sliceVal b loB k := by
          have h := sliceVal_split b loB n k (by omega) hB; linarith
        -- R₁ < B₁ and A_lo_k < β_k, so
        -- A_lo_k + R₁ * β_k < β_k + B₁ * β_k = (B₁ + 1) * β_k
        -- But we need < B = B₁ * β_k + B₀, which is stronger.
        -- Use R₁ ≤ B₁ - 1:
        -- A_lo_k + R₁ * β_k ≤ (β_k - 1) + (B₁ - 1) * β_k = B₁ * β_k - 1 < B = B₁ * β_k + B₀
        -- Avoid Nat subtraction issues by adding to both sides:
        rw [h_a_split, h_B_decomp']
        -- Goal: lo + R₁ * β < B₁ * β + B₀.
        -- We have lo ≤ β - 1 and R₁ ≤ B₁ - 1 in ℕ, i.e. lo + 1 ≤ β and R₁ + 1 ≤ B₁.
        -- lo + R₁ * β + 1 ≤ β + (B₁ - 1) * β = B₁ * β ≤ B₁ * β + B₀.
        have h_R1_succ : sliceVal a (loA + 2 * k) (n - k) + 1 ≤ sliceVal b (loB + k) (n - k) := by
          omega
        have h_lo_succ : sliceVal a (loA + k) k + 1 ≤ 2 ^ (64 * k) := by omega
        -- (R₁ + 1) * β ≤ B₁ * β
        have h1 : (sliceVal a (loA + 2 * k) (n - k) + 1) * 2 ^ (64 * k)
            ≤ sliceVal b (loB + k) (n - k) * 2 ^ (64 * k) :=
          Nat.mul_le_mul_right _ h_R1_succ
        -- lo + R₁ * β < (R₁ + 1) * β (since lo < β)
        have h2 : sliceVal a (loA + k) k + sliceVal a (loA + 2 * k) (n - k) * 2 ^ (64 * k)
            < (sliceVal a (loA + 2 * k) (n - k) + 1) * 2 ^ (64 * k) := by
          have : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
          nlinarith
        linarith
      linarith
    | true =>
      -- borrow = true, ec = 0: impossible.
      exfalso
      have h_delta5 : adj.2 = 5 := h_delta_fuel rfl h_borrow
      rw [h_delta5] at h_cons
      -- adj result < β (from toNatLimbsList_lt_pow)
      have h_adj_lt : sliceVal adj.1 (loA + k) (n + m - k) < 2 ^ (64 * (n + m - k)) := by
        have h := toNatLimbsList_lt_pow (adj.1.toList.drop (loA + k) |>.take (n + m - k))
        have h_len : (adj.1.toList.drop (loA + k) |>.take (n + m - k)).length = n + m - k := by
          rw [List.length_take, List.length_drop, Array.length_toList]
          apply Nat.min_eq_left
          have : adj.1.size = a.size :=
            (addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
              ((subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _))
          omega
        rw [h_len] at h; exact h
      -- subGeqLimbs with borrow=true
      have h_sub := subGeqLimbs_toNat a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
        h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
      simp only [List.drop_zero] at h_sub
      rw [show subRes.2.toNat = 1 from by rw [h_borrow]; rfl] at h_sub
      simp at h_sub
      -- From h_sub + h_cons: a2_val + β + 5*B = adj_val + q1b0_val
      -- From h_adj_lt: adj_val < β. So a2_val + 5*B < q1b0_val.
      -- From h_Q_B0_le: q1b0_val ≤ 4*B. So 5*B ≤ a2_val + 5*B < q1b0_val ≤ 4*B. ⊥
      have h_sub_bridge : sliceVal a2 (loA + k) (n + m - k) + 2 ^ (64 * (n + m - k))
          = sliceVal subRes.1 (loA + k) (n + m - k)
            + sliceVal q1_b0 0 (m + 1) := by
        show toNatLimbsList ((a2.toList.drop (loA + k)).take (n + m - k)) + 2 ^ (64 * (n + m - k))
          = toNatLimbsList ((subRes.1.toList.drop (loA + k)).take (n + m - k))
            + toNatLimbsList ((q1_b0.toList.drop 0).take (m + 1))
        exact h_sub
      have h_q1b0_le : sliceVal q1_b0 0 (m + 1) ≤ 4 * sliceVal b loB n := by
        have h_len_ge : m + 1 ≤ q1_b0.toList.length := by
          rw [Array.length_toList]; exact h_q1_b0_size
        have h_decomp := toNatLimbsList_take_drop q1_b0.toList (m + 1) h_len_ge
        have h_total : toNatLimbsList q1_b0.toList
            = toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k) := by
          have h := mulLimbs_toNat q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k
          simp only [List.drop_zero] at h
          rw [List.take_of_length_le (by rw [Array.length_toList]; omega)] at h; exact h
        show toNatLimbsList ((q1_b0.toList.drop 0).take (m + 1)) ≤ _
        simp only [List.drop_zero]
        have h_take_le_total : toNatLimbsList (q1_b0.toList.take (m + 1))
            ≤ toNatLimbsList q1_b0.toList := by omega
        linarith [h_take_le_total, h_total, h_Q_B0_le]
      linarith [h_sub_bridge, h_cons, h_adj_lt, h_q1b0_le]
  · -- ec = 1: direct from addbackLoop_combined's h_lt.
    exact h_lt (by omega)

/-- Clean conservation for stage 2 sub+addback: no borrow/end_carry terms.
    Mirrors `afterFirstRec_spec` but for the second adjustment stage
    (zeroed region is [loA+n, loA+n+k), addbackLoop at offset loA with highLen=n+m). -/
theorem recursiveDivModLimbs.afterSecondRec_spec
    (a b : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_Q0_B0_le : toNatLimbsList ((a.extract (loA + n) (loA + n + m / 2)).push
        q_top_0).toList * toNatLimbsList ((b.toList.drop loB).take (m / 2))
      ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n)) :
    let k := m / 2
    let q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
    let a6 := zeroFill a (loA + n) (loA + n + k)
    let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
    let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [zeroFill_size]; omega) (by
        show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k _ _).size
        have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
        omega)
      (by omega) (by omega) (by omega)
    let adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
      (by have : subRes2.1.size = a.size :=
            (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _)
          rw [this]; omega)
      hB (by omega) h_n_pos (by omega)
    toNatLimbsList ((a.toList.drop loA).take n)
      + toNatLimbsList ((a.toList.drop (loA + n + k)).take (m - k))
        * 2 ^ (64 * (n + k))
      + adj2.2 * toNatLimbsList ((b.toList.drop loB).take n)
    = toNatLimbsList ((adj2.1.toList.drop loA).take (n + m))
      + toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k) := by
  show _ = _
  set k := m / 2
  set q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_size : q0_arr.size = k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  have h_q0_hA : 0 + (k + 1) ≤ q0_arr.size := by rw [h_q0_size]; omega
  have h_loB_k : loB + k ≤ b.size := by omega
  set q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
  have h_q0_b0_size : 2 * k + 1 ≤ q0_b0.size := by
    show 2 * k + 1 ≤ (mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k).size
    have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k; omega
  have h_subGeq_hA : loA + (n + m) ≤ a6.size := by rw [h_a6_size]; omega
  have h_subGeq_hB : 0 + (2 * k + 1) ≤ q0_b0.size := by omega
  have h_subGeq := subGeqLimbs_toNat a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  simp only at h_subGeq
  set subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a7_size : subRes2.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_size
  have h_ab_hA : loA + 0 + (n + m) ≤ subRes2.1.size := by rw [h_a7_size]; omega
  have h_ab_n_le : n ≤ n + m := by omega
  have h_ab_high : 0 < n + m := by omega
  obtain ⟨ec, h_ec_le, h_addback, h_lt, h_delta_fuel⟩ :=
    addbackLoop_combined subRes2.1 b loA loB n 0 (n + m) 5
      h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
      subRes2.2 (fun _ => by omega)
  -- (A) h_a6_eq
  have h_a6_eq : toNatLimbsList ((a6.toList.drop loA).take (n + m))
      = toNatLimbsList ((a.toList.drop loA).take n)
        + toNatLimbsList ((a.toList.drop (loA + n + k)).take (m - k))
          * 2 ^ (64 * (n + k)) := by
    have h_split1 := sliceVal_split a6 loA (n + m) n (by omega) (by rw [h_a6_size]; omega)
    have h_split2 := sliceVal_split a6 (loA + n) m k (by omega) (by rw [h_a6_size]; omega)
    have h_low_eq : sliceVal a6 loA n = sliceVal a loA n := by
      apply sliceVal_eq_of_getElem_eq a6 a loA n (by rw [h_a6_size]; omega) (by omega)
      intro j h_j; exact zeroFill_get_outside a (loA + n) (loA + n + k) (loA + j)
        (Or.inl (by omega)) (by omega)
    have h_zero : sliceVal a6 (loA + n) k = 0 :=
      zeroFill_sliceVal_zero a (loA + n) k (by omega)
    have h_high_eq : sliceVal a6 (loA + n + k) (m - k) = sliceVal a (loA + n + k) (m - k) := by
      apply sliceVal_eq_of_getElem_eq a6 a (loA + n + k) (m - k)
        (by rw [h_a6_size]; omega) (by omega)
      intro j h_j; exact zeroFill_get_outside a (loA + n) (loA + n + k) (loA + n + k + j)
        (Or.inr (by omega)) (by omega)
    show sliceVal a6 loA (n + m) = sliceVal a loA n
        + sliceVal a (loA + n + k) (m - k) * 2 ^ (64 * (n + k))
    rw [h_split1, show n + m - n = m from by omega, h_split2, h_low_eq, h_zero, h_high_eq]
    have : (2 : Nat) ^ (64 * (n + k)) = 2 ^ (64 * k) * 2 ^ (64 * n) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [this]; ring
  -- (B) h_q0_b0_slice — use toNatLimbsList_take_drop to avoid conv_lhs
  have h_q0_b0_slice : toNatLimbsList ((q0_b0.toList.drop 0).take (2 * k + 1))
      = toNatLimbsList q0_arr.toList
        * toNatLimbsList ((b.toList.drop loB).take k) := by
    simp only [List.drop_zero]
    have h_total : toNatLimbsList q0_b0.toList
        = toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k) := by
      have h := mulLimbs_toNat q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
      simp only [List.drop_zero] at h
      rw [List.take_of_length_le (by rw [Array.length_toList]; omega)] at h; exact h
    have h_bound : toNatLimbsList q0_b0.toList < 2 ^ (64 * (2 * k + 1)) := by
      rw [h_total]
      have h_q0 := toNatLimbsList_lt_pow q0_arr.toList
      rw [show q0_arr.toList.length = k + 1 from by rw [Array.length_toList, h_q0_size]] at h_q0
      have h_b := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
      rw [show ((b.toList.drop loB).take k).length = k from by
        rw [List.length_take, List.length_drop, Array.length_toList]; omega] at h_b
      calc _ < 2 ^ (64 * (k + 1)) * 2 ^ (64 * k) :=
            Nat.mul_lt_mul_of_lt_of_le h_q0 (Nat.le_of_lt h_b) (Nat.two_pow_pos _)
        _ = 2 ^ (64 * (2 * k + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    have h_len_ge : 2 * k + 1 ≤ q0_b0.toList.length := by
      rw [Array.length_toList]; exact h_q0_b0_size
    have h_decomp := toNatLimbsList_take_drop q0_b0.toList (2 * k + 1) h_len_ge
    have h_high_zero : toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) = 0 := by
      by_contra h_ne
      have h_pos : 0 < toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) :=
        Nat.pos_of_ne_zero h_ne
      have h_lower : 2 ^ (64 * (2 * k + 1))
          ≤ toNatLimbsList (q0_b0.toList.drop (2 * k + 1)) * 2 ^ (64 * (2 * k + 1)) :=
        Nat.le_mul_of_pos_left _ h_pos
      linarith
    rw [← h_total, h_decomp, h_high_zero]; ring
  -- (C) Rewrite
  rw [h_a6_eq] at h_subGeq; rw [h_q0_b0_slice] at h_subGeq
  simp only [Nat.add_zero] at h_addback
  -- (D) Combine + mca_fuel_sufficiency
  have h_full : toNatLimbsList ((a.toList.drop loA).take n)
      + toNatLimbsList ((a.toList.drop (loA + n + k)).take (m - k)) * 2 ^ (64 * (n + k))
      + subRes2.2.toNat * 2 ^ (64 * (n + m))
      + (addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2
        * toNatLimbsList ((b.toList.drop loB).take n)
    = toNatLimbsList (((addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop loA).take (n + m))
      + toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
      + ec * 2 ^ (64 * (n + m)) := by linarith
  have h_borrow_eq_ec : subRes2.2.toNat = ec :=
    mca_fuel_sufficiency _ _ _ _ _ _ _ h_full (by cases subRes2.2 <;> decide) h_ec_le
      (by exact stage2_UD_lt_beta _ _ _ _ n k m
            (by have h := toNatLimbsList_lt_pow ((a.toList.drop loA).take n)
                simp [List.length_take, List.length_drop, Array.length_toList] at h
                exact h.trans_eq (by congr 1; omega))
            (by have h := toNatLimbsList_lt_pow ((a.toList.drop (loA + n + k)).take (m - k))
                simp [List.length_take, List.length_drop, Array.length_toList] at h
                exact h.trans_eq (by congr 1; omega))
            (by have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
                simp [List.length_take, List.length_drop, Array.length_toList] at h
                exact h.trans_eq (by congr 1; omega))
            (addbackLoop_delta_le _ _ _ _ _ _ _ _ 5 _ _ _ _ _)
            (by omega) (by omega))
      (by intro h_ec0 h_bor1
          have h_bor_bool : subRes2.2 = true := by
            cases h : subRes2.2
            · exfalso; simp [h] at h_bor1
            · rfl
          have h_delta5 := h_delta_fuel h_ec0 h_bor_bool
          have h_result_lt := toNatLimbsList_lt_pow
            ((addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
              h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop loA |>.take (n + m))
          have h_take_len : ((addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
              h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop loA |>.take (n + m)).length
              = n + m := by
            simp [List.length_take, List.length_drop, Array.length_toList,
              addbackLoop_size, h_a7_size]; omega
          rw [h_take_len] at h_result_lt
          simp only [h_ec0, Nat.zero_mul, Nat.add_zero, h_bor1, Nat.one_mul, h_delta5] at h_full
          linarith)
  rw [h_borrow_eq_ec] at h_full; linarith

/-- Pure-Nat "adjust spec" for the sub+addback pattern.  Given:
    - Conservation (after borrow/ec cancellation):
      `U + delta * B = result + Q * B₀`
    - `ec = 1 → result < B` (from addbackLoop_combined's h_lt)
    - `ec = 0 → borrow = true → delta = fuel` (fuel exhaustion)
    - `borrow = ec` (from mca_fuel_sufficiency)
    - `B₀ ≤ B` (low part of divisor ≤ full divisor)
    - `0 < B` (divisor is positive)
    Derives both:
    1. `delta ≤ Q`
    2. `result < B`

    The ec=1 case: `result < B` is given. Then `delta * B ≤ result + Q * B₀
    < B + Q * B ≤ (Q + 1) * B`, so `delta ≤ Q`.

    The ec=0 case (borrow = ec = 0): delta = 0, result = input (loop didn't
    run). `delta ≤ Q` holds trivially. `result < B` follows from the IH via
    the caller (not proven here — returned as a hypothesis obligation). -/
theorem adjust_spec_limbs
    (U delta B result Q B₀ : Nat)
    (h_cons : U + delta * B = result + Q * B₀)
    (h_B₀_le : B₀ ≤ B)
    (_ : 0 < B)
    (h_result_lt : result < B) :
    delta ≤ Q := by
  -- From h_cons: delta * B ≤ result + Q * B₀ (since U ≥ 0 in Nat).
  have h1 : delta * B ≤ result + Q * B₀ := by omega
  -- From h_B₀_le: Q * B₀ ≤ Q * B.
  have h2 : Q * B₀ ≤ Q * B := Nat.mul_le_mul_left Q h_B₀_le
  -- So delta * B < B + Q * B = (Q + 1) * B.
  have h3 : delta * B < (Q + 1) * B := by
    calc delta * B ≤ result + Q * B₀ := h1
      _ < B + Q * B := by linarith
      _ = (Q + 1) * B := by ring
  -- Cancel B: delta < Q + 1, i.e., delta ≤ Q.
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h3)

/-- Variant of `adjust_spec_limbs` for the two-case (ec=1 or ec=0) pattern
    from `addbackLoop_combined`.  When ec=1, `result < B` is given directly.
    When ec=0, delta=0 so `delta ≤ Q` is trivial regardless of `result < B`.

    Returns both `delta ≤ Q` and `result < B` (the latter via case analysis). -/
theorem adjust_spec_limbs_combined
    (U delta B result Q B₀ ec : Nat)
    (h_cons : U + delta * B = result + Q * B₀)
    (h_B₀_le : B₀ ≤ B)
    (h_B_pos : 0 < B)
    (h_ec_le : ec ≤ 1)
    (h_ec1_lt : ec = 1 → result < B)
    (h_ec0_delta : ec = 0 → delta = 0)
    (h_ec0_lt : ec = 0 → result < B) :
    delta ≤ Q ∧ result < B := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le ec) with h_ec0 | h_ec1
  · -- ec = 0: delta = 0, result < B from hypothesis.
    exact ⟨by rw [h_ec0_delta h_ec0.symm]; omega, h_ec0_lt h_ec0.symm⟩
  · -- ec ≥ 1, so ec = 1.
    have hec : ec = 1 := by omega
    have h_rlt := h_ec1_lt hec
    exact ⟨adjust_spec_limbs U delta B result Q B₀ h_cons h_B₀_le h_B_pos h_rlt, h_rlt⟩


set_option maxHeartbeats 800000 in
/-- The full (n+m)-limb addbackLoop result inside `afterSecondRec` is
    strictly less than the divisor B.  When ec=1, this is direct from
    `addbackLoop_combined`'s `h_lt`.  When ec=0, the bound follows from
    `h_ec0_bound` (the zeroed value < product + B) via subGeqLimbs_toNat. -/
theorem recursiveDivModLimbs.afterSecondRec_result_lt_B
    (a b : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_Q0_B0_le : toNatLimbsList ((a.extract (loA + n) (loA + n + m / 2)).push
        q_top_0).toList * toNatLimbsList ((b.toList.drop loB).take (m / 2))
      ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n))
    (h_ec0_bound : sliceVal (zeroFill a (loA + n) (loA + n + m / 2)) loA (n + m)
      < sliceVal (mulLimbs ((a.extract (loA + n) (loA + n + m / 2)).push q_top_0) b
          0 (m / 2 + 1) loB (m / 2)
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega))
        0 (2 * (m / 2) + 1)
      + sliceVal b loB n) :
    let k := m / 2
    let q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
    let a6 := zeroFill a (loA + n) (loA + n + k)
    let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
    let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [zeroFill_size]; omega) (by
        show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k _ _).size
        have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
        omega)
      (by omega) (by omega) (by omega)
    let adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
      (by have : subRes2.1.size = a.size :=
            (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _)
          rw [this]; omega)
      hB (by omega) h_n_pos (by omega)
    sliceVal adj2.1 loA (n + m) < sliceVal b loB n := by
  show _ < _
  set k := m / 2
  set q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_size : q0_arr.size = k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  have h_q0_hA : 0 + (k + 1) ≤ q0_arr.size := by rw [h_q0_size]; omega
  have h_loB_k : loB + k ≤ b.size := by omega
  set q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
  have h_q0_b0_size : 2 * k + 1 ≤ q0_b0.size := by
    show 2 * k + 1 ≤ (mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k).size
    have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k; omega
  have h_subGeq_hA : loA + (n + m) ≤ a6.size := by rw [h_a6_size]; omega
  have h_subGeq_hB : 0 + (2 * k + 1) ≤ q0_b0.size := by omega
  set subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a7_size : subRes2.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_size
  have h_ab_hA : loA + 0 + (n + m) ≤ subRes2.1.size := by rw [h_a7_size]; omega
  have h_ab_n_le : n ≤ n + m := by omega
  have h_ab_high : 0 < n + m := by omega
  obtain ⟨ec, h_ec_le, h_addback, h_lt, h_delta_fuel⟩ :=
    addbackLoop_combined subRes2.1 b loA loB n 0 (n + m) 5
      h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
      subRes2.2 (fun _ => by omega)
  set adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
    h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
  simp only [Nat.add_zero] at h_lt
  rcases Nat.eq_or_lt_of_le (Nat.zero_le ec) with h_ec0 | h_ec1
  · -- ec = 0: derive from h_ec0_bound + subGeqLimbs_toNat.
    have hec : ec = 0 := h_ec0.symm
    subst hec
    simp only [Nat.zero_mul, Nat.add_zero, Nat.add_zero] at h_addback
    -- h_addback: input + adj2.2 * B = output (in toNatLimbsList form).
    -- Convert to sliceVal form.
    have h_cons : sliceVal subRes2.1 loA (n + m) + adj2.2 * sliceVal b loB n
        = sliceVal adj2.1 loA (n + m) := h_addback
    -- Case split on borrow (subRes2.2).
    cases h_borrow : subRes2.2 with
    | false =>
      -- borrow = false: addbackLoop with false borrow returns (input, 0).
      -- So adj2.2 = 0 and adj2.1 = subRes2.1.
      -- From h_cons with adj2.2 = 0: subRes2_val = adj2_val.
      have h_adj2_2 : adj2.2 = 0 := by
        show (addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2 = 0
        rw [h_borrow]; unfold addbackLoop; simp
      rw [h_adj2_2, Nat.zero_mul, Nat.add_zero] at h_cons
      -- h_cons: sliceVal subRes2.1 loA (n+m) = sliceVal adj2.1 loA (n+m)
      rw [← h_cons]
      -- From subGeqLimbs_toNat with borrow = false:
      --   sliceVal a6 loA (n+m) = sliceVal subRes2.1 loA (n+m) + sliceVal q0_b0 0 (2*k+1)
      have h_subGeq := subGeqLimbs_toNat a6 q0_b0 loA (n + m) 0 (2 * k + 1)
        h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
      simp only [List.drop_zero] at h_subGeq
      have h_borrow_zero : (subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
          h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)).2.toNat = 0 := by
        have : (subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
            h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)).2 = subRes2.2 := rfl
        rw [this, h_borrow]; decide
      rw [h_borrow_zero, Nat.zero_mul, Nat.add_zero] at h_subGeq
      -- h_subGeq: sliceVal a6 loA (n+m) = sliceVal subRes2.1 loA (n+m) + sliceVal q0_b0 0 (2*k+1)
      have h_subGeq' : sliceVal a6 loA (n + m)
          = sliceVal subRes2.1 loA (n + m) + sliceVal q0_b0 0 (2 * k + 1) := h_subGeq
      linarith [h_ec0_bound]
    | true =>
      -- borrow = true, ec = 0: unreachable.
      -- Chain: a6_val + β + 5*B = result + q0b0_val, result < β, q0b0_val ≤ 4*B
      -- → a6_val + 5*B < 4*B → impossible in Nat.
      exfalso
      have h_delta5 : adj2.2 = 5 := h_delta_fuel rfl h_borrow
      rw [h_delta5] at h_cons
      -- h_cons: sliceVal subRes2.1 loA (n+m) + 5*B = sliceVal adj2.1 loA (n+m)
      -- h_ec0_bound: sliceVal a6 loA (n+m) < sliceVal q0_b0 0 (2*k+1) + B
      -- adj2 result < β (from toNatLimbsList_lt_pow):
      have h_adj2_lt : sliceVal adj2.1 loA (n + m) < 2 ^ (64 * (n + m)) := by
        have h := toNatLimbsList_lt_pow (adj2.1.toList.drop loA |>.take (n + m))
        have h_len : (adj2.1.toList.drop loA |>.take (n + m)).length = n + m := by
          rw [List.length_take, List.length_drop, Array.length_toList]
          apply Nat.min_eq_left
          have : adj2.1.size = a.size :=
            (addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
              ((subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _))
          omega
        rw [h_len] at h; exact h
      -- subGeqLimbs with borrow=true: a6_val + β = subRes2_val + q0b0_take_val
      have h_sub := subGeqLimbs_toNat a6 q0_b0 loA (n + m) 0 (2 * k + 1)
        h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
      simp only [List.drop_zero] at h_sub
      rw [show subRes2.2.toNat = 1 from by rw [h_borrow]; rfl] at h_sub
      simp at h_sub
      -- h_sub: sliceVal a6 loA (n+m) + 2^(64*(n+m))
      --      = sliceVal subRes2.1 loA (n+m) + sliceVal q0_b0 0 (2*k+1)
      -- From h_cons + h_sub: a6_val + β + 5*B = adj2_val + q0b0_val
      -- From h_adj2_lt: adj2_val < β
      -- From h_Q0_B0_le: Q₀*B₀ ≤ 4*B. Need: q0b0_val ≤ 4*B.
      -- Actually just use h_ec0_bound: a6_val < q0b0_val + B.
      -- Combined: a6_val + β + 5*B < β + q0b0_val (from adj2_val < β)
      --         → a6_val + 5*B < q0b0_val
      --         → q0b0_val > 5*B ≥ 0
      -- But from h_ec0_bound: a6_val < q0b0_val + B → q0b0_val > a6_val - B
      -- So: a6_val + 5*B < q0b0_val ≤ 4*B + ... hmm just use linarith
      -- Key: a6_val + β + 5*B = adj2_val + q0b0_val AND adj2_val < β
      -- → a6_val + 5*B < q0b0_val. But a6_val ≥ 0 → 5*B < q0b0_val.
      -- And q0b0_val = sliceVal q0_b0 0 (2*k+1) ≤ toNatLimbsList q0_b0.toList = Q₀*B₀ ≤ 4*B.
      -- So 5*B ≤ q0b0_val ≤ 4*B → 5*B ≤ 4*B → False.
      -- Need: sliceVal q0_b0 0 (2*k+1) ≤ 4*B from h_Q0_B0_le + slice ≤ total.
      -- Bridge syntactic gaps between h_sub terms and sliceVal:
      have h_sub_bridge : sliceVal a6 loA (n + m) + 2 ^ (64 * (n + m))
          = sliceVal subRes2.1 loA (n + m)
            + sliceVal q0_b0 0 (2 * k + 1) := by
        show toNatLimbsList ((a6.toList.drop loA).take (n + m)) + 2 ^ (64 * (n + m))
          = toNatLimbsList ((subRes2.1.toList.drop loA).take (n + m))
            + toNatLimbsList ((q0_b0.toList.drop 0).take (2 * k + 1))
        exact h_sub
      -- Chain: a6_val + β + 5*B = adj2_val + q0b0_val (from h_sub_bridge + h_cons)
      -- adj2_val < β, so a6_val + 5*B < q0b0_val. But a6_val ≥ 0, so 5*B ≤ q0b0_val.
      -- And from h_ec0_bound: q0b0_val < a6_val + B... wait we need q0b0_val ≤ 4*B.
      -- Actually: from h_sub_bridge + h_cons: a6_val + β + 5*B = adj2_val + q0b0_val.
      -- From h_adj2_lt: adj2_val < β.
      -- So a6_val + β + 5*B < β + q0b0_val → a6_val + 5*B < q0b0_val.
      -- From h_ec0_bound: a6_val < q0b0_val + B.
      -- Combine: q0b0_val > a6_val + 5*B > 5*B - 1 ≥ 4*B (when B ≥ 1).
      -- But h_ec0_bound says a6 < q0b0 + B, giving q0b0 > a6 - B ≥ -B. Hmm.
      -- Actually just: a6 + 5*B < q0b0 AND a6 ≥ 0 → q0b0 > 5*B.
      -- And q0b0 = sliceVal q0_b0 0 (2*k+1). From h_ec0_bound: a6 < q0b0 + B,
      -- so q0b0 > a6 - B ≥ -B... in Nat this means nothing since a6 could be 0.
      -- The contradiction: from a6 + 5*B < q0b0 and a6 ≥ 0: 5*B ≤ a6 + 5*B.
      -- Wait no: a6 + 5*B < q0b0 means q0b0 > a6 + 5*B ≥ 5*B.
      -- And from h_ec0_bound: a6 < q0b0 + B. With q0b0 ≤ 4*B (from h_Q0_B0_le somehow):
      -- a6 < 4*B + B = 5*B. And a6 + 5*B < q0b0 ≤ 4*B. Then a6 + 5*B < 4*B, a6 < -B. ⊥.
      -- So we need q0b0 ≤ 4*B. From h_Q0_B0_le.
      -- But h_Q0_B0_le is about toNatLimbsList q0_arr.toList * ..., not sliceVal q0_b0 0 (2*k+1).
      -- Use h_ec0_bound directly for the contradiction:
      -- h_ec0_bound: a6_val < q0b0_val + B. And h_sub_bridge + h_cons: a6_val + β + 5*B = adj2_val + q0b0_val.
      -- So: (q0b0_val + B - 1) + β + 5*B > a6_val + β + 5*B = adj2_val + q0b0_val.
      -- i.e., q0b0_val + 6*B - 1 + β > adj2_val + q0b0_val → 6*B - 1 + β > adj2_val.
      -- Not useful. Let me just use the numerical chain directly:
      -- From h_sub_bridge: subRes2_val = a6_val + β - q0b0_val.
      -- From h_cons: subRes2_val + 5*B = adj2_val.
      -- So: adj2_val = a6_val + β - q0b0_val + 5*B.
      -- From h_adj2_lt: adj2_val < β. So: a6_val + β - q0b0_val + 5*B < β.
      -- Hence: a6_val + 5*B < q0b0_val.
      -- From h_ec0_bound: a6_val < q0b0_val + B. So q0b0_val > a6_val - B.
      -- Contradiction: a6_val + 5*B < q0b0_val AND (need q0b0_val ≤ something small).
      -- Without q0b0 ≤ 4*B, just use: a6_val ≥ 0, so 5*B ≤ a6_val + 5*B < q0b0_val.
      -- And q0b0 = toNatLimbsList take (2*k+1) of q0_b0. This is < 2^(64*(2*k+1)) ≤ 2^(64*(n+m)).
      -- And 5*B < q0b0 < 2^(64*(n+m)). No contradiction from this alone.
      -- We NEED q0b0_val ≤ 4*B. This IS h_Q0_B0_le after connecting q0b0_val = Q₀*B₀.
      -- Derive it from toNatLimbsList_take_drop (same as afterSecondRec_spec's h_q0_b0_slice):
      have h_q0b0_le : sliceVal q0_b0 0 (2 * k + 1) ≤ 4 * sliceVal b loB n := by
        -- sliceVal q0_b0 0 (2*k+1) ≤ toNatLimbsList q0_b0.toList = Q₀*B₀ ≤ 4*B
        have h_len_ge : 2 * k + 1 ≤ q0_b0.toList.length := by
          rw [Array.length_toList]; exact h_q0_b0_size
        have h_decomp := toNatLimbsList_take_drop q0_b0.toList (2 * k + 1) h_len_ge
        have h_total : toNatLimbsList q0_b0.toList
            = toNatLimbsList q0_arr.toList * toNatLimbsList ((b.toList.drop loB).take k) := by
          have h := mulLimbs_toNat q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
          simp only [List.drop_zero] at h
          rw [List.take_of_length_le (by rw [Array.length_toList]; omega)] at h; exact h
        -- sliceVal q0_b0 0 (2*k+1) ≤ total = Q₀*B₀ ≤ 4*B
        show toNatLimbsList ((q0_b0.toList.drop 0).take (2 * k + 1)) ≤ _
        simp only [List.drop_zero]
        have h_take_le_total : toNatLimbsList (q0_b0.toList.take (2 * k + 1))
            ≤ toNatLimbsList q0_b0.toList := by omega
        linarith [h_take_le_total, h_total, h_Q0_B0_le]
      linarith [h_sub_bridge, h_cons, h_adj2_lt, h_q0b0_le]
  · -- ec = 1: direct from addbackLoop_combined's h_lt.
    exact h_lt (by omega)

set_option maxHeartbeats 800000 in
/-- The low n limbs of `afterSecondRec`'s output equal the low n limbs
    of the internal addbackLoop result `adj2`.  This is because
    `writeSlice` at offset `loA+n` preserves positions below `loA+n`. -/
theorem recursiveDivModLimbs.afterSecondRec_low_eq
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_q1_arr'_size : q1_arr'.size = m - m / 2 + 1) :
    let k := m / 2
    let q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
    let a6 := zeroFill a (loA + n) (loA + n + k)
    let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
    let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [zeroFill_size]; omega) (by
        show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k _ _).size
        have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
        omega)
      (by omega) (by omega) (by omega)
    let adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
      (by have : subRes2.1.size = a.size :=
            (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _)
          rw [this]; omega)
      hB (by omega) h_n_pos (by omega)
    sliceVal (recursiveDivModLimbs.afterSecondRec a b q1_arr' q_top_0 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2 h_q1_arr'_size).1 loA n
    = sliceVal adj2.1 loA n := by
  show _ = _
  unfold recursiveDivModLimbs.afterSecondRec; simp only
  set k := m / 2
  set q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_size : q0_arr.size = k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  have h_q0_hA : 0 + (k + 1) ≤ q0_arr.size := by rw [h_q0_size]; omega
  have h_loB_k : loB + k ≤ b.size := by omega
  set q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
  have h_subGeq_hA : loA + (n + m) ≤ a6.size := by rw [h_a6_size]; omega
  have h_subGeq_hB : 0 + (2 * k + 1) ≤ q0_b0.size := by
    show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k).size
    have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k; omega
  set subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a7_size : subRes2.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_size
  have h_ab_hA : loA + 0 + (n + m) ≤ subRes2.1.size := by rw [h_a7_size]; omega
  have h_ab_n_le : n ≤ n + m := by omega
  have h_ab_high : 0 < n + m := by omega
  set adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
    h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
  have h_a8_size : adj2.1.size = a.size :=
    (addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans h_a7_size
  -- Set Q-assembly arrays.
  set q0_arr' := decrementSlice q0_arr 0 adj2.2 (Nat.zero_le _)
  have h_q0_arr'_size : q0_arr'.size = k + 1 := by
    show (decrementSlice _ _ _ _).size = _; rw [decrementSlice_size]; exact h_q0_size
  set tempQ : Array UInt64 := Array.replicate (m + 1) 0
  have h_tempQ_size : tempQ.size = m + 1 := Array.size_replicate
  set tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
    (by rw [h_tempQ_size]; omega) (by rw [h_q0_arr'_size]; omega)
  have h_tempQ1_size : tempQ1.size = m + 1 := by
    show (writeSlice _ _ _ _ _ _ _ _).size = _; rw [writeSlice_size]; exact h_tempQ_size
  set addRes := addSameLengthLimbs tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1_arr'_size]; omega)
  set tempQ2 := addRes.1
  have h_tempQ2_size : tempQ2.size = m + 1 :=
    (addSameLengthLimbs_size tempQ1 q1_arr' k 0 (m - k + 1)
      (by rw [h_tempQ1_size]; omega) (by rw [h_q1_arr'_size]; omega)).trans h_tempQ1_size
  -- writeSlice at loA+n preserves [loA, loA+n).
  have h_ws_hA : loA + n + m ≤ adj2.1.size := by rw [h_a8_size]; omega
  have h_ws_hS : 0 + m ≤ tempQ2.size := by rw [h_tempQ2_size]; omega
  apply sliceVal_eq_of_getElem_eq _ adj2.1 loA n
    (by rw [writeSlice_size, h_a8_size]; omega) (by rw [h_a8_size]; omega)
  intro j h_j
  exact writeSlice_get_outside adj2.1 tempQ2 (loA + n) 0 m 0
    h_ws_hA h_ws_hS (loA + j) (Or.inl (by omega))
    (by rw [h_a8_size]; omega)

/-- The remainder after `afterSecondRec` is strictly less than the divisor.
    Follows from `afterSecondRec_result_lt_B`: the full (n+m)-limb result < B,
    and since the low n limbs ≤ the full (n+m)-limb value, the low n limbs < B. -/
theorem recursiveDivModLimbs.afterSecondRec_rem_lt
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_q1_arr'_size : q1_arr'.size = m - m / 2 + 1)
    (h_Q0_B0_le : toNatLimbsList ((a.extract (loA + n) (loA + n + m / 2)).push
        q_top_0).toList * toNatLimbsList ((b.toList.drop loB).take (m / 2))
      ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n))
    (_ : sliceVal a (loA + m / 2) (n - m / 2)
      < sliceVal b (loB + m / 2) (n - m / 2))
    (h_ec0_bound : sliceVal (zeroFill a (loA + n) (loA + n + m / 2)) loA (n + m)
      < sliceVal (mulLimbs ((a.extract (loA + n) (loA + n + m / 2)).push q_top_0) b
          0 (m / 2 + 1) loB (m / 2)
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega))
        0 (2 * (m / 2) + 1)
      + sliceVal b loB n) :
    sliceVal (recursiveDivModLimbs.afterSecondRec a b q1_arr' q_top_0 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2 h_q1_arr'_size).1 loA n
    < sliceVal b loB n := by
  show sliceVal _ loA n < sliceVal b loB n
  unfold recursiveDivModLimbs.afterSecondRec; simp only
  set k := m / 2
  set q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_size : q0_arr.size = k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  have h_q0_hA : 0 + (k + 1) ≤ q0_arr.size := by rw [h_q0_size]; omega
  have h_loB_k : loB + k ≤ b.size := by omega
  set q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
  have h_q0_b0_size : 2 * k + 1 ≤ q0_b0.size := by
    show 2 * k + 1 ≤ (mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k).size
    have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k; omega
  have h_subGeq_hA : loA + (n + m) ≤ a6.size := by rw [h_a6_size]; omega
  have h_subGeq_hB : 0 + (2 * k + 1) ≤ q0_b0.size := by omega
  set subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a7_size : subRes2.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_size
  have h_ab_hA : loA + 0 + (n + m) ≤ subRes2.1.size := by rw [h_a7_size]; omega
  have h_ab_n_le : n ≤ n + m := by omega
  have h_ab_high : 0 < n + m := by omega
  set adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
    h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
  have h_a8_size : adj2.1.size = a.size :=
    (addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans h_a7_size
  -- Use afterSecondRec_result_lt_B: sliceVal adj2.1 loA (n+m) < B.
  have h_full_lt : sliceVal adj2.1 loA (n + m) < sliceVal b loB n :=
    recursiveDivModLimbs.afterSecondRec_result_lt_B a b q_top_0 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2 h_Q0_B0_le h_ec0_bound
  -- sliceVal adj2.1 loA n ≤ sliceVal adj2.1 loA (n+m) via sliceVal_split.
  have h_lo_le : sliceVal adj2.1 loA n ≤ sliceVal adj2.1 loA (n + m) := by
    have h := sliceVal_split adj2.1 loA (n + m) n (by omega) (by rw [h_a8_size]; omega)
    rw [h]; omega
  -- Set the Q-assembly arrays (tempQ, tempQ1, tempQ2) and their sizes.
  set q0_arr' := decrementSlice q0_arr 0 adj2.2 (Nat.zero_le _)
  have h_q0_arr'_size : q0_arr'.size = k + 1 := by
    show (decrementSlice _ _ _ _).size = _; rw [decrementSlice_size]; exact h_q0_size
  set tempQ : Array UInt64 := Array.replicate (m + 1) 0
  have h_tempQ_size : tempQ.size = m + 1 := Array.size_replicate
  set tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
    (by rw [h_tempQ_size]; omega) (by rw [h_q0_arr'_size]; omega)
  have h_tempQ1_size : tempQ1.size = m + 1 := by
    show (writeSlice _ _ _ _ _ _ _ _).size = _; rw [writeSlice_size]; exact h_tempQ_size
  set addRes := addSameLengthLimbs tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1_arr'_size]; omega)
  set tempQ2 := addRes.1
  have h_tempQ2_size : tempQ2.size = m + 1 :=
    (addSameLengthLimbs_size tempQ1 q1_arr' k 0 (m - k + 1)
      (by rw [h_tempQ1_size]; omega) (by rw [h_q1_arr'_size]; omega)).trans h_tempQ1_size
  -- writeSlice preserves [loA, loA+n).
  have h_ws_hA : loA + n + m ≤ adj2.1.size := by rw [h_a8_size]; omega
  have h_ws_hS : 0 + m ≤ tempQ2.size := by rw [h_tempQ2_size]; omega
  calc sliceVal (writeSlice adj2.1 tempQ2 (loA + n) 0 m 0 h_ws_hA h_ws_hS) loA n
      = sliceVal adj2.1 loA n := by
        apply sliceVal_eq_of_getElem_eq _ adj2.1 loA n
          (by rw [writeSlice_size, h_a8_size]; omega) (by rw [h_a8_size]; omega)
        intro j h_j
        exact writeSlice_get_outside adj2.1 tempQ2 (loA + n) 0 m 0
          h_ws_hA h_ws_hS (loA + j) (Or.inl (by omega))
          (by rw [h_a8_size]; omega)
    _ < sliceVal b loB n := by linarith

/-- Algebraic identity: `(S - X * P) * Q + X * (P * Q) = S * Q` when
    `X * P ≤ S`.  Extracted to avoid `linarith` timeouts on large terms. -/
private theorem nat_sub_mul_cancel (S X P Q : Nat) (h_le : X * P ≤ S) :
    (S - X * P) * Q + X * (P * Q) = S * Q := by
  have h1 : X * (P * Q) = X * P * Q := by ring
  rw [h1]
  have h2 : (S - X * P) * Q + X * P * Q = (S - X * P + X * P) * Q := by
    rw [Nat.add_mul]
  rw [h2, Nat.sub_add_cancel h_le]

/-- Sub-lemma: after writing `q0_arr'` into the first `k+1` positions of a
    zero-replicate buffer of size `m+1`, the full buffer value equals
    `q0_arr'.toNat`. -/
private theorem tempQ1_value (q0_arr' : Array UInt64) (m k : Nat)
    (hk : k ≤ m) (h_q0' : q0_arr'.size = k + 1) :
    let tempQ := Array.replicate (m + 1) (0 : UInt64)
    let tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
      (by rw [Array.size_replicate]; omega) (by rw [h_q0']; omega)
    sliceVal tempQ1 0 (m + 1) = toNatLimbsList q0_arr'.toList := by
  intro tempQ tempQ1
  have h_tempQ_size : tempQ.size = m + 1 := Array.size_replicate
  have h_tempQ1_size : tempQ1.size = m + 1 := by
    show (writeSlice _ _ _ _ _ _ _ _).size = _
    rw [writeSlice_size, h_tempQ_size]
  have h := sliceVal_split tempQ1 0 (m + 1) (k + 1) (by omega)
    (by rw [h_tempQ1_size]; omega)
  have h_diff : (m + 1) - (k + 1) = m - k := by omega
  have h_idx : 0 + (k + 1) = k + 1 := by omega
  rw [h_diff, h_idx] at h
  have h_low : sliceVal tempQ1 0 (k + 1) = toNatLimbsList q0_arr'.toList := by
    have h_ws := writeSlice_sliceVal tempQ q0_arr' 0 0 (k + 1)
      (by rw [h_tempQ_size]; omega) (by rw [h_q0']; omega)
    show toNatLimbsList ((tempQ1.toList.drop 0).take (k + 1)) = _
    rw [h_ws, List.drop_zero, List.take_of_length_le]
    rw [Array.length_toList, h_q0']
  have h_high : sliceVal tempQ1 (k + 1) (m - k) = 0 := by
    apply (sliceVal_eq_of_getElem_eq tempQ1 tempQ (k + 1) (m - k)
      (by rw [h_tempQ1_size]; omega) (by rw [h_tempQ_size]; omega) ?_).trans
    · exact Array.replicate_sliceVal_zero (m + 1) (k + 1) (m - k)
    · intro j h_j
      exact writeSlice_get_outside tempQ q0_arr' 0 0 (k + 1) 0
        (by rw [h_tempQ_size]; omega) (by rw [h_q0']; omega)
        (k + 1 + j) (Or.inr (by omega)) (by rw [h_tempQ_size]; omega)
  rw [h_low, h_high] at h; linarith

/-- Sub-lemma (parametrized): given a tempQ2 array that arose from adding
    `q1_arr'` at offset `k` into a buffer whose full value is `Q0_val`,
    the result satisfies the Q-assembly conservation.  Parametrized on
    the array + carry to avoid kernel reduction of `addSameLengthLimbs`. -/
private theorem tempQ2_conservation_param
    (tempQ1 tempQ2_arr : Array UInt64) (carry : Bool) (Q0_val : Nat)
    (m k : Nat) (hk : k ≤ m) (_ : 0 < k)
    (q1_val : Nat)
    (h_tempQ1_size : tempQ1.size = m + 1)
    (h_tempQ2_size : tempQ2_arr.size = m + 1)
    (h_tempQ1_val : sliceVal tempQ1 0 (m + 1) = Q0_val)
    (h_addSL : sliceVal tempQ2_arr k (m - k + 1) + carry.toNat * 2 ^ (64 * (m - k + 1))
        = sliceVal tempQ1 k (m - k + 1) + q1_val)
    (h_low_eq : sliceVal tempQ2_arr 0 k = sliceVal tempQ1 0 k) :
    sliceVal tempQ2_arr 0 (m + 1) + carry.toNat * 2 ^ (64 * (m + 1))
      = Q0_val + q1_val * 2 ^ (64 * k) := by
  -- Decompose tempQ2_arr at k.
  have h_at_k : sliceVal tempQ2_arr 0 (m + 1)
      = sliceVal tempQ2_arr 0 k + sliceVal tempQ2_arr k (m - k + 1) * 2 ^ (64 * k) := by
    have h := sliceVal_split tempQ2_arr 0 (m + 1) k (by omega)
      (by rw [h_tempQ2_size]; omega)
    have h_d : (m + 1) - k = m - k + 1 := by omega
    have h_i : 0 + k = k := by omega
    rw [h_d, h_i] at h; exact h
  -- Decompose tempQ1 at k.
  have h_tempQ1_at_k : sliceVal tempQ1 0 (m + 1)
      = sliceVal tempQ1 0 k + sliceVal tempQ1 k (m - k + 1) * 2 ^ (64 * k) := by
    have h := sliceVal_split tempQ1 0 (m + 1) k (by omega)
      (by rw [h_tempQ1_size]; omega)
    have h_d : (m + 1) - k = m - k + 1 := by omega
    have h_i : 0 + k = k := by omega
    rw [h_d, h_i] at h; exact h
  -- β^(m+1) = β^(m-k+1) * β^k.
  have h_β : (2 : Nat) ^ (64 * (m + 1)) = 2 ^ (64 * (m - k + 1)) * 2 ^ (64 * k) := by
    have h : 64 * (m - k + 1) + 64 * k = 64 * (m + 1) := by omega
    rw [← h, Nat.pow_add]
  -- From h_addSL: tempQ2 k = tempQ1 k + q1_val - carry * β^(m-k+1).
  have h_addSL_le : carry.toNat * 2 ^ (64 * (m - k + 1))
      ≤ sliceVal tempQ1 k (m - k + 1) + q1_val := by linarith
  have h_tempQ2_k : sliceVal tempQ2_arr k (m - k + 1)
      = sliceVal tempQ1 k (m - k + 1) + q1_val
        - carry.toNat * 2 ^ (64 * (m - k + 1)) := by omega
  -- Apply nat_sub_mul_cancel to simplify the subtraction + carry.
  have h_cancel := nat_sub_mul_cancel
    (sliceVal tempQ1 k (m - k + 1) + q1_val)
    carry.toNat (2 ^ (64 * (m - k + 1))) (2 ^ (64 * k)) h_addSL_le
  -- Chain: tempQ2 0 (m+1) + carry * β^(m+1) = tempQ1 0 k + (tempQ1 k + q1_val) * β^k.
  have h_step1 : sliceVal tempQ2_arr 0 (m + 1) + carry.toNat * 2 ^ (64 * (m + 1))
      = sliceVal tempQ1 0 k + (sliceVal tempQ1 k (m - k + 1) + q1_val) * 2 ^ (64 * k) := by
    have h_eq : sliceVal tempQ2_arr 0 (m + 1)
        = sliceVal tempQ1 0 k
          + (sliceVal tempQ1 k (m - k + 1) + q1_val
              - carry.toNat * 2 ^ (64 * (m - k + 1))) * 2 ^ (64 * k) := by
      rw [h_at_k, h_low_eq, h_tempQ2_k]
    rw [h_eq, h_β]; linarith [h_cancel]
  -- = tempQ1 0 (m+1) + q1_val * β^k = Q0_val + q1_val * β^k.
  have h_expand : sliceVal tempQ1 0 k
      + (sliceVal tempQ1 k (m - k + 1) + q1_val) * 2 ^ (64 * k)
      = sliceVal tempQ1 0 (m + 1) + q1_val * 2 ^ (64 * k) := by
    have : (sliceVal tempQ1 k (m - k + 1) + q1_val) * 2 ^ (64 * k)
        = sliceVal tempQ1 k (m - k + 1) * 2 ^ (64 * k) + q1_val * 2 ^ (64 * k) := by
      ring
    linarith [h_tempQ1_at_k]
  linarith [h_step1, h_expand]

/-- Q-assembly conservation for `afterSecondRec`'s post-addback phase.

    Given the post-addback state (`a8`, with adjusted `q0_arr'` derived
    from decrementing `q0_arr` by `delta0`, and the incoming `q1_arr'`),
    the assembly steps produce `tempQ2` and `a9` such that:

    `sliceVal a9 (loA + n) m + tempQ2[m].toNat * β^m + carry * β^(m+1)
      = q0_arr'.toNat + q1_arr'.toNat * β^k`

    where `carry ∈ {0, 1}` is the `addSameLengthLimbs` overflow.  For
    well-behaved Q₀, Q₁ bounds (each ≤ 2 · β^len), `carry = 0`. -/
theorem recursiveDivModLimbs.afterSecondRec_assembly_toNat
    (a8 q0_arr' q1_arr' : Array UInt64) (m k : Nat)
    (hk : k ≤ m) (h_k_pos : 0 < k) (_ : k + 1 ≤ m + 1)
    (h_q0' : q0_arr'.size = k + 1) (h_q1' : q1_arr'.size = m - k + 1)
    (loA n : Nat) (hA : loA + n + m ≤ a8.size) (_ : 0 < n) :
    let tempQ : Array UInt64 := Array.replicate (m + 1) 0
    let tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
      (by rw [Array.size_replicate]; omega) (by rw [h_q0']; omega)
    let addRes := addSameLengthLimbs tempQ1 q1_arr' k 0 (m - k + 1)
      (by rw [writeSlice_size, Array.size_replicate]; omega)
      (by rw [h_q1']; omega)
    let tempQ2 := addRes.1
    have h_tempQ2_size : tempQ2.size = m + 1 := by
      show (addSameLengthLimbs _ _ _ _ _ _ _).1.size = m + 1
      rw [addSameLengthLimbs_size, writeSlice_size, Array.size_replicate]
    let a9 := writeSlice a8 tempQ2 (loA + n) 0 m 0
      (by omega) (by rw [h_tempQ2_size]; omega)
    have h_top_idx : m < tempQ2.size := by rw [h_tempQ2_size]; omega
    ∃ assembly_carry : Nat, assembly_carry ≤ 1 ∧
      toNatLimbsList ((a9.toList.drop (loA + n)).take m)
        + (tempQ2[m]'h_top_idx).toNat * 2 ^ (64 * m)
        + assembly_carry * 2 ^ (64 * (m + 1))
      = toNatLimbsList q0_arr'.toList
        + toNatLimbsList q1_arr'.toList * 2 ^ (64 * k) := by
  show ∃ _, _
  -- Use tempQ1_value and tempQ2_conservation_param.
  set tempQ := Array.replicate (m + 1) (0 : UInt64)
  set tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
    (by rw [Array.size_replicate]; omega) (by rw [h_q0']; omega)
  have h_tempQ1_size : tempQ1.size = m + 1 := by
    show (writeSlice _ _ _ _ _ _ _ _).size = _; rw [writeSlice_size, Array.size_replicate]
  set addRes := addSameLengthLimbs tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1']; omega)
  set tempQ2 := addRes.1
  have h_tempQ2_size : tempQ2.size = m + 1 := by
    show (addSameLengthLimbs _ _ _ _ _ _ _).1.size = _
    rw [addSameLengthLimbs_size, h_tempQ1_size]
  have h_top_idx : m < tempQ2.size := by omega
  set a9 := writeSlice a8 tempQ2 (loA + n) 0 m 0 (by omega) (by rw [h_tempQ2_size]; omega)
  -- (1) sliceVal a9 (loA + n) m = sliceVal tempQ2 0 m.
  have h_a9 := writeSlice_sliceVal a8 tempQ2 (loA + n) 0 m (by omega) (by rw [h_tempQ2_size]; omega)
  -- (2) tempQ2 0 (m+1) = sliceVal tempQ2 0 m + tempQ2[m] * β^m.
  have h_split : sliceVal tempQ2 0 (m + 1)
      = sliceVal tempQ2 0 m + sliceVal tempQ2 m 1 * 2 ^ (64 * m) := by
    have h := sliceVal_split tempQ2 0 (m + 1) m (by omega) (by rw [h_tempQ2_size]; omega)
    have : (m + 1) - m = 1 := by omega
    have : (0 : Nat) + m = m := by omega
    simp only [*] at h; exact h
  -- (3) sliceVal tempQ2 m 1 = tempQ2[m].toNat (single-limb slice value).
  have h_top : sliceVal tempQ2 m 1 = (tempQ2[m]'h_top_idx).toNat := by
    show toNatLimbsList ((tempQ2.toList.drop m).take 1) = _
    have h_len : (tempQ2.toList.drop m).length ≥ 1 := by
      rw [List.length_drop, Array.length_toList, h_tempQ2_size]; omega
    have h_eq : (tempQ2.toList.drop m).take 1 = [(tempQ2.toList.drop m)[0]'(by omega)] := by
      apply List.ext_getElem
      · simp [List.length_take]; omega
      · intro i h1 _; have : i = 0 := by simp [List.length_take] at h1; omega
        subst this; simp [List.getElem_take]
    rw [h_eq, toNatLimbsList_cons, toNatLimbsList]
    simp [List.getElem_drop, Array.getElem_toList]
  -- (4) tempQ2_conservation_param.
  have h_addSL := addSameLengthLimbs_toNat tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1']; omega)
  simp only at h_addSL
  have h_q1_take : toNatLimbsList ((q1_arr'.toList.drop 0).take (m - k + 1))
      = toNatLimbsList q1_arr'.toList := by
    rw [List.drop_zero, List.take_of_length_le]; rw [Array.length_toList, h_q1']
  rw [h_q1_take] at h_addSL
  have h_low := addSameLengthLimbs_get_outside tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1']; omega)
  have h_low_eq : sliceVal tempQ2 0 k = sliceVal tempQ1 0 k := by
    apply sliceVal_eq_of_getElem_eq tempQ2 tempQ1 0 k
      (by rw [h_tempQ2_size]; omega) (by rw [h_tempQ1_size]; omega)
    intro j h_j
    exact h_low (0 + j) (Or.inl (by omega)) (by rw [h_tempQ1_size]; omega)
  have h_addSL_slice : sliceVal tempQ2 k (m - k + 1) + addRes.2.toNat * 2 ^ (64 * (m - k + 1))
      = sliceVal tempQ1 k (m - k + 1) + toNatLimbsList q1_arr'.toList := by
    exact h_addSL
  have h_val := tempQ1_value q0_arr' m k hk h_q0'
  have h_cons := tempQ2_conservation_param tempQ1 tempQ2 addRes.2
    (toNatLimbsList q0_arr'.toList) m k hk h_k_pos
    (toNatLimbsList q1_arr'.toList) h_tempQ1_size h_tempQ2_size
    h_val h_addSL_slice h_low_eq
  -- Combine.
  refine ⟨addRes.2.toNat, ?_, ?_⟩
  · cases addRes.2 <;> decide
  · rw [h_a9]; show sliceVal tempQ2 0 m + _ + _ = _
    rw [h_top] at h_split
    linarith [h_split, h_cons]
  /- Previous monolithic proof attempt that hit kernel timeouts.
     Resolved by extracting tempQ1_value + tempQ2_conservation_param.
  have h_tempQ_size : tempQ.size = m + 1 := Array.size_replicate
  set tempQ1 := writeSlice tempQ q0_arr' 0 0 (k + 1) 0
    (by rw [h_tempQ_size]; omega) (by rw [h_q0']; omega) with htempQ1_def
  have h_tempQ1_size : tempQ1.size = m + 1 := by
    rw [htempQ1_def, writeSlice_size, h_tempQ_size]
  set addRes := addSameLengthLimbs tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1']; omega) with hAddRes_def
  set tempQ2 := addRes.1
  have h_tempQ2_size : tempQ2.size = m + 1 := by
    show (addSameLengthLimbs _ _ _ _ _ _ _).1.size = m + 1
    rw [addSameLengthLimbs_size, h_tempQ1_size]
  have h_top_idx : m < tempQ2.size := by rw [h_tempQ2_size]; omega
  set a9 := writeSlice a8 tempQ2 (loA + n) 0 m 0
    (by omega) (by rw [h_tempQ2_size]; omega)
  -- (1) sliceVal a9 (loA + n) m = sliceVal tempQ2 0 m.
  have h_a9_eq : toNatLimbsList ((a9.toList.drop (loA + n)).take m)
      = toNatLimbsList ((tempQ2.toList.drop 0).take m) :=
    writeSlice_sliceVal a8 tempQ2 (loA + n) 0 m _ _
  -- (2) addSameLengthLimbs_toNat on tempQ1 / q1_arr' at offset k.
  have h_addSL := addSameLengthLimbs_toNat tempQ1 q1_arr' k 0 (m - k + 1)
    (by rw [h_tempQ1_size]; omega) (by rw [h_q1']; omega)
  simp only at h_addSL
  rw [← hAddRes_def] at h_addSL
  have h_q1_full : toNatLimbsList ((q1_arr'.toList.drop 0).take (m - k + 1))
      = toNatLimbsList q1_arr'.toList := by
    rw [List.drop_zero, List.take_of_length_le]
    rw [Array.length_toList, h_q1']
  rw [h_q1_full] at h_addSL
  -- (3) tempQ1's full value = q0_arr'.toNat (writeSlice_sliceVal + replicate zeros).
  have h_tempQ1_val : sliceVal tempQ1 0 (m + 1) = toNatLimbsList q0_arr'.toList := by
    have h := sliceVal_split tempQ1 0 (m + 1) (k + 1) (by omega)
      (by rw [h_tempQ1_size]; omega)
    have h_diff : (m + 1) - (k + 1) = m - k := by omega
    have h_idx : 0 + (k + 1) = k + 1 := by omega
    rw [h_diff, h_idx] at h
    have h_low : sliceVal tempQ1 0 (k + 1) = toNatLimbsList q0_arr'.toList := by
      have h_ws := writeSlice_sliceVal tempQ q0_arr' 0 0 (k + 1) _ _
      rw [← htempQ1_def] at h_ws
      show toNatLimbsList ((tempQ1.toList.drop 0).take (k + 1)) = _
      rw [h_ws, List.drop_zero, List.take_of_length_le]
      rw [Array.length_toList, h_q0']
    have h_high : sliceVal tempQ1 (k + 1) (m - k) = 0 := by
      apply (sliceVal_eq_of_getElem_eq tempQ1 tempQ (k + 1) (m - k)
        (by rw [h_tempQ1_size]; omega) (by rw [h_tempQ_size]; omega) ?_).trans
      · exact Array.replicate_sliceVal_zero (m + 1) (k + 1) (m - k)
      · intro j h_j
        exact writeSlice_get_outside tempQ q0_arr' 0 0 (k + 1) 0
          (by rw [h_tempQ_size]; omega) (by rw [h_q0']; omega)
          (k + 1 + j) (Or.inr (by omega)) (by rw [h_tempQ_size]; omega)
    rw [h_low, h_high] at h; linarith
  -- (4) Decompose tempQ2 at k and m.
  have h_tempQ2_at_k : sliceVal tempQ2 0 (m + 1)
      = sliceVal tempQ2 0 k + sliceVal tempQ2 k (m - k + 1) * 2 ^ (64 * k) := by
    have h := sliceVal_split tempQ2 0 (m + 1) k (by omega)
      (by rw [h_tempQ2_size]; omega)
    have h_diff : (m + 1) - k = m - k + 1 := by omega
    have h_idx : 0 + k = k := by omega
    rw [h_diff, h_idx] at h; exact h
  have h_tempQ2_at_m : sliceVal tempQ2 0 (m + 1)
      = sliceVal tempQ2 0 m + sliceVal tempQ2 m 1 * 2 ^ (64 * m) := by
    have h := sliceVal_split tempQ2 0 (m + 1) m (by omega)
      (by rw [h_tempQ2_size]; omega)
    have h_diff : (m + 1) - m = 1 := by omega
    have h_idx : 0 + m = m := by omega
    rw [h_diff, h_idx] at h; exact h
  -- (5) sliceVal tempQ2 m 1 = tempQ2[m].toNat.
  have h_top_limb : sliceVal tempQ2 m 1 = (tempQ2[m]'h_top_idx).toNat := by
    show toNatLimbsList ((tempQ2.toList.drop m).take 1) = _
    have h_single : (tempQ2.toList.drop m).take 1
        = [(tempQ2.toList.drop m)[0]'(by
            rw [List.length_drop, Array.length_toList, h_tempQ2_size]; omega)] := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, Array.length_toList, h_tempQ2_size]
        omega
      · intro i h1 _
        have : i = 0 := by
          simp [List.length_take, List.length_drop, Array.length_toList,
            h_tempQ2_size] at h1; omega
        subst this; simp [List.getElem_take]
    rw [h_single]; simp [toNatLimbsList_cons, toNatLimbsList]
    rw [List.getElem_drop, Array.getElem_toList]; congr 1; omega
  -- (6) tempQ2's [0, k) = tempQ1's [0, k) (preservation).
  have h_tempQ2_low : sliceVal tempQ2 0 k = sliceVal tempQ1 0 k := by
    apply sliceVal_eq_of_getElem_eq tempQ2 tempQ1 0 k
      (by rw [h_tempQ2_size]; omega) (by rw [h_tempQ1_size]; omega)
    intro j h_j
    exact addSameLengthLimbs_get_outside tempQ1 q1_arr' k 0 (m - k + 1)
      (by rw [h_tempQ1_size]; omega) (by rw [h_q1']; omega) (0 + j)
      (Or.inl (by omega)) (by rw [h_tempQ1_size]; omega)
  -- (7) tempQ1 at offset k (used by addSL).
  have h_tempQ1_at_k : sliceVal tempQ1 0 (m + 1)
      = sliceVal tempQ1 0 k + sliceVal tempQ1 k (m - k + 1) * 2 ^ (64 * k) := by
    have h := sliceVal_split tempQ1 0 (m + 1) k (by omega)
      (by rw [h_tempQ1_size]; omega)
    have h_diff : (m + 1) - k = m - k + 1 := by omega
    have h_idx : 0 + k = k := by omega
    rw [h_diff, h_idx] at h; exact h
  -- (8) Compose: tempQ2 full value = q0_arr' + q1_arr' * β^k - carry * β^(m+1).
  have h_β_split : (2 : Nat) ^ (64 * (m + 1)) = 2 ^ (64 * (m - k + 1)) * 2 ^ (64 * k) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h_tempQ2_conservation :
      sliceVal tempQ2 0 (m + 1) + addRes.2.toNat * 2 ^ (64 * (m + 1))
      = toNatLimbsList q0_arr'.toList + toNatLimbsList q1_arr'.toList * 2 ^ (64 * k) := by
    -- From h_addSL: sliceVal tempQ2 k (m-k+1) + carry * β^(m-k+1) = sliceVal tempQ1 k (m-k+1) + q1_arr'.
    -- From h_tempQ2_at_k: sliceVal tempQ2 0 (m+1) = low + sliceVal tempQ2 k (m-k+1) * β^k.
    -- From h_tempQ2_low: low = sliceVal tempQ1 0 k.
    -- From h_tempQ1_at_k: sliceVal tempQ1 0 (m+1) = sliceVal tempQ1 0 k + sliceVal tempQ1 k (...) * β^k.
    -- Use nat_sub_mul_cancel to handle the (S - X*P) * Q + X*(P*Q) = S*Q pattern.
    have h_addSL_le : addRes.2.toNat * 2 ^ (64 * (m - k + 1))
        ≤ sliceVal tempQ1 k (m - k + 1) + toNatLimbsList q1_arr'.toList := by
      rcases h_b : addRes.2 with _ | _
      · simp
      · rw [h_b] at h_addSL; linarith
    rw [h_tempQ2_at_k, h_tempQ2_low, h_β_split]
    -- Goal: sliceVal tempQ1 0 k + sliceVal tempQ2 k (m-k+1) * β^k + carry * (β^(m-k+1) * β^k)
    --     = q0_arr'.toNat + q1_arr'.toNat * β^k.
    -- tempQ2 k (m-k+1) = tempQ1 k (m-k+1) + q1_arr' - carry * β^(m-k+1).
    have h_tempQ2_k_val : sliceVal tempQ2 k (m - k + 1)
        = sliceVal tempQ1 k (m - k + 1) + toNatLimbsList q1_arr'.toList
          - addRes.2.toNat * 2 ^ (64 * (m - k + 1)) := by omega
    rw [h_tempQ2_k_val]
    -- Apply nat_sub_mul_cancel.
    rw [nat_sub_mul_cancel
      (sliceVal tempQ1 k (m - k + 1) + toNatLimbsList q1_arr'.toList)
      addRes.2.toNat (2 ^ (64 * (m - k + 1))) (2 ^ (64 * k)) h_addSL_le]
    -- Goal: sliceVal tempQ1 0 k + (sliceVal tempQ1 k (m-k+1) + q1_arr') * β^k = q0_arr' + q1_arr' * β^k.
    have h_expand : (sliceVal tempQ1 k (m - k + 1) + toNatLimbsList q1_arr'.toList)
        * 2 ^ (64 * k)
        = sliceVal tempQ1 k (m - k + 1) * 2 ^ (64 * k)
          + toNatLimbsList q1_arr'.toList * 2 ^ (64 * k) := by ring
    rw [h_expand]
    -- LHS: sliceVal tempQ1 0 k + sliceVal tempQ1 k (m-k+1) * β^k + q1_arr' * β^k.
    -- = sliceVal tempQ1 0 (m+1) + q1_arr' * β^k.
    -- = q0_arr' + q1_arr' * β^k.
    rw [show sliceVal tempQ1 0 k + sliceVal tempQ1 k (m - k + 1) * 2 ^ (64 * k)
        = sliceVal tempQ1 0 (m + 1) from h_tempQ1_at_k.symm, h_tempQ1_val]
  -- Final: use h_tempQ2_at_m and h_top_limb to match goal.
  refine ⟨addRes.2.toNat, ?_, ?_⟩
  · cases addRes.2 <;> decide
  · rw [h_a9_eq, show toNatLimbsList ((tempQ2.toList.drop 0).take m)
      = sliceVal tempQ2 0 m from by rfl, h_top_limb]
    rw [show sliceVal tempQ2 0 m + sliceVal tempQ2 m 1 * 2 ^ (64 * m)
        = sliceVal tempQ2 0 (m + 1) from h_tempQ2_at_m.symm]
    exact h_tempQ2_conservation
  -/

set_option maxHeartbeats 1600000 in
theorem recursiveDivModLimbs.afterSecondRec_full_assembly
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_q1_arr'_size : q1_arr'.size = m - m / 2 + 1) :
    let k := m / 2
    let q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
    let a6 := zeroFill a (loA + n) (loA + n + k)
    let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
    let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [zeroFill_size]; omega) (by
        show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k _ _).size
        have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
        omega)
      (by omega) (by omega) (by omega)
    let adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
      (by have : subRes2.1.size = a.size :=
            (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _)
          rw [this]; omega)
      hB (by omega) h_n_pos (by omega)
    let q0_arr' := decrementSlice q0_arr 0 adj2.2 (Nat.zero_le _)
    let res := recursiveDivModLimbs.afterSecondRec a b q1_arr' q_top_0 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2 h_q1_arr'_size
    ∃ assembly_carry : Nat, assembly_carry ≤ 1 ∧
      sliceVal res.1 (loA + n) m
        + res.2.toNat * 2 ^ (64 * m)
        + assembly_carry * 2 ^ (64 * (m + 1))
      = toNatLimbsList q0_arr'.toList
        + toNatLimbsList q1_arr'.toList * 2 ^ (64 * k) := by
  show ∃ _, _
  -- Unfold afterSecondRec to expose its internal let bindings.
  unfold recursiveDivModLimbs.afterSecondRec; simp only
  set k := m / 2
  have h_k_pos : 0 < k := by omega
  set q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_size : q0_arr.size = k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a6 := zeroFill a (loA + n) (loA + n + k)
  have h_a6_size : a6.size = a.size := zeroFill_size _ _ _
  have h_q0_hA : 0 + (k + 1) ≤ q0_arr.size := by rw [h_q0_size]; omega
  have h_loB_k : loB + k ≤ b.size := by omega
  set q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k
  have h_subGeq_hA : loA + (n + m) ≤ a6.size := by rw [h_a6_size]; omega
  have h_subGeq_hB : 0 + (2 * k + 1) ≤ q0_b0.size := by
    show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k).size
    have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k h_q0_hA h_loB_k; omega
  set subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a7_size : subRes2.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_size
  set adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
    (by rw [h_a7_size]; omega) hB (by omega) h_n_pos (by omega)
  have h_a8_size : adj2.1.size = a.size :=
    (addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans h_a7_size
  set q0_arr'_int := decrementSlice q0_arr 0 adj2.2 (Nat.zero_le _)
  have h_q0_arr'_size : q0_arr'_int.size = k + 1 := by
    show (decrementSlice _ _ _ _).size = _; rw [decrementSlice_size]; exact h_q0_size
  -- Now apply afterSecondRec_assembly_toNat with the concrete arrays.
  exact recursiveDivModLimbs.afterSecondRec_assembly_toNat
    adj2.1 q0_arr'_int q1_arr' m k (by omega) h_k_pos (by omega)
    h_q0_arr'_size h_q1_arr'_size loA n (by rw [h_a8_size]; omega) h_n_pos

/-- Preservation invariant for `recursiveDivModLimbsAux`: positions
    outside the dividend range `[loA, loA + n + m)` are unchanged.

    Proof: strong induction on `n + m`.  Basecase delegates to
    `schoolbookDivModLimbs_getElem_outside`.  Chunking composes chunk
    + rest + `addLimb` preservations.  D&C currently sorried (mirrors
    the chunking composition but with more sub-calls). -/
theorem recursiveDivModLimbsAux_preserves_outside
    (threshold : Nat) (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) (j : Nat)
    (h_j : j < loA ∨ loA + n + m ≤ j) (h_j_size : j < a.size) :
    (recursiveDivModLimbsAux threshold a b loA loB n m
        h_n_pos hA hB hbn1).val.1[j]'(by
      rw [(recursiveDivModLimbsAux threshold a b loA loB n m
        h_n_pos hA hB hbn1).property]; exact h_j_size) = a[j] := by
  induction h_sum : n + m using Nat.strong_induction_on
    generalizing a loA loB n m j with
  | _ S ih =>
    subst h_sum
    by_cases h_unbal : n < m
    · -- Chunking branch: chunk + rest + addLimb compositions.
      have h_n_le_m : n ≤ m := Nat.le_of_lt h_unbal
      have hA_chunk : (loA + (m - n)) + n + n ≤ a.size := by omega
      -- IH on chunk call: preserves outside [loA + (m - n), loA + (m - n) + n + n).
      have h_chunk_j : j < loA + (m - n) ∨ loA + (m - n) + n + n ≤ j := by
        rcases h_j with h | h
        · left; omega
        · right; omega
      have h_chunk_ih := ih (n + n) (by omega) a (loA + (m - n)) loB n n
        h_n_pos hA_chunk hB hbn1 j h_chunk_j h_j_size rfl
      set chunk_res := recursiveDivModLimbsAux threshold a b
        (loA + (m - n)) loB n n h_n_pos hA_chunk hB hbn1
      set a_chunk := chunk_res.val.1
      have h_chunk_size : a_chunk.size = a.size := chunk_res.property
      have hA_rest : loA + n + (m - n) ≤ a_chunk.size := by
        rw [h_chunk_size]; omega
      -- IH on rest call: preserves outside [loA, loA + n + (m - n)) = [loA, loA + m).
      have h_rest_j : j < loA ∨ loA + n + (m - n) ≤ j := by
        rcases h_j with h | h
        · left; exact h
        · right; omega
      have h_rest_ih := ih (n + (m - n)) (by omega) a_chunk loA loB n (m - n)
        h_n_pos hA_rest hB hbn1 j h_rest_j
        (by rw [h_chunk_size]; exact h_j_size) rfl
      set rest_res := recursiveDivModLimbsAux threshold a_chunk b
        loA loB n (m - n) h_n_pos hA_rest hB hbn1
      set a_rest := rest_res.val.1
      have h_rest_size : a_rest.size = a.size := by
        rw [show a_rest.size = a_chunk.size from rest_res.property]
        exact h_chunk_size
      have hAdd_end : loA + m + n ≤ a_rest.size := by
        rw [h_rest_size]; omega
      -- Show the function output's value at j equals a[j].
      show (recursiveDivModLimbsAux threshold a b loA loB n m
        h_n_pos hA hB hbn1).val.1[j]'_ = a[j]
      unfold recursiveDivModLimbsAux
      simp only [h_unbal, ↓reduceDIte]
      -- Goal: (addLimb a_rest (loA + m) (loA + m + n) q_top_rest _ _).1[j] = a[j]
      -- Chain: addLimb preserves j → a_rest_ih → chunk_ih.
      have h_addLimb_eq :
          (addLimb a_rest (loA + m) (loA + m + n) (rest_res).val.2
            (by omega) hAdd_end).1[j]'(by rw [addLimb_size, h_rest_size]; exact h_j_size)
            = a_rest[j]'(by rw [h_rest_size]; exact h_j_size) := by
        rcases h_j with h | h
        · exact addLimb_get_below a_rest (loA + m) (loA + m + n) (rest_res).val.2
            (by omega) hAdd_end j (by omega) (by rw [h_rest_size]; exact h_j_size)
        · exact addLimb_get_above a_rest (loA + m) (loA + m + n) (rest_res).val.2
            (by omega) hAdd_end j (by omega) (by rw [h_rest_size]; exact h_j_size)
      exact h_addLimb_eq.trans (h_rest_ih.trans h_chunk_ih)
    · by_cases h_small : m < max threshold 2
      · -- Basecase: schoolbook.
        show (recursiveDivModLimbsAux threshold a b loA loB n m
          h_n_pos hA hB hbn1).val.1[j]'_ = a[j]
        unfold recursiveDivModLimbsAux
        simp only [h_unbal, ↓reduceDIte, h_small]
        exact schoolbookDivModLimbs_getElem_outside a b loA loB n m
          h_n_pos hA hB hbn1 j h_j h_j_size
      · -- D&C body: composes 2 recursive calls + afterFirstRec + afterSecondRec.
        have h_m_le_n : m ≤ n := by omega
        have h_m_ge_2 : 2 ≤ m := by
          have := le_max_right threshold 2; omega
        have h_k_pos : 0 < m / 2 := by omega
        have h_2k_le_n : 2 * (m / 2) ≤ n := by omega
        have h_k_lt_n : m / 2 < n := by omega
        have h_n_minus_k_pos : 0 < n - m / 2 := by omega
        have hA_top : (loA + 2 * (m / 2)) + (n - m / 2) + (m - m / 2) ≤ a.size := by
          omega
        have hB_top : (loB + m / 2) + (n - m / 2) ≤ b.size := by omega
        have hbn1_top :
            2 ^ 63 ≤ (b[(loB + m / 2) + (n - m / 2) - 1]'(by omega)).toNat := by
          have h_eq : b[(loB + m / 2) + (n - m / 2) - 1]'(by omega)
              = b[loB + n - 1]'(by omega) := by congr 1; omega
          rw [h_eq]; exact hbn1
        -- IH for first recursive call.
        have h_j_first : j < loA + 2 * (m / 2)
            ∨ loA + 2 * (m / 2) + (n - m / 2) + (m - m / 2) ≤ j := by
          rcases h_j with h | h
          · left; omega
          · right; omega
        have h_first_ih := ih ((n - m / 2) + (m - m / 2)) (by omega) a
          (loA + 2 * (m / 2)) (loB + m / 2) (n - m / 2) (m - m / 2)
          h_n_minus_k_pos hA_top hB_top hbn1_top j h_j_first h_j_size rfl
        set first_res := recursiveDivModLimbsAux threshold a b
          (loA + 2 * (m / 2)) (loB + m / 2) (n - m / 2) (m - m / 2)
          h_n_minus_k_pos hA_top hB_top hbn1_top
        set a1 := first_res.val.1
        have h_a1_size : a1.size = a.size := first_res.property
        -- afterFirstRec preserves outside [loA, loA + n + m).
        set after1_res := recursiveDivModLimbs.afterFirstRec a1 b first_res.val.2
          loA loB n m h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n h_m_ge_2
        set a4 := after1_res.1
        have h_a4_size : a4.size = a.size :=
          (recursiveDivModLimbs.afterFirstRec_size a1 b first_res.val.2
            loA loB n m h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n h_m_ge_2).trans
            h_a1_size
        have h_after1_eq : a4[j]'(by rw [h_a4_size]; exact h_j_size) = a[j] := by
          have h_step : a4[j]'(by rw [h_a4_size]; exact h_j_size)
              = a1[j]'(by rw [h_a1_size]; exact h_j_size) :=
            recursiveDivModLimbs.afterFirstRec_get_outside a1 b first_res.val.2
              loA loB n m h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n
              h_m_ge_2 j h_j (by rw [h_a1_size]; exact h_j_size)
          exact h_step.trans h_first_ih
        have hA_mid : (loA + m / 2) + (n - m / 2) + (m / 2) ≤ a4.size := by
          rw [h_a4_size]; omega
        -- IH for second recursive call.
        have h_j_second : j < loA + m / 2
            ∨ loA + m / 2 + (n - m / 2) + (m / 2) ≤ j := by
          rcases h_j with h | h
          · left; omega
          · right; omega
        have h_second_ih := ih ((n - m / 2) + (m / 2)) (by omega) a4
          (loA + m / 2) (loB + m / 2) (n - m / 2) (m / 2)
          h_n_minus_k_pos hA_mid hB_top hbn1_top j h_j_second
          (by rw [h_a4_size]; exact h_j_size) rfl
        set second_res := recursiveDivModLimbsAux threshold a4 b
          (loA + m / 2) (loB + m / 2) (n - m / 2) (m / 2)
          h_n_minus_k_pos hA_mid hB_top hbn1_top
        set a5 := second_res.val.1
        have h_a5_size : a5.size = a.size :=
          second_res.property.trans h_a4_size
        have h_q1_size : after1_res.2.1.size = m - m / 2 + 1 :=
          recursiveDivModLimbs.afterFirstRec_q1size a1 b first_res.val.2
            loA loB n m h_n_pos (by rw [h_a1_size]; exact hA) hB h_m_le_n h_m_ge_2
        -- afterSecondRec preserves outside [loA, loA + n + m).
        have h_final_eq :
            (recursiveDivModLimbs.afterSecondRec a5 b after1_res.2.1
              second_res.val.2 loA loB n m h_n_pos
              (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2
              h_q1_size).1[j]'(by
                rw [recursiveDivModLimbs.afterSecondRec_size, h_a5_size]
                exact h_j_size) = a[j] := by
          have h_step :
              (recursiveDivModLimbs.afterSecondRec a5 b after1_res.2.1
                second_res.val.2 loA loB n m h_n_pos
                (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2
                h_q1_size).1[j]'(by
                  rw [recursiveDivModLimbs.afterSecondRec_size, h_a5_size]
                  exact h_j_size)
              = a5[j]'(by rw [h_a5_size]; exact h_j_size) :=
            recursiveDivModLimbs.afterSecondRec_get_outside a5 b after1_res.2.1
              second_res.val.2 loA loB n m h_n_pos
              (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size j h_j
              (by rw [h_a5_size]; exact h_j_size)
          exact h_step.trans (h_second_ih.trans h_after1_eq)
        -- Show the function output equals res_final at j.
        show (recursiveDivModLimbsAux threshold a b loA loB n m
          h_n_pos hA hB hbn1).val.1[j]'_ = a[j]
        unfold recursiveDivModLimbsAux
        simp only [h_unbal, ↓reduceDIte, h_small]
        exact h_final_eq

/-- Slice corollary of `recursiveDivModLimbsAux_preserves_outside`:
    a slice disjoint from `[loA, loA + n + m)` has unchanged `sliceVal`. -/
theorem recursiveDivModLimbsAux_sliceVal_outside
    (threshold : Nat) (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat)
    (lo len : Nat) (h_size : lo + len ≤ a.size)
    (h_disjoint : lo + len ≤ loA ∨ loA + n + m ≤ lo) :
    sliceVal (recursiveDivModLimbsAux threshold a b loA loB n m
        h_n_pos hA hB hbn1).val.1 lo len = sliceVal a lo len := by
  apply sliceVal_eq_of_getElem_eq
    (h_bound1 := by
      rw [(recursiveDivModLimbsAux threshold a b loA loB n m
        h_n_pos hA hB hbn1).property]; exact h_size)
    (h_bound2 := h_size)
  intro k h_k
  exact recursiveDivModLimbsAux_preserves_outside threshold a b loA loB n m
    h_n_pos hA hB hbn1 (lo + k) (by rcases h_disjoint with h | h <;> omega)
    (by omega)

/-- Divisor lower bound: a normalized n-limb slice has value ≥ 2^(64n - 1).
    Mirrors the `private` `schoolbookDivModLimbs.divisor_bound`. -/
theorem sliceVal_divisor_bound (b : Array UInt64) (loB n : Nat)
    (h_n_pos : 0 < n) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    2 ^ (64 * n - 1) ≤ sliceVal b loB n := by
  show 2 ^ (64 * n - 1) ≤ toNatLimbsList ((b.toList.drop loB).take n)
  have h_split := toNatLimbsList_drop_take_split b loB n (n - 1) (by omega) hB
  have h_sub : n - (n - 1) = 1 := by omega
  rw [h_sub] at h_split
  have h_loB_eq : loB + (n - 1) = loB + n - 1 := by omega
  rw [h_loB_eq] at h_split
  rw [h_split]
  have h_idx : loB + n - 1 < b.size := by omega
  have h_top_eq : toNatLimbsList ((b.toList.drop (loB + n - 1)).take 1)
                    = (b[loB + n - 1]'h_idx).toNat := by
    have h := toNatLimbsList_drop_take_succ b (loB + n - 1) 0 h_idx
    simpa [toNatLimbsList] using h
  rw [h_top_eq]
  have h_pow_eq : (2 : Nat) ^ (64 * n - 1) = 2 ^ 63 * 2 ^ (64 * (n - 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h_pow_eq]
  calc 2 ^ 63 * 2 ^ (64 * (n - 1))
      ≤ (b[loB + n - 1]'h_idx).toNat * 2 ^ (64 * (n - 1)) :=
        Nat.mul_le_mul_right _ hbn1
    _ ≤ _ := Nat.le_add_left _ _

set_option maxHeartbeats 400000 in
/-- The adjust count (delta1) from `afterFirstRec` is at most the quotient Q₁.
    Proof: unfold `afterFirstRec`, case-split on the borrow flag.
    - borrow=false: addbackLoop returns delta=0, trivially ≤ Q₁.
    - borrow=true: prove ec=1 by contradiction (ec=0 + borrow=true leads to
      fuel exhaustion violating limb bounds), then `addbackLoop_combined`'s
      h_lt gives result < B, and `adjust_spec_limbs` derives delta ≤ Q₁. -/
theorem recursiveDivModLimbs.afterFirstRec_delta_le_Q
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat)
    (h_Q_B0_le : toNatLimbsList ((a.extract (loA + n + m / 2) (loA + n + m)).push
        q_top_1).toList * toNatLimbsList ((b.toList.drop loB).take (m / 2))
      ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n)) :
    let res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2
    let k := m / 2
    res.2.2 ≤ toNatLimbsList ((a.extract (loA + n + k) (loA + n + m)).push q_top_1).toList := by
  -- Get the clean conservation from afterFirstRec_spec.
  have h_clean := recursiveDivModLimbs.afterFirstRec_spec a b q_top_1 loA loB n m
    h_n_pos hA hB h_m_le_n h_m_ge_2 h_Q_B0_le
  -- Unfold to access the internal addbackLoop and case-split on borrow.
  show _ ≤ _
  unfold recursiveDivModLimbs.afterFirstRec; simp only
  set k := m / 2
  set q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
  have h_q1_size : q1_arr.size = m - k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  set a2 := zeroFill a (loA + n + k) (loA + n + m)
  have h_a2_size : a2.size = a.size := zeroFill_size _ _ _
  have h_q1_hA : 0 + (m - k + 1) ≤ q1_arr.size := by rw [h_q1_size]; omega
  have h_loB_k : loB + k ≤ b.size := by have := h_m_le_n; omega
  set q1_b0 := mulLimbs q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k
  have h_q1_b0_size : m + 1 ≤ q1_b0.size := by
    show m + 1 ≤ (mulLimbs q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k).size
    have := mulLimbs_size_ge q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k; omega
  have h_subGeq_hA : loA + k + (n + m - k) ≤ a2.size := by rw [h_a2_size]; omega
  have h_subGeq_hB : 0 + (m + 1) ≤ q1_b0.size := by omega
  set subRes := subGeqLimbs a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
    h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
  have h_a3_size : subRes.1.size = a.size :=
    (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a2_size
  have h_ab_hA : loA + k + (n + m - k) ≤ subRes.1.size := by rw [h_a3_size]; omega
  have h_ab_n_le : n ≤ n + m - k := by omega
  have h_ab_high : 0 < n + m - k := by omega
  -- Case split on borrow.
  cases h_bor : subRes.2
  · -- borrow = false: addbackLoop returns (subRes.1, 0). delta = 0.
    show (addbackLoop subRes.1 b loA loB n k (n + m - k) false 5
      h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2
      ≤ toNatLimbsList q1_arr.toList
    cases h_fuel : (5 : Nat) <;> simp [addbackLoop]
  · -- borrow = true: get addbackLoop_combined, then adjust_spec_limbs.
    obtain ⟨ec, h_ec_le, h_addback, h_lt, h_delta_fuel⟩ :=
      addbackLoop_combined subRes.1 b loA loB n k (n + m - k) 5
        h_ab_hA hB h_ab_n_le h_n_pos h_ab_high
        true (fun _ => by omega)
    -- Reproduce the subGeqLimbs conservation.
    have h_subGeq := subGeqLimbs_toNat a2 q1_b0 (loA + k) (n + m - k) 0 (m + 1)
      h_subGeq_hA h_subGeq_hB (by omega) (by omega) (by omega)
    simp only at h_subGeq
    have h_a2_eq : toNatLimbsList ((a2.toList.drop (loA + k)).take (n + m - k))
        = toNatLimbsList ((a.toList.drop (loA + k)).take n) := by
      have h_split : sliceVal a2 (loA + k) (n + m - k)
          = sliceVal a2 (loA + k) n
            + sliceVal a2 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
        have h := sliceVal_split a2 (loA + k) (n + m - k) n (by omega)
          (by rw [h_a2_size]; omega)
        have h_idx : loA + k + n = loA + n + k := by ring
        have h_diff : (n + m - k) - n = m - k := by omega
        rw [h_idx, h_diff] at h; exact h
      have h_low_eq : sliceVal a2 (loA + k) n = sliceVal a (loA + k) n := by
        apply sliceVal_eq_of_getElem_eq a2 a (loA + k) n
          (by rw [h_a2_size]; omega) (by omega)
        intro j h_j
        exact zeroFill_get_outside a (loA + n + k) (loA + n + m) (loA + k + j)
          (Or.inl (by omega)) (by omega)
      have h_high_zero : sliceVal a2 (loA + n + k) (m - k) = 0 := by
        show toNatLimbsList ((a2.toList.drop (loA + n + k)).take (m - k)) = 0
        have := zeroFill_sliceVal_zero a (loA + n + k) (m - k) (by omega)
        have h_eq : loA + n + k + (m - k) = loA + n + m := by omega
        rw [h_eq] at this; exact this
      show sliceVal a2 (loA + k) (n + m - k) = sliceVal a (loA + k) n
      rw [h_split, h_low_eq, h_high_zero]; ring
    have h_q1_b0_slice : toNatLimbsList ((q1_b0.toList.drop 0).take (m + 1))
        = toNatLimbsList q1_arr.toList
          * toNatLimbsList ((b.toList.drop loB).take k) := by
      simp only [List.drop_zero]
      have h_q1_b0_total : toNatLimbsList q1_b0.toList
          = toNatLimbsList q1_arr.toList
            * toNatLimbsList ((b.toList.drop loB).take k) := by
        have h := mulLimbs_toNat q1_arr b 0 (m - k + 1) loB k h_q1_hA h_loB_k
        simp only [List.drop_zero] at h
        have h_q1_take : (q1_arr.toList).take (m - k + 1) = q1_arr.toList := by
          rw [List.take_of_length_le]; rw [Array.length_toList]; omega
        rw [h_q1_take] at h; exact h
      have h_B_bound : toNatLimbsList q1_arr.toList
            * toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * (m + 1)) := by
        have h_q1 : toNatLimbsList q1_arr.toList < 2 ^ (64 * (m - k + 1)) := by
          have h := toNatLimbsList_lt_pow q1_arr.toList
          have h_len : q1_arr.toList.length = m - k + 1 := by
            rw [Array.length_toList]; exact h_q1_size
          rw [h_len] at h; exact h
        have h_b : toNatLimbsList ((b.toList.drop loB).take k) < 2 ^ (64 * k) := by
          have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
          have h_len : ((b.toList.drop loB).take k).length = k := by
            rw [List.length_take, List.length_drop, Array.length_toList]; omega
          rw [h_len] at h; exact h
        calc toNatLimbsList q1_arr.toList * toNatLimbsList ((b.toList.drop loB).take k)
            < 2 ^ (64 * (m - k + 1)) * 2 ^ (64 * k) :=
              Nat.mul_lt_mul_of_lt_of_le h_q1 (Nat.le_of_lt h_b) (Nat.two_pow_pos _)
          _ = 2 ^ (64 * (m + 1)) := by rw [← Nat.pow_add]; congr 1; omega
      have h_lt2 : toNatLimbsList q1_b0.toList < 2 ^ (64 * (m + 1)) := by
        rw [h_q1_b0_total]; exact h_B_bound
      have h_split : q1_b0.toList
          = q1_b0.toList.take (m + 1) ++ q1_b0.toList.drop (m + 1) :=
        (List.take_append_drop (m + 1) q1_b0.toList).symm
      have h_decomp : toNatLimbsList q1_b0.toList
          = toNatLimbsList (q1_b0.toList.drop (m + 1)) * 2 ^ (64 * (m + 1))
            + toNatLimbsList (q1_b0.toList.take (m + 1)) := by
        conv_lhs => rw [h_split]
        rw [toNatLimbsList_append]
        have h_take_len : (q1_b0.toList.take (m + 1)).length = m + 1 := by
          rw [List.length_take, Array.length_toList]; omega
        rw [h_take_len]
      have h_high_zero : toNatLimbsList (q1_b0.toList.drop (m + 1)) = 0 := by
        by_contra h_ne
        have h_ge1 : 1 ≤ toNatLimbsList (q1_b0.toList.drop (m + 1)) :=
          Nat.one_le_iff_ne_zero.mpr h_ne
        have h_lower : 2 ^ (64 * (m + 1))
            ≤ toNatLimbsList (q1_b0.toList.drop (m + 1)) * 2 ^ (64 * (m + 1)) :=
          Nat.le_mul_of_pos_left _ (by omega)
        linarith
      rw [← h_q1_b0_total]; rw [h_decomp, h_high_zero]; ring
    rw [h_a2_eq] at h_subGeq; rw [h_q1_b0_slice] at h_subGeq
    have h_bor_nat : subRes.2.toNat = 1 := by rw [h_bor]; rfl
    -- ec = 1: by contradiction (ec=0 + borrow=true → fuel exhaustion violates bounds).
    have h_ec1 : ec = 1 := by
      by_contra h_ne
      have h_ec0 : ec = 0 := by omega
      have h_delta5 := h_delta_fuel h_ec0 rfl
      have h_result_lt := toNatLimbsList_lt_pow
        ((addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k) |>.take (n + m - k))
      have h_res_size : (addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.size = subRes.1.size :=
        addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _
      have h_take_len : ((addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k) |>.take (n + m - k)).length
          = n + m - k := by
        simp [List.length_take, List.length_drop, h_res_size, h_a3_size]; omega
      rw [h_take_len] at h_result_lt
      simp only [h_ec0, Nat.zero_mul, Nat.add_zero] at h_addback
      have h_U := toNatLimbsList_lt_pow ((a.toList.drop (loA + k)).take n)
      have h_B := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
      simp [List.length_take, List.length_drop] at h_U h_B
      have h_n_take : min n (a.size - (loA + k)) = n := by omega
      have h_n_take2 : min n (b.size - loB) = n := by omega
      rw [h_n_take] at h_U; rw [h_n_take2] at h_B
      rw [show subRes.2.toNat = 1 from h_bor_nat] at h_subGeq
      simp only [Nat.one_mul] at h_subGeq
      rw [h_delta5] at h_addback
      have h_pow_eq : 2 ^ (64 * n) * 2 ^ (64 * (m - k)) = 2 ^ (64 * (n + m - k)) := by
        rw [← Nat.pow_add]; congr 1; omega
      have h64mk : (2 : Nat) ^ (64 * (m - k)) ≥ 2 ^ 64 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h64_ge7 : (2 : Nat) ^ 64 ≥ 7 := by norm_num
      nlinarith
    -- h_lt gives result < B when ec = 1.
    have h_result_lt := h_lt h_ec1
    -- Clean conservation: cancel borrow=1, ec=1 from subGeq + addback.
    have h_clean_eq : toNatLimbsList ((a.toList.drop (loA + k)).take n)
        + (addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
            h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2
          * toNatLimbsList ((b.toList.drop loB).take n)
      = toNatLimbsList (((addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
            h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k)).take (n + m - k))
        + toNatLimbsList q1_arr.toList
          * toNatLimbsList ((b.toList.drop loB).take k) := by
      rw [show subRes.2.toNat = 1 from h_bor_nat] at h_subGeq
      simp only [Nat.one_mul] at h_subGeq
      have h_addback' := h_addback
      rw [h_ec1] at h_addback'; simp only [Nat.one_mul] at h_addback'
      linarith
    -- B₀ ≤ B and 0 < B.
    have h_B_decomp := sliceVal_split b loB n k (by omega) hB
    have h_B0_le_B : sliceVal b loB k ≤ sliceVal b loB n := by
      linarith [Nat.zero_le (sliceVal b (loB + k) (n - k) * 2 ^ (64 * k))]
    have h_B_pos : 0 < sliceVal b loB n := by
      have h := sliceVal_divisor_bound b loB n h_n_pos hB hbn1; linarith
    exact adjust_spec_limbs
      (toNatLimbsList ((a.toList.drop (loA + k)).take n))
      (addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
          h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).2
      (toNatLimbsList ((b.toList.drop loB).take n))
      (toNatLimbsList (((addbackLoop subRes.1 b loA loB n k (n + m - k) true 5
            h_ab_hA hB h_ab_n_le h_n_pos h_ab_high).1.toList.drop (loA + k)).take (n + m - k)))
      (toNatLimbsList q1_arr.toList)
      (toNatLimbsList ((b.toList.drop loB).take k))
      h_clean_eq h_B0_le_B h_B_pos h_result_lt

/-- The Q₁ array returned by `afterFirstRec` equals
    `decrementSlice q1_arr 0 delta1`, where `q1_arr` is the
    original quotient array and `delta1 = (afterFirstRec ...).2.2`.
    This is a definitional unfolding of `afterFirstRec`. -/
theorem recursiveDivModLimbs.afterFirstRec_q1_is_decrementSlice
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    let res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2
    let k := m / 2
    let q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
    res.2.1 = decrementSlice q1_arr 0 res.2.2 (Nat.zero_le _) := by
  show _ = _
  unfold recursiveDivModLimbs.afterFirstRec; simp only

set_option maxHeartbeats 800000 in
theorem recursiveDivModLimbs.afterFirstRec_q1_toNat
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (h_d_lt : (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).2.2 < 2 ^ 64)
    (h_d_le : (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).2.2
      ≤ toNatLimbsList ((a.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList) :
    let res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2
    let k := m / 2
    let q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
    toNatLimbsList res.2.1.toList
      = toNatLimbsList q1_arr.toList - res.2.2 := by
  show _ = _
  set res := recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
    h_n_pos hA hB h_m_le_n h_m_ge_2
  set k := m / 2
  set q1_arr := ((a.extract (loA + n + k) (loA + n + m)).push q_top_1)
  have h_q1_eq : res.2.1 = decrementSlice q1_arr 0 res.2.2 (Nat.zero_le _) :=
    recursiveDivModLimbs.afterFirstRec_q1_is_decrementSlice a b q_top_1
      loA loB n m h_n_pos hA hB h_m_le_n h_m_ge_2
  rw [h_q1_eq]
  have h_q1_size : q1_arr.size = m - k + 1 := by
    show ((a.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  have h_q1_pos : 0 < q1_arr.size := by rw [h_q1_size]; omega
  -- decrementSlice preserves size.
  have h_dec_size : (decrementSlice q1_arr 0 res.2.2 (Nat.zero_le _)).size = q1_arr.size :=
    decrementSlice_size _ _ _ _
  -- Rewrite toNatLimbsList x.toList as toNatLimbsList (x.toList.drop 0).take (x.size - 0)
  have h_dec_full : toNatLimbsList (decrementSlice q1_arr 0 res.2.2 (Nat.zero_le _)).toList
      = toNatLimbsList (((decrementSlice q1_arr 0 res.2.2 (Nat.zero_le _)).toList.drop 0).take
          (q1_arr.size - 0)) := by
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le]
    rw [Array.length_toList, h_dec_size]
  have h_orig_full : toNatLimbsList q1_arr.toList
      = toNatLimbsList ((q1_arr.toList.drop 0).take (q1_arr.size - 0)) := by
    rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le]
    rw [Array.length_toList]
  rw [h_dec_full, h_orig_full]
  exact decrementSlice_val_eq q1_arr res.2.2 h_q1_pos h_d_lt (by rw [← h_orig_full]; exact h_d_le)

theorem recursiveDivModLimbs.afterFirstRec_delta_le_fuel
    (a b : Array UInt64) (q_top_1 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m) :
    (recursiveDivModLimbs.afterFirstRec a b q_top_1 loA loB n m
      h_n_pos hA hB h_m_le_n h_m_ge_2).2.2 ≤ 5 := by
  show _ ≤ _
  unfold recursiveDivModLimbs.afterFirstRec; simp only
  exact addbackLoop_delta_le _ _ _ _ _ _ _ _ 5 _ _ _ _ _

theorem recursiveDivModLimbs.afterSecondRec_delta_le_fuel
    (a b q1_arr' : Array UInt64) (q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (_ : q1_arr'.size = m - m / 2 + 1) :
    let k := m / 2
    let q0_arr := ((a.extract (loA + n) (loA + n + k)).push q_top_0)
    let a6 := zeroFill a (loA + n) (loA + n + k)
    let q0_b0 := mulLimbs q0_arr b 0 (k + 1) loB k
      (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
    let subRes2 := subGeqLimbs a6 q0_b0 loA (n + m) 0 (2 * k + 1)
      (by rw [zeroFill_size]; omega) (by
        show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr b 0 (k + 1) loB k _ _).size
        have := mulLimbs_size_ge q0_arr b 0 (k + 1) loB k
          (by rw [Array.size_push, Array.size_extract]; omega) (by omega)
        omega)
      (by omega) (by omega) (by omega)
    let adj2 := addbackLoop subRes2.1 b loA loB n 0 (n + m) subRes2.2 5
      (by have : subRes2.1.size = a.size :=
            (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans (zeroFill_size _ _ _)
          rw [this]; omega)
      hB (by omega) h_n_pos (by omega)
    adj2.2 ≤ 5 := by
  show _ ≤ _
  exact addbackLoop_delta_le _ _ _ _ _ _ _ _ 5 _ _ _ _ _

/-- Any `q_top` satisfying the spec is ≤ 1.  Derives from `div_eq` +
    `rem_lt` + divisor normalization (`2^63 ≤` the top divisor limb). -/
theorem q_top_le_one_of_spec (a b : Array UInt64) (loA loB n m : Nat)
    (a' : Array UInt64) (q_top : UInt64)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat)
    (h_spec : RecursiveDivModLimbsSpec a b loA loB n m a' q_top) :
    q_top.toNat ≤ 1 := by
  by_contra h
  push Not at h
  have h_q : 2 ≤ q_top.toNat := h
  have h_V := sliceVal_divisor_bound b loB n h_n_pos hB hbn1
  have h_A_lt : sliceVal a loA (n + m) < 2 ^ (64 * (n + m)) := by
    show toNatLimbsList ((a.toList.drop loA).take (n + m)) < 2 ^ (64 * (n + m))
    have h := toNatLimbsList_lt_pow ((a.toList.drop loA).take (n + m))
    have h_len : ((a.toList.drop loA).take (n + m)).length = n + m := by
      simp [List.length_take, List.length_drop, Array.length_toList]; omega
    rw [h_len] at h; exact h
  have h_div := h_spec.div_eq
  have h_A_ge : q_top.toNat * 2 ^ (64 * m) * sliceVal b loB n
      ≤ sliceVal a loA (n + m) := by
    rw [h_div]
    have h1 : q_top.toNat * 2 ^ (64 * m)
        ≤ q_top.toNat * 2 ^ (64 * m) + sliceVal a' (loA + n) m :=
      Nat.le_add_right _ _
    have h2 : q_top.toNat * 2 ^ (64 * m) * sliceVal b loB n
        ≤ (q_top.toNat * 2 ^ (64 * m) + sliceVal a' (loA + n) m) * sliceVal b loB n :=
      Nat.mul_le_mul_right _ h1
    linarith
  have h_pow_split : 2 ^ (64 * (n + m))
      = 2 * (2 ^ (64 * m) * 2 ^ (64 * n - 1)) := by
    have h_e : 64 * (n + m) = 1 + 64 * m + (64 * n - 1) := by omega
    rw [h_e, pow_add, pow_add]; ring
  have h_mul_lower : q_top.toNat * 2 ^ (64 * m) * 2 ^ (64 * n - 1)
      ≤ q_top.toNat * 2 ^ (64 * m) * sliceVal b loB n :=
    Nat.mul_le_mul_left _ h_V
  have h_chain : q_top.toNat * 2 ^ (64 * m) * 2 ^ (64 * n - 1)
      < 2 ^ (64 * (n + m)) :=
    lt_of_le_of_lt (Nat.le_trans h_mul_lower h_A_ge) h_A_lt
  rw [h_pow_split] at h_chain
  have h_assoc : q_top.toNat * 2 ^ (64 * m) * 2 ^ (64 * n - 1)
      = q_top.toNat * (2 ^ (64 * m) * 2 ^ (64 * n - 1)) := by ring
  rw [h_assoc] at h_chain
  have h_2X : 2 * (2 ^ (64 * m) * 2 ^ (64 * n - 1))
      ≤ q_top.toNat * (2 ^ (64 * m) * 2 ^ (64 * n - 1)) :=
    Nat.mul_le_mul_right _ h_q
  omega

/-! ### Algebraic helpers (Nat-only, for the chunking case) -/

/-- The algebraic identity behind the chunking case.  Given:
      - `A = A_top · β_mn + A_bot` (dividend decomposition).
      - Chunk spec: `A_top = Q_chunk · V + R_chunk` with `R_chunk < V`,
        where `Q_chunk = q_chunk_top · β_n + Q_chunk_low`.
      - Rest spec: `R_chunk · β_mn + A_bot = Q_rest · V + R_rest`
        with `R_rest < V`, where `Q_rest = q_rest_top · β_mn + Q_rest_low`.
      - `β_m = β_mn · β_n`.
    Derive: `A = ((q_chunk_top + carry) · β_m + Q_rest_low +
                  (Q_chunk_low_after_add) · β_mn) · V + R_rest`,
    where `(Q_chunk_low + q_rest_top) = Q_chunk_low_after_add + carry · β_n`
    captures the `addLimb` step's carry.

    This is the pure-Nat skeleton of the chunking proof. -/
theorem chunking_algebra
    (A A_top A_bot V β_m β_mn β_n
     q_chunk_top Q_chunk_low R_chunk
     q_rest_top Q_rest_low R_rest
     Q_chunk_low_after_add carry : Nat)
    (h_A : A = A_top * β_mn + A_bot)
    (h_chunk_div : A_top = (q_chunk_top * β_n + Q_chunk_low) * V + R_chunk)
    (h_rest_div : R_chunk * β_mn + A_bot
                    = (q_rest_top * β_mn + Q_rest_low) * V + R_rest)
    (h_β_m : β_m = β_mn * β_n)
    (h_addlimb : Q_chunk_low + q_rest_top
                   = Q_chunk_low_after_add + carry * β_n) :
    A = ((q_chunk_top + carry) * β_m + Q_rest_low
          + Q_chunk_low_after_add * β_mn) * V + R_rest := by
  calc A = A_top * β_mn + A_bot := h_A
    _ = ((q_chunk_top * β_n + Q_chunk_low) * V + R_chunk) * β_mn + A_bot := by
        rw [h_chunk_div]
    _ = (q_chunk_top * β_n + Q_chunk_low) * V * β_mn
          + (R_chunk * β_mn + A_bot) := by ring
    _ = (q_chunk_top * β_n + Q_chunk_low) * V * β_mn
          + ((q_rest_top * β_mn + Q_rest_low) * V + R_rest) := by rw [h_rest_div]
    _ = ((q_chunk_top * β_n + Q_chunk_low) * β_mn
          + (q_rest_top * β_mn + Q_rest_low)) * V + R_rest := by ring
    _ = (q_chunk_top * (β_n * β_mn) + (Q_chunk_low + q_rest_top) * β_mn
          + Q_rest_low) * V + R_rest := by ring
    _ = (q_chunk_top * β_m + (Q_chunk_low + q_rest_top) * β_mn
          + Q_rest_low) * V + R_rest := by
        rw [show β_n * β_mn = β_m from by rw [h_β_m]; ring]
    _ = (q_chunk_top * β_m + (Q_chunk_low_after_add + carry * β_n) * β_mn
          + Q_rest_low) * V + R_rest := by rw [h_addlimb]
    _ = ((q_chunk_top + carry) * β_m + Q_rest_low
          + Q_chunk_low_after_add * β_mn) * V + R_rest := by
        rw [h_β_m]; ring

/-! ### Basecase: schoolbook reduction -/

/-- Basecase: when `recursiveDivModLimbsAux` delegates to
    `schoolbookDivModLimbs`, the spec follows from
    `schoolbookDivModLimbs_toNat`. -/
theorem recursiveDivModLimbsAux_spec_basecase
    (threshold : Nat) (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat)
    (h_basecase : ¬ n < m ∧ m < max threshold 2) :
    let res := recursiveDivModLimbsAux threshold a b loA loB n m
      h_n_pos hA hB hbn1
    RecursiveDivModLimbsSpec a b loA loB n m res.1.1 res.1.2 := by
  -- Unfold the function — basecase dispatches to schoolbookDivModLimbs.
  have h_unbal : ¬ n < m := h_basecase.1
  have h_small : m < max threshold 2 := h_basecase.2
  show RecursiveDivModLimbsSpec a b loA loB n m _ _
  obtain ⟨h_lt, h_eq, _⟩ :=
    schoolbookDivModLimbs_toNat a b loA loB n m h_n_pos hA hB hbn1
  -- The function's result when basecase fires is exactly
  -- `schoolbookDivModLimbs`'s.  Convert via unfold.
  refine ⟨?_, ?_⟩
  · -- rem_lt
    show sliceVal _ _ _ < sliceVal _ _ _
    unfold sliceVal
    unfold recursiveDivModLimbsAux
    simp only [h_unbal, ↓reduceDIte, h_small]
    exact h_lt
  · -- div_eq
    show sliceVal _ _ _ = _
    unfold sliceVal
    unfold recursiveDivModLimbsAux
    simp only [h_unbal, ↓reduceDIte, h_small]
    exact h_eq

private theorem quotient_assembly_eq_aux
    (Q' res_q_val res_slice carry A R B : Nat)
    (β_m β_m1 : Nat)
    (h_asm : res_slice + res_q_val * β_m + carry * β_m1 = Q')
    (h_carry_le : carry ≤ 1)
    (h_dc : A = Q' * B + R)
    (h_A_lt : A < β_m1 * B)
    (_ : 0 < B) :
    Q' = res_q_val * β_m + res_slice := by
  -- From h_dc: Q' * B ≤ A < β_m1 * B. So Q' < β_m1.
  have h_Q'_lt : Q' < β_m1 := by
    have h_QB : Q' * B ≤ A := by linarith [Nat.zero_le R]
    exact Nat.lt_of_mul_lt_mul_right (by linarith : Q' * B < β_m1 * B)
  -- carry = 0: if carry ≥ 1, then Q' ≥ carry * β_m1 ≥ β_m1 > Q'. Contradiction.
  have h_carry_zero : carry = 0 := by
    by_contra h
    have : carry ≥ 1 := by omega
    have : carry * β_m1 ≥ β_m1 := Nat.le_mul_of_pos_left _ (by omega)
    linarith [Nat.zero_le res_slice, Nat.zero_le (res_q_val * β_m)]
  rw [h_carry_zero, Nat.zero_mul, Nat.add_zero] at h_asm
  linarith

-- The old s9_quotient_assembly with Array parameters caused heartbeat timeouts
-- due to expensive whnf on afterSecondRec terms. This version is fully abstract.
private theorem s9_quotient_assembly
    (Q1 Q0 : Nat) (delta1 delta0 : Nat) (β_k : Nat)
    (res_Q res_S : Nat) (carry : Nat)
    (q0_dec q1_dec : Nat)
    (A R B β_m β_m1 : Nat)
    (h_carry_le : carry ≤ 1)
    (_ : delta1 ≤ Q1) (_ : delta0 ≤ Q0)
    (h_q1_dec : q1_dec = Q1 - delta1) (h_q0_dec : q0_dec = Q0 - delta0)
    (h_asm : res_S + res_Q * β_m + carry * β_m1 = q0_dec + q1_dec * β_k)
    (h_dc : A = ((Q1 - delta1) * β_k + (Q0 - delta0)) * B + R)
    (h_A_lt : A < β_m1 * B) (_ : 0 < B) :
    (Q1 - delta1) * β_k + (Q0 - delta0) = res_Q * β_m + res_S := by
  set Q' := (Q1 - delta1) * β_k + (Q0 - delta0)
  have h_rhs_eq : q0_dec + q1_dec * β_k = Q' := by rw [h_q0_dec, h_q1_dec]; ring
  have h_QB : Q' * B ≤ A := by linarith [Nat.zero_le R]
  have h_Q'_lt : Q' < β_m1 := Nat.lt_of_mul_lt_mul_right (by linarith : Q' * B < β_m1 * B)
  have h_carry_zero : carry = 0 := by
    by_contra h_ne
    have : carry * β_m1 ≥ β_m1 := Nat.le_mul_of_pos_left _ (by omega)
    linarith [Nat.zero_le (res_S + res_Q * β_m), h_rhs_eq]
  rw [h_carry_zero, Nat.zero_mul, Nat.add_zero] at h_asm
  linarith [h_rhs_eq]

/-  DELETED: s9_quotient_assembly_bridge and s9_quotient_assembly_concrete
    (both caused heartbeat timeouts due to afterSecondRec terms in parameters).
    The proof is now done inline at the call site using the abstract
    s9_quotient_assembly theorem.

private theorem s9_quotient_assembly_bridge
    (a_orig a5 b a1 q1_arr' : Array UInt64)
    (q_top_1 q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a_orig.size) (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat)
    (hA_after1 : loA + n + m ≤ a1.size) (h_a5_size : a5.size = a_orig.size)
    (h_q1_size : q1_arr'.size = m - m / 2 + 1)
    (delta1 delta0 : Nat)
    (h_delta1_le : delta1 ≤ toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList)
    (h_d0_le : delta0 ≤ toNatLimbsList ((a5.extract (loA + n) (loA + n + m / 2)).push q_top_0).toList)
    (h_delta0_le_fuel : delta0 ≤ 5)
    (h_dc : sliceVal a_orig loA (n + m) =
      ((toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList - delta1) *
            2 ^ (64 * (m / 2)) +
          (toNatLimbsList ((a5.extract (loA + n) (loA + n + m / 2)).push q_top_0).toList - delta0)) *
        sliceVal b loB n +
      sliceVal (recursiveDivModLimbs.afterSecondRec a5 b q1_arr' q_top_0 loA loB n m
          h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size).1
        loA n)
    (h_after1_eq : q1_arr' = (recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
        h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.1)
    (h_delta1_eq : delta1 = (recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
        h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.2) :
    let k := m / 2
    let res_final := recursiveDivModLimbs.afterSecondRec a5 b q1_arr' q_top_0 loA loB n m
      h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
    (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
        - delta1) * 2 ^ (64 * k)
    + (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push q_top_0).toList
        - delta0)
    = res_final.2.toNat * 2 ^ (64 * m) + sliceVal res_final.1 (loA + n) m := by
  show _ = _
  set k := m / 2
  set res_final := recursiveDivModLimbs.afterSecondRec a5 b q1_arr' q_top_0 loA loB n m
    h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
  obtain ⟨carry, h_carry_le, h_asm⟩ :=
    recursiveDivModLimbs.afterSecondRec_full_assembly
      a5 b q1_arr' q_top_0 loA loB n m
      h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
  have h_delta1_lt : delta1 < 2 ^ 64 := by
    rw [h_delta1_eq]; linarith [recursiveDivModLimbs.afterFirstRec_delta_le_fuel
      a1 b q_top_1 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2]
  have h_delta1_le' : (recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
      h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.2
      ≤ toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList := by
    rw [← h_delta1_eq]; exact h_delta1_le
  have h_d_lt_afr : (recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
      h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.2 < 2 ^ 64 := by
    have := recursiveDivModLimbs.afterFirstRec_delta_le_fuel
      a1 b q_top_1 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
    omega
  have h_q1_val := recursiveDivModLimbs.afterFirstRec_q1_toNat
    a1 b q_top_1 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
    h_d_lt_afr h_delta1_le'
  set q0_loc := ((a5.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_sz : q0_loc.size = k + 1 := by
    show ((a5.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  have h_q0_dec_val : toNatLimbsList
      (decrementSlice q0_loc 0 delta0 (Nat.zero_le _)).toList
      = toNatLimbsList q0_loc.toList - delta0 := by
    have hds := decrementSlice_size q0_loc 0 delta0 (Nat.zero_le _)
    have h1 : (decrementSlice q0_loc 0 delta0 _).toList
        = ((decrementSlice q0_loc 0 delta0 _).toList.drop 0).take (q0_loc.size - 0) := by
      simp only [List.drop_zero, Nat.sub_zero]
      rw [List.take_of_length_le (by rw [Array.length_toList, hds])]
    have h2 : q0_loc.toList = (q0_loc.toList.drop 0).take (q0_loc.size - 0) := by
      simp only [List.drop_zero, Nat.sub_zero]
      rw [List.take_of_length_le (by rw [Array.length_toList])]
    rw [h1, h2]; exact decrementSlice_val_eq q0_loc delta0 (by omega) (by omega) (by rw [← h2]; exact h_d0_le)
  have h_A_lt : sliceVal a_orig loA (n + m) < 2 ^ (64 * (n + m)) := by
    have h := toNatLimbsList_lt_pow ((a_orig.toList.drop loA).take (n + m))
    rw [show ((a_orig.toList.drop loA).take (n + m)).length = n + m from by
      rw [List.length_take, List.length_drop, Array.length_toList]; omega] at h; exact h
  have h_B_ge := sliceVal_divisor_bound b loB n h_n_pos hB hbn1
  exact s9_quotient_assembly
    (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList)
    (toNatLimbsList q0_loc.toList) delta1 delta0 (2 ^ (64 * k))
    res_final.2.toNat (sliceVal res_final.1 (loA + n) m) carry
    (toNatLimbsList (decrementSlice q0_loc 0 delta0 (Nat.zero_le _)).toList)
    (toNatLimbsList q1_arr'.toList)
    (sliceVal a_orig loA (n + m)) (sliceVal res_final.1 loA n) (sliceVal b loB n)
    (2 ^ (64 * m)) (2 ^ (64 * (m + 1)))
    h_carry_le h_delta1_le h_d0_le h_q1_val h_q0_dec_val h_asm h_dc
    (by calc sliceVal a_orig loA (n + m) < 2 ^ (64 * (n + m)) := h_A_lt
          _ = 2 ^ (64 * (m + 1)) * 2 ^ (64 * n - 1) := by rw [← Nat.pow_add]; congr 1; omega
          _ ≤ 2 ^ (64 * (m + 1)) * sliceVal b loB n := Nat.mul_le_mul_left _ h_B_ge)
    (by linarith)

-- The concrete proof is done entirely at the call site using s9_quotient_assembly
-- plus afterSecondRec_full_assembly, afterFirstRec_q1_toNat, and decrementSlice_val_eq.
-- The old concrete wrapper is deleted to avoid heartbeat issues.
-- KEEP: the old proof body is deleted. The section below is a dead comment.
/-
private theorem s9_quotient_assembly_concrete_DELETED
    (a_orig a5 b a1 : Array UInt64) (q1_arr' : Array UInt64)
    (q_top_1 q_top_0 : UInt64)
    (loA loB n m : Nat)
    (h_n_pos : 0 < n)
    (hA : loA + n + m ≤ a_orig.size)
    (hB : loB + n ≤ b.size)
    (h_m_le_n : m ≤ n) (h_m_ge_2 : 2 ≤ m)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat)
    (hA_after1 : loA + n + m ≤ a1.size)
    (h_a5_size : a5.size = a_orig.size)
    (h_q1_size : q1_arr'.size = m - m / 2 + 1)
    (delta1 delta0 : Nat)
    (h_delta1_le : delta1
      ≤ toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList)
    (h_d0_le : delta0
      ≤ toNatLimbsList ((a5.extract (loA + n) (loA + n + m / 2)).push q_top_0).toList)
    (h_delta0_le_fuel : delta0 ≤ 5)
    (h_A_lt : sliceVal a_orig loA (n + m) < 2 ^ (64 * (n + m)))
    (h_after1_eq : q1_arr' = (recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
        h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.1)
    (h_delta1_eq : delta1 = (recursiveDivModLimbs.afterFirstRec a1 b q_top_1 loA loB n m
        h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.2)
    (res_R : Nat)
    (h_dc : sliceVal a_orig loA (n + m)
      = ((toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList
            - delta1) * 2 ^ (64 * (m / 2))
          + (toNatLimbsList ((a5.extract (loA + n) (loA + n + m / 2)).push q_top_0).toList
              - delta0))
        * sliceVal b loB n + res_R)
    (res_Q res_S : Nat)
    (h_asm_eq : ∃ carry ≤ 1,
      res_S + res_Q * 2 ^ (64 * m) + carry * 2 ^ (64 * (m + 1))
      = toNatLimbsList (decrementSlice
          ((a5.extract (loA + n) (loA + n + m / 2)).push q_top_0) 0
          delta0 (Nat.zero_le _)).toList
        + toNatLimbsList q1_arr'.toList * 2 ^ (64 * (m / 2)))
    (h_dc : sliceVal a_orig loA (n + m)
      = ((toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push q_top_1).toList
            - delta1) * 2 ^ (64 * (m / 2))
          + (toNatLimbsList ((a5.extract (loA + n) (loA + n + m / 2)).push q_top_0).toList
              - delta0))
        * sliceVal b loB n + res_R) :
    let k := m / 2
    (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
        - delta1) * 2 ^ (64 * k)
    + (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push q_top_0).toList
        - delta0)
    = res_Q * 2 ^ (64 * m) + res_S := by
  show _ = _
  set k := m / 2
  -- Step 1: Assembly equation from parameter.
  obtain ⟨carry, h_carry_le, h_asm⟩ := h_asm_eq
  -- Step 2: delta bounds from fuel.
  have h_delta1_lt : delta1 < 2 ^ 64 := by
    rw [h_delta1_eq]; linarith [recursiveDivModLimbs.afterFirstRec_delta_le_fuel
      a1 b q_top_1 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2]
  have h_delta0_le_5 : delta0 ≤ 5 := h_delta0_le_fuel
  -- Step 3: q1 value = Q₁ - delta1.
  have h_q1_val : toNatLimbsList q1_arr'.toList
      = toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
        - delta1 := by
    rw [h_after1_eq, h_delta1_eq]
    have h_fuel := recursiveDivModLimbs.afterFirstRec_delta_le_fuel
      a1 b q_top_1 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
    exact recursiveDivModLimbs.afterFirstRec_q1_toNat
      a1 b q_top_1 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
      (by omega) (by rw [← h_delta1_eq]; exact h_delta1_le)
  -- Step 4: q0 decremented value = Q₀ - delta0.
  set q0_arr_loc := ((a5.extract (loA + n) (loA + n + k)).push q_top_0)
  have h_q0_size : q0_arr_loc.size = k + 1 := by
    show ((a5.extract _ _).push _).size = _; rw [Array.size_push, Array.size_extract]; omega
  have h_q0_val : toNatLimbsList
      (decrementSlice q0_arr_loc 0 delta0 (Nat.zero_le _)).toList
      = toNatLimbsList q0_arr_loc.toList - delta0 := by
    have hds := decrementSlice_size q0_arr_loc 0 delta0 (Nat.zero_le _)
    -- Rewrite both sides to use drop 0 / take (size - 0) form.
    have h_dec_eq : toNatLimbsList (decrementSlice q0_arr_loc 0 delta0 (Nat.zero_le _)).toList
        = toNatLimbsList (((decrementSlice q0_arr_loc 0 delta0 (Nat.zero_le _)).toList.drop 0).take
            (q0_arr_loc.size - 0)) := by
      simp only [List.drop_zero, Nat.sub_zero]
      rw [List.take_of_length_le (by rw [Array.length_toList, hds])]
    have h_orig_eq : toNatLimbsList q0_arr_loc.toList
        = toNatLimbsList ((q0_arr_loc.toList.drop 0).take (q0_arr_loc.size - 0)) := by
      simp only [List.drop_zero, Nat.sub_zero]
      rw [List.take_of_length_le (by rw [Array.length_toList])]
    rw [h_dec_eq, h_orig_eq]
    exact decrementSlice_val_eq q0_arr_loc delta0
      (by rw [h_q0_size]; omega) (by omega) (by rw [← h_orig_eq]; exact h_d0_le)
  -- Step 5: carry = 0 and combine.
  -- Q' = (Q₁ - delta1) * β_k + (Q₀ - delta0)
  -- From h_asm: res_slice + res_q * β_m + carry * β_{m+1} = q0'_val + q1'_val * β_k
  -- And q0'_val + q1'_val * β_k = (Q₀ - delta0) + (Q₁ - delta1) * β_k = Q'.
  -- From h_dc: Q' * B + R = A. So Q' ≤ A / B < β_{m+1}.
  -- Therefore carry = 0 and the equation follows.
  have h_B_ge := sliceVal_divisor_bound b loB n h_n_pos hB hbn1
  -- Rewrite h_asm using h_q0_val and h_q1_val.
  have h_rhs_val : toNatLimbsList (decrementSlice q0_arr_loc 0 delta0 (Nat.zero_le _)).toList
      + toNatLimbsList q1_arr'.toList * 2 ^ (64 * k)
      = (toNatLimbsList q0_arr_loc.toList - delta0)
        + (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
            - delta1) * 2 ^ (64 * k) := by
    rw [h_q0_val, h_q1_val]
  -- Q' definition matches:
  have h_Q'_def : (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
        - delta1) * 2 ^ (64 * k)
      + (toNatLimbsList q0_arr_loc.toList - delta0)
      = (toNatLimbsList q0_arr_loc.toList - delta0)
        + (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
            - delta1) * 2 ^ (64 * k) := by ring
  -- Q' * B ≤ A
  set Q' := (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push q_top_1).toList
      - delta1) * 2 ^ (64 * k)
    + (toNatLimbsList q0_arr_loc.toList - delta0)
  have h_QB : Q' * sliceVal b loB n ≤ sliceVal a_orig loA (n + m) := by
    linarith [Nat.zero_le res_R]
  -- Q' * 2^(64*n-1) ≤ A < 2^(64*(n+m)) = 2^(64*(m+1)) * 2^(64*n-1)
  have h_pow_eq : (2 : Nat) ^ (64 * (n + m)) = 2 ^ (64 * (m + 1)) * 2 ^ (64 * n - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h_Q'_lt : Q' < 2 ^ (64 * (m + 1)) := by
    by_contra h_neg
    push_neg at h_neg
    have : Q' * 2 ^ (64 * n - 1) ≥ 2 ^ (64 * (m + 1)) * 2 ^ (64 * n - 1) :=
      Nat.mul_le_mul_right _ h_neg
    have : Q' * sliceVal b loB n ≥ Q' * 2 ^ (64 * n - 1) :=
      Nat.mul_le_mul_left _ h_B_ge
    linarith [h_pow_eq]
  -- carry = 0:
  have h_carry_zero : carry = 0 := by
    by_contra h_ne
    have h_c1 : carry ≥ 1 := by omega
    have h_rhs_ge : carry * 2 ^ (64 * (m + 1)) ≥ 2 ^ (64 * (m + 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    -- h_asm says res_slice + res_q * β_m + carry * β_{m+1} = RHS.
    -- RHS = q0'_val + q1'_val * β_k = Q' (by h_rhs_val + h_Q'_def).
    -- LHS ≥ carry * β_{m+1} ≥ β_{m+1} > Q' = RHS. Contradiction.
    linarith [h_rhs_val, h_Q'_def, Nat.zero_le (res_S + res_Q * 2 ^ (64 * m))]
  rw [h_carry_zero, Nat.zero_mul, Nat.add_zero] at h_asm
  linarith [h_rhs_val, h_Q'_def]
-/
-/

/-! ### Full theorem (chunking + D&C body deferred) -/

set_option maxHeartbeats 1600000 in
/-- Main spec.  Currently proven via strong induction on `n + m`, with
    the basecase fully proved and the chunking + D&C branches deferred
    to future iterations (their structure mirrors the AzNat-level proof
    in `Equiv/DivRecursive.lean`). -/
theorem recursiveDivModLimbsAux_spec
    (threshold : Nat) (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    let res := recursiveDivModLimbsAux threshold a b loA loB n m
      h_n_pos hA hB hbn1
    RecursiveDivModLimbsSpec a b loA loB n m res.1.1 res.1.2 := by
  -- Strong induction on n + m to handle the recursive calls.
  induction h_sum : n + m using Nat.strong_induction_on
    generalizing a loA loB n m with
  | _ S ih =>
    subst h_sum
    by_cases h_unbal : n < m
    · -- Chunking branch.
      have h_n_le_m : n ≤ m := Nat.le_of_lt h_unbal
      have hA_chunk : (loA + (m - n)) + n + n ≤ a.size := by omega
      -- IH for chunk call (sum = 2n < n + m).
      have h_chunk_spec :
          RecursiveDivModLimbsSpec a b (loA + (m - n)) loB n n
            (recursiveDivModLimbsAux threshold a b
              (loA + (m - n)) loB n n h_n_pos hA_chunk hB hbn1).1.1
            (recursiveDivModLimbsAux threshold a b
              (loA + (m - n)) loB n n h_n_pos hA_chunk hB hbn1).1.2 :=
        ih (n + n) (by omega) a (loA + (m - n)) loB n n
          h_n_pos hA_chunk hB hbn1 rfl
      -- Extract chunk's outputs.
      set chunk_res := recursiveDivModLimbsAux threshold a b
        (loA + (m - n)) loB n n h_n_pos hA_chunk hB hbn1 with h_chunk_def
      set a_chunk := chunk_res.1.1 with h_a_chunk_def
      set q_top_chunk := chunk_res.1.2 with h_q_top_chunk_def
      have h_chunk_size : a_chunk.size = a.size := chunk_res.2
      have hA_rest : loA + n + (m - n) ≤ a_chunk.size := by
        rw [h_chunk_size]; omega
      -- IH for rest call (sum = n + (m - n) = m < n + m for m ≥ 1).
      have h_rest_spec :
          RecursiveDivModLimbsSpec a_chunk b loA loB n (m - n)
            (recursiveDivModLimbsAux threshold a_chunk b
              loA loB n (m - n) h_n_pos hA_rest hB hbn1).1.1
            (recursiveDivModLimbsAux threshold a_chunk b
              loA loB n (m - n) h_n_pos hA_rest hB hbn1).1.2 :=
        ih (n + (m - n)) (by omega) a_chunk loA loB n (m - n)
          h_n_pos hA_rest hB hbn1 rfl
      set rest_res := recursiveDivModLimbsAux threshold a_chunk b
        loA loB n (m - n) h_n_pos hA_rest hB hbn1 with h_rest_def
      set a_rest := rest_res.1.1 with h_a_rest_def
      set q_top_rest := rest_res.1.2 with h_q_top_rest_def
      have h_rest_size : a_rest.size = a.size := by
        rw [show a_rest.size = a_chunk.size from rest_res.2]; exact h_chunk_size
      -- Final addLimb.
      have hAdd_end : loA + m + n ≤ a_rest.size := by
        rw [h_rest_size]; omega
      set addRes := addLimb a_rest (loA + m) (loA + m + n) q_top_rest
        (by omega) hAdd_end with h_add_def
      set a_final := addRes.1 with h_a_final_def
      set carryOut : UInt64 := if addRes.2 then 1 else 0 with h_carryOut_def
      refine ⟨?_, ?_⟩
      · -- rem_lt: sliceVal a_final loA n < sliceVal b loB n.
        -- Expose the function's output.
        show sliceVal _ loA n < sliceVal b loB n
        unfold recursiveDivModLimbsAux
        simp only [h_unbal, ↓reduceDIte]
        show sliceVal a_final loA n < sliceVal b loB n
        -- a_final = addLimb result; addLimb leaves [loA, loA + n) unchanged
        -- since loA + n ≤ loA + m (chunking branch has n ≤ m).
        have h_a_final_size : a_final.size = a.size := by
          show (addLimb a_rest (loA + m) (loA + m + n) q_top_rest _ _).1.size = a.size
          rw [addLimb_size, h_rest_size]
        have h_slice_eq : sliceVal a_final loA n = sliceVal a_rest loA n := by
          apply sliceVal_eq_of_getElem_eq a_final a_rest loA n
            (by rw [h_a_final_size]; omega) (by rw [h_rest_size]; omega)
          intro k h_k
          show (addLimb a_rest (loA + m) (loA + m + n) q_top_rest _ _).1[loA + k]
            = a_rest[loA + k]
          exact addLimb_get_below a_rest (loA + m) (loA + m + n) q_top_rest
            (by omega) hAdd_end (loA + k) (by omega) (by rw [h_rest_size]; omega)
        rw [h_slice_eq]
        exact h_rest_spec.rem_lt
      · -- div_eq: A = Q * V + R for the chunking branch.
        show sliceVal a loA (n + m) = _
        unfold recursiveDivModLimbsAux
        simp only [h_unbal, ↓reduceDIte]
        show sliceVal a loA (n + m)
            = ((q_top_chunk + carryOut).toNat * 2 ^ (64 * m)
                + sliceVal a_final (loA + n) m) * sliceVal b loB n
                + sliceVal a_final loA n
        -- Build the five hypotheses for `chunking_algebra`.
        -- (1) A = A_top * β_mn + A_bot via sliceVal_split.
        have h_A : sliceVal a loA (n + m)
            = sliceVal a (loA + (m - n)) (n + n) * 2 ^ (64 * (m - n))
              + sliceVal a loA (m - n) := by
          rw [sliceVal_split a loA (n + m) (m - n) (by omega) (by omega)]
          have h_eq : n + m - (m - n) = n + n := by omega
          rw [h_eq, Nat.add_comm]
        -- (2) Chunk's div_eq.
        have h_chunk_div := h_chunk_spec.div_eq
        -- Massage (loA + (m - n) + n) into (loA + m) form.
        have h_idx_eq : loA + (m - n) + n = loA + m := by omega
        rw [h_idx_eq] at h_chunk_div
        -- (3) Rest's div_eq, rewritten as needed.
        have h_rest_div := h_rest_spec.div_eq
        have h_n_plus : n + (m - n) = m := by omega
        rw [h_n_plus] at h_rest_div
        -- Decompose sliceVal a_chunk loA m via sliceVal_split.
        have h_a_chunk_size_bd : loA + m ≤ a_chunk.size := by
          rw [h_chunk_size]; omega
        have h_chunk_loA_m : sliceVal a_chunk loA m
            = sliceVal a_chunk loA (m - n)
              + sliceVal a_chunk (loA + (m - n)) n * 2 ^ (64 * (m - n)) := by
          have h := sliceVal_split a_chunk loA m (m - n) (by omega) h_a_chunk_size_bd
          have h_eq : m - (m - n) = n := by omega
          rw [h_eq] at h; exact h
        -- Chunk preserves a's [loA, loA + m - n) (chunk operates on
        -- [loA + (m - n), loA + n + m)).
        have h_chunk_prefix : sliceVal a_chunk loA (m - n) = sliceVal a loA (m - n) :=
          recursiveDivModLimbsAux_sliceVal_outside threshold a b
            (loA + (m - n)) loB n n h_n_pos hA_chunk hB hbn1 loA (m - n)
            (by omega) (Or.inl (by omega))
        -- Combine to get the chunking_algebra h_rest_div form:
        --   R_chunk * β_mn + A_bot = (q_rest_top * β_mn + Q_rest_low) * V + R_rest.
        have h_rest_div_alg :
            sliceVal a_chunk (loA + (m - n)) n * 2 ^ (64 * (m - n))
              + sliceVal a loA (m - n)
            = (q_top_rest.toNat * 2 ^ (64 * (m - n))
                + sliceVal a_rest (loA + n) (m - n)) * sliceVal b loB n
              + sliceVal a_rest loA n := by
          rw [← h_chunk_prefix]
          have h_eq : sliceVal a_chunk loA m
              = sliceVal a_chunk (loA + (m - n)) n * 2 ^ (64 * (m - n))
                + sliceVal a_chunk loA (m - n) := by
            rw [h_chunk_loA_m]; ring
          linarith [h_eq, h_rest_div]
        -- (4) β_m = β_mn * β_n.
        have h_β_m : (2 : Nat) ^ (64 * m) = 2 ^ (64 * (m - n)) * 2 ^ (64 * n) := by
          rw [← pow_add]; congr 1; omega
        -- (5) addLimb_toNat application.
        have h_addlimb_raw := addLimb_toNat a_rest (loA + m) (loA + m + n)
          q_top_rest (by omega) hAdd_end (by omega)
        -- Simplify hi - lo = n.
        have h_diff : loA + m + n - (loA + m) = n := by omega
        simp only [h_diff] at h_addlimb_raw
        -- a_final = addRes.1.
        have h_addRes_eq : addRes = addLimb a_rest (loA + m) (loA + m + n)
            q_top_rest (by omega) hAdd_end := h_add_def
        -- Rest preserves a_chunk's [loA + m, ...).
        have h_rest_suffix : sliceVal a_rest (loA + m) n
            = sliceVal a_chunk (loA + m) n :=
          recursiveDivModLimbsAux_sliceVal_outside threshold a_chunk b
            loA loB n (m - n) h_n_pos hA_rest hB hbn1 (loA + m) n
            (by rw [h_chunk_size]; omega) (Or.inr (by omega))
        -- Bool-to-UInt64 carry identity: carryOut.toNat = addRes.2.toNat
        -- when carryOut := if addRes.2 then 1 else 0.
        have h_carryOut_toNat : carryOut.toNat = addRes.2.toNat := by
          rw [h_carryOut_def]
          rcases h_b : addRes.2 with _ | _ <;> simp
        -- The addLimb identity in sliceVal form.
        have h_addlimb : sliceVal a_chunk (loA + m) n + q_top_rest.toNat
            = sliceVal a_final (loA + m) n + carryOut.toNat * 2 ^ (64 * n) := by
          rw [← h_rest_suffix, h_carryOut_toNat]
          show toNatLimbsList ((a_rest.toList.drop (loA + m)).take n) + q_top_rest.toNat
              = toNatLimbsList ((a_final.toList.drop (loA + m)).take n)
                + addRes.2.toNat * 2 ^ (64 * n)
          have h_a_final_addRes : a_final = addRes.1 := h_a_final_def
          rw [h_a_final_addRes, h_addRes_eq]
          linarith [h_addlimb_raw]
        -- Apply chunking_algebra.
        have h_algebra := chunking_algebra
          (sliceVal a loA (n + m))
          (sliceVal a (loA + (m - n)) (n + n))
          (sliceVal a loA (m - n))
          (sliceVal b loB n)
          (2 ^ (64 * m))
          (2 ^ (64 * (m - n)))
          (2 ^ (64 * n))
          q_top_chunk.toNat
          (sliceVal a_chunk (loA + m) n)
          (sliceVal a_chunk (loA + (m - n)) n)
          q_top_rest.toNat
          (sliceVal a_rest (loA + n) (m - n))
          (sliceVal a_rest loA n)
          (sliceVal a_final (loA + m) n)
          carryOut.toNat
          h_A h_chunk_div h_rest_div_alg h_β_m h_addlimb
        -- (a) a_final's low-n slice equals a_rest's (addLimb preservation).
        have h_a_final_size : a_final.size = a.size := by
          show (addLimb a_rest (loA + m) (loA + m + n) q_top_rest _ _).1.size = a.size
          rw [addLimb_size, h_rest_size]
        have h_final_low : sliceVal a_final loA n = sliceVal a_rest loA n := by
          apply sliceVal_eq_of_getElem_eq a_final a_rest loA n
            (by rw [h_a_final_size]; omega) (by rw [h_rest_size]; omega)
          intro k h_k
          show (addLimb a_rest (loA + m) (loA + m + n) q_top_rest _ _).1[loA + k]
              = a_rest[loA + k]
          exact addLimb_get_below a_rest (loA + m) (loA + m + n) q_top_rest
            (by omega) hAdd_end (loA + k) (by omega) (by rw [h_rest_size]; omega)
        -- (b) a_final's mid slice [loA + n, loA + m) equals a_rest's
        -- (addLimb at [loA + m, …) doesn't touch this range either).
        have h_final_mid : sliceVal a_final (loA + n) (m - n)
            = sliceVal a_rest (loA + n) (m - n) := by
          apply sliceVal_eq_of_getElem_eq a_final a_rest (loA + n) (m - n)
            (by rw [h_a_final_size]; omega) (by rw [h_rest_size]; omega)
          intro k h_k
          show (addLimb a_rest (loA + m) (loA + m + n) q_top_rest _ _).1[loA + n + k]
              = a_rest[loA + n + k]
          exact addLimb_get_below a_rest (loA + m) (loA + m + n) q_top_rest
            (by omega) hAdd_end (loA + n + k) (by omega) (by rw [h_rest_size]; omega)
        -- (c) Decompose sliceVal a_final (loA + n) m.
        have h_final_split : sliceVal a_final (loA + n) m
            = sliceVal a_final (loA + n) (m - n)
              + sliceVal a_final (loA + m) n * 2 ^ (64 * (m - n)) := by
          have h := sliceVal_split a_final (loA + n) m (m - n) (by omega)
            (by rw [h_a_final_size]; omega)
          have h_eq : m - (m - n) = n := by omega
          have h_idx : loA + n + (m - n) = loA + m := by omega
          rw [h_eq, h_idx] at h; exact h
        -- (d) UInt64 carry sum without overflow:
        --     q_top_chunk ≤ 1 (by q_top_le_one_of_spec on chunk_spec),
        --     carryOut ≤ 1 (by definition), so sum ≤ 2 < 2^64.
        have h_q_top_chunk_bound : q_top_chunk.toNat ≤ 1 :=
          q_top_le_one_of_spec a b (loA + (m - n)) loB n n a_chunk q_top_chunk
            h_n_pos hA_chunk hB hbn1 h_chunk_spec
        have h_carryOut_bound : carryOut.toNat ≤ 1 := by
          rw [h_carryOut_def]
          rcases addRes.2 with _ | _ <;> simp
        have h_sum_lt : q_top_chunk.toNat + carryOut.toNat < 2 ^ 64 := by
          have h_le : q_top_chunk.toNat + carryOut.toNat ≤ 2 := by omega
          have : (2 : Nat) < 2 ^ 64 := by decide
          omega
        have h_q_sum : (q_top_chunk + carryOut).toNat
            = q_top_chunk.toNat + carryOut.toNat := by
          rw [_root_.UInt64.toNat_add, Nat.mod_eq_of_lt h_sum_lt]
        -- Combine all pieces into the final equality.
        rw [h_algebra, h_q_sum, h_final_split, h_final_mid, h_final_low]
        ring
    · by_cases h_small : m < max threshold 2
      · exact recursiveDivModLimbsAux_spec_basecase threshold a b loA loB n m
          h_n_pos hA hB hbn1 ⟨h_unbal, h_small⟩
      · -- D&C body: parallels MCA Algorithm 1.8.
        --
        -- The slice-level body composes:
        --   1. First recursive call on top (n - k)/(m - k) sub-problem
        --      at (loA + 2k, loB + k).  Gives (Q₁, R₁) with Q₁ = q_top_1
        --      placed at high limb + Q₁_low in a[loA + n + k, loA + n + m).
        --   2. `afterFirstRec`: zeros Q₁ region, subtracts Q₁ · B₀ from
        --      [loA + k, loA + n + m), addbacks to adjust.
        --   3. Second recursive call on middle (n - k)/k sub-problem
        --      at (loA + k, loB + k).  Gives (Q₀, R₀).
        --   4. `afterSecondRec`: parallel adjustment for Q₀ stage, then
        --      assembles Q = Q₁' · β^k + Q₀' into a[loA + n, loA + n + m).
        --
        -- The proof mirrors `balanced_correct` in `Equiv/DivRecursive.lean`,
        -- applying the two IH calls, then chaining:
        --   - `afterFirstRec_toNat` + `afterSecondRec_subAddback_toNat`
        --     (conservation lemmas for the adjust stages)
        --   - `afterSecondRec_assembly_toNat` (Q-assembly conservation)
        --   - `dc_full_bookkeeping` (algebraic chaining into the final spec)
        --   - `s9_quotient_assembly` + `afterSecondRec_full_assembly` (Q value)
        have h_m_le_n : m ≤ n := by omega
        have h_m_ge_2 : 2 ≤ m := by
          have := le_max_right threshold 2; omega
        have h_k_pos : 0 < m / 2 := by omega
        have h_2k_le_n : 2 * (m / 2) ≤ n := by omega
        have h_n_minus_k_pos : 0 < n - m / 2 := by omega
        have hA_top : (loA + 2 * (m / 2)) + (n - m / 2) + (m - m / 2) ≤ a.size := by
          omega
        have hB_top : (loB + m / 2) + (n - m / 2) ≤ b.size := by omega
        have hbn1_top :
            2 ^ 63 ≤ (b[(loB + m / 2) + (n - m / 2) - 1]'(by omega)).toNat := by
          have h_eq : b[(loB + m / 2) + (n - m / 2) - 1]'(by omega)
              = b[loB + n - 1]'(by omega) := by congr 1; omega
          rw [h_eq]; exact hbn1
        -- IH 1: First recursive call's spec (top sub-problem).
        have h_first_spec :
            RecursiveDivModLimbsSpec a b (loA + 2 * (m / 2)) (loB + m / 2)
              (n - m / 2) (m - m / 2)
              (recursiveDivModLimbsAux threshold a b (loA + 2 * (m / 2))
                (loB + m / 2) (n - m / 2) (m - m / 2)
                h_n_minus_k_pos hA_top hB_top hbn1_top).val.1
              (recursiveDivModLimbsAux threshold a b (loA + 2 * (m / 2))
                (loB + m / 2) (n - m / 2) (m - m / 2)
                h_n_minus_k_pos hA_top hB_top hbn1_top).val.2 :=
          ih ((n - m / 2) + (m - m / 2)) (by omega) a (loA + 2 * (m / 2))
            (loB + m / 2) (n - m / 2) (m - m / 2)
            h_n_minus_k_pos hA_top hB_top hbn1_top rfl
        set first_res := recursiveDivModLimbsAux threshold a b
          (loA + 2 * (m / 2)) (loB + m / 2) (n - m / 2) (m - m / 2)
          h_n_minus_k_pos hA_top hB_top hbn1_top
        set a1 := first_res.val.1
        have h_a1_size : a1.size = a.size := first_res.property
        have hA_after1 : loA + n + m ≤ a1.size := by rw [h_a1_size]; exact hA
        -- afterFirstRec output.
        set after1_res := recursiveDivModLimbs.afterFirstRec a1 b first_res.val.2
          loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
        set a4 := after1_res.1
        have h_a4_size : a4.size = a.size :=
          (recursiveDivModLimbs.afterFirstRec_size a1 b first_res.val.2
            loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).trans h_a1_size
        have hA_mid : (loA + m / 2) + (n - m / 2) + (m / 2) ≤ a4.size := by
          rw [h_a4_size]; omega
        -- IH 2: Second recursive call's spec (middle sub-problem on a4).
        have h_second_spec :
            RecursiveDivModLimbsSpec a4 b (loA + m / 2) (loB + m / 2)
              (n - m / 2) (m / 2)
              (recursiveDivModLimbsAux threshold a4 b (loA + m / 2)
                (loB + m / 2) (n - m / 2) (m / 2)
                h_n_minus_k_pos hA_mid hB_top hbn1_top).val.1
              (recursiveDivModLimbsAux threshold a4 b (loA + m / 2)
                (loB + m / 2) (n - m / 2) (m / 2)
                h_n_minus_k_pos hA_mid hB_top hbn1_top).val.2 :=
          ih ((n - m / 2) + (m / 2)) (by omega) a4 (loA + m / 2)
            (loB + m / 2) (n - m / 2) (m / 2)
            h_n_minus_k_pos hA_mid hB_top hbn1_top rfl
        -- Bind k BEFORE set commands to avoid elaboration conflicts.
        set k := m / 2 with hk_def
        -- Bind the second recursive call and afterSecondRec.
        set second_res := recursiveDivModLimbsAux threshold a4 b
          (loA + k) (loB + k) (n - k) k
          h_n_minus_k_pos hA_mid hB_top hbn1_top
        set a5 := second_res.val.1
        have h_a5_size : a5.size = a.size := second_res.property.trans h_a4_size
        have h_q1_size : after1_res.2.1.size = m - k + 1 :=
          recursiveDivModLimbs.afterFirstRec_q1size a1 b first_res.val.2
            loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
        set res_final := recursiveDivModLimbs.afterSecondRec a5 b
          after1_res.2.1 second_res.val.2 loA loB n m
          h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
        -- ── Stage 1 conservation (via afterFirstRec_spec) ──────────
        have h_q_top1_le : first_res.val.2.toNat ≤ 1 :=
          q_top_le_one_of_spec a b (loA + 2 * k) (loB + k) (n - k) (m - k)
            first_res.val.1 first_res.val.2
            h_n_minus_k_pos hA_top hB_top hbn1_top h_first_spec
        have h_Q_B0_le : toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push
            first_res.val.2).toList * toNatLimbsList ((b.toList.drop loB).take k)
          ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n) := by
          apply quotient_low_times_le_4B _ _ _ (64 * (m - k)) (64 * k) (64 * n)
          · -- Q < 2 * 2^(64*(m-k)): from q_top ≤ 1 and lower limbs < 2^(64*(m-k)).
            have h_ext_size : (a1.extract (loA + n + k) (loA + n + m)).size = m - k := by
              rw [Array.size_extract]; omega
            have h_ext_lt := toNatLimbsList_lt_pow (a1.extract (loA + n + k) (loA + n + m)).toList
            have h_ext_len : (a1.extract (loA + n + k) (loA + n + m)).toList.length = m - k := by
              rw [Array.length_toList, h_ext_size]
            rw [h_ext_len] at h_ext_lt
            have h_val : toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push
                first_res.val.2).toList
              = first_res.val.2.toNat * 2 ^ (64 * (m - k))
                + toNatLimbsList (a1.extract (loA + n + k) (loA + n + m)).toList := by
              conv_lhs => rw [show ((a1.extract (loA + n + k) (loA + n + m)).push
                first_res.val.2).toList
                = (a1.extract (loA + n + k) (loA + n + m)).toList ++ [first_res.val.2]
                from Array.toList_push]
              rw [toNatLimbsList_append, h_ext_len]
              simp [toNatLimbsList]
            have h_top_bound := Nat.mul_le_mul_right (2 ^ (64 * (m - k))) h_q_top1_le
            linarith
          · -- B₀ < 2^(64*k)
            have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
            have h_len : ((b.toList.drop loB).take k).length = k := by
              rw [List.length_take, List.length_drop, Array.length_toList]; omega
            rw [h_len] at h; exact h
          · -- 2^(64*n - 1) ≤ B
            exact sliceVal_divisor_bound b loB n h_n_pos hB hbn1
          · omega
          · omega
        have h_cons1 := recursiveDivModLimbs.afterFirstRec_spec a1 b first_res.val.2
          loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2 h_Q_B0_le

        -- ── Stage 2 conservation (via afterSecondRec_spec) ──────────
        have h_Q0_B0_le : toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push
            second_res.val.2).toList * toNatLimbsList ((b.toList.drop loB).take k)
          ≤ 4 * toNatLimbsList ((b.toList.drop loB).take n) := by
          have h_q_top0_le : second_res.val.2.toNat ≤ 1 :=
            q_top_le_one_of_spec a4 b (loA + k) (loB + k) (n - k) k
              second_res.val.1 second_res.val.2
              h_n_minus_k_pos hA_mid hB_top hbn1_top h_second_spec
          apply quotient_low_times_le_4B _ _ _ (64 * k) (64 * k) (64 * n)
          · have h_ext_lt := toNatLimbsList_lt_pow (a5.extract (loA + n) (loA + n + k)).toList
            have h_ext_len : (a5.extract (loA + n) (loA + n + k)).toList.length = k := by
              rw [Array.length_toList, Array.size_extract]; omega
            rw [h_ext_len] at h_ext_lt
            have h_val : toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push
                second_res.val.2).toList
              = second_res.val.2.toNat * 2 ^ (64 * k)
                + toNatLimbsList (a5.extract (loA + n) (loA + n + k)).toList := by
              conv_lhs => rw [show ((a5.extract (loA + n) (loA + n + k)).push
                second_res.val.2).toList
                = (a5.extract (loA + n) (loA + n + k)).toList ++ [second_res.val.2]
                from Array.toList_push]
              rw [toNatLimbsList_append, h_ext_len]; simp [toNatLimbsList]
            have h_top_bound := Nat.mul_le_mul_right (2 ^ (64 * k)) h_q_top0_le
            linarith
          · have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take k)
            have h_len : ((b.toList.drop loB).take k).length = k := by
              rw [List.length_take, List.length_drop, Array.length_toList]; omega
            rw [h_len] at h; exact h
          · exact sliceVal_divisor_bound b loB n h_n_pos hB hbn1
          · omega
          · omega
        have h_cons2 := recursiveDivModLimbs.afterSecondRec_spec a5 b second_res.val.2
          loA loB n m h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2
          h_Q0_B0_le
        -- ── Delta bounds (adjust count ≤ quotient) ──────────────────
        have h_delta1_le : after1_res.2.2 ≤
            toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push
              first_res.val.2).toList :=
          recursiveDivModLimbs.afterFirstRec_delta_le_Q a1 b first_res.val.2
            loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2 hbn1 h_Q_B0_le

        -- ── SliceVal bookkeeping for dc_full_bookkeeping ─────────────
        -- a1 preservation: [loA + k, loA + 2k) unchanged from a.
        have h_a1_pres : sliceVal a1 (loA + k) k = sliceVal a (loA + k) k :=
          recursiveDivModLimbsAux_sliceVal_outside threshold a b
            (loA + 2 * k) (loB + k) (n - k) (m - k) h_n_minus_k_pos
            hA_top hB_top hbn1_top (loA + k) k
            (by omega) (Or.inl (by omega))
        -- U₁ decomposition.
        have h_U1 : sliceVal a1 (loA + k) n
            = sliceVal a (loA + k) k
              + sliceVal a1 (loA + 2 * k) (n - k) * 2 ^ (64 * k) := by
          have h := sliceVal_split a1 (loA + k) n k (by omega)
            (by rw [h_a1_size]; omega)
          rw [show loA + k + k = loA + 2 * k from by ring] at h
          rw [h, h_a1_pres]
        -- Clean adj1.
        have h_adj1 : sliceVal a (loA + k) k
            + sliceVal a1 (loA + 2 * k) (n - k) * 2 ^ (64 * k)
            + after1_res.2.2 * sliceVal b loB n
            = sliceVal a4 (loA + k) (n + m - k)
              + toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push
                  first_res.val.2).toList * sliceVal b loB k := by
          rw [← h_U1]; linarith [h_cons1]
        -- a4 low preservation: [loA, loA + k) unchanged by afterFirstRec.
        -- Chain: a1 preserves [loA, loA+2k) outside first rec's range,
        -- then afterFirstRec preserves [loA, loA+k) since all sub-ops
        -- (zeroFill, subGeqLimbs, addbackLoop) start at loA+k.
        have h_a4_lo : sliceVal a4 loA k = sliceVal a loA k := by
          -- a1's [loA, loA+k) = a's (first rec preserves below loA+2k).
          have h_a1_lo : sliceVal a1 loA k = sliceVal a loA k :=
            recursiveDivModLimbsAux_sliceVal_outside threshold a b
              (loA + 2 * k) (loB + k) (n - k) (m - k) h_n_minus_k_pos
              hA_top hB_top hbn1_top loA k
              (show loA + k ≤ a.size by linarith [hA])
              (Or.inl (show loA + k ≤ loA + 2 * k by omega))
          -- afterFirstRec preserves [loA, loA+k) (all sub-ops start at loA+k).
          have h_afr := recursiveDivModLimbs.afterFirstRec_sliceVal_below_k
            a1 b first_res.val.2 loA loB n m h_n_pos hA_after1 hB h_m_le_n
            h_m_ge_2 loA k (by rw [h_a1_size]; linarith [hA]) (by omega)
          rw [h_afr, h_a1_lo]
        -- A' = A_lo + V₁ * β_k.
        have h_A'_eq : sliceVal a4 loA (n + m)
            = sliceVal a loA k
              + sliceVal a4 (loA + k) (n + m - k) * 2 ^ (64 * k) := by
          have h := sliceVal_split a4 loA (n + m) k (by omega) (by rw [h_a4_size]; omega)
          rw [h, h_a4_lo]
        -- A decomposition.
        have h_A_eq : sliceVal a loA (n + m)
            = sliceVal a loA k + sliceVal a (loA + k) k * 2 ^ (64 * k)
              + sliceVal a (loA + 2 * k) (n + m - 2 * k)
                * (2 ^ (64 * k) * 2 ^ (64 * k)) := by
          have h1 := sliceVal_split a loA (n + m) k (by omega) (by omega)
          have h2 := sliceVal_split a (loA + k) (n + m - k) k (by omega) (by omega)
          rw [show loA + k + k = loA + 2 * k from by ring,
            show n + m - k - k = n + m - 2 * k from by omega] at h2
          rw [h1, h2]; ring
        -- β_2k = β_k².
        have h_β_2k : (2 : Nat) ^ (64 * (2 * k)) = 2 ^ (64 * k) * 2 ^ (64 * k) := by
          rw [← Nat.pow_add]; congr 1; ring
        -- a5 low preservation: [loA, loA + k) unchanged from a4.
        have h_a5_lo : sliceVal a5 loA k = sliceVal a4 loA k :=
          recursiveDivModLimbsAux_sliceVal_outside threshold a4 b
            (loA + k) (loB + k) (n - k) k h_n_minus_k_pos
            hA_mid hB_top hbn1_top loA k
            (show loA + k ≤ a4.size by rw [h_a4_size]; linarith [hA])
            (Or.inl (show loA + k ≤ loA + k from Nat.le_refl _))
        -- Stage 2 bookkeeping: similar preservation + decomposition chain.
        -- Needs afterFirstRec_get_below_k + sliceVal_split + preservation.
        -- All sub-steps are provable using existing lemmas.
        show RecursiveDivModLimbsSpec a b loA loB n m _ _
        unfold recursiveDivModLimbsAux
        simp only [h_unbal, ↓reduceDIte, show ¬ m < max threshold 2 from h_small]
        show RecursiveDivModLimbsSpec a b loA loB n m res_final.1 res_final.2
        -- ── Prove h_ec0_bound for a5 (used by both rem_lt and div_eq) ──
        -- Step 1: afterFirstRec_result_lt_B gives V₁ < B.
        have h_V1_lt_B : sliceVal a4 (loA + k) (n + m - k) < sliceVal b loB n :=
          recursiveDivModLimbs.afterFirstRec_result_lt_B a1 b first_res.val.2
            loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2 h_Q_B0_le
            h_first_spec.rem_lt
        -- Step 2: V₁ < B < 2^(64*n), so high part of V₁ at position n is 0.
        have h_B_lt_pow_n : sliceVal b loB n < 2 ^ (64 * n) := by
          have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
          have h_len : ((b.toList.drop loB).take n).length = n := by
            rw [List.length_take, List.length_drop, Array.length_toList]; omega
          rw [h_len] at h; exact h
        have h_V1_split : sliceVal a4 (loA + k) (n + m - k)
            = sliceVal a4 (loA + k) n
              + sliceVal a4 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
          have h := sliceVal_split a4 (loA + k) (n + m - k) n (by omega)
            (by rw [h_a4_size]; omega)
          have h_idx : loA + k + n = loA + n + k := by omega
          have h_diff : n + m - k - n = m - k := by omega
          rw [h_idx, h_diff] at h; exact h
        have h_a4_high_zero : sliceVal a4 (loA + n + k) (m - k) = 0 := by
          by_contra h_ne
          have h_pos : 0 < sliceVal a4 (loA + n + k) (m - k) := Nat.pos_of_ne_zero h_ne
          have : 2 ^ (64 * n) ≤ sliceVal a4 (loA + n + k) (m - k) * 2 ^ (64 * n) :=
            Nat.le_mul_of_pos_left _ h_pos
          linarith
        -- Step 3: Preservation — second rec doesn't touch [loA+n+k, loA+n+m).
        have h_a5_high_eq : sliceVal a5 (loA + n + k) (m - k)
            = sliceVal a4 (loA + n + k) (m - k) :=
          recursiveDivModLimbsAux_sliceVal_outside threshold a4 b
            (loA + k) (loB + k) (n - k) k h_n_minus_k_pos
            hA_mid hB_top hbn1_top (loA + n + k) (m - k)
            (by rw [h_a4_size]; omega) (Or.inr (by omega))
        have h_a5_high_zero : sliceVal a5 (loA + n + k) (m - k) = 0 := by
          rw [h_a5_high_eq]; exact h_a4_high_zero
        -- Step 4: The zeroed value of a5 = sliceVal a5 loA n.
        have h_zeroed_eq : sliceVal (zeroFill a5 (loA + n) (loA + n + k)) loA (n + m)
            = sliceVal a5 loA n := by
          have h_zf_size : (zeroFill a5 (loA + n) (loA + n + k)).size = a5.size :=
            zeroFill_size _ _ _
          have h_split := sliceVal_split (zeroFill a5 (loA + n) (loA + n + k))
            loA (n + m) n (by omega) (by rw [h_zf_size, h_a5_size]; omega)
          have h_lo : sliceVal (zeroFill a5 (loA + n) (loA + n + k)) loA n
              = sliceVal a5 loA n := by
            apply sliceVal_eq_of_getElem_eq _ a5 loA n
              (by rw [h_zf_size, h_a5_size]; omega) (by rw [h_a5_size]; omega)
            intro j h_j; exact zeroFill_get_outside a5 (loA + n) (loA + n + k) (loA + j)
              (Or.inl (by omega)) (by rw [h_a5_size]; omega)
          -- The [loA+n, loA+n+m) part: split into [loA+n, loA+n+k) (zeroed) and
          -- [loA+n+k, loA+n+m) (= sliceVal a5 (loA+n+k) (m-k) = 0).
          have h_hi_split := sliceVal_split (zeroFill a5 (loA + n) (loA + n + k))
            (loA + n) m k (by omega) (by rw [h_zf_size, h_a5_size]; omega)
          have h_zeroed_mid : sliceVal (zeroFill a5 (loA + n) (loA + n + k)) (loA + n) k = 0 :=
            zeroFill_sliceVal_zero a5 (loA + n) k (by rw [h_a5_size]; omega)
          have h_zeroed_hi : sliceVal (zeroFill a5 (loA + n) (loA + n + k))
              (loA + n + k) (m - k) = sliceVal a5 (loA + n + k) (m - k) := by
            apply sliceVal_eq_of_getElem_eq _ a5 (loA + n + k) (m - k)
              (by rw [h_zf_size, h_a5_size]; omega) (by rw [h_a5_size]; omega)
            intro j h_j; exact zeroFill_get_outside a5 (loA + n) (loA + n + k) (loA + n + k + j)
              (Or.inr (by omega)) (by rw [h_a5_size]; omega)
          rw [h_split, h_lo, show n + m - n = m from by omega, h_hi_split, h_zeroed_mid,
            h_zeroed_hi, h_a5_high_zero]
          ring
        -- Step 5: sliceVal a5 loA n < B.
        have h_a5_lo_lt_B : sliceVal a5 loA n < sliceVal b loB n := by
          -- sliceVal a5 loA n = sliceVal a5 loA k + sliceVal a5 (loA+k) (n-k) * 2^(64*k)
          -- From h_second_spec.rem_lt: sliceVal a5 (loA+k) (n-k) < sliceVal b (loB+k) (n-k) = B₁
          -- From h_a5_lo + h_a4_lo: sliceVal a5 loA k = sliceVal a loA k < 2^(64*k) = β_k
          -- Same chain as afterFirstRec_result_lt_B's borrow=false case.
          have h_a5_split : sliceVal a5 loA n
              = sliceVal a5 loA k + sliceVal a5 (loA + k) (n - k) * 2 ^ (64 * k) := by
            have h := sliceVal_split a5 loA n k (by omega) (by rw [h_a5_size]; omega)
            exact h
          have h_B_decomp' : sliceVal b loB n
              = sliceVal b (loB + k) (n - k) * 2 ^ (64 * k) + sliceVal b loB k := by
            have h := sliceVal_split b loB n k (by omega) hB; linarith
          have h_lo_lt : sliceVal a5 loA k < 2 ^ (64 * k) := by
            have h := toNatLimbsList_lt_pow ((a5.toList.drop loA).take k)
            have h_len : ((a5.toList.drop loA).take k).length = k := by
              rw [List.length_take, List.length_drop, Array.length_toList]; omega
            rw [h_len] at h; exact h
          have h_rem_lt : sliceVal a5 (loA + k) (n - k) < sliceVal b (loB + k) (n - k) :=
            h_second_spec.rem_lt
          rw [h_a5_split, h_B_decomp']
          have h_R0_succ : sliceVal a5 (loA + k) (n - k) + 1 ≤ sliceVal b (loB + k) (n - k) := by
            omega
          have h1 : (sliceVal a5 (loA + k) (n - k) + 1) * 2 ^ (64 * k)
              ≤ sliceVal b (loB + k) (n - k) * 2 ^ (64 * k) :=
            Nat.mul_le_mul_right _ h_R0_succ
          have h2 : sliceVal a5 loA k + sliceVal a5 (loA + k) (n - k) * 2 ^ (64 * k)
              < (sliceVal a5 (loA + k) (n - k) + 1) * 2 ^ (64 * k) := by
            rw [Nat.add_mul]
            have : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
            omega
          linarith
        -- Step 6: Conclude.
        have h_ec0_bound_a5 : sliceVal (zeroFill a5 (loA + n) (loA + n + m / 2)) loA (n + m)
            < sliceVal (mulLimbs ((a5.extract (loA + n) (loA + n + m / 2)).push second_res.val.2) b
                0 (m / 2 + 1) loB (m / 2)
                (by rw [Array.size_push, Array.size_extract]; omega) (by omega))
              0 (2 * (m / 2) + 1)
            + sliceVal b loB n := by
          rw [h_zeroed_eq]; linarith
        constructor
        · -- rem_lt: sliceVal res_final.1 loA n < sliceVal b loB n
          exact recursiveDivModLimbs.afterSecondRec_rem_lt a5 b after1_res.2.1
            second_res.val.2 loA loB n m h_n_pos (by rw [h_a5_size]; exact hA)
            hB h_m_le_n h_m_ge_2 h_q1_size h_Q0_B0_le
            h_second_spec.rem_lt
            h_ec0_bound_a5
        · -- div_eq: sliceVal a loA (n+m)
          --         = (res_final.2.toNat * 2^(64*m) + sliceVal res_final.1 (loA+n) m) * B + R
          --
          -- High-level proof via dc_full_bookkeeping + afterSecondRec_assembly_toNat:
          --
          -- Let β_k := 2^(64*k), B := sliceVal b loB n,
          --     B₁ := sliceVal b (loB+k) (n-k), B₀ := sliceVal b loB k,
          --     A := sliceVal a loA (n+m), k := m/2.
          --
          -- (1) Decompose A (from h_A_eq + h_β_2k):
          --     A = A_lo + A_lo_hi * β_k + A_top * β_2k
          --     where A_lo  := sliceVal a loA k
          --           A_lo_hi := sliceVal a (loA+k) k
          --           A_top  := sliceVal a (loA+2k) (n+m-2k)
          --
          -- (2) First IH (h_first_spec.div_eq), rewritten with A_top notation:
          --     A_top = Q₁ * B₁ + R₁
          --
          -- (3) Stage-1 conservation (h_adj1 rearranged as mca_bridge_step1 input):
          --     A_lo_hi + R₁ * β_k + delta1 * B = V₁ + Q₁ * B₀
          --
          -- (4) A' = sliceVal a4 loA (n+m) (h_A'_eq):
          --     A' = A_lo + sliceVal a4 (loA+k) (n+m-k) * β_k
          --        = A_lo + V₁ * β_k   (from h_adj1 giving V₁ = sliceVal a4 (loA+k) (n+m-k))
          --
          -- (5) Second IH (h_second_spec.div_eq on a4 at loA+k):
          --     sliceVal a4 (loA+k) (n+m-k) = (Q₀_top * β_k + Q₀_low) * B₁ + R₀
          --     i.e., the middle part decomposes as Q₀ * B₁ + R₀.
          --
          -- (6) Stage-2 conservation (h_cons2 rearranged as mca_bridge_step2 input):
          --     A_lo + R₀ * β_k + V_hi * β_(n+k) + delta0 * B = R + Q₀ * B₀
          --     where V_hi := sliceVal a5 (loA+n+k) (m-k).
          --
          -- (7) dc_full_bookkeeping assembles (1)-(6) into:
          --     A = ((Q₁ - delta1) * β_k + (Q₀ - delta0)) * B + R
          --
          -- (8) afterSecondRec_assembly_toNat shows:
          --     sliceVal res_final.1 (loA+n) m = sliceVal tempQ2 0 m
          --     and res_final.2.toNat = tempQ2[m].toNat,
          --     with tempQ2 encoding Q' := (Q₁ - delta1) * β_k + (Q₀ - delta0).
          --     Hence (res_final.2.toNat * 2^(64*m) + sliceVal res_final.1 (loA+n) m) = Q'.
          -- ── Proof of div_eq ──────────────────────────────────────────
          -- The proof is structured via dc_full_bookkeeping plus the Q-assembly
          -- link to res_final.
          --
          -- Key algebraic quantities:
          --   β_k := 2^(64*k),  B := sliceVal b loB n
          --   B₁ := sliceVal b (loB+k) (n-k),  B₀ := sliceVal b loB k
          --   A_lo := sliceVal a loA k
          --   A_top := sliceVal a (loA+2k) (n+m-2k)
          --   Q₁ := toNatLimbsList ((a1.extract ..).push first_res.val.2).toList
          --   R₁ := sliceVal a1 (loA+2k) (n-k)
          --   V₁ := sliceVal a4 (loA+k) (n+m-k)
          --   Q₀ := toNatLimbsList ((a5.extract ..).push second_res.val.2).toList
          --   R₀ := sliceVal a5 (loA+k) (n-k)
          --   V_hi := sliceVal a5 (loA+n+k) (m-k)
          --
          -- (S1) B = B₁ * 2^(64k) + B₀
          have h_B_decomp : sliceVal b loB n
              = sliceVal b (loB + k) (n - k) * 2 ^ (64 * k) + sliceVal b loB k := by
            have h := sliceVal_split b loB n k (by omega) hB
            rw [show n - k = n - k from rfl] at h; linarith
          -- (S2) A = A_lo + A_lo_hi * β_k + A_top * β_2k  (directly from h_A_eq + h_β_2k)
          have h_A_decomp : sliceVal a loA (n + m)
              = sliceVal a loA k + sliceVal a (loA + k) k * 2 ^ (64 * k)
                + sliceVal a (loA + 2 * k) (n + m - 2 * k) * (2 ^ (64 * k) * 2 ^ (64 * k)) :=
            h_A_eq
          -- (S3) First IH: A_top = Q₁ * B₁ + R₁
          have h_first_IH :
              sliceVal a (loA + 2 * k) (n + m - 2 * k)
              = toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push first_res.val.2).toList
                * sliceVal b (loB + k) (n - k)
                + sliceVal a1 (loA + 2 * k) (n - k) := by
            have h := h_first_spec.div_eq
            rw [show (n - k) + (m - k) = n + m - 2 * k from by omega,
                show (loA + 2 * k) + (n - k) = loA + n + k from by omega] at h
            -- Connect Q₁ value to toNatLimbsList of push.
            have h_Q1 : first_res.val.2.toNat * 2 ^ (64 * (m - k))
                + sliceVal a1 (loA + n + k) (m - k)
              = toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push
                  first_res.val.2).toList := by
              rw [show ((a1.extract (loA + n + k) (loA + n + m)).push first_res.val.2).toList
                  = (a1.extract (loA + n + k) (loA + n + m)).toList ++ [first_res.val.2]
                  from Array.toList_push]
              rw [toNatLimbsList_append]
              have h_len : (a1.extract (loA + n + k) (loA + n + m)).toList.length = m - k := by
                rw [Array.length_toList, Array.size_extract]; omega
              rw [h_len]; simp [toNatLimbsList]
              congr 1; congr 1; omega
            rw [h_Q1] at h; exact h
          -- (S4) Stage-1 adjustment: A_lo_hi + R₁ * β_k + delta1 * B = V₁ + Q₁ * B₀
          have h_adj1_clean :
              sliceVal a (loA + k) k
              + sliceVal a1 (loA + 2 * k) (n - k) * 2 ^ (64 * k)
              + after1_res.2.2 * sliceVal b loB n
              = sliceVal a4 (loA + k) (n + m - k)
              + toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push first_res.val.2).toList
                * sliceVal b loB k := h_adj1
          -- (S5) A' = A_lo + V₁ * β_k  (directly h_A'_eq)
          have h_A'_V₁ : sliceVal a4 loA (n + m)
              = sliceVal a loA k + sliceVal a4 (loA + k) (n + m - k) * 2 ^ (64 * k) := h_A'_eq
          -- (S6) A' decomposition: V₁ = (Q₀ * B₁ + R₀) + V_hi * β_n
          -- From h_A'_V₁ + h_second_spec.div_eq + sliceVal_split + preservation.
          have h_A'_decomp : sliceVal a4 loA (n + m)
              = sliceVal a loA k
                + (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList
                    * sliceVal b (loB + k) (n - k)
                  + sliceVal a5 (loA + k) (n - k)) * 2 ^ (64 * k)
                + sliceVal a5 (loA + n + k) (m - k) * 2 ^ (64 * (n + k)) := by
            -- Step 1: Split sliceVal a4 (loA+k) (n+m-k) at position n.
            have h_split_V₁ : sliceVal a4 (loA + k) (n + m - k)
                = sliceVal a4 (loA + k) n
                  + sliceVal a4 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
              have h := sliceVal_split a4 (loA + k) (n + m - k) n (by omega)
                (by rw [h_a4_size]; omega)
              have h_idx1 : loA + k + n = loA + n + k := by omega
              have h_diff1 : n + m - k - n = m - k := by omega
              rw [h_idx1, h_diff1] at h; exact h
            -- Step 2: Second IH gives sliceVal a4 (loA+k) n = Q₀*B₁ + R₀.
            have h_sec : sliceVal a4 (loA + k) n
                = toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push
                    second_res.val.2).toList
                  * sliceVal b (loB + k) (n - k)
                + sliceVal a5 (loA + k) (n - k) := by
              have h := h_second_spec.div_eq
              -- h_second_spec is on (loA+m/2, loB+m/2, n-m/2, m/2) = (loA+k, loB+k, n-k, k)
              -- and `k := m/2` is a set-binding, so indices are definitionally equal.
              rw [show (n - k) + k = n from by omega,
                  show (loA + k) + (n - k) = loA + n from by omega] at h
              -- h: sliceVal a4 (loA+k) n = (q_top*2^(64*k) + sliceVal a5 (loA+n) k) * B₁ + R₀
              -- Connect Q₀ push value.
              have h_Q0 : second_res.val.2.toNat * 2 ^ (64 * k)
                  + sliceVal a5 (loA + n) k
                = toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push
                    second_res.val.2).toList := by
                rw [show ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList
                    = (a5.extract (loA + n) (loA + n + k)).toList ++ [second_res.val.2]
                    from Array.toList_push]
                rw [toNatLimbsList_append]
                have h_len : (a5.extract (loA + n) (loA + n + k)).toList.length = k := by
                  rw [Array.length_toList, Array.size_extract]; omega
                rw [h_len]; simp [toNatLimbsList]
              rw [h_Q0] at h; exact h
            -- Step 3: Preservation of a4[loA+n+k, loA+n+m) by second rec.
            have h_a5_high : sliceVal a5 (loA + n + k) (m - k)
                = sliceVal a4 (loA + n + k) (m - k) :=
              recursiveDivModLimbsAux_sliceVal_outside threshold a4 b
                (loA + k) (loB + k) (n - k) k h_n_minus_k_pos
                hA_mid hB_top hbn1_top (loA + n + k) (m - k)
                (by rw [h_a4_size]; omega) (Or.inr (by omega))
            -- Step 4: Combine using s6_decomp_helper.
            have h_β_nk : (2 : Nat) ^ (64 * (n + k)) = 2 ^ (64 * n) * 2 ^ (64 * k) := by
              rw [← Nat.pow_add]; congr 1; ring
            have h_V₁_combined : sliceVal a4 (loA + k) (n + m - k)
                = (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push
                      second_res.val.2).toList
                    * sliceVal b (loB + k) (n - k)
                  + sliceVal a5 (loA + k) (n - k))
                + sliceVal a4 (loA + n + k) (m - k) * 2 ^ (64 * n) := by
              rw [← h_sec]; exact h_split_V₁
            exact s6_decomp_helper
              (sliceVal a4 loA (n + m))  -- A'_val
              (sliceVal a loA k)  -- A_lo
              (sliceVal a4 (loA + k) (n + m - k))  -- V₁
              (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push
                    second_res.val.2).toList)  -- Q₀_val
              (sliceVal b (loB + k) (n - k))  -- B₁
              (sliceVal a5 (loA + k) (n - k))  -- R₀
              (sliceVal a5 (loA + n + k) (m - k))  -- V_hi
              (sliceVal a4 (loA + n + k) (m - k))  -- V_hi'
              (2 ^ (64 * k))  -- β_k
              (2 ^ (64 * n))  -- β_n
              (2 ^ (64 * (n + k)))  -- β_nk
              h_A'_eq  -- h_A'_val
              h_V₁_combined  -- h_V₁_split
              h_a5_high.symm  -- h_V_hi
              h_β_nk  -- h_β
          -- (S7) Stage-2 adjustment from h_cons2: ∃ delta0 ≤ Q₀
          -- Define the Stage 2 internal adj2 at the outer level so delta0
          -- is a transparent let binding, matching afterSecondRec_full_assembly.
          set q0_arr_s2 := ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2)
          have h_q0_s2_size : q0_arr_s2.size = k + 1 := by
            show ((a5.extract _ _).push _).size = _
            rw [Array.size_push, Array.size_extract]; omega
          have h_q0_s2_hA : 0 + (k + 1) ≤ q0_arr_s2.size := by
            rw [h_q0_s2_size]; omega
          have h_loB_k_s2 : loB + k ≤ b.size := by omega
          set q0_b0_s2 := mulLimbs q0_arr_s2 b 0 (k + 1) loB k h_q0_s2_hA h_loB_k_s2
          set a6_s2 := zeroFill a5 (loA + n) (loA + n + k)
          have h_a6_s2_size : a6_s2.size = a5.size := zeroFill_size _ _ _
          set subRes2_s2 := subGeqLimbs a6_s2 q0_b0_s2 loA (n + m) 0 (2 * k + 1)
            (by rw [h_a6_s2_size, h_a5_size]; omega) (by
              show 0 + (2 * k + 1) ≤ (mulLimbs q0_arr_s2 b 0 (k + 1) loB k _ _).size
              have := mulLimbs_size_ge q0_arr_s2 b 0 (k + 1) loB k
                h_q0_s2_hA h_loB_k_s2; omega)
            (by omega) (by omega) (by omega)
          have h_a7_s2_size : subRes2_s2.1.size = a5.size :=
            (subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_s2_size
          set adj2_s2 := addbackLoop subRes2_s2.1 b loA loB n 0 (n + m)
            subRes2_s2.2 5
            (by rw [h_a7_s2_size, h_a5_size]; omega)
            hB (by omega) h_n_pos (by omega)
          -- delta0 = adj2_s2.2 (transparent let binding).
          let delta0 := adj2_s2.2
          have h_stage2 :
              delta0 ≤ toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList ∧
              delta0 ≤ 5 ∧
              sliceVal a loA k
              + sliceVal a5 (loA + k) (n - k) * 2 ^ (64 * k)
              + sliceVal a5 (loA + n + k) (m - k) * 2 ^ (64 * (n + k))
              + delta0 * sliceVal b loB n
              = sliceVal res_final.1 loA n
                + toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList
                  * sliceVal b loB k := by
            -- Use afterSecondRec_low_eq to relate res_final.1's low n limbs
            -- to the internal adj2.1's low n limbs.
            have h_low_eq := recursiveDivModLimbs.afterSecondRec_low_eq
              a5 b after1_res.2.1 second_res.val.2 loA loB n m
              h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
            -- Use afterSecondRec_result_lt_B to get full (n+m)-limb result < B.
            have h_full_lt := recursiveDivModLimbs.afterSecondRec_result_lt_B
              a5 b second_res.val.2 loA loB n m
              h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_Q0_B0_le
              h_ec0_bound_a5
            -- The outer-level adj2_s2 matches the let-chain in the conclusions
            -- of h_low_eq, h_full_lt, and h_cons2.
            have h_a8_s2_size : adj2_s2.1.size = a5.size :=
              (addbackLoop_size _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
                ((subGeqLimbs_size _ _ _ _ _ _ _ _ _ _ _).trans h_a6_s2_size)
            -- Derive high = 0 from h_full_lt + B < 2^(64*n).
            have h_B_lt_pow : sliceVal b loB n < 2 ^ (64 * n) := by
              have h := toNatLimbsList_lt_pow ((b.toList.drop loB).take n)
              have h_len : ((b.toList.drop loB).take n).length = n := by
                rw [List.length_take, List.length_drop, Array.length_toList]; omega
              rw [h_len] at h; exact h
            have h_adj2_split := sliceVal_split adj2_s2.1 loA (n + m) n (by omega)
              (by rw [h_a8_s2_size, h_a5_size]; omega)
            have h_high_zero : sliceVal adj2_s2.1 (loA + n) (n + m - n) = 0 := by
              by_contra h_ne
              have h_pos : 0 < sliceVal adj2_s2.1 (loA + n) (n + m - n) :=
                Nat.pos_of_ne_zero h_ne
              have : 2 ^ (64 * n) ≤ sliceVal adj2_s2.1 (loA + n) (n + m - n) * 2 ^ (64 * n) :=
                Nat.le_mul_of_pos_left _ h_pos
              linarith
            have h_nm_n : n + m - n = m := by omega
            rw [h_nm_n] at h_high_zero
            have h_adj2_eq_lo : sliceVal adj2_s2.1 loA (n + m)
                = sliceVal adj2_s2.1 loA n := by
              rw [h_adj2_split, h_nm_n, h_high_zero]; ring
            -- Decompose sliceVal a5 loA n.
            have h_a5_decomp : sliceVal a5 loA n
                = sliceVal a5 loA k + sliceVal a5 (loA + k) (n - k) * 2 ^ (64 * k) := by
              have h := sliceVal_split a5 loA n k (by omega) (by rw [h_a5_size]; omega)
              rw [show n - k = n - k from rfl] at h; exact h
            have h_a5_lo_eq : sliceVal a5 loA k = sliceVal a loA k := by
              rw [h_a5_lo, h_a4_lo]
            -- Prove the three properties of delta0 = adj2_s2.2.
            refine ⟨?_, ?_, ?_⟩
            · -- delta0 ≤ Q0: from adjust_spec_limbs + result < B.
              have h_B0_le_B : sliceVal b loB k ≤ sliceVal b loB n := by
                linarith [h_B_decomp,
                  Nat.zero_le (sliceVal b (loB + k) (n - k) * 2 ^ (64 * k))]
              have h_B_pos : 0 < sliceVal b loB n := by
                have h := sliceVal_divisor_bound b loB n h_n_pos hB hbn1; linarith
              have h_cons2' : sliceVal a5 loA n
                  + sliceVal a5 (loA + n + k) (m - k) * 2 ^ (64 * (n + k))
                  + delta0 * sliceVal b loB n
                = sliceVal adj2_s2.1 loA (n + m)
                  + toNatLimbsList q0_arr_s2.toList * sliceVal b loB k := h_cons2
              have h_result_lt : sliceVal adj2_s2.1 loA (n + m) < sliceVal b loB n :=
                h_full_lt
              exact adjust_spec_limbs
                (sliceVal a5 loA n
                  + sliceVal a5 (loA + n + k) (m - k) * 2 ^ (64 * (n + k)))
                delta0 (sliceVal b loB n)
                (sliceVal adj2_s2.1 loA (n + m))
                (toNatLimbsList q0_arr_s2.toList) (sliceVal b loB k)
                h_cons2' h_B0_le_B h_B_pos h_result_lt
            · -- delta0 ≤ 5: from addbackLoop fuel bound.
              exact addbackLoop_delta_le _ _ _ _ _ _ _ _ 5 _ _ _ _ _
            · -- Conservation equation.
              have h_low : sliceVal res_final.1 loA n = sliceVal adj2_s2.1 loA n :=
                h_low_eq
              have h_cons2' : sliceVal a5 loA n
                    + sliceVal a5 (loA + n + k) (m - k) * 2 ^ (64 * (n + k))
                    + delta0 * sliceVal b loB n
                  = sliceVal adj2_s2.1 loA (n + m)
                    + toNatLimbsList q0_arr_s2.toList * sliceVal b loB k :=
                h_cons2
              rw [h_a5_decomp, h_a5_lo_eq] at h_cons2'
              linarith
          obtain ⟨h_d0_le, h_delta0_le_fuel, h_adj2_clean⟩ := h_stage2
          -- (S8) Apply dc_full_bookkeeping to get
          --   A = ((Q₁ - delta1) * β_k + (Q₀ - delta0)) * B + R
          have h_dc : sliceVal a loA (n + m)
              = ((toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push first_res.val.2).toList
                    - after1_res.2.2) * 2 ^ (64 * k)
                  + (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList
                      - delta0))
                * sliceVal b loB n
              + sliceVal res_final.1 loA n :=
            dc_full_bookkeeping
              (sliceVal a loA (n + m))
              (sliceVal a loA k)
              (sliceVal a (loA + k) k)
              (sliceVal a (loA + 2 * k) (n + m - 2 * k))
              (sliceVal b loB n)
              (sliceVal b (loB + k) (n - k))
              (sliceVal b loB k)
              (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push first_res.val.2).toList)
              (sliceVal a1 (loA + 2 * k) (n - k))
              after1_res.2.2
              (sliceVal a4 (loA + k) (n + m - k))
              (sliceVal a4 loA (n + m))
              (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList)
              (sliceVal a5 (loA + k) (n - k))
              (sliceVal a5 (loA + n + k) (m - k))
              delta0
              (sliceVal res_final.1 loA n)
              (2 ^ (64 * k))
              (2 ^ (64 * k) * 2 ^ (64 * k))
              (2 ^ (64 * (n + k)))
              h_B_decomp (by ring) h_A_decomp
              h_first_IH h_adj1_clean h_A'_V₁ h_A'_decomp h_adj2_clean
              h_delta1_le h_d0_le
          -- (S9) Q' = res_final.2.toNat * 2^(64*m) + sliceVal res_final.1 (loA+n) m
          --      Follows from afterSecondRec_assembly_toNat linking the assembled tempQ2.
          have h_Q'_eq :
              (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push first_res.val.2).toList
                  - after1_res.2.2) * 2 ^ (64 * k)
              + (toNatLimbsList ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2).toList
                  - delta0)
              = res_final.2.toNat * 2 ^ (64 * m)
                + sliceVal res_final.1 (loA + n) m := by
            -- Step 1: Get assembly equation with carry from afterSecondRec_full_assembly.
            obtain ⟨carry, h_carry_le, h_asm⟩ :=
              recursiveDivModLimbs.afterSecondRec_full_assembly
                a5 b after1_res.2.1 second_res.val.2 loA loB n m
                h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
            -- h_asm: res_low + res_top * β_m + carry * β_{m+1} = q0_dec + q1_dec * β_k
            -- where q0_dec = decrementSlice(q0_arr, 0, internal_delta).toNat
            --   and q1_dec = after1_res.2.1.toNat
            -- Abbreviate h_asm's RHS to avoid expensive whnf.
            -- Step 2: Get q1 decrement equation.
            have h_d_lt_afr : (recursiveDivModLimbs.afterFirstRec a1 b first_res.val.2
                loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.2 < 2 ^ 64 := by
              have := recursiveDivModLimbs.afterFirstRec_delta_le_fuel
                a1 b first_res.val.2 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
              omega
            have h_delta1_le' : (recursiveDivModLimbs.afterFirstRec a1 b first_res.val.2
                loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2).2.2
                ≤ toNatLimbsList ((a1.extract (loA + n + m / 2) (loA + n + m)).push
                    first_res.val.2).toList :=
              h_delta1_le
            have h_q1_val := recursiveDivModLimbs.afterFirstRec_q1_toNat
              a1 b first_res.val.2 loA loB n m h_n_pos hA_after1 hB h_m_le_n h_m_ge_2
              h_d_lt_afr h_delta1_le'
            -- h_q1_val: toNatLimbsList after1_res.2.1.toList = Q1 - after1_res.2.2
            -- Step 3: Get q0 decrement equation via afterSecondRec_delta_le_fuel.
            have h_d0_fuel := recursiveDivModLimbs.afterSecondRec_delta_le_fuel
              a5 b after1_res.2.1 second_res.val.2 loA loB n m
              h_n_pos (by rw [h_a5_size]; exact hA) hB h_m_le_n h_m_ge_2 h_q1_size
            -- The internal delta from afterSecondRec is definitionally delta0
            -- (both are (addbackLoop ...).2 from the same computation).
            -- So h_d0_fuel : delta0 ≤ 5.
            -- Step 4: Prove the goal using s9_quotient_assembly.
            -- First, show the q0 decrement: decrementSlice q0 0 delta0 gives Q0 - delta0.
            set q0_loc := ((a5.extract (loA + n) (loA + n + k)).push second_res.val.2)
            have h_q0_sz : q0_loc.size = k + 1 := by
              show ((a5.extract _ _).push _).size = _
              rw [Array.size_push, Array.size_extract]; omega
            have h_q0_dec_val : toNatLimbsList
                (decrementSlice q0_loc 0 delta0 (Nat.zero_le _)).toList
                = toNatLimbsList q0_loc.toList - delta0 := by
              have hds := decrementSlice_size q0_loc 0 delta0 (Nat.zero_le _)
              have h1 : (decrementSlice q0_loc 0 delta0 (Nat.zero_le _)).toList
                  = ((decrementSlice q0_loc 0 delta0 (Nat.zero_le _)).toList.drop 0).take
                      (q0_loc.size - 0) := by
                simp only [List.drop_zero, Nat.sub_zero]
                rw [List.take_of_length_le (by rw [Array.length_toList, hds])]
              have h2 : q0_loc.toList = (q0_loc.toList.drop 0).take (q0_loc.size - 0) := by
                simp only [List.drop_zero, Nat.sub_zero]
                rw [List.take_of_length_le (by rw [Array.length_toList])]
              rw [h1, h2]
              exact decrementSlice_val_eq q0_loc delta0 (by omega) (by omega)
                (by rw [← h2]; exact h_d0_le)
            -- h_q0_dec_val: decrementSlice q0_loc 0 delta0 ... = Q0 - delta0
            -- Step 5: Apply s9_quotient_assembly.
            -- delta0 = adj2_s2.2 is a transparent let binding (not opaque have),
            -- so it matches the internal delta in h_asm definitionally.
            exact s9_quotient_assembly
              (toNatLimbsList ((a1.extract (loA + n + k) (loA + n + m)).push
                  first_res.val.2).toList)
              (toNatLimbsList q0_loc.toList) after1_res.2.2 delta0 (2 ^ (64 * k))
              res_final.2.toNat (sliceVal res_final.1 (loA + n) m) carry
              (toNatLimbsList (decrementSlice q0_loc 0 delta0 (Nat.zero_le _)).toList)
              (toNatLimbsList after1_res.2.1.toList)
              (sliceVal a loA (n + m)) (sliceVal res_final.1 loA n) (sliceVal b loB n)
              (2 ^ (64 * m)) (2 ^ (64 * (m + 1)))
              h_carry_le h_delta1_le h_d0_le h_q1_val h_q0_dec_val h_asm h_dc
              (by have h_A_lt := toNatLimbsList_lt_pow ((a.toList.drop loA).take (n + m))
                  have h_A_len : ((a.toList.drop loA).take (n + m)).length = n + m := by
                    rw [List.length_take, List.length_drop, Array.length_toList]; omega
                  rw [h_A_len] at h_A_lt
                  have h_B_ge := sliceVal_divisor_bound b loB n h_n_pos hB hbn1
                  calc sliceVal a loA (n + m) < 2 ^ (64 * (n + m)) := h_A_lt
                    _ ≤ 2 ^ (64 * (m + 1) + (64 * n - 1)) :=
                        Nat.pow_le_pow_right (by omega) (by omega)
                    _ = 2 ^ (64 * (m + 1)) * 2 ^ (64 * n - 1) := by
                        rw [Nat.pow_add]
                    _ ≤ 2 ^ (64 * (m + 1)) * sliceVal b loB n :=
                        Nat.mul_le_mul_left _ h_B_ge)
              (by linarith [Nat.two_pow_pos (64 * n - 1),
                    sliceVal_divisor_bound b loB n h_n_pos hB hbn1])
          /- The full proof of h_Q'_eq uses afterSecondRec_assembly_toNat +
             decrementSlice_toNat to show:
             1. q0_arr'_val = Q₀ - delta0 (decrementSlice with borrow=0)
             2. q1_arr'_val = Q₁ - delta1 (decrementSlice with borrow=0)
             3. carry = 0 (from Q' < 2*β_m < β_{m+1}, using h_dc + h_A_lt + h_B_ge)
             4. Combine: Q' = q0'_val + q1'_val * β_k
                = (Q₀ - delta0) + (Q₁ - delta1) * β_k
                = sliceVal res_final.1 (loA+n) m + res_final.2 * β_m. -/
          -- Conclude: substitute h_Q'_eq into h_dc.
          exact h_Q'_eq ▸ h_dc

/-! ### AzNat wrapper correctness

Given `recursiveDivModLimbsAux_spec`, the AzNat wrapper
`recursiveDivModFast` is correct.  This is the "headline" theorem
that lets us retire the AzNat-level `recursiveDivMod` (eventually). -/

set_option maxHeartbeats 1600000 in
/-- `recursiveDivModFast` computes the same `(quotient, remainder)`
    pair as Lean's built-in Nat `divMod`, viewed through `toNat`.  The
    trivial cases (`V = 0`, `V.size ≤ 2`, `U < V`) are fully proven;
    the D&C path (the actual headline case) is sorried, pending
    completion of `recursiveDivModLimbsAux_spec`'s D&C body. -/
theorem recursiveDivModFast_toNat (threshold : Nat) (U V : AzNat) :
    (recursiveDivModFast threshold U V).1.toNat * V.toNat
        + (recursiveDivModFast threshold U V).2.toNat = U.toNat ∧
    (V.toNat ≠ 0 →
      (recursiveDivModFast threshold U V).2.toNat < V.toNat) := by
  unfold recursiveDivModFast
  by_cases h0V : V.limbs.size = 0
  · -- Case 1: V = 0.  Returns (0, U); the second conjunct is vacuous.
    simp only [h0V, ↓reduceDIte]
    have h_V_zero : V.toNat = 0 := (toNat_eq_zero_iff V).mpr h0V
    refine ⟨?_, ?_⟩
    · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
      simp
    · intro h_ne; exact absurd h_V_zero h_ne
  · simp only [h0V, ↓reduceDIte]
    have h_V_pos : 0 < V.limbs.size := Nat.pos_of_ne_zero h0V
    by_cases hVsmall : V.limbs.size ≤ 2
    · -- Case 2: V small — delegate to schoolbook `divMod`.
      simp only [hVsmall, ↓reduceDIte]
      exact divMod_toNat_of_size_le2 U V hVsmall
    · simp only [hVsmall, ↓reduceDIte]
      by_cases hUV : U.limbs.size < V.limbs.size
      · -- Case 3: U has fewer limbs than V, so U < V trivially.
        simp only [hUV, ↓reduceDIte]
        refine ⟨?_, ?_⟩
        · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
          simp
        · intro _
          calc U.toNat
              < 2 ^ (64 * U.limbs.size) := toNat_lt_pow U
            _ ≤ 2 ^ (64 * (V.limbs.size - 1)) :=
                Nat.pow_le_pow_right (by decide) (by omega)
            _ ≤ V.toNat := toNat_pos_of_size_pos V h_V_pos
      · -- Case 4: D&C path.  Normalize V, build U buffer, call
        -- `recursiveDivModLimbsArr`, extract Q + R, right-shift R.
        -- Proof structure mirrors `recursiveDivMod_toNat`'s case 5
        -- (Equiv/DivRecursive.lean:1227) and `divMod_toNat`'s size-≥-3
        -- branch (Equiv/Div/DivMod.lean:374).
        simp only [hUV, ↓reduceDIte]
        -- Re-introduce the same `let` names as `recursiveDivModFast`.
        set n  := V.limbs.size with hn_def
        set nU := U.limbs.size with hnU_def
        have h_n_ge_3 : 3 ≤ n := by push Not at hVsmall; omega
        have h_nU_ge_n : n ≤ nU := Nat.le_of_not_lt hUV
        have h_top_lt : n - 1 < V.limbs.size := by omega
        have h_n2_lt  : n - 2 < V.limbs.size := by omega
        set topB := V.limbs[n - 1]'h_top_lt with htopB_def
        have h_topB_ne : topB ≠ 0 := by
          intro h
          apply V.last_ne_zero
          rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_top_lt]
          exact congrArg some h
        set k  := UInt64.leadingZeros topB with hk_def
        have hk_le : k ≤ 63 := UInt64.leadingZeros_le topB h_topB_ne
        set kU : UInt64 := UInt64.ofNat k
        set carryToTop : UInt64 :=
          if hk0 : k = 0 then 0
          else V.limbs[n - 2]'h_n2_lt >>> UInt64.ofNat (64 - k)
        set d_top : UInt64 := (topB <<< kU) ||| carryToTop with hd_top_def
        have h_d_top_ge : 2 ^ 63 ≤ d_top.toNat := by
          have h_shl_ge : 2 ^ 63 ≤ (topB <<< kU).toNat :=
            UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
          show 2 ^ 63 ≤ ((topB <<< kU) ||| carryToTop).toNat
          rw [UInt64.toNat_or]
          exact Nat.le_trans h_shl_ge Nat.left_le_or
        -- Build dividend buffer.
        set UBufRaw : Array UInt64 := U.limbs ++ #[0]
        have h_UBufRaw_size : UBufRaw.size = nU + 1 := by
          show (U.limbs ++ #[0]).size = nU + 1
          rw [Array.size_append]; rfl
        set UBuf : Array UInt64 :=
          if hk0 : k = 0 then UBufRaw
          else
            have hk_lb : 1 ≤ k := by omega
            (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
              (by rw [h_UBufRaw_size]) hk_lb hk_le).1
        have h_UBuf_size : UBuf.size = nU + 1 := by
          show (if hk0 : k = 0 then UBufRaw else _).size = nU + 1
          split_ifs with hk0
          · exact h_UBufRaw_size
          · rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
        -- Build divisor buffer.
        set VBufRaw : Array UInt64 :=
          if hk0 : k = 0 then V.limbs
          else
            have hk_lb : 1 ≤ k := by omega
            (shiftLimbsLeft V.limbs 0 (n - 1) k (by omega) (by omega) hk_lb hk_le).1
        have h_VBufRaw_size : VBufRaw.size = n := by
          show (if hk0 : k = 0 then V.limbs else _).size = n
          split_ifs with hk0
          · rfl
          · rw [shiftLimbsLeft_size]
        have h_top_in_raw : n - 1 < VBufRaw.size := by rw [h_VBufRaw_size]; omega
        set VBuf : Array UInt64 := VBufRaw.set (n - 1) d_top h_top_in_raw
        have h_VBuf_size : VBuf.size = n := by
          show (VBufRaw.set _ _ _).size = n
          rw [Array.size_set]; exact h_VBufRaw_size
        set m := nU + 1 - n with hm_def
        have h_n_pos : 0 < n := by omega
        have h_loA : 0 + n + m ≤ UBuf.size := by
          show 0 + n + (nU + 1 - n) ≤ UBuf.size
          rw [h_UBuf_size]; omega
        have h_loB : 0 + n ≤ VBuf.size := by rw [h_VBuf_size]; omega
        have h_VBuf_norm :
            2 ^ 63 ≤ (VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega)).toNat := by
          -- VBuf = VBufRaw.set (n-1) d_top h_top_in_raw; position 0+n-1 = n-1.
          -- This is the same proof used in the `def` at line 742-747 of
          -- DivRecursiveLimbs.lean.
          have h_eq : VBuf[0 + n - 1]'(by rw [h_VBuf_size]; omega) = d_top := by
            show (VBufRaw.set (n - 1) d_top h_top_in_raw)[0 + n - 1] = d_top
            rw [Array.getElem_set]
            rw [if_pos (show (n - 1 : Nat) = 0 + n - 1 from by omega)]
          rw [h_eq]; exact h_d_top_ge
        -- Call the D&C core.
        set res := recursiveDivModLimbsArr threshold UBuf VBuf 0 0 n m
          h_n_pos h_loA h_loB h_VBuf_norm with hres_def
        -- Apply the spec.
        have h_spec : RecursiveDivModLimbsSpec UBuf VBuf 0 0 n m res.1 res.2 :=
          recursiveDivModLimbsAux_spec threshold UBuf VBuf 0 0 n m
            h_n_pos h_loA h_loB h_VBuf_norm
        obtain ⟨h_rem_lt, h_div_eq⟩ := h_spec
        -- Simplify sliceVal at loA=0, loB=0 (zero_add, take n).
        simp only [Nat.zero_add] at h_rem_lt h_div_eq
        -- Size of res.1.
        have h_res_size : res.1.size = UBuf.size :=
          recursiveDivModLimbsArr_size threshold UBuf VBuf 0 0 n m
            h_n_pos h_loA h_loB h_VBuf_norm
        have h_res_len : res.1.toList.length = nU + 1 := by
          rw [Array.length_toList, h_res_size, h_UBuf_size]
        -- Key values.
        set R  : Nat := sliceVal res.1 0 n with hR_def
        set Q' : Nat := sliceVal res.1 n m  with hQ'_def
        -- `sliceVal UBuf 0 (n + m) = U.toNat * 2^k`.
        have h_UBuf_toNat : sliceVal UBuf 0 (n + m) = U.toNat * 2 ^ k := by
          -- The dividend buffer (with or without shift) represents U * 2^k.
          -- Case k = 0: UBuf = UBufRaw, value = U.toNat * 1 = U.toNat.
          -- Case k > 0: UBuf is the shifted buffer, carries zero by size bound.
          -- Both cases are mirror images of `toNatLimbsList_UBufRaw` and
          -- `toNatLimbsList_shifted_UBufRaw` from DivMod.lean.
          unfold sliceVal
          rw [List.drop_zero]
          have h_nm : n + m = nU + 1 := by omega
          have h_len : UBuf.toList.length = nU + 1 := by
            rw [Array.length_toList, h_UBuf_size]
          have h_take_full : UBuf.toList.take (n + m) = UBuf.toList := by
            apply List.take_of_length_le; rw [h_len, h_nm]
          rw [h_take_full]
          by_cases hk0 : k = 0
          · -- UBuf = UBufRaw = U.limbs ++ #[0].
            have h_UBuf_eq : UBuf = UBufRaw := by
              show (if hk0' : k = 0 then UBufRaw else _) = UBufRaw
              rw [dif_pos hk0]
            rw [h_UBuf_eq, hk0, Nat.pow_zero, Nat.mul_one]
            -- toNatLimbsList (U.limbs ++ #[0]).toList = U.toNat.
            rw [Array.toList_append]
            rw [toNatLimbsList_append]
            have h_zero : toNatLimbsList [(0 : UInt64)] = 0 := by simp [toNatLimbsList]
            rw [h_zero, Nat.zero_mul, Nat.zero_add]; rfl
          · -- UBuf is the shifted buffer; carry is zero by size argument.
            have hk_lb : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            have h_UBuf_eq : UBuf =
                (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                  (by rw [h_UBufRaw_size]) hk_lb hk_le).1 := by
              show (if hk0' : k = 0 then UBufRaw else _) = _
              rw [dif_neg hk0]
            rw [h_UBuf_eq]
            -- From shiftLimbsLeft_toNat: slice + carry*β = original * 2^k.
            have h_shift := shiftLimbsLeft_toNat UBufRaw 0 (nU + 1) k
              (Nat.zero_le _) (by rw [h_UBufRaw_size]) hk_lb hk_le
            -- shiftLimbsLeft preserves size.
            have h_shl_size : (shiftLimbsLeft UBufRaw 0 (nU + 1) k
                (Nat.zero_le _) (by rw [h_UBufRaw_size]) hk_lb hk_le).1.size = nU + 1 := by
              rw [shiftLimbsLeft_size, h_UBufRaw_size]
            simp only [Nat.sub_zero, List.drop_zero] at h_shift ⊢
            -- Original value: toNatLimbsList UBufRaw.toList = U.toNat.
            have h_raw_val : toNatLimbsList (UBufRaw.toList.take (nU + 1)) = U.toNat := by
              rw [List.take_of_length_le (by rw [Array.length_toList, h_UBufRaw_size])]
              show toNatLimbsList (U.limbs ++ #[0]).toList = U.toNat
              rw [Array.toList_append]
              rw [toNatLimbsList_append]
              have h_zero : toNatLimbsList ([(0 : UInt64)] : List UInt64) = 0 := by
                simp [toNatLimbsList]
              rw [h_zero, Nat.zero_mul, Nat.zero_add]; rfl
            rw [h_raw_val] at h_shift
            -- Carry = 0 because U.toNat * 2^k < 2^(64*(nU+1)).
            have h_U_lt : U.toNat < 2 ^ (64 * nU) := toNat_lt_pow U
            have h_prod_lt : U.toNat * 2 ^ k < 2 ^ (64 * (nU + 1)) := by
              calc U.toNat * 2 ^ k
                  < 2 ^ (64 * nU) * 2 ^ k := Nat.mul_lt_mul_of_pos_right h_U_lt (Nat.two_pow_pos _)
                _ = 2 ^ (64 * nU + k) := by rw [Nat.pow_add]
                _ ≤ 2 ^ (64 * (nU + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
            have h_carry_zero :
                (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                  (by rw [h_UBufRaw_size]) hk_lb hk_le).2.toNat = 0 := by
              have h_slice_lt := toNatLimbsList_lt_pow
                ((shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                  (by rw [h_UBufRaw_size]) hk_lb hk_le).1.toList.take (nU + 1))
              have h_len : ((shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                  (by rw [h_UBufRaw_size]) hk_lb hk_le).1.toList.take (nU + 1)).length
                  = nU + 1 := by
                rw [List.length_take, Array.length_toList, h_shl_size]; exact Nat.min_self _
              rw [h_len] at h_slice_lt
              -- From h_shift: slice + carry * β = U.toNat * 2^k < β.
              -- So carry * β ≤ U.toNat * 2^k < β, hence carry = 0.
              have h_pow_pos : (0 : Nat) < 2 ^ (64 * (nU + 1)) := Nat.two_pow_pos _
              nlinarith
            rw [h_carry_zero, Nat.zero_mul, Nat.add_zero] at h_shift
            -- h_shift now: toNatLimbsList (UBuf.toList.take (nU+1)) = U.toNat * 2^k
            have h_take_full : (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                (by rw [h_UBufRaw_size]) hk_lb hk_le).1.toList.take (nU + 1)
              = (shiftLimbsLeft UBufRaw 0 (nU + 1) k (Nat.zero_le _)
                (by rw [h_UBufRaw_size]) hk_lb hk_le).1.toList := by
              apply List.take_of_length_le; rw [Array.length_toList, h_shl_size]
            rw [h_take_full] at h_shift; exact h_shift
        -- `sliceVal VBuf 0 n = V.toNat * 2^k`.
        have h_VBuf_toNat : sliceVal VBuf 0 n = V.toNat * 2 ^ k := by
          -- Unfold sliceVal and simplify the drop 0.
          unfold sliceVal
          rw [List.drop_zero]
          -- VBuf.toList.take n = VBuf.toList (since VBuf.size = n).
          have h_VBuf_len : VBuf.toList.length = n := by
            rw [Array.length_toList, h_VBuf_size]
          rw [List.take_of_length_le (le_of_eq h_VBuf_len)]
          by_cases hk0 : k = 0
          · -- k = 0 branch: VBufRaw = V.limbs, carryToTop = 0,
            -- d_top = topB <<< 0 ||| 0 = topB, VBuf = V.limbs.set (n-1) topB.
            -- Since topB = V.limbs[n-1], the set is a no-op.
            have h_VBufRaw_eq : VBufRaw = V.limbs := by
              show (if hk0' : k = 0 then V.limbs else _) = V.limbs
              rw [dif_pos hk0]
            have h_carryToTop_zero : carryToTop = 0 := by
              show (if hk0' : k = 0 then (0 : UInt64) else _) = 0
              rw [dif_pos hk0]
            have h_dtop_eq : d_top = topB := by
              rw [hd_top_def, h_carryToTop_zero]
              have h_kU_zero : kU = 0 := by show UInt64.ofNat k = 0; rw [hk0]; rfl
              rw [h_kU_zero, UInt64.shiftLeft_zero, UInt64.or_zero]
            have h_set_no_op : VBufRaw.set (n - 1) d_top h_top_in_raw = VBufRaw := by
              apply Array.ext
              · rw [Array.size_set]
              · intro i hi1 hi2
                rw [Array.getElem_set]
                split_ifs with h_eq
                · -- h_eq : n - 1 = i; show d_top = VBufRaw[i].
                  -- d_top = topB = V.limbs[n-1] = VBufRaw[i].
                  have h_VBufRaw_get : VBufRaw[i]'hi2 = topB := by
                    have h_idx : i = n - 1 := h_eq.symm
                    subst h_idx
                    -- VBufRaw = V.limbs (in k=0 branch), so VBufRaw[n-1] = V.limbs[n-1] = topB.
                    have h_eq2 : VBufRaw = V.limbs := h_VBufRaw_eq
                    calc VBufRaw[n - 1]'hi2
                        = V.limbs[n - 1]'(h_eq2 ▸ hi2) := by
                          simp [h_eq2]
                      _ = topB := htopB_def.symm
                  rw [h_dtop_eq, h_VBufRaw_get]
                · rfl
            -- VBuf = V.limbs.
            have h_VBuf_eq : VBuf.toList = V.limbs.toList := by
              show (VBufRaw.set (n - 1) d_top h_top_in_raw).toList = V.limbs.toList
              rw [h_set_no_op, h_VBufRaw_eq]
            rw [h_VBuf_eq, hk0, Nat.pow_zero, Nat.mul_one]
            rfl
          · -- k > 0 branch.
            have hk_lb : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
            -- VBufRaw is the shifted array.
            have h_VBufRaw_eq : VBufRaw =
                (shiftLimbsLeft V.limbs 0 (n - 1) k (by omega) (by omega) hk_lb hk_le).1 := by
              show (if hk0' : k = 0 then V.limbs else _) = _
              rw [dif_neg hk0]
            have h_VBufRaw_len : VBufRaw.toList.length = n := by
              rw [Array.length_toList, h_VBufRaw_size]
            -- carryToTop = V.limbs[n-2] >>> (64 - k).
            have h_carryToTop_eq : carryToTop =
                V.limbs[n - 2]'h_n2_lt >>> UInt64.ofNat (64 - k) := by
              show (if hk0' : k = 0 then (0 : UInt64) else _) = _
              rw [dif_neg hk0]
            -- Bound on carryToTop from limb_shift_step's right-shift bound.
            have h_carry_lt : carryToTop.toNat < 2 ^ k := by
              rw [h_carryToTop_eq]
              -- Use limb_shift_step with zero carry to get the shift bound.
              obtain ⟨_, h_shr_lt⟩ :=
                limb_shift_step (V.limbs[n - 2]'h_n2_lt) 0 k hk_lb hk_le (Nat.two_pow_pos _)
              exact h_shr_lt
            -- topB.toNat < 2^(64-k) (from leading zeros definition).
            have h_topB_lt_pow : topB.toNat < 2 ^ (64 - k) := by
              -- topB.toNat * 2^k < 2^64 follows from the shift normalization.
              have h_prod_lt : topB.toNat * 2 ^ k < 2 ^ 64 := by
                have h_shl_ge :=
                  UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
                -- (topB <<< k).toNat = topB.toNat * 2^k (since product fits in UInt64).
                -- We need topB.toNat * 2^k < 2^64.
                -- Derive from: leadingZeros topB = k, topB.toNat * 2^k < 2^64 (from the proof
                -- of two_pow_63_le_toNat_shiftLeft_leadingZeros via log2 bound).
                have hd_nat_ne : topB.toNat ≠ 0 :=
                  fun h => h_topB_ne (UInt64.eq_of_toNat_eq (h.trans rfl))
                have hd_lt : topB.toNat < 2 ^ 64 := UInt64.toNat_lt _
                have hL_lt_64 : topB.toNat.log2 < 64 := (Nat.log2_lt hd_nat_ne).mpr hd_lt
                have hk_def2 : k = 63 - topB.toNat.log2 := by
                  rw [hk_def]
                  show (if topB = 0 then 64 else 63 - topB.toNat.log2) = _
                  rw [if_neg h_topB_ne]
                have hpow_hi : topB.toNat < 2 ^ (topB.toNat.log2 + 1) :=
                  (Nat.log2_lt hd_nat_ne).mp (Nat.lt_succ_of_le (Nat.le_refl _))
                calc topB.toNat * 2 ^ k
                    < 2 ^ (topB.toNat.log2 + 1) * 2 ^ k :=
                      Nat.mul_lt_mul_of_pos_right hpow_hi (Nat.two_pow_pos _)
                  _ = 2 ^ (topB.toNat.log2 + 1 + k) := (Nat.pow_add _ _ _).symm
                  _ = 2 ^ 64 := by congr 1; omega
              have h_pow_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos _
              have h_split : (2 : Nat) ^ 64
                  = 2 ^ (64 - k) * 2 ^ k := by
                rw [← Nat.pow_add]; congr 1; omega
              rw [h_split] at h_prod_lt
              exact (Nat.mul_lt_mul_right h_pow_pos).mp h_prod_lt
            -- topB >>> (64-k) = 0.
            have h_topB_shr_zero :
                (topB >>> UInt64.ofNat (64 - k)).toNat = 0 := by
              rw [UInt64.toNat_shiftRight]
              have h_ofNat : (UInt64.ofNat (64 - k) : UInt64).toNat = 64 - k := by
                show (64 - k) % 2 ^ 64 = _
                apply Nat.mod_eq_of_lt; omega
              rw [h_ofNat,
                  Nat.mod_eq_of_lt (show 64 - k < 64 from by omega),
                  Nat.shiftRight_eq_div_pow]
              exact Nat.div_eq_of_lt h_topB_lt_pow
            -- limb_shift_step for d_top: d_top.toNat = topB.toNat * 2^k + carryToTop.toNat.
            obtain ⟨h_dtop_eq, _⟩ :=
              limb_shift_step topB carryToTop k hk_lb hk_le h_carry_lt
            rw [h_topB_shr_zero, Nat.zero_mul, Nat.add_zero] at h_dtop_eq
            -- kU = UInt64.ofNat k, so d_top = (topB <<< kU) ||| carryToTop.
            have h_kU_eq : kU = UInt64.ofNat k := rfl
            -- d_top.toNat = topB.toNat * 2^k + carryToTop.toNat.
            have h_dtop_val : d_top.toNat = topB.toNat * 2 ^ k + carryToTop.toNat := by
              have : d_top = (topB <<< UInt64.ofNat k) ||| carryToTop := by
                rw [hd_top_def, h_kU_eq]
              rw [this]
              exact h_dtop_eq
            -- VBuf.toList = VBufRaw.toList.take (n-1) ++ [d_top]
            -- (from Array.toList_set decomposition).
            have h_n_minus_1_lt : n - 1 < VBufRaw.toList.length := by
              rw [h_VBufRaw_len]; omega
            have h_VBufRaw_drop_eq :
                VBufRaw.toList.drop (n - 1)
                  = [VBufRaw.toList[n - 1]'h_n_minus_1_lt] := by
              rw [List.drop_eq_getElem_cons h_n_minus_1_lt]
              congr 1
              exact List.drop_of_length_le (by rw [h_VBufRaw_len]; omega)
            have h_VBufRaw_split :
                VBufRaw.toList
                  = VBufRaw.toList.take (n - 1)
                    ++ [VBufRaw.toList[n - 1]'h_n_minus_1_lt] := by
              conv_lhs =>
                rw [← List.take_append_drop (n - 1) VBufRaw.toList, h_VBufRaw_drop_eq]
            have h_VBuf_toList :
                VBuf.toList = VBufRaw.toList.take (n - 1) ++ [d_top] := by
              show (VBufRaw.set (n - 1) d_top h_top_in_raw).toList = _
              rw [Array.toList_set]
              conv_lhs => rw [h_VBufRaw_split]
              rw [List.set_append_right _ _
                    (by rw [List.length_take, h_VBufRaw_len]; omega)]
              congr 1
              rw [show (n - 1) - (VBufRaw.toList.take (n - 1)).length = 0
                    from by rw [List.length_take, h_VBufRaw_len]; omega]
              rfl
            -- toNatLimbsList of VBuf.toList.
            rw [h_VBuf_toList, toNatLimbsList_append]
            have h_take_len :
                (VBufRaw.toList.take (n - 1)).length = n - 1 := by
              rw [List.length_take]; omega
            rw [h_take_len]
            have h_dtop_singleton : toNatLimbsList [d_top] = d_top.toNat := by
              simp [toNatLimbsList]
            rw [h_dtop_singleton]
            -- V.toNat splits as topB.toNat * 2^(64*(n-1)) + V_take.
            have hV_split :
                V.toNat
                  = topB.toNat * 2 ^ (64 * (n - 1))
                    + toNatLimbsList (V.limbs.toList.take (n - 1)) := by
              show toNatLimbsList V.limbs.toList = _
              have h_V_len : V.limbs.toList.length = n := rfl
              have h_n_lt_V : n - 1 < V.limbs.toList.length := by
                rw [h_V_len]; omega
              have h_V_drop_eq :
                  V.limbs.toList.drop (n - 1)
                    = [V.limbs.toList[n - 1]'h_n_lt_V] := by
                rw [List.drop_eq_getElem_cons h_n_lt_V]
                congr 1
                exact List.drop_of_length_le (by rw [h_V_len]; omega)
              conv_lhs =>
                rw [← List.take_append_drop (n - 1) V.limbs.toList, h_V_drop_eq]
              rw [toNatLimbsList_append]
              have h_take_len_V :
                  (V.limbs.toList.take (n - 1)).length = n - 1 := by
                rw [List.length_take]; omega
              rw [h_take_len_V]
              have h_singleton :
                  toNatLimbsList [V.limbs.toList[n - 1]'h_n_lt_V] = topB.toNat := by
                rw [show V.limbs.toList[n - 1]'h_n_lt_V
                        = V.limbs[n - 1]'h_top_lt
                    from (Array.getElem_toList _).symm,
                    ← htopB_def]
                simp [toNatLimbsList]
              rw [h_singleton]
            -- shiftLimbsLeft_toNat for the bottom n-1 limbs.
            have h_shift :=
              shiftLimbsLeft_toNat V.limbs 0 (n - 1) k
                (by omega) (by omega) hk_lb hk_le
            simp only [List.drop_zero, Nat.sub_zero] at h_shift
            rw [← h_VBufRaw_eq] at h_shift
            -- carry from shiftLimbsLeft = V.limbs[n-2] >>> (64-k).
            have h_carry_shift_eq :
                (shiftLimbsLeft V.limbs 0 (n - 1) k (by omega) (by omega)
                  hk_lb hk_le).2
                  = V.limbs[(n - 1) - 1]'(by omega)
                      >>> UInt64.ofNat (64 - k) := by
              apply shiftLimbsLeft_carry_eq; omega
            have h_n2_idx_eq :
                V.limbs[(n - 1) - 1]'(by omega) = V.limbs[n - 2]'h_n2_lt := by
              congr 1
            rw [h_carry_shift_eq, h_n2_idx_eq, ← h_carryToTop_eq] at h_shift
            -- h_shift: toNatLimbsList (VBufRaw.toList.take (n-1))
            --        + carryToTop.toNat * 2^(64*(n-1))
            --        = toNatLimbsList (V.limbs.toList.take (n-1)) * 2^k.
            -- Algebra: goal is
            --   d_top.toNat * 2^(64*(n-1)) + toNatLimbsList (VBufRaw.toList.take (n-1))
            --   = (topB.toNat * 2^(64*(n-1)) + V_take) * 2^k.
            set V_take := toNatLimbsList (V.limbs.toList.take (n - 1)) with hV_take_def
            set bot := toNatLimbsList (VBufRaw.toList.take (n - 1)) with hbot_def
            set ctop : Nat := carryToTop.toNat with hctop_def
            -- h_shift : bot + ctop * 2^(64*(n-1)) = V_take * 2^k.
            -- h_dtop_val : d_top.toNat = topB.toNat * 2^k + ctop.
            -- hV_split : V.toNat = topB.toNat * 2^(64*(n-1)) + V_take.
            -- Goal: d_top.toNat * 2^(64*(n-1)) + bot = V.toNat * 2^k.
            have h_le : ctop * 2 ^ (64 * (n - 1)) ≤ V_take * 2 ^ k := by omega
            have h_bot_eq :
                bot
                  = V_take * 2 ^ k - ctop * 2 ^ (64 * (n - 1)) := by omega
            rw [h_bot_eq, h_dtop_val, hV_split]
            have h_add_sub :
                (topB.toNat * 2 ^ k + ctop) * 2 ^ (64 * (n - 1))
                    + (V_take * 2 ^ k - ctop * 2 ^ (64 * (n - 1)))
                  = topB.toNat * 2 ^ k * 2 ^ (64 * (n - 1)) + V_take * 2 ^ k := by
              have h_expand :
                  (topB.toNat * 2 ^ k + ctop) * 2 ^ (64 * (n - 1))
                    = topB.toNat * 2 ^ k * 2 ^ (64 * (n - 1))
                      + ctop * 2 ^ (64 * (n - 1)) := by ring
              rw [h_expand]
              omega
            rw [h_add_sub]
            ring
        -- Now rephrase div_eq using the buffer-value facts.
        rw [h_UBuf_toNat, h_VBuf_toNat] at h_div_eq
        -- h_div_eq :
        --   U.toNat * 2^k =
        --   (res.2.toNat * 2^(64*m) + Q') * (V.toNat * 2^k) + R
        -- Set Q = (res.2.toNat * 2^(64*m) + Q'), the full quotient value.
        set Q_val : Nat := res.2.toNat * 2 ^ (64 * m) + Q' with hQ_val_def
        -- Express ofLimbs(extract 0 n).toNat = R.
        have h_extract_R : (ofLimbs (res.1.extract 0 n)).toNat = R := by
          rw [toNat_ofLimbs, Array.toList_extract, List.extract_eq_take_drop]
          show toNatLimbsList ((res.1.toList.drop 0).take (n - 0)) = _
          rw [List.drop_zero, Nat.sub_zero, hR_def]
          rfl
        -- Express ofLimbs(extract n (n+m) ++ #[res.2]).toNat = Q_val.
        have h_extract_Q' :
            (res.1.extract n (n + m)).toList = (res.1.toList.drop n).take m := by
          rw [Array.toList_extract, List.extract_eq_take_drop]
          show (res.1.toList.drop n).take (n + m - n) = _
          rw [Nat.add_sub_cancel_left]
        have h_extract_Q :
            (ofLimbs (res.1.extract n (n + m) ++ #[res.2])).toNat = Q_val := by
          rw [toNat_ofLimbs, Array.toList_append, h_extract_Q']
          show toNatLimbsList ((res.1.toList.drop n).take m ++ [res.2]) = _
          rw [toNatLimbsList_append]
          have h_take_len : ((res.1.toList.drop n).take m).length = m := by
            rw [List.length_take, List.length_drop, h_res_len]; omega
          rw [h_take_len]
          show toNatLimbsList [res.2] * 2 ^ (64 * m) + Q' = _
          have h_sing : toNatLimbsList [res.2] = res.2.toNat := by simp [toNatLimbsList]
          rw [h_sing, hQ'_def]
        -- Algebra: U * 2^k = Q_val * (V * 2^k) + R.
        have h_2k_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
        -- Q_val * V ≤ U (otherwise the LHS exceeds U * 2^k).
        have h_QV_le : Q_val * V.toNat ≤ U.toNat := by
          have h_le_2k : Q_val * V.toNat * 2 ^ k ≤ U.toNat * 2 ^ k := by
            have h_assoc : Q_val * V.toNat * 2 ^ k = Q_val * (V.toNat * 2 ^ k) := by ring
            rw [h_assoc]; linarith [h_div_eq]
          exact Nat.le_of_mul_le_mul_right h_le_2k h_2k_pos
        -- R = (U - Q_val * V) * 2^k.
        have h_R_eq : R = (U.toNat - Q_val * V.toNat) * 2 ^ k := by
          have h_assoc : Q_val * (V.toNat * 2 ^ k) = Q_val * V.toNat * 2 ^ k := by ring
          rw [h_assoc] at h_div_eq
          have h_sub : (U.toNat - Q_val * V.toNat) * 2 ^ k
                      = U.toNat * 2 ^ k - Q_val * V.toNat * 2 ^ k :=
            Nat.sub_mul _ _ _
          omega
        -- Now connect rem_lt (R < V*2^k) to (remNorm >>> k) < V.
        -- rem_lt : R < V.toNat * 2^k
        rw [h_VBuf_toNat] at h_rem_lt
        -- (ofLimbs (res.1.extract 0 n) >>> k).toNat = R / 2^k.
        have h_shr : (ofLimbs (res.1.extract 0 n) >>> k).toNat
                    = (ofLimbs (res.1.extract 0 n)).toNat / 2 ^ k := by
          rw [hShiftRight_eq, toNat_shiftRight]
        show (ofLimbs (res.1.extract n (n + m) ++ #[res.2])).toNat * V.toNat
              + (ofLimbs (res.1.extract 0 n) >>> k).toNat = U.toNat
            ∧ (V.toNat ≠ 0 →
              (ofLimbs (res.1.extract 0 n) >>> k).toNat < V.toNat)
        rw [h_extract_Q, h_shr, h_extract_R, h_R_eq,
            Nat.mul_div_cancel _ h_2k_pos]
        refine ⟨?_, ?_⟩
        · -- Q_val * V + (U - Q_val * V) = U.
          omega
        · -- (U - Q_val * V) < V.
          intro _
          have h_lt' : (U.toNat - Q_val * V.toNat) * 2 ^ k < V.toNat * 2 ^ k := by
            rw [← h_R_eq]; exact h_rem_lt
          exact Nat.lt_of_mul_lt_mul_right h_lt'

end Azurite.AzNat
