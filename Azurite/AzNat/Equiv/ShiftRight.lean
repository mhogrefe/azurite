import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.ShiftLeft

namespace Azurite.AzNat

/-- Popping a trailing zero limb preserves the numeric value. -/
private lemma toNatLimbsList_dropLast_of_getLast?_zero (l : List UInt64)
    (h : l.getLast? = some 0) : toNatLimbsList l.dropLast = toNatLimbsList l := by
  have h_ne : l ≠ [] := by
    intro heq; rw [heq] at h; simp at h
  have h_last : l.getLast h_ne = 0 := by
    rw [List.getLast?_eq_some_getLast h_ne] at h
    exact Option.some.inj h
  have h_split : l.dropLast ++ [l.getLast h_ne] = l :=
    List.dropLast_append_getLast h_ne
  have h_app := toNatLimbsList_append l.dropLast [l.getLast h_ne]
  rw [h_split, h_last] at h_app
  rw [h_app]
  simp [toNatLimbsList]

/-- `trimTrailingZeros` preserves the numeric value. -/
theorem toNatLimbsList_trimTrailingZeros (a : Array UInt64) :
    toNatLimbsList (trimTrailingZeros a).toList = toNatLimbsList a.toList := by
  rw [trimTrailingZeros]
  by_cases h : a.size = 0
  · simp only [h, ↓reduceDIte]
  · simp only [h, ↓reduceDIte]
    have h_idx : a.size - 1 < a.size :=
      Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one
    by_cases h_last : a[a.size - 1] = 0
    · rw [if_pos h_last]
      rw [toNatLimbsList_trimTrailingZeros a.pop]
      rw [Array.toList_pop]
      apply toNatLimbsList_dropLast_of_getLast?_zero
      rw [Array.getLast?_toList, Array.back?_eq_getElem?,
          Array.getElem?_eq_getElem h_idx, h_last]
    · rw [if_neg h_last]
  termination_by a.size
  decreasing_by simp [Array.size_pop]; omega

/-- `toNat` of `ofLimbs` equals `toNatLimbsList` of the input array. -/
theorem toNat_ofLimbs (a : Array UInt64) :
    (ofLimbs a).toNat = toNatLimbsList a.toList := by
  show toNatLimbsList (trimTrailingZeros a).toList = _
  exact toNatLimbsList_trimTrailingZeros a

/-- Dropping the first `k` limbs corresponds to dividing by `2 ^ (64 * k)`. -/
theorem toNatLimbsList_drop (l : List UInt64) (k : Nat) :
    toNatLimbsList (l.drop k) = toNatLimbsList l / 2 ^ (64 * k) := by
  by_cases hk : k ≤ l.length
  · have h_take_len : (l.take k).length = k := by rw [List.length_take]; omega
    have h_app := toNatLimbsList_append (l.take k) (l.drop k)
    rw [List.take_append_drop, h_take_len] at h_app
    have h_take_lt : toNatLimbsList (l.take k) < 2 ^ (64 * k) := by
      have := toNatLimbsList_lt_pow (l.take k)
      rw [h_take_len] at this
      exact this
    rw [h_app, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (64 * k)),
        Nat.div_eq_of_lt h_take_lt, Nat.zero_add]
  · have hkl : l.length ≤ k := by omega
    rw [List.drop_eq_nil_of_le hkl]
    have h_lt : toNatLimbsList l < 2 ^ (64 * k) :=
      lt_of_lt_of_le (toNatLimbsList_lt_pow l)
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt h_lt]
    rfl

/-- `Array.extract k size` corresponds to `List.drop k` on `toList`. -/
theorem toNatLimbsList_extract_size (a : Array UInt64) (k : Nat) :
    toNatLimbsList (a.extract k a.size).toList = toNatLimbsList a.toList / 2 ^ (64 * k) := by
  rw [Array.toList_extract, List.extract_eq_take_drop]
  have h_len : a.toList.length = a.size := rfl
  rw [List.take_of_length_le (by rw [List.length_drop, h_len])]
  rw [toNatLimbsList_drop]

/-- `shiftRightMul64 a k` represents `a.toNat / 2 ^ (64 * k)`. -/
theorem toNat_shiftRightMul64 (a : AzNat) (k : Nat) :
    (shiftRightMul64 a k).toNat = a.toNat / 2 ^ (64 * k) := by
  show toNatLimbsList (shiftRightMul64 a k).limbs.toList = _
  show toNatLimbsList (ofLimbs (a.limbs.extract k a.limbs.size)).limbs.toList = _
  show toNatLimbsList (trimTrailingZeros (a.limbs.extract k a.limbs.size)).toList = _
  rw [toNatLimbsList_trimTrailingZeros]
  exact toNatLimbsList_extract_size a.limbs k

/-- Computing a single limb of the right-shift.  Given incoming carry aligned
    to the top `sh` bits (i.e. its low `64-sh` bits are zero), the new limb is
    `(x >>> sh) + carry` and the new carry `x <<< (64-sh)` captures the bits
    that fell off the bottom of `x`, placed in its top `sh` bits. -/
private lemma limb_shift_right_step (x carry : UInt64) (sh : Nat)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63)
    (hcarry : 2 ^ (64 - sh) ∣ carry.toNat) :
    (x <<< UInt64.ofNat (64 - sh)).toNat
        + ((x >>> UInt64.ofNat sh) ||| carry).toNat * 2 ^ 64
      = x.toNat * 2 ^ (64 - sh) + carry.toNat * 2 ^ 64
    ∧ 2 ^ (64 - sh) ∣ (x <<< UInt64.ofNat (64 - sh)).toNat := by
  have hsh'_lb : 1 ≤ 64 - sh := by omega
  have hsh'_ub : 64 - sh ≤ 63 := by omega
  have h_zero_lt : (0 : UInt64).toNat < 2 ^ (64 - sh) := Nat.two_pow_pos _
  -- Reuse `limb_shift_step` with shift amount `64 - sh` and zero carry.
  obtain ⟨h_eq0, h_shr_lt⟩ := limb_shift_step x 0 (64 - sh) hsh'_lb hsh'_ub h_zero_lt
  have h_sh_eq : 64 - (64 - sh) = sh := by omega
  rw [h_sh_eq] at h_eq0 h_shr_lt
  have h_or_zero : ((x <<< UInt64.ofNat (64 - sh)) ||| 0).toNat
                    = (x <<< UInt64.ofNat (64 - sh)).toNat := by
    rw [UInt64.toNat_or]
    show _ ||| 0 = _
    exact Nat.or_zero _
  rw [h_or_zero, show (0 : UInt64).toNat = 0 from rfl, Nat.add_zero] at h_eq0
  -- h_eq0 : (x <<< (64-sh)).toNat + (x >>> sh).toNat * 2^64 = x.toNat * 2^(64-sh)
  obtain ⟨q, hq⟩ := hcarry
  -- Disjoint-OR: (x >>> sh) has low (64-sh) bits only; carry has high sh bits only.
  have h_shr_lt' : (x >>> UInt64.ofNat sh).toNat < 2 ^ (64 - sh) := h_shr_lt
  have h_or_add : ((x >>> UInt64.ofNat sh) ||| carry).toNat
                  = (x >>> UInt64.ofNat sh).toNat + carry.toNat := by
    rw [UInt64.toNat_or]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, hq]
    rw [show (x >>> UInt64.ofNat sh).toNat + 2 ^ (64 - sh) * q
          = 2 ^ (64 - sh) * q + (x >>> UInt64.ofNat sh).toNat from Nat.add_comm _ _]
    rw [Nat.testBit_two_pow_mul_add _ h_shr_lt', Nat.testBit_two_pow_mul]
    by_cases hj : j < 64 - sh
    · simp [hj, show ¬(j ≥ 64 - sh) from by omega]
    · have h_shr_bit : (x >>> UInt64.ofNat sh).toNat.testBit j = false :=
        Nat.testBit_lt_two_pow
          (lt_of_lt_of_le h_shr_lt' (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [h_shr_bit]
      simp [hj, show j ≥ 64 - sh from by omega]
  refine ⟨?_, ?_⟩
  · rw [h_or_add]
    have h_algebra : (x <<< UInt64.ofNat (64 - sh)).toNat
            + ((x >>> UInt64.ofNat sh).toNat + (2 ^ (64 - sh) * q)) * 2 ^ 64
          = ((x <<< UInt64.ofNat (64 - sh)).toNat
              + (x >>> UInt64.ofNat sh).toNat * 2 ^ 64) + (2 ^ (64 - sh) * q) * 2 ^ 64 := by
      ring
    rw [hq, h_algebra, h_eq0]
  · -- `(x <<< (64-sh)).toNat` is a multiple of `2^(64-sh)`.
    have h_ofNat' : (UInt64.ofNat (64 - sh)).toNat = 64 - sh := by
      show (64 - sh) % 2 ^ 64 = 64 - sh
      exact Nat.mod_eq_of_lt (by omega)
    have h_sub_mod : (64 - sh) % 64 = 64 - sh := Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_shiftLeft, h_ofNat', h_sub_mod, Nat.shiftLeft_eq]
    have h_pow64 : (2 : Nat) ^ 64 = 2 ^ sh * 2 ^ (64 - sh) := by
      rw [← Nat.pow_add]; congr 1; omega
    refine ⟨x.toNat % 2 ^ sh, ?_⟩
    rw [h_pow64, Nat.mul_mod_mul_right, Nat.mul_comm]

/-- `shiftLimbsRightAux lo sh a i carry` leaves positions `≥ i` unchanged. -/
private lemma shiftLimbsRightAux_preserves_ge (lo sh : Nat)
    (a : Array UInt64) (i : Nat) (carry : UInt64) (h_i : i ≤ a.size)
    (j : Nat) (hij : i ≤ j) :
    ∀ (hj_new : j < (shiftLimbsRightAux lo sh a i carry h_i).1.size)
      (hj_old : j < a.size),
      (shiftLimbsRightAux lo sh a i carry h_i).1[j]'hj_new = a[j]'hj_old := by
  induction i using Nat.strong_induction_on generalizing a carry with
  | _ i ih =>
    intro hj_new hj_old
    unfold shiftLimbsRightAux
    by_cases hlt : lo < i
    · simp only [hlt, dif_pos]
      have h_dec : i - 1 < i := Nat.sub_lt (by omega) Nat.zero_lt_one
      have hij' : i - 1 ≤ j := by omega
      have h_ne : j ≠ i - 1 := by omega
      have h_inner := ih (i - 1) h_dec
                        (a.set (i - 1) ((a[i - 1] >>> UInt64.ofNat sh) ||| carry))
                        (a[i - 1] <<< UInt64.ofNat (64 - sh))
                        (by rw [Array.size_set]; omega) hij'
      have hj_set : j < (a.set (i - 1) ((a[i - 1] >>> UInt64.ofNat sh) ||| carry)).size := by
        rw [Array.size_set]; exact hj_old
      rw [h_inner _ hj_set]
      exact Array.getElem_set_ne _ _ h_ne.symm
    · simp [hlt]

/-- Peeling the last limb of a `take` slice, written additively. -/
private lemma toNatLimbsList_take_succ_last (a : Array UInt64) (lo i : Nat)
    (h : i - 1 < a.size) (hlo : lo + 1 ≤ i) :
    toNatLimbsList ((a.toList.drop lo).take (i - lo))
      = toNatLimbsList ((a.toList.drop lo).take ((i - 1) - lo))
        + a[i - 1].toNat * 2 ^ (64 * ((i - 1) - lo)) := by
  have h_len : a.toList.length = a.size := rfl
  -- i - lo = ((i - 1) - lo) + 1
  have h_len_sub : i - lo = ((i - 1) - lo) + 1 := by omega
  -- The (i-lo)-th taken element, i.e. the last one, is at position i-1 of the list.
  have h_drop_len : (a.toList.drop lo).length = a.size - lo := by
    rw [List.length_drop, h_len]
  have h_take_lt : (i - 1) - lo < (a.toList.drop lo).length := by
    rw [h_drop_len]; omega
  have h_idx_lt : lo + ((i - 1) - lo) < a.toList.length := by
    rw [h_len]; omega
  rw [h_len_sub]
  -- Split the take using take_succ and List.getElem? drop lo get = getElem at (lo + ...).
  rw [List.take_add_one]
  have h_get :
      (a.toList.drop lo)[(i - 1) - lo]?
        = some (a[i - 1]) := by
    rw [List.getElem?_eq_getElem h_take_lt]
    rw [List.getElem_drop]
    show some (a.toList[lo + ((i - 1) - lo)]'_) = some a[i - 1]
    congr 1
    rw [Array.getElem_toList (h := by omega)]
    congr 1
    omega
  rw [h_get, Option.toList]
  -- toNatLimbsList (xs ++ [x]) = toNatLimbsList xs + x * 2 ^ (64 * xs.length)
  rw [toNatLimbsList_append]
  have h_take_len : ((a.toList.drop lo).take ((i - 1) - lo)).length = (i - 1) - lo := by
    rw [List.length_take, h_drop_len]; omega
  rw [h_take_len]
  have h_single : toNatLimbsList [a[i - 1]] = a[i - 1].toNat := by
    unfold toNatLimbsList; simp
  rw [h_single]
  ring

/-- Invariant of `shiftLimbsRightAux`: starting from state `(a, i, carry)`,
    the result's slice `[lo, i)` plus the final carry equals the original
    slice shifted right by `sh` bits. -/
private lemma shiftLimbsRightAux_correct (lo sh : Nat)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63)
    (a : Array UInt64) (i : Nat) (carry : UInt64) (h_i : i ≤ a.size)
    (hlo : lo ≤ i) (hcarry : 2 ^ (64 - sh) ∣ carry.toNat) :
    toNatLimbsList (((shiftLimbsRightAux lo sh a i carry h_i).1.toList.drop lo).take (i - lo))
        * 2 ^ 64 + (shiftLimbsRightAux lo sh a i carry h_i).2.toNat
      = toNatLimbsList ((a.toList.drop lo).take (i - lo)) * 2 ^ (64 - sh)
        + carry.toNat * 2 ^ (64 * (i - lo)) := by
  induction i_sub_lo : i - lo generalizing a i carry with
  | zero =>
    have h_le : i ≤ lo := by omega
    have h_i_eq : i = lo := Nat.le_antisymm h_le hlo
    have h_eq : shiftLimbsRightAux lo sh a i carry h_i = (a, carry) := by
      conv_lhs => rw [shiftLimbsRightAux]
      simp [h_i_eq]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : lo < i := by omega
    have h_im1_lt : i - 1 < a.size := by
      have : i - 1 < i := Nat.sub_lt (by omega) Nat.zero_lt_one
      omega
    set x := a[i - 1] with hx_def
    set newCarry := x <<< UInt64.ofNat (64 - sh) with hnc_def
    set newVal := (x >>> UInt64.ofNat sh) ||| carry with hnv_def
    set a' := a.set (i - 1) newVal with ha'_def
    have h_size' : i - 1 ≤ a'.size := by rw [ha'_def, Array.size_set]; omega
    have h_eq : shiftLimbsRightAux lo sh a i carry h_i
                = shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size' := by
      conv_lhs => rw [shiftLimbsRightAux]
      simp [h_lt, hx_def, hnc_def, hnv_def, ha'_def]
    -- Single-limb identity
    obtain ⟨h_limb_eq, h_newCarry_dvd⟩ :=
      limb_shift_right_step x carry sh hsh_lb hsh_ub hcarry
    -- Apply inductive hypothesis
    have h_rec : (i - 1) - lo = n := by omega
    have hlo' : lo ≤ i - 1 := by omega
    have h_ih := ih a' (i - 1) newCarry h_size' hlo' h_newCarry_dvd h_rec
    rw [h_eq]
    -- Need: the result at position i-1 is newVal (recursion only touches lo..i-2)
    -- This uses that shiftLimbsRightAux leaves positions ≥ i untouched.
    have h_res_size :
        (shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').1.size = a'.size :=
      shiftLimbsRightAux_size lo sh a' (i - 1) newCarry h_size'
    have h_res_size_eq :
        (shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').1.size = a.size := by
      rw [h_res_size, ha'_def, Array.size_set]
    -- The full slice ((result.drop lo).take (i-lo)) splits as
    --   ((result.drop lo).take ((i-1)-lo)) ++ [result[i-1]].
    have h_res_i_size :
        i - 1 < (shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').1.size := by
      rw [h_res_size_eq]; exact h_im1_lt
    have h_idx_a' : i - 1 < a'.size := by rw [ha'_def, Array.size_set]; exact h_im1_lt
    have h_a'_i : a'[i - 1]'h_idx_a' = newVal := by
      show (a.set (i - 1) newVal h_im1_lt)[i - 1]'_ = newVal
      exact Array.getElem_set_self ..
    have h_prev :=
      shiftLimbsRightAux_preserves_ge lo sh a' (i - 1) newCarry h_size'
        (i - 1) (Nat.le_refl _) h_res_i_size h_idx_a'
    have h_res_i :
        (shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').1[i - 1]'h_res_i_size
          = newVal := h_prev.trans h_a'_i
    -- Split target using toNatLimbsList_take_succ_last on both sides.
    rw [show (n + 1) = i - lo from i_sub_lo.symm]
    rw [toNatLimbsList_take_succ_last
          (shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').1 lo i h_res_i_size
          (by omega)]
    rw [toNatLimbsList_take_succ_last a lo i h_im1_lt (by omega)]
    -- Rewrite result[i-1] to newVal.
    rw [h_res_i]
    -- a'.toList.drop lo ... take (i-1-lo) equals a.toList.drop lo ... take (i-1-lo)
    have h_drop_take_a' :
        (a'.toList.drop lo).take ((i - 1) - lo)
          = (a.toList.drop lo).take ((i - 1) - lo) := by
      rw [ha'_def, Array.toList_set, List.drop_set]
      rw [if_neg (by omega : ¬ i - 1 < lo)]
      rw [List.take_set]
      rw [List.set_eq_of_length_le (by
        rw [List.length_take, List.length_drop]
        have : a.toList.length = a.size := rfl
        omega)]
    -- Rewrite 2 ^ (64 * (i - lo)) = 2 ^ (64 * ((i-1) - lo)) * 2 ^ 64
    have h_pow : (2 : Nat) ^ (64 * (i - lo))
                = 2 ^ (64 * ((i - 1) - lo)) * 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h_pow]
    -- Denote and apply IH (with its `a'` drop-take replaced by the `a` form).
    set P := toNatLimbsList
      (((shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').1.toList.drop lo).take ((i - 1) - lo))
      with hP_def
    set Q := toNatLimbsList ((a.toList.drop lo).take ((i - 1) - lo)) with hQ_def
    set R := (shiftLimbsRightAux lo sh a' (i - 1) newCarry h_size').2.toNat with hR_def
    have h_ih' : P * 2 ^ 64 + R
                = Q * 2 ^ (64 - sh) + newCarry.toNat * 2 ^ (64 * ((i - 1) - lo)) := by
      have h := ih a' (i - 1) newCarry h_size' hlo' h_newCarry_dvd h_rec
      rw [← h_rec] at h
      rw [h_drop_take_a'] at h
      exact h
    -- Algebra: combine IH with the single-limb identity h_limb_eq.
    have h_lhs :
        (Q + x.toNat * 2 ^ (64 * ((i - 1) - lo))) * 2 ^ (64 - sh)
          + carry.toNat * (2 ^ (64 * ((i - 1) - lo)) * 2 ^ 64)
        = Q * 2 ^ (64 - sh)
            + (x.toNat * 2 ^ (64 - sh) + carry.toNat * 2 ^ 64)
              * 2 ^ (64 * ((i - 1) - lo)) := by ring
    rw [h_lhs, ← h_limb_eq]
    have h_rhs :
        (P + newVal.toNat * 2 ^ (64 * ((i - 1) - lo))) * 2 ^ 64 + R
        = (P * 2 ^ 64 + R) + newVal.toNat * 2 ^ 64 * 2 ^ (64 * ((i - 1) - lo)) := by ring
    rw [h_rhs, h_ih']
    ring

/-- `shiftLimbsRightAux lo sh a i carry` leaves positions `< lo` unchanged. -/
private lemma shiftLimbsRightAux_preserves_lt (lo sh : Nat)
    (a : Array UInt64) (i : Nat) (carry : UInt64) (h_i : i ≤ a.size)
    (j : Nat) (hj : j < lo) :
    ∀ (hj_new : j < (shiftLimbsRightAux lo sh a i carry h_i).1.size)
      (hj_old : j < a.size),
      (shiftLimbsRightAux lo sh a i carry h_i).1[j]'hj_new = a[j]'hj_old := by
  induction i using Nat.strong_induction_on generalizing a carry with
  | _ i ih =>
    intro hj_new hj_old
    unfold shiftLimbsRightAux
    by_cases hlt : lo < i
    · simp only [hlt, dif_pos]
      have h_dec : i - 1 < i := Nat.sub_lt (by omega) Nat.zero_lt_one
      have h_ne : j ≠ i - 1 := by omega
      have h_inner := ih (i - 1) h_dec
                        (a.set (i - 1) ((a[i - 1] >>> UInt64.ofNat sh) ||| carry))
                        (a[i - 1] <<< UInt64.ofNat (64 - sh))
                        (by rw [Array.size_set]; omega)
      have hj_set : j < (a.set (i - 1) ((a[i - 1] >>> UInt64.ofNat sh) ||| carry)).size := by
        rw [Array.size_set]; exact hj_old
      rw [h_inner _ hj_set]
      exact Array.getElem_set_ne _ _ h_ne.symm
    · simp [hlt]

/-- Correctness of `shiftLimbsRight`: the modified limbs `[lo, hi)` times `2^64` plus the
    returned carry represents the original slice shifted right by `sh` bits (times `2^(64-sh)`). -/
theorem shiftLimbsRight_toNat (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    let (a', carry) := shiftLimbsRight a lo hi sh hlo hhi hsh_lb hsh_ub
    toNatLimbsList ((a'.toList.drop lo).take (hi - lo)) * 2 ^ 64
        + carry.toNat
      = toNatLimbsList ((a.toList.drop lo).take (hi - lo)) * 2 ^ (64 - sh) := by
  have hcarry : 2 ^ (64 - sh) ∣ (0 : UInt64).toNat := by
    show 2 ^ (64 - sh) ∣ 0
    exact dvd_zero _
  have h := shiftLimbsRightAux_correct lo sh hsh_lb hsh_ub a hi 0 hhi hlo hcarry
  simp at h
  exact h

/-- `shiftLimbsRight` leaves the prefix `[0, lo)` unchanged. -/
theorem shiftLimbsRight_toList_take (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    (shiftLimbsRight a lo hi sh hlo hhi hsh_lb hsh_ub).1.toList.take lo
      = a.toList.take lo := by
  have h_size := shiftLimbsRight_size a lo hi sh hlo hhi hsh_lb hsh_ub
  apply List.ext_getElem
  · rw [List.length_take, List.length_take]
    show min lo (shiftLimbsRight _ _ _ _ _ _ _ _).1.size = min lo a.size
    rw [h_size]
  · intro j hj_new _
    rw [List.length_take] at hj_new
    have hj : j < lo := by
      have : j < min lo _ := hj_new
      omega
    have h_j_a : j < a.size := by
      have : j < lo := hj
      omega
    have h_j_res : j < (shiftLimbsRight a lo hi sh hlo hhi hsh_lb hsh_ub).1.size := by
      rw [h_size]; exact h_j_a
    rw [List.getElem_take, List.getElem_take]
    rw [show a.toList[j]'(by exact h_j_a) = a[j]'h_j_a from (Array.getElem_toList _).symm]
    rw [show (shiftLimbsRight a lo hi sh hlo hhi hsh_lb hsh_ub).1.toList[j]'(by exact h_j_res)
          = (shiftLimbsRight a lo hi sh hlo hhi hsh_lb hsh_ub).1[j]'h_j_res from
            (Array.getElem_toList _).symm]
    exact shiftLimbsRightAux_preserves_lt lo sh a hi 0 hhi j hj _ _

/-- Correctness of `shiftRightGeneralLimbs`. -/
theorem toNat_shiftRightGeneralLimbs (a : AzNat) (sh : Nat)
    (hsm : ¬ sh % 64 = 0) :
    (shiftRightGeneralLimbs a sh hsm).toNat = a.toNat / 2 ^ sh := by
  unfold shiftRightGeneralLimbs
  have hsh_lb : 1 ≤ sh % 64 := by omega
  have hsh_ub : sh % 64 ≤ 63 := by
    have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
    omega
  by_cases h : sh / 64 ≥ a.limbs.size
  · rw [dif_pos h]
    have h_a_lt : a.toNat < 2 ^ sh := by
      have h1 : a.toNat < 2 ^ (64 * a.limbs.size) := by
        have := toNatLimbsList_lt_pow a.limbs.toList
        have h_len : a.limbs.toList.length = a.limbs.size := rfl
        rw [h_len] at this
        exact this
      have h2 : 64 * a.limbs.size ≤ sh := by
        have h_sh_eq : sh = 64 * (sh / 64) + sh % 64 := (Nat.div_add_mod sh 64).symm
        omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)
    show (0 : AzNat).toNat = a.toNat / 2 ^ sh
    rw [Nat.div_eq_of_lt h_a_lt]
    rfl
  · rw [dif_neg h]
    -- Setup: bigShift, smallShift, shifted, carry
    set bigShift := sh / 64 with hbs
    set smallShift := sh % 64 with hss
    set shifted := (shiftLimbsRight a.limbs bigShift a.limbs.size smallShift
      (by omega) (Nat.le_refl _) hsh_lb hsh_ub).1 with hsh_def
    set carryOut := (shiftLimbsRight a.limbs bigShift a.limbs.size smallShift
      (by omega) (Nat.le_refl _) hsh_lb hsh_ub).2 with hco_def
    have h_size : shifted.size = a.limbs.size := by
      rw [hsh_def]
      exact shiftLimbsRight_size a.limbs bigShift a.limbs.size smallShift
        (by omega) (Nat.le_refl _) hsh_lb hsh_ub
    -- Correctness of the shift.
    have h_inv : toNatLimbsList ((shifted.toList.drop bigShift).take (a.limbs.size - bigShift)) * 2 ^ 64
               + carryOut.toNat
             = toNatLimbsList ((a.limbs.toList.drop bigShift).take (a.limbs.size - bigShift)) * 2 ^ (64 - smallShift) := by
      have := shiftLimbsRight_toNat a.limbs bigShift a.limbs.size smallShift
        (by omega) (Nat.le_refl _) hsh_lb hsh_ub
      simp only at this
      exact this
    -- Simplify take.
    have h_drop_shifted_len : shifted.toList.length - bigShift = a.limbs.size - bigShift := by
      have : shifted.toList.length = shifted.size := rfl
      rw [this, h_size]
    have h_take_shifted : (shifted.toList.drop bigShift).take (a.limbs.size - bigShift)
                        = shifted.toList.drop bigShift := by
      apply List.take_of_length_le
      rw [List.length_drop, h_drop_shifted_len]
    have h_take_a : (a.limbs.toList.drop bigShift).take (a.limbs.size - bigShift)
                  = a.limbs.toList.drop bigShift := by
      apply List.take_of_length_le
      rw [List.length_drop]
      have : a.limbs.toList.length = a.limbs.size := rfl
      rw [this]
    rw [h_take_shifted, h_take_a] at h_inv
    set shifted_low := toNatLimbsList (shifted.toList.drop bigShift) with hsl_def
    set high := toNatLimbsList (a.limbs.toList.drop bigShift) with hh_def
    -- Compute the result's toNat.
    change toNatLimbsList (trimTrailingZeros (shifted.extract bigShift shifted.size)).toList
            = a.toNat / 2 ^ sh
    rw [toNatLimbsList_trimTrailingZeros]
    rw [toNatLimbsList_extract_size]
    -- Goal: toNatLimbsList shifted.toList / 2^(64*bigShift) = a.toNat / 2^sh
    -- shifted.toList = take bigShift ++ drop bigShift, and take bigShift = a.limbs.take bigShift
    have h_prefix_shifted : shifted.toList.take bigShift = a.limbs.toList.take bigShift := by
      rw [hsh_def]
      exact shiftLimbsRight_toList_take a.limbs bigShift a.limbs.size smallShift
        (by omega) (Nat.le_refl _) hsh_lb hsh_ub
    have h_shifted_split :
        toNatLimbsList shifted.toList = toNatLimbsList (a.limbs.toList.take bigShift)
                                       + shifted_low * 2 ^ (64 * bigShift) := by
      conv_lhs => rw [← List.take_append_drop bigShift shifted.toList]
      rw [toNatLimbsList_append, h_prefix_shifted]
      have h_take_len : (a.limbs.toList.take bigShift).length = bigShift := by
        rw [List.length_take]
        have : a.limbs.toList.length = a.limbs.size := rfl
        rw [this]; omega
      rw [h_take_len, Nat.add_comm]
    have h_take_lt : toNatLimbsList (a.limbs.toList.take bigShift) < 2 ^ (64 * bigShift) := by
      have := toNatLimbsList_lt_pow (a.limbs.toList.take bigShift)
      have h_take_len : (a.limbs.toList.take bigShift).length = bigShift := by
        rw [List.length_take]
        have : a.limbs.toList.length = a.limbs.size := rfl
        rw [this]; omega
      rw [h_take_len] at this
      exact this
    rw [h_shifted_split, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt h_take_lt, Nat.zero_add]
    -- Goal: shifted_low = a.toNat / 2^sh
    -- a.toNat = take bigShift + drop bigShift * 2^(64*bigShift) = low + high * 2^(64*bigShift)
    have h_a_split :
        a.toNat = toNatLimbsList (a.limbs.toList.take bigShift) + high * 2 ^ (64 * bigShift) := by
      show toNatLimbsList a.limbs.toList = _
      conv_lhs => rw [← List.take_append_drop bigShift a.limbs.toList]
      rw [toNatLimbsList_append]
      have h_take_len : (a.limbs.toList.take bigShift).length = bigShift := by
        rw [List.length_take]
        have : a.limbs.toList.length = a.limbs.size := rfl
        rw [this]; omega
      rw [h_take_len, Nat.add_comm]
    -- a.toNat / 2^sh = a.toNat / (2^(64*bigShift) * 2^smallShift) = (a.toNat / 2^(64*bigShift)) / 2^smallShift
    have h_sh_eq : sh = 64 * bigShift + smallShift := (Nat.div_add_mod sh 64).symm
    have h_pow_sh : (2 : Nat) ^ sh = 2 ^ (64 * bigShift) * 2 ^ smallShift := by
      rw [h_sh_eq, Nat.pow_add]
    rw [h_pow_sh, ← Nat.div_div_eq_div_mul]
    -- Goal: shifted_low = a.toNat / 2^(64*bigShift) / 2^smallShift
    rw [h_a_split, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt h_take_lt, Nat.zero_add]
    -- Goal: shifted_low = high / 2^smallShift
    -- Use h_inv: shifted_low * 2^64 + carryOut.toNat = high * 2^(64-smallShift)
    -- Divide by 2^64 (noting carryOut.toNat < 2^64):
    have h_carry_lt : carryOut.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have h_lhs_div : (shifted_low * 2 ^ 64 + carryOut.toNat) / 2 ^ 64 = shifted_low := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt h_carry_lt, Nat.zero_add]
    have h_pow_split : (2 : Nat) ^ 64 = 2 ^ smallShift * 2 ^ (64 - smallShift) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h_rhs_div : high * 2 ^ (64 - smallShift) / 2 ^ 64 = high / 2 ^ smallShift := by
      rw [h_pow_split, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]
    calc shifted_low
        = (shifted_low * 2 ^ 64 + carryOut.toNat) / 2 ^ 64 := h_lhs_div.symm
      _ = high * 2 ^ (64 - smallShift) / 2 ^ 64 := by rw [h_inv]
      _ = high / 2 ^ smallShift := h_rhs_div

/-- Correctness of `shiftRight`: `toNat (a >>> sh) = a.toNat / 2 ^ sh`. -/
theorem toNat_shiftRight (a : AzNat) (sh : Nat) :
    (shiftRight a sh).toNat = a.toNat / 2 ^ sh := by
  unfold shiftRight
  by_cases hz : a.limbs.size = 0
  · rw [if_pos hz]
    have h_nil : a.limbs.toList = [] := by
      have : a.limbs.toList.length = 0 := hz
      simp_all
    have h_toNat_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      rw [h_nil]; rfl
    rw [h_toNat_zero]; simp
  · rw [if_neg hz]
    by_cases hsm : sh % 64 = 0
    · rw [dif_pos hsm, toNat_shiftRightMul64]
      congr 1
      conv_rhs => rw [show sh = 64 * (sh / 64) + sh % 64 from (Nat.div_add_mod sh 64).symm]
      rw [hsm, Nat.add_zero]
    · rw [dif_neg hsm]
      exact toNat_shiftRightGeneralLimbs a sh hsm

/-- Compatibility of `HShiftRight` notation with `shiftRight`. -/
@[simp] lemma hShiftRight_eq (a : AzNat) (sh : Nat) : a >>> sh = shiftRight a sh := rfl

/-- `toNat` respects right shift. -/
theorem toNat_hShiftRight (a : AzNat) (sh : Nat) :
    (a >>> sh).toNat = a.toNat >>> sh := by
  rw [hShiftRight_eq, toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- `ofNat` respects right shift. -/
theorem ofNat_shiftRight (n sh : Nat) : ofNat (n >>> sh) = ofNat n >>> sh := by
  apply toNat_injective
  rw [toNat_hShiftRight, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
