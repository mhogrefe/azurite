import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.Equiv.Mul.Basic
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Mathlib.Data.Nat.GCD.Basic

/-!
## Correctness of `AzNat.mulSchoolbookModPow2`

`(mulSchoolbookModPow2 a b k).toNat = (a.toNat * b.toNat) % 2 ^ k`.

The argument is a truncated-product invariant for the outer loop, stated modulo
`2 ^ (64 * L)` (with `L = (k + 63) / 64`).  Each clamped row contributes
`a-slice * b[j] * 2 ^ (64 j)` modulo `2 ^ (64 L)`; the dropped high limbs and the
dropped carry are all multiples of `2 ^ (64 L)`.
-/

namespace Azurite.AzNat

/-- Decompose the value of a size-`L` array into a prefix `[0, j)`, a window
    `[j, j+w)`, and a tail `[j+w, L)`. -/
private lemma toNatLimbsList_split3 (arr : Array UInt64) (j w L : Nat)
    (hsize : arr.size = L) (hjw : j + w ≤ L) :
    toNatLimbsList arr.toList
      = toNatLimbsList (arr.toList.take j)
        + toNatLimbsList ((arr.toList.drop j).take w) * 2 ^ (64 * j)
        + toNatLimbsList ((arr.toList.drop (j + w)).take (L - (j + w)))
          * 2 ^ (64 * (j + w)) := by
  have hlen : arr.toList.length = L := by rw [Array.length_toList, hsize]
  have hwhole : arr.toList.take L = arr.toList := List.take_of_length_le (by rw [hlen])
  have h1 := toNatLimbsList_drop_take_split arr 0 L (j + w) (by omega) (by omega)
  have h2 := toNatLimbsList_drop_take_split arr 0 (j + w) j (by omega) (by omega)
  simp only [List.drop_zero, Nat.zero_add, hwhole] at h1 h2
  rw [show j + w - j = w from by omega] at h2
  rw [h1, h2]

/-- Setting a currently-zero cell `p` of an array to `v` adds `v * 2 ^ (64 p)`
    to its limb value. -/
private lemma toNatLimbsList_set_of_zero (arr : Array UInt64) (p : Nat) (v : UInt64)
    (hp : p < arr.size) (hz : arr[p]'hp = 0) :
    toNatLimbsList (arr.set p v hp).toList
      = toNatLimbsList arr.toList + v.toNat * 2 ^ (64 * p) := by
  have hlen : arr.toList.length = arr.size := Array.length_toList
  have hp_lt : p < arr.toList.length := by omega
  have hset_len : (arr.set p v hp).toList.length = arr.toList.length := by
    rw [Array.toList_set, List.length_set]
  have hsplit_arr := toNatLimbsList_take_drop arr.toList p (by omega)
  have hsplit_set := toNatLimbsList_take_drop (arr.set p v hp).toList p (by rw [hset_len]; omega)
  have h_take : (arr.set p v hp).toList.take p = arr.toList.take p := by
    rw [Array.toList_set, List.take_set_of_le (Nat.le_refl p)]
  have h_drop_arr : arr.toList.drop p = arr[p]'hp :: arr.toList.drop (p + 1) := by
    rw [List.drop_eq_getElem_cons hp_lt, Array.getElem_toList]
  have h_drop_set : (arr.set p v hp).toList.drop p = v :: arr.toList.drop (p + 1) := by
    rw [Array.toList_set, List.drop_eq_getElem_cons (by rw [List.length_set]; omega),
      List.getElem_set_self]
    congr 1
    rw [List.drop_set]
    simp
  rw [hsplit_set, hsplit_arr, h_take, h_drop_arr, h_drop_set, hz]
  rw [toNatLimbsList_cons, toNatLimbsList_cons]
  simp only [UInt64.toNat_zero]
  ring

/-- **Row lemma.** A single clamped multiply-accumulate row of the low schoolbook
    multiplication adds `a-slice * b[j] * 2 ^ (64 j)` to the accumulator, modulo
    `2 ^ (64 L)`.  Needs the zero-tail invariant (positions `[j+lenA, L)` of `acc`
    are `0`) so a stored carry lands on a zero cell. -/
private lemma schoolbookMulLowRow_modEq
    (a : Array UInt64) (loA lenA : Nat) (bj : UInt64) (L j : Nat) (acc : Array UInt64)
    (hA : loA + lenA ≤ a.size) (hAccEq : acc.size = L) (hjL : j ≤ L)
    (h_zero : ∀ (i : Nat) (hi : i < acc.size), j + lenA ≤ i → i < L → acc[i]'hi = 0) :
    toNatLimbsList (schoolbookMulLowRow a loA lenA bj L j acc hA hAccEq.ge hjL).toList
      ≡ toNatLimbsList acc.toList
          + toNatLimbsList ((a.toList.drop loA).take lenA) * bj.toNat * 2 ^ (64 * j)
        [MOD 2 ^ (64 * L)] := by
  set rowLen := min lenA (L - j) with hrowLen
  have h_rowLen_le_lenA : rowLen ≤ lenA := Nat.min_le_left _ _
  have h_rowLen_le : rowLen ≤ L - j := Nat.min_le_right _ _
  have h_jrow_le : j + rowLen ≤ L := by omega
  have hAccRow : j + rowLen ≤ acc.size := by omega
  have hARow : loA + rowLen ≤ a.size := by omega
  set r := mulAddLimbs a loA rowLen j bj acc hARow hAccRow with hr
  have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
  set AS := toNatLimbsList ((a.toList.drop loA).take lenA) with hAS
  set ASr := toNatLimbsList ((a.toList.drop loA).take rowLen) with hASr
  set Wacc := toNatLimbsList ((acc.toList.drop j).take rowLen) with hWacc
  set Wr := toNatLimbsList ((r.1.toList.drop j).take rowLen) with hWr
  have h_mac : ASr * bj.toNat + Wacc = Wr + r.2.toNat * 2 ^ (64 * rowLen) :=
    mulAddLimbs_toNat a loA rowLen j bj acc hARow hAccRow
  have h_take_j : r.1.toList.take j = acc.toList.take j := by
    have := mulAddLimbs.go_toList_take a loA rowLen j bj acc 0 0 hARow hAccRow
    simpa [hr, mulAddLimbs] using this
  have h_drop : r.1.toList.drop (j + rowLen) = acc.toList.drop (j + rowLen) := by
    have := mulAddLimbs.go_toList_drop a loA rowLen j bj acc 0 0 hARow hAccRow
    simpa [hr, mulAddLimbs] using this
  have h_dec_acc := toNatLimbsList_split3 acc j rowLen L hAccEq h_jrow_le
  have h_dec_r := toNatLimbsList_split3 r.1 j rowLen L (by rw [h_r_size]; exact hAccEq) h_jrow_le
  rw [← hWacc] at h_dec_acc
  rw [← hWr, h_take_j, h_drop] at h_dec_r
  have h_pow_jrow : (2 : ℕ) ^ (64 * (j + rowLen)) = 2 ^ (64 * rowLen) * 2 ^ (64 * j) := by
    rw [← Nat.pow_add]; congr 1; ring
  -- KEY-R1: `acc + ASr*bj*2^(64j) = r.1 + r.2*2^(64(j+rowLen))`.
  have hd : ASr * bj.toNat * 2 ^ (64 * j) + Wacc * 2 ^ (64 * j)
      = Wr * 2 ^ (64 * j) + r.2.toNat * 2 ^ (64 * rowLen) * 2 ^ (64 * j) := by
    have h := congrArg (· * 2 ^ (64 * j)) h_mac
    simpa [Nat.add_mul] using h
  have hKey : toNatLimbsList acc.toList + ASr * bj.toNat * 2 ^ (64 * j)
      = toNatLimbsList r.1.toList + r.2.toNat * 2 ^ (64 * (j + rowLen)) := by
    rw [h_dec_acc, h_dec_r, h_pow_jrow]
    linarith [hd]
  -- Split on whether the carry is stored.  Restate the row in terms of the local
  -- `rowLen`/`r` (defeq through the `let`s and proof irrelevance).
  have heqRow : schoolbookMulLowRow a loA lenA bj L j acc hA hAccEq.ge hjL
      = if h2 : j + rowLen < L then r.1.set (j + rowLen) r.2 (by rw [h_r_size, hAccEq]; omega)
        else r.1 := rfl
  rw [heqRow]
  split
  · -- `j + rowLen < L`: carry stored at position `j + rowLen` (a zero cell).
    rename_i h2
    have h_rowLen_eq : rowLen = lenA := by omega
    have hASeq : ASr = AS := by rw [hASr, hAS, h_rowLen_eq]
    have h_jrow_lt_r : j + rowLen < r.1.size := by rw [h_r_size, hAccEq]; exact h2
    have h_acc_lt : j + rowLen < acc.size := by rw [hAccEq]; exact h2
    have h_r_at : r.1[j + rowLen]'h_jrow_lt_r = 0 := by
      have hacc0 : acc[j + rowLen]'h_acc_lt = 0 := h_zero (j + rowLen) h_acc_lt (by omega) h2
      -- `r.1[j+rowLen] = acc[j+rowLen]` from suffix preservation `h_drop`.
      have h := congrArg (fun l => l[0]?) h_drop
      simp only [List.getElem?_drop, Nat.add_zero] at h
      rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h_jrow_lt_r),
          List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h_acc_lt),
          Array.getElem_toList, Array.getElem_toList, Option.some.injEq] at h
      rw [h, hacc0]
    have h_set := toNatLimbsList_set_of_zero r.1 (j + rowLen) r.2 h_jrow_lt_r h_r_at
    rw [hASeq] at hKey
    rw [h_set, ← hKey]
  · -- `¬ (j + rowLen < L)`, so `j + rowLen = L`: carry dropped.
    rename_i h2
    have h_jrow_eq : j + rowLen = L := by omega
    have hmod1 : toNatLimbsList r.1.toList
        ≡ toNatLimbsList acc.toList + ASr * bj.toNat * 2 ^ (64 * j) [MOD 2 ^ (64 * L)] := by
      have hL : (2 : ℕ) ^ (64 * (j + rowLen)) = 2 ^ (64 * L) := by rw [h_jrow_eq]
      unfold Nat.ModEq
      rw [hKey, hL, Nat.add_mul_mod_self_right]
    have hAShigh : AS = ASr
        + toNatLimbsList ((a.toList.drop (loA + rowLen)).take (lenA - rowLen)) * 2 ^ (64 * rowLen) := by
      rw [hAS, hASr]
      exact toNatLimbsList_drop_take_split a loA lenA rowLen h_rowLen_le_lenA hA
    have hmod2 : ASr * bj.toNat * 2 ^ (64 * j)
        ≡ AS * bj.toNat * 2 ^ (64 * j) [MOD 2 ^ (64 * L)] := by
      rw [hAShigh]
      set H := toNatLimbsList ((a.toList.drop (loA + rowLen)).take (lenA - rowLen)) with hH
      have hexpand : (ASr + H * 2 ^ (64 * rowLen)) * bj.toNat * 2 ^ (64 * j)
          = ASr * bj.toNat * 2 ^ (64 * j) + H * bj.toNat * 2 ^ (64 * L) := by
        rw [← h_jrow_eq, h_pow_jrow]; ring
      rw [hexpand]
      unfold Nat.ModEq
      rw [Nat.add_mul_mod_self_right]
    calc toNatLimbsList r.1.toList
        ≡ toNatLimbsList acc.toList + ASr * bj.toNat * 2 ^ (64 * j) [MOD 2 ^ (64 * L)] := hmod1
      _ ≡ toNatLimbsList acc.toList + AS * bj.toNat * 2 ^ (64 * j) [MOD 2 ^ (64 * L)] :=
          Nat.ModEq.add_left _ hmod2

/-- Equal suffixes (`drop m`) give equal entries at any index `≥ m`. -/
private lemma getElem_eq_of_drop_eq {arr1 arr2 : Array UInt64} {m i : Nat}
    (h : arr1.toList.drop m = arr2.toList.drop m) (hm : m ≤ i)
    (hi1 : i < arr1.size) (hi2 : i < arr2.size) :
    arr1[i]'hi1 = arr2[i]'hi2 := by
  have hk := congrArg (fun l => l[i - m]?) h
  simp only [List.getElem?_drop] at hk
  rw [show m + (i - m) = i from by omega] at hk
  rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; exact hi1),
      List.getElem?_eq_getElem (by rw [Array.length_toList]; exact hi2),
      Array.getElem_toList, Array.getElem_toList, Option.some.injEq] at hk
  exact hk

/-- A clamped row preserves the suffix from position `j + lenA + 1`:  the row
    touches `[j, j+rowLen)` and may set a carry at `j+rowLen ≤ j+lenA`. -/
private lemma schoolbookMulLowRow_toList_drop (a : Array UInt64) (loA lenA : Nat) (bj : UInt64)
    (L j : Nat) (acc : Array UInt64) (hA : loA + lenA ≤ a.size) (hAcc : L ≤ acc.size) (hjL : j ≤ L) :
    (schoolbookMulLowRow a loA lenA bj L j acc hA hAcc hjL).toList.drop (j + lenA + 1)
      = acc.toList.drop (j + lenA + 1) := by
  set rowLen := min lenA (L - j) with hrowLen
  have h_rowLen_le_lenA : rowLen ≤ lenA := Nat.min_le_left _ _
  have h_rowLen_le : rowLen ≤ L - j := Nat.min_le_right _ _
  have hARow : loA + rowLen ≤ a.size := by omega
  have hAccRow : j + rowLen ≤ acc.size := by omega
  set r := mulAddLimbs a loA rowLen j bj acc hARow hAccRow with hr
  have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
  have h_drop : r.1.toList.drop (j + rowLen) = acc.toList.drop (j + rowLen) := by
    have := mulAddLimbs.go_toList_drop a loA rowLen j bj acc 0 0 hARow hAccRow
    simpa [hr, mulAddLimbs] using this
  have h_drop' : r.1.toList.drop (j + lenA + 1) = acc.toList.drop (j + lenA + 1) := by
    have hcong := congrArg (List.drop (lenA + 1 - rowLen)) h_drop
    rw [List.drop_drop, List.drop_drop,
      show (j + rowLen) + (lenA + 1 - rowLen) = j + lenA + 1 from by omega] at hcong
    exact hcong
  have heqRow : schoolbookMulLowRow a loA lenA bj L j acc hA hAcc hjL
      = if h2 : j + rowLen < L then r.1.set (j + rowLen) r.2 (by rw [h_r_size]; omega) else r.1 := rfl
  rw [heqRow]
  split
  · rw [Array.toList_set, List.drop_set, if_pos (by omega : j + rowLen < j + lenA + 1)]
    exact h_drop'
  · exact h_drop'

/-- **Outer-loop invariant.** Processing rows `[j, …)` of the low schoolbook
    multiplication adds `a-slice * b[loB+j:] * 2 ^ (64 j)` to the accumulator,
    modulo `2 ^ (64 L)`. -/
private lemma schoolbookMulLowLimbs.go_correct (a : Array UInt64) (loA lenA : Nat)
    (b : Array UInt64) (loB lenB L : Nat) (acc : Array UInt64) (j : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (hAccEq : acc.size = L) (hjL : j ≤ L)
    (h_zero : ∀ (i : Nat) (hi : i < acc.size), j + lenA ≤ i → i < L → acc[i]'hi = 0) :
    toNatLimbsList (schoolbookMulLowLimbs.go a loA lenA b loB lenB L acc j hA hB hAccEq.ge).toList
      ≡ toNatLimbsList acc.toList
        + toNatLimbsList ((a.toList.drop loA).take lenA)
          * toNatLimbsList ((b.toList.drop (loB + j)).take (lenB - j))
          * 2 ^ (64 * j)
        [MOD 2 ^ (64 * L)] := by
  induction h_sub : L - j generalizing acc j with
  | zero =>
    have hjge : L ≤ j := by omega
    have h_eq : schoolbookMulLowLimbs.go a loA lenA b loB lenB L acc j hA hB hAccEq.ge = acc := by
      rw [schoolbookMulLowLimbs.go, dif_neg (by omega : ¬ (j < lenB ∧ j < L))]
    rw [h_eq]
    obtain ⟨c, hc⟩ := Nat.pow_dvd_pow 2 (show 64 * L ≤ 64 * j from by omega)
    set X := toNatLimbsList ((a.toList.drop loA).take lenA)
      * toNatLimbsList ((b.toList.drop (loB + j)).take (lenB - j)) with hX
    show toNatLimbsList acc.toList ≡ toNatLimbsList acc.toList + X * 2 ^ (64 * j) [MOD 2 ^ (64 * L)]
    unfold Nat.ModEq
    rw [hc, show X * (2 ^ (64 * L) * c) = X * c * 2 ^ (64 * L) from by ring,
      Nat.add_mul_mod_self_right]
  | succ n ih =>
    have hjlt : j < L := by omega
    by_cases hjb : j < lenB
    · set acc' := schoolbookMulLowRow a loA lenA b[loB + j] L j acc hA hAccEq.ge hjL with hacc'
      have hAcc'Eq : acc'.size = L := by rw [hacc', schoolbookMulLowRow_size]; exact hAccEq
      have h_eq : schoolbookMulLowLimbs.go a loA lenA b loB lenB L acc j hA hB hAccEq.ge
          = schoolbookMulLowLimbs.go a loA lenA b loB lenB L acc' (j + 1) hA hB hAcc'Eq.ge := by
        conv_lhs => rw [schoolbookMulLowLimbs.go]
        rw [dif_pos (⟨hjb, hjlt⟩ : j < lenB ∧ j < L)]
      have h_zero' : ∀ (i : Nat) (hi : i < acc'.size), (j + 1) + lenA ≤ i → i < L → acc'[i]'hi = 0 := by
        intro i hi hge hlt
        have hi_acc : i < acc.size := by rw [hAccEq]; rw [hAcc'Eq] at hi; exact hi
        have hdrop := schoolbookMulLowRow_toList_drop a loA lenA b[loB + j] L j acc hA hAccEq.ge hjL
        rw [← hacc'] at hdrop
        rw [getElem_eq_of_drop_eq hdrop (by omega) hi hi_acc]
        exact h_zero i hi_acc (by omega) hlt
      have ih' := ih acc' (j + 1) hAcc'Eq (by omega) h_zero' (by omega)
      rw [h_eq]
      have hrow := schoolbookMulLowRow_modEq a loA lenA b[loB + j] L j acc hA hAccEq hjL h_zero
      rw [← hacc'] at hrow
      have hbjlt : loB + j < b.toList.length := by rw [Array.length_toList]; omega
      have hBsplit : toNatLimbsList ((b.toList.drop (loB + j)).take (lenB - j))
          = b[loB + j].toNat
            + toNatLimbsList ((b.toList.drop (loB + (j + 1))).take (lenB - (j + 1))) * 2 ^ 64 := by
        have hcons : (b.toList.drop (loB + j)).take (lenB - j)
            = b[loB + j] :: (b.toList.drop (loB + (j + 1))).take (lenB - (j + 1)) := by
          rw [List.drop_eq_getElem_cons hbjlt, Array.getElem_toList,
            show lenB - j = (lenB - (j + 1)) + 1 from by omega, List.take_succ_cons,
            show loB + j + 1 = loB + (j + 1) from by ring]
        rw [hcons, toNatLimbsList_cons]; ring
      set AS := toNatLimbsList ((a.toList.drop loA).take lenA) with hAS
      set Bj1 := toNatLimbsList ((b.toList.drop (loB + (j + 1))).take (lenB - (j + 1))) with hBj1
      rw [hBsplit]
      have hpow : (2 : ℕ) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
        rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
      have hRHS : toNatLimbsList acc.toList + AS * (b[loB + j].toNat + Bj1 * 2 ^ 64) * 2 ^ (64 * j)
          = (toNatLimbsList acc.toList + AS * b[loB + j].toNat * 2 ^ (64 * j))
            + AS * Bj1 * 2 ^ (64 * (j + 1)) := by
        rw [hpow]; ring
      rw [hRHS]
      exact ih'.trans (Nat.ModEq.add_right _ hrow)
    · have h_eq : schoolbookMulLowLimbs.go a loA lenA b loB lenB L acc j hA hB hAccEq.ge = acc := by
        rw [schoolbookMulLowLimbs.go, dif_neg (by omega : ¬ (j < lenB ∧ j < L))]
      have hzero_slice : toNatLimbsList ((b.toList.drop (loB + j)).take (lenB - j)) = 0 := by
        rw [show lenB - j = 0 from by omega]; rfl
      rw [h_eq, hzero_slice, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]

private lemma toNatLimbsList_replicate_zero (m : Nat) :
    toNatLimbsList (List.replicate m (0 : UInt64)) = 0 := by
  induction m with
  | zero => rfl
  | succ p ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp

/-- **Slice-level correctness.** `schoolbookMulLowLimbs` computes the product of
    the two slices truncated to `2 ^ (64 L)`. -/
theorem schoolbookMulLowLimbs_modEq (a b : Array UInt64) (loA lenA loB lenB L : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (schoolbookMulLowLimbs a b loA lenA loB lenB L hA hB).toList
      ≡ toNatLimbsList ((a.toList.drop loA).take lenA)
        * toNatLimbsList ((b.toList.drop loB).take lenB) [MOD 2 ^ (64 * L)] := by
  unfold schoolbookMulLowLimbs
  have hAcc0 : (Array.replicate L (0 : UInt64)).size = L := Array.size_replicate
  have h_zero : ∀ (i : Nat) (hi : i < (Array.replicate L (0 : UInt64)).size),
      0 + lenA ≤ i → i < L → (Array.replicate L (0 : UInt64))[i]'hi = 0 := by
    intro i hi _ _; simp [Array.getElem_replicate]
  have h := schoolbookMulLowLimbs.go_correct a loA lenA b loB lenB L (Array.replicate L 0) 0
    hA hB hAcc0 (by omega) h_zero
  rw [show toNatLimbsList (Array.replicate L (0 : UInt64)).toList = 0 from by
        rw [Array.toList_replicate]; exact toNatLimbsList_replicate_zero L] at h
  simpa using h

/-- **Correctness of `mulSchoolbookModPow2`.** -/
theorem toNat_mulSchoolbookModPow2 (a b : AzNat) (k : Nat) :
    (mulSchoolbookModPow2 a b k).toNat = (a.toNat * b.toNat) % 2 ^ k := by
  unfold mulSchoolbookModPow2
  rw [toNat_modPow2, toNat_ofLimbs]
  set L := (k + 63) / 64 with hL
  have hslice := schoolbookMulLowLimbs_modEq a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size L
    (by omega) (by omega)
  rw [List.drop_zero, List.drop_zero,
      List.take_of_length_le (by rw [Array.length_toList]),
      List.take_of_length_le (by rw [Array.length_toList]),
      show toNatLimbsList a.limbs.toList = a.toNat from rfl,
      show toNatLimbsList b.limbs.toList = b.toNat from rfl] at hslice
  unfold Nat.ModEq at hslice
  set R := toNatLimbsList (schoolbookMulLowLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size L
    (by omega) (by omega)).toList with hR
  have hdvd : (2 : ℕ) ^ k ∣ 2 ^ (64 * L) := Nat.pow_dvd_pow 2 (by rw [hL]; omega)
  have h1 : R % 2 ^ k = R % 2 ^ (64 * L) % 2 ^ k := (Nat.mod_mod_of_dvd R hdvd).symm
  have h2 : a.toNat * b.toNat % 2 ^ k = a.toNat * b.toNat % 2 ^ (64 * L) % 2 ^ k :=
    (Nat.mod_mod_of_dvd _ hdvd).symm
  rw [h1, h2, hslice]

end Azurite.AzNat
