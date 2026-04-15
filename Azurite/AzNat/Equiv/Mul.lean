import Azurite.AzNat.Mul
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.MulWithCarry
import Azurite.UInt64.Equiv.MulAddWithCarry

namespace Azurite.AzNat

/-- Size preservation of `mulLimb.go`. -/
theorem mulLimb.go_size (hi : Nat) (b : UInt64) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) :
    (mulLimb.go hi b a i carry h_size).1.size = a.size := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [mulLimb.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    rw [mulLimb.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega), Array.size_set]

/-- Size preservation of `mulLimb`. -/
theorem mulLimb_size (hi : Nat) (a : Array UInt64) (lo : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (mulLimb a lo hi b hlo hhi).1.size = a.size :=
  mulLimb.go_size hi b a lo 0 hhi

/-- `mulLimb.go` preserves the prefix `[0, i)`. -/
theorem mulLimb.go_toList_take (hi : Nat) (b : UInt64) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) :
    (mulLimb.go hi b a i carry h_size).1.toList.take i = a.toList.take i := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [mulLimb.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    rw [mulLimb.go]
    simp only [h_lt, ↓reduceDIte]
    have h_rec : hi - (i + 1) = n := by omega
    set prod := UInt64.mulWithCarry a[i] b carry with hprod_def
    have h_take_succ : List.take i
        ((mulLimb.go hi b (a.set i prod.2) (i + 1) prod.1
            (by rw [Array.size_set]; exact h_size)).1.toList.take (i + 1))
          = (mulLimb.go hi b (a.set i prod.2) (i + 1) prod.1
              (by rw [Array.size_set]; exact h_size)).1.toList.take i := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    rw [← h_take_succ, ih _ _ _ _ h_rec, List.take_take, Nat.min_eq_left (by omega)]
    rw [Array.toList_set, List.take_set]
    rw [List.set_eq_of_length_le]
    rw [List.length_take, Array.length_toList]
    omega

/-- Invariant of `mulLimb.go`: multiplying the original slice by `b` and adding
    the incoming `carry` equals the resulting modified slice plus the outgoing
    carry placed at position `hi`. -/
private lemma mulLimb.go_correct (hi : Nat) (a : Array UInt64) (i : Nat)
    (carry b : UInt64) (h_size : hi ≤ a.size) :
    toNatLimbsList ((a.toList.drop i).take (hi - i)) * b.toNat + carry.toNat
      = toNatLimbsList (((mulLimb.go hi b a i carry h_size).1.toList.drop i).take (hi - i))
        + (mulLimb.go hi b a i carry h_size).2.toNat * 2 ^ (64 * (hi - i)) := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    have h_eq : mulLimb.go hi b a i carry h_size = (a, carry) := by
      conv_lhs => rw [mulLimb.go]; simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    set x := a[i] with hx_def
    set prod := UInt64.mulWithCarry x b carry with hprod_def
    set newCarry := prod.1 with hnc_def
    set lo' := prod.2 with hlo_def
    set a' := a.set i lo' h_i_size with ha'_def
    have h_size' : hi ≤ a'.size := by rw [ha'_def, Array.size_set]; exact h_size
    have h_eq : mulLimb.go hi b a i carry h_size
                = mulLimb.go hi b a' (i + 1) newCarry h_size' := by
      conv_lhs => rw [mulLimb.go]
      simp [h_lt, hx_def, hprod_def, hnc_def, hlo_def, ha'_def]
    have h_rec : hi - (i + 1) = n := by omega
    have h_ih := ih a' (i + 1) newCarry h_size' h_rec
    have h_limb : x.toNat * b.toNat + carry.toNat = newCarry.toNat * 2 ^ 64 + lo'.toNat := by
      rw [hnc_def, hlo_def, hprod_def]
      have := UInt64.mulWithCarry_eq x b carry
      omega
    have h_res_size :
        (mulLimb.go hi b a' (i + 1) newCarry h_size').1.size = a.size := by
      rw [mulLimb.go_size, ha'_def, Array.size_set]
    have h_res_i_size : i < (mulLimb.go hi b a' (i + 1) newCarry h_size').1.size := by
      rw [h_res_size]; exact h_i_size
    have h_res_i : (mulLimb.go hi b a' (i + 1) newCarry h_size').1[i]'h_res_i_size = lo' := by
      have h_prefix := mulLimb.go_toList_take hi b a' (i + 1) newCarry h_size'
      have h_len_L : ((mulLimb.go hi b a' (i + 1) newCarry h_size').1.toList).length = a.size := by
        rw [Array.length_toList]; exact h_res_size
      have h_i_lt_L_take :
          i < ((mulLimb.go hi b a' (i + 1) newCarry h_size').1.toList.take (i + 1)).length := by
        rw [List.length_take, h_len_L]; omega
      have h_i_lt_R_take : i < (a'.toList.take (i + 1)).length := by
        rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
      have h_get_eq :
          ((mulLimb.go hi b a' (i + 1) newCarry h_size').1.toList.take (i + 1))[i]'h_i_lt_L_take
            = (a'.toList.take (i + 1))[i]'h_i_lt_R_take := by
        congr 1
      rw [List.getElem_take, List.getElem_take] at h_get_eq
      rw [← Array.getElem_toList h_res_i_size, h_get_eq]
      have h_i_lt : i < (a.set i lo' h_i_size).toList.length := by
        rw [Array.length_toList, Array.size_set]; exact h_i_size
      show (a.set i lo' h_i_size).toList[i]'h_i_lt = lo'
      simp [Array.toList_set, List.getElem_set_self]
    have h_drop_eq : a'.toList.drop (i + 1) = a.toList.drop (i + 1) := by
      rw [ha'_def, Array.toList_set, List.drop_set]; simp
    rw [h_eq]
    rw [show (n + 1) = hi - i from hi_sub_i.symm]
    rw [toNatLimbsList_take_succ (mulLimb.go hi b a' (i + 1) newCarry h_size').1 i hi
          h_res_i_size h_lt]
    rw [h_res_i]
    rw [toNatLimbsList_take_succ a i hi h_i_size h_lt]
    have h_pow : (2 : Nat) ^ (64 * (hi - i))
                = 2 ^ (64 * (hi - (i + 1))) * 2 ^ 64 := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [h_pow]
    rw [← h_drop_eq]
    rw [← h_rec] at h_ih
    set P := toNatLimbsList ((a'.toList.drop (i + 1)).take (hi - (i + 1))) with hP_def
    set Q := toNatLimbsList
        (((mulLimb.go hi b a' (i + 1) newCarry h_size').1.toList.drop (i + 1)).take (hi - (i + 1)))
      with hQ_def
    set R := (mulLimb.go hi b a' (i + 1) newCarry h_size').2.toNat with hR_def
    change (x.toNat + P * 2 ^ 64) * b.toNat + carry.toNat
         = lo'.toNat + Q * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
    have h1 : (x.toNat + P * 2 ^ 64) * b.toNat + carry.toNat
            = (x.toNat * b.toNat + carry.toNat) + P * b.toNat * 2 ^ 64 := by ring
    rw [h1, h_limb]
    have h_ih_mul : (P * b.toNat + newCarry.toNat) * 2 ^ 64
        = (Q + R * 2 ^ (64 * (hi - (i + 1)))) * 2 ^ 64 := by rw [h_ih]
    nlinarith [h_ih_mul]

/-- Correctness of `mulLimb`: multiplying the original slice `[lo, hi)` by `b`
    equals the modified slice plus the returned carry at the top. -/
theorem mulLimb_toNat (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    let (a', c) := mulLimb a lo hi b hlo hhi
    toNatLimbsList ((a.toList.drop lo).take (hi - lo)) * b.toNat
      = toNatLimbsList ((a'.toList.drop lo).take (hi - lo))
        + c.toNat * 2 ^ (64 * (hi - lo)) := by
  have h := mulLimb.go_correct hi a lo 0 b hhi
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h0, Nat.add_zero] at h
  exact h

/-- Correctness of `AzNat.mulUInt64`. -/
theorem toNat_mulUInt64 (a : AzNat) (b : UInt64) :
    (a.mulUInt64 b).toNat = a.toNat * b.toNat := by
  unfold mulUInt64
  by_cases hsz : a.limbs.size = 0
  · have h_nil : a.limbs.toList = [] := by
      have : a.limbs.toList.length = 0 := hsz
      exact List.length_eq_zero_iff.mp this
    have h_a_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      rw [h_nil]; rfl
    simp [hsz, h_a_zero]
  · simp only [hsz, ↓reduceIte]
    by_cases hb : b = 0
    · simp [hb]
    · simp only [hb, ↓reduceIte]
      set n := a.limbs.size with hn_def
      have h_pos : 0 < n := Nat.pos_of_ne_zero hsz
      have h_size : (mulLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.size = n :=
        mulLimb_size _ _ _ _ _ _
      have h_main := mulLimb_toNat a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)
      simp only [List.drop_zero, Nat.sub_zero] at h_main
      have h_take_arr : a.limbs.toList.take n = a.limbs.toList := by
        rw [List.take_of_length_le]; rw [Array.length_toList]
      have h_take_r : (mulLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList.take n
                    = (mulLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList := by
        rw [List.take_of_length_le]; rw [Array.length_toList, h_size]
      rw [h_take_arr, h_take_r] at h_main
      set r := mulLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)
      have h_a : a.toNat = toNatLimbsList a.limbs.toList := rfl
      by_cases hc : r.2 = 0
      · simp only [hc, ↓reduceIte]
        rw [toNat_ofLimbs]
        have hc0 : r.2.toNat = 0 := by rw [hc]; rfl
        rw [hc0] at h_main
        rw [h_a]; omega
      · simp only [hc, ↓reduceIte]
        rw [toNat_ofLimbs, Array.toList_push, toNatLimbsList_append]
        have h_len : (r.1.toList).length = n := by rw [Array.length_toList, h_size]
        rw [h_len]
        show toNatLimbsList [r.2] * 2 ^ (64 * n) + toNatLimbsList r.1.toList
              = a.toNat * b.toNat
        have h_single : toNatLimbsList [r.2] = r.2.toNat := by
          show toNatLimbsList [r.2] = r.2.toNat
          rw [show ([r.2] : List UInt64) = r.2 :: [] from rfl, toNatLimbsList_cons]
          simp [toNatLimbsList]
        rw [h_single, h_a]; omega

/-! ### Correctness of `mulAddLimbs` -/

/-- `mulAddLimbs.go` preserves any prefix of `acc` up to `offAcc + k`. -/
theorem mulAddLimbs.go_toList_take_le (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64) (k : Nat) (carry : UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size)
    (m : Nat) (hm : m ≤ offAcc + k) :
    (mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc).1.toList.take m
      = acc.toList.take m := by
  induction h_sub : lenA - k generalizing acc k carry with
  | zero =>
    have h_ge : lenA ≤ k := by omega
    rw [mulAddLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < lenA := by omega
    have h_rec : lenA - (k + 1) = n := by omega
    rw [mulAddLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega) h_rec]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `mulAddLimbs.go` preserves the prefix of `acc` up to `offAcc + k`. -/
theorem mulAddLimbs.go_toList_take (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64) (k : Nat) (carry : UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    (mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc).1.toList.take (offAcc + k)
      = acc.toList.take (offAcc + k) :=
  mulAddLimbs.go_toList_take_le a offA lenA offAcc b acc k carry hA hAcc (offAcc + k)
    (Nat.le_refl _)

/-- `mulAddLimbs.go` preserves the suffix of `acc` from `offAcc + lenA`. -/
theorem mulAddLimbs.go_toList_drop (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64) (k : Nat) (carry : UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    (mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc).1.toList.drop (offAcc + lenA)
      = acc.toList.drop (offAcc + lenA) := by
  induction h_sub : lenA - k generalizing acc k carry with
  | zero =>
    have h_ge : lenA ≤ k := by omega
    rw [mulAddLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < lenA := by omega
    rw [mulAddLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    have h_rec : lenA - (k + 1) = n := by omega
    rw [ih _ _ _ _ h_rec]
    rw [Array.toList_set, List.drop_set]
    simp
    omega

/-- Invariant of `mulAddLimbs.go`: multiplying original `a`-slice by `b`, adding
    original `acc`-slice and incoming `carry`, equals modified `acc`-slice plus
    final carry at position `lenA - k`. -/
private lemma mulAddLimbs.go_correct (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64) (k : Nat) (carry : UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    toNatLimbsList ((a.toList.drop (offA + k)).take (lenA - k)) * b.toNat
      + toNatLimbsList ((acc.toList.drop (offAcc + k)).take (lenA - k))
      + carry.toNat
    = toNatLimbsList
        (((mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc).1.toList.drop (offAcc + k)).take
          (lenA - k))
      + (mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc).2.toNat
        * 2 ^ (64 * (lenA - k)) := by
  induction h_sub : lenA - k generalizing acc k carry with
  | zero =>
    have h_ge : lenA ≤ k := by omega
    have h_eq : mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc = (acc, carry) := by
      rw [mulAddLimbs.go]; simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]; simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : k < lenA := by omega
    have h_iA : offA + k < a.size := by omega
    have h_iAcc : offAcc + k < acc.size := by omega
    set mac := UInt64.mulAddWithCarry a[offA + k] b acc[offAcc + k] carry with hmac_def
    set newCarry := mac.1 with hnc_def
    set lo' := mac.2 with hlo_def
    set acc' := acc.set (offAcc + k) lo' with hacc'_def
    have hAcc' : offAcc + lenA ≤ acc'.size := by rw [hacc'_def, Array.size_set]; exact hAcc
    have h_eq : mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc
              = mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc' := by
      conv_lhs => rw [mulAddLimbs.go]
      simp [h_lt, hmac_def, hnc_def, hlo_def, hacc'_def]
    have h_rec : lenA - (k + 1) = n := by omega
    have h_ih := ih acc' (k + 1) newCarry hAcc' h_rec
    have h_mac := UInt64.mulAddWithCarry_eq a[offA + k] b acc[offAcc + k] carry
    rw [← hmac_def] at h_mac
    have h_res_size :
        (mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1.size = acc.size := by
      rw [mulAddLimbs.go_size, hacc'_def, Array.size_set]
    have h_res_iAcc_size :
        offAcc + k
          < (mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1.size := by
      rw [h_res_size]; exact h_iAcc
    have h_res_i :
        (mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1[offAcc + k]'h_res_iAcc_size
          = lo' := by
      have h_prefix :=
        mulAddLimbs.go_toList_take a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc'
      have h_len_L :
          ((mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1.toList).length
            = acc.size := by rw [Array.length_toList]; exact h_res_size
      have h_i_lt_L_take :
          offAcc + k
            < ((mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1.toList.take
                (offAcc + (k + 1))).length := by rw [List.length_take, h_len_L]; omega
      have h_i_lt_R_take :
          offAcc + k < (acc'.toList.take (offAcc + (k + 1))).length := by
        rw [List.length_take, Array.length_toList, hacc'_def, Array.size_set]; omega
      have h_get_eq :
          ((mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1.toList.take
              (offAcc + (k + 1)))[offAcc + k]'h_i_lt_L_take
            = (acc'.toList.take (offAcc + (k + 1)))[offAcc + k]'h_i_lt_R_take := by
        congr 1
      rw [List.getElem_take, List.getElem_take] at h_get_eq
      rw [← Array.getElem_toList h_res_iAcc_size, h_get_eq]
      have h_i_lt : offAcc + k < (acc.set (offAcc + k) lo' h_iAcc).toList.length := by
        rw [Array.length_toList, Array.size_set]; exact h_iAcc
      show (acc.set (offAcc + k) lo' h_iAcc).toList[offAcc + k]'h_i_lt = lo'
      simp [Array.toList_set, List.getElem_set_self]
    have h_drop_acc' :
        acc'.toList.drop (offAcc + (k + 1)) = acc.toList.drop (offAcc + (k + 1)) := by
      rw [hacc'_def, Array.toList_set, List.drop_set]; simp
    rw [h_eq]
    have split_arr : ∀ (A : Array UInt64) (i m : Nat) (hi_size : i < A.size),
        toNatLimbsList ((A.toList.drop i).take (m + 1))
          = A[i].toNat + toNatLimbsList ((A.toList.drop (i + 1)).take m) * 2 ^ 64 := by
      intro A i m hi_size
      have h_lt_list : i < A.toList.length := hi_size
      rw [List.drop_eq_getElem_cons h_lt_list, List.take_succ_cons, toNatLimbsList_cons]
      rw [show A.toList[i] = A[i] from (Array.getElem_toList hi_size).symm]
      ring
    have h_len_split : lenA - k = (lenA - (k + 1)) + 1 := by omega
    rw [show (n + 1) = lenA - k from h_sub.symm, h_len_split]
    rw [split_arr a (offA + k) (lenA - (k + 1)) h_iA]
    rw [split_arr acc (offAcc + k) (lenA - (k + 1)) h_iAcc]
    rw [split_arr
          (mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1
          (offAcc + k) (lenA - (k + 1)) h_res_iAcc_size]
    rw [h_res_i]
    have h_pow : (2 : Nat) ^ (64 * ((lenA - (k + 1)) + 1))
                = 2 ^ (64 * (lenA - (k + 1))) * 2 ^ 64 := by
      rw [show 64 * ((lenA - (k + 1)) + 1) = 64 * (lenA - (k + 1)) + 64 from by ring, Nat.pow_add]
    rw [h_pow]
    rw [show offA + k + 1 = offA + (k + 1) from by ring]
    rw [show offAcc + k + 1 = offAcc + (k + 1) from by ring]
    rw [← h_drop_acc']
    rw [← h_rec] at h_ih
    set P := toNatLimbsList ((a.toList.drop (offA + (k + 1))).take (lenA - (k + 1))) with hP_def
    set A' := toNatLimbsList ((acc'.toList.drop (offAcc + (k + 1))).take (lenA - (k + 1)))
      with hA'_def
    set Q := toNatLimbsList
        (((mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').1.toList.drop
            (offAcc + (k + 1))).take (lenA - (k + 1))) with hQ_def
    set R := (mulAddLimbs.go a offA lenA offAcc b acc' (k + 1) newCarry hA hAcc').2.toNat
      with hR_def
    change (a[offA + k].toNat + P * 2 ^ 64) * b.toNat
           + (acc[offAcc + k].toNat + A' * 2 ^ 64)
           + carry.toNat
         = lo'.toNat + Q * 2 ^ 64 + R * (2 ^ (64 * (lenA - (k + 1))) * 2 ^ 64)
    have h_limb :
        a[offA + k].toNat * b.toNat + acc[offAcc + k].toNat + carry.toNat
          = newCarry.toNat * 2 ^ 64 + lo'.toNat := by
      rw [hnc_def, hlo_def]; omega
    have h_ih_mul :
        (P * b.toNat + A' + newCarry.toNat) * 2 ^ 64
          = (Q + R * 2 ^ (64 * (lenA - (k + 1)))) * 2 ^ 64 := by rw [h_ih]
    nlinarith [h_ih_mul, h_limb]

/-- Correctness of `mulAddLimbs`: the result's slice plus its returned carry
    equals original `a`-slice times `b` plus original `acc`-slice. -/
theorem mulAddLimbs_toNat (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    toNatLimbsList ((a.toList.drop offA).take lenA) * b.toNat
      + toNatLimbsList ((acc.toList.drop offAcc).take lenA)
    = toNatLimbsList
        (((mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.drop offAcc).take lenA)
      + (mulAddLimbs a offA lenA offAcc b acc hA hAcc).2.toNat * 2 ^ (64 * lenA) := by
  have h := mulAddLimbs.go_correct a offA lenA offAcc b acc 0 0 hA hAcc
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h0, Nat.add_zero, Nat.add_zero, Nat.sub_zero] at h
  simpa using h

/-! ### Correctness of `schoolbookMulLimbs` -/

private lemma toNatLimbsList_eq_zero_of_all_zero :
    ∀ (l : List UInt64),
      (∀ (i : Nat) (hi : i < l.length), l[i] = (0 : UInt64)) → toNatLimbsList l = 0
  | [], _ => rfl
  | x :: xs, h => by
    rw [toNatLimbsList_cons]
    have hx : x = (0 : UInt64) := by
      have := h 0 (by simp); simpa using this
    have hxs : ∀ (i : Nat) (hi : i < xs.length), xs[i] = (0 : UInt64) := by
      intro i hi
      have := h (i + 1) (by simp; omega); simpa using this
    rw [toNatLimbsList_eq_zero_of_all_zero xs hxs, hx]; simp

private lemma toNatLimbsList_take_add (l : List UInt64) (m k : Nat) (hm : m ≤ l.length) :
    toNatLimbsList (l.take (m + k))
      = toNatLimbsList (l.take m)
        + toNatLimbsList ((l.drop m).take k) * 2 ^ (64 * m) := by
  rw [List.take_add, toNatLimbsList_append, List.length_take, Nat.min_eq_left hm]
  ring

private lemma toNatLimbsList_take_step (l : List UInt64) (i : Nat) (hi : i < l.length) :
    toNatLimbsList (l.take (i + 1))
      = toNatLimbsList (l.take i) + l[i].toNat * 2 ^ (64 * i) := by
  rw [toNatLimbsList_take_add l i 1 (Nat.le_of_lt hi)]
  rw [List.drop_eq_getElem_cons hi]
  simp [List.take, toNatLimbsList]

/-- `r.1[i] = acc[i]` for indices `i ≥ offAcc + lenA` past the affected window. -/
private lemma mulAddLimbs_getElem_ge (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size)
    (i : Nat) (hge : offAcc + lenA ≤ i)
    (hi : i < (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.size) :
    (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1[i]'hi = acc[i]'(by
      have := mulAddLimbs_size a offA lenA offAcc b acc hA hAcc
      omega) := by
  have h_drop := mulAddLimbs.go_toList_drop a offA lenA offAcc b acc 0 0 hA hAcc
  change (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.drop (offAcc + lenA)
    = acc.toList.drop (offAcc + lenA) at h_drop
  have h_sizeR := mulAddLimbs_size a offA lenA offAcc b acc hA hAcc
  have h_acc_size : i < acc.size := by omega
  have h_lenL : (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.length = acc.size := by
    rw [Array.length_toList]; exact h_sizeR
  have h_idx : i - (offAcc + lenA)
      < ((mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.drop (offAcc + lenA)).length := by
    rw [List.length_drop, h_lenL]; omega
  have h_idx' : i - (offAcc + lenA) < (acc.toList.drop (offAcc + lenA)).length := by
    rw [List.length_drop, Array.length_toList]; omega
  have h_get := congrArg (fun l => l[i - (offAcc + lenA)]? ) h_drop
  simp only [List.getElem?_drop] at h_get
  rw [show offAcc + lenA + (i - (offAcc + lenA)) = i from by omega] at h_get
  have hi_L : i < (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.length := by
    rw [h_lenL]; exact by omega
  have hi_R : i < acc.toList.length := by rw [Array.length_toList]; exact h_acc_size
  have h_L : ((mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList)[i]?
      = some ((mulAddLimbs a offA lenA offAcc b acc hA hAcc).1[i]'hi) := by
    rw [List.getElem?_eq_getElem hi_L, Array.getElem_toList]
  have h_R : (acc.toList)[i]? = some (acc[i]'h_acc_size) := by
    rw [List.getElem?_eq_getElem hi_R, Array.getElem_toList]
  rw [h_L, h_R] at h_get
  exact Option.some.inj h_get

/-- Size preservation of `schoolbookMulLimbs.go`. -/
theorem schoolbookMulLimbs.go_size (a : Array UInt64) (loA lenA : Nat) (b : Array UInt64)
    (loB lenB : Nat) (acc : Array UInt64) (j : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (hAcc : lenA + lenB ≤ acc.size) :
    (schoolbookMulLimbs.go a loA lenA b loB lenB acc j hA hB hAcc).size = acc.size := by
  induction h_sub : lenB - j generalizing acc j with
  | zero =>
    have h_ge : lenB ≤ j := by omega
    rw [schoolbookMulLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : j < lenB := by omega
    have h_rec : lenB - (j + 1) = n := by omega
    rw [schoolbookMulLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ h_rec, Array.size_set, mulAddLimbs_size]

/-- Invariant of `schoolbookMulLimbs.go`: with the zero-tail invariant on `acc`
    (positions `[j+lenA, lenA+lenB)` of `acc` are zero), the low `lenA + lenB`
    limbs of the result equal `acc` plus `a_slice * b[loB+j:loB+lenB] * 2^(64j)`. -/
private lemma schoolbookMulLimbs.go_correct (a : Array UInt64) (loA lenA : Nat) (b : Array UInt64)
    (loB lenB : Nat) (acc : Array UInt64) (j : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (hAcc : lenA + lenB ≤ acc.size) (hj : j ≤ lenB)
    (h_zero : ∀ (i : Nat) (hi : i < acc.size), j + lenA ≤ i → i < lenA + lenB →
        acc[i]'hi = (0 : UInt64)) :
    toNatLimbsList
        ((schoolbookMulLimbs.go a loA lenA b loB lenB acc j hA hB hAcc).toList.take (lenA + lenB))
      = toNatLimbsList (acc.toList.take (lenA + lenB))
        + toNatLimbsList ((a.toList.drop loA).take lenA)
          * toNatLimbsList ((b.toList.drop (loB + j)).take (lenB - j))
          * 2 ^ (64 * j) := by
  induction h_sub : lenB - j generalizing acc j with
  | zero =>
    have h_ge : lenB ≤ j := by omega
    have h_eq : schoolbookMulLimbs.go a loA lenA b loB lenB acc j hA hB hAcc = acc := by
      rw [schoolbookMulLimbs.go]; simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : j < lenB := by omega
    have h_rec : lenB - (j + 1) = n := by omega
    have hBj : loB + j < b.size := by omega
    have hAcc_row : j + lenA ≤ acc.size := by omega
    set r := mulAddLimbs a loA lenA j b[loB + j] acc hA hAcc_row with hr_def
    have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
    have hCarryIdx : j + lenA < r.1.size := by rw [h_r_size]; omega
    set acc' := r.1.set (j + lenA) r.2 with hacc'_def
    have h_acc'_size : acc'.size = acc.size := by rw [hacc'_def, Array.size_set, h_r_size]
    have hAcc' : lenA + lenB ≤ acc'.size := by rw [h_acc'_size]; exact hAcc
    have h_eq_go : schoolbookMulLimbs.go a loA lenA b loB lenB acc j hA hB hAcc
                 = schoolbookMulLimbs.go a loA lenA b loB lenB acc' (j + 1) hA hB hAcc' := by
      conv_lhs => rw [schoolbookMulLimbs.go]
      simp [h_lt, hr_def, hacc'_def]
    have h_zero' : ∀ (i : Nat) (hi : i < acc'.size), (j + 1) + lenA ≤ i →
        i < lenA + lenB → acc'[i]'hi = (0 : UInt64) := by
      intro i hi hlo hhi
      have h_ne : i ≠ j + lenA := by omega
      have hi_r : i < r.1.size := by rw [h_r_size]; rw [h_acc'_size] at hi; exact hi
      have h_acc'_eq : acc'[i]'hi = r.1[i]'hi_r := Array.getElem_set_ne _ _ h_ne.symm
      rw [h_acc'_eq]
      have h_acc_i : i < acc.size := by rw [← h_r_size]; exact hi_r
      rw [mulAddLimbs_getElem_ge a loA lenA j b[loB + j] acc hA hAcc_row i (by omega) hi_r]
      exact h_zero i h_acc_i (by omega) hhi
    have hj' : j + 1 ≤ lenB := h_lt
    have h_ih := ih acc' (j + 1) hAcc' hj' h_zero' h_rec
    rw [h_eq_go, h_ih]
    -- Now prove: toNat(acc'.take(lenA+lenB)) + AS * P_{j+1} * 2^(64(j+1))
    --         = toNat(acc.take(lenA+lenB))  + AS * P_j     * 2^(64j)
    set AS := toNatLimbsList ((a.toList.drop loA).take lenA) with hAS_def
    have h_len_acc : acc.toList.length = acc.size := Array.length_toList
    have h_len_acc' : acc'.toList.length = acc.size := by
      rw [Array.length_toList, h_acc'_size]
    have h_len_r : r.1.toList.length = acc.size := by rw [Array.length_toList, h_r_size]
    have hj_le : j ≤ acc.toList.length := by rw [h_len_acc]; omega
    have hjlenA_le : j + lenA ≤ acc.toList.length := by rw [h_len_acc]; omega
    have hj_le' : j ≤ acc'.toList.length := by rw [h_len_acc']; omega
    have hjlenA_le' : j + lenA ≤ acc'.toList.length := by rw [h_len_acc']; omega
    -- Split toNat(acc.take(lenA+lenB)) = L + M * 2^(64j) + T * 2^(64(j+lenA))
    have h_len_eq : lenA + lenB = (j + lenA) + (lenB - j) := by omega
    have h_split_acc :
        toNatLimbsList (acc.toList.take (lenA + lenB))
          = toNatLimbsList (acc.toList.take (j + lenA))
            + toNatLimbsList ((acc.toList.drop (j + lenA)).take (lenB - j))
              * 2 ^ (64 * (j + lenA)) := by
      rw [h_len_eq]
      exact toNatLimbsList_take_add acc.toList (j + lenA) (lenB - j) hjlenA_le
    have h_split_acc_inner :
        toNatLimbsList (acc.toList.take (j + lenA))
          = toNatLimbsList (acc.toList.take j)
            + toNatLimbsList ((acc.toList.drop j).take lenA) * 2 ^ (64 * j) :=
      toNatLimbsList_take_add acc.toList j lenA hj_le
    have h_split_acc' :
        toNatLimbsList (acc'.toList.take (lenA + lenB))
          = toNatLimbsList (acc'.toList.take (j + lenA))
            + toNatLimbsList ((acc'.toList.drop (j + lenA)).take (lenB - j))
              * 2 ^ (64 * (j + lenA)) := by
      rw [h_len_eq]
      exact toNatLimbsList_take_add acc'.toList (j + lenA) (lenB - j) hjlenA_le'
    have h_split_acc'_inner :
        toNatLimbsList (acc'.toList.take (j + lenA))
          = toNatLimbsList (acc'.toList.take j)
            + toNatLimbsList ((acc'.toList.drop j).take lenA) * 2 ^ (64 * j) :=
      toNatLimbsList_take_add acc'.toList j lenA hj_le'
    -- Prefix equality: acc'.take j = acc.take j.
    have h_acc'_take_j :
        toNatLimbsList (acc'.toList.take j) = toNatLimbsList (acc.toList.take j) := by
      have h_list_eq : acc'.toList.take j = acc.toList.take j := by
        rw [hacc'_def, Array.toList_set, List.take_set_of_le (by omega)]
        exact mulAddLimbs.go_toList_take_le a loA lenA j b[loB + j] acc 0 0 hA hAcc_row j
          (by omega)
      rw [h_list_eq]
    -- Middle slice: acc'.drop(j).take(lenA) = r.1.drop(j).take(lenA).
    have h_acc'_mid :
        (acc'.toList.drop j).take lenA = (r.1.toList.drop j).take lenA := by
      rw [hacc'_def, Array.toList_set, List.drop_set]
      simp only [show ¬ j + lenA < j from by omega, ↓reduceIte]
      rw [List.take_set_of_le (by omega)]
    -- Middle slice toNat via mulAddLimbs_toNat.
    have h_mac := mulAddLimbs_toNat a loA lenA j b[loB + j] acc hA hAcc_row
    rw [show mulAddLimbs a loA lenA j b[loB + j] acc hA hAcc_row = r from hr_def.symm] at h_mac
    change AS * b[loB + j].toNat
        + toNatLimbsList ((acc.toList.drop j).take lenA)
      = toNatLimbsList ((r.1.toList.drop j).take lenA)
        + r.2.toNat * 2 ^ (64 * lenA) at h_mac
    -- Tail slice of acc: all zero.
    have h_tail_acc :
        toNatLimbsList ((acc.toList.drop (j + lenA)).take (lenB - j)) = 0 := by
      apply toNatLimbsList_eq_zero_of_all_zero
      intro i hi
      have h_len_le : ((acc.toList.drop (j + lenA)).take (lenB - j)).length ≤ lenB - j :=
        List.length_take_le _ _
      have h_i_lt_total : j + lenA + i < lenA + lenB := by omega
      have h_drop_len : (acc.toList.drop (j + lenA)).length = acc.size - (j + lenA) := by
        rw [List.length_drop, h_len_acc]
      have h_i_lt_drop : i < (acc.toList.drop (j + lenA)).length := by
        have hlt := hi
        rw [List.length_take] at hlt
        rw [h_drop_len]; omega
      have h_at : ((acc.toList.drop (j + lenA)).take (lenB - j))[i]
                = (acc.toList.drop (j + lenA))[i]'h_i_lt_drop := by
        rw [List.getElem_take]
      rw [h_at, List.getElem_drop]
      have h_idx_lt : j + lenA + i < acc.size := by
        have := h_i_lt_drop; rw [h_drop_len] at this; omega
      have h_arr : acc.toList[j + lenA + i]'(by rw [h_len_acc]; exact h_idx_lt)
                 = acc[j + lenA + i]'h_idx_lt := by
        rw [Array.getElem_toList]
      rw [h_arr]
      exact h_zero (j + lenA + i) h_idx_lt (by omega) h_i_lt_total
    -- Tail slice of acc': only r.2 at position 0 is nonzero (rest zero).
    -- acc'.drop(j+lenA) = r.2 :: r.1.drop(j+lenA+1) = r.2 :: acc.drop(j+lenA+1).
    have h_drop_r : r.1.toList.drop (j + lenA) = acc.toList.drop (j + lenA) :=
      mulAddLimbs.go_toList_drop a loA lenA j b[loB + j] acc 0 0 hA hAcc_row
    have h_jlenA_lt_r : j + lenA < r.1.toList.length := by rw [h_len_r]; omega
    have h_jlenA_lt_acc : j + lenA < acc.toList.length := by rw [h_len_acc]; omega
    have h_tail_acc' :
        toNatLimbsList ((acc'.toList.drop (j + lenA)).take (lenB - j)) = r.2.toNat := by
      have h_drop_succ : r.1.toList.drop (j + lenA + 1) = acc.toList.drop (j + lenA + 1) := by
        have h := congrArg (List.drop 1) h_drop_r
        simpa [List.drop_drop, Nat.add_comm 1] using h
      have h_form : (acc'.toList.drop (j + lenA)).take (lenB - j)
          = r.2 :: (acc.toList.drop (j + lenA + 1)).take (lenB - j - 1) := by
        rw [hacc'_def, Array.toList_set, List.drop_set]
        simp only [show ¬ j + lenA < j + lenA from lt_irrefl _, ↓reduceIte]
        rw [show j + lenA - (j + lenA) = 0 from by omega]
        rw [List.drop_eq_getElem_cons h_jlenA_lt_r, List.set_cons_zero]
        rw [show lenB - j = (lenB - j - 1) + 1 from by omega, List.take_succ_cons]
        rw [show lenB - j - 1 + 1 - 1 = lenB - j - 1 from by omega]
        rw [h_drop_succ]
      rw [h_form, toNatLimbsList_cons]
      have h_zero_tail :
          toNatLimbsList ((acc.toList.drop (j + lenA + 1)).take (lenB - j - 1)) = 0 := by
        apply toNatLimbsList_eq_zero_of_all_zero
        intro i hi
        have h_drop_len : (acc.toList.drop (j + lenA + 1)).length = acc.size - (j + lenA + 1) := by
          rw [List.length_drop, h_len_acc]
        have h_i_lt_drop : i < (acc.toList.drop (j + lenA + 1)).length := by
          have hlt := hi
          rw [List.length_take] at hlt
          rw [h_drop_len]; omega
        have h_i_lt_total : j + lenA + 1 + i < lenA + lenB := by
          have hlt := hi
          rw [List.length_take] at hlt
          omega
        have h_at : ((acc.toList.drop (j + lenA + 1)).take (lenB - j - 1))[i]
                  = (acc.toList.drop (j + lenA + 1))[i]'h_i_lt_drop := by
          rw [List.getElem_take]
        rw [h_at, List.getElem_drop]
        have h_idx_lt : j + lenA + 1 + i < acc.size := by
          have := h_i_lt_drop; rw [h_drop_len] at this; omega
        have h_arr : acc.toList[j + lenA + 1 + i]'(by rw [h_len_acc]; exact h_idx_lt)
                   = acc[j + lenA + 1 + i]'h_idx_lt := by rw [Array.getElem_toList]
        rw [h_arr]
        exact h_zero (j + lenA + 1 + i) h_idx_lt (by omega) h_i_lt_total
      rw [h_zero_tail]; simp
    -- Unfold P_j into b[loB+j] + P_{j+1} * 2^64.
    have hBj_len : loB + j < b.toList.length := by rw [Array.length_toList]; exact hBj
    have h_P_split : toNatLimbsList ((b.toList.drop (loB + j)).take (n + 1))
        = b[loB + j].toNat
          + toNatLimbsList ((b.toList.drop (loB + (j + 1))).take n) * 2 ^ 64 := by
      rw [List.drop_eq_getElem_cons hBj_len, List.take_succ_cons, toNatLimbsList_cons]
      have h_arr : b.toList[loB + j]'hBj_len = b[loB + j]'hBj := by rw [Array.getElem_toList]
      rw [h_arr, show loB + j + 1 = loB + (j + 1) from by ring]
      ring
    -- Assemble.
    rw [h_split_acc, h_split_acc_inner, h_split_acc', h_split_acc'_inner]
    rw [h_acc'_take_j, h_acc'_mid, h_tail_acc, h_tail_acc', h_P_split]
    -- Now it's pure arithmetic. Use h_mac.
    have h_pow1 : (2 : Nat) ^ (64 * (j + lenA)) = 2 ^ (64 * j) * 2 ^ (64 * lenA) := by
      rw [show 64 * (j + lenA) = 64 * j + 64 * lenA from by ring, Nat.pow_add]
    have h_pow2 : (2 : Nat) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by
      rw [show 64 * (j + 1) = 64 * j + 64 from by ring, Nat.pow_add]
    rw [h_pow1, h_pow2]
    have h_scaled := congrArg (· * 2 ^ (64 * j)) h_mac
    simp only at h_scaled
    linarith [h_scaled, Nat.add_mul (AS * b[loB + j].toNat)
      (toNatLimbsList (List.take lenA (List.drop j acc.toList))) (2 ^ (64 * j))]

/-- Correctness of `schoolbookMulLimbs` at the slice level. -/
theorem schoolbookMulLimbs_toNat (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (schoolbookMulLimbs a b loA lenA loB lenB hA hB).toList
      = toNatLimbsList ((a.toList.drop loA).take lenA)
        * toNatLimbsList ((b.toList.drop loB).take lenB) := by
  unfold schoolbookMulLimbs
  set acc0 : Array UInt64 := Array.replicate (lenA + lenB) 0 with hacc0_def
  have h_acc0_size : acc0.size = lenA + lenB := by rw [hacc0_def, Array.size_replicate]
  have hAcc0 : lenA + lenB ≤ acc0.size := by rw [h_acc0_size]
  have h_zero : ∀ (i : Nat) (hi : i < acc0.size), 0 + lenA ≤ i → i < lenA + lenB →
      acc0[i]'hi = (0 : UInt64) := by
    intro i hi _ _
    simp [hacc0_def, Array.getElem_replicate]
  have h_go := schoolbookMulLimbs.go_correct a loA lenA b loB lenB acc0 0 hA hB hAcc0
    (Nat.zero_le _) h_zero
  have h_go_size : (schoolbookMulLimbs.go a loA lenA b loB lenB acc0 0 hA hB hAcc0).size = lenA + lenB := by
    rw [schoolbookMulLimbs.go_size, h_acc0_size]
  have h_take_all :
      (schoolbookMulLimbs.go a loA lenA b loB lenB acc0 0 hA hB hAcc0).toList.take (lenA + lenB)
        = (schoolbookMulLimbs.go a loA lenA b loB lenB acc0 0 hA hB hAcc0).toList := by
    apply List.take_of_length_le
    rw [Array.length_toList, h_go_size]
  have h_acc0_zero : toNatLimbsList (acc0.toList.take (lenA + lenB)) = 0 := by
    rw [hacc0_def, Array.toList_replicate]
    rw [List.take_of_length_le (by rw [List.length_replicate])]
    clear h_go
    induction lenA + lenB with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp
  rw [h_take_all] at h_go
  rw [h_go, h_acc0_zero]
  simp

theorem toNat_mul (a b : AzNat) : (a * b).toNat = a.toNat * b.toNat := by
  show (mul a b).toNat = _
  unfold mul mulLimbs
  rw [toNat_ofLimbs, schoolbookMulLimbs_toNat]
  show toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)
        * toNatLimbsList ((b.limbs.toList.drop 0).take b.limbs.size) = a.toNat * b.toNat
  rw [List.drop_zero, List.drop_zero]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rw [List.take_of_length_le (by rw [Array.length_toList])]
  rfl

/-- `ofNat`-version of `toNat_mulUInt64`. -/
theorem ofNat_mulUInt64 (n : Nat) (b : UInt64) :
    ofNat (n * b.toNat) = (ofNat n).mulUInt64 b := by
  have h : (ofNat (n * b.toNat)).toNat = ((ofNat n).mulUInt64 b).toNat := by
    rw [toNat_ofNat, toNat_mulUInt64, toNat_ofNat]
  have := congrArg ofNat h
  rwa [ofNat_toNat, ofNat_toNat] at this

/-- `ofNat`-version of `toNat_mul`. -/
theorem ofNat_mul (m n : Nat) : ofNat (m * n) = ofNat m * ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_mul, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
