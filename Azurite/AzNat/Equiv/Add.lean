import Azurite.AzNat.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.AddWithCarry

namespace Azurite.AzNat

lemma toNatLimbsList_take_succ (a : Array UInt64) (i hi : Nat)
    (h : i < a.size) (hi_lt : i + 1 ≤ hi) :
    toNatLimbsList ((a.toList.drop i).take (hi - i))
      = a[i].toNat + toNatLimbsList ((a.toList.drop (i + 1)).take (hi - (i + 1))) * 2 ^ 64 := by
  have h_len : a.toList.length = a.size := rfl
  have h_lt_list : i < a.toList.length := by rw [h_len]; exact h
  rw [List.drop_eq_getElem_cons h_lt_list]
  have h_sub : hi - i = (hi - (i + 1)) + 1 := by omega
  rw [h_sub, List.take_succ_cons, toNatLimbsList_cons]
  rw [show a.toList[i] = a[i] from (Array.getElem_toList h).symm]
  ring

/-- `addLimb.go` preserves the prefix `[0, i)`. -/
theorem addLimb.go_toList_take (hi : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) :
    (addLimb.go hi a i carry h_size).1.toList.take i = a.toList.take i := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [addLimb.go]
    by_cases hc : carry = 0
    · simp [hc]
    · simp [hc, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    rw [addLimb.go]
    by_cases hc : carry = 0
    · simp [hc]
    · simp only [hc, ↓reduceIte, h_lt, ↓reduceDIte]
      have h_rec : hi - (i + 1) = n := by omega
      set sum := a[i] + carry with hsum_def
      set newCarry : UInt64 := if a[i] + carry < carry then 1 else 0 with hnc_def
      have h_take_succ : List.take i
          ((addLimb.go hi (a.set i sum) (i + 1) newCarry
              (by rw [Array.size_set]; exact h_size)).1.toList.take (i + 1))
            = (addLimb.go hi (a.set i sum) (i + 1) newCarry
                (by rw [Array.size_set]; exact h_size)).1.toList.take i := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [← h_take_succ, ih _ _ _ _ h_rec, List.take_take, Nat.min_eq_left (by omega)]
      rw [Array.toList_set, List.take_set]
      rw [List.set_eq_of_length_le]
      rw [List.length_take, Array.length_toList]
      omega

/-- `addLimb` preserves the prefix `[0, lo)`. -/
theorem addLimb_toList_take (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (addLimb a lo hi b hlo hhi).1.toList.take lo = a.toList.take lo :=
  addLimb.go_toList_take hi a lo b hhi

/-- Single-limb add step: adding a carry to a UInt64 produces a sum and a
    carry-out bit that together preserve the numerical value. -/
lemma limb_add_step (x carry : UInt64) :
    (x + carry).toNat
        + (if x + carry < carry then (1 : UInt64) else 0).toNat * 2 ^ 64
      = x.toNat + carry.toNat := by
  have hxlt : x.toNat < 2 ^ 64 := UInt64.toNat_lt x
  have hclt : carry.toNat < 2 ^ 64 := UInt64.toNat_lt carry
  have h_add : (x + carry).toNat = (x.toNat + carry.toNat) % 2 ^ 64 :=
    UInt64.toNat_add x carry
  have h_iff : x + carry < carry ↔ x.toNat + carry.toNat ≥ 2 ^ 64 := by
    rw [UInt64.lt_iff_toNat_lt, h_add]
    constructor
    · intro h
      by_contra h_lt
      push Not at h_lt
      rw [Nat.mod_eq_of_lt h_lt] at h
      omega
    · intro h_ge
      have : (x.toNat + carry.toNat) % 2 ^ 64
              = x.toNat + carry.toNat - 2 ^ 64 := by
        rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt (by omega)]
      rw [this]; omega
  by_cases h_ovf : x + carry < carry
  · have h_ge : x.toNat + carry.toNat ≥ 2 ^ 64 := h_iff.mp h_ovf
    have h_mod : (x.toNat + carry.toNat) % 2 ^ 64
                  = x.toNat + carry.toNat - 2 ^ 64 := by
      rw [Nat.mod_eq_sub_mod h_ge, Nat.mod_eq_of_lt (by omega)]
    simp only [h_ovf, ↓reduceIte]
    show (x + carry).toNat + 1 * 2 ^ 64 = x.toNat + carry.toNat
    rw [h_add, h_mod]; omega
  · have h_lt : x.toNat + carry.toNat < 2 ^ 64 := by
      by_contra h_ge
      push Not at h_ge
      exact h_ovf (h_iff.mpr h_ge)
    simp only [h_ovf, ↓reduceIte]
    show (x + carry).toNat + 0 * 2 ^ 64 = x.toNat + carry.toNat
    rw [h_add, Nat.mod_eq_of_lt h_lt]; ring

/-- Invariant of `addLimb.go`: starting from `(a, i, carry)`, the resulting
    modified slice `[i, hi)` together with the final carry bit at position
    `hi` equals the original slice plus the incoming `carry` at position `i`.
    Valid whenever `carry ≤ 1` or the loop can still advance. -/
private lemma addLimb.go_correct (hi : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size)
    (hcarry : carry.toNat ≤ 1 ∨ i < hi) :
    toNatLimbsList (((addLimb.go hi a i carry h_size).1.toList.drop i).take (hi - i))
      + (addLimb.go hi a i carry h_size).2.toNat * 2 ^ (64 * (hi - i))
      = toNatLimbsList ((a.toList.drop i).take (hi - i)) + carry.toNat := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    by_cases hc : carry = 0
    · have h_eq : addLimb.go hi a i carry h_size = (a, false) := by
        conv_lhs => rw [addLimb.go]
        simp [hc]
      rw [h_eq, hc]
      simp [toNatLimbsList]
    · have h_carry_ne : carry.toNat ≠ 0 := by
        intro h
        exact hc (UInt64.toNat_inj.mp (show carry.toNat = (0 : UInt64).toNat from h))
      have h_carry_le : carry.toNat ≤ 1 :=
        hcarry.resolve_right (fun h => absurd h (Nat.not_lt.mpr h_ge))
      have h_carry_eq : carry.toNat = 1 := by omega
      have h_eq : addLimb.go hi a i carry h_size = (a, true) := by
        conv_lhs => rw [addLimb.go]
        simp [hc, Nat.not_lt.mpr h_ge]
      rw [h_eq]
      simp [toNatLimbsList, h_carry_eq]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    by_cases hc : carry = 0
    · have h_eq : addLimb.go hi a i carry h_size = (a, false) := by
        conv_lhs => rw [addLimb.go]
        simp [hc]
      rw [h_eq, hc]
      simp [toNatLimbsList]
    · set x := a[i] with hx_def
      set sum := x + carry with hsum_def
      set newCarry : UInt64 := if sum < carry then 1 else 0 with hnc_def
      set a' := a.set i sum h_i_size with ha'_def
      have h_size' : hi ≤ a'.size := by rw [ha'_def, Array.size_set]; exact h_size
      have h_eq : addLimb.go hi a i carry h_size
                  = addLimb.go hi a' (i + 1) newCarry h_size' := by
        conv_lhs => rw [addLimb.go]
        simp [hc, h_lt, hx_def, hsum_def, hnc_def, ha'_def]
      -- IH setup
      have h_rec : hi - (i + 1) = n := by omega
      have h_nc_le : newCarry.toNat ≤ 1 := by
        rw [hnc_def]
        by_cases hovf : sum < carry
        · simp [hovf]
        · simp [hovf]
      have h_ih := ih a' (i + 1) newCarry h_size' (Or.inl h_nc_le) h_rec
      -- limb step
      have h_limb : sum.toNat + newCarry.toNat * 2 ^ 64 = x.toNat + carry.toNat := by
        rw [hsum_def, hnc_def]
        exact limb_add_step x carry
      -- position i of final array = sum
      have h_res_size :
          (addLimb.go hi a' (i + 1) newCarry h_size').1.size = a.size := by
        rw [addLimb.go_size, ha'_def, Array.size_set]
      have h_res_i_size : i < (addLimb.go hi a' (i + 1) newCarry h_size').1.size := by
        rw [h_res_size]; exact h_i_size
      have h_res_i : (addLimb.go hi a' (i + 1) newCarry h_size').1[i]'h_res_i_size
                      = sum := by
        have h_prefix :=
          addLimb.go_toList_take hi a' (i + 1) newCarry h_size'
        have h_len_L : ((addLimb.go hi a' (i + 1) newCarry h_size').1.toList).length = a.size := by
          rw [Array.length_toList]; exact h_res_size
        have h_i_lt_L_take :
            i < ((addLimb.go hi a' (i + 1) newCarry h_size').1.toList.take (i + 1)).length := by
          rw [List.length_take, h_len_L]; omega
        have h_i_lt_R_take : i < (a'.toList.take (i + 1)).length := by
          rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
        have h_get_eq :
            ((addLimb.go hi a' (i + 1) newCarry h_size').1.toList.take (i + 1))[i]'h_i_lt_L_take
              = (a'.toList.take (i + 1))[i]'h_i_lt_R_take := by
          congr 1
        rw [List.getElem_take, List.getElem_take] at h_get_eq
        rw [← Array.getElem_toList h_res_i_size, h_get_eq]
        have h_i_lt : i < (a.set i sum h_i_size).toList.length := by
          rw [Array.length_toList, Array.size_set]; exact h_i_size
        show (a.set i sum h_i_size).toList[i]'h_i_lt = sum
        simp [Array.toList_set, List.getElem_set_self]
      have h_drop_eq : a'.toList.drop (i + 1) = a.toList.drop (i + 1) := by
        rw [ha'_def, Array.toList_set, List.drop_set]; simp
      rw [h_eq]
      rw [show (n + 1) = hi - i from hi_sub_i.symm]
      rw [toNatLimbsList_take_succ (addLimb.go hi a' (i + 1) newCarry h_size').1 i hi
            h_res_i_size h_lt]
      rw [h_res_i]
      rw [toNatLimbsList_take_succ a i hi h_i_size h_lt]
      have h_pow : (2 : Nat) ^ (64 * (hi - i))
                  = 2 ^ (64 * (hi - (i + 1))) * 2 ^ 64 := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h_pow]
      rw [← h_drop_eq]
      -- Now pull n back to hi - (i + 1) in the IH
      rw [← h_rec] at h_ih
      set P := toNatLimbsList
          (((addLimb.go hi a' (i + 1) newCarry h_size').1.toList.drop (i + 1)).take (hi - (i + 1)))
        with hP_def
      set Q := toNatLimbsList ((a'.toList.drop (i + 1)).take (hi - (i + 1))) with hQ_def
      set R := (addLimb.go hi a' (i + 1) newCarry h_size').2.toNat with hR_def
      change sum.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
           = x.toNat + Q * 2 ^ 64 + carry.toNat
      have h1 : sum.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
              = sum.toNat + (P + R * 2 ^ (64 * (hi - (i + 1)))) * 2 ^ 64 := by ring
      rw [h1, h_ih]
      have h2 : sum.toNat + (Q + newCarry.toNat) * 2 ^ 64
              = (sum.toNat + newCarry.toNat * 2 ^ 64) + Q * 2 ^ 64 := by ring
      rw [h2, h_limb]
      ring

/-- Correctness of `addLimb`: the modified slice `[lo, hi)` plus the returned
    carry at the top represent the original slice plus `b.toNat`. -/
theorem addLimb_toNat (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (h_lo_lt : lo < hi) :
    let (a', c) := addLimb a lo hi b hlo hhi
    toNatLimbsList ((a'.toList.drop lo).take (hi - lo))
        + c.toNat * 2 ^ (64 * (hi - lo))
      = toNatLimbsList ((a.toList.drop lo).take (hi - lo)) + b.toNat := by
  have h := addLimb.go_correct hi a lo b hhi (Or.inr h_lo_lt)
  simp at h
  exact h

/-- Correctness of `AzNat.addUInt64`: agrees with `Nat` addition. -/
theorem toNat_addUInt64 (a : AzNat) (b : UInt64) :
    (a.addUInt64 b).toNat = a.toNat + b.toNat := by
  unfold addUInt64
  by_cases hsz : a.limbs.size = 0
  · have h_nil : a.limbs.toList = [] := by
      have : a.limbs.toList.length = 0 := hsz
      exact List.length_eq_zero_iff.mp this
    have h_a_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      rw [h_nil]; rfl
    simp [hsz, UInt64.toNat_toAzNat, h_a_zero]
  · simp only [hsz]
    set n := a.limbs.size with hn_def
    have h_pos : 0 < n := Nat.pos_of_ne_zero hsz
    have h_size : (addLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.size = n :=
      addLimb_size a.limbs 0 n b _ _
    have h_main := addLimb_toNat a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _) h_pos
    simp only [List.drop_zero, Nat.sub_zero] at h_main
    have h_take_arr : a.limbs.toList.take n = a.limbs.toList := by
      rw [List.take_of_length_le]; rw [Array.length_toList]
    have h_take_r : (addLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList.take n
                  = (addLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList := by
      rw [List.take_of_length_le]; rw [Array.length_toList, h_size]
    rw [h_take_arr, h_take_r] at h_main
    -- h_main : toNatLimbsList r.1.toList + r.2.toNat * 2^(64*n) = a.toNat + b.toNat
    set r := addLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)
    have h_a : a.toNat = toNatLimbsList a.limbs.toList := rfl
    rcases hc : r.2 with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [toNat_ofLimbs]
      rw [hc] at h_main
      simp at h_main
      rw [h_a]; exact h_main
    · simp only [↓reduceIte]
      rw [toNat_ofLimbs, Array.toList_push, toNatLimbsList_append]
      have h_len : r.1.toList.length = n := by rw [Array.length_toList]; exact h_size
      rw [h_len]
      have h_one : toNatLimbsList [(1 : UInt64)] = 1 := by simp [toNatLimbsList]
      rw [h_one]
      rw [hc] at h_main
      change _ + 1 * 2 ^ (64 * n) = _ at h_main
      rw [h_a]; omega

/-! ### Correctness of `addSameLengthLimbs` -/

/-- `addSameLengthLimbs.go` preserves any prefix up to `loA + k`. -/
theorem addSameLengthLimbs.go_toList_take_le (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size)
    (m : Nat) (hm : m ≤ loA + k) :
    (addSameLengthLimbs.go b loA loB len a k carry hA hB).1.toList.take m
      = a.toList.take m := by
  induction h_sub : len - k generalizing a k carry with
  | zero =>
    have h_ge : len ≤ k := by omega
    rw [addSameLengthLimbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    have h_rec : len - (k + 1) = n := by omega
    rw [addSameLengthLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega) h_rec]
    rw [Array.toList_set, List.take_set_of_le (by omega)]

/-- `addSameLengthLimbs.go` preserves the prefix of `a` up to `loA + k`. -/
theorem addSameLengthLimbs.go_toList_take (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (addSameLengthLimbs.go b loA loB len a k carry hA hB).1.toList.take (loA + k)
      = a.toList.take (loA + k) :=
  addSameLengthLimbs.go_toList_take_le b loA loB len a k carry hA hB (loA + k) (Nat.le_refl _)

/-- `addSameLengthLimbs.go` preserves the suffix of `a` from `loA + len`. -/
theorem addSameLengthLimbs.go_toList_drop (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (addSameLengthLimbs.go b loA loB len a k carry hA hB).1.toList.drop (loA + len)
      = a.toList.drop (loA + len) := by
  induction h_sub : len - k generalizing a k carry with
  | zero =>
    have h_ge : len ≤ k := by omega
    rw [addSameLengthLimbs.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    rw [addSameLengthLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    have h_rec : len - (k + 1) = n := by omega
    rw [ih _ _ _ _ h_rec]
    rw [Array.toList_set, List.drop_set]
    simp
    omega

/-- Invariant of `addSameLengthLimbs.go` at step `k`. -/
private lemma addSameLengthLimbs.go_correct (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList
        (((addSameLengthLimbs.go b loA loB len a k carry hA hB).1.toList.drop (loA + k)).take
          (len - k))
      + (addSameLengthLimbs.go b loA loB len a k carry hA hB).2.toNat * 2 ^ (64 * (len - k))
      = toNatLimbsList ((a.toList.drop (loA + k)).take (len - k))
        + toNatLimbsList ((b.toList.drop (loB + k)).take (len - k))
        + carry.toNat := by
  induction h_sub : len - k generalizing a k carry with
  | zero =>
    have h_ge : len ≤ k := by omega
    have h_eq : addSameLengthLimbs.go b loA loB len a k carry hA hB = (a, carry) := by
      rw [addSameLengthLimbs.go]
      simp [Nat.not_lt.mpr h_ge]
    rw [h_eq]
    simp [toNatLimbsList]
  | succ n ih =>
    have h_lt : k < len := by omega
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    set awc := UInt64.addWithCarry a[loA + k] b[loB + k] carry with hawc_def
    set sum := awc.1 with hsum_def
    set newCarry := awc.2 with hnc_def
    set a' := a.set (loA + k) sum h_iA with ha'_def
    have hA' : loA + len ≤ a'.size := by rw [ha'_def, Array.size_set]; exact hA
    have h_eq : addSameLengthLimbs.go b loA loB len a k carry hA hB
              = addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB := by
      conv_lhs => rw [addSameLengthLimbs.go]
      simp [h_lt, hawc_def, hsum_def, hnc_def, ha'_def]
    have h_rec : len - (k + 1) = n := by omega
    have h_ih := ih a' (k + 1) newCarry hA' h_rec
    -- AWC equation
    have h_awc := UInt64.addWithCarry_eq a[loA + k] b[loB + k] carry
    rw [← hawc_def] at h_awc
    -- position loA + k of final array = sum
    have h_res_size :
        (addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1.size = a.size := by
      rw [addSameLengthLimbs.go_size, ha'_def, Array.size_set]
    have h_res_iA_size :
        loA + k < (addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1.size := by
      rw [h_res_size]; exact h_iA
    have h_res_i :
        (addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1[loA + k]'h_res_iA_size
          = sum := by
      have h_prefix :=
        addSameLengthLimbs.go_toList_take b loA loB len a' (k + 1) newCarry hA' hB
      have h_len_L :
          ((addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1.toList).length
            = a.size := by rw [Array.length_toList]; exact h_res_size
      have h_i_lt_L_take :
          loA + k
            < ((addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1.toList.take
                (loA + (k + 1))).length := by
        rw [List.length_take, h_len_L]; omega
      have h_i_lt_R_take : loA + k < (a'.toList.take (loA + (k + 1))).length := by
        rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
      have h_get_eq :
          ((addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1.toList.take
              (loA + (k + 1)))[loA + k]'h_i_lt_L_take
            = (a'.toList.take (loA + (k + 1)))[loA + k]'h_i_lt_R_take := by
        congr 1
      rw [List.getElem_take, List.getElem_take] at h_get_eq
      rw [← Array.getElem_toList h_res_iA_size, h_get_eq]
      have h_i_lt : loA + k < (a.set (loA + k) sum h_iA).toList.length := by
        rw [Array.length_toList, Array.size_set]; exact h_iA
      show (a.set (loA + k) sum h_iA).toList[loA + k]'h_i_lt = sum
      simp [Array.toList_set, List.getElem_set_self]
    have h_drop_eq : a'.toList.drop (loA + (k + 1)) = a.toList.drop (loA + (k + 1)) := by
      rw [ha'_def, Array.toList_set, List.drop_set]; simp
    rw [h_eq]
    -- Split each toNatLimbsList((drop i).take (m + 1)) using a local succ lemma.
    have split_arr : ∀ (A : Array UInt64) (i m : Nat) (hi_size : i < A.size),
        toNatLimbsList ((A.toList.drop i).take (m + 1))
          = A[i].toNat + toNatLimbsList ((A.toList.drop (i + 1)).take m) * 2 ^ 64 := by
      intro A i m hi_size
      have h_lt_list : i < A.toList.length := hi_size
      rw [List.drop_eq_getElem_cons h_lt_list, List.take_succ_cons, toNatLimbsList_cons]
      rw [show A.toList[i] = A[i] from (Array.getElem_toList hi_size).symm]
      ring
    have h_len_split : len - k = (len - (k + 1)) + 1 := by omega
    rw [show (n + 1) = len - k from h_sub.symm, h_len_split]
    rw [split_arr
          (addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1
          (loA + k) (len - (k + 1)) h_res_iA_size]
    rw [h_res_i]
    rw [split_arr a (loA + k) (len - (k + 1)) h_iA]
    rw [split_arr b (loB + k) (len - (k + 1)) h_iB]
    have h_pow : (2 : Nat) ^ (64 * ((len - (k + 1)) + 1))
                = 2 ^ (64 * (len - (k + 1))) * 2 ^ 64 := by
      rw [show 64 * ((len - (k + 1)) + 1) = 64 * (len - (k + 1)) + 64 from by ring, Nat.pow_add]
    rw [h_pow]
    rw [show loA + k + 1 = loA + (k + 1) from by ring]
    rw [show loB + k + 1 = loB + (k + 1) from by ring]
    rw [← h_drop_eq]
    rw [← h_rec] at h_ih
    set P := toNatLimbsList
        (((addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).1.toList.drop
            (loA + (k + 1))).take (len - (k + 1))) with hP_def
    set Q := toNatLimbsList ((a'.toList.drop (loA + (k + 1))).take (len - (k + 1))) with hQ_def
    set S := toNatLimbsList ((b.toList.drop (loB + (k + 1))).take (len - (k + 1))) with hS_def
    set R := (addSameLengthLimbs.go b loA loB len a' (k + 1) newCarry hA' hB).2.toNat with hR_def
    change sum.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (len - (k + 1))) * 2 ^ 64)
         = a[loA + k].toNat + Q * 2 ^ 64
           + (b[loB + k].toNat + S * 2 ^ 64) + carry.toNat
    have h1 : sum.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (len - (k + 1))) * 2 ^ 64)
            = sum.toNat + (P + R * 2 ^ (64 * (len - (k + 1)))) * 2 ^ 64 := by ring
    rw [h1, h_ih]
    have h_limb : sum.toNat + (if newCarry then 1 else 0) * 2 ^ 64
                = a[loA + k].toNat + b[loB + k].toNat + (if carry then 1 else 0) := by
      rw [hsum_def, hnc_def]; omega
    have h_cN : newCarry.toNat = (if newCarry then 1 else 0) := by cases newCarry <;> simp
    have h_c : carry.toNat = (if carry then 1 else 0) := by cases carry <;> simp
    rw [h_cN, h_c]
    have goal_eq : sum.toNat + (Q + S + (if newCarry = true then 1 else 0)) * 2 ^ 64
                = (sum.toNat + (if newCarry = true then 1 else 0) * 2 ^ 64)
                  + Q * 2 ^ 64 + S * 2 ^ 64 := by ring
    rw [goal_eq, h_limb]
    ring

/-- Correctness of `addSameLengthLimbs`: sum of corresponding subranges equals
    modified-`a` subrange plus final carry at the top. -/
theorem addSameLengthLimbs_toNat (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    let (a', c) := addSameLengthLimbs a b loA loB len hA hB
    toNatLimbsList ((a'.toList.drop loA).take len) + c.toNat * 2 ^ (64 * len)
      = toNatLimbsList ((a.toList.drop loA).take len)
        + toNatLimbsList ((b.toList.drop loB).take len) := by
  have h := addSameLengthLimbs.go_correct b loA loB len a 0 false hA hB
  simpa using h

/-! ### Correctness of `addGeqLimbs` -/

/-- Splitting helper: a slice of length `lenA = lenB + (lenA - lenB)` decomposes
    into a low part of length `lenB` and a high part of length `lenA - lenB`. -/
lemma toNatLimbsList_drop_take_split (arr : Array UInt64)
    (lo lenA lenB : Nat) (h_ge : lenB ≤ lenA) (h_bound : lo + lenA ≤ arr.size) :
    toNatLimbsList ((arr.toList.drop lo).take lenA)
      = toNatLimbsList ((arr.toList.drop lo).take lenB)
        + toNatLimbsList ((arr.toList.drop (lo + lenB)).take (lenA - lenB)) * 2 ^ (64 * lenB) := by
  have h_split : (arr.toList.drop lo).take lenA
      = (arr.toList.drop lo).take lenB
        ++ (arr.toList.drop (lo + lenB)).take (lenA - lenB) := by
    conv_lhs => rw [show lenA = lenB + (lenA - lenB) from by omega]
    rw [List.take_add, List.drop_drop]
  rw [h_split, toNatLimbsList_append]
  have h_len : ((arr.toList.drop lo).take lenB).length = lenB := by
    rw [List.length_take, List.length_drop, Array.length_toList]
    omega
  rw [h_len, Nat.add_comm]

/-- Correctness of `addGeqLimbs`: agrees with `Nat` addition over the slices. -/
theorem addGeqLimbs_toNat (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB) :
    let (a', c) := addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB
    toNatLimbsList ((a'.toList.drop loA).take lenA) + c.toNat * 2 ^ (64 * lenA)
      = toNatLimbsList ((a.toList.drop loA).take lenA)
        + toNatLimbsList ((b.toList.drop loB).take lenB) := by
  set lo := addSameLengthLimbs a b loA loB lenB (by omega) hB with hlo_def
  have h_lo_size : lo.1.size = a.size := by
    rw [hlo_def]; exact addSameLengthLimbs_size a b loA loB lenB _ _
  have h_unfold : addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB =
      if lo.2 then addLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                    (by rw [h_lo_size]; exact hA)
              else (lo.1, false) := rfl
  show toNatLimbsList ((((addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1.toList).drop loA).take lenA)
        + (addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).2.toNat * 2 ^ (64 * lenA)
      = toNatLimbsList ((a.toList.drop loA).take lenA)
        + toNatLimbsList ((b.toList.drop loB).take lenB)
  rw [h_unfold]
  have h_low := addSameLengthLimbs_toNat a b loA loB lenB (by omega) hB
  rw [← hlo_def] at h_low
  simp only at h_low
  -- High slice of lo.1 is unchanged
  have h_high_unchanged :
      (lo.1.toList.drop (loA + lenB)).take (lenA - lenB)
        = (a.toList.drop (loA + lenB)).take (lenA - lenB) := by
    rw [hlo_def]
    show (((addSameLengthLimbs.go b loA loB lenB a 0 false _ _).1.toList).drop _).take _ = _
    have h_drop_eq :
        (addSameLengthLimbs.go b loA loB lenB a 0 false (by omega) hB).1.toList.drop
            (loA + lenB)
          = a.toList.drop (loA + lenB) :=
      addSameLengthLimbs.go_toList_drop b loA loB lenB a 0 false (by omega) hB
    have h_take_split :
        ((addSameLengthLimbs.go b loA loB lenB a 0 false (by omega) hB).1.toList.drop
            (loA + lenB)).take (lenA - lenB)
          = (a.toList.drop (loA + lenB)).take (lenA - lenB) := by
      rw [h_drop_eq]
    exact h_take_split
  -- Case split on lenB < lenA (needed for addLimb_toNat) vs lenA = lenB
  by_cases h_lt : lenB < lenA
  swap
  · have h_eq : lenA = lenB := by omega
    -- addLimb on empty range with nonzero carry returns (lo.1, true)
    have h_addLimb_empty : addLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                           (by rw [h_lo_size]; exact hA) = (lo.1, true) := by
      unfold addLimb addLimb.go
      simp [show ¬ (loA + lenB < loA + lenA) from by omega]
    -- The if-expression collapses to (lo.1, lo.2)
    have h_result :
        (if lo.2 then addLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                        (by rw [h_lo_size]; exact hA) else (lo.1, false))
          = (lo.1, lo.2) := by
      by_cases hc : lo.2 = true
      · rw [if_pos hc, h_addLimb_empty, hc]
      · have hcf : lo.2 = false := by cases h : lo.2 <;> simp_all
        rw [hcf]; rfl
    rw [h_result]
    rw [h_eq]
    exact h_low
  -- Splittings of LHS and RHS
  rw [toNatLimbsList_drop_take_split a loA lenA lenB h_ge hA]
  by_cases hc : lo.2 = true
  · simp only [hc, ↓reduceIte]
    set hi := addLimb lo.1 (loA + lenB) (loA + lenA) 1
              (by omega) (by rw [h_lo_size]; exact hA) with hhi_def
    have h_high := addLimb_toNat lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
                    (by rw [h_lo_size]; exact hA) (by omega)
    rw [← hhi_def] at h_high
    simp only at h_high
    -- Slice [loA+lenB, loA+lenA) length is lenA - lenB
    have h_len_sub : loA + lenA - (loA + lenB) = lenA - lenB := by omega
    rw [h_len_sub] at h_high
    -- The low slice of hi.1 = the low slice of lo.1
    have h_hi_low :
        (hi.1.toList.drop loA).take lenB = (lo.1.toList.drop loA).take lenB := by
      have h_take :=
        addLimb_toList_take lo.1 (loA + lenB) (loA + lenA) 1
          (by omega) (by rw [h_lo_size]; exact hA)
      rw [← hhi_def] at h_take
      rw [show lenB = (loA + lenB) - loA from by omega,
          ← List.drop_take, ← List.drop_take, h_take]
    -- Split LHS
    have h_hi_size : hi.1.size = a.size := by
      rw [hhi_def, addLimb_size, h_lo_size]
    rw [toNatLimbsList_drop_take_split hi.1 loA lenA lenB h_ge (by rw [h_hi_size]; exact hA)]
    rw [h_hi_low]
    -- Pow split
    have h_pow : (2 : Nat) ^ (64 * lenA)
                = 2 ^ (64 * (lenA - lenB)) * 2 ^ (64 * lenB) := by
      rw [← Nat.pow_add]; congr 1
      rw [show 64 * (lenA - lenB) + 64 * lenB = 64 * lenA from by
        rw [← Nat.mul_add]; congr 1; omega]
    rw [h_pow]
    -- Now use h_high to rewrite the high part of hi.1
    -- h_high : toNatLimbsList ((hi.1.drop (loA+lenB)).take (lenA-lenB)) + hi.2.toNat * 2^(64*(lenA-lenB))
    --          = toNatLimbsList ((lo.1.drop (loA+lenB)).take (lenA-lenB)) + 1.toNat
    have h1_toNat : (1 : UInt64).toNat = 1 := rfl
    rw [h1_toNat] at h_high
    -- Rewrite low-of-lo.1 using h_low (carry = 1)
    have h_lo_carry : lo.2.toNat = 1 := by rw [hc]; rfl
    rw [h_lo_carry] at h_low
    -- Goal manipulation
    set L1 := toNatLimbsList ((hi.1.toList.drop (loA + lenB)).take (lenA - lenB)) with hL1
    set L2 := toNatLimbsList ((lo.1.toList.drop (loA + lenB)).take (lenA - lenB)) with hL2
    set Lalow := toNatLimbsList ((lo.1.toList.drop loA).take lenB) with hLalow
    set Aorig := toNatLimbsList ((a.toList.drop loA).take lenB) with hAorig
    set Ahi := toNatLimbsList ((a.toList.drop (loA + lenB)).take (lenA - lenB)) with hAhi
    set Bs := toNatLimbsList ((b.toList.drop loB).take lenB) with hBs
    have hL2_eq : L2 = Ahi := by rw [hL2, hAhi, h_high_unchanged]
    rw [hL2_eq] at h_high
    -- h_low : Lalow + 1 * 2^(64*lenB) = Aorig + Bs
    -- h_high : L1 + hi.2.toNat * 2^(64*(lenA-lenB)) = Ahi + 1
    -- Goal: Lalow + L1 * 2^(64*lenB) + hi.2.toNat * (2^(64*(lenA-lenB)) * 2^(64*lenB))
    --       = Aorig + Ahi * 2^(64*lenB) + Bs
    have step1 :
        Lalow + L1 * 2 ^ (64 * lenB) + hi.2.toNat * (2 ^ (64 * (lenA - lenB)) * 2 ^ (64 * lenB))
          = Lalow + (L1 + hi.2.toNat * 2 ^ (64 * (lenA - lenB))) * 2 ^ (64 * lenB) := by ring
    rw [step1, h_high]
    have step2 :
        Lalow + (Ahi + 1) * 2 ^ (64 * lenB)
          = (Lalow + 1 * 2 ^ (64 * lenB)) + Ahi * 2 ^ (64 * lenB) := by ring
    rw [step2, h_low]
    ring
  · have hc' : lo.2 = false := by cases h : lo.2 <;> simp_all
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    -- Result is (lo.1, false), goal carry term is zero
    rw [toNatLimbsList_drop_take_split lo.1 loA lenA lenB h_ge (by rw [h_lo_size]; exact hA)]
    have h_low_low :
        toNatLimbsList ((lo.1.toList.drop (loA + lenB)).take (lenA - lenB))
          = toNatLimbsList ((a.toList.drop (loA + lenB)).take (lenA - lenB)) := by
      rw [h_high_unchanged]
    rw [h_low_low]
    rw [hc'] at h_low
    have h_zero : (false : Bool).toNat = 0 := rfl
    rw [h_zero] at h_low
    -- h_low : toNatLimbsList ((lo.1.drop loA).take lenB) + 0 = aLow + bSlice
    simp only [Nat.zero_mul, Nat.add_zero] at h_low
    rw [h_low, h_zero]
    ring

/-- Correctness of `addLimbs`: dispatches to `addGeqLimbs` based on which slice
    is longer; the result is read out at the offset of the longer slice. -/
theorem addLimbs_toNat (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_posA : 0 < lenA) (h_posB : 0 < lenB) :
    let (r, c) := addLimbs a b loA lenA loB lenB hA hB h_posA h_posB
    let lenMax := max lenA lenB
    let loMax := if lenB ≤ lenA then loA else loB
    toNatLimbsList ((r.toList.drop loMax).take lenMax) + c.toNat * 2 ^ (64 * lenMax)
      = toNatLimbsList ((a.toList.drop loA).take lenA)
        + toNatLimbsList ((b.toList.drop loB).take lenB) := by
  unfold addLimbs
  by_cases h : lenB ≤ lenA
  · rw [show (max lenA lenB) = lenA from Nat.max_eq_left h,
        show (if lenB ≤ lenA then loA else loB) = loA from if_pos h]
    simp only [h, ↓reduceDIte]
    exact addGeqLimbs_toNat a b loA lenA loB lenB hA hB h h_posA h_posB
  · rw [show (max lenA lenB) = lenB from Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h)),
        show (if lenB ≤ lenA then loA else loB) = loB from if_neg h]
    simp only [h, ↓reduceDIte]
    have := addGeqLimbs_toNat b a loB lenB loA lenA hB hA (by omega) h_posB h_posA
    simp only at this ⊢
    rw [this]
    ring

/-- Correctness of `AzNat.add`: agrees with `Nat` addition. -/
theorem toNat_add (a b : AzNat) : (a + b).toNat = a.toNat + b.toNat := by
  show (add a b).toNat = a.toNat + b.toNat
  unfold add
  by_cases ha : a.limbs.size = 0
  · simp only [ha, ↓reduceDIte]
    have h_a_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      have : a.limbs.toList = [] := by
        have : a.limbs.toList.length = 0 := ha
        exact List.length_eq_zero_iff.mp this
      rw [this]; rfl
    rw [h_a_zero, Nat.zero_add]
  · simp only [ha, ↓reduceDIte]
    by_cases hb : b.limbs.size = 0
    · simp only [hb, ↓reduceDIte]
      have h_b_zero : b.toNat = 0 := by
        show toNatLimbsList b.limbs.toList = 0
        have : b.limbs.toList = [] := by
          have : b.limbs.toList.length = 0 := hb
          exact List.length_eq_zero_iff.mp this
        rw [this]; rfl
      rw [h_b_zero, Nat.add_zero]
    · simp only [hb, ↓reduceDIte]
      set r := addLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
                (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
                (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) with hr_def
      have h_main := addLimbs_toNat a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
                      (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
                      (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      rw [← hr_def] at h_main
      simp only [List.drop_zero] at h_main
      -- The lo-offset is 0 in both branches, length = max
      set lenMax := max a.limbs.size b.limbs.size with hlenMax
      have h_lo : (if b.limbs.size ≤ a.limbs.size then 0 else 0) = 0 := by
        split <;> rfl
      rw [h_lo] at h_main
      simp only [List.drop_zero] at h_main
      -- Compute size of r.1
      have h_r_size : r.1.size = lenMax := by
        rw [hr_def]
        unfold addLimbs
        by_cases h : b.limbs.size ≤ a.limbs.size
        · simp only [h, ↓reduceDIte]
          have := addGeqLimbs_size a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
                    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
                    h (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
          rw [this, hlenMax, Nat.max_eq_left h]
        · simp only [h, ↓reduceDIte]
          have := addGeqLimbs_size b.limbs a.limbs 0 b.limbs.size 0 a.limbs.size
                    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
                    (by omega) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero ha)
          rw [this, hlenMax, Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]
      have h_take_r : r.1.toList.take lenMax = r.1.toList := by
        rw [List.take_of_length_le]; rw [Array.length_toList, h_r_size]
      rw [h_take_r] at h_main
      -- Reduce a.toList.take a.limbs.size and b.toList.take b.limbs.size
      have h_take_a : a.limbs.toList.take a.limbs.size = a.limbs.toList := by
        rw [List.take_of_length_le]; rw [Array.length_toList]
      have h_take_b : b.limbs.toList.take b.limbs.size = b.limbs.toList := by
        rw [List.take_of_length_le]; rw [Array.length_toList]
      rw [h_take_a, h_take_b] at h_main
      have h_a_eq : a.toNat = toNatLimbsList a.limbs.toList := rfl
      have h_b_eq : b.toNat = toNatLimbsList b.limbs.toList := rfl
      -- h_main : toNatLimbsList r.1.toList + r.2.toNat * 2^(64*lenMax) = a.toNat + b.toNat
      rcases hc : r.2 with _ | _
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [toNat_ofLimbs]
        rw [hc] at h_main
        simp at h_main
        rw [h_a_eq, h_b_eq]; exact h_main
      · simp only [↓reduceIte]
        rw [toNat_ofLimbs, Array.toList_push, toNatLimbsList_append]
        have h_len : r.1.toList.length = lenMax := by
          rw [Array.length_toList, h_r_size]
        rw [h_len]
        have h_one : toNatLimbsList [(1 : UInt64)] = 1 := by simp [toNatLimbsList]
        rw [h_one]
        rw [hc] at h_main
        change _ + 1 * 2 ^ (64 * lenMax) = _ at h_main
        rw [h_a_eq, h_b_eq]; omega

/-- `ofNat`-version of `toNat_addUInt64`. -/
theorem ofNat_addUInt64 (n : Nat) (b : UInt64) :
    ofNat (n + b.toNat) = (ofNat n).addUInt64 b := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_addUInt64, toNat_ofNat]

/-- `ofNat`-version of `toNat_add`. -/
theorem ofNat_add (m n : Nat) : ofNat (m + n) = ofNat m + ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_add, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
