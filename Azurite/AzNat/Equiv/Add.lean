import Azurite.AzNat.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.ShiftRight

namespace Azurite.AzNat

private lemma toNatLimbsList_take_succ (a : Array UInt64) (i hi : Nat)
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

/-- Size preservation of `addLimb.go`. -/
theorem addLimb.go_size (hi : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) :
    (addLimb.go hi a i carry h_size).1.size = a.size := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [addLimb.go]
    by_cases hc : carry = 0
    · simp [hc]
    · simp [hc, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    rw [addLimb.go]
    by_cases hc : carry = 0
    · simp [hc]
    · simp only [hc, ↓reduceIte, h_lt, ↓reduceDIte]
      have h_rec : hi - (i + 1) = n := by omega
      rw [ih _ _ _ _ h_rec]
      rw [Array.size_set]

/-- Size preservation of `addLimb`. -/
theorem addLimb_size (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (addLimb a lo hi b hlo hhi).1.size = a.size :=
  addLimb.go_size hi a lo b hhi

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

end Azurite.AzNat
