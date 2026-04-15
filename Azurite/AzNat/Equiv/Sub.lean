import Azurite.AzNat.Sub
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.UInt64.Equiv.SubWithBorrow

namespace Azurite.AzNat

/-- Size preservation of `subLimb.go`. -/
theorem subLimb.go_size (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size) :
    (subLimb.go hi a i borrow h_size).1.size = a.size := by
  induction hi_sub_i : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [subLimb.go]
    by_cases hb : borrow = 0
    · simp [hb]
    · simp [hb, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    rw [subLimb.go]
    by_cases hb : borrow = 0
    · simp [hb]
    · simp only [hb, ↓reduceIte, h_lt, ↓reduceDIte]
      have h_rec : hi - (i + 1) = n := by omega
      rw [ih _ _ _ _ h_rec]
      rw [Array.size_set]

/-- Size preservation of `subLimb`. -/
theorem subLimb_size (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (subLimb a lo hi b hlo hhi).1.size = a.size :=
  subLimb.go_size hi a lo b hhi

/-- `subLimb.go` preserves the prefix `[0, i)`. -/
theorem subLimb.go_toList_take (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size) :
    (subLimb.go hi a i borrow h_size).1.toList.take i = a.toList.take i := by
  induction hi_sub_i : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [subLimb.go]
    by_cases hb : borrow = 0
    · simp [hb]
    · simp [hb, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    rw [subLimb.go]
    by_cases hb : borrow = 0
    · simp [hb]
    · simp only [hb, ↓reduceIte, h_lt, ↓reduceDIte]
      have h_rec : hi - (i + 1) = n := by omega
      set diff := a[i] - borrow with hdiff_def
      set newBorrow : UInt64 := if a[i] < borrow then 1 else 0 with hnb_def
      have h_take_succ : List.take i
          ((subLimb.go hi (a.set i diff) (i + 1) newBorrow
              (by rw [Array.size_set]; exact h_size)).1.toList.take (i + 1))
            = (subLimb.go hi (a.set i diff) (i + 1) newBorrow
                (by rw [Array.size_set]; exact h_size)).1.toList.take i := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [← h_take_succ, ih _ _ _ _ h_rec, List.take_take, Nat.min_eq_left (by omega)]
      rw [Array.toList_set, List.take_set]
      rw [List.set_eq_of_length_le]
      rw [List.length_take, Array.length_toList]
      omega

/-- `subLimb` preserves the prefix `[0, lo)`. -/
theorem subLimb_toList_take (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (subLimb a lo hi b hlo hhi).1.toList.take lo = a.toList.take lo :=
  subLimb.go_toList_take hi a lo b hhi

/-- Single-limb sub step: subtracting a borrow from a UInt64 produces a
    difference and a new borrow-out bit that together preserve the
    numerical value. -/
lemma limb_sub_step (x borrow : UInt64) :
    x.toNat + (if x < borrow then (1 : UInt64) else 0).toNat * 2 ^ 64
      = (x - borrow).toNat + borrow.toNat := by
  have hxlt : x.toNat < 2 ^ 64 := UInt64.toNat_lt x
  have hblt : borrow.toNat < 2 ^ 64 := UInt64.toNat_lt borrow
  have h_sub : (x - borrow).toNat = (2 ^ 64 - borrow.toNat + x.toNat) % 2 ^ 64 :=
    UInt64.toNat_sub x borrow
  have h_lt_iff : x < borrow ↔ x.toNat < borrow.toNat :=
    UInt64.lt_iff_toNat_lt
  by_cases h_uf : x < borrow
  · have h_lt : x.toNat < borrow.toNat := h_lt_iff.mp h_uf
    have h_mod : (2 ^ 64 - borrow.toNat + x.toNat) % 2 ^ 64
                  = 2 ^ 64 - borrow.toNat + x.toNat := by
      rw [Nat.mod_eq_of_lt]; omega
    simp only [h_uf, ↓reduceIte]
    show x.toNat + 1 * 2 ^ 64 = (x - borrow).toNat + borrow.toNat
    rw [h_sub, h_mod]; omega
  · have h_ge : borrow.toNat ≤ x.toNat := by
      by_contra h_lt
      push Not at h_lt
      exact h_uf (h_lt_iff.mpr h_lt)
    have h_mod : (2 ^ 64 - borrow.toNat + x.toNat) % 2 ^ 64
                  = x.toNat - borrow.toNat := by
      rw [show 2 ^ 64 - borrow.toNat + x.toNat
            = (x.toNat - borrow.toNat) + 1 * 2 ^ 64 from by omega]
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [h_uf, ↓reduceIte]
    show x.toNat + 0 * 2 ^ 64 = (x - borrow).toNat + borrow.toNat
    rw [h_sub, h_mod]; omega

/-- Invariant of `subLimb.go`: starting from `(a, i, borrow)`, the original
    slice `[i, hi)` plus the incoming `borrow` equals the resulting modified
    slice plus the final borrow bit at position `hi`.  Valid whenever
    `borrow ≤ 1` or the loop can still advance. -/
private lemma subLimb.go_correct (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size)
    (hborrow : borrow.toNat ≤ 1 ∨ i < hi) :
    toNatLimbsList ((a.toList.drop i).take (hi - i))
        + (subLimb.go hi a i borrow h_size).2.toNat * 2 ^ (64 * (hi - i))
      = toNatLimbsList (((subLimb.go hi a i borrow h_size).1.toList.drop i).take (hi - i))
        + borrow.toNat := by
  induction hi_sub_i : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    by_cases hb : borrow = 0
    · have h_eq : subLimb.go hi a i borrow h_size = (a, false) := by
        conv_lhs => rw [subLimb.go]
        simp [hb]
      rw [h_eq, hb]
      simp [toNatLimbsList]
    · have h_borrow_ne : borrow.toNat ≠ 0 := by
        intro h
        exact hb (UInt64.toNat_inj.mp (show borrow.toNat = (0 : UInt64).toNat from h))
      have h_borrow_le : borrow.toNat ≤ 1 :=
        hborrow.resolve_right (fun h => absurd h (Nat.not_lt.mpr h_ge))
      have h_borrow_eq : borrow.toNat = 1 := by omega
      have h_eq : subLimb.go hi a i borrow h_size = (a, true) := by
        conv_lhs => rw [subLimb.go]
        simp [hb, Nat.not_lt.mpr h_ge]
      rw [h_eq]
      simp [toNatLimbsList, h_borrow_eq]
  | succ n ih =>
    have h_lt : i < hi := by omega
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
    by_cases hb : borrow = 0
    · have h_eq : subLimb.go hi a i borrow h_size = (a, false) := by
        conv_lhs => rw [subLimb.go]
        simp [hb]
      rw [h_eq, hb]
      simp [toNatLimbsList]
    · set x := a[i] with hx_def
      set diff := x - borrow with hdiff_def
      set newBorrow : UInt64 := if x < borrow then 1 else 0 with hnb_def
      set a' := a.set i diff h_i_size with ha'_def
      have h_size' : hi ≤ a'.size := by rw [ha'_def, Array.size_set]; exact h_size
      have h_eq : subLimb.go hi a i borrow h_size
                  = subLimb.go hi a' (i + 1) newBorrow h_size' := by
        conv_lhs => rw [subLimb.go]
        simp [hb, h_lt, hx_def, hdiff_def, hnb_def, ha'_def]
      have h_rec : hi - (i + 1) = n := by omega
      have h_nb_le : newBorrow.toNat ≤ 1 := by
        rw [hnb_def]
        by_cases huf : x < borrow
        · simp [huf]
        · simp [huf]
      have h_ih := ih a' (i + 1) newBorrow h_size' (Or.inl h_nb_le) h_rec
      have h_limb : x.toNat + newBorrow.toNat * 2 ^ 64 = diff.toNat + borrow.toNat := by
        rw [hdiff_def, hnb_def]
        exact limb_sub_step x borrow
      have h_res_size :
          (subLimb.go hi a' (i + 1) newBorrow h_size').1.size = a.size := by
        rw [subLimb.go_size, ha'_def, Array.size_set]
      have h_res_i_size : i < (subLimb.go hi a' (i + 1) newBorrow h_size').1.size := by
        rw [h_res_size]; exact h_i_size
      have h_res_i : (subLimb.go hi a' (i + 1) newBorrow h_size').1[i]'h_res_i_size
                      = diff := by
        have h_prefix :=
          subLimb.go_toList_take hi a' (i + 1) newBorrow h_size'
        have h_len_L : ((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList).length = a.size := by
          rw [Array.length_toList]; exact h_res_size
        have h_i_lt_L_take :
            i < ((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList.take (i + 1)).length := by
          rw [List.length_take, h_len_L]; omega
        have h_i_lt_R_take : i < (a'.toList.take (i + 1)).length := by
          rw [List.length_take, Array.length_toList, ha'_def, Array.size_set]; omega
        have h_get_eq :
            ((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList.take (i + 1))[i]'h_i_lt_L_take
              = (a'.toList.take (i + 1))[i]'h_i_lt_R_take := by
          congr 1
        rw [List.getElem_take, List.getElem_take] at h_get_eq
        rw [← Array.getElem_toList h_res_i_size, h_get_eq]
        have h_i_lt : i < (a.set i diff h_i_size).toList.length := by
          rw [Array.length_toList, Array.size_set]; exact h_i_size
        show (a.set i diff h_i_size).toList[i]'h_i_lt = diff
        simp [Array.toList_set, List.getElem_set_self]
      have h_drop_eq : a'.toList.drop (i + 1) = a.toList.drop (i + 1) := by
        rw [ha'_def, Array.toList_set, List.drop_set]; simp
      rw [h_eq]
      rw [show (n + 1) = hi - i from hi_sub_i.symm]
      rw [toNatLimbsList_take_succ (subLimb.go hi a' (i + 1) newBorrow h_size').1 i hi
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
          (((subLimb.go hi a' (i + 1) newBorrow h_size').1.toList.drop (i + 1)).take (hi - (i + 1)))
        with hQ_def
      set R := (subLimb.go hi a' (i + 1) newBorrow h_size').2.toNat with hR_def
      change x.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
           = diff.toNat + Q * 2 ^ 64 + borrow.toNat
      have h1 : x.toNat + P * 2 ^ 64 + R * (2 ^ (64 * (hi - (i + 1))) * 2 ^ 64)
              = x.toNat + (P + R * 2 ^ (64 * (hi - (i + 1)))) * 2 ^ 64 := by ring
      rw [h1, h_ih]
      have h2 : x.toNat + (Q + newBorrow.toNat) * 2 ^ 64
              = (x.toNat + newBorrow.toNat * 2 ^ 64) + Q * 2 ^ 64 := by ring
      rw [h2, h_limb]
      ring

/-- Correctness of `subLimb`: the original slice `[lo, hi)` plus `b` equals
    the modified slice plus the returned borrow at the top. -/
theorem subLimb_toNat (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (h_lo_lt : lo < hi) :
    let (a', c) := subLimb a lo hi b hlo hhi
    toNatLimbsList ((a.toList.drop lo).take (hi - lo))
        + c.toNat * 2 ^ (64 * (hi - lo))
      = toNatLimbsList ((a'.toList.drop lo).take (hi - lo)) + b.toNat := by
  have h := subLimb.go_correct hi a lo b hhi (Or.inr h_lo_lt)
  simp at h
  exact h

/-- Correctness of `AzNat.subUInt64`: agrees with truncated `Nat` subtraction. -/
theorem toNat_subUInt64 (a : AzNat) (b : UInt64) :
    (a.subUInt64 b).toNat = a.toNat - b.toNat := by
  unfold subUInt64
  by_cases hsz : a.limbs.size = 0
  · have h_nil : a.limbs.toList = [] := by
      have : a.limbs.toList.length = 0 := hsz
      exact List.length_eq_zero_iff.mp this
    have h_a_zero : a.toNat = 0 := by
      show toNatLimbsList a.limbs.toList = 0
      rw [h_nil]; rfl
    simp [hsz, h_a_zero]
  · simp only [hsz, ↓reduceIte]
    set n := a.limbs.size with hn_def
    have h_pos : 0 < n := Nat.pos_of_ne_zero hsz
    have h_size : (subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.size = n :=
      subLimb_size a.limbs 0 n b _ _
    have h_main := subLimb_toNat a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _) h_pos
    simp only [List.drop_zero, Nat.sub_zero] at h_main
    have h_take_arr : a.limbs.toList.take n = a.limbs.toList := by
      rw [List.take_of_length_le]; rw [Array.length_toList]
    have h_take_r : (subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList.take n
                  = (subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)).1.toList := by
      rw [List.take_of_length_le]; rw [Array.length_toList, h_size]
    rw [h_take_arr, h_take_r] at h_main
    set r := subLimb a.limbs 0 n b (Nat.zero_le _) (Nat.le_refl _)
    have h_a : a.toNat = toNatLimbsList a.limbs.toList := rfl
    have h_r_lt : toNatLimbsList r.1.toList < 2 ^ (64 * n) := by
      have ht := toNatLimbsList_lt_pow r.1.toList
      rw [Array.length_toList, h_size] at ht
      exact ht
    rcases hc : r.2 with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [toNat_ofLimbs]
      rw [hc] at h_main
      simp at h_main
      rw [h_a]; omega
    · simp only [↓reduceIte]
      rw [hc] at h_main
      change toNatLimbsList a.limbs.toList + 1 * 2 ^ (64 * n) = _ + b.toNat at h_main
      show (0 : AzNat).toNat = a.toNat - b.toNat
      have h0 : (0 : AzNat).toNat = 0 := rfl
      rw [h0, h_a]; omega

end Azurite.AzNat
