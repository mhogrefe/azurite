import Azurite.AzNat.Mul
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Conversion
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.UInt64.Equiv.MulWithCarry

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

/-- `ofNat`-version of `toNat_mulUInt64`. -/
theorem ofNat_mulUInt64 (n : Nat) (b : UInt64) :
    ofNat (n * b.toNat) = (ofNat n).mulUInt64 b := by
  have h : (ofNat (n * b.toNat)).toNat = ((ofNat n).mulUInt64 b).toNat := by
    rw [toNat_ofNat, toNat_mulUInt64, toNat_ofNat]
  have := congrArg ofNat h
  rwa [ofNat_toNat, ofNat_toNat] at this

end Azurite.AzNat
