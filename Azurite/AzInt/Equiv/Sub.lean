import Azurite.AzInt.Sub
import Azurite.AzInt.Equiv.Add

namespace Azurite.AzInt

/-- Correctness of `AzInt.subUInt64`. -/
theorem toInt_subUInt64 (z : AzInt) (u : UInt64) :
    (z.subUInt64 u).toInt = z.toInt - (u.toNat : Int) := by
  unfold subUInt64
  have h_tz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  rw [h_tz]
  by_cases hs : z.sign
  · simp only [hs, ↓reduceIte]
    rw [AzNat.compareUInt64_eq]
    rcases h_cmp : Ord.compare z.abs.toNat u.toNat with _ | _ | _
    · have h_lt : z.abs.toNat < u.toNat := by
        have := Nat.compare_eq_lt.mp h_cmp; omega
      have h_sub_pos : u.toAzNat - z.abs ≠ 0 := by
        intro hc
        have hc' : (u.toAzNat - z.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub, UInt64.toNat_toAzNat] at hc'
        omega
      rw [toInt_mkNorm_false _ h_sub_pos, AzNat.toNat_sub, UInt64.toNat_toAzNat]
      omega
    · have h_eq : z.abs.toNat = u.toNat := Nat.compare_eq_eq.mp h_cmp
      rw [toInt_zero]
      omega
    · have h_gt : u.toNat < z.abs.toNat := Nat.compare_eq_gt.mp h_cmp
      rw [toInt_mkNorm_true, AzNat.toNat_subUInt64]
      omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have h_abs_ne : z.abs ≠ 0 := by
      intro h0
      have := z.zero_sign h0
      rw [this] at hs; contradiction
    have h_abs_pos : 0 < z.abs.toNat := by
      rcases Nat.eq_zero_or_pos z.abs.toNat with h | h
      · exact absurd
          (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero])) h_abs_ne
      · exact h
    have h_sum_pos : z.abs.addUInt64 u ≠ 0 := by
      intro hc
      have hc' : (z.abs.addUInt64 u).toNat = 0 := by rw [hc]; rfl
      rw [AzNat.toNat_addUInt64] at hc'
      omega
    rw [toInt_mkNorm_false _ h_sum_pos, AzNat.toNat_addUInt64]
    omega

/-- `ofInt`-version of `toInt_subUInt64`. -/
theorem ofInt_subUInt64 (i : Int) (u : UInt64) :
    ofInt (i - (u.toNat : Int)) = (ofInt i).subUInt64 u := by
  have h : (ofInt (i - (u.toNat : Int))).toInt = ((ofInt i).subUInt64 u).toInt := by
    rw [toInt_ofInt, toInt_subUInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Correctness of `AzInt.addInt64`. -/
theorem toInt_addInt64 (z : AzInt) (i : Int64) :
    (z.addInt64 i).toInt = z.toInt + i.toInt := by
  unfold addInt64
  by_cases hi : i ≥ 0
  · simp only [hi, ↓reduceIte]
    rw [toInt_addUInt64]
    have ht : (i.toUInt64.toNat : Int) = i.toBitVec.toNat := rfl
    rw [ht, Int64.toInt_of_nonneg hi]
  · simp only [hi, ↓reduceIte]
    rw [toInt_subUInt64]
    have hi_neg : i.toInt = (i.toBitVec.toNat : Int) - 2^64 := Int64.toInt_of_neg hi
    have h_iLt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
    have hh_neg_int : ¬0 ≤ i.toBitVec.toInt := by
      revert hi
      change ¬(decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) →
             ¬(0 ≤ i.toBitVec.toInt)
      intro he
      have h_dec : decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = false :=
        Bool.eq_false_of_not_eq_true he
      have he2 := of_decide_eq_false h_dec
      have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
      rw [h0] at he2
      exact he2
    unfold BitVec.toInt at hh_neg_int
    have h_pos : i.toBitVec.toNat > 0 := by
      split_ifs at hh_neg_int
      · omega
      · omega
    have h_neg_u_toNat : ((-i).toUInt64.toNat : Int) = 2^64 - i.toBitVec.toNat := by
      change (((-i).toBitVec).toNat : Int) = 2^64 - i.toBitVec.toNat
      have h_neg_bv : (-i).toBitVec = -i.toBitVec := rfl
      rw [h_neg_bv]
      have h_mod : ((-i.toBitVec).toNat : Int)
                  = ((2^64 - i.toBitVec.toNat) % 2^64 : Nat) := by
        change ((((2^64 - i.toBitVec.toNat) % 2^64 : Nat)) : Int) =
               ((2^64 - i.toBitVec.toNat) % 2^64 : Nat)
        rfl
      rw [h_mod]
      have h_lt : 2^64 - i.toBitVec.toNat < 2^64 := by omega
      rw [Nat.mod_eq_of_lt h_lt]
      have h_le : i.toBitVec.toNat ≤ 2^64 := by omega
      rw [Nat.cast_sub h_le]; rfl
    rw [h_neg_u_toNat, hi_neg]
    ring

/-- `ofInt`-version of `toInt_addInt64`. -/
theorem ofInt_addInt64 (i : Int) (j : Int64) :
    ofInt (i + j.toInt) = (ofInt i).addInt64 j := by
  have h : (ofInt (i + j.toInt)).toInt = ((ofInt i).addInt64 j).toInt := by
    rw [toInt_ofInt, toInt_addInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Correctness of `AzInt.subInt64`. -/
theorem toInt_subInt64 (z : AzInt) (i : Int64) :
    (z.subInt64 i).toInt = z.toInt - i.toInt := by
  unfold subInt64
  by_cases hi : i ≥ 0
  · simp only [hi, ↓reduceIte]
    rw [toInt_subUInt64]
    have ht : (i.toUInt64.toNat : Int) = i.toBitVec.toNat := rfl
    rw [ht, Int64.toInt_of_nonneg hi]
  · simp only [hi, ↓reduceIte]
    rw [toInt_addUInt64]
    have hi_neg : i.toInt = (i.toBitVec.toNat : Int) - 2^64 := Int64.toInt_of_neg hi
    have h_iLt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
    have hh_neg_int : ¬0 ≤ i.toBitVec.toInt := by
      revert hi
      change ¬(decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = true) →
             ¬(0 ≤ i.toBitVec.toInt)
      intro he
      have h_dec : decide ((0 : Int64).toBitVec.toInt ≤ i.toBitVec.toInt) = false :=
        Bool.eq_false_of_not_eq_true he
      have he2 := of_decide_eq_false h_dec
      have h0 : (0 : Int64).toBitVec.toInt = 0 := rfl
      rw [h0] at he2
      exact he2
    unfold BitVec.toInt at hh_neg_int
    have h_pos : i.toBitVec.toNat > 0 := by
      split_ifs at hh_neg_int
      · omega
      · omega
    have h_neg_u_toNat : ((-i).toUInt64.toNat : Int) = 2^64 - i.toBitVec.toNat := by
      change (((-i).toBitVec).toNat : Int) = 2^64 - i.toBitVec.toNat
      have h_neg_bv : (-i).toBitVec = -i.toBitVec := rfl
      rw [h_neg_bv]
      have h_mod : ((-i.toBitVec).toNat : Int)
                  = ((2^64 - i.toBitVec.toNat) % 2^64 : Nat) := by
        change ((((2^64 - i.toBitVec.toNat) % 2^64 : Nat)) : Int) =
               ((2^64 - i.toBitVec.toNat) % 2^64 : Nat)
        rfl
      rw [h_mod]
      have h_lt : 2^64 - i.toBitVec.toNat < 2^64 := by omega
      rw [Nat.mod_eq_of_lt h_lt]
      have h_le : i.toBitVec.toNat ≤ 2^64 := by omega
      rw [Nat.cast_sub h_le]; rfl
    rw [h_neg_u_toNat, hi_neg]
    ring

/-- `ofInt`-version of `toInt_subInt64`. -/
theorem ofInt_subInt64 (i : Int) (j : Int64) :
    ofInt (i - j.toInt) = (ofInt i).subInt64 j := by
  have h : (ofInt (i - j.toInt)).toInt = ((ofInt i).subInt64 j).toInt := by
    rw [toInt_ofInt, toInt_subInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
