import Azurite.AzInt.Mul
import Azurite.AzInt.Equiv.Add
import Azurite.AzNat.Equiv.Mul

namespace Azurite.AzInt

private lemma toInt_mkNorm_zero (s : Bool) : (mkNorm s 0).toInt = 0 := by
  unfold mkNorm
  split_ifs
  · rfl
  · contradiction

/-- Correctness of `AzInt.mulUInt64`. -/
theorem toInt_mulUInt64 (z : AzInt) (u : UInt64) :
    (z.mulUInt64 u).toInt = z.toInt * (u.toNat : Int) := by
  unfold mulUInt64
  have h_tz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  by_cases h0 : z.abs.mulUInt64 u = 0
  · have h0' : (z.abs.mulUInt64 u).toNat = 0 := by rw [h0]; rfl
    rw [AzNat.toNat_mulUInt64] at h0'
    rw [h0, toInt_mkNorm_zero, h_tz]
    rcases Nat.mul_eq_zero.mp h0' with ha | hu
    · have h_abs : z.abs = 0 :=
        AzNat.toNat_injective (by rw [ha, AzNat.toNat_zero])
      rw [h_abs]; simp
    · simp [hu]
  · cases hs : z.sign
    · rw [toInt_mkNorm_false _ h0, AzNat.toNat_mulUInt64, h_tz, hs]; simp
    · rw [toInt_mkNorm_true, AzNat.toNat_mulUInt64, h_tz, hs]; simp

/-- `ofInt`-version of `toInt_mulUInt64`. -/
theorem ofInt_mulUInt64 (i : Int) (u : UInt64) :
    ofInt (i * (u.toNat : Int)) = (ofInt i).mulUInt64 u := by
  have h : (ofInt (i * (u.toNat : Int))).toInt = ((ofInt i).mulUInt64 u).toInt := by
    rw [toInt_ofInt, toInt_mulUInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

private lemma int64_neg_toNat (i : Int64) (hi : ¬ i ≥ 0) :
    ((-i).toUInt64.toNat : Int) = -i.toInt := by
  have hi_neg : i.toInt = (i.toBitVec.toNat : Int) - 2^64 := Int64.toInt_of_neg hi
  have h_iLt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
  have hh_neg_int : ¬ 0 ≤ i.toBitVec.toInt := by
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
  have h_pos : i.toBitVec.toNat > 0 := by split_ifs at hh_neg_int <;> omega
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
  rw [h_neg_u_toNat, hi_neg]; ring

/-- Correctness of `AzInt.mulInt64`. -/
theorem toInt_mulInt64 (z : AzInt) (i : Int64) :
    (z.mulInt64 i).toInt = z.toInt * i.toInt := by
  unfold mulInt64
  have h_tz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  by_cases hi : i ≥ 0
  · simp only [hi, ↓reduceIte]
    have h_i_toInt : (i.toUInt64.toNat : Int) = i.toInt := by
      change (i.toBitVec.toNat : Int) = i.toInt
      rw [Int64.toInt_of_nonneg hi]
    have := toInt_mulUInt64 z i.toUInt64
    unfold mulUInt64 at this
    rw [this, h_i_toInt]
  · simp only [hi, ↓reduceIte]
    have h_neg_toInt : ((-i).toUInt64.toNat : Int) = -i.toInt :=
      int64_neg_toNat i hi
    by_cases h0 : z.abs.mulUInt64 (-i).toUInt64 = 0
    · have h0' : (z.abs.mulUInt64 (-i).toUInt64).toNat = 0 := by rw [h0]; rfl
      rw [AzNat.toNat_mulUInt64] at h0'
      rw [h0, toInt_mkNorm_zero, h_tz]
      rcases Nat.mul_eq_zero.mp h0' with ha | hu
      · have h_abs : z.abs = 0 :=
          AzNat.toNat_injective (by rw [ha, AzNat.toNat_zero])
        rw [h_abs]; simp
      · have h_u_zero : ((-i).toUInt64.toNat : Int) = 0 := by exact_mod_cast hu
        rw [h_u_zero] at h_neg_toInt
        have h_i_zero : i.toInt = 0 := by linarith
        simp [h_i_zero]
    · cases hs : z.sign
      · rw [Bool.not_false, toInt_mkNorm_true, AzNat.toNat_mulUInt64, h_tz, hs]
        push_cast; rw [h_neg_toInt]; ring
      · rw [Bool.not_true, toInt_mkNorm_false _ h0, AzNat.toNat_mulUInt64, h_tz, hs]
        push_cast; rw [h_neg_toInt]; simp

/-- `ofInt`-version of `toInt_mulInt64`. -/
theorem ofInt_mulInt64 (i : Int) (j : Int64) :
    ofInt (i * j.toInt) = (ofInt i).mulInt64 j := by
  have h : (ofInt (i * j.toInt)).toInt = ((ofInt i).mulInt64 j).toInt := by
    rw [toInt_ofInt, toInt_mulInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Correctness of `AzInt.mul`. -/
theorem toInt_mul (a b : AzInt) : (a * b).toInt = a.toInt * b.toInt := by
  show (mul a b).toInt = a.toInt * b.toInt
  unfold mul
  have h_ta : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_tb : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  by_cases h0 : a.abs * b.abs = 0
  · have h0' : (a.abs * b.abs).toNat = 0 := by rw [h0]; rfl
    rw [AzNat.toNat_mul] at h0'
    rw [h0, toInt_mkNorm_zero, h_ta, h_tb]
    rcases Nat.mul_eq_zero.mp h0' with ha | hb
    · have h_abs_a : a.abs = 0 :=
        AzNat.toNat_injective (by rw [ha, AzNat.toNat_zero])
      rw [h_abs_a]; simp
    · have h_abs_b : b.abs = 0 :=
        AzNat.toNat_injective (by rw [hb, AzNat.toNat_zero])
      rw [h_abs_b]; simp
  · cases hsa : a.sign <;> cases hsb : b.sign
    · show (mkNorm true _).toInt = _
      rw [toInt_mkNorm_true, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp
    · show (mkNorm false _).toInt = _
      rw [toInt_mkNorm_false _ h0, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp
    · show (mkNorm false _).toInt = _
      rw [toInt_mkNorm_false _ h0, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp
    · show (mkNorm true _).toInt = _
      rw [toInt_mkNorm_true, AzNat.toNat_mul, h_ta, h_tb, hsa, hsb]
      push_cast; simp

/-- `ofInt`-version of `toInt_mul`. -/
theorem ofInt_mul (i j : Int) : ofInt (i * j) = ofInt i * ofInt j := by
  have h : (ofInt (i * j)).toInt = (ofInt i * ofInt j).toInt := by
    rw [toInt_ofInt, toInt_mul, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
