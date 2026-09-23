import Azurite.AzInt.Compare
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.Compare

namespace Azurite.AzInt

lemma compare_eq_lt_iff_toInt_lt (a b : AzInt) : compare a b = Ordering.lt ↔ a.toInt < b.toInt := by
  change (if a.sign ≠ b.sign then if a.sign then Ordering.gt else Ordering.lt else if a.sign then Ord.compare a.abs b.abs else Ord.compare b.abs a.abs) = Ordering.lt ↔ a.toInt < b.toInt
  unfold toInt
  rcases a with ⟨as, aa, ah⟩; rcases b with ⟨bs, ba, bh⟩
  rcases as with _ | _ <;> rcases bs with _ | _
  · dsimp
    have h1 : Ord.compare ba aa = Ordering.lt ↔ ba < aa := compare_lt_iff_lt
    rw [h1, AzNat.lt_iff_toNat_lt]
    constructor <;> intro h <;> omega
  · dsimp
    simp
    have h1 : aa.toNat > 0 := by
      by_contra hc
      have h0 : aa.toNat = 0 := by omega
      have haa : aa = 0 := AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])
      have f : false = true := ah haa
      contradiction
    have h2 : ba.toNat ≥ 0 := by omega
    omega
  · simp
  · dsimp
    have h1 : Ord.compare aa ba = Ordering.lt ↔ aa < ba := compare_lt_iff_lt
    rw [h1, AzNat.lt_iff_toNat_lt]
    constructor <;> intro h <;> omega

lemma compare_eq_eq_iff_toInt_eq (a b : AzInt) : compare a b = Ordering.eq ↔ a.toInt = b.toInt := by
  change (if a.sign ≠ b.sign then if a.sign then Ordering.gt else Ordering.lt else if a.sign then Ord.compare a.abs b.abs else Ord.compare b.abs a.abs) = Ordering.eq ↔ a.toInt = b.toInt
  unfold toInt
  rcases a with ⟨as, aa, ah⟩; rcases b with ⟨bs, ba, bh⟩
  rcases as with _ | _ <;> rcases bs with _ | _
  · dsimp
    have h1 : Ord.compare ba aa = Ordering.eq ↔ ba = aa := compare_eq_iff_eq
    have h2 : ba = aa ↔ ba.toNat = aa.toNat := by
      constructor
      · intro h; rw [h]
      · intro h; exact AzNat.toNat_injective h
    rw [h1, h2]
    constructor <;> intro h <;> omega
  · dsimp
    simp
    intro h
    have h_pos : (ba.toNat : Int) ≥ 0 := Int.natCast_nonneg ba.toNat
    have h0 : aa.toNat = 0 := by omega
    have h1 : aa = 0 := AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])
    have f : false = true := ah h1
    contradiction
  · dsimp
    simp
    intro h
    have h_pos : (aa.toNat : Int) ≥ 0 := Int.natCast_nonneg aa.toNat
    have h0b : ba.toNat = 0 := by omega
    have h1 : ba = 0 := AzNat.toNat_injective (by rw [h0b, AzNat.toNat_zero])
    have f : false = true := bh h1
    contradiction
  · dsimp
    have h1 : Ord.compare aa ba = Ordering.eq ↔ aa = ba := compare_eq_iff_eq
    have h2 : aa = ba ↔ aa.toNat = ba.toNat := by
      constructor
      · intro h; rw [h]
      · intro h; exact AzNat.toNat_injective h
    rw [h1, h2]
    constructor <;> intro h <;> omega

lemma compare_eq_compare_toInt (a b : AzInt) : compare a b = Ord.compare a.toInt b.toInt := by
  have hl : compare a b = Ordering.lt ↔ a.toInt < b.toInt := compare_eq_lt_iff_toInt_lt a b
  have he : compare a b = Ordering.eq ↔ a.toInt = b.toInt := compare_eq_eq_iff_toInt_eq a b
  rcases hc1 : compare a b <;> rcases hc2 : Ord.compare a.toInt b.toInt
  · rfl
  · have hz : compare a b = Ordering.eq := he.mpr (compare_eq_iff_eq.mp hc2)
    rw [hc1] at hz; contradiction
  · have hnlt : ¬(a.toInt < b.toInt) := by
      intro hc; have t : Ord.compare a.toInt b.toInt = Ordering.lt := compare_lt_iff_lt.mpr hc
      rw [t] at hc2; contradiction
    have hnlt_a : ¬(compare a b = Ordering.lt) := by rw [compare_eq_lt_iff_toInt_lt]; exact hnlt
    contradiction
  · have hz : compare a b = Ordering.lt := hl.mpr (compare_lt_iff_lt.mp hc2)
    rw [hc1] at hz; contradiction
  · rfl
  · have hneq : ¬(a.toInt = b.toInt) := by
      intro hc; have t : Ord.compare a.toInt b.toInt = Ordering.eq := compare_eq_iff_eq.mpr hc
      rw [t] at hc2; contradiction
    have hneq_a : ¬(compare a b = Ordering.eq) := by rw [compare_eq_eq_iff_toInt_eq]; exact hneq
    contradiction
  · have hz : compare a b = Ordering.lt := hl.mpr (compare_lt_iff_lt.mp hc2)
    rw [hc1] at hz; contradiction
  · have hz : compare a b = Ordering.eq := he.mpr (compare_eq_iff_eq.mp hc2)
    rw [hc1] at hz; contradiction
  · rfl

theorem compare_ofInt_eq_compare (a b : Int) : compare (ofInt a) (ofInt b) = Ord.compare a b := by
  rw [compare_eq_compare_toInt]
  rw [toInt_ofInt, toInt_ofInt]

lemma le_iff_toInt_le (a b : AzInt) : a ≤ b ↔ a.toInt ≤ b.toInt := by
  change compare a b ≠ Ordering.gt ↔ a.toInt ≤ b.toInt
  rw [compare_eq_compare_toInt]
  exact compare_le_iff_le

lemma lt_iff_toInt_lt (a b : AzInt) : a < b ↔ a.toInt < b.toInt := by
  change compare a b = Ordering.lt ↔ a.toInt < b.toInt
  rw [compare_eq_compare_toInt]
  exact compare_lt_iff_lt

lemma le_refl (a : AzInt) : a ≤ a := by
  rw [le_iff_toInt_le]

lemma le_trans (a b c : AzInt) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rw [le_iff_toInt_le] at *
  exact Int.le_trans h1 h2

lemma le_antisymm (a b : AzInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  rw [le_iff_toInt_le] at *
  have ht : a.toInt = b.toInt := Int.le_antisymm h1 h2
  have hr : ofInt a.toInt = ofInt b.toInt := congrArg ofInt ht
  rw [ofInt_toInt, ofInt_toInt] at hr
  exact hr

lemma le_total (a b : AzInt) : a ≤ b ∨ b ≤ a := by
  rw [le_iff_toInt_le, le_iff_toInt_le]
  exact Int.le_total a.toInt b.toInt

lemma lt_iff_le_not_ge (a b : AzInt) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  rw [lt_iff_toInt_lt, le_iff_toInt_le, le_iff_toInt_le]
  omega

lemma compare_eq_compareOfLessAndEq (a b : AzInt) : compare a b = compareOfLessAndEq a b := by
  have hl1 : a < b ↔ a.toInt < b.toInt := lt_iff_toInt_lt a b
  have he1 : a = b ↔ a.toInt = b.toInt := by
    constructor
    · intro h; rw [h]
    · intro h
      have q : ofInt a.toInt = ofInt b.toInt := congrArg ofInt h
      rw [ofInt_toInt, ofInt_toInt] at q
      exact q
  change compare a b = (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt)
  rw [compare_eq_compare_toInt]
  rcases hc2 : Ord.compare a.toInt b.toInt
  · have ht : a.toInt < b.toInt := compare_lt_iff_lt.mp hc2
    have ha : a < b := hl1.mpr ht
    rw [ite_eq_left ha]
  · have ht : a.toInt = b.toInt := compare_eq_iff_eq.mp hc2
    have h1 : ¬ (a.toInt < b.toInt) := by omega
    have h_not_lt : ¬ (a < b) := fun h => h1 (hl1.mp h)
    have ha : a = b := he1.mpr ht
    rw [ite_eq_right h_not_lt, ite_eq_left ha]
  · have ht : Ord.compare a.toInt b.toInt = Ordering.gt := hc2
    have h_not_lt : ¬(a.toInt < b.toInt) := by
      intro h_lt
      have hz2 : Ord.compare a.toInt b.toInt = Ordering.lt := compare_lt_iff_lt.mpr h_lt
      rw [hz2] at ht; contradiction
    have h_not_eq : ¬(a.toInt = b.toInt) := by
      intro h_eq
      have hz2 : Ord.compare a.toInt b.toInt = Ordering.eq := compare_eq_iff_eq.mpr h_eq
      rw [hz2] at ht; contradiction
    have h1 : ¬ (a < b) := fun h => h_not_lt (hl1.mp h)
    have h2 : ¬ (a = b) := fun h => h_not_eq (he1.mp h)
    rw [ite_eq_right h1, ite_eq_right h2]

-- Helper: sign=false implies abs is positive
private lemma neg_sign_abs_pos {z : AzInt} (hs : z.sign = false) : z.abs.toNat > 0 := by
  by_contra hc
  have h0 : z.abs.toNat = 0 := by omega
  have habs : z.abs = 0 := AzNat.toNat_injective (by rw [h0, AzNat.toNat_zero])
  have := z.zero_sign habs
  rw [hs] at this; contradiction

-- Helper: sign=false implies toInt < 0
private lemma neg_sign_toInt_neg {z : AzInt} (hs : z.sign = false) : z.toInt < 0 := by
  unfold toInt; rw [ite_eq_right (by rw [hs]; decide)]
  have := neg_sign_abs_pos hs
  omega

theorem compareUInt64_eq (z : AzInt) (u : UInt64) :
    z.compareUInt64 u = Ord.compare z.toInt (u.toNat : Int) := by
  unfold compareUInt64 toInt
  split_ifs with hs
  · -- sign = true, z.toInt = z.abs.toNat
    rw [AzNat.compareUInt64_eq, AzNat.compare_nat_cast_int]
  · -- sign = false, z.toInt = -z.abs.toNat, result is .lt
    have h_neg : -(z.abs.toNat : Int) < (u.toNat : Int) := by
      have := neg_sign_abs_pos (Bool.eq_false_iff.mpr hs)
      omega
    symm; exact compare_lt_iff_lt.mpr h_neg

theorem compareAzNat_eq (z : AzInt) (a : AzNat) :
    z.compareAzNat a = Ord.compare z.toInt (a.toNat : Int) := by
  unfold compareAzNat toInt
  split_ifs with hs
  · -- sign = true
    have hc : Ord.compare z.abs a = AzNat.compare z.abs a := rfl
    rw [hc, AzNat.compare_eq_compare_toNat, AzNat.compare_nat_cast_int]
  · -- sign = false
    have h_neg : -(z.abs.toNat : Int) < (a.toNat : Int) := by
      have := neg_sign_abs_pos (Bool.eq_false_iff.mpr hs)
      omega
    symm; exact compare_lt_iff_lt.mpr h_neg

private lemma compare_swap_nat (a b : Nat) : (Ord.compare a b).swap = Ord.compare b a := by
  show (if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt).swap =
       (if b < a then Ordering.lt else if b = a then Ordering.eq else Ordering.gt)
  split_ifs <;> simp [Ordering.swap] <;> omega

private lemma compare_neg_int (a b : Int) : Ord.compare a b = Ord.compare (-b) (-a) := by
  rcases h : Ord.compare a b with _ | _ | _
  · exact (compare_lt_iff_lt.mpr (by have := compare_lt_iff_lt.mp h; omega)).symm
  · exact (compare_eq_iff_eq.mpr (by have := compare_eq_iff_eq.mp h; omega)).symm
  · exact (compare_gt_iff_gt.mpr (by have := compare_gt_iff_gt.mp h; omega)).symm

private lemma Int64.neg_toUInt64_toNat_eq {i : Int64} (hi : i < 0) :
    ((-i).toUInt64.toNat : Int) = -i.toInt := by
  have h_neg : i.toInt < 0 := by rwa [Int64.lt_iff_toInt_lt] at hi
  have h1 : (-i).toUInt64.toNat = (-i).toBitVec.toNat := rfl
  have h2 : i.toInt = i.toBitVec.toInt := rfl
  have h3 : (-i).toBitVec = -i.toBitVec := rfl
  rw [h1, h3, h2]
  rw [h2] at h_neg
  have h_lt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
  have h_toInt_eq : i.toBitVec.toInt = ↑i.toBitVec.toNat - (2^64 : Int) := by
    simp only [BitVec.toInt] at h_neg ⊢
    split_ifs at h_neg ⊢ with hc
    · omega
    · rfl
  have h_pos : i.toBitVec.toNat > 0 := by
    simp only [BitVec.toInt] at h_neg; split_ifs at h_neg <;> omega
  have h_neg_nat : (-i.toBitVec).toNat = 2^64 - i.toBitVec.toNat := by
    have hx := @BitVec.toNat_neg 64 i.toBitVec
    rw [hx]; exact Nat.mod_eq_of_lt (by omega)
  rw [h_neg_nat, h_toInt_eq]
  omega

theorem compareInt64_eq (z : AzInt) (i : Int64) :
    z.compareInt64 i = Ord.compare z.toInt i.toInt := by
  unfold compareInt64
  split_ifs with hs hi hs2
  · -- sign = true, i < 0
    have h_neg : i.toInt < 0 := by rwa [Int64.lt_iff_toInt_lt] at hi
    have h_pos : z.toInt ≥ 0 := by unfold toInt; rw [ite_eq_left hs]; exact Int.natCast_nonneg _
    symm; exact compare_gt_iff_gt.mpr (by omega)
  · -- sign = true, i ≥ 0
    rw [AzNat.compareUInt64_eq]
    have h_eq : (i.toUInt64.toNat : Int) = i.toInt := by
      have h_nn : ¬i.toInt < 0 := by rwa [Int64.lt_iff_toInt_lt] at hi
      have h1 : i.toUInt64.toNat = i.toBitVec.toNat := rfl
      have h2 : i.toInt = i.toBitVec.toInt := rfl
      rw [h1, h2]; rw [h2] at h_nn
      have h_lt : i.toBitVec.toNat < 2^64 := i.toBitVec.isLt
      unfold BitVec.toInt at h_nn ⊢
      split_ifs with h
      · rfl
      · exfalso; simp only [not_lt] at h
        split_ifs at h_nn with h2 <;> omega
    unfold toInt; rw [ite_eq_left hs]
    rw [AzNat.compare_nat_cast_int, h_eq]
  · -- sign = false, i < 0: compare two negatives
    rw [AzNat.compareUInt64_eq, compare_swap_nat, AzNat.compare_nat_cast_int]
    have h_neg_eq := Int64.neg_toUInt64_toNat_eq hs2
    unfold toInt; rw [ite_eq_right hs, h_neg_eq, compare_neg_int]
    congr 1; omega
  · -- sign = false, i ≥ 0
    have h_neg := neg_sign_toInt_neg (Bool.eq_false_iff.mpr hs)
    have h_nn : i.toInt ≥ 0 := by
      have : ¬i.toInt < 0 := by rwa [Int64.lt_iff_toInt_lt] at hs2
      omega
    symm; exact compare_lt_iff_lt.mpr (by omega)

instance : LinearOrder AzInt where
  le_refl := le_refl
  le_trans a b c := le_trans a b c
  lt_iff_le_not_ge := lt_iff_le_not_ge
  le_antisymm a b := le_antisymm a b
  le_total := le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  min_def := fun _ _ => rfl
  max_def := fun _ _ => rfl
  compare := compare
  compare_eq_compareOfLessAndEq := compare_eq_compareOfLessAndEq

end Azurite.AzInt
