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
    rw [if_pos ha]
  · have ht : a.toInt = b.toInt := compare_eq_iff_eq.mp hc2
    have h1 : ¬ (a.toInt < b.toInt) := by omega
    have h_not_lt : ¬ (a < b) := fun h => h1 (hl1.mp h)
    have ha : a = b := he1.mpr ht
    rw [if_neg h_not_lt, if_pos ha]
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
    rw [if_neg h1, if_neg h2]

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
