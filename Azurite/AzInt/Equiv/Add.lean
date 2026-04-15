import Azurite.AzInt.Add
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Compare

namespace Azurite.AzInt

/-- `mkNorm true a` represents `a` nonnegatively. -/
lemma toInt_mkNorm_true (a : AzNat) : (mkNorm true a).toInt = (a.toNat : Int) := by
  unfold mkNorm
  by_cases h : a = 0
  · simp only [h, ↓reduceDIte]
    show ((0 : AzInt)).toInt = ((0 : AzNat).toNat : Int)
    rfl
  · simp only [h, ↓reduceDIte]
    show (if true then (a.toNat : Int) else _) = _
    simp

/-- `mkNorm false a` represents `-a` when `a ≠ 0`. -/
lemma toInt_mkNorm_false (a : AzNat) (h : a ≠ 0) :
    (mkNorm false a).toInt = -(a.toNat : Int) := by
  unfold mkNorm
  simp only [h, ↓reduceDIte]
  show (if false then _ else -(a.toNat : Int)) = _
  simp

/-- Correctness of `AzInt.addUInt64`. -/
theorem toInt_addUInt64 (z : AzInt) (u : UInt64) :
    (z.addUInt64 u).toInt = z.toInt + (u.toNat : Int) := by
  unfold addUInt64
  have h_tz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  rw [h_tz]
  by_cases hs : z.sign
  · simp only [hs, ↓reduceIte]
    rw [toInt_mkNorm_true, AzNat.toNat_addUInt64]
    push_cast; ring
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    rw [AzNat.compareUInt64_eq]
    rcases h_cmp : Ord.compare z.abs.toNat u.toNat with _ | _ | _
    · -- .lt : z.abs.toNat < u.toNat
      have h_lt : z.abs.toNat < u.toNat := by
        have := Nat.compare_eq_lt.mp h_cmp; omega
      have h_sub_pos : u.toAzNat - z.abs ≠ 0 := by
        intro hc
        have hc' : (u.toAzNat - z.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub, UInt64.toNat_toAzNat] at hc'
        omega
      rw [toInt_mkNorm_true, AzNat.toNat_sub, UInt64.toNat_toAzNat]
      omega
    · -- .eq : z.abs.toNat = u.toNat
      have h_eq : z.abs.toNat = u.toNat := Nat.compare_eq_eq.mp h_cmp
      rw [toInt_zero]
      omega
    · -- .gt : z.abs.toNat > u.toNat
      have h_gt : u.toNat < z.abs.toNat := Nat.compare_eq_gt.mp h_cmp
      have h_sub_pos : z.abs.subUInt64 u ≠ 0 := by
        intro hc
        have hc' : (z.abs.subUInt64 u).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_subUInt64] at hc'
        have h_abs_pos : 0 < z.abs.toNat := by omega
        omega
      rw [toInt_mkNorm_false _ h_sub_pos, AzNat.toNat_subUInt64]
      omega

/-- `ofInt`-version of `toInt_addUInt64`. -/
theorem ofInt_addUInt64 (i : Int) (u : UInt64) :
    ofInt (i + (u.toNat : Int)) = (ofInt i).addUInt64 u := by
  have h : (ofInt (i + (u.toNat : Int))).toInt = ((ofInt i).addUInt64 u).toInt := by
    rw [toInt_ofInt, toInt_addUInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Helper: relate `AzNat.compare` to `Ord.compare` on `toNat`. -/
private lemma azNat_compare_eq (a b : AzNat) :
    AzNat.compare a b = Ord.compare a.toNat b.toNat :=
  AzNat.compare_eq_compare_toNat a b

/-- Correctness of `AzInt.add`. -/
theorem toInt_add (a b : AzInt) : (a + b).toInt = a.toInt + b.toInt := by
  show (add a b).toInt = a.toInt + b.toInt
  unfold add
  have h_ta : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_tb : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  rw [h_ta, h_tb]
  have h_a_ne : a.sign = false → a.abs ≠ 0 := fun hs h0 => by
    rw [a.zero_sign h0] at hs; contradiction
  have h_b_ne : b.sign = false → b.abs ≠ 0 := fun hs h0 => by
    rw [b.zero_sign h0] at hs; contradiction
  rcases hsa : a.sign with _ | _ <;> rcases hsb : b.sign with _ | _
  all_goals simp only
  · -- false, false
    have hanz : a.abs ≠ 0 := h_a_ne hsa
    have hbnz : b.abs ≠ 0 := h_b_ne hsb
    have h_sum_ne : a.abs + b.abs ≠ 0 := by
      intro hc
      have : (a.abs + b.abs).toNat = 0 := by rw [hc]; rfl
      rw [AzNat.toNat_add] at this
      have : a.abs.toNat = 0 := by omega
      exact hanz (AzNat.toNat_injective (by rw [this, AzNat.toNat_zero]))
    rw [toInt_mkNorm_false _ h_sum_ne, AzNat.toNat_add]
    push_cast; ring
  · -- false, true: -a.abs + b.abs
    rw [azNat_compare_eq]
    rcases h_cmp : Ord.compare a.abs.toNat b.abs.toNat with _ | _ | _
    · have h_lt : a.abs.toNat < b.abs.toNat := by
        have := Nat.compare_eq_lt.mp h_cmp; omega
      have h_sub_ne : b.abs - a.abs ≠ 0 := by
        intro hc
        have : (b.abs - a.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub] at this; omega
      rw [toInt_mkNorm_true, AzNat.toNat_sub]
      push_cast; omega
    · have h_eq : a.abs.toNat = b.abs.toNat := Nat.compare_eq_eq.mp h_cmp
      rw [toInt_zero]; push_cast; omega
    · have h_gt : b.abs.toNat < a.abs.toNat := Nat.compare_eq_gt.mp h_cmp
      have h_sub_ne : a.abs - b.abs ≠ 0 := by
        intro hc
        have : (a.abs - b.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub] at this; omega
      rw [toInt_mkNorm_false _ h_sub_ne, AzNat.toNat_sub]
      push_cast; omega
  · -- true, false: a.abs - b.abs
    rw [azNat_compare_eq]
    rcases h_cmp : Ord.compare a.abs.toNat b.abs.toNat with _ | _ | _
    · have h_lt : a.abs.toNat < b.abs.toNat := by
        have := Nat.compare_eq_lt.mp h_cmp; omega
      have h_sub_ne : b.abs - a.abs ≠ 0 := by
        intro hc
        have : (b.abs - a.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub] at this; omega
      rw [toInt_mkNorm_false _ h_sub_ne, AzNat.toNat_sub]
      push_cast; omega
    · have h_eq : a.abs.toNat = b.abs.toNat := Nat.compare_eq_eq.mp h_cmp
      rw [toInt_zero]; push_cast; omega
    · have h_gt : b.abs.toNat < a.abs.toNat := Nat.compare_eq_gt.mp h_cmp
      have h_sub_ne : a.abs - b.abs ≠ 0 := by
        intro hc
        have : (a.abs - b.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub] at this; omega
      rw [toInt_mkNorm_true, AzNat.toNat_sub]
      push_cast; omega
  · -- true, true
    rw [toInt_mkNorm_true, AzNat.toNat_add]
    push_cast; ring

/-- `ofInt`-version of `toInt_add`. -/
theorem ofInt_add (i j : Int) : ofInt (i + j) = ofInt i + ofInt j := by
  have h : (ofInt (i + j)).toInt = (ofInt i + ofInt j).toInt := by
    rw [toInt_ofInt, toInt_add, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
