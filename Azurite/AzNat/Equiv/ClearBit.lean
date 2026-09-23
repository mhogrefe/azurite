import Azurite.AzNat.ClearBit
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.SetBit
import Azurite.AzNat.Equiv.TestBit
import Azurite.UInt64.Equiv.ClearBit

namespace Azurite.AzNat

theorem toNat_clearBit (n : AzNat) (i : Nat) :
    (n.clearBit i).toNat = Nat.ldiff n.toNat (2 ^ i) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_ldiff, Nat.testBit_two_pow]
  conv_rhs => rw [testBit_toNat_limbs]
  have hr_lt : j % 64 < 64 := Nat.mod_lt _ (by omega)
  have hj_decomp : j = (j % 64) + 64 * (j / 64) := by omega
  have h_size_eq : n.limbs.toList.length = n.limbs.size := rfl
  by_cases h_in_range : i / 64 < n.limbs.size
  · -- Case A: i / 64 < n.limbs.size — one existing limb is modified in place.
    simp only [clearBit, dite_eq_left h_in_range]
    rw [toNat_ofLimbs, Array.toList_set]
    conv_lhs => rw [hj_decomp]
    rw [testBit_toNatLimbsList_aux _ _ hr_lt]
    simp only [List.length_set]
    by_cases hq : j / 64 < n.limbs.toList.length
    · rw [dite_eq_left hq, dite_eq_left hq, List.getElem_set]
      by_cases hqi : i / 64 = j / 64
      · rw [ite_eq_left hqi, UInt64.testBit_toNat_clearBit]
        have h_limb_eq : n.limbs[i / 64]'h_in_range = n.limbs.toList[j / 64]'hq := by
          rw [← Array.getElem_toList]; congr 1
        rw [h_limb_eq, decide_mod_eq_of_div_eq hqi]
      · rw [ite_eq_right hqi]
        have h_ij : i ≠ j := fun h => hqi (by rw [h])
        rw [decide_eq_false h_ij, Bool.not_false, Bool.and_true]
    · rw [dite_eq_right hq, dite_eq_right hq]
      have h_ij : i ≠ j := by
        intro h
        apply hq
        rw [← h, h_size_eq]
        exact h_in_range
      rw [decide_eq_false h_ij, Bool.not_false, Bool.and_true]
  · -- Case B: i / 64 ≥ n.limbs.size — n unchanged (bit already 0).
    simp only [clearBit, dite_eq_right h_in_range]
    push Not at h_in_range
    conv_lhs => rw [hj_decomp]
    show Nat.testBit (toNatLimbsList _) _ = _
    rw [testBit_toNatLimbsList_aux _ _ hr_lt]
    by_cases hq : j / 64 < n.limbs.toList.length
    · rw [dite_eq_left hq]
      have h_ij : i ≠ j := by
        intro h
        rw [← h, h_size_eq] at hq
        omega
      rw [decide_eq_false h_ij, Bool.not_false, Bool.and_true]
    · rw [dite_eq_right hq, Bool.false_and]

theorem clearBit_ofNat (n i : Nat) : clearBit (ofNat n) i = ofNat (Nat.ldiff n (2 ^ i)) := by
  apply toNat_injective
  rw [toNat_clearBit, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
