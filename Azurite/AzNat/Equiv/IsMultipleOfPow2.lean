import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.SetBit

namespace Azurite.AzNat

/-- 2^k divides n iff all bits of n at positions < k are zero. -/
private lemma pow_two_dvd_iff_testBit (n k : Nat) :
    2 ^ k ∣ n ↔ ∀ j, j < k → n.testBit j = false := by
  rw [Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h j hj
    have hmod : (n % 2 ^ k).testBit j = n.testBit j := by
      rw [Nat.testBit_mod_two_pow]; simp [hj]
    rw [← hmod, h, Nat.zero_testBit]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hjk : j < k
    · simp [hjk, h j hjk]
    · simp [hjk]

/-- The numeric value of the low-`r`-bit mask `(1 <<< r) - 1` in UInt64 is `2^r - 1`. -/
private lemma lowMask_toNat (r : Nat) (hr : r < 64) :
    (((1 : UInt64) <<< UInt64.ofNat r) - 1).toNat = 2 ^ r - 1 := by
  have h1 : ((1 : UInt64) <<< UInt64.ofNat r).toNat = 2 ^ r := by
    rw [UInt64.toNat_shiftLeft, show ((1 : UInt64).toNat = 1) from rfl]
    have hofNat : (UInt64.ofNat r).toNat = r := Nat.mod_eq_of_lt (by omega)
    rw [hofNat, Nat.one_shiftLeft, Nat.mod_eq_of_lt hr]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hr)
  rw [UInt64.toNat_sub, h1]
  change (2 ^ 64 - 1 + 2 ^ r) % 2 ^ 64 = 2 ^ r - 1
  have h2pow : 2 ^ r < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hr
  have h2pos : 0 < 2 ^ r := Nat.two_pow_pos _
  rw [show 2 ^ 64 - 1 + 2 ^ r = 2 ^ 64 + (2 ^ r - 1) from by omega]
  omega

/-- The low-`r`-bit mask zeros out iff every low-`r` bit of `u` is zero. -/
private lemma uint64_lowMask_eq_zero_iff (u : UInt64) (r : Nat) (hr : r < 64) :
    (u &&& (((1 : UInt64) <<< UInt64.ofNat r) - 1) == 0) = true ↔
      ∀ b, b < r → u.toNat.testBit b = false := by
  rw [beq_iff_eq]
  have h_toNat_eq :
      u &&& (((1 : UInt64) <<< UInt64.ofNat r) - 1) = 0 ↔
        (u &&& (((1 : UInt64) <<< UInt64.ofNat r) - 1)).toNat = 0 :=
    ⟨fun h => h ▸ rfl, fun h => UInt64.eq_of_toNat_eq (by rw [h]; rfl)⟩
  rw [h_toNat_eq, UInt64.toNat_and, lowMask_toNat r hr,
      Nat.and_two_pow_sub_one_eq_mod]
  constructor
  · intro hmod b hb
    have hbit : (u.toNat % 2 ^ r).testBit b = u.toNat.testBit b := by
      rw [Nat.testBit_mod_two_pow]; simp [hb]
    rw [← hbit, hmod, Nat.zero_testBit]
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hbr : b < r
    · simp [hbr, hall b hbr]
    · simp [hbr]

/-- `n.toNat.testBit j` expressed as a bit test on the appropriate limb. -/
private lemma testBit_toNat_limb (n : AzNat) (j : Nat) (h : j / 64 < n.limbs.size) :
    n.toNat.testBit j = Nat.testBit (n.limbs[j / 64]'h).toNat (j % 64) := by
  rw [testBit_toNat_limbs]
  have h' : j / 64 < n.limbs.toList.length := h
  rw [dif_pos h', ← Array.getElem_toList]

/-- In case B (`k / 64 ≥ n.limbs.size`), `n.toNat < 2 ^ k`. -/
private lemma toNat_lt_two_pow_of_size_le (n : AzNat) (k : Nat)
    (h : n.limbs.size ≤ k / 64) : n.toNat < 2 ^ k := by
  have h1 : n.toNat < 2 ^ (64 * n.limbs.size) :=
    toNatLimbsList_lt_pow n.limbs.toList
  have hk_le : 64 * (k / 64) ≤ k := Nat.mul_div_le k 64
  have hsize_le : 64 * n.limbs.size ≤ 64 * (k / 64) := Nat.mul_le_mul_left 64 h
  have h3 : (2 : Nat) ^ (64 * n.limbs.size) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem isMultipleOfPow2_eq (n : AzNat) (k : Nat) :
    n.isMultipleOfPow2 k = decide (2 ^ k ∣ n.toNat) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, pow_two_dvd_iff_testBit]
  unfold AzNat.isMultipleOfPow2
  have hr_lt : k % 64 < 64 := Nat.mod_lt _ (by omega)
  by_cases h_in_range : k / 64 < n.limbs.size
  · -- Case A: the boundary bit lives inside an existing limb.
    rw [dif_pos h_in_range]
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    rw [allZeroLoop_eq_true_iff, beq_iff_eq, uint64_lowMask_eq_zero_iff _ _ hr_lt]
    constructor
    · rintro ⟨h_low_limbs, h_top⟩ j hj
      have hjq_le : j / 64 ≤ k / 64 := Nat.div_le_div_right (Nat.le_of_lt hj)
      have hj_div_lt : j / 64 < n.limbs.size := by omega
      rw [testBit_toNat_limb n j hj_div_lt]
      by_cases hjq_lt : j / 64 < k / 64
      · have h_limb_zero : n.limbs[j / 64]'hj_div_lt = 0 :=
          h_low_limbs (j / 64) hjq_lt
        rw [h_limb_zero]
        show Nat.testBit (0 : UInt64).toNat (j % 64) = false
        rw [show ((0 : UInt64).toNat = 0) from rfl, Nat.zero_testBit]
      · have hjq_eq : j / 64 = k / 64 := by omega
        have hjmod_lt : j % 64 < k % 64 := by
          have hk_decomp : k = k % 64 + 64 * (k / 64) := by omega
          have hj_decomp : j = j % 64 + 64 * (j / 64) := by omega
          rw [hjq_eq] at hj_decomp
          omega
        rcases h_top with hr0 | h_bits_zero
        · omega
        · have h_limb_eq : n.limbs[j / 64]'hj_div_lt = n.limbs[k / 64]'h_in_range := by
            congr 1
          rw [h_limb_eq]
          exact h_bits_zero (j % 64) hjmod_lt
    · intro h_all_bits_zero
      refine ⟨?_, ?_⟩
      · intro i hi
        apply UInt64.eq_of_toNat_eq
        apply Nat.eq_of_testBit_eq
        intro b
        rw [show ((0 : UInt64).toNat = 0) from rfl, Nat.zero_testBit]
        by_cases hb : b < 64
        · have hi_lt : i < n.limbs.size := by omega
          have h_in : (b + 64 * i) / 64 < n.limbs.size := by
            rw [Nat.add_mul_div_left b i (by omega : (64 : Nat) > 0)]
            rw [Nat.div_eq_of_lt hb]; omega
          rw [show b = (b + 64 * i) % 64 from by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]]
          have h_limb_eq : n.limbs[i]'hi_lt =
              n.limbs[(b + 64 * i) / 64]'h_in := by
            congr 1
            rw [Nat.add_mul_div_left b i (by omega : (64 : Nat) > 0)]
            rw [Nat.div_eq_of_lt hb]; omega
          rw [h_limb_eq, ← testBit_toNat_limb n (b + 64 * i) h_in]
          apply h_all_bits_zero
          have hk_bound : 64 * (k / 64) ≤ k := Nat.mul_div_le k 64
          have hi1 : 64 * (i + 1) ≤ 64 * (k / 64) := Nat.mul_le_mul_left 64 (by omega)
          omega
        · -- b ≥ 64: (n.limbs[i]).toNat < 2^64, so its bit b is false.
          apply Nat.testBit_eq_false_of_lt
          exact lt_of_lt_of_le (UInt64.toNat_lt _)
            (Nat.pow_le_pow_right (by omega) (by omega))
      · by_cases hr0 : k % 64 = 0
        · left; exact hr0
        · right
          intro b hb
          have h_in : (b + 64 * (k / 64)) / 64 < n.limbs.size := by
            rw [Nat.add_mul_div_left b (k / 64) (by omega : (64 : Nat) > 0)]
            rw [Nat.div_eq_of_lt (by omega)]; omega
          rw [show b = (b + 64 * (k / 64)) % 64 from by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]]
          have h_limb_eq : n.limbs[k / 64]'h_in_range =
              n.limbs[(b + 64 * (k / 64)) / 64]'h_in := by
            congr 1
            rw [Nat.add_mul_div_left b (k / 64) (by omega : (64 : Nat) > 0)]
            rw [show b / 64 = 0 from Nat.div_eq_of_lt (by omega)]; omega
          rw [h_limb_eq, ← testBit_toNat_limb n (b + 64 * (k / 64)) h_in]
          apply h_all_bits_zero
          have hk_decomp : k = k % 64 + 64 * (k / 64) := by omega
          omega
  · -- Case B: all of `n` sits strictly below 2^k.
    rw [dif_neg h_in_range]
    push Not at h_in_range
    have hbounded : n.toNat < 2 ^ k :=
      toNat_lt_two_pow_of_size_le n k h_in_range
    rw [beq_iff_eq]
    constructor
    · intro h_size_zero j hj
      have htoNat_zero : n.toNat = 0 := (toNat_eq_zero_iff n).mpr h_size_zero
      rw [htoNat_zero, Nat.zero_testBit]
    · intro h_all_bits_zero
      have h_toNat_zero : n.toNat = 0 := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.zero_testBit]
        by_cases hjk : j < k
        · exact h_all_bits_zero j hjk
        · apply Nat.testBit_eq_false_of_lt
          exact lt_of_lt_of_le hbounded (Nat.pow_le_pow_right (by omega) (by omega))
      exact (toNat_eq_zero_iff n).mp h_toNat_zero

end Azurite.AzNat
