import Azurite.AzNat.GetBits
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TestBit

namespace Azurite.AzNat

/-! ### Bit-level helpers -/

/-- Bit at position `r + 64 * q` of `n.toNat` reads limb `q` if it exists. -/
private lemma testBit_toNat_limb (n : AzNat) (q r : Nat) (hr : r < 64) :
    n.toNat.testBit (r + 64 * q) =
      if h : q < n.limbs.size then (n.limbs[q]'h).toNat.testBit r else false := by
  have h_size_eq : n.limbs.size = n.limbs.toList.length := rfl
  change (toNatLimbsList n.limbs.toList).testBit (r + 64 * q) = _
  rw [testBit_toNatLimbsList_aux q r hr]
  by_cases h : q < n.limbs.size
  · have h' : q < n.limbs.toList.length := h_size_eq ▸ h
    simp [h, Array.getElem_toList]
  · have h' : ¬ q < n.limbs.toList.length := fun hc => h (h_size_eq ▸ hc)
    simp [h]

/-- Bit `k` of UInt64 right-shift by `s` equals bit `k + s` of input, for `s < 64`. -/
private lemma testBit_uint64_shiftRight (u : UInt64) (s k : Nat) (hs : s < 64) :
    (u >>> UInt64.ofNat s).toNat.testBit k = u.toNat.testBit (k + s) := by
  rw [UInt64.toNat_shiftRight]
  have h1 : (UInt64.ofNat s).toNat = s := Nat.mod_eq_of_lt (by omega)
  rw [show (UInt64.ofNat s).toNat % 64 = s from by rw [h1, Nat.mod_eq_of_lt hs],
      Nat.shiftRight_eq_div_pow, Nat.testBit_div_two_pow]

/-- Bit `k` of UInt64 left-shift by `s`: `false` if `k < s`, else bit `k - s` of input
    (also `false` if `k ≥ 64`), for `s < 64`. -/
private lemma testBit_uint64_shiftLeft (u : UInt64) (s k : Nat) (hs : s < 64) :
    (u <<< UInt64.ofNat s).toNat.testBit k =
      (decide (s ≤ k) && decide (k < 64) && u.toNat.testBit (k - s)) := by
  rw [UInt64.toNat_shiftLeft]
  have h1 : (UInt64.ofNat s).toNat = s := Nat.mod_eq_of_lt (by omega)
  rw [show (UInt64.ofNat s).toNat % 64 = s from by rw [h1, Nat.mod_eq_of_lt hs]]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  by_cases hsk : s ≤ k
  · by_cases hk : k < 64
    · simp [hsk, hk]
    · simp [hk]
  · simp [hsk]

/-- `(1 <<< width) - 1` in UInt64 evaluates to `2^width - 1` (for `width < 64`). -/
private lemma uint64_low_mask_toNat (width : Nat) (hw : width < 64) :
    (((1 : UInt64) <<< UInt64.ofNat width) - 1).toNat = 2 ^ width - 1 := by
  have h1 : ((1 : UInt64) <<< UInt64.ofNat width).toNat = 2 ^ width := by
    rw [UInt64.toNat_shiftLeft, show ((1 : UInt64).toNat = 1) from rfl]
    have : (UInt64.ofNat width).toNat = width := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.one_shiftLeft, Nat.mod_eq_of_lt hw]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hw)
  rw [UInt64.toNat_sub, h1]
  change (2 ^ 64 - 1 + 2 ^ width) % 2 ^ 64 = 2 ^ width - 1
  have h2pow : 2 ^ width < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hw
  have h2pos : 0 < 2 ^ width := Nat.two_pow_pos _
  rw [show 2 ^ 64 - 1 + 2 ^ width = 2 ^ 64 + (2 ^ width - 1) from by omega]
  omega

/-- Bit `k + i` of `n.toNat` reads either limb `q` at offset `k + r` (if it fits)
    or limb `q + 1` at offset `k + r - 64`, where `q = i / 64`, `r = i % 64`,
    `r < 64`. -/
private lemma testBit_n_at_offset (n : AzNat) (i k : Nat) (hk : k < 64) :
    n.toNat.testBit (k + i) =
      if k + i % 64 < 64 then
        if h : i / 64 < n.limbs.size then
          (n.limbs[i / 64]'h).toNat.testBit (k + i % 64) else false
      else
        if h : i / 64 + 1 < n.limbs.size then
          (n.limbs[i / 64 + 1]'h).toNat.testBit (k + i % 64 - 64) else false := by
  have hr_lt : i % 64 < 64 := Nat.mod_lt _ (by omega)
  by_cases hkr : k + i % 64 < 64
  · simp only [hkr, if_true]
    rw [show k + i = (k + i % 64) + 64 * (i / 64) from by omega,
        testBit_toNat_limb n (i / 64) (k + i % 64) hkr]
  · simp only [hkr, if_false]
    push Not at hkr
    have hkr_sub : k + i % 64 - 64 < 64 := by omega
    rw [show k + i = (k + i % 64 - 64) + 64 * (i / 64 + 1) from by omega,
        testBit_toNat_limb n (i / 64 + 1) (k + i % 64 - 64) hkr_sub]

/-! ### Bit-level identity for `getBitsAsLimb` -/

/-- The key bit-level identity: bit `k` of `getBitsAsLimb i j` matches bit `k + i` of `n.toNat`
    when `k < j - i`, and is `false` otherwise. -/
private lemma testBit_getBitsAsLimb (n : AzNat) (i j : Nat) (h : j - i ≤ 64) (k : Nat) :
    (n.getBitsAsLimb i j h).toNat.testBit k =
      (decide (k < j - i) && n.toNat.testBit (k + i)) := by
  unfold getBitsAsLimb
  by_cases hij : i ≥ j
  · simp [hij, show j - i = 0 from by omega]
  push Not at hij
  rw [if_neg (by omega : ¬ i ≥ j)]
  have hr_lt : i % 64 < 64 := Nat.mod_lt _ (by omega)
  have hwidth_le : j - i ≤ 64 := h
  -- Helper: bound on (any UInt64).toNat
  have h_uint64_high : ∀ (u : UInt64), ¬ k < 64 → u.toNat.testBit k = false := by
    intros u hk
    apply Nat.testBit_eq_false_of_lt
    have := UInt64.toNat_lt u
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
  by_cases hq : i / 64 ≥ n.limbs.size
  · -- LHS = 0. Need RHS = false.
    rw [dif_pos hq]
    change (0 : Nat).testBit k = _
    rw [Nat.zero_testBit]
    symm
    rw [Bool.and_eq_false_iff]
    by_cases hkw : k < j - i
    · right
      have hk_lt_64 : k < 64 := lt_of_lt_of_le hkw hwidth_le
      rw [testBit_n_at_offset n i k hk_lt_64]
      by_cases hkr : k + i % 64 < 64
      · simp only [hkr, if_true]; simp [show ¬ i / 64 < n.limbs.size from by omega]
      · simp only [hkr, if_false]; simp [show ¬ i / 64 + 1 < n.limbs.size from by omega]
    · left; simp [hkw]
  -- Now i / 64 < n.limbs.size.
  push Not at hq
  rw [dif_neg (by omega : ¬ i / 64 ≥ n.limbs.size)]
  -- Compute bit `k` of the (possibly cross-limb) shifted+masked expression.
  -- Step 1: bit `k` of `n.limbs[q] >>> r`.
  have h_lowBits_k : (n.limbs[i / 64] >>> UInt64.ofNat (i % 64)).toNat.testBit k =
      (decide (k < 64) && (n.limbs[i / 64]).toNat.testBit (k + i % 64)) := by
    by_cases hk_64 : k < 64
    · rw [testBit_uint64_shiftRight _ _ _ hr_lt]
      simp [hk_64]
    · rw [h_uint64_high _ hk_64]
      simp [hk_64]
  -- Step 2: bit `k` of `n.limbs[q+1] <<< (64 - i % 64)` (when `i % 64 > 0`).
  have h_highBits_k : ∀ (hq1 : i / 64 + 1 < n.limbs.size) (hr_pos : 0 < i % 64),
      (n.limbs[i / 64 + 1] <<< UInt64.ofNat (64 - i % 64)).toNat.testBit k =
        (decide (64 - i % 64 ≤ k) && decide (k < 64) &&
          (n.limbs[i / 64 + 1]).toNat.testBit (k - (64 - i % 64))) := by
    intros hq1 hr_pos
    exact testBit_uint64_shiftLeft _ _ _ (by omega)
  -- Define a clean way to write the RHS using `testBit_n_at_offset` after dispatching the case.
  have h_target : ∀ (hk_lt : k < 64),
      n.toNat.testBit (k + i) =
        (if k + i % 64 < 64 then
          (n.limbs[i / 64]).toNat.testBit (k + i % 64)
        else
          if h : i / 64 + 1 < n.limbs.size then
            (n.limbs[i / 64 + 1]'h).toNat.testBit (k + i % 64 - 64)
          else false) := by
    intros hk_lt
    rw [testBit_n_at_offset n i k hk_lt]
    by_cases hkr : k + i % 64 < 64
    · simp [hkr, show i / 64 < n.limbs.size from hq]
    · simp [hkr]
  -- Now split on width = 64 (no mask) and r + width > 64 (cross or not).
  by_cases hwidth : j - i = 64
  · -- No mask. Combined is the result.
    have hkw : k < j - i ↔ k < 64 := by rw [hwidth]
    rw [if_pos hwidth]
    have hcross : i % 64 + (j - i) > 64 ↔ 0 < i % 64 := by rw [hwidth]; omega
    by_cases hr_pos : 0 < i % 64
    · -- Cross-limb branch (since r + 64 > 64 ↔ r > 0).
      rw [if_pos (hcross.mpr hr_pos)]
      by_cases hq1 : i / 64 + 1 < n.limbs.size
      · rw [dif_pos hq1, UInt64.toNat_or, Nat.testBit_or, h_lowBits_k, h_highBits_k hq1 hr_pos]
        by_cases hk_64 : k < 64
        · simp only [hk_64, decide_true, Bool.true_and, Bool.and_true, hwidth,
                     decide_true]
          rw [h_target hk_64]
          by_cases hkr : k + i % 64 < 64
          · -- low limb only: highBits.testBit k = false
            have : ¬ (64 - i % 64 ≤ k) := by omega
            simp [hkr, this]
          · -- high limb: lowBits.testBit k = false
            push Not at hkr
            have h_low_false : (n.limbs[i / 64]).toNat.testBit (k + i % 64) = false := by
              apply Nat.testBit_eq_false_of_lt
              have := UInt64.toNat_lt n.limbs[i / 64]
              exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hkr)
            simp only [show ¬ k + i % 64 < 64 from by omega, if_false]
            rw [h_low_false]
            simp only [Bool.false_or]
            have hs_le : 64 - i % 64 ≤ k := by omega
            simp only [hs_le, decide_true, Bool.true_and]
            simp [show i / 64 + 1 < n.limbs.size from hq1,
                  show k - (64 - i % 64) = k + i % 64 - 64 from by omega]
        · -- k ≥ 64: both bits false.
          simp only [hk_64, decide_false, Bool.false_and, Bool.false_or, Bool.and_false]
          have : ¬ k < j - i := by rw [hwidth]; exact hk_64
          simp [this]
      · -- q + 1 ≥ size, only lowBits.
        rw [dif_neg hq1, h_lowBits_k]
        by_cases hk_64 : k < 64
        · simp only [hk_64, decide_true, Bool.true_and, hkw.mpr hk_64]
          rw [h_target hk_64]
          by_cases hkr : k + i % 64 < 64
          · simp [hkr]
          · push Not at hkr
            have h_low_false : (n.limbs[i / 64]).toNat.testBit (k + i % 64) = false := by
              apply Nat.testBit_eq_false_of_lt
              have := UInt64.toNat_lt n.limbs[i / 64]
              exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hkr)
            simp only [show ¬ k + i % 64 < 64 from by omega, if_false]
            rw [h_low_false]
            simp [show ¬ i / 64 + 1 < n.limbs.size from hq1]
        · simp only [hk_64, decide_false, Bool.false_and]
          have : ¬ k < j - i := by rw [hwidth]; exact hk_64
          simp [this]
    · -- r = 0: no cross even though width = 64.
      push Not at hr_pos
      rw [if_neg (by simp [show ¬ i % 64 + (j - i) > 64 from by omega])]
      rw [h_lowBits_k]
      have hr_eq : i % 64 = 0 := by omega
      by_cases hk_64 : k < 64
      · simp only [hk_64, decide_true, Bool.true_and, hwidth, decide_true]
        rw [h_target hk_64, hr_eq, Nat.add_zero]
        simp [hk_64]
      · simp only [hk_64, decide_false, Bool.false_and]
        have : ¬ k < j - i := by rw [hwidth]; exact hk_64
        simp [this]
  · -- Mask present: width < 64.
    rw [if_neg hwidth]
    have hw_lt : j - i < 64 := lt_of_le_of_ne hwidth_le hwidth
    rw [UInt64.toNat_and, Nat.testBit_and, uint64_low_mask_toNat (j - i) hw_lt,
        Nat.testBit_two_pow_sub_one]
    -- Goal LHS now has `combined.testBit k && decide (k < j - i)`.
    -- Show combined.testBit k = n.toNat.testBit (k + i) when k < j - i.
    by_cases hkw : k < j - i
    · simp only [hkw, decide_true, Bool.and_true]
      have hk_64 : k < 64 := lt_of_lt_of_le hkw (Nat.le_of_lt hw_lt)
      -- Now compute combined.testBit k.
      by_cases hcross : i % 64 + (j - i) > 64
      · rw [if_pos hcross]
        by_cases hq1 : i / 64 + 1 < n.limbs.size
        · rw [dif_pos hq1, UInt64.toNat_or, Nat.testBit_or, h_lowBits_k,
              testBit_uint64_shiftLeft _ _ _ (by omega : 64 - i % 64 < 64)]
          rw [h_target hk_64]
          have hr_pos : 0 < i % 64 := by omega
          by_cases hkr : k + i % 64 < 64
          · simp only [hkr, if_true, hk_64, decide_true, Bool.true_and]
            have hs_not_le : ¬ (64 - i % 64 ≤ k) := by omega
            simp [hs_not_le]
          · push Not at hkr
            have h_low_false : (n.limbs[i / 64]).toNat.testBit (k + i % 64) = false := by
              apply Nat.testBit_eq_false_of_lt
              have := UInt64.toNat_lt n.limbs[i / 64]
              exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hkr)
            simp only [show ¬ k + i % 64 < 64 from by omega, if_false, hk_64, decide_true,
                       Bool.true_and, Bool.and_true]
            rw [h_low_false]
            simp only [Bool.false_or]
            have hs_le : 64 - i % 64 ≤ k := by omega
            simp only [hs_le, decide_true, Bool.true_and]
            simp [show i / 64 + 1 < n.limbs.size from hq1,
                  show k - (64 - i % 64) = k + i % 64 - 64 from by omega]
        · rw [dif_neg hq1, h_lowBits_k]
          rw [h_target hk_64]
          by_cases hkr : k + i % 64 < 64
          · simp [hkr, hk_64]
          · push Not at hkr
            have h_low_false : (n.limbs[i / 64]).toNat.testBit (k + i % 64) = false := by
              apply Nat.testBit_eq_false_of_lt
              have := UInt64.toNat_lt n.limbs[i / 64]
              exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) hkr)
            simp only [show ¬ k + i % 64 < 64 from by omega, if_false, hk_64, decide_true,
                       Bool.true_and]
            rw [h_low_false]
            simp [show ¬ i / 64 + 1 < n.limbs.size from hq1]
      · rw [if_neg hcross, h_lowBits_k]
        rw [h_target hk_64]
        have hkr : k + i % 64 < 64 := by omega
        simp [hkr, hk_64]
    · -- k ≥ width: mask kills, RHS false.
      simp [hkw]

/-! ### Main correctness theorems -/

/-- **Correctness of `getBitsAsLimb`.** -/
theorem toNat_getBitsAsLimb (n : AzNat) (i j : Nat) (h : j - i ≤ 64) :
    (n.getBitsAsLimb i j h).toNat = n.toNat / 2 ^ i % 2 ^ (j - i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, testBit_getBitsAsLimb n i j h k,
      Nat.add_comm k i]

/-- **Correctness of `getBits`.** -/
theorem toNat_getBits (n : AzNat) (i j : Nat) :
    (n.getBits i j).toNat = n.toNat / 2 ^ i % 2 ^ (j - i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hij : i ≥ j
  · have h_func : n.getBits i j = 0 := by unfold getBits; simp [hij]
    rw [h_func, show j - i = 0 from by omega]
    simp
  push Not at hij
  unfold getBits
  rw [if_neg (by omega : ¬ i ≥ j), toNat_ofLimbs]
  set width := j - i with hwidth_def
  set numLimbs := (width + 63) / 64 with hnum_def
  set arr : Array UInt64 := (Array.range numLimbs).map fun l =>
    n.getBitsAsLimb (i + l * 64) (min (i + l * 64 + 64) j) (by omega)
  have h_arr_size : arr.size = numLimbs := by simp [arr]
  have h_arr_get : ∀ l (hl : l < numLimbs),
      arr.toList[l]'(by rw [Array.length_toList, h_arr_size]; exact hl) =
        n.getBitsAsLimb (i + l * 64) (min (i + l * 64 + 64) j) (by omega) := by
    intros l hl
    rw [Array.getElem_toList]
    simp [arr, Array.getElem_range]
  have hr_lt : k % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [show k = k % 64 + 64 * (k / 64) from by omega,
      testBit_toNatLimbsList_aux (k / 64) (k % 64) hr_lt]
  have h_arr_size_eq : arr.toList.length = numLimbs := by rw [Array.length_toList]; exact h_arr_size
  by_cases hsl : k / 64 < numLimbs
  · have hsl' : k / 64 < arr.toList.length := by rw [h_arr_size_eq]; exact hsl
    simp only [hsl', dif_pos]
    rw [h_arr_get (k / 64) hsl,
        testBit_getBitsAsLimb n (i + (k / 64) * 64)
          (min (i + (k / 64) * 64 + 64) j) (by omega) (k % 64)]
    -- LHS = decide (k % 64 < min(...) - (i + k/64*64)) && n.toNat.testBit (k % 64 + (i + k/64*64))
    have h_pos : k % 64 + (i + k / 64 * 64) = k % 64 + 64 * (k / 64) + i := by ring
    rw [h_pos, show k % 64 + 64 * (k / 64) = k from by omega]
    have h_width_eq : min (i + k / 64 * 64 + 64) j - (i + k / 64 * 64) =
        min 64 (width - k / 64 * 64) := by rw [hwidth_def]; omega
    rw [h_width_eq]
    by_cases hkw : k < width
    · have h_iff : k % 64 < min 64 (width - k / 64 * 64) := by
        rw [lt_min_iff]; refine ⟨hr_lt, ?_⟩; omega
      simp [h_iff, hkw]
    · have : ¬ k % 64 < min 64 (width - k / 64 * 64) := by
        intro hc; rw [lt_min_iff] at hc; omega
      simp [this, hkw]
  · -- k/64 ≥ numLimbs: no such limb; bit is 0. Also k ≥ width.
    have hsl' : ¬ k / 64 < arr.toList.length := by rw [h_arr_size_eq]; exact hsl
    simp only [hsl', dif_neg, not_false_eq_true]
    push Not at hsl
    have h_k_ge : k ≥ width := by
      have h1 : numLimbs * 64 ≥ width := by rw [hnum_def]; omega
      have h2 : k ≥ numLimbs * 64 := by have := Nat.div_mul_le_self k 64; omega
      omega
    have h_eq_k : k % 64 + 64 * (k / 64) = k := by omega
    rw [h_eq_k]
    have : ¬ k < width := by omega
    simp [this]

/-- **AzNat-level equivalence**: `getBits i j` matches the obvious-but-inefficient spec
    `(n >>> i).modPow2 (j - i)`. -/
theorem getBits_eq_shiftRight_modPow2 (n : AzNat) (i j : Nat) :
    n.getBits i j = (n >>> i).modPow2 (j - i) := by
  apply toNat_injective
  rw [toNat_getBits, toNat_modPow2, toNat_hShiftRight, Nat.shiftRight_eq_div_pow]

end Azurite.AzNat
