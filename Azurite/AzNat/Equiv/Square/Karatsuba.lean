/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Mul.Karatsuba
import Azurite.AzNat.Equiv.Square

/-!
# Karatsuba squaring correctness

`karatsubaSquareLimbsRec_toNat` mirrors `karatsubaMulLimbsRec_toNat` in
`Equiv/Mul/Karatsuba.lean`, with the simplification that `A = B`: all four
slice values `(A₀, A₁, B₀, B₁)` collapse to `(A₀, A₁, A₀, A₁)`, both signs
are computed from the same `|A₀ − A₁|`, and the `middleBuf` `sameSign`
branch is forced to `true`. The cross-term simplifies algebraically:

  `D₀ + D₂ − C = A₀² + A₁² − (A₀ − A₁)² = 2 A₀ A₁`,

so the assembled buffer holds `A₀² + 2 A₀ A₁ β^k + A₁² β^{2k} = (A₀ + A₁ β^k)² = A²`.

The proof leverages the same `middle_equals_cross_terms`, `C2_le_C0_plus_C1`,
`mid_value_lt`, and `total_lt` lemmas as the mul proof — specialised to
`B := A`, where they reduce to the squaring identities above.
-/

namespace Azurite.AzNat

set_option maxHeartbeats 1600000 in
/-- Correctness of the size-tracked recursive version. -/
theorem karatsubaSquareLimbsRec_toNat (threshold : Nat) :
    ∀ (len : Nat) (a : Array UInt64) (lo : Nat) (hA : lo + len ≤ a.size),
    toNatLimbsList (karatsubaSquareLimbsRec threshold a lo len hA).val.toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intros a lo hA
    unfold karatsubaSquareLimbsRec
    by_cases h_base : len < 2 ∨ len < threshold
    · -- Base case: schoolbookSquareLimbs
      simp only [h_base, ↓reduceDIte]
      exact schoolbookSquareLimbs_toNat a lo len hA
    · -- Recursive case
      simp only [h_base, ↓reduceDIte]
      have hlen : 2 ≤ len := by omega
      set k := (len + 1) / 2 with hk_def
      set m := len - k with hm_def
      have hk_pos : 0 < k := by show 0 < (len + 1) / 2; omega
      have hk_lt : k < len := by show (len + 1) / 2 < len; omega
      have hm_pos : 0 < m := by show 0 < len - (len + 1) / 2; omega
      have hm_le : m ≤ k := by show len - (len + 1) / 2 ≤ (len + 1) / 2; omega
      have hm_lt : m < len := by show len - (len + 1) / 2 < len; omega
      have hkm : k + m = len := by
        show (len + 1) / 2 + (len - (len + 1) / 2) = len; omega
      have hA0 : lo + k ≤ a.size := by omega
      have hA1 : (lo + k) + m ≤ a.size := by omega
      have hAabs : lo + k + m ≤ a.size := by omega
      -- Bind the recursive results.
      set D0 := karatsubaSquareLimbsRec threshold a lo k hA0 with hD0_def
      set D2 := karatsubaSquareLimbsRec threshold a (lo + k) m hA1 with hD2_def
      set absA := absSubLimbsKM a lo k m hAabs hm_le hk_pos hm_pos with habsA_def
      have hAabs_lim : 0 + k ≤ absA.1.1.size := by rw [absA.1.2]; omega
      set C := karatsubaSquareLimbsRec threshold absA.1.1 0 k hAabs_lim with hC_def
      set middle := karatsubaMulLimbsRec.middleBuf k m D0.1 D2.1 C.1 true
                      D0.2 D2.2 C.2 hk_pos hm_pos hm_le with hmiddle_def
      -- Slice values.
      set A0 := toNatLimbsList ((a.toList.drop lo).take k) with hA0_val
      set A1 := toNatLimbsList ((a.toList.drop (lo + k)).take m) with hA1_val
      -- Bounds.
      have hA0_lt : A0 < 2 ^ (64 * k) := slice_lt_pow a lo k
      have hA1_lt : A1 < 2 ^ (64 * m) := slice_lt_pow a (lo + k) m
      -- IH on k, m.
      have h_D0_toNat : toNatLimbsList D0.1.toList = A0 ^ 2 := by
        rw [hD0_def]; exact ih k hk_lt a lo hA0
      have h_D2_toNat : toNatLimbsList D2.1.toList = A1 ^ 2 := by
        rw [hD2_def]; exact ih m hm_lt a (lo + k) hA1
      -- absSubLimbsKM_toNat.
      have h_absA_props := absSubLimbsKM_toNat a lo k m hAabs hm_le hk_pos hm_pos
      rw [show absSubLimbsKM a lo k m hAabs hm_le hk_pos hm_pos = absA from rfl]
        at h_absA_props
      simp only at h_absA_props
      obtain ⟨hsignA, h_absA_val⟩ := h_absA_props
      have h_absA_size : absA.1.1.size = k := absA.1.2
      -- IH on k for C (on the absA buffer, length k).
      have h_C_toNat : toNatLimbsList C.1.toList = (toNatLimbsList absA.1.1.toList) ^ 2 := by
        rw [hC_def]
        have h_ih := ih k hk_lt absA.1.1 0 hAabs_lim
        rw [List.drop_zero] at h_ih
        rw [List.take_of_length_le (by rw [Array.length_toList, h_absA_size])] at h_ih
        exact h_ih
      have h_C_value : toNatLimbsList C.1.toList
                      = (if A1 ≤ A0 then A0 - A1 else A1 - A0) ^ 2 := by
        rw [h_C_toNat, h_absA_val]
      -- Re-expand `^2` to a product form so `C2_le_C0_plus_C1` /
      -- `middle_equals_cross_terms` apply (they're stated for products).
      have h_C_value_mul : toNatLimbsList C.1.toList
            = (if A1 ≤ A0 then A0 - A1 else A1 - A0)
              * (if A1 ≤ A0 then A0 - A1 else A1 - A0) := by
        rw [h_C_value, sq]
      -- Subtraction safety for middleBuf: toNat C ≤ toNat D0 + toNat D2.
      -- Specialise C2_le_C0_plus_C1 to B := A (the squaring case): same sign,
      -- same |·|, so `|A0-A1|² ≤ A0² + A1²`.
      have h_sub_ok : (true : Bool) = true →
          toNatLimbsList C.1.toList
            ≤ toNatLimbsList D0.1.toList + toNatLimbsList D2.1.toList := by
        intro _
        rw [h_C_value_mul, h_D0_toNat, h_D2_toNat, sq, sq]
        have h := C2_le_C0_plus_C1 A0 A1 A0 A1 absA.2 absA.2 hsignA hsignA
          _ _ rfl rfl (by simp)
        exact h
      have h_middle_toNat := karatsubaMulLimbsRec.middleBuf_toNat k m D0.1 D2.1 C.1 true
        D0.2 D2.2 C.2 hk_pos hm_pos hm_le h_sub_ok
      rw [show karatsubaMulLimbsRec.middleBuf k m D0.1 D2.1 C.1 true
                 D0.2 D2.2 C.2 hk_pos hm_pos hm_le = middle from rfl] at h_middle_toNat
      -- middle = D0 + D2 - C = 2 A0 A1.
      have h_middle_value : toNatLimbsList middle.1.toList = 2 * A0 * A1 := by
        rw [h_middle_toNat, h_D0_toNat, h_D2_toNat, h_C_value_mul, sq, sq]
        simp only [ite_true]
        have h_cross := middle_equals_cross_terms A0 A1 A0 A1 absA.2 absA.2 hsignA hsignA
          _ rfl _ rfl
        have h_same : (absA.2 == absA.2) = true := by simp
        rw [h_same] at h_cross
        simp only [ite_true] at h_cross
        -- h_cross : A0 * A0 + A1 * A1 − (…)·(…) = A0 * A1 + A1 * A0
        -- Goal:    A0 * A0 + A1 * A1 − (…)·(…) = 2 * A0 * A1
        have h_eq : A0 * A1 + A1 * A0 = 2 * A0 * A1 := by ring
        linarith [h_cross, h_eq]
      -- Bounds for assemble_toNat.
      have h_mid_bound : toNatLimbsList middle.1.toList < 2 ^ (64 * (2 * len - k)) := by
        rw [h_middle_value, show 2 * len - k = k + m + m from by omega]
        have h := mid_value_lt A0 A1 A0 A1 k m hA0_lt hA1_lt hA0_lt hA1_lt hm_pos
        -- mid_value_lt: A0*A1 + A1*A0 < 2^(64*(k+m+m)).  Same as 2*A0*A1.
        linarith
      have h_2k_eq : 2 ^ (64 * (2 * k)) = 2 ^ (64 * k) * 2 ^ (64 * k) := pow_double_factor k
      have h_total_bound :
          toNatLimbsList D0.1.toList
          + toNatLimbsList middle.1.toList * 2 ^ (64 * k)
          + toNatLimbsList D2.1.toList * 2 ^ (64 * (2 * k))
          < 2 ^ (64 * (2 * len)) := by
        rw [h_D0_toNat, h_middle_value, h_D2_toNat]
        have h_factor : A0 ^ 2 + 2 * A0 * A1 * 2 ^ (64 * k)
                          + A1 ^ 2 * 2 ^ (64 * (2 * k))
                       = (A0 + A1 * 2 ^ (64 * k)) * (A0 + A1 * 2 ^ (64 * k)) := by
          rw [h_2k_eq]; ring
        rw [h_factor]
        exact total_lt A0 A1 A0 A1 k m len hA0_lt hA1_lt hA0_lt hA1_lt hkm
      have h_assemble := karatsubaMulLimbsRec.assemble_toNat k m len D0.1 D2.1 middle.1
        D0.2 D2.2 middle.2 hkm hk_pos hm_pos hm_le h_mid_bound h_total_bound
      -- Combine.
      rw [h_assemble, h_D0_toNat, h_middle_value, h_D2_toNat]
      -- Final algebra: A² = A0² + 2·A0·A1·β^k + A1²·β^(2k).
      have h_slice_a : toNatLimbsList ((a.toList.drop lo).take len)
                         = A0 + A1 * 2 ^ (64 * k) := by
        rw [show len = k + m from hkm.symm]
        exact toNat_slice_split a lo k m (by omega)
      rw [h_slice_a, h_2k_eq, sq]
      ring

/-- Correctness of `karatsubaSquareLimbs`: agrees with squaring of the
    corresponding limb-slice integer. -/
theorem karatsubaSquareLimbs_toNat (threshold : Nat) (a : Array UInt64)
    (lo len : Nat) (hA : lo + len ≤ a.size) :
    toNatLimbsList (karatsubaSquareLimbs threshold a lo len hA).toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 :=
  karatsubaSquareLimbsRec_toNat threshold len a lo hA

/-- Correctness of `squareKaratsuba` (AzNat-level). -/
theorem toNat_squareKaratsuba (threshold : Nat) (a : AzNat) :
    (squareKaratsuba threshold a).toNat = a.toNat ^ 2 := by
  show (ofLimbs (karatsubaSquareLimbs threshold a.limbs 0 a.limbs.size _)).toNat = _
  rw [toNat_ofLimbs, karatsubaSquareLimbs_toNat]
  show (toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)) ^ 2 = a.toNat ^ 2
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList])]
  rfl

end Azurite.AzNat
