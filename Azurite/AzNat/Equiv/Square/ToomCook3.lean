/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.Square.Karatsuba
import Azurite.AzNat.Square.ToomCook3

/-!
# Toom-Cook 3-way squaring correctness

`toomCook3SquareLimbsRec_toNat` mirrors `toomCook3MulLimbsRec_toNat` in
`Equiv/Mul/ToomCook3.lean`, with `B := A`: all slice values
`(A_i, B_i)` collapse to `(A_i, A_i)`, the sign bit of `v_{-1}` is
constantly `true` (since `v_{-1} = (A_0 - A_1 + A_2)^2 ≥ 0`), and the
inner `toomCook3_nat_identity` produces `(A_0 + A_1 K + A_2 K^2)^2`.
The proof reuses `toomCook3Interpolate_toNat` from the mul side
unchanged.
-/

namespace Azurite.AzNat

set_option maxHeartbeats 1600000 in
/-- Correctness of `toomCook3SquareLimbsRec`.  Strong induction on `len`;
    base case delegates to Karatsuba squaring; recursive case applies the
    IH to each of the five sub-squarings and assembles via
    `toomCook3Interpolate_toNat` + `toomCook3_nat_identity` with `B := A`. -/
theorem toomCook3SquareLimbsRec_toNat (toomThreshold karaThreshold : Nat) :
    ∀ (len : Nat) (a : Array UInt64) (loA : Nat) (hA : loA + len ≤ a.size),
    toNatLimbsList
        (toomCook3SquareLimbsRec toomThreshold karaThreshold a loA len hA).val.toList
      = (toNatLimbsList ((a.toList.drop loA).take len)) ^ 2 := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intros a loA hA
    unfold toomCook3SquareLimbsRec
    by_cases h_base : len < toomThreshold ∨ len < 3
    · simp only [h_base, ↓reduceDIte]
      exact karatsubaSquareLimbs_toNat karaThreshold a loA len hA
    · simp only [h_base, ↓reduceDIte]
      have hlen : 3 ≤ len := by omega
      let k := (len + 2) / 3
      let m := len - 2 * k
      have hk_pos : 0 < k := by show 0 < (len + 2) / 3; omega
      have hk_lt : k < len := by show (len + 2) / 3 < len; omega
      have hk1_lt : k + 1 < len := by show (len + 2) / 3 + 1 < len; omega
      have hm_le_k : m ≤ k := by show len - 2 * ((len + 2) / 3) ≤ (len + 2) / 3; omega
      have hm_lt : m < len := by show len - 2 * ((len + 2) / 3) < len; omega
      have hA0 : loA + k ≤ a.size := by omega
      have hA2 : (loA + 2 * k) + m ≤ a.size := by omega
      let s0 := sum012 a loA k m
      let s2 := sum124 a loA k m
      let da := diffM1 a loA k m
      have hs0_sz : 0 + (k + 1) ≤ s0.size := by
        show 0 + (k + 1) ≤ (sum012 a loA k m).size
        unfold sum012; rw [truncatePad_size]; omega
      have hs2_sz : 0 + (k + 1) ≤ s2.size := by
        show 0 + (k + 1) ≤ (sum124 a loA k m).size
        unfold sum124; rw [truncatePad_size]; omega
      have hda_sz : 0 + (k + 1) ≤ da.1.size := diffM1_size_ge _ _ _ _
      -- IH applications for the five recursive squarings.
      have h_v0_eq := ih k hk_lt a loA hA0
      have h_v1_eq := ih (k + 1) hk1_lt s0 0 hs0_sz
      have h_v2_eq := ih (k + 1) hk1_lt s2 0 hs2_sz
      have h_vm1_eq := ih (k + 1) hk1_lt da.1 0 hda_sz
      have h_vinf_eq := ih m hm_lt a (loA + 2 * k) hA2
      have h_s0_eq := sum012_toNat a loA k m hm_le_k
      have h_s2_eq := sum124_toNat a loA k m hm_le_k
      have h_da_eq := diffM1_toNat a loA k m hm_le_k
      let A0 := sliceToNat a loA k
      let A1 := sliceToNat a (loA + k) k
      let A2 := sliceToNat a (loA + 2 * k) m
      let v0  := toomCook3SquareLimbsRec toomThreshold karaThreshold a loA k hA0
      let v1  := toomCook3SquareLimbsRec toomThreshold karaThreshold s0 0 (k + 1) hs0_sz
      let v2  := toomCook3SquareLimbsRec toomThreshold karaThreshold s2 0 (k + 1) hs2_sz
      let vm1 := toomCook3SquareLimbsRec toomThreshold karaThreshold da.1 0 (k + 1) hda_sz
      let vinf := toomCook3SquareLimbsRec toomThreshold karaThreshold a
                    (loA + 2 * k) m hA2
      have hv0_sz : v0.1.size = 2 * k := v0.2
      have hv1_sz : v1.1.size = 2 * (k + 1) := v1.2
      have hv2_sz : v2.1.size = 2 * (k + 1) := v2.2
      have hvm1_sz : vm1.1.size = 2 * (k + 1) := vm1.2
      have hvinf_sz : vinf.1.size = 2 * m := vinf.2
      -- AzNat-level toNats of the recursive squarings.
      have h_v0_n : (ofLimbs v0.1).toNat = A0 * A0 := by
        rw [toNat_ofLimbs, h_v0_eq, sq]; rfl
      have h_vinf_n : (ofLimbs vinf.1).toNat = A2 * A2 := by
        rw [toNat_ofLimbs, h_vinf_eq, sq]; rfl
      have h_s0_size : s0.size = k + 1 := by
        show (sum012 a loA k m).size = k + 1
        unfold sum012; exact truncatePad_size _ _
      have h_s2_size : s2.size = k + 1 := by
        show (sum124 a loA k m).size = k + 1
        unfold sum124; exact truncatePad_size _ _
      have h_da_size : da.1.size = k + 1 := diffM1_size _ _ _ _
      have h_v1_n : (ofLimbs v1.1).toNat = (A0 + A1 + A2) * (A0 + A1 + A2) := by
        rw [toNat_ofLimbs, h_v1_eq, sq]
        rw [List.drop_zero]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_s0_size])]
        rw [h_s0_eq]
      have h_v2_n : (ofLimbs v2.1).toNat
                      = (A0 + 2 * A1 + 4 * A2) * (A0 + 2 * A1 + 4 * A2) := by
        rw [toNat_ofLimbs, h_v2_eq, sq]
        rw [List.drop_zero]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_s2_size])]
        rw [h_s2_eq]
      have h_vm1_n : (ofLimbs vm1.1).toNat
                      = (if A0 + A2 ≥ A1 then A0 + A2 - A1 else A1 - (A0 + A2))
                        * (if A0 + A2 ≥ A1 then A0 + A2 - A1 else A1 - (A0 + A2)) := by
        rw [toNat_ofLimbs, h_vm1_eq, sq]
        rw [List.drop_zero]
        rw [List.take_of_length_le (by rw [Array.length_toList, h_da_size])]
        rw [h_da_eq.1]
      -- Apply the interpolation helper, then the polynomial identity at B := A.
      have h_interp := toomCook3Interpolate_toNat (ofLimbs v0.1) (ofLimbs v1.1)
        (ofLimbs v2.1) (ofLimbs vm1.1) (ofLimbs vinf.1) true k
      simp only [h_v0_n, h_v1_n, h_v2_n, h_vm1_n, h_vinf_n] at h_interp
      -- Toom-Cook 3 Nat-level identity at B := A, with sgnA = sgnB = da.2
      -- (so `vm1_sign = sgnA == sgnB = true`, matching what we pass above).
      have h_identity := toomCook3_nat_identity A0 A1 A2 A0 A1 A2 (2 ^ (64 * k))
        da.2 da.2 h_da_eq.2 h_da_eq.2
      have h_vm1_sign_true : (da.2 == da.2) = true := beq_self_eq_true _
      simp only [h_vm1_sign_true] at h_identity
      have h_result_toNat :
          (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
              (ofLimbs vm1.1) (ofLimbs vinf.1) true k).toNat
            = (A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2)
              * (A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2) := by
        rw [h_interp]; exact h_identity
      -- Slice decomposition: a = A0 + A1·K + A2·K² with K = 2^(64·k).
      have hk_K_sq : (2 ^ (64 * k)) ^ 2 = 2 ^ (64 * (2 * k)) := by
        rw [← pow_mul]; ring_nf
      have h_a_decomp : toNatLimbsList ((a.toList.drop loA).take len)
                       = A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2 := by
        rw [hk_K_sq, show len = k + k + m from by omega]
        exact slice_decomp_3 a loA k m (by omega)
      have h_a_lt : toNatLimbsList ((a.toList.drop loA).take len) < 2 ^ (64 * len) :=
        slice_lt_pow a loA len
      have h_prod_bound : (A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2)
                          * (A0 + A1 * 2 ^ (64 * k) + A2 * (2 ^ (64 * k)) ^ 2)
                          < 2 ^ (64 * (2 * len)) := by
        rw [← h_a_decomp,
            show 64 * (2 * len) = 64 * len + 64 * len from by ring, pow_add]
        exact Nat.mul_lt_mul'' h_a_lt h_a_lt
      -- Convert the goal to truncatePad form and apply the bound.
      show toNatLimbsList (truncatePad
          (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
            (ofLimbs vm1.1) (ofLimbs vinf.1) true k).limbs
          (2 * len)).toList = _
      have h_bound : toNatLimbsList
            (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
              (ofLimbs vm1.1) (ofLimbs vinf.1) true k).limbs.toList
            < 2 ^ (64 * (2 * len)) := by
        show (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
              (ofLimbs vm1.1) (ofLimbs vinf.1) true k).toNat < _
        rw [h_result_toNat]; exact h_prod_bound
      rw [truncatePad_toNat _ _ h_bound]
      show (toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
            (ofLimbs vm1.1) (ofLimbs vinf.1) true k).toNat = _
      rw [h_result_toNat, ← h_a_decomp, sq]

/-- Correctness of `toomCook3SquareLimbs` (un-Subtyped). -/
theorem toomCook3SquareLimbs_toNat (toomThreshold karaThreshold : Nat) (a : Array UInt64)
    (loA len : Nat) (hA : loA + len ≤ a.size) :
    toNatLimbsList (toomCook3SquareLimbs toomThreshold karaThreshold a loA len hA).toList
      = (toNatLimbsList ((a.toList.drop loA).take len)) ^ 2 :=
  toomCook3SquareLimbsRec_toNat toomThreshold karaThreshold len a loA hA

/-- Correctness of `squareToomCook3` (AzNat-level). -/
theorem toNat_squareToomCook3 (toomThreshold karaThreshold : Nat) (a : AzNat) :
    (squareToomCook3 toomThreshold karaThreshold a).toNat = a.toNat ^ 2 := by
  show (ofLimbs (toomCook3SquareLimbs toomThreshold karaThreshold
                  a.limbs 0 a.limbs.size _)).toNat = _
  rw [toNat_ofLimbs, toomCook3SquareLimbs_toNat]
  show (toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)) ^ 2 = a.toNat ^ 2
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList])]
  rfl

-- ── 3-way square dispatcher correctness ─────────────────────────────────────

/-- Correctness of `squareLimbs`: agrees with squaring on the slice,
    regardless of which branch (schoolbook / Karatsuba / Toom-Cook 3)
    fires. -/
theorem squareLimbs_toNat (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    toNatLimbsList (squareLimbs a lo len hA).toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 := by
  unfold squareLimbs squareLimbsParam
  by_cases h_toom : squareDispatchToomCook3Cutoff ≤ len
  · rw [ite_eq_left h_toom]
    exact toomCook3SquareLimbs_toNat squareDispatchToomCook3Cutoff
            squareDispatchThreshold a lo len hA
  · rw [ite_eq_right h_toom]
    by_cases h_kara : squareDispatchThreshold ≤ len
    · rw [ite_eq_left h_kara]
      exact karatsubaSquareLimbs_toNat squareDispatchThreshold a lo len hA
    · rw [ite_eq_right h_kara]
      exact schoolbookSquareLimbs_toNat a lo len hA

/-- Correctness of `square` (the dispatched AzNat squaring). -/
theorem toNat_square (a : AzNat) : (square a).toNat = a.toNat ^ 2 := by
  show (ofLimbs (squareLimbs a.limbs 0 a.limbs.size _)).toNat = _
  rw [toNat_ofLimbs, squareLimbs_toNat]
  show (toNatLimbsList ((a.limbs.toList.drop 0).take a.limbs.size)) ^ 2 = a.toNat ^ 2
  rw [List.drop_zero, List.take_of_length_le (by rw [Array.length_toList])]
  rfl

end Azurite.AzNat
