/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Div.DivModLimb
import Azurite.AzNat.Equiv.Div.DivModLimb2
import Azurite.AzNat.Equiv.Div.Schoolbook
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.DivRecursiveLimbs
import Azurite.UInt64.Equiv.LeadingZeros

namespace Azurite.AzNat

/-- Combine the recursiveDivModLimbsArr result with the de-normalization (`>>> k`)
    to produce the divMod correctness identity, given the normalization facts
    that UBuf represents `U * 2^k`, VBuf represents `V * 2^k`, and VBuf's top
    limb is normalized. -/
private theorem divMod_size_ge3_finish (U V : AzNat)
    (k : Nat) (_hk_le : k ≤ 63)
    (UBuf VBuf : Array UInt64)
    (h_n_ge_3 : 3 ≤ V.limbs.size)
    (h_n_le_nU : V.limbs.size ≤ U.limbs.size)
    (h_UBuf_size : UBuf.size = U.limbs.size + 1)
    (h_VBuf_size : VBuf.size = V.limbs.size)
    (h_VBuf_norm :
      2 ^ 63 ≤ (VBuf[0 + V.limbs.size - 1]'(by rw [h_VBuf_size]; omega)).toNat)
    (h_UBuf_toNat : toNatLimbsList UBuf.toList = U.toNat * 2 ^ k)
    (h_VBuf_toNat : toNatLimbsList VBuf.toList = V.toNat * 2 ^ k)
    (_hV_pos : 0 < V.toNat) :
    let res := recursiveDivModLimbsArr 32 UBuf VBuf 0 0 V.limbs.size
                  (U.limbs.size + 1 - V.limbs.size)
                  (by omega) (by rw [h_UBuf_size]; omega)
                  (by rw [h_VBuf_size]; omega) h_VBuf_norm
    (ofLimbs (res.1.extract V.limbs.size
                (V.limbs.size + (U.limbs.size + 1 - V.limbs.size))
              ++ #[res.2])).toNat * V.toNat
        + (ofLimbs (res.1.extract 0 V.limbs.size) >>> k).toNat = U.toNat
    ∧ (V.toNat ≠ 0 →
        (ofLimbs (res.1.extract 0 V.limbs.size) >>> k).toNat < V.toNat) := by
  -- Abbreviate the key sizes.
  set n  := V.limbs.size with hn_def
  set nU := U.limbs.size with hnU_def
  set m  := nU + 1 - n with hm_def
  have h_n_pos : 0 < n := by omega
  have h_nU_ge_n : n ≤ nU := h_n_le_nU
  -- Proof-obligation bounds for recursiveDivModLimbsArr.
  have h_loA : 0 + n + m ≤ UBuf.size := by
    rw [h_UBuf_size]; omega
  have h_loB : 0 + n ≤ VBuf.size := by rw [h_VBuf_size]; omega
  -- Introduce the result.
  set res := recursiveDivModLimbsArr 32 UBuf VBuf 0 0 n m
               h_n_pos h_loA h_loB h_VBuf_norm with hres_def
  -- Apply the spec to get rem_lt and div_eq.
  have h_spec : RecursiveDivModLimbsSpec UBuf VBuf 0 0 n m res.1 res.2 :=
    recursiveDivModLimbsAux_spec 32 UBuf VBuf 0 0 n m
      h_n_pos h_loA h_loB h_VBuf_norm
  obtain ⟨h_rem_lt, h_div_eq⟩ := h_spec
  -- Simplify sliceVal at loA = 0, loB = 0.
  simp only [Nat.zero_add] at h_rem_lt h_div_eq
  -- Size of res.1.
  have h_res_size : res.1.size = UBuf.size :=
    recursiveDivModLimbsArr_size 32 UBuf VBuf 0 0 n m
      h_n_pos h_loA h_loB h_VBuf_norm
  have h_res_len : res.1.toList.length = nU + 1 := by
    rw [Array.length_toList, h_res_size, h_UBuf_size]
  -- Key slice values.
  set R  : Nat := sliceVal res.1 0 n with hR_def
  set Q' : Nat := sliceVal res.1 n m  with hQ'_def
  -- `sliceVal UBuf 0 (n + m) = U.toNat * 2^k`.
  have h_UBuf_sv : sliceVal UBuf 0 (n + m) = U.toNat * 2 ^ k := by
    unfold sliceVal
    rw [List.drop_zero]
    have h_nm : n + m = nU + 1 := by omega
    have h_len : UBuf.toList.length = nU + 1 := by
      rw [Array.length_toList, h_UBuf_size]
    rw [List.take_of_length_le (by rw [h_len, h_nm])]
    exact h_UBuf_toNat
  -- `sliceVal VBuf 0 n = V.toNat * 2^k`.
  have h_VBuf_sv : sliceVal VBuf 0 n = V.toNat * 2 ^ k := by
    unfold sliceVal
    rw [List.drop_zero]
    have h_len : VBuf.toList.length = n := by
      rw [Array.length_toList, h_VBuf_size]
    rw [List.take_of_length_le (le_of_eq h_len)]
    exact h_VBuf_toNat
  -- Rewrite the spec hypotheses in terms of U, V, k.
  rw [h_UBuf_sv, h_VBuf_sv] at h_div_eq
  rw [h_VBuf_sv] at h_rem_lt
  -- Set Q_val = the full quotient.
  set Q_val : Nat := res.2.toNat * 2 ^ (64 * m) + Q' with hQ_val_def
  -- Express ofLimbs (res.1.extract 0 n) = R.
  have h_extract_R : (ofLimbs (res.1.extract 0 n)).toNat = R := by
    rw [toNat_ofLimbs, Array.toList_extract, List.extract_eq_take_drop]
    show toNatLimbsList ((res.1.toList.drop 0).take (n - 0)) = _
    rw [List.drop_zero, Nat.sub_zero, hR_def]
    rfl
  -- Express ofLimbs (res.1.extract n (n+m) ++ #[res.2]) = Q_val.
  have h_extract_Q' :
      (res.1.extract n (n + m)).toList = (res.1.toList.drop n).take m := by
    rw [Array.toList_extract, List.extract_eq_take_drop]
    show (res.1.toList.drop n).take (n + m - n) = _
    rw [Nat.add_sub_cancel_left]
  have h_extract_Q :
      (ofLimbs (res.1.extract n (n + m) ++ #[res.2])).toNat = Q_val := by
    rw [toNat_ofLimbs, Array.toList_append, h_extract_Q']
    show toNatLimbsList ((res.1.toList.drop n).take m ++ [res.2]) = _
    rw [toNatLimbsList_append]
    have h_take_len : ((res.1.toList.drop n).take m).length = m := by
      rw [List.length_take, List.length_drop, h_res_len]; omega
    rw [h_take_len]
    show toNatLimbsList [res.2] * 2 ^ (64 * m) + Q' = _
    have h_sing : toNatLimbsList [res.2] = res.2.toNat := by simp [toNatLimbsList]
    rw [h_sing, hQ'_def]
  -- (>>> k) on the remainder.
  have h_2k_pos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  -- Q_val * V ≤ U.
  have h_QV_le : Q_val * V.toNat ≤ U.toNat := by
    have h_le_2k : Q_val * V.toNat * 2 ^ k ≤ U.toNat * 2 ^ k := by
      have h_assoc : Q_val * V.toNat * 2 ^ k = Q_val * (V.toNat * 2 ^ k) := by ring
      rw [h_assoc]; linarith [h_div_eq]
    exact Nat.le_of_mul_le_mul_right h_le_2k h_2k_pos
  -- R = (U - Q_val * V) * 2^k.
  have h_R_eq : R = (U.toNat - Q_val * V.toNat) * 2 ^ k := by
    have h_assoc : Q_val * (V.toNat * 2 ^ k) = Q_val * V.toNat * 2 ^ k := by ring
    rw [h_assoc] at h_div_eq
    have h_sub : (U.toNat - Q_val * V.toNat) * 2 ^ k
                = U.toNat * 2 ^ k - Q_val * V.toNat * 2 ^ k :=
      Nat.sub_mul _ _ _
    omega
  -- (ofLimbs (res.1.extract 0 n) >>> k).toNat = R / 2^k.
  have h_shr : (ofLimbs (res.1.extract 0 n) >>> k).toNat
              = (ofLimbs (res.1.extract 0 n)).toNat / 2 ^ k := by
    rw [hShiftRight_eq, toNat_shiftRight]
  -- Rewrite the goal using our expressions.
  -- The conclusion uses V.limbs.size in extract bounds; unfold n.
  show (ofLimbs (res.1.extract n (n + m) ++ #[res.2])).toNat * V.toNat
        + (ofLimbs (res.1.extract 0 n) >>> k).toNat = U.toNat
      ∧ (V.toNat ≠ 0 → (ofLimbs (res.1.extract 0 n) >>> k).toNat < V.toNat)
  rw [h_extract_Q, h_shr, h_extract_R, h_R_eq, Nat.mul_div_cancel _ h_2k_pos]
  refine ⟨?_, ?_⟩
  · -- Q_val * V + (U - Q_val * V) = U.
    omega
  · -- (U - Q_val * V) < V.
    intro _
    have h_lt' : (U.toNat - Q_val * V.toNat) * 2 ^ k < V.toNat * 2 ^ k := by
      rw [← h_R_eq]; exact h_rem_lt
    exact Nat.lt_of_mul_lt_mul_right h_lt'

set_option maxHeartbeats 800000 in
/-- **Top-level correctness of `divMod`**: `divMod U V` returns `(Q, R)` such
    that `Q * V + R = U`, with `R < V` whenever `V > 0`. By convention,
    `divMod U 0 = (0, U)`, so the value identity holds (with vacuous bound). -/
theorem divMod_toNat (U V : AzNat) :
    (divMod U V).1.toNat * V.toNat + (divMod U V).2.toNat = U.toNat
    ∧ (V.toNat ≠ 0 → (divMod U V).2.toNat < V.toNat) := by
  unfold divMod
  -- Case 1: V.limbs.size = 0 (i.e., V = 0).
  by_cases h0V : V.limbs.size = 0
  · simp only [h0V, ↓reduceDIte]
    have h_V_zero : V.toNat = 0 := (toNat_eq_zero_iff V).mpr h0V
    refine ⟨?_, ?_⟩
    · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
      rw [h_V_zero]; show 0 * 0 + U.toNat = U.toNat; ring
    · intro h_ne; exact absurd h_V_zero h_ne
  · simp only [h0V, ↓reduceDIte]
    have hV_pos : 0 < V.limbs.size := Nat.pos_of_ne_zero h0V
    have hV_toNat_pos : 0 < V.toNat := by
      have := toNat_pos_of_size_pos V hV_pos
      have h_pow_pos : 0 < (2 : Nat) ^ (64 * (V.limbs.size - 1)) := Nat.two_pow_pos _
      omega
    -- Case 2: V.limbs.size = 1.
    by_cases h1V : V.limbs.size = 1
    · simp only [h1V, ↓reduceDIte]
      have hV0 : 0 < V.limbs.size := by omega
      set v := V.limbs[0]'hV0 with hv_def
      have hv_ne : v ≠ 0 := by
        intro hv0
        apply V.last_ne_zero
        rw [Array.back?_eq_getElem?]
        rw [show V.limbs.size - 1 = 0 from by omega]
        rw [Array.getElem?_eq_getElem hV0]
        exact congrArg some hv0
      have h_V_eq_v : V.toNat = v.toNat := by
        rw [hv_def]; exact toNat_of_size_one V h1V
      set qr := divModUInt64 U v hv_ne with hqr_def
      have h_div := toNat_divModUInt64 U v hv_ne
      simp only at h_div
      obtain ⟨h_eq, h_lt⟩ := h_div
      refine ⟨?_, ?_⟩
      · show qr.1.toNat * V.toNat + (ofLimbs #[qr.2]).toNat = U.toNat
        rw [toNat_ofLimbs_singleton, h_V_eq_v]; exact h_eq
      · intro _
        show (ofLimbs #[qr.2]).toNat < V.toNat
        rw [toNat_ofLimbs_singleton, h_V_eq_v]; exact h_lt
    · simp only [h1V, ↓reduceDIte]
      -- Case 3: U.limbs.size < V.limbs.size.
      by_cases hUV : U.limbs.size < V.limbs.size
      · simp only [hUV, ↓reduceDIte]
        refine ⟨?_, ?_⟩
        · show (0 : AzNat).toNat * V.toNat + U.toNat = U.toNat
          show 0 * V.toNat + U.toNat = U.toNat; ring
        · intro _; exact toNat_lt_of_size_lt U V hUV
      · simp only [hUV, ↓reduceDIte]
        by_cases hUV_num : U < V
        · simp only [hUV_num, ↓reduceIte]
          exact ⟨by simp, fun _ => (lt_iff_toNat_lt U V).mp hUV_num⟩
        · simp only [hUV_num, ↓reduceIte]
          -- Cases 4 and 5: V.limbs.size ≥ 2 and U.limbs.size ≥ V.limbs.size.
          have h_n_ge_2 : 2 ≤ V.limbs.size := by omega
          have h_nU_ge_n : V.limbs.size ≤ U.limbs.size := Nat.le_of_not_lt hUV
          by_cases h2V : V.limbs.size = 2
          · -- Case 4: V.limbs.size = 2. Dispatches to divModLimb2.
            simp only [h2V, ↓reduceDIte,
                       show (2 - 1 : Nat) = 1 from rfl,
                       show (2 - 2 : Nat) = 0 from rfl]
            have h_topB_idx : (1 : Nat) < V.limbs.size := by omega
            have h_v0_idx : (0 : Nat) < V.limbs.size := by omega
            set topB : UInt64 := V.limbs[1]'h_topB_idx with htopB_def
            set v0 : UInt64 := V.limbs[0]'h_v0_idx with hv0_def
            have h_topB_ne : topB ≠ 0 := by
              intro h0
              apply V.last_ne_zero
              rw [Array.back?_eq_getElem?]
              rw [show V.limbs.size - 1 = 1 from by omega]
              rw [Array.getElem?_eq_getElem h_topB_idx]
              exact congrArg some h0
            have hk_le : V.limbs[1].leadingZeros ≤ 63 :=
              UInt64.leadingZeros_le _ h_topB_ne
            have hV_eq : V.toNat = V.limbs[1].toNat * 2 ^ 64 + V.limbs[0].toNat := by
              rw [← htopB_def, ← hv0_def]; exact toNat_of_size_two V h2V
            have h_UBufRaw_size : (U.limbs ++ #[(0:UInt64)]).size = U.limbs.size + 1 := by
              rw [Array.size_append]; rfl
            split_ifs with hk0
            · -- k = 0 branch: UBuf = U.limbs ++ #[0], d_top = topB ||| 0 = topB, d0 = v0.
              have hk_zero : V.limbs[1].leadingZeros = 0 := hk0
              have h_kU_zero : (UInt64.ofNat V.limbs[1].leadingZeros : UInt64) = 0 := by
                rw [hk_zero]; rfl
              -- Simplify d_top and d0.
              have h_dtop_eq :
                  V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros ||| (0:UInt64)
                    = V.limbs[1] := by
                rw [h_kU_zero, UInt64.shiftLeft_zero, UInt64.or_zero]
              have h_d0_eq :
                  V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros = V.limbs[0] := by
                rw [h_kU_zero, UInt64.shiftLeft_zero]
              -- d_top normalization (after simplification, d_top = topB).
              have h_dtop_norm :
                  2 ^ 63 ≤ (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                              (0:UInt64)).toNat := by
                rw [h_dtop_eq]
                have h := UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros V.limbs[1] h_topB_ne
                rw [h_kU_zero, UInt64.shiftLeft_zero] at h; exact h
              -- UBuf = U.limbs ++ #[0]; toNatLimbsList = U.toNat * 2^0 = U.toNat.
              have h_UBuf_toNat :
                  toNatLimbsList ((U.limbs ++ #[(0:UInt64)]).toList)
                    = U.toNat * 2 ^ V.limbs[1].leadingZeros := by
                rw [hk_zero, Nat.pow_zero, Nat.mul_one]
                exact toNatLimbsList_UBufRaw U
              -- d_top * 2^64 + d0 = V * 2^0 = V.
              have h_dtop_d0_eq :
                  (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                    (0:UInt64)).toNat * 2 ^ 64
                    + (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                    = V.toNat * 2 ^ V.limbs[1].leadingZeros := by
                rw [h_dtop_eq, h_d0_eq, hk_zero, Nat.pow_zero, Nat.mul_one]
                exact hV_eq.symm
              -- Apply finish with concrete d_top, d0 expressions.
              exact divMod_size2_finish U V V.limbs[1].leadingZeros hk_le
                      (U.limbs ++ #[0])
                      (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros ||| 0)
                      (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros)
                      h_UBufRaw_size h_dtop_norm h_UBuf_toNat h_dtop_d0_eq hV_toNat_pos
            · -- k > 0 branch.
              have hk_pos : 1 ≤ V.limbs[1].leadingZeros := Nat.one_le_iff_ne_zero.mpr hk0
              -- (v0 >> (64-k)).toNat < 2^k (used as carry bound).
              obtain ⟨_, h_v0_carry_lt⟩ :=
                limb_shift_step V.limbs[0] 0 V.limbs[1].leadingZeros
                  hk_pos hk_le (Nat.two_pow_pos _)
              -- topB * 2^k < 2^64 (used to derive (topB >> (64-k)).toNat = 0).
              obtain ⟨_, h_topB_shl_lt⟩ :=
                topB_shl_lt V.limbs[1] V.limbs[1].leadingZeros rfl h_topB_ne
              have h_topB_lt_pow :
                  V.limbs[1].toNat < 2 ^ (64 - V.limbs[1].leadingZeros) := by
                have h_pow_pos : 0 < (2:Nat) ^ V.limbs[1].leadingZeros := Nat.two_pow_pos _
                have h_split : (2:Nat) ^ 64
                    = 2 ^ (64 - V.limbs[1].leadingZeros) * 2 ^ V.limbs[1].leadingZeros := by
                  rw [← Nat.pow_add]; congr 1; omega
                rw [h_split] at h_topB_shl_lt
                exact (Nat.mul_lt_mul_right h_pow_pos).mp h_topB_shl_lt
              have h_topB_shr_zero :
                  (V.limbs[1] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros)).toNat = 0 := by
                rw [UInt64.toNat_shiftRight]
                have h_ofNat :
                    (UInt64.ofNat (64 - V.limbs[1].leadingZeros) : UInt64).toNat
                      = 64 - V.limbs[1].leadingZeros := by
                  show (64 - V.limbs[1].leadingZeros) % 2 ^ 64 = _
                  apply Nat.mod_eq_of_lt; omega
                rw [h_ofNat]
                rw [Nat.mod_eq_of_lt (show 64 - V.limbs[1].leadingZeros < 64 from by omega)]
                rw [Nat.shiftRight_eq_div_pow]
                exact Nat.div_eq_of_lt h_topB_lt_pow
              -- d_top equation via limb_shift_step on topB.
              obtain ⟨h_dtop_or_eq, _⟩ :=
                limb_shift_step V.limbs[1]
                  (V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros))
                  V.limbs[1].leadingZeros hk_pos hk_le h_v0_carry_lt
              rw [h_topB_shr_zero, Nat.zero_mul, Nat.add_zero] at h_dtop_or_eq
              -- d0 equation via limb_shift_step on v0 with carry 0.
              obtain ⟨h_v0_shl_eq, _⟩ :=
                limb_shift_step V.limbs[0] 0 V.limbs[1].leadingZeros
                  hk_pos hk_le (Nat.two_pow_pos _)
              rw [UInt64.or_zero, UInt64.toNat_zero, Nat.add_zero] at h_v0_shl_eq
              -- Three preconditions for divMod_size2_finish.
              have h_size_eq :
                  (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (U.limbs.size + 1)
                      V.limbs[1].leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                      hk_pos hk_le).1.size = U.limbs.size + 1 := by
                rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
              have h_dtop_norm :
                  2 ^ 63 ≤ (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                              V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros)).toNat := by
                have h_shl_ge :=
                  UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros V.limbs[1] h_topB_ne
                rw [UInt64.toNat_or]
                exact Nat.le_trans h_shl_ge Nat.left_le_or
              have h_UBuf_toNat :
                  toNatLimbsList
                      (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (U.limbs.size + 1)
                        V.limbs[1].leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                        hk_pos hk_le).1.toList
                    = U.toNat * 2 ^ V.limbs[1].leadingZeros :=
                toNatLimbsList_shifted_UBufRaw U V.limbs[1].leadingZeros hk_pos hk_le
              have h_dtop_d0_eq :
                  (V.limbs[1] <<< UInt64.ofNat V.limbs[1].leadingZeros |||
                    V.limbs[0] >>> UInt64.ofNat (64 - V.limbs[1].leadingZeros)).toNat * 2 ^ 64 +
                    (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat =
                  V.toNat * 2 ^ V.limbs[1].leadingZeros := by
                rw [h_dtop_or_eq, hV_eq]
                calc (V.limbs[1].toNat * 2 ^ V.limbs[1].leadingZeros
                        + (V.limbs[0] >>> UInt64.ofNat
                            (64 - V.limbs[1].leadingZeros)).toNat) * 2 ^ 64
                      + (V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                    = V.limbs[1].toNat * 2 ^ V.limbs[1].leadingZeros * 2 ^ 64
                        + ((V.limbs[0] <<< UInt64.ofNat V.limbs[1].leadingZeros).toNat
                           + (V.limbs[0] >>> UInt64.ofNat
                              (64 - V.limbs[1].leadingZeros)).toNat * 2 ^ 64) := by ring
                  _ = V.limbs[1].toNat * 2 ^ V.limbs[1].leadingZeros * 2 ^ 64
                        + V.limbs[0].toNat * 2 ^ V.limbs[1].leadingZeros := by
                        rw [h_v0_shl_eq]
                  _ = (V.limbs[1].toNat * 2 ^ 64 + V.limbs[0].toNat)
                        * 2 ^ V.limbs[1].leadingZeros := by ring
              exact divMod_size2_finish U V V.limbs[1].leadingZeros hk_le _ _ _
                      h_size_eq h_dtop_norm h_UBuf_toNat h_dtop_d0_eq hV_toNat_pos
          · -- Case 5: V.limbs.size ≥ 3.
            simp only [h2V, ↓reduceDIte]
            set n := V.limbs.size with hn_def
            set nU := U.limbs.size with hnU_def
            have h_n_ge_3 : 3 ≤ n := by omega
            have h_top_idx : n - 1 < V.limbs.size := by omega
            have h_n2_idx : n - 2 < V.limbs.size := by omega
            set topB : UInt64 := V.limbs[n - 1]'h_top_idx with htopB_def
            have h_topB_ne : topB ≠ 0 := by
              intro h0
              apply V.last_ne_zero
              rw [Array.back?_eq_getElem?]
              rw [show V.limbs.size - 1 = n - 1 from rfl]
              rw [Array.getElem?_eq_getElem h_top_idx]
              exact congrArg some h0
            have hk_le : topB.leadingZeros ≤ 63 :=
              UInt64.leadingZeros_le _ h_topB_ne
            have h_UBufRaw_size : (U.limbs ++ #[(0 : UInt64)]).size = nU + 1 := by
              rw [Array.size_append]; rfl
            split_ifs with hk0
            · -- k = 0 branch.
              have hk_zero : topB.leadingZeros = 0 := hk0
              have h_kU_zero : (UInt64.ofNat topB.leadingZeros : UInt64) = 0 := by
                rw [hk_zero]; rfl
              -- d_top = topB <<< 0 ||| 0 = topB.
              have h_dtop_eq :
                  topB <<< UInt64.ofNat topB.leadingZeros ||| (0:UInt64)
                    = topB := by
                rw [h_kU_zero, UInt64.shiftLeft_zero, UInt64.or_zero]
              -- VBuf = V.limbs.set (n-1) topB. Since V.limbs[n-1] = topB,
              -- the set is a no-op at the value level.
              have h_set_no_op : V.limbs.set (n - 1) topB h_top_idx = V.limbs := by
                apply Array.ext
                · rw [Array.size_set]
                · intro i hi1 hi2
                  rw [Array.getElem_set]
                  split_ifs with h_eq
                  · subst h_eq; exact htopB_def
                  · rfl
              -- h_VBuf_norm: VBuf[n-1] = topB, and topB has high bit ≥ 2^63 since
              -- leadingZeros = 0.
              have h_topB_norm : 2 ^ 63 ≤ topB.toNat := by
                have h := UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
                rw [h_kU_zero, UInt64.shiftLeft_zero] at h; exact h
              -- toNatLimbsList of VBuf (after set) = V.toNat.
              have h_VBuf_toNat :
                  toNatLimbsList ((V.limbs.set (n - 1)
                      (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                      h_top_idx).toList)
                    = V.toNat * 2 ^ topB.leadingZeros := by
                rw [h_dtop_eq, h_set_no_op, hk_zero, Nat.pow_zero, Nat.mul_one]
                rfl
              have h_UBuf_toNat :
                  toNatLimbsList ((U.limbs ++ #[(0:UInt64)]).toList)
                    = U.toNat * 2 ^ topB.leadingZeros := by
                rw [hk_zero, Nat.pow_zero, Nat.mul_one]
                exact toNatLimbsList_UBufRaw U
              have h_VBuf_size_eq :
                  (V.limbs.set (n - 1)
                      (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                      h_top_idx).size = n := by
                rw [Array.size_set]
              have h_VBuf_norm :
                  2 ^ 63 ≤ ((V.limbs.set (n - 1)
                      (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                      h_top_idx)[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega)).toNat := by
                have h_idx_eq : (0 + n - 1 : Nat) = n - 1 := by omega
                have h_get_eq :
                    (V.limbs.set (n - 1)
                        (topB <<< UInt64.ofNat topB.leadingZeros ||| 0)
                        h_top_idx)[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega)
                    = topB <<< UInt64.ofNat topB.leadingZeros ||| 0 := by
                  conv_lhs => rw [Array.getElem_set]
                  rw [ite_eq_left h_idx_eq.symm]
                rw [h_get_eq, h_dtop_eq]
                exact h_topB_norm
              exact divMod_size_ge3_finish U V topB.leadingZeros hk_le
                      (U.limbs ++ #[0])
                      (V.limbs.set (n - 1)
                        (topB <<< UInt64.ofNat topB.leadingZeros ||| 0) h_top_idx)
                      h_n_ge_3 h_nU_ge_n h_UBufRaw_size h_VBuf_size_eq
                      h_VBuf_norm h_UBuf_toNat h_VBuf_toNat hV_toNat_pos
            · -- k > 0 branch.
              have hk_pos : 1 ≤ topB.leadingZeros := Nat.one_le_iff_ne_zero.mpr hk0
              -- Bound on V.limbs[n - 2] >>> (64 - k) from limb_shift_step.
              obtain ⟨_, h_carry_lt⟩ :=
                limb_shift_step (V.limbs[n - 2]'h_n2_idx) 0 topB.leadingZeros
                  hk_pos hk_le (Nat.two_pow_pos _)
              -- Bound on topB * 2^k.
              obtain ⟨_, h_topB_shl_lt⟩ :=
                topB_shl_lt topB topB.leadingZeros rfl h_topB_ne
              -- Show topB >>> (64 - k) = 0.
              have h_topB_lt_pow :
                  topB.toNat < 2 ^ (64 - topB.leadingZeros) := by
                have h_pow_pos : 0 < (2:Nat) ^ topB.leadingZeros := Nat.two_pow_pos _
                have h_split : (2:Nat) ^ 64
                    = 2 ^ (64 - topB.leadingZeros) * 2 ^ topB.leadingZeros := by
                  rw [← Nat.pow_add]; congr 1; omega
                rw [h_split] at h_topB_shl_lt
                exact (Nat.mul_lt_mul_right h_pow_pos).mp h_topB_shl_lt
              have h_topB_shr_zero :
                  (topB >>> UInt64.ofNat (64 - topB.leadingZeros)).toNat = 0 := by
                rw [UInt64.toNat_shiftRight]
                have h_ofNat : (UInt64.ofNat (64 - topB.leadingZeros) : UInt64).toNat
                    = 64 - topB.leadingZeros := by
                  show (64 - topB.leadingZeros) % 2 ^ 64 = _
                  apply Nat.mod_eq_of_lt; omega
                rw [h_ofNat,
                    Nat.mod_eq_of_lt (show 64 - topB.leadingZeros < 64 from by omega),
                    Nat.shiftRight_eq_div_pow]
                exact Nat.div_eq_of_lt h_topB_lt_pow
              -- d_top = topB <<< k ||| (V.limbs[n - 2] >>> (64 - k)).
              obtain ⟨h_dtop_or_eq, _⟩ :=
                limb_shift_step topB
                  (V.limbs[n - 2]'h_n2_idx >>> UInt64.ofNat (64 - topB.leadingZeros))
                  topB.leadingZeros hk_pos hk_le h_carry_lt
              rw [h_topB_shr_zero, Nat.zero_mul, Nat.add_zero] at h_dtop_or_eq
              -- d_top normalization.
              have h_dtop_norm :
                  2 ^ 63 ≤ (topB <<< UInt64.ofNat topB.leadingZeros |||
                    (V.limbs[n - 2]'h_n2_idx >>>
                      UInt64.ofNat (64 - topB.leadingZeros))).toNat := by
                have h_shl_ge :=
                  UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros topB h_topB_ne
                rw [UInt64.toNat_or]
                exact Nat.le_trans h_shl_ge Nat.left_le_or
              -- VBufRaw size and getElem at n-1 (preserved by shiftLimbsLeft 0 (n-1)).
              set VBufRaw : Array UInt64 :=
                (shiftLimbsLeft V.limbs 0 (n - 1) topB.leadingZeros (by omega) (by omega)
                  hk_pos hk_le).1 with hVBufRaw_def
              have h_VBufRaw_size : VBufRaw.size = n := by
                rw [hVBufRaw_def, shiftLimbsLeft_size]
              have h_VBufRaw_len : VBufRaw.toList.length = n := by
                rw [Array.length_toList, h_VBufRaw_size]
              have h_top_in_raw : n - 1 < VBufRaw.size := by rw [h_VBufRaw_size]; omega
              -- VBuf and its size.
              set d_top : UInt64 :=
                topB <<< UInt64.ofNat topB.leadingZeros |||
                  V.limbs[n - 2]'h_n2_idx >>> UInt64.ofNat (64 - topB.leadingZeros)
                with hdtop_def
              set VBuf : Array UInt64 := VBufRaw.set (n - 1) d_top h_top_in_raw
                with hVBuf_def
              have h_VBuf_size_eq : VBuf.size = n := by
                rw [hVBuf_def, Array.size_set]; exact h_VBufRaw_size
              have h_VBuf_norm :
                  2 ^ 63 ≤ (VBuf[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega)).toNat := by
                have h_idx_eq : (0 + n - 1 : Nat) = n - 1 := by omega
                have h_get_eq :
                    VBuf[0 + n - 1]'(by rw [h_VBuf_size_eq]; omega) = d_top := by
                  show (VBufRaw.set (n - 1) d_top h_top_in_raw)[0 + n - 1] = d_top
                  rw [Array.getElem_set]
                  rw [ite_eq_left h_idx_eq.symm]
                rw [h_get_eq]; exact h_dtop_norm
              -- UBuf representation.
              have h_UBuf_size_dyn :
                  (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (nU + 1) topB.leadingZeros
                     (Nat.zero_le _) (by rw [h_UBufRaw_size]) hk_pos hk_le).1.size
                    = nU + 1 := by
                rw [shiftLimbsLeft_size]; exact h_UBufRaw_size
              have h_UBuf_toNat :
                  toNatLimbsList
                      (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (nU + 1)
                        topB.leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                        hk_pos hk_le).1.toList
                    = U.toNat * 2 ^ topB.leadingZeros :=
                toNatLimbsList_shifted_UBufRaw U topB.leadingZeros hk_pos hk_le
              -- VBuf representation: toNatLimbsList VBuf.toList = V.toNat * 2^k.
              have h_VBuf_toNat :
                  toNatLimbsList VBuf.toList = V.toNat * 2 ^ topB.leadingZeros := by
                -- Step 1: VBuf.toList = VBufRaw.toList.take (n-1) ++ [d_top].
                have h_n_minus_1_lt : n - 1 < VBufRaw.toList.length := by
                  rw [h_VBufRaw_len]; omega
                have h_drop_eq :
                    VBufRaw.toList.drop (n - 1)
                      = [VBufRaw.toList[n - 1]'h_n_minus_1_lt] := by
                  rw [List.drop_eq_getElem_cons h_n_minus_1_lt]
                  congr 1
                  exact List.drop_of_length_le (by rw [h_VBufRaw_len]; omega)
                have h_VBufRaw_split :
                    VBufRaw.toList
                      = VBufRaw.toList.take (n - 1)
                        ++ [VBufRaw.toList[n - 1]'h_n_minus_1_lt] := by
                  conv_lhs =>
                    rw [← List.take_append_drop (n - 1) VBufRaw.toList, h_drop_eq]
                have h_VBuf_toList :
                    VBuf.toList = VBufRaw.toList.take (n - 1) ++ [d_top] := by
                  rw [hVBuf_def, Array.toList_set]
                  conv_lhs => rw [h_VBufRaw_split]
                  rw [List.set_append_right _ _
                        (by rw [List.length_take, h_VBufRaw_len]; omega)]
                  congr 1
                  rw [show (n - 1) - (VBufRaw.toList.take (n - 1)).length = 0
                        from by rw [List.length_take, h_VBufRaw_len]; omega]
                  rfl
                -- Step 2: toNatLimbsList of VBuf.toList.
                rw [h_VBuf_toList, toNatLimbsList_append]
                have h_take_len :
                    (VBufRaw.toList.take (n - 1)).length = n - 1 := by
                  rw [List.length_take]; omega
                rw [h_take_len]
                have h_dtop_singleton : toNatLimbsList [d_top] = d_top.toNat := by
                  simp [toNatLimbsList]
                rw [h_dtop_singleton]
                -- Step 3: V.toNat splits as topB * 2^(64*(n-1)) + bottom.
                have hV_split :
                    V.toNat
                      = topB.toNat * 2 ^ (64 * (n - 1))
                        + toNatLimbsList (V.limbs.toList.take (n - 1)) := by
                  show toNatLimbsList V.limbs.toList = _
                  have h_V_len : V.limbs.toList.length = n := rfl
                  have h_n_lt_V : n - 1 < V.limbs.toList.length := by
                    rw [h_V_len]; omega
                  have h_V_drop_eq :
                      V.limbs.toList.drop (n - 1)
                        = [V.limbs.toList[n - 1]'h_n_lt_V] := by
                    rw [List.drop_eq_getElem_cons h_n_lt_V]
                    congr 1
                    exact List.drop_of_length_le (by rw [h_V_len]; omega)
                  conv_lhs =>
                    rw [← List.take_append_drop (n - 1) V.limbs.toList, h_V_drop_eq]
                  rw [toNatLimbsList_append]
                  have h_take_len_V :
                      (V.limbs.toList.take (n - 1)).length = n - 1 := by
                    rw [List.length_take]; omega
                  rw [h_take_len_V]
                  have h_singleton :
                      toNatLimbsList [V.limbs.toList[n - 1]'h_n_lt_V] = topB.toNat := by
                    rw [show V.limbs.toList[n - 1]'h_n_lt_V
                            = V.limbs[n - 1]'h_top_idx
                        from (Array.getElem_toList _).symm,
                        ← htopB_def]
                    simp [toNatLimbsList]
                  rw [h_singleton]
                -- Step 4: shiftLimbsLeft_toNat for the bottom n-1 limbs.
                have h_inv :=
                  shiftLimbsLeft_toNat V.limbs 0 (n - 1) topB.leadingZeros
                    (by omega) (by omega) hk_pos hk_le
                simp only [List.drop_zero, Nat.sub_zero] at h_inv
                rw [← hVBufRaw_def] at h_inv
                -- carry from shiftLimbsLeft = V.limbs[n - 2] >>> (64 - k).
                have h_carry_eq :
                    (shiftLimbsLeft V.limbs 0 (n - 1) topB.leadingZeros (by omega)
                      (by omega) hk_pos hk_le).2
                      = V.limbs[(n - 1) - 1]'(by omega)
                          >>> UInt64.ofNat (64 - topB.leadingZeros) := by
                  apply shiftLimbsLeft_carry_eq; omega
                rw [h_carry_eq] at h_inv
                have h_n2_idx_eq :
                    V.limbs[(n - 1) - 1]'(by omega) = V.limbs[n - 2]'h_n2_idx := by
                  congr 1
                rw [h_n2_idx_eq] at h_inv
                -- Now combine. d_top.toNat = topB * 2^k + carry.toNat.
                rw [show d_top = topB <<< UInt64.ofNat topB.leadingZeros
                            ||| (V.limbs[n - 2]'h_n2_idx
                              >>> UInt64.ofNat (64 - topB.leadingZeros)) from rfl,
                    h_dtop_or_eq]
                rw [hV_split]
                -- Set abbreviations to make omega/ring tractable.
                set k := topB.leadingZeros with hk_def
                set V_take := toNatLimbsList (V.limbs.toList.take (n - 1)) with hVtake_def
                set bot := toNatLimbsList (VBufRaw.toList.take (n - 1)) with hbot_def
                set ctop : Nat :=
                  (V.limbs[n - 2]'h_n2_idx >>> UInt64.ofNat (64 - k)).toNat
                  with hctop_def
                -- h_inv : bot + ctop * 2^(64*(n-1)) = V_take * 2^k.
                -- Goal: (topB.toNat * 2^k + ctop) * 2^(64*(n-1)) + bot
                --        = (topB.toNat * 2^(64*(n-1)) + V_take) * 2^k.
                have h_le : ctop * 2 ^ (64 * (n - 1)) ≤ V_take * 2 ^ k := by omega
                have h_bot_eq :
                    bot
                      = V_take * 2 ^ k - ctop * 2 ^ (64 * (n - 1)) := by omega
                rw [h_bot_eq]
                have h_add_sub :
                    (topB.toNat * 2 ^ k + ctop) * 2 ^ (64 * (n - 1))
                        + (V_take * 2 ^ k - ctop * 2 ^ (64 * (n - 1)))
                      = topB.toNat * 2 ^ k * 2 ^ (64 * (n - 1)) + V_take * 2 ^ k := by
                  have h_expand :
                      (topB.toNat * 2 ^ k + ctop) * 2 ^ (64 * (n - 1))
                        = topB.toNat * 2 ^ k * 2 ^ (64 * (n - 1))
                          + ctop * 2 ^ (64 * (n - 1)) := by ring
                  rw [h_expand]
                  omega
                rw [h_add_sub]
                ring
              exact divMod_size_ge3_finish U V topB.leadingZeros hk_le
                      (shiftLimbsLeft (U.limbs ++ #[(0:UInt64)]) 0 (nU + 1)
                        topB.leadingZeros (Nat.zero_le _) (by rw [h_UBufRaw_size])
                        hk_pos hk_le).1
                      VBuf
                      h_n_ge_3 h_nU_ge_n h_UBuf_size_dyn h_VBuf_size_eq
                      h_VBuf_norm h_UBuf_toNat h_VBuf_toNat hV_toNat_pos

/-! ### Correctness of `div` and `mod` -/

/-- When the divisor is zero, `divMod` returns `(0, U)`. -/
private lemma divMod_of_toNat_zero (U V : AzNat) (hV : V.toNat = 0) :
    divMod U V = (0, U) := by
  have h_size : V.limbs.size = 0 := (toNat_eq_zero_iff V).mp hV
  unfold divMod
  rw [dite_eq_left h_size]

/-- The specialised `div` returns the same value as `(divMod U V).1`.
    Holds structurally: `div` mirrors `divMod`'s branch-by-branch
    dispatch but skips the remainder-side post-processing, so each
    branch produces the first component of the corresponding `divMod`
    return. -/
theorem div_eq_divMod_fst (U V : AzNat) : div U V = (divMod U V).1 := by
  unfold div divMod
  -- Push `(_).1` through both the outer 3-way dispatch and the inner
  -- `n = 2` vs `n ≥ 3` split.  Each branch then matches structurally.
  simp only [apply_dite Prod.fst, apply_ite Prod.fst]

/-- The specialised `mod` agrees with the second projection of `divMod`.
    Proof mirrors `div_eq_divMod_fst`: `mod` shares `divMod`'s outer
    dispatch but skips the quotient-side assembly. -/
theorem mod_eq_divMod_snd (U V : AzNat) : mod U V = (divMod U V).2 := by
  unfold mod divMod
  simp only [apply_dite Prod.snd, apply_ite Prod.snd]

/-- `(U / V).toNat = U.toNat / V.toNat`. -/
@[simp] theorem toNat_div (U V : AzNat) : (U / V).toNat = U.toNat / V.toNat := by
  show (div U V).toNat = _
  rw [div_eq_divMod_fst]
  by_cases hV : V.toNat = 0
  · rw [divMod_of_toNat_zero U V hV, hV, Nat.div_zero, toNat_zero]
  · obtain ⟨h_id, h_lt⟩ := divMod_toNat U V
    have h_lt' := h_lt hV
    have h_pos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have h_eq : U.toNat
        = (divMod U V).2.toNat + (divMod U V).1.toNat * V.toNat := by omega
    rw [h_eq, Nat.add_mul_div_right _ _ h_pos, Nat.div_eq_of_lt h_lt', Nat.zero_add]

/-- `(U % V).toNat = U.toNat % V.toNat`. -/
@[simp] theorem toNat_mod (U V : AzNat) : (U % V).toNat = U.toNat % V.toNat := by
  show (mod U V).toNat = _
  rw [mod_eq_divMod_snd]
  by_cases hV : V.toNat = 0
  · rw [divMod_of_toNat_zero U V hV, hV, Nat.mod_zero]
  · obtain ⟨h_id, h_lt⟩ := divMod_toNat U V
    have h_lt' := h_lt hV
    have h_pos : 0 < V.toNat := Nat.pos_of_ne_zero hV
    have h_eq : U.toNat
        = (divMod U V).2.toNat + (divMod U V).1.toNat * V.toNat := by omega
    rw [h_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt']

/-- `ofNat`-version of `toNat_div`. -/
theorem ofNat_div (m n : Nat) : ofNat (m / n) = ofNat m / ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_div, toNat_ofNat, toNat_ofNat]

/-- `ofNat`-version of `toNat_mod`. -/
theorem ofNat_mod (m n : Nat) : ofNat (m % n) = ofNat m % ofNat n := by
  apply toNat_injective
  rw [toNat_ofNat, toNat_mod, toNat_ofNat, toNat_ofNat]

end Azurite.AzNat
