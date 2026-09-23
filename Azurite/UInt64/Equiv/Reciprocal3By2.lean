/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Azurite.UInt64.Reciprocal3By2
import Azurite.UInt64.Equiv.Reciprocal
import Azurite.UInt64.Equiv.WideMul

namespace UInt64

set_option maxHeartbeats 250000

/-- Shared ℤ-level identity underlying the step-4 key invariant of Algorithm 6.
    With `k` the decrement applied to `V0` and `k'` the additive wrap (`0` in case A,
    `1` in cases B1/B2), this captures
    `(V1 + β)·(D1·β + D0) = β³ - β² + β·P1 + V1·D0`
    where `V1 = V0 - k`, `P1 = P_low + k'·β - k·D1`. -/
private lemma recip3by2_hKey_identity
    (V0 P_low D1 D0 Q k k' : ℤ)
    (hQ : Q * 2 ^ 64 + P_low = D1 * V0 + D0)
    (hQk' : Q + D1 = 2 ^ 64 - 1 + k') :
    (V0 - k + 2 ^ 64) * (D1 * 2 ^ 64 + D0)
      = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * (P_low + k' * 2 ^ 64 - k * D1) + (V0 - k) * D0 := by
  linear_combination -(2 ^ 64 : ℤ) * hQ + (2 ^ 128 : ℤ) * hQk'

/-- Pure-ℕ "steps 5–7" correctness for Algorithm 6. Given step-4 output `V1, P1` with
the key identity `(V1 + β)(D1·β + D0) = β³ - β² + β·P1 + V1·D0` and the step-5 wide
product `V1·D0 = T_hi·β + T_lo`, the final `Vf` produced by steps 6–7 satisfies
`(Vf + β)·D ≤ β³ - 1 < (Vf + β + 1)·D` (so `Vf + β = ⌊(β³-1)/D⌋`) and fits in 64 bits. -/
private lemma recip3by2_finish_nat
    {V1 P1 D1 D0 T_hi T_lo : ℕ}
    (hD1_lo : 2 ^ 63 ≤ D1) (hD1_hi : D1 < 2 ^ 64)
    (hD0 : D0 < 2 ^ 64) (hV1 : V1 < 2 ^ 64)
    (hP1_ge : 2 ^ 64 - D1 ≤ P1) (hP1_lt : P1 < 2 ^ 64)
    (hKey : ((V1 : ℤ) + 2 ^ 64) * (D1 * 2 ^ 64 + D0)
          = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * P1 + V1 * D0)
    (hT : T_hi * 2 ^ 64 + T_lo = V1 * D0)
    (hT_hi : T_hi < 2 ^ 64) (hT_lo : T_lo < 2 ^ 64) :
    let P2 := (P1 + T_hi) % 2 ^ 64
    let c3 : ℕ := (P1 + T_hi) / 2 ^ 64
    let Vf : ℕ :=
      if c3 = 0 then V1
      else if D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo) then V1 - 2
      else V1 - 1
    (Vf + 2 ^ 64) * (D1 * 2 ^ 64 + D0) ≤ 2 ^ 192 - 1
      ∧ 2 ^ 192 - 1 < (Vf + 2 ^ 64 + 1) * (D1 * 2 ^ 64 + D0)
      ∧ Vf < 2 ^ 64 := by
  intro P2 c3 Vf
  set D : ℕ := D1 * 2 ^ 64 + D0 with hD_def
  have hD_pos : 0 < D := by
    rw [hD_def]
    have hD1_p : 0 < D1 := by omega
    have h2 : 0 < D1 * 2 ^ 64 := Nat.mul_pos hD1_p (by norm_num)
    exact Nat.lt_of_lt_of_le h2 (Nat.le_add_right _ _)
  have hPT_div_mod : P1 + T_hi = c3 * 2 ^ 64 + P2 := by
    have := Nat.div_add_mod (P1 + T_hi) (2 ^ 64)
    show P1 + T_hi = (P1 + T_hi) / 2 ^ 64 * 2 ^ 64 + (P1 + T_hi) % 2 ^ 64
    omega
  have hP2_lt : P2 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hc3_le : c3 ≤ 1 := by
    show (P1 + T_hi) / 2 ^ 64 ≤ 1
    have h1 : (P1 + T_hi) / 2 ^ 64 * 2 ^ 64 ≤ P1 + T_hi := Nat.div_mul_le_self _ _
    have h2 : P1 + T_hi < 2 * 2 ^ 64 := by omega
    by_contra h
    have h3 : 2 ≤ (P1 + T_hi) / 2 ^ 64 := by omega
    have h4 : 2 * 2 ^ 64 ≤ (P1 + T_hi) / 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_le_mul_right _ h3
    omega
  -- ℤ versions
  have hD_Z : (D : ℤ) = D1 * 2 ^ 64 + D0 := by rw [hD_def]; push_cast; ring
  have hKey_Z :
      ((V1 : ℤ) + 2 ^ 64) * D = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * P1 + V1 * D0 := by
    rw [hD_Z]; exact_mod_cast hKey
  have hT_Z : ((T_hi : ℤ) * 2 ^ 64 + T_lo) = V1 * D0 := by exact_mod_cast hT
  have hPT_Z : ((P1 : ℤ) + T_hi) = c3 * 2 ^ 64 + P2 := by exact_mod_cast hPT_div_mod
  have hGap :
      (2 : ℤ) ^ 192 - 1 - ((V1 : ℤ) + 2 ^ 64) * D
        = (1 - c3) * 2 ^ 128 - 2 ^ 64 * P2 - T_lo - 1 := by
    have h128 : (2 : ℤ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
    have h192 : (2 : ℤ) ^ 192 = 2 ^ 128 * 2 ^ 64 := by norm_num
    linear_combination (-1 : ℤ) * hKey_Z + hT_Z - (2 : ℤ) ^ 64 * hPT_Z
  -- Integer bounds
  have hD1Z_lo : (2 : ℤ) ^ 63 ≤ D1 := by exact_mod_cast hD1_lo
  have hD1Z_hi : (D1 : ℤ) < 2 ^ 64 := by exact_mod_cast hD1_hi
  have hD0Z_lt : (D0 : ℤ) < 2 ^ 64 := by exact_mod_cast hD0
  have hD0Z_nn : (0 : ℤ) ≤ D0 := by positivity
  have hV1Z_lt : (V1 : ℤ) < 2 ^ 64 := by exact_mod_cast hV1
  have hV1Z_nn : (0 : ℤ) ≤ V1 := by positivity
  have hP2Z_lt : (P2 : ℤ) < 2 ^ 64 := by exact_mod_cast hP2_lt
  have hP2Z_nn : (0 : ℤ) ≤ P2 := by positivity
  have hTloZ_lt : (T_lo : ℤ) < 2 ^ 64 := by exact_mod_cast hT_lo
  have hTloZ_nn : (0 : ℤ) ≤ T_lo := by positivity
  have hP1_Z_lo : ((2 : ℤ) ^ 64 - D1 : ℤ) ≤ P1 := by
    have hD1_le : D1 ≤ 2 ^ 64 := by omega
    have h1 : ((2 ^ 64 - D1 : ℕ) : ℤ) = (2 : ℤ) ^ 64 - D1 := by push_cast; omega
    have h2 : ((2 ^ 64 - D1 : ℕ) : ℤ) ≤ P1 := by exact_mod_cast hP1_ge
    linarith
  have h128 : (2 : ℤ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
  -- Helper to convert ℤ bounds back to ℕ.
  have h192_cast : ((2 ^ 192 - 1 : ℕ) : ℤ) = (2 : ℤ) ^ 192 - 1 := by
    have : (1 : ℕ) ≤ 2 ^ 192 := by norm_num
    push_cast [this]
  rcases (show c3 = 0 ∨ c3 = 1 by omega) with hc3 | hc3
  · -- c3 = 0: no overflow in step 6, Vf = V1.
    have hVf_val : Vf = V1 := by
      show (if c3 = 0 then V1 else _) = V1
      rw [ite_eq_left hc3]
    have hc3Z : (c3 : ℤ) = 0 := by exact_mod_cast hc3
    have hP2_eq : P2 = P1 + T_hi := by omega
    have hP2_ge : 2 ^ 64 - D1 ≤ P2 := by rw [hP2_eq]; omega
    have hP2_Z_ge : (2 : ℤ) ^ 64 - D1 ≤ P2 := by
      have h1 : ((2 ^ 64 - D1 : ℕ) : ℤ) = (2 : ℤ) ^ 64 - D1 := by push_cast; omega
      have h2 : ((2 ^ 64 - D1 : ℕ) : ℤ) ≤ P2 := by exact_mod_cast hP2_ge
      linarith
    have hGap0 :
        (2 : ℤ) ^ 192 - 1 - ((V1 : ℤ) + 2 ^ 64) * D = 2 ^ 128 - 2 ^ 64 * P2 - T_lo - 1 := by
      rw [hGap, hc3Z]; ring
    rw [hVf_val]
    refine ⟨?_, ?_, hV1⟩
    · have hZlb : (0 : ℤ) ≤ 2 ^ 128 - 2 ^ 64 * P2 - T_lo - 1 := by nlinarith [h128]
      have hZle : ((V1 : ℤ) + 2 ^ 64) * D ≤ 2 ^ 192 - 1 := by linarith
      have hc_lhs : (((V1 + 2 ^ 64) * D : ℕ) : ℤ) = ((V1 : ℤ) + 2 ^ 64) * D := by push_cast; ring
      have : ((V1 + 2 ^ 64) * D : ℕ) ≤ 2 ^ 192 - 1 := by
        have : (((V1 + 2 ^ 64) * D : ℕ) : ℤ) ≤ ((2 ^ 192 - 1 : ℕ) : ℤ) := by
          rw [hc_lhs, h192_cast]; exact hZle
        exact_mod_cast this
      exact this
    · have hZub : (2 : ℤ) ^ 128 - 2 ^ 64 * (P2 : ℤ) - T_lo - 1 < (D : ℤ) := by
        rw [hD_Z]; nlinarith [hP2_Z_ge, h128]
      have hZlt : ((2 : ℤ) ^ 192 - 1) < ((V1 : ℤ) + 2 ^ 64 + 1) * D := by linarith
      have hc_lhs : (((V1 + 2 ^ 64 + 1) * D : ℕ) : ℤ) = ((V1 : ℤ) + 2 ^ 64 + 1) * D := by
        push_cast; ring
      have : (2 ^ 192 - 1 : ℕ) < ((V1 + 2 ^ 64 + 1) * D : ℕ) := by
        have : ((2 ^ 192 - 1 : ℕ) : ℤ) < (((V1 + 2 ^ 64 + 1) * D : ℕ) : ℤ) := by
          rw [hc_lhs, h192_cast]; exact hZlt
        exact_mod_cast this
      exact this
  · -- c3 = 1
    have hc3Z : (c3 : ℤ) = 1 := by exact_mod_cast hc3
    have hGap1 :
        (2 : ℤ) ^ 192 - 1 - ((V1 : ℤ) + 2 ^ 64) * D = -(2 ^ 64 * P2) - T_lo - 1 := by
      rw [hGap, hc3Z]; ring
    by_cases hStep7 : D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo)
    · -- Vf = V1 - 2. Need V1 ≥ 2.
      have hVf_val : Vf = V1 - 2 := by
        show (if c3 = 0 then V1 else if D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo) then V1 - 2
              else V1 - 1) = V1 - 2
        rw [ite_eq_right (by omega : c3 ≠ 0), ite_eq_left hStep7]
      have hV1_ge_2 : 2 ≤ V1 := by
        by_contra h
        push Not at h
        -- V1 ∈ {0, 1}. Then V1 * D0 < 2^64, so T_hi = 0, c3 = 0. Contradiction.
        have hV1D0_lt : V1 * D0 < 2 ^ 64 := by
          have : V1 * D0 ≤ 1 * (2 ^ 64 - 1) := by
            apply Nat.mul_le_mul <;> omega
          omega
        have hT_hi_0 : T_hi = 0 := by
          by_contra hh
          have : T_hi * 2 ^ 64 ≥ 2 ^ 64 := by
            have : 1 ≤ T_hi := by omega
            calc T_hi * 2 ^ 64 ≥ 1 * 2 ^ 64 := Nat.mul_le_mul_right _ this
              _ = 2 ^ 64 := by ring
          omega
        have hc3_0 : c3 = 0 := by
          show (P1 + T_hi) / 2 ^ 64 = 0
          rw [hT_hi_0]; exact Nat.div_eq_of_lt (by omega : P1 + 0 < 2 ^ 64)
        omega
      rw [hVf_val]
      refine ⟨?_, ?_, by omega⟩
      · have hV1_sub_Z : ((V1 - 2 : ℕ) : ℤ) = (V1 : ℤ) - 2 := by omega
        have hZkey :
            (2 : ℤ) ^ 192 - 1 - (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64) * D
              = (-(2 ^ 64 * (P2 : ℤ)) - T_lo - 1) + 2 * D := by
          rw [hV1_sub_Z]; linear_combination hGap1
        have hLB_Z : (0 : ℤ) ≤ -(2 ^ 64 * (P2 : ℤ)) - T_lo - 1 + 2 * D := by
          rw [hD_Z]
          rcases hStep7 with h1 | ⟨hP2eq, hT_ge_D0⟩
          · have h1Z : (D1 : ℤ) + 1 ≤ P2 := by exact_mod_cast h1
            linarith [mul_le_mul_of_nonneg_left (show (P2 : ℤ) + 1 ≤ 2 * D1 by linarith)
              (show (0:ℤ) ≤ 2^64 by norm_num)]
          · have hP2eqZ : (P2 : ℤ) = D1 := by exact_mod_cast hP2eq
            have hTge : (D0 : ℤ) ≤ T_lo := by exact_mod_cast hT_ge_D0
            rw [hP2eqZ]; linarith
        have hZle : (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64) * D ≤ 2 ^ 192 - 1 := by linarith
        have hc_lhs :
            (((V1 - 2 + 2 ^ 64) * D : ℕ) : ℤ) = (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64) * D := by
          push_cast; ring
        have : ((V1 - 2 + 2 ^ 64) * D : ℕ) ≤ 2 ^ 192 - 1 := by
          have : (((V1 - 2 + 2 ^ 64) * D : ℕ) : ℤ) ≤ ((2 ^ 192 - 1 : ℕ) : ℤ) := by
            rw [hc_lhs, h192_cast]; exact hZle
          exact_mod_cast this
        exact this
      · have hV1_sub_Z : ((V1 - 2 : ℕ) : ℤ) = (V1 : ℤ) - 2 := by omega
        have hZkey :
            (2 : ℤ) ^ 192 - 1 - (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64) * D
              = (-(2 ^ 64 * (P2 : ℤ)) - T_lo - 1) + 2 * D := by
          rw [hV1_sub_Z]; linear_combination hGap1
        have hUB_Z : -(2 ^ 64 * (P2 : ℤ)) - T_lo - 1 + 2 * (D : ℤ) < D := by
          rw [hD_Z]
          rcases hStep7 with h1 | ⟨hP2eq, hT_ge_D0⟩
          · have h1Z : (D1 : ℤ) + 1 ≤ P2 := by exact_mod_cast h1
            linarith [mul_le_mul_of_nonneg_left (show (D1 : ℤ) + 1 ≤ P2 from h1Z)
              (show (0:ℤ) ≤ 2^64 by norm_num)]
          · have hP2eqZ : (P2 : ℤ) = D1 := by exact_mod_cast hP2eq
            have hTge : (D0 : ℤ) ≤ T_lo := by exact_mod_cast hT_ge_D0
            rw [hP2eqZ]; linarith
        have hZlt : ((2 : ℤ) ^ 192 - 1) < (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64 + 1) * D := by
          have hstep :
              (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64 + 1) * D
                = (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64) * D + D := by ring
          linarith
        have hc_lhs : (((V1 - 2 + 2 ^ 64 + 1) * D : ℕ) : ℤ)
            = (((V1 - 2 : ℕ) : ℤ) + 2 ^ 64 + 1) * D := by push_cast; ring
        have : (2 ^ 192 - 1 : ℕ) < ((V1 - 2 + 2 ^ 64 + 1) * D : ℕ) := by
          have : ((2 ^ 192 - 1 : ℕ) : ℤ) < (((V1 - 2 + 2 ^ 64 + 1) * D : ℕ) : ℤ) := by
            rw [hc_lhs, h192_cast]; exact hZlt
          exact_mod_cast this
        exact this
    · -- Vf = V1 - 1. Need V1 ≥ 1.
      have hVf_val : Vf = V1 - 1 := by
        show (if c3 = 0 then V1 else if D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo) then V1 - 2
              else V1 - 1) = V1 - 1
        rw [ite_eq_right (by omega : c3 ≠ 0), ite_eq_right hStep7]
      have hV1_ge_1 : 1 ≤ V1 := by
        by_contra h
        push Not at h
        have hV1_0 : V1 = 0 := by omega
        have hT_0 : T_hi * 2 ^ 64 + T_lo = 0 := by rw [hT, hV1_0]; ring
        have hT_hi_0 : T_hi = 0 := by omega
        have : c3 = 0 := by
          show (P1 + T_hi) / 2 ^ 64 = 0
          rw [hT_hi_0]; exact Nat.div_eq_of_lt (by omega : P1 + 0 < 2 ^ 64)
        omega
      push Not at hStep7
      have hP2_le : P2 ≤ D1 := hStep7.1
      have hNotEq : P2 = D1 → T_lo < D0 := fun heq => hStep7.2 heq
      rw [hVf_val]
      refine ⟨?_, ?_, by omega⟩
      · have hP2Z_le : (P2 : ℤ) ≤ D1 := by exact_mod_cast hP2_le
        have hV1_sub_Z : ((V1 - 1 : ℕ) : ℤ) = (V1 : ℤ) - 1 := by omega
        have hZkey :
            (2 : ℤ) ^ 192 - 1 - (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64) * D
              = (-(2 ^ 64 * (P2 : ℤ)) - T_lo - 1) + D := by
          rw [hV1_sub_Z]; linear_combination hGap1
        have hLB_Z : (0 : ℤ) ≤ -(2 ^ 64 * (P2 : ℤ)) - T_lo - 1 + D := by
          rw [hD_Z]
          rcases lt_or_eq_of_le hP2Z_le with hlt | heq
          · linarith [mul_le_mul_of_nonneg_left (show (P2 : ℤ) + 1 ≤ D1 from by linarith)
              (show (0:ℤ) ≤ 2^64 by norm_num)]
          · have hTlt : T_lo < D0 := hNotEq (by exact_mod_cast heq)
            have hTltZ : (T_lo : ℤ) < D0 := by exact_mod_cast hTlt
            rw [heq]; linarith
        have hZle : (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64) * D ≤ 2 ^ 192 - 1 := by linarith
        have hc_lhs :
            (((V1 - 1 + 2 ^ 64) * D : ℕ) : ℤ) = (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64) * D := by
          push_cast; ring
        have : ((V1 - 1 + 2 ^ 64) * D : ℕ) ≤ 2 ^ 192 - 1 := by
          have : (((V1 - 1 + 2 ^ 64) * D : ℕ) : ℤ) ≤ ((2 ^ 192 - 1 : ℕ) : ℤ) := by
            rw [hc_lhs, h192_cast]; exact hZle
          exact_mod_cast this
        exact this
      · have hV1_sub_Z : ((V1 - 1 : ℕ) : ℤ) = (V1 : ℤ) - 1 := by omega
        have hZkey :
            (2 : ℤ) ^ 192 - 1 - (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64) * D
              = (-(2 ^ 64 * (P2 : ℤ)) - T_lo - 1) + D := by
          rw [hV1_sub_Z]; linear_combination hGap1
        have hUB_Z : -(2 ^ 64 * (P2 : ℤ)) - T_lo - 1 + (D : ℤ) < D := by
          have : (0 : ℤ) ≤ 2 ^ 64 * P2 :=
            mul_nonneg (by positivity) hP2Z_nn
          linarith
        have hZlt : ((2 : ℤ) ^ 192 - 1) < (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64 + 1) * D := by
          have hstep :
              (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64 + 1) * D
                = (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64) * D + D := by ring
          linarith
        have hc_lhs : (((V1 - 1 + 2 ^ 64 + 1) * D : ℕ) : ℤ)
            = (((V1 - 1 : ℕ) : ℤ) + 2 ^ 64 + 1) * D := by push_cast; ring
        have : (2 ^ 192 - 1 : ℕ) < ((V1 - 1 + 2 ^ 64 + 1) * D : ℕ) := by
          have : ((2 ^ 192 - 1 : ℕ) : ℤ) < (((V1 - 1 + 2 ^ 64 + 1) * D : ℕ) : ℤ) := by
            rw [hc_lhs, h192_cast]; exact hZlt
          exact_mod_cast this
        exact this

/-- Given step-4 data `(v1, p1)` satisfying the Möller–Granlund invariant, compute
the final value of the algorithm (steps 5–7) in terms of its `.toNat`. -/
private lemma recip3by2_tail_toNat
    (d_hi d_lo v1 p1 : UInt64)
    (hD1 : 2 ^ 63 ≤ d_hi.toNat)
    (hP1_ge : 2 ^ 64 - d_hi.toNat ≤ p1.toNat)
    (hKey : ((v1.toNat : ℤ) + 2 ^ 64) * (d_hi.toNat * 2 ^ 64 + d_lo.toNat)
          = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * p1.toNat + v1.toNat * d_lo.toNat) :
    (let (t_hi, t_lo) := wideMul v1 d_lo
     let p := p1 + t_hi
     if p < t_hi then
       let v := v1 - 1
       if p > d_hi ∨ (p = d_hi ∧ t_lo ≥ d_lo) then v - 1 else v
     else v1).toNat
    = (2 ^ 192 - 1) / (d_hi.toNat * 2 ^ 64 + d_lo.toNat) - 2 ^ 64 := by
  set D1 : ℕ := d_hi.toNat with hD1_eq
  set D0 : ℕ := d_lo.toNat with hD0_eq
  set V1 : ℕ := v1.toNat with hV1_eq
  set P1 : ℕ := p1.toNat with hP1_eq
  set D : ℕ := D1 * 2 ^ 64 + D0 with hD_eq
  have hD1_lt : D1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD0_lt : D0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV1_lt : V1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hP1_lt : P1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_pos : 0 < D := by
    rw [hD_eq]
    have h1 : 0 < D1 := by omega
    exact Nat.lt_of_lt_of_le (Nat.mul_pos h1 (by norm_num : 0 < 2 ^ 64))
      (Nat.le_add_right _ _)
  rcases hwm : wideMul v1 d_lo with ⟨t_hi_u, t_lo_u⟩
  set T_hi : ℕ := t_hi_u.toNat with hT_hi_eq
  set T_lo : ℕ := t_lo_u.toNat with hT_lo_eq
  have hT_hi_lt : T_hi < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hT_lo_lt : T_lo < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hT_val : T_hi * 2 ^ 64 + T_lo = V1 * D0 := by
    have h := toNat_wideMul v1 d_lo
    rw [hwm] at h
    exact h
  have hsum_lt : P1 + T_hi < 2 * 2 ^ 64 := by omega
  set P2 : ℕ := (P1 + T_hi) % 2 ^ 64 with hP2_eq
  set c3 : ℕ := (P1 + T_hi) / 2 ^ 64 with hc3_eq
  have hP2_lt : P2 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hPT_split : P1 + T_hi = c3 * 2 ^ 64 + P2 := by
    have h := Nat.div_add_mod (P1 + T_hi) (2 ^ 64)
    rw [hP2_eq, hc3_eq]; omega
  have hc3_le : c3 ≤ 1 := by
    rw [hc3_eq]
    by_contra hh
    push Not at hh
    have h1 : 2 ≤ (P1 + T_hi) / 2 ^ 64 := by omega
    have h2 : 2 * 2 ^ 64 ≤ (P1 + T_hi) / 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_le_mul_right _ h1
    have h3 := Nat.div_mul_le_self (P1 + T_hi) (2 ^ 64)
    omega
  set p_u : UInt64 := p1 + t_hi_u with hp_u_eq
  have hp_u_toNat : p_u.toNat = P2 := by
    rw [hp_u_eq, _root_.UInt64.toNat_add, hP2_eq]
  have h_lt_iff : (p_u < t_hi_u) ↔ c3 = 1 := by
    rw [_root_.UInt64.lt_iff_toNat_lt, hp_u_toNat]
    constructor
    · intro h
      rcases (show c3 = 0 ∨ c3 = 1 by omega) with h0 | h1
      · rw [h0] at hPT_split; omega
      · exact h1
    · intro h
      rw [h] at hPT_split
      omega
  have h_gt_d_iff : (p_u > d_hi) ↔ D1 < P2 := by
    show d_hi < p_u ↔ _
    rw [_root_.UInt64.lt_iff_toNat_lt, hp_u_toNat]
  have h_eq_d_iff : (p_u = d_hi) ↔ P2 = D1 := by
    rw [← _root_.UInt64.toNat_inj, hp_u_toNat]
  have h_tlo_ge_iff : (t_lo_u ≥ d_lo) ↔ D0 ≤ T_lo := by
    show d_lo ≤ t_lo_u ↔ _
    rw [_root_.UInt64.le_iff_toNat_le]
  have hKey' : ((V1 : ℤ) + 2 ^ 64) * (D1 * 2 ^ 64 + D0)
      = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * P1 + V1 * D0 := hKey
  have hFinish := recip3by2_finish_nat (V1 := V1) (P1 := P1) (D1 := D1) (D0 := D0)
    (T_hi := T_hi) (T_lo := T_lo) hD1 hD1_lt hD0_lt hV1_lt hP1_ge hP1_lt
    hKey' hT_val hT_hi_lt hT_lo_lt
  -- Unfold and compute the final UInt64's .toNat.
  have h_pgt_or_teq : ¬(p_u > d_hi ∨ p_u = d_hi ∧ t_lo_u ≥ d_lo)
        ↔ ¬(D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo)) := by
    rw [not_or, not_or, h_gt_d_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      intro ⟨heq, hle⟩
      exact h2 ⟨(h_eq_d_iff.mpr heq), (h_tlo_ge_iff.mpr hle)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      intro ⟨heq, hle⟩
      exact h2 ⟨(h_eq_d_iff.mp heq), (h_tlo_ge_iff.mp hle)⟩
  -- Compute the final result. After rcases on wideMul, the let has reduced.
  change (if p_u < t_hi_u then
          if p_u > d_hi ∨ p_u = d_hi ∧ t_lo_u ≥ d_lo then v1 - 1 - 1 else v1 - 1
         else v1).toNat = _
  -- Case split on c3.
  rcases (show c3 = 0 ∨ c3 = 1 by omega) with hc3_0 | hc3_1
  · -- c3 = 0: final is v1.
    have h_nlt : ¬ p_u < t_hi_u := by
      rw [h_lt_iff]; omega
    rw [ite_eq_right h_nlt]
    -- Vf = V1 in the helper
    obtain ⟨hle_f, hlt_f, hVf_lt⟩ := hFinish
    -- Vf = if c3 = 0 then V1 else _ = V1
    have hVf_eq : (if c3 = 0 then V1
                  else if D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo) then V1 - 2
                  else V1 - 1) = V1 := by
      rw [ite_eq_left hc3_0]
    rw [hVf_eq] at hle_f hlt_f
    show V1 = (2 ^ 192 - 1) / D - 2 ^ 64
    have hdiv : (2 ^ 192 - 1) / D = V1 + 2 ^ 64 :=
      Nat.div_eq_of_lt_le (n := D) (m := 2 ^ 192 - 1) (k := V1 + 2 ^ 64) hle_f hlt_f
    omega
  · -- c3 = 1
    have h_lt : p_u < t_hi_u := by rw [h_lt_iff]; exact hc3_1
    rw [ite_eq_left h_lt]
    -- Need to compute (v1 - 1).toNat. Depends on V1 ≥ 1.
    obtain ⟨hle_f, hlt_f, hVf_lt⟩ := hFinish
    have hVf_def : (if c3 = 0 then V1
                    else if D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo) then V1 - 2
                    else V1 - 1)
          = if D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo) then V1 - 2 else V1 - 1 := by
      rw [ite_eq_right (by omega : c3 ≠ 0)]
    rw [hVf_def] at hle_f hlt_f hVf_lt
    by_cases hStep7 : D1 < P2 ∨ (P2 = D1 ∧ D0 ≤ T_lo)
    · -- Vf = V1 - 2. Need V1 ≥ 2.
      rw [ite_eq_left hStep7] at hle_f hlt_f hVf_lt
      have hV1_ge_2 : 2 ≤ V1 := by
        -- Derived from the helper's proof: if V1 < 2 then c3 = 0, contradicting c3 = 1.
        by_contra h; push Not at h
        have hV1D0_lt : V1 * D0 < 2 ^ 64 := by
          have : V1 * D0 ≤ 1 * (2 ^ 64 - 1) := by
            apply Nat.mul_le_mul <;> omega
          omega
        have hT_hi_0 : T_hi = 0 := by
          by_contra hh
          have h1 : 1 ≤ T_hi := by omega
          have h2 : 1 * 2 ^ 64 ≤ T_hi * 2 ^ 64 := Nat.mul_le_mul_right _ h1
          omega
        have hc3_0 : c3 = 0 := by
          rw [hc3_eq, hT_hi_0]
          exact Nat.div_eq_of_lt (by omega)
        omega
      have h_step7_u : p_u > d_hi ∨ (p_u = d_hi ∧ t_lo_u ≥ d_lo) := by
        rcases hStep7 with h1 | ⟨h1, h2⟩
        · left; rw [h_gt_d_iff]; exact h1
        · right; exact ⟨h_eq_d_iff.mpr h1, h_tlo_ge_iff.mpr h2⟩
      rw [ite_eq_left h_step7_u]
      -- Final UInt64 is v1 - 1 - 1. Its .toNat = V1 - 2.
      have h1 : (v1 - 1).toNat = V1 - 1 := by
        rw [_root_.UInt64.toNat_sub_of_le]
        · show V1 - (1 : UInt64).toNat = V1 - 1; rfl
        · rw [_root_.UInt64.le_iff_toNat_le]
          show (1 : UInt64).toNat ≤ V1
          show 1 ≤ V1
          omega
      have h2 : (v1 - 1 - 1).toNat = V1 - 2 := by
        rw [_root_.UInt64.toNat_sub_of_le]
        · show (v1 - 1).toNat - (1 : UInt64).toNat = V1 - 2
          rw [h1]; show V1 - 1 - 1 = V1 - 2; omega
        · rw [_root_.UInt64.le_iff_toNat_le, h1]
          show (1 : UInt64).toNat ≤ V1 - 1
          show 1 ≤ V1 - 1
          omega
      rw [h2]
      show V1 - 2 = (2 ^ 192 - 1) / D - 2 ^ 64
      have hdiv : (2 ^ 192 - 1) / D = (V1 - 2) + 2 ^ 64 :=
        Nat.div_eq_of_lt_le (n := D) (m := 2 ^ 192 - 1) (k := V1 - 2 + 2 ^ 64) hle_f hlt_f
      omega
    · rw [ite_eq_right hStep7] at hle_f hlt_f hVf_lt
      have h_nstep7_u : ¬ (p_u > d_hi ∨ p_u = d_hi ∧ t_lo_u ≥ d_lo) :=
        h_pgt_or_teq.mpr hStep7
      rw [ite_eq_right h_nstep7_u]
      -- Final UInt64 is v1 - 1. Its .toNat = V1 - 1.
      have hV1_ge_1 : 1 ≤ V1 := by
        by_contra h; push Not at h
        have hV1_0 : V1 = 0 := by omega
        have hT_0 : T_hi * 2 ^ 64 + T_lo = 0 := by rw [hT_val, hV1_0]; ring
        have hT_hi_0 : T_hi = 0 := by omega
        have hc3_0 : c3 = 0 := by
          rw [hc3_eq, hT_hi_0]
          exact Nat.div_eq_of_lt (by omega)
        omega
      have h1 : (v1 - 1).toNat = V1 - 1 := by
        rw [_root_.UInt64.toNat_sub_of_le]
        · show V1 - (1 : UInt64).toNat = V1 - 1; rfl
        · rw [_root_.UInt64.le_iff_toNat_le]
          show (1 : UInt64).toNat ≤ V1
          show 1 ≤ V1
          omega
      rw [h1]
      show V1 - 1 = (2 ^ 192 - 1) / D - 2 ^ 64
      have hdiv : (2 ^ 192 - 1) / D = (V1 - 1) + 2 ^ 64 :=
        Nat.div_eq_of_lt_le (n := D) (m := 2 ^ 192 - 1) (k := V1 - 1 + 2 ^ 64) hle_f hlt_f
      omega

/-- Shared setup data used by all three step-4 cases of Algorithm 6: establishes
ℕ/ℤ forms of the reciprocal invariant, bounds on `Q = (D1·V0+D0) / 2^64`, and the
boundary identity linking `Q`, `D1`, and `P_low`. -/
private lemma recip3by2_caseA
    (d_hi d_lo : UInt64) (hd : 2 ^ 63 ≤ d_hi.toNat)
    (hA : ¬ d_hi * reciprocal d_hi hd + d_lo < d_lo) :
    (reciprocal3By2 d_hi d_lo hd).toNat =
      (2 ^ 192 - 1) / (d_hi.toNat * 2 ^ 64 + d_lo.toNat) - 2 ^ 64 := by
  set D1 : ℕ := d_hi.toNat with hD1_eq
  set D0 : ℕ := d_lo.toNat with hD0_eq
  set V0 : ℕ := (reciprocal d_hi hd).toNat with hV0_eq
  have hD1_lt : D1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD0_lt : D0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV0_lt : V0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD1_ge : 2 ^ 63 ≤ D1 := hd
  have hD1_pos : 0 < D1 := by omega
  have hV0_eq_div : V0 = (2 ^ 128 - 1) / D1 - 2 ^ 64 := toNat_reciprocal d_hi hd
  have h_div_ge_64 : 2 ^ 64 ≤ (2 ^ 128 - 1) / D1 := by
    rw [Nat.le_div_iff_mul_le hD1_pos]
    calc 2 ^ 64 * D1 ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 ^ 128 - 1 := by norm_num
  have hV0_hi : (V0 + 2 ^ 64) * D1 ≤ 2 ^ 128 - 1 := by
    rw [hV0_eq_div, Nat.sub_add_cancel h_div_ge_64]
    exact Nat.div_mul_le_self _ _
  have hV0_lo : 2 ^ 128 - 1 < (V0 + 2 ^ 64 + 1) * D1 := by
    rw [hV0_eq_div]
    have heq : (2 ^ 128 - 1) / D1 - 2 ^ 64 + 2 ^ 64 + 1 = (2 ^ 128 - 1) / D1 + 1 := by omega
    rw [heq]
    have h := Nat.lt_mul_div_succ (2 ^ 128 - 1) hD1_pos
    have hcomm : D1 * ((2 ^ 128 - 1) / D1 + 1) = ((2 ^ 128 - 1) / D1 + 1) * D1 := by ring
    omega
  -- Shorthand for `p_raw = d_hi * v0 + d_lo` and its `.toNat`.
  set p_raw : UInt64 := d_hi * reciprocal d_hi hd + d_lo with hp_raw_eq
  set P_low : ℕ := p_raw.toNat with hP_low_eq
  have hP_low_lt : P_low < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hP_low_mod : P_low = (D1 * V0 + D0) % 2 ^ 64 := by
    show p_raw.toNat = _
    rw [hp_raw_eq, _root_.UInt64.toNat_add, _root_.UInt64.toNat_mul]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hDVD_ub : D1 * V0 + D0 < 2 ^ 128 := by
    have h1 : V0 * D1 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
      have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
      rw [← heq]; exact hV0_hi
    have h2 : (2 : ℕ) ^ 64 * D1 ≥ 2 ^ 127 := by
      have : 2 ^ 64 * D1 ≥ 2 ^ 64 * 2 ^ 63 := Nat.mul_le_mul_left _ hD1_ge
      have heq : (2 : ℕ) ^ 64 * 2 ^ 63 = 2 ^ 127 := by norm_num
      omega
    have h3 : V0 * D1 ≤ 2 ^ 127 - 1 := by omega
    have hcomm : V0 * D1 = D1 * V0 := by ring
    omega
  -- Q = (D1*V0+D0) / 2^64, so P_low = D1*V0+D0 - Q*2^64.
  set Q : ℕ := (D1 * V0 + D0) / 2 ^ 64 with hQ_eq
  have hQ_mul_add : Q * 2 ^ 64 + P_low = D1 * V0 + D0 := by
    rw [hQ_eq, hP_low_mod]
    have h := Nat.div_add_mod (D1 * V0 + D0) (2 ^ 64)
    omega
  have hQ_lt_2p64 : Q < 2 ^ 64 := by
    rw [hQ_eq]
    by_contra hh; push Not at hh
    have : 2 ^ 64 * 2 ^ 64 ≤ (D1 * V0 + D0) / 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hh
    have := Nat.div_mul_le_self (D1 * V0 + D0) (2 ^ 64)
    have : 2 ^ 128 ≤ D1 * V0 + D0 := by
      have h1 : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
      omega
    omega
  -- Some Nat facts about D1.
  have hD1_le_2p64 : D1 ≤ 2 ^ 64 := by omega
  have hD1_mul_le : D1 * 2 ^ 64 ≤ 2 ^ 128 := by
    calc D1 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ hD1_le_2p64
      _ = 2 ^ 128 := by norm_num
  have h2p64_D1_eq : (2 ^ 64 - D1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
    rw [Nat.sub_mul]
    have : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
    have : D1 * 2 ^ 64 = 2 ^ 64 * D1 := by ring
    omega
  -- Q ≤ 2^64 - D1.
  have hQ_le : Q ≤ 2 ^ 64 - D1 := by
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : V0 * D1 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
      have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
      rw [← heq]; exact hV0_hi
    -- Q*2^64 + P_low = D1*V0 + D0 ≤ (2^128-1 - 2^64*D1) + (2^64-1).
    have h2 : Q * 2 ^ 64 < (2 ^ 64 - D1 + 1) * 2 ^ 64 := by
      have hexp : (2 ^ 64 - D1 + 1) * 2 ^ 64 = (2 ^ 64 - D1) * 2 ^ 64 + 2 ^ 64 := by ring
      omega
    by_contra hh; push Not at hh
    have hge : 2 ^ 64 - D1 + 1 ≤ Q := hh
    have : (2 ^ 64 - D1 + 1) * 2 ^ 64 ≤ Q * 2 ^ 64 := Nat.mul_le_mul_right _ hge
    omega
  -- Q ≥ 2^64 - D1 - 1.
  have hQ_ge : 2 ^ 64 - D1 - 1 ≤ Q := by
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : D1 * V0 + 2 ^ 64 * D1 + D1 ≥ 2 ^ 128 := by
      have heq : (V0 + 2 ^ 64 + 1) * D1 = V0 * D1 + 2 ^ 64 * D1 + D1 := by ring
      omega
    have hbd : 2 ^ 64 * D1 + D1 ≤ 2 ^ 128 - 1 := by
      have ha : (2 ^ 64 + 1) * D1 ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hb : (2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
      have he : (2 ^ 64 + 1) * D1 = 2 ^ 64 * D1 + D1 := by ring
      omega
    have hfact : (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 1) + 1 := by omega
      calc (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64
          = ((2 ^ 64 - D1 - 1) + 1) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh]
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    -- From hQ_mul_add and h1, Q*2^64 + P_low ≥ 2^128 - 2^64*D1 - D1.
    -- P_low < 2^64, so Q*2^64 > 2^128 - 2^64*D1 - D1 - 2^64.
    -- hfact: (2^64-D1-1)*2^64 = 2^128 - 2^64*D1 - 2^64.
    -- So Q*2^64 > (2^64-D1-1)*2^64 - D1, hence Q*2^64 ≥ (2^64-D1-1)*2^64 - D1 + 1.
    -- Since (2^64-D1-1)*2^64 is much larger than D1, Q ≥ 2^64-D1-1.
    by_contra hh
    push Not at hh
    have hQlt : Q ≤ 2 ^ 64 - D1 - 2 := by omega
    have hmul : Q * 2 ^ 64 ≤ (2 ^ 64 - D1 - 2) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hQlt
    have hfact2 : (2 ^ 64 - D1 - 2) * 2 ^ 64 + 2 * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh' : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 2) + 2 := by omega
      calc (2 ^ 64 - D1 - 2) * 2 ^ 64 + 2 * 2 ^ 64
          = ((2 ^ 64 - D1 - 2) + 2) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh']
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    omega
  have hQ_int : ((Q : ℤ) * 2 ^ 64 + P_low : ℤ) = D1 * V0 + D0 := by exact_mod_cast hQ_mul_add
  -- Case A: no overflow. V1 = V0, P1 = P_low.
  have hA_nat : ¬ (P_low < D0) :=
    fun h => hA (_root_.UInt64.lt_iff_toNat_lt.mpr h)
  have hP_low_ge_D0 : D0 ≤ P_low := Nat.le_of_not_lt hA_nat
  have hQ_val : Q = 2 ^ 64 - D1 - 1 := by
    have hcase : Q = 2 ^ 64 - D1 - 1 ∨ Q = 2 ^ 64 - D1 := by omega
    rcases hcase with h | h
    · exact h
    · exfalso
      have hQ_mul : Q * 2 ^ 64 = (2 ^ 64 - D1) * 2 ^ 64 := by rw [h]
      have hD1V0_hi : D1 * V0 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
        have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
        have hcomm : V0 * D1 = D1 * V0 := by ring
        have := hV0_hi
        omega
      have hP_low_ub : P_low ≤ D0 - 1 := by
        have h1 : (2 ^ 64 - D1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
        omega
      omega
  have hA_raw : ¬ (d_hi * reciprocal d_hi hd + d_lo < d_lo) := hA
  have h_red : reciprocal3By2 d_hi d_lo hd =
      reciprocal3By2Tail d_hi d_lo (reciprocal d_hi hd) p_raw := by
    unfold reciprocal3By2
    rw [ite_eq_right hA_raw]
  rw [h_red]
  set v1_u : UInt64 := reciprocal d_hi hd with hv1_u_eq
  set p1_u : UInt64 := p_raw with hp1_u_eq
  show (reciprocal3By2Tail d_hi d_lo v1_u p1_u).toNat = _
  unfold reciprocal3By2Tail
  have hv1_u_toNat : v1_u.toNat = V0 := by rw [hv1_u_eq]
  have hp1_u_toNat : p1_u.toNat = P_low := by rw [hp1_u_eq]
  have hKey : ((v1_u.toNat : ℤ) + 2 ^ 64) * (d_hi.toNat * 2 ^ 64 + d_lo.toNat)
        = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * p1_u.toNat + v1_u.toNat * d_lo.toNat := by
    have hV1_Z : (v1_u.toNat : ℤ) = (V0 : ℤ) - 0 := by
      rw [hv1_u_toNat]; ring
    have hP1_Z : (p1_u.toNat : ℤ) = (P_low : ℤ) + 0 * 2 ^ 64 - 0 * D1 := by
      rw [hp1_u_toNat]; push_cast; ring
    have hQk' : (Q : ℤ) + D1 = 2 ^ 64 - 1 + 0 := by
      have hc : (Q : ℤ) = (2 ^ 64 : ℤ) - D1 - 1 := by
        have h1 : ((2 ^ 64 - D1 - 1 : ℕ) : ℤ) = (2 ^ 64 : ℤ) - D1 - 1 := by push_cast; omega
        have h2 : (Q : ℤ) = ((2 ^ 64 - D1 - 1 : ℕ) : ℤ) := by exact_mod_cast hQ_val
        linarith
      linarith
    have key := recip3by2_hKey_identity (V0 : ℤ) P_low D1 D0 Q 0 0 hQ_int hQk'
    show ((v1_u.toNat : ℤ) + 2 ^ 64) * (D1 * 2 ^ 64 + D0) = _
    rw [hV1_Z, hP1_Z]
    linear_combination key
  have hP1_ge : 2 ^ 64 - d_hi.toNat ≤ p1_u.toNat := by
    show 2 ^ 64 - D1 ≤ _
    rw [hp1_u_toNat]
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : D1 * V0 + 2 ^ 64 * D1 + D1 ≥ 2 ^ 128 := by
      have heq : (V0 + 2 ^ 64 + 1) * D1 = V0 * D1 + 2 ^ 64 * D1 + D1 := by ring
      omega
    have h2 : Q * 2 ^ 64 = (2 ^ 64 - D1 - 1) * 2 ^ 64 := by rw [hQ_val]
    have h3 : (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 1) + 1 := by omega
      calc (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64
          = ((2 ^ 64 - D1 - 1) + 1) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh]
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    omega
  exact recip3by2_tail_toNat d_hi d_lo v1_u p1_u hd hP1_ge hKey

/-- Step-4 case B1 of Algorithm 6: `p_raw` overflowed `d_lo` but `p_raw < d_hi`. -/
private lemma recip3by2_caseB1
    (d_hi d_lo : UInt64) (hd : 2 ^ 63 ≤ d_hi.toNat)
    (hA : d_hi * reciprocal d_hi hd + d_lo < d_lo)
    (hB2 : ¬ d_hi * reciprocal d_hi hd + d_lo ≥ d_hi) :
    (reciprocal3By2 d_hi d_lo hd).toNat =
      (2 ^ 192 - 1) / (d_hi.toNat * 2 ^ 64 + d_lo.toNat) - 2 ^ 64 := by
  set D1 : ℕ := d_hi.toNat with hD1_eq
  set D0 : ℕ := d_lo.toNat with hD0_eq
  set V0 : ℕ := (reciprocal d_hi hd).toNat with hV0_eq
  have hD1_lt : D1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD0_lt : D0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV0_lt : V0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD1_ge : 2 ^ 63 ≤ D1 := hd
  have hD1_pos : 0 < D1 := by omega
  have hV0_eq_div : V0 = (2 ^ 128 - 1) / D1 - 2 ^ 64 := toNat_reciprocal d_hi hd
  have h_div_ge_64 : 2 ^ 64 ≤ (2 ^ 128 - 1) / D1 := by
    rw [Nat.le_div_iff_mul_le hD1_pos]
    calc 2 ^ 64 * D1 ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 ^ 128 - 1 := by norm_num
  have hV0_hi : (V0 + 2 ^ 64) * D1 ≤ 2 ^ 128 - 1 := by
    rw [hV0_eq_div, Nat.sub_add_cancel h_div_ge_64]
    exact Nat.div_mul_le_self _ _
  have hV0_lo : 2 ^ 128 - 1 < (V0 + 2 ^ 64 + 1) * D1 := by
    rw [hV0_eq_div]
    have heq : (2 ^ 128 - 1) / D1 - 2 ^ 64 + 2 ^ 64 + 1 = (2 ^ 128 - 1) / D1 + 1 := by omega
    rw [heq]
    have h := Nat.lt_mul_div_succ (2 ^ 128 - 1) hD1_pos
    have hcomm : D1 * ((2 ^ 128 - 1) / D1 + 1) = ((2 ^ 128 - 1) / D1 + 1) * D1 := by ring
    omega
  set p_raw : UInt64 := d_hi * reciprocal d_hi hd + d_lo with hp_raw_eq
  set P_low : ℕ := p_raw.toNat with hP_low_eq
  have hP_low_lt : P_low < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hP_low_mod : P_low = (D1 * V0 + D0) % 2 ^ 64 := by
    show p_raw.toNat = _
    rw [hp_raw_eq, _root_.UInt64.toNat_add, _root_.UInt64.toNat_mul]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hDVD_ub : D1 * V0 + D0 < 2 ^ 128 := by
    have h1 : V0 * D1 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
      have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
      rw [← heq]; exact hV0_hi
    have h2 : (2 : ℕ) ^ 64 * D1 ≥ 2 ^ 127 := by
      have : 2 ^ 64 * D1 ≥ 2 ^ 64 * 2 ^ 63 := Nat.mul_le_mul_left _ hD1_ge
      have heq : (2 : ℕ) ^ 64 * 2 ^ 63 = 2 ^ 127 := by norm_num
      omega
    have h3 : V0 * D1 ≤ 2 ^ 127 - 1 := by omega
    have hcomm : V0 * D1 = D1 * V0 := by ring
    omega
  set Q : ℕ := (D1 * V0 + D0) / 2 ^ 64 with hQ_eq
  have hQ_mul_add : Q * 2 ^ 64 + P_low = D1 * V0 + D0 := by
    rw [hQ_eq, hP_low_mod]
    have h := Nat.div_add_mod (D1 * V0 + D0) (2 ^ 64)
    omega
  have hQ_lt_2p64 : Q < 2 ^ 64 := by
    rw [hQ_eq]
    by_contra hh; push Not at hh
    have : 2 ^ 64 * 2 ^ 64 ≤ (D1 * V0 + D0) / 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hh
    have := Nat.div_mul_le_self (D1 * V0 + D0) (2 ^ 64)
    have : 2 ^ 128 ≤ D1 * V0 + D0 := by
      have h1 : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
      omega
    omega
  have hD1_le_2p64 : D1 ≤ 2 ^ 64 := by omega
  have hD1_mul_le : D1 * 2 ^ 64 ≤ 2 ^ 128 := by
    calc D1 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ hD1_le_2p64
      _ = 2 ^ 128 := by norm_num
  have h2p64_D1_eq : (2 ^ 64 - D1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
    rw [Nat.sub_mul]
    have : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
    have : D1 * 2 ^ 64 = 2 ^ 64 * D1 := by ring
    omega
  have hQ_le : Q ≤ 2 ^ 64 - D1 := by
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : V0 * D1 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
      have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
      rw [← heq]; exact hV0_hi
    have h2 : Q * 2 ^ 64 < (2 ^ 64 - D1 + 1) * 2 ^ 64 := by
      have hexp : (2 ^ 64 - D1 + 1) * 2 ^ 64 = (2 ^ 64 - D1) * 2 ^ 64 + 2 ^ 64 := by ring
      omega
    by_contra hh; push Not at hh
    have hge : 2 ^ 64 - D1 + 1 ≤ Q := hh
    have : (2 ^ 64 - D1 + 1) * 2 ^ 64 ≤ Q * 2 ^ 64 := Nat.mul_le_mul_right _ hge
    omega
  have hQ_ge : 2 ^ 64 - D1 - 1 ≤ Q := by
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : D1 * V0 + 2 ^ 64 * D1 + D1 ≥ 2 ^ 128 := by
      have heq : (V0 + 2 ^ 64 + 1) * D1 = V0 * D1 + 2 ^ 64 * D1 + D1 := by ring
      omega
    have hbd : 2 ^ 64 * D1 + D1 ≤ 2 ^ 128 - 1 := by
      have ha : (2 ^ 64 + 1) * D1 ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hb : (2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
      have he : (2 ^ 64 + 1) * D1 = 2 ^ 64 * D1 + D1 := by ring
      omega
    have hfact : (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 1) + 1 := by omega
      calc (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64
          = ((2 ^ 64 - D1 - 1) + 1) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh]
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    by_contra hh
    push Not at hh
    have hQlt : Q ≤ 2 ^ 64 - D1 - 2 := by omega
    have hmul : Q * 2 ^ 64 ≤ (2 ^ 64 - D1 - 2) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hQlt
    have hfact2 : (2 ^ 64 - D1 - 2) * 2 ^ 64 + 2 * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh' : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 2) + 2 := by omega
      calc (2 ^ 64 - D1 - 2) * 2 ^ 64 + 2 * 2 ^ 64
          = ((2 ^ 64 - D1 - 2) + 2) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh']
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    omega
  have hQ_int : ((Q : ℤ) * 2 ^ 64 + P_low : ℤ) = D1 * V0 + D0 := by exact_mod_cast hQ_mul_add
  -- Case B common: derive hQ_val = 2^64 - D1.
  have hP_low_lt_D0 : P_low < D0 := _root_.UInt64.lt_iff_toNat_lt.mp hA
  have hQ_val : Q = 2 ^ 64 - D1 := by
    have hcase : Q = 2 ^ 64 - D1 - 1 ∨ Q = 2 ^ 64 - D1 := by omega
    rcases hcase with h | h
    · exfalso
      have hcomm : V0 * D1 = D1 * V0 := by ring
      have hV0_lo_exp : V0 * D1 + 2 ^ 64 * D1 + D1 ≥ 2 ^ 128 := by
        have heq : (V0 + 2 ^ 64 + 1) * D1 = V0 * D1 + 2 ^ 64 * D1 + D1 := by ring
        omega
      have hprod_bd : 2 ^ 64 * D1 + D1 ≤ 2 ^ 128 := by
        have h1 : (2 ^ 64 + 1) * D1 ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h2 : (2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
        have h3 : (2 ^ 64 + 1) * D1 = 2 ^ 64 * D1 + D1 := by ring
        omega
      have hfact : (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
        have hh : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 1) + 1 := by omega
        calc (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64
            = ((2 ^ 64 - D1 - 1) + 1) * 2 ^ 64 := by ring
          _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh]
          _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
      have hsub : (2 ^ 64 - D1 - 1) * 2 ^ 64 + P_low = D1 * V0 + D0 := by
        rw [← h]; exact hQ_mul_add
      omega
    · exact h
  -- Case B1 body: V1 = V0-1, P1 = P_low - D1 + β (since P_low < D1).
  have hB2_nat : ¬ (D1 ≤ P_low) :=
    fun h => hB2 (_root_.UInt64.le_iff_toNat_le.mpr h)
  have hP_low_lt_D1' : P_low < D1 := Nat.lt_of_not_le hB2_nat
  have hA_raw : d_hi * reciprocal d_hi hd + d_lo < d_lo := hA
  have hB2_raw : ¬ (d_hi * reciprocal d_hi hd + d_lo ≥ d_hi) := hB2
  have h_red : reciprocal3By2 d_hi d_lo hd =
      (let (t_hi, t_lo) := wideMul (reciprocal d_hi hd - 1) d_lo
       let p := (p_raw - d_hi) + t_hi
       if p < t_hi then
         let v := reciprocal d_hi hd - 1 - 1
         if p > d_hi ∨ (p = d_hi ∧ t_lo ≥ d_lo) then v - 1 else v
       else reciprocal d_hi hd - 1) := by
    simp only [reciprocal3By2, ite_eq_left hA_raw, ite_eq_right hB2_raw]
    rfl
  rw [h_red]
  set v1_u : UInt64 := reciprocal d_hi hd - 1 with hv1_u_eq
  set p1_u : UInt64 := p_raw - d_hi with hp1_u_eq
  change (let (t_hi, t_lo) := wideMul v1_u d_lo
          let p := p1_u + t_hi
          if p < t_hi then
            let v := v1_u - 1
            if p > d_hi ∨ (p = d_hi ∧ t_lo ≥ d_lo) then v - 1 else v
          else v1_u).toNat = _
  have hV0_ge_1 : 1 ≤ V0 := by
    by_contra h
    have hV0_0 : V0 = 0 := by omega
    rw [hV0_0] at hV0_lo
    have ha : (0 + 2 ^ 64 + 1) * D1 ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) := by
      apply Nat.mul_le_mul_left; omega
    have h2 : (2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
    omega
  have hv1_u_toNat : v1_u.toNat = V0 - 1 := by
    rw [hv1_u_eq]
    rw [_root_.UInt64.toNat_sub_of_le]
    · show V0 - (1 : UInt64).toNat = V0 - 1; rfl
    · rw [_root_.UInt64.le_iff_toNat_le]
      show (1 : UInt64).toNat ≤ V0
      show 1 ≤ V0; omega
  have hp1_u_toNat : p1_u.toNat = P_low + 2 ^ 64 - D1 := by
    rw [hp1_u_eq, _root_.UInt64.toNat_sub]
    show (2 ^ 64 - d_hi.toNat + p_raw.toNat) % 2 ^ 64 = _
    have h : 2 ^ 64 - D1 + P_low = P_low + 2 ^ 64 - D1 := by omega
    rw [h]
    apply Nat.mod_eq_of_lt; omega
  have hKey : ((v1_u.toNat : ℤ) + 2 ^ 64) * (d_hi.toNat * 2 ^ 64 + d_lo.toNat)
        = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * p1_u.toNat + v1_u.toNat * d_lo.toNat := by
    have hV1_Z : (v1_u.toNat : ℤ) = (V0 : ℤ) - 1 := by
      rw [hv1_u_toNat]; omega
    have hP1_Z : (p1_u.toNat : ℤ) = (P_low : ℤ) + 1 * 2 ^ 64 - 1 * D1 := by
      rw [hp1_u_toNat]; push_cast; omega
    have hQk' : (Q : ℤ) + D1 = 2 ^ 64 - 1 + 1 := by
      have hc : (Q : ℤ) = (2 ^ 64 : ℤ) - D1 := by
        have h1 : ((2 ^ 64 - D1 : ℕ) : ℤ) = (2 ^ 64 : ℤ) - D1 := by push_cast; omega
        have h2 : (Q : ℤ) = ((2 ^ 64 - D1 : ℕ) : ℤ) := by exact_mod_cast hQ_val
        linarith
      linarith
    have key := recip3by2_hKey_identity (V0 : ℤ) P_low D1 D0 Q 1 1 hQ_int hQk'
    show ((v1_u.toNat : ℤ) + 2 ^ 64) * (D1 * 2 ^ 64 + D0) = _
    rw [hV1_Z, hP1_Z]
    linear_combination key
  have hP1_ge : 2 ^ 64 - d_hi.toNat ≤ p1_u.toNat := by
    show 2 ^ 64 - D1 ≤ _
    rw [hp1_u_toNat]; omega
  exact recip3by2_tail_toNat d_hi d_lo v1_u p1_u hd hP1_ge hKey

/-- Step-4 case B2 of Algorithm 6: `p_raw` overflowed `d_lo` and `p_raw ≥ d_hi`. -/
private lemma recip3by2_caseB2
    (d_hi d_lo : UInt64) (hd : 2 ^ 63 ≤ d_hi.toNat)
    (hA : d_hi * reciprocal d_hi hd + d_lo < d_lo)
    (hB2 : d_hi * reciprocal d_hi hd + d_lo ≥ d_hi) :
    (reciprocal3By2 d_hi d_lo hd).toNat =
      (2 ^ 192 - 1) / (d_hi.toNat * 2 ^ 64 + d_lo.toNat) - 2 ^ 64 := by
  set D1 : ℕ := d_hi.toNat with hD1_eq
  set D0 : ℕ := d_lo.toNat with hD0_eq
  set V0 : ℕ := (reciprocal d_hi hd).toNat with hV0_eq
  have hD1_lt : D1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD0_lt : D0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV0_lt : V0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD1_ge : 2 ^ 63 ≤ D1 := hd
  have hD1_pos : 0 < D1 := by omega
  have hV0_eq_div : V0 = (2 ^ 128 - 1) / D1 - 2 ^ 64 := toNat_reciprocal d_hi hd
  have h_div_ge_64 : 2 ^ 64 ≤ (2 ^ 128 - 1) / D1 := by
    rw [Nat.le_div_iff_mul_le hD1_pos]
    calc 2 ^ 64 * D1 ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 ^ 128 - 1 := by norm_num
  have hV0_hi : (V0 + 2 ^ 64) * D1 ≤ 2 ^ 128 - 1 := by
    rw [hV0_eq_div, Nat.sub_add_cancel h_div_ge_64]
    exact Nat.div_mul_le_self _ _
  have hV0_lo : 2 ^ 128 - 1 < (V0 + 2 ^ 64 + 1) * D1 := by
    rw [hV0_eq_div]
    have heq : (2 ^ 128 - 1) / D1 - 2 ^ 64 + 2 ^ 64 + 1 = (2 ^ 128 - 1) / D1 + 1 := by omega
    rw [heq]
    have h := Nat.lt_mul_div_succ (2 ^ 128 - 1) hD1_pos
    have hcomm : D1 * ((2 ^ 128 - 1) / D1 + 1) = ((2 ^ 128 - 1) / D1 + 1) * D1 := by ring
    omega
  set p_raw : UInt64 := d_hi * reciprocal d_hi hd + d_lo with hp_raw_eq
  set P_low : ℕ := p_raw.toNat with hP_low_eq
  have hP_low_lt : P_low < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hP_low_mod : P_low = (D1 * V0 + D0) % 2 ^ 64 := by
    show p_raw.toNat = _
    rw [hp_raw_eq, _root_.UInt64.toNat_add, _root_.UInt64.toNat_mul]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hDVD_ub : D1 * V0 + D0 < 2 ^ 128 := by
    have h1 : V0 * D1 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
      have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
      rw [← heq]; exact hV0_hi
    have h2 : (2 : ℕ) ^ 64 * D1 ≥ 2 ^ 127 := by
      have : 2 ^ 64 * D1 ≥ 2 ^ 64 * 2 ^ 63 := Nat.mul_le_mul_left _ hD1_ge
      have heq : (2 : ℕ) ^ 64 * 2 ^ 63 = 2 ^ 127 := by norm_num
      omega
    have h3 : V0 * D1 ≤ 2 ^ 127 - 1 := by omega
    have hcomm : V0 * D1 = D1 * V0 := by ring
    omega
  set Q : ℕ := (D1 * V0 + D0) / 2 ^ 64 with hQ_eq
  have hQ_mul_add : Q * 2 ^ 64 + P_low = D1 * V0 + D0 := by
    rw [hQ_eq, hP_low_mod]
    have h := Nat.div_add_mod (D1 * V0 + D0) (2 ^ 64)
    omega
  have hQ_lt_2p64 : Q < 2 ^ 64 := by
    rw [hQ_eq]
    by_contra hh; push Not at hh
    have : 2 ^ 64 * 2 ^ 64 ≤ (D1 * V0 + D0) / 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hh
    have := Nat.div_mul_le_self (D1 * V0 + D0) (2 ^ 64)
    have : 2 ^ 128 ≤ D1 * V0 + D0 := by
      have h1 : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
      omega
    omega
  have hD1_le_2p64 : D1 ≤ 2 ^ 64 := by omega
  have hD1_mul_le : D1 * 2 ^ 64 ≤ 2 ^ 128 := by
    calc D1 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ hD1_le_2p64
      _ = 2 ^ 128 := by norm_num
  have h2p64_D1_eq : (2 ^ 64 - D1) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
    rw [Nat.sub_mul]
    have : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
    have : D1 * 2 ^ 64 = 2 ^ 64 * D1 := by ring
    omega
  have hQ_le : Q ≤ 2 ^ 64 - D1 := by
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : V0 * D1 + 2 ^ 64 * D1 ≤ 2 ^ 128 - 1 := by
      have heq : (V0 + 2 ^ 64) * D1 = V0 * D1 + 2 ^ 64 * D1 := by ring
      rw [← heq]; exact hV0_hi
    have h2 : Q * 2 ^ 64 < (2 ^ 64 - D1 + 1) * 2 ^ 64 := by
      have hexp : (2 ^ 64 - D1 + 1) * 2 ^ 64 = (2 ^ 64 - D1) * 2 ^ 64 + 2 ^ 64 := by ring
      omega
    by_contra hh; push Not at hh
    have hge : 2 ^ 64 - D1 + 1 ≤ Q := hh
    have : (2 ^ 64 - D1 + 1) * 2 ^ 64 ≤ Q * 2 ^ 64 := Nat.mul_le_mul_right _ hge
    omega
  have hQ_ge : 2 ^ 64 - D1 - 1 ≤ Q := by
    have hcomm : V0 * D1 = D1 * V0 := by ring
    have h1 : D1 * V0 + 2 ^ 64 * D1 + D1 ≥ 2 ^ 128 := by
      have heq : (V0 + 2 ^ 64 + 1) * D1 = V0 * D1 + 2 ^ 64 * D1 + D1 := by ring
      omega
    have hbd : 2 ^ 64 * D1 + D1 ≤ 2 ^ 128 - 1 := by
      have ha : (2 ^ 64 + 1) * D1 ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hb : (2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
      have he : (2 ^ 64 + 1) * D1 = 2 ^ 64 * D1 + D1 := by ring
      omega
    have hfact : (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 1) + 1 := by omega
      calc (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64
          = ((2 ^ 64 - D1 - 1) + 1) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh]
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    by_contra hh
    push Not at hh
    have hQlt : Q ≤ 2 ^ 64 - D1 - 2 := by omega
    have hmul : Q * 2 ^ 64 ≤ (2 ^ 64 - D1 - 2) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hQlt
    have hfact2 : (2 ^ 64 - D1 - 2) * 2 ^ 64 + 2 * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
      have hh' : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 2) + 2 := by omega
      calc (2 ^ 64 - D1 - 2) * 2 ^ 64 + 2 * 2 ^ 64
          = ((2 ^ 64 - D1 - 2) + 2) * 2 ^ 64 := by ring
        _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh']
        _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
    omega
  have hQ_int : ((Q : ℤ) * 2 ^ 64 + P_low : ℤ) = D1 * V0 + D0 := by exact_mod_cast hQ_mul_add
  have hP_low_lt_D0 : P_low < D0 := _root_.UInt64.lt_iff_toNat_lt.mp hA
  have hQ_val : Q = 2 ^ 64 - D1 := by
    have hcase : Q = 2 ^ 64 - D1 - 1 ∨ Q = 2 ^ 64 - D1 := by omega
    rcases hcase with h | h
    · exfalso
      have hcomm : V0 * D1 = D1 * V0 := by ring
      have hV0_lo_exp : V0 * D1 + 2 ^ 64 * D1 + D1 ≥ 2 ^ 128 := by
        have heq : (V0 + 2 ^ 64 + 1) * D1 = V0 * D1 + 2 ^ 64 * D1 + D1 := by ring
        omega
      have hprod_bd : 2 ^ 64 * D1 + D1 ≤ 2 ^ 128 := by
        have h1 : (2 ^ 64 + 1) * D1 ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have h2 : (2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
        have h3 : (2 ^ 64 + 1) * D1 = 2 ^ 64 * D1 + D1 := by ring
        omega
      have hfact : (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D1 := by
        have hh : 2 ^ 64 - D1 = (2 ^ 64 - D1 - 1) + 1 := by omega
        calc (2 ^ 64 - D1 - 1) * 2 ^ 64 + 2 ^ 64
            = ((2 ^ 64 - D1 - 1) + 1) * 2 ^ 64 := by ring
          _ = (2 ^ 64 - D1) * 2 ^ 64 := by rw [← hh]
          _ = 2 ^ 128 - 2 ^ 64 * D1 := h2p64_D1_eq
      have hsub : (2 ^ 64 - D1 - 1) * 2 ^ 64 + P_low = D1 * V0 + D0 := by
        rw [← h]; exact hQ_mul_add
      omega
    · exact h
  -- Case B2 body: V1 = V0-2, P1 = P_low - 2*D1 + β.
  have hP_low_ge_D1 : D1 ≤ P_low := _root_.UInt64.le_iff_toNat_le.mp hB2
  have hA_raw : d_hi * reciprocal d_hi hd + d_lo < d_lo := hA
  have hB2_raw : d_hi * reciprocal d_hi hd + d_lo ≥ d_hi := hB2
  have h_red : reciprocal3By2 d_hi d_lo hd =
      (let (t_hi, t_lo) := wideMul (reciprocal d_hi hd - 1 - 1) d_lo
       let p := (p_raw - d_hi - d_hi) + t_hi
       if p < t_hi then
         let v := reciprocal d_hi hd - 1 - 1 - 1
         if p > d_hi ∨ (p = d_hi ∧ t_lo ≥ d_lo) then v - 1 else v
       else reciprocal d_hi hd - 1 - 1) := by
    simp only [reciprocal3By2, ite_eq_left hA_raw, ite_eq_left hB2_raw]
    rfl
  rw [h_red]
  set v1_u : UInt64 := reciprocal d_hi hd - 1 - 1 with hv1_u_eq
  set p1_u : UInt64 := p_raw - d_hi - d_hi with hp1_u_eq
  change (let (t_hi, t_lo) := wideMul v1_u d_lo
          let p := p1_u + t_hi
          if p < t_hi then
            let v := v1_u - 1
            if p > d_hi ∨ (p = d_hi ∧ t_lo ≥ d_lo) then v - 1 else v
          else v1_u).toNat = _
  have hV0_ge_2 : 2 ≤ V0 := by
    by_contra h
    have hV0_le_1 : V0 ≤ 1 := by omega
    have hDV0_le : D1 * V0 ≤ D1 := by
      have : D1 * V0 ≤ D1 * 1 := Nat.mul_le_mul_left _ hV0_le_1
      omega
    have hsum_lt : D1 * V0 + D0 < 2 * 2 ^ 64 := by omega
    have hQ_le_1 : Q ≤ 1 := by
      by_contra hh
      have hQ_ge_2 : 2 ≤ Q := by omega
      have : 2 * 2 ^ 64 ≤ Q * 2 ^ 64 := Nat.mul_le_mul_right _ hQ_ge_2
      omega
    have hD1_eq_max : D1 = 2 ^ 64 - 1 := by omega
    have hV0_not_0 : V0 ≠ 0 := by
      intro hV0_0
      rw [hV0_0, hD1_eq_max] at hV0_lo
      have : (0 + 2 ^ 64 + 1) * (2 ^ 64 - 1) = 2 ^ 128 - 1 := by norm_num
      omega
    have hV0_is_1 : V0 = 1 := by omega
    rw [hD1_eq_max] at hP_low_ge_D1
    omega
  have hv1_u_toNat : v1_u.toNat = V0 - 2 := by
    rw [hv1_u_eq]
    have h1 : (reciprocal d_hi hd - 1).toNat = V0 - 1 := by
      rw [_root_.UInt64.toNat_sub_of_le]
      · show V0 - (1 : UInt64).toNat = V0 - 1; rfl
      · rw [_root_.UInt64.le_iff_toNat_le]
        show (1 : UInt64).toNat ≤ V0
        show 1 ≤ V0
        omega
    rw [_root_.UInt64.toNat_sub_of_le]
    · show (reciprocal d_hi hd - 1).toNat - (1 : UInt64).toNat = V0 - 2
      rw [h1]; show V0 - 1 - 1 = V0 - 2; omega
    · rw [_root_.UInt64.le_iff_toNat_le, h1]
      show (1 : UInt64).toNat ≤ V0 - 1
      show 1 ≤ V0 - 1; omega
  have hp1_u_toNat : p1_u.toNat = P_low + 2 ^ 64 - 2 * D1 := by
    rw [hp1_u_eq]
    have h1 : (p_raw - d_hi).toNat = P_low - D1 := by
      rw [_root_.UInt64.toNat_sub_of_le]
      rw [_root_.UInt64.le_iff_toNat_le]
      exact hP_low_ge_D1
    rw [_root_.UInt64.toNat_sub]
    show (2 ^ 64 - d_hi.toNat + (p_raw - d_hi).toNat) % 2 ^ 64 = _
    rw [h1]
    have h2 : 2 ^ 64 - D1 + (P_low - D1) = P_low + 2 ^ 64 - 2 * D1 := by omega
    rw [h2]
    apply Nat.mod_eq_of_lt
    omega
  have hKey : ((v1_u.toNat : ℤ) + 2 ^ 64) * (d_hi.toNat * 2 ^ 64 + d_lo.toNat)
        = 2 ^ 192 - 2 ^ 128 + 2 ^ 64 * p1_u.toNat + v1_u.toNat * d_lo.toNat := by
    have hV1_Z : (v1_u.toNat : ℤ) = (V0 : ℤ) - 2 := by
      rw [hv1_u_toNat]; omega
    have hP1_Z : (p1_u.toNat : ℤ) = (P_low : ℤ) + 1 * 2 ^ 64 - 2 * D1 := by
      rw [hp1_u_toNat]; push_cast; omega
    have hQk' : (Q : ℤ) + D1 = 2 ^ 64 - 1 + 1 := by
      have hc : (Q : ℤ) = (2 ^ 64 : ℤ) - D1 := by
        have h1 : ((2 ^ 64 - D1 : ℕ) : ℤ) = (2 ^ 64 : ℤ) - D1 := by push_cast; omega
        have h2 : (Q : ℤ) = ((2 ^ 64 - D1 : ℕ) : ℤ) := by exact_mod_cast hQ_val
        linarith
      linarith
    have key := recip3by2_hKey_identity (V0 : ℤ) P_low D1 D0 Q 2 1 hQ_int hQk'
    show ((v1_u.toNat : ℤ) + 2 ^ 64) * (D1 * 2 ^ 64 + D0) = _
    rw [hV1_Z, hP1_Z]
    linear_combination key
  have hP1_ge : 2 ^ 64 - d_hi.toNat ≤ p1_u.toNat := by
    show 2 ^ 64 - D1 ≤ _
    rw [hp1_u_toNat]
    omega
  exact recip3by2_tail_toNat d_hi d_lo v1_u p1_u hd hP1_ge hKey

/-- Correctness of `reciprocal3By2` (Möller–Granlund Algorithm 6): for a normalized
128-bit divisor `d = d_hi · 2^64 + d_lo` with `2^63 ≤ d_hi.toNat`, the returned value
equals `⌊(2^192 − 1) / d⌋ − 2^64`. -/
theorem toNat_reciprocal3By2 (d_hi d_lo : UInt64) (hd : 2 ^ 63 ≤ d_hi.toNat) :
    (reciprocal3By2 d_hi d_lo hd).toNat =
      (2 ^ 192 - 1) / (d_hi.toNat * 2 ^ 64 + d_lo.toNat) - 2 ^ 64 := by
  by_cases hA : d_hi * reciprocal d_hi hd + d_lo < d_lo
  · by_cases hB2 : d_hi * reciprocal d_hi hd + d_lo ≥ d_hi
    · exact recip3by2_caseB2 d_hi d_lo hd hA hB2
    · exact recip3by2_caseB1 d_hi d_lo hd hA hB2
  · exact recip3by2_caseA d_hi d_lo hd hA

end UInt64
