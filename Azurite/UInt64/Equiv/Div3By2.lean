import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Azurite.UInt64.Div3By2
import Azurite.UInt64.Equiv.Reciprocal3By2
import Azurite.UInt64.Equiv.WideAdd
import Azurite.UInt64.Equiv.WideMul
import Azurite.UInt64.Equiv.WideSub

namespace UInt64

/-- Lower-bound half of Theorem 3 of Möller–Granlund: with the setup below,
`max(2^128 − D, q0·2^64 + 1) − 2^128 ≤ rtilde`, where
`rtilde := [u2, u1, u0] − (q1 + 1) · D`. -/
theorem div3By2_rtilde_lower_bound
    {D u2 u1 u0 q1 q0 v : ℕ}
    (hD_hi : D < 2 ^ 128)
    (hq0 : q0 < 2 ^ 64)
    (hInv_lo : (2 ^ 64 + v) * D ≤ 2 ^ 192 - 1)
    (hInv_hi : 2 ^ 192 - 1 < (2 ^ 64 + v + 1) * D)
    (hSum : q1 * 2 ^ 64 + q0 = (2 ^ 64 + v) * u2 + u1) :
    max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64 + 1) - 2 ^ 128
      ≤ (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D := by
  -- ℤ-level hypotheses.
  have hD_Z_hi : (D : ℤ) < 2 ^ 128 := by exact_mod_cast hD_hi
  have hq0_Z_lt : (q0 : ℤ) < 2 ^ 64 := by exact_mod_cast hq0
  have hu2_nn : (0 : ℤ) ≤ (u2 : ℤ) := Int.natCast_nonneg _
  have hu1_nn : (0 : ℤ) ≤ (u1 : ℤ) := Int.natCast_nonneg _
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := Int.natCast_nonneg _
  have hq0_nn : (0 : ℤ) ≤ (q0 : ℤ) := Int.natCast_nonneg _
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := Int.natCast_nonneg _
  have hInv_lo_Z : ((2 ^ 64 : ℤ) + v) * D + 1 ≤ 2 ^ 192 := by
    have h : (2 ^ 64 + v) * D + 1 ≤ 2 ^ 192 := by omega
    exact_mod_cast h
  have hInv_hi_Z : (2 ^ 192 : ℤ) ≤ ((2 ^ 64 : ℤ) + v + 1) * D := by
    have h : (2 ^ 192 : ℕ) ≤ (2 ^ 64 + v + 1) * D := by omega
    exact_mod_cast h
  have hSum_Z : (q1 : ℤ) * 2 ^ 64 + q0 = ((2 ^ 64 : ℤ) + v) * u2 + u1 := by
    exact_mod_cast hSum
  -- K := 2^192 - (2^64+v)*D lies in [1, D].
  have hK_ge : (1 : ℤ) ≤ 2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D := by linarith
  have h2_128_D_pos : (1 : ℤ) ≤ (2 ^ 128 : ℤ) - D := by linarith
  have h2_128_D_nn : (0 : ℤ) ≤ (2 ^ 128 : ℤ) - D := by linarith
  have h2_64_q0_pos : (1 : ℤ) ≤ (2 ^ 64 : ℤ) - q0 := by linarith
  have h2_64_pos : (0 : ℤ) < 2 ^ 64 := by norm_num
  -- Nonnegativity of the products appearing in the key identity.
  have hKu2 : (0 : ℤ) ≤ (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D) * u2 :=
    mul_nonneg (by linarith) hu2_nn
  have hu1_2128D : (0 : ℤ) ≤ (u1 : ℤ) * ((2 ^ 128 : ℤ) - D) :=
    mul_nonneg hu1_nn h2_128_D_nn
  have hu0_264 : (0 : ℤ) ≤ (u0 : ℤ) * 2 ^ 64 := mul_nonneg hu0_nn (by norm_num)
  have hq0D : (0 : ℤ) ≤ (q0 : ℤ) * D := mul_nonneg hq0_nn (by linarith)
  -- Key identity:
  -- rtilde * 2^64 = K · u2 + u1 · (2^128 − D) + u0 · 2^64 + q0 · D − D · 2^64,
  -- where K := 2^192 − (2^64 + v) · D.
  have key :
      ((u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D) * 2 ^ 64
        = (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D) * u2 + u1 * (2 ^ 128 - D)
          + u0 * 2 ^ 64 + q0 * D - D * 2 ^ 64 := by
    linear_combination -(D : ℤ) * hSum_Z
  -- From key, (rtilde + D) · 2^64 = K·u2 + u1·(2^128-D) + u0·2^64 + q0·D ≥ 0,
  -- so rtilde ≥ -D.
  have h_ge_neg_D : -(D : ℤ) ≤ (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D := by
    have hmul : -(D : ℤ) * 2 ^ 64
        ≤ ((u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D) * 2 ^ 64 := by
      linarith [key, hKu2, hu1_2128D, hu0_264, hq0D]
    exact le_of_mul_le_mul_right hmul h2_64_pos
  -- (rtilde + 2^128 − q0·2^64) · 2^64
  --   = K·u2 + u1·(2^128-D) + u0·2^64 + (2^64 − q0)·(2^128 − D) ≥ 1.
  have h_prod_id :
      ((u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
          + 2 ^ 128 - q0 * 2 ^ 64) * 2 ^ 64
        = (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D) * u2 + u1 * (2 ^ 128 - D)
          + u0 * 2 ^ 64 + ((2 ^ 64 : ℤ) - q0) * ((2 ^ 128 : ℤ) - D) := by
    linarith [key]
  have h_pair : (1 : ℤ) ≤ ((2 ^ 64 : ℤ) - q0) * ((2 ^ 128 : ℤ) - D) := by
    have := mul_le_mul h2_64_q0_pos h2_128_D_pos (by norm_num) (by linarith)
    linarith
  have h_prod_ge_1 :
      (1 : ℤ) ≤ ((u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
            + 2 ^ 128 - q0 * 2 ^ 64) * 2 ^ 64 := by
    linarith [h_prod_id, hKu2, hu1_2128D, hu0_264, h_pair]
  have h_ge_q0_shift :
      (q0 : ℤ) * 2 ^ 64 + 1 - 2 ^ 128
        ≤ (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D := by
    by_contra hc
    push Not at hc
    have h_neg :
        (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
            + 2 ^ 128 - q0 * 2 ^ 64 ≤ 0 := by linarith
    have h_prod_le :
        ((u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
            + 2 ^ 128 - q0 * 2 ^ 64) * 2 ^ 64 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h_neg (by linarith)
    linarith [h_prod_ge_1]
  by_cases h : (2 ^ 128 : ℤ) - D ≤ (q0 : ℤ) * 2 ^ 64 + 1
  · rw [max_eq_right h]; linarith
  · push Not at h; rw [max_eq_left (le_of_lt h)]; linarith

/-- Upper-bound Case 1 for Theorem 3: when `u2 < d1` (where `D = d1 · 2^64 + d0`),
`rtilde < max(2^128 − D, q0·2^64)`. -/
theorem div3By2_rtilde_upper_case_lt_d1
    {D u2 u1 u0 q1 q0 v d1 d0 : ℕ}
    (hD_hi : D < 2 ^ 128)
    (hu1 : u1 < 2 ^ 64)
    (hu0 : u0 < 2 ^ 64)
    (hq0 : q0 < 2 ^ 64)
    (hInv_lo : (2 ^ 64 + v) * D ≤ 2 ^ 192 - 1)
    (hInv_hi : 2 ^ 192 - 1 < (2 ^ 64 + v + 1) * D)
    (hSum : q1 * 2 ^ 64 + q0 = (2 ^ 64 + v) * u2 + u1)
    (hD_split : D = d1 * 2 ^ 64 + d0)
    (hd0 : d0 < 2 ^ 64)
    (hu2_lt_d1 : u2 < d1) :
    (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
      < max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) := by
  have hD_Z_hi : (D : ℤ) < 2 ^ 128 := by exact_mod_cast hD_hi
  have hu1_Z_lt : (u1 : ℤ) < 2 ^ 64 := by exact_mod_cast hu1
  have hu0_Z_lt : (u0 : ℤ) < 2 ^ 64 := by exact_mod_cast hu0
  have hq0_Z_lt : (q0 : ℤ) < 2 ^ 64 := by exact_mod_cast hq0
  have hu2_nn : (0 : ℤ) ≤ (u2 : ℤ) := Int.natCast_nonneg _
  have hu1_nn : (0 : ℤ) ≤ (u1 : ℤ) := Int.natCast_nonneg _
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := Int.natCast_nonneg _
  have hq0_nn : (0 : ℤ) ≤ (q0 : ℤ) := Int.natCast_nonneg _
  have hd0_nn : (0 : ℤ) ≤ (d0 : ℤ) := Int.natCast_nonneg _
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := Int.natCast_nonneg _
  have hd0_Z_lt : (d0 : ℤ) < 2 ^ 64 := by exact_mod_cast hd0
  have hu2_lt_d1_Z : (u2 : ℤ) + 1 ≤ d1 := by exact_mod_cast hu2_lt_d1
  have hD_split_Z : (D : ℤ) = (d1 : ℤ) * 2 ^ 64 + d0 := by exact_mod_cast hD_split
  have hInv_lo_Z : ((2 ^ 64 : ℤ) + v) * D + 1 ≤ 2 ^ 192 := by
    have h : (2 ^ 64 + v) * D + 1 ≤ 2 ^ 192 := by omega
    exact_mod_cast h
  have hInv_hi_Z : (2 ^ 192 : ℤ) ≤ ((2 ^ 64 : ℤ) + v + 1) * D := by
    have h : (2 ^ 192 : ℕ) ≤ (2 ^ 64 + v + 1) * D := by omega
    exact_mod_cast h
  have hSum_Z : (q1 : ℤ) * 2 ^ 64 + q0 = ((2 ^ 64 : ℤ) + v) * u2 + u1 := by
    exact_mod_cast hSum
  have hK_le : (2 : ℤ) ^ 192 - ((2 ^ 64 : ℤ) + v) * D ≤ D := by linarith
  have hK_nn : (0 : ℤ) ≤ 2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D := by linarith
  have h2_128_D_nn : (0 : ℤ) ≤ (2 ^ 128 : ℤ) - D := by linarith
  have h2_128_pos : (0 : ℤ) < 2 ^ 128 := by norm_num
  -- Key identity (as in the lower bound proof).
  have key :
      ((u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D) * 2 ^ 64
        = (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D) * u2 + u1 * (2 ^ 128 - D)
          + u0 * 2 ^ 64 + q0 * D - D * 2 ^ 64 := by
    linear_combination -(D : ℤ) * hSum_Z
  -- Define rt for brevity.
  set rt : ℤ := (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D with hrt_def
  -- Bounds used for nonnegativity.
  have hu2_d1 : (u2 : ℤ) ≤ d1 - 1 := by linarith
  have hu1_ub : (u1 : ℤ) ≤ 2 ^ 64 - 1 := by linarith
  have hDmK_nn : (0 : ℤ) ≤ (D : ℤ) - (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D) := by linarith
  have hd1_u2_nn : (0 : ℤ) ≤ (d1 : ℤ) - 1 - u2 := by linarith
  have h2_64_u1_nn : (0 : ℤ) ≤ (2 ^ 64 : ℤ) - 1 - u1 := by linarith
  have h2_64_u0_pos : (1 : ℤ) ≤ (2 ^ 64 : ℤ) - u0 := by linarith
  have hP1 : (0 : ℤ) ≤ ((D : ℤ) - (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D)) * u2 :=
    mul_nonneg hDmK_nn hu2_nn
  have hP2 : (0 : ℤ) ≤ (D : ℤ) * ((d1 : ℤ) - 1 - u2) :=
    mul_nonneg hD_Z_nn hd1_u2_nn
  have hP3 : (0 : ℤ) ≤ ((2 ^ 64 : ℤ) - 1 - u1) * ((2 ^ 128 : ℤ) - D) :=
    mul_nonneg h2_64_u1_nn h2_128_D_nn
  have hP4 : (1 : ℤ) ≤ ((2 ^ 64 : ℤ) - u0) * 2 ^ 128 := by
    have := mul_le_mul_of_nonneg_right h2_64_u0_pos (by norm_num : (0 : ℤ) ≤ 2 ^ 128)
    linarith
  have hd0D_nn : (0 : ℤ) ≤ (d0 : ℤ) * D := mul_nonneg hd0_nn hD_Z_nn
  -- Set c = max(2^128-D, q0*2^64).
  set c : ℤ := max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) with hc_def
  have hc_ge_A : ((2 ^ 128 : ℤ) - D) ≤ c := le_max_left _ _
  have hc_ge_B : ((q0 : ℤ) * 2 ^ 64) ≤ c := le_max_right _ _
  have hP5 : (0 : ℤ) ≤ (c - ((2 ^ 128 : ℤ) - D)) * ((2 ^ 128 : ℤ) - D) := by
    apply mul_nonneg _ h2_128_D_nn; linarith
  have hP6 : (0 : ℤ) ≤ (c - (q0 : ℤ) * 2 ^ 64) * D := by
    apply mul_nonneg _ hD_Z_nn; linarith
  -- Algebraic identity: c*2^128 - rt*2^128 decomposes into a sum of nonneg terms.
  have hdiff :
      c * 2 ^ 128 - rt * 2 ^ 128
        = ((D : ℤ) - (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D)) * u2 * 2 ^ 64
          + D * ((d1 : ℤ) - 1 - u2) * 2 ^ 64
          + ((2 ^ 64 : ℤ) - 1 - u1) * ((2 ^ 128 : ℤ) - D) * 2 ^ 64
          + ((2 ^ 64 : ℤ) - u0) * 2 ^ 128
          + (c - ((2 ^ 128 : ℤ) - D)) * ((2 ^ 128 : ℤ) - D)
          + (c - (q0 : ℤ) * 2 ^ 64) * D
          + (d0 : ℤ) * D := by
    linear_combination (D : ℤ) * 2 ^ 64 * hSum_Z + (D : ℤ) * hD_split_Z
  have h_mul_lt : rt * 2 ^ 128 < c * 2 ^ 128 := by
    have hP1' := mul_le_mul_of_nonneg_right hP1 (by norm_num : (0 : ℤ) ≤ 2 ^ 64)
    have hP2' := mul_le_mul_of_nonneg_right hP2 (by norm_num : (0 : ℤ) ≤ 2 ^ 64)
    have hP3' := mul_le_mul_of_nonneg_right hP3 (by norm_num : (0 : ℤ) ≤ 2 ^ 64)
    linarith [hdiff, hP1', hP2', hP3', hP4, hP5, hP6, hd0D_nn]
  exact lt_of_mul_lt_mul_right h_mul_lt (by norm_num : (0 : ℤ) ≤ 2 ^ 128)

/-- Upper-bound Case 2 for Theorem 3: when `u2 = d1` and `u1 < d0` (so `[u2,u1] < D`)
and the "non-borderline" assumption `D + 2^64 ≤ 2^128` (equivalently `D ≤ 2^64·(2^64−1)`),
`rtilde < max(2^128 − D, q0·2^64)`. -/
theorem div3By2_rtilde_upper_case_eq_d1
    {D u2 u1 u0 q1 q0 v d1 d0 : ℕ}
    (hD_hi : D < 2 ^ 128)
    (hu0 : u0 < 2 ^ 64)
    (hq0 : q0 < 2 ^ 64)
    (hInv_lo : (2 ^ 64 + v) * D ≤ 2 ^ 192 - 1)
    (hInv_hi : 2 ^ 192 - 1 < (2 ^ 64 + v + 1) * D)
    (hSum : q1 * 2 ^ 64 + q0 = (2 ^ 64 + v) * u2 + u1)
    (hD_split : D = d1 * 2 ^ 64 + d0)
    (hd0 : d0 < 2 ^ 64)
    (hu2_eq_d1 : u2 = d1)
    (hu1_lt_d0 : u1 < d0)
    (hD_small : D + 2 ^ 64 ≤ 2 ^ 128) :
    (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
      < max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) := by
  have hD_Z_hi : (D : ℤ) < 2 ^ 128 := by exact_mod_cast hD_hi
  have hu0_Z_lt : (u0 : ℤ) < 2 ^ 64 := by exact_mod_cast hu0
  have hq0_Z_lt : (q0 : ℤ) < 2 ^ 64 := by exact_mod_cast hq0
  have hu2_nn : (0 : ℤ) ≤ (u2 : ℤ) := Int.natCast_nonneg _
  have hu1_nn : (0 : ℤ) ≤ (u1 : ℤ) := Int.natCast_nonneg _
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := Int.natCast_nonneg _
  have hq0_nn : (0 : ℤ) ≤ (q0 : ℤ) := Int.natCast_nonneg _
  have hd0_nn : (0 : ℤ) ≤ (d0 : ℤ) := Int.natCast_nonneg _
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := Int.natCast_nonneg _
  have hd0_Z_lt : (d0 : ℤ) < 2 ^ 64 := by exact_mod_cast hd0
  have hu1_lt_d0_Z : (u1 : ℤ) + 1 ≤ d0 := by exact_mod_cast hu1_lt_d0
  have hu2_eq_d1_Z : (u2 : ℤ) = d1 := by exact_mod_cast hu2_eq_d1
  have hD_split_Z : (D : ℤ) = (d1 : ℤ) * 2 ^ 64 + d0 := by exact_mod_cast hD_split
  have hD_small_Z : (D : ℤ) + 2 ^ 64 ≤ 2 ^ 128 := by exact_mod_cast hD_small
  have hInv_lo_Z : ((2 ^ 64 : ℤ) + v) * D + 1 ≤ 2 ^ 192 := by
    have h : (2 ^ 64 + v) * D + 1 ≤ 2 ^ 192 := by omega
    exact_mod_cast h
  have hInv_hi_Z : (2 ^ 192 : ℤ) ≤ ((2 ^ 64 : ℤ) + v + 1) * D := by
    have h : (2 ^ 192 : ℕ) ≤ (2 ^ 64 + v + 1) * D := by omega
    exact_mod_cast h
  have hSum_Z : (q1 : ℤ) * 2 ^ 64 + q0 = ((2 ^ 64 : ℤ) + v) * u2 + u1 := by
    exact_mod_cast hSum
  have hK_le : (2 : ℤ) ^ 192 - ((2 ^ 64 : ℤ) + v) * D ≤ D := by linarith
  have h2_128_D_nn : (0 : ℤ) ≤ (2 ^ 128 : ℤ) - D := by linarith
  -- (2^64+1)*D ≤ 2^192 from D + 2^64 ≤ 2^128.
  -- Proof: (2^64+1)*D = 2^64*D + D ≤ 2^64*D + (2^128 - 2^64) = 2^64*(D + 2^64) - 2^64*2^64 + 2^128
  --       = 2^64*(D+2^64) ≤ 2^64*2^128 = 2^192. Wait that gives equality if D+2^64=2^128.
  have h_D_2_192 : ((2 ^ 64 : ℤ) + 1) * D ≤ 2 ^ 192 := by
    have h1 : ((2 ^ 64 : ℤ) + 1) * D = 2 ^ 64 * D + D := by ring
    have h2 : (2 ^ 64 : ℤ) * D ≤ 2 ^ 64 * (2 ^ 128 - 2 ^ 64) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have h3 : (2 ^ 64 : ℤ) * (2 ^ 128 - 2 ^ 64) = 2 ^ 192 - 2 ^ 128 := by ring
    linarith
  -- Define rt.
  set rt : ℤ := (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D with hrt_def
  -- Nonneg factors.
  have hDmK_nn : (0 : ℤ) ≤ (D : ℤ) - (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D) := by linarith
  have hd0_u1_nn : (0 : ℤ) ≤ (d0 : ℤ) - 1 - u1 := by linarith
  have h2_64_d0_nn : (0 : ℤ) ≤ (2 ^ 64 : ℤ) - d0 := by linarith
  have h2_64_u0_pos : (1 : ℤ) ≤ (2 ^ 64 : ℤ) - u0 := by linarith
  have h_2192_D_nn : (0 : ℤ) ≤ (2 ^ 192 : ℤ) - ((2 ^ 64 : ℤ) + 1) * D := by linarith
  -- Named products.
  have hP1 : (0 : ℤ) ≤ ((D : ℤ) - (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D)) * u2 :=
    mul_nonneg hDmK_nn hu2_nn
  have hP3 : (0 : ℤ) ≤ ((d0 : ℤ) - 1 - u1) * ((2 ^ 128 : ℤ) - D) :=
    mul_nonneg hd0_u1_nn h2_128_D_nn
  have hP4 : (1 : ℤ) ≤ ((2 ^ 64 : ℤ) - u0) * 2 ^ 128 := by
    have := mul_le_mul_of_nonneg_right h2_64_u0_pos (by norm_num : (0 : ℤ) ≤ 2 ^ 128)
    linarith
  have hP7 : (0 : ℤ) ≤ ((2 ^ 64 : ℤ) - d0) * ((2 ^ 192 : ℤ) - ((2 ^ 64 : ℤ) + 1) * D) :=
    mul_nonneg h2_64_d0_nn h_2192_D_nn
  -- Set c = max(2^128-D, q0*2^64).
  set c : ℤ := max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) with hc_def
  have hc_ge_A : ((2 ^ 128 : ℤ) - D) ≤ c := le_max_left _ _
  have hc_ge_B : ((q0 : ℤ) * 2 ^ 64) ≤ c := le_max_right _ _
  have hP5 : (0 : ℤ) ≤ (c - ((2 ^ 128 : ℤ) - D)) * ((2 ^ 128 : ℤ) - D) := by
    apply mul_nonneg _ h2_128_D_nn; linarith
  have hP6 : (0 : ℤ) ≤ (c - (q0 : ℤ) * 2 ^ 64) * D := by
    apply mul_nonneg _ hD_Z_nn; linarith
  -- Algebraic identity.
  have hdiff :
      c * 2 ^ 128 - rt * 2 ^ 128
        = ((D : ℤ) - (2 ^ 192 - ((2 ^ 64 : ℤ) + v) * D)) * u2 * 2 ^ 64
          + ((d0 : ℤ) - 1 - u1) * ((2 ^ 128 : ℤ) - D) * 2 ^ 64
          + ((2 ^ 64 : ℤ) - u0) * 2 ^ 128
          + (c - ((2 ^ 128 : ℤ) - D)) * ((2 ^ 128 : ℤ) - D)
          + (c - (q0 : ℤ) * 2 ^ 64) * D
          + ((2 ^ 64 : ℤ) - d0) * ((2 ^ 192 : ℤ) - ((2 ^ 64 : ℤ) + 1) * D) := by
    linear_combination (D : ℤ) * 2 ^ 64 * hSum_Z + (D : ℤ) * hD_split_Z
      - (D : ℤ) * 2 ^ 64 * hu2_eq_d1_Z
  have h_mul_lt : rt * 2 ^ 128 < c * 2 ^ 128 := by
    have hP1' := mul_le_mul_of_nonneg_right hP1 (by norm_num : (0 : ℤ) ≤ 2 ^ 64)
    have hP3' := mul_le_mul_of_nonneg_right hP3 (by norm_num : (0 : ℤ) ≤ 2 ^ 64)
    linarith [hdiff, hP1', hP3', hP4, hP5, hP6, hP7]
  exact lt_of_mul_lt_mul_right h_mul_lt (by norm_num : (0 : ℤ) ≤ 2 ^ 128)

/-- Upper-bound Case 3 (borderline) for Theorem 3: when `u2 = d1` and
`D > 2^128 − 2^64`, we must have `v = 0`, `d1 = u2 = 2^64 − 1`, `q1 = u2`,
and `rtilde = (u1 − d0)·2^64 + u0 < 0 ≤ max(2^128 − D, q0·2^64)`. -/
theorem div3By2_rtilde_upper_case_borderline
    {D u2 u1 u0 q1 q0 v d1 d0 : ℕ}
    (hD_hi : D < 2 ^ 128)
    (hu0 : u0 < 2 ^ 64)
    (hq0 : q0 < 2 ^ 64)
    (hInv_lo : (2 ^ 64 + v) * D ≤ 2 ^ 192 - 1)
    (hSum : q1 * 2 ^ 64 + q0 = (2 ^ 64 + v) * u2 + u1)
    (hD_split : D = d1 * 2 ^ 64 + d0)
    (hd0 : d0 < 2 ^ 64)
    (hu1 : u1 < 2 ^ 64)
    (hu2_eq_d1 : u2 = d1)
    (hu1_lt_d0 : u1 < d0)
    (hD_large : 2 ^ 128 - 2 ^ 64 < D) :
    (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
      < max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) := by
  -- Derive v = 0 using hInv_lo and D > 2^128 - 2^64.
  have hv_zero : v = 0 := by
    by_contra hv
    have hv_pos : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr hv
    have h1 : (2 ^ 64 + 1) * D ≤ (2 ^ 64 + v) * D :=
      Nat.mul_le_mul_right _ (by omega)
    have hD_lb : 2 ^ 128 - 2 ^ 64 + 1 ≤ D := by omega
    have h2 : (2 ^ 64 + 1) * (2 ^ 128 - 2 ^ 64 + 1) ≤ (2 ^ 64 + 1) * D :=
      Nat.mul_le_mul_left _ hD_lb
    have h3 : (2 ^ 64 + 1) * (2 ^ 128 - 2 ^ 64 + 1) = 2 ^ 192 + 1 := by norm_num
    omega
  -- With v=0, d1 = 2^64 - 1 and d0 ≥ 1.
  have hd1_eq : d1 = 2 ^ 64 - 1 := by
    have h1 : d1 * 2 ^ 64 + d0 > 2 ^ 128 - 2 ^ 64 := by omega
    have h2 : d1 < 2 ^ 64 := by
      by_contra h
      push Not at h
      have hmul : 2 ^ 64 * 2 ^ 64 ≤ d1 * 2 ^ 64 := Nat.mul_le_mul_right _ h
      have heq : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
      omega
    have h3 : d1 ≥ 2 ^ 64 - 1 := by
      by_contra h
      push Not at h
      have hd1_lt : d1 ≤ 2 ^ 64 - 2 := by omega
      have : d1 * 2 ^ 64 ≤ (2 ^ 64 - 2) * 2 ^ 64 := Nat.mul_le_mul_right _ hd1_lt
      have hexp : (2 ^ 64 - 2) * 2 ^ 64 = 2 ^ 128 - 2 * 2 ^ 64 := by
        have : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
        omega
      omega
    omega
  -- q1 = 2^64 - 1 = u2.
  have hu2_val : u2 = 2 ^ 64 - 1 := by rw [hu2_eq_d1, hd1_eq]
  have hq1_eq : q1 = 2 ^ 64 - 1 := by
    have h_sum_val : q1 * 2 ^ 64 + q0 = 2 ^ 64 * (2 ^ 64 - 1) + u1 := by
      rw [hSum, hv_zero, hu2_val]; ring
    have : 2 ^ 64 * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 64 := by
      have : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
      omega
    omega
  -- Integer casts.
  have hD_split_Z : (D : ℤ) = (d1 : ℤ) * 2 ^ 64 + d0 := by exact_mod_cast hD_split
  have hu2_eq_d1_Z : (u2 : ℤ) = d1 := by exact_mod_cast hu2_eq_d1
  have hq1_eq_u2_Z : (q1 : ℤ) = u2 := by
    have : q1 = u2 := by rw [hq1_eq, hu2_val]
    exact_mod_cast this
  have hu1_lt_d0_Z : (u1 : ℤ) + 1 ≤ d0 := by exact_mod_cast hu1_lt_d0
  have hu0_Z_lt : (u0 : ℤ) < 2 ^ 64 := by exact_mod_cast hu0
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := Int.natCast_nonneg _
  have hD_Z_hi : (D : ℤ) < 2 ^ 128 := by exact_mod_cast hD_hi
  -- Compute rtilde = (u1 - d0)*2^64 + u0. Uses d1 = u2 = 2^64 - 1.
  have h_rtilde_eq :
      (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
        = ((u1 : ℤ) - d0) * 2 ^ 64 + u0 := by
    have h1 : (1 : ℕ) ≤ 2 ^ 64 := by norm_num
    have hu2_Z : (u2 : ℤ) = (2 : ℤ) ^ 64 - 1 := by
      rw [hu2_val]; push_cast [Nat.cast_sub h1]
    have hq1_Z : (q1 : ℤ) = (2 : ℤ) ^ 64 - 1 := by
      rw [hq1_eq]; push_cast [Nat.cast_sub h1]
    have hd1_Z : (d1 : ℤ) = (2 : ℤ) ^ 64 - 1 := by
      rw [hd1_eq]; push_cast [Nat.cast_sub h1]
    rw [hu2_Z, hq1_Z, hD_split_Z, hd1_Z]
    ring
  -- Show rtilde < 0.
  have h_rtilde_neg : ((u1 : ℤ) - d0) * 2 ^ 64 + u0 < 0 := by
    have h1 : (u1 : ℤ) - d0 ≤ -1 := by linarith
    have h2 : ((u1 : ℤ) - d0) * 2 ^ 64 ≤ -1 * 2 ^ 64 := by
      apply mul_le_mul_of_nonneg_right h1 (by norm_num)
    linarith
  -- c ≥ 2^128 - D ≥ 1 > 0.
  have h2_128_D_pos : (1 : ℤ) ≤ (2 ^ 128 : ℤ) - D := by linarith
  have hc_ge : (0 : ℤ) ≤ max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) := by
    have : ((2 ^ 128 : ℤ) - D) ≤ max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) :=
      le_max_left _ _
    linarith
  rw [h_rtilde_eq]
  linarith

/-- Theorem 3 of Möller–Granlund: given a normalized 128-bit divisor
`D = d1 · 2^64 + d0` (`2^127 ≤ D < 2^128`), a 192-bit dividend `[u2, u1, u0]`
with `[u2, u1] < D`, and a 64-bit reciprocal `v` characterized by
`(2^64 + v) · D ≤ 2^192 − 1 < (2^64 + v + 1) · D`, let `[q1, q0]` be the
two-word number `(2^64 + v) · u2 + u1`. Then the candidate remainder
`rtilde := [u2, u1, u0] − (q1 + 1) · D` satisfies the tight bound
`max(2^128 − D, q0·2^64 + 1) − 2^128 ≤ rtilde < max(2^128 − D, q0·2^64)`. -/
theorem div3By2_rtilde_bounds
    {D u2 u1 u0 q1 q0 v : ℕ}
    (hD_lo : 2 ^ 127 ≤ D) (hD_hi : D < 2 ^ 128)
    (hu1 : u1 < 2 ^ 64) (hu0 : u0 < 2 ^ 64)
    (hq0 : q0 < 2 ^ 64)
    (hUD : u2 * 2 ^ 64 + u1 < D)
    (hInv_lo : (2 ^ 64 + v) * D ≤ 2 ^ 192 - 1)
    (hInv_hi : 2 ^ 192 - 1 < (2 ^ 64 + v + 1) * D)
    (hSum : q1 * 2 ^ 64 + q0 = (2 ^ 64 + v) * u2 + u1) :
    max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64 + 1) - 2 ^ 128
      ≤ (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
    ∧ (u2 : ℤ) * 2 ^ 128 + u1 * 2 ^ 64 + u0 - ((q1 : ℤ) + 1) * D
        < max ((2 ^ 128 : ℤ) - D) ((q0 : ℤ) * 2 ^ 64) := by
  refine ⟨div3By2_rtilde_lower_bound hD_hi hq0 hInv_lo hInv_hi hSum, ?_⟩
  -- Upper bound: case-split on u2 vs d1 := D / 2^64.
  set d1 : ℕ := D / 2 ^ 64 with hd1_def
  set d0 : ℕ := D % 2 ^ 64 with hd0_def
  have hpow_pos : 0 < (2 : ℕ) ^ 64 := by norm_num
  have hD_split : D = d1 * 2 ^ 64 + d0 := by
    rw [hd1_def, hd0_def, Nat.div_add_mod']
  have hd0 : d0 < 2 ^ 64 := Nat.mod_lt _ hpow_pos
  by_cases hcase1 : u2 < d1
  · exact div3By2_rtilde_upper_case_lt_d1 hD_hi hu1 hu0 hq0 hInv_lo hInv_hi hSum
      hD_split hd0 hcase1
  · push Not at hcase1
    have hu2_eq_d1 : u2 = d1 := by
      by_contra hne
      have hu2_gt : d1 < u2 := lt_of_le_of_ne hcase1 (Ne.symm hne)
      have h1 : d1 + 1 ≤ u2 := hu2_gt
      have h2 : (d1 + 1) * 2 ^ 64 ≤ u2 * 2 ^ 64 := Nat.mul_le_mul_right _ h1
      have h3 : (d1 + 1) * 2 ^ 64 = d1 * 2 ^ 64 + 2 ^ 64 := by ring
      have : u2 * 2 ^ 64 + u1 < d1 * 2 ^ 64 + d0 := by rw [← hD_split]; exact hUD
      omega
    have hu1_lt_d0 : u1 < d0 := by
      have h := hUD
      rw [hu2_eq_d1, hD_split] at h
      omega
    by_cases hcase2 : D + 2 ^ 64 ≤ 2 ^ 128
    · exact div3By2_rtilde_upper_case_eq_d1 hD_hi hu0 hq0 hInv_lo hInv_hi hSum
        hD_split hd0 hu2_eq_d1 hu1_lt_d0 hcase2
    · push Not at hcase2
      have hD_large : 2 ^ 128 - 2 ^ 64 < D := by omega
      exact div3By2_rtilde_upper_case_borderline hD_hi hu0 hq0 hInv_lo hSum
        hD_split hd0 hu1 hu2_eq_d1 hu1_lt_d0 hD_large

/-- Under the invariants of Algorithm 5 the 128-bit sum `(2^64 + v) · u2 + u1`
does not overflow `2^128`. -/
private lemma div3By2_sum_lt {D d1 d0 u2 u1 v : ℕ}
    (hD_split : D = d1 * 2 ^ 64 + d0)
    (hd0 : d0 < 2 ^ 64)
    (hu1 : u1 < 2 ^ 64)
    (hUD : u2 * 2 ^ 64 + u1 < D)
    (hInv_lo : (2 ^ 64 + v) * D ≤ 2 ^ 192 - 1) :
    (2 ^ 64 + v) * u2 + u1 < 2 ^ 128 := by
  have hu2_le : u2 ≤ d1 := by
    by_contra hne
    push Not at hne
    have h1 : d1 + 1 ≤ u2 := hne
    have h2 : (d1 + 1) * 2 ^ 64 ≤ u2 * 2 ^ 64 := Nat.mul_le_mul_right _ h1
    have h3 : (d1 + 1) * 2 ^ 64 = d1 * 2 ^ 64 + 2 ^ 64 := by ring
    have h4 : u2 * 2 ^ 64 + u1 < d1 * 2 ^ 64 + d0 := by rw [← hD_split]; exact hUD
    omega
  -- Multiply to work modulo 2^128 * 2^64 = 2^192.
  have h_exp : (2 : ℕ) ^ 192 = 2 ^ 128 * 2 ^ 64 := by norm_num
  -- (2^64 + v) * D = (2^64+v)*d1*2^64 + (2^64+v)*d0.
  have hDeq : (2 ^ 64 + v) * D = (2 ^ 64 + v) * d1 * 2 ^ 64 + (2 ^ 64 + v) * d0 := by
    rw [hD_split]; ring
  by_cases hcase : u2 < d1
  · -- (2^64+v)*u2 + (2^64+v) ≤ (2^64+v)*d1 ≤ 2^128 - 1 (since (2^64+v)*d1*2^64 ≤ 2^192-1).
    have h1 : u2 + 1 ≤ d1 := hcase
    have h2 : (2 ^ 64 + v) * (u2 + 1) ≤ (2 ^ 64 + v) * d1 := Nat.mul_le_mul_left _ h1
    have h_wide : (2 ^ 64 + v) * d1 * 2 ^ 64 ≤ 2 ^ 192 - 1 := by
      have := hInv_lo
      have h_nn : 0 ≤ (2 ^ 64 + v) * d0 := Nat.zero_le _
      omega
    have h_d1_ub : (2 ^ 64 + v) * d1 ≤ 2 ^ 128 - 1 := by
      by_contra hge
      push Not at hge
      have : 2 ^ 128 ≤ (2 ^ 64 + v) * d1 := by omega
      have : 2 ^ 128 * 2 ^ 64 ≤ (2 ^ 64 + v) * d1 * 2 ^ 64 := Nat.mul_le_mul_right _ this
      omega
    have h3 : (2 ^ 64 + v) * (u2 + 1) = (2 ^ 64 + v) * u2 + (2 ^ 64 + v) := by ring
    have h4 : (2 ^ 64 + v) ≥ 2 ^ 64 := Nat.le_add_right _ _
    omega
  · push Not at hcase
    have hu2_eq : u2 = d1 := by omega
    have hu1_lt : u1 < d0 := by rw [hu2_eq, hD_split] at hUD; omega
    rw [hu2_eq]
    -- Want: (2^64+v)*d1 + u1 < 2^128. Contradiction argument via multiply by 2^64.
    by_contra hne
    push Not at hne
    have hge : 2 ^ 128 ≤ (2 ^ 64 + v) * d1 + u1 := hne
    have hmul : 2 ^ 128 * 2 ^ 64 ≤ ((2 ^ 64 + v) * d1 + u1) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ hge
    have hexp_lhs : ((2 ^ 64 + v) * d1 + u1) * 2 ^ 64
        = (2 ^ 64 + v) * d1 * 2 ^ 64 + u1 * 2 ^ 64 := by ring
    -- (2^64+v)*d1*2^64 + (2^64+v)*d0 ≤ 2^192-1, and u1*2^64 + 2^64 ≤ (2^64+v)*d0.
    have h_u1_p1 : u1 + 1 ≤ d0 := hu1_lt
    have h_u1m : (u1 + 1) * 2 ^ 64 ≤ d0 * 2 ^ 64 := Nat.mul_le_mul_right _ h_u1_p1
    have h_d0_v : d0 * 2 ^ 64 ≤ (2 ^ 64 + v) * d0 := by
      have : 2 ^ 64 * d0 ≤ (2 ^ 64 + v) * d0 :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      linarith [Nat.mul_comm d0 (2 ^ 64)]
    have hexp_u : (u1 + 1) * 2 ^ 64 = u1 * 2 ^ 64 + 2 ^ 64 := by ring
    omega

/-- A 128-bit ≥ comparison expressed as the UInt64 pair test. -/
private lemma div3By2_h128_ge_of_test (a1 a0 b1 b0 : UInt64) :
    (a1 > b1 ∨ (a1 = b1 ∧ a0 ≥ b0)) →
      b1.toNat * 2 ^ 64 + b0.toNat ≤ a1.toNat * 2 ^ 64 + a0.toNat := by
  have ha0 : a0.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hb0 : b0.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  rintro (h | ⟨h1, h2⟩)
  · have hlt : b1.toNat < a1.toNat := _root_.UInt64.lt_iff_toNat_lt.mp h
    have : b1.toNat + 1 ≤ a1.toNat := hlt
    have : (b1.toNat + 1) * 2 ^ 64 ≤ a1.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ this
    have : b1.toNat * 2 ^ 64 + 2 ^ 64 ≤ a1.toNat * 2 ^ 64 := by
      have heq : (b1.toNat + 1) * 2 ^ 64 = b1.toNat * 2 ^ 64 + 2 ^ 64 := by ring
      omega
    omega
  · have heq : a1.toNat = b1.toNat := by rw [h1]
    have hle : b0.toNat ≤ a0.toNat := _root_.UInt64.le_iff_toNat_le.mp h2
    omega

private lemma div3By2_h_test_of_128_ge (a1 a0 b1 b0 : UInt64) :
    b1.toNat * 2 ^ 64 + b0.toNat ≤ a1.toNat * 2 ^ 64 + a0.toNat →
      (a1 > b1 ∨ (a1 = b1 ∧ a0 ≥ b0)) := by
  intro hle
  have ha0 : a0.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hb0 : b0.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  by_cases hlt : b1.toNat < a1.toNat
  · exact Or.inl (_root_.UInt64.lt_iff_toNat_lt.mpr hlt)
  · push Not at hlt
    have heq_toNat : a1.toNat = b1.toNat := by
      by_contra hne
      have h1 : a1.toNat < b1.toNat := lt_of_le_of_ne hlt hne
      have h2 : a1.toNat + 1 ≤ b1.toNat := h1
      have h3 : (a1.toNat + 1) * 2 ^ 64 ≤ b1.toNat * 2 ^ 64 :=
        Nat.mul_le_mul_right _ h2
      have h4 : (a1.toNat + 1) * 2 ^ 64 = a1.toNat * 2 ^ 64 + 2 ^ 64 := by ring
      omega
    have heq : a1 = b1 := _root_.UInt64.eq_of_toNat_eq heq_toNat
    have hb0_le_a0 : b0.toNat ≤ a0.toNat := by
      have : b1.toNat * 2 ^ 64 = a1.toNat * 2 ^ 64 := by rw [heq_toNat]
      omega
    exact Or.inr ⟨heq, _root_.UInt64.le_iff_toNat_le.mpr hb0_le_a0⟩

/-- Given n : ℕ and z : ℤ representing the same residue class mod 2^128 — with
`n < 2^128` and `-(2^128) ≤ z < 2^128` — and `n - z = K * 2^128`, the integer `n`
is the canonical representative: it equals `z` when `z ≥ 0`, and `z + 2^128`
when `z < 0`. This abstracts the K = 0 / K = 1 case analysis used inside
`toNat_div3By2`. -/
private lemma div3By2_rep_of_mod {n : ℕ} {z : ℤ} {K : ℤ}
    (hn_lt : (n : ℤ) < 2 ^ 128) (hz_lt : z < 2 ^ 128)
    (hz_ge : -(2 ^ 128 : ℤ) ≤ z)
    (hK : (n : ℤ) - z = K * 2 ^ 128) :
    (0 ≤ z → (n : ℤ) = z) ∧ (z < 0 → (n : ℤ) = z + 2 ^ 128) := by
  have hn_nn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  have h264 : (0 : ℤ) < 2 ^ 128 := by norm_num
  refine ⟨fun hnn => ?_, fun hneg => ?_⟩
  · have hK_zero : K = 0 := by
      rcases lt_trichotomy K 0 with hlt | heq | hgt
      · have : K ≤ -1 := by linarith
        have : K * 2 ^ 128 ≤ -1 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right this (le_of_lt h264)
        linarith
      · exact heq
      · have : 1 ≤ K := by linarith
        have : 1 * 2 ^ 128 ≤ K * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right this (le_of_lt h264)
        linarith
    rw [hK_zero] at hK; linarith
  · have hK_eq_1 : K = 1 := by
      rcases lt_trichotomy K 1 with hlt | heq | hgt
      · have : K ≤ 0 := by linarith
        have : K * 2 ^ 128 ≤ 0 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right this (le_of_lt h264)
        linarith
      · exact heq
      · have : 2 ≤ K := by linarith
        have : 2 * 2 ^ 128 ≤ K * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right this (le_of_lt h264)
        linarith
    rw [hK_eq_1] at hK; linarith

/-- If `Q · D ≤ B < D · 2^64` and `D > 0`, then `Q < 2^64`. Used repeatedly inside
`toNat_div3By2` to show that successive increments of the initial quotient
remain within `UInt64`. -/
private lemma div3By2_Q_bound {Q D B : ℤ} (hD_pos : 0 < D)
    (hQD : Q * D ≤ B) (hB : B < D * 2 ^ 64) : Q < 2 ^ 64 := by
  by_contra hge
  push Not at hge
  have hmul : (2 ^ 64 : ℤ) * D ≤ Q * D :=
    mul_le_mul_of_nonneg_right hge (le_of_lt hD_pos)
  linarith

/-- Case A-HI of `toNat_div3By2`: `Rtilde ≥ 0` and `r1 ≥ ql`. The normalized result
is `(qh0 + 1 - 1 + 1, x1, x0)` where `x = R_FINAL = Rtilde`. Returns the inner-if
test (`s ≥ D`) together with correctness and remainder bounds. -/
private lemma toNat_div3By2_case_A_HI
    {qh0 ql r1 r0 s1 s0 x1 x0 d1 d0 : UInt64}
    {D U0 U1 U2 Q_HI0 Q_LO R_FINAL : ℕ} {Rtilde : ℤ}
    (hD_def : D = d1.toNat * 2 ^ 64 + d0.toNat)
    (hQ_HI0_def : Q_HI0 = qh0.toNat)
    (hD_Z_pos : (0 : ℤ) < D)
    (hD_lo : 2 ^ 127 ≤ D)
    (hR_FINAL_def : R_FINAL = r1.toNat * 2 ^ 64 + r0.toNat)
    (hR_FINAL_lt : R_FINAL < 2 ^ 128)
    (hR_FINAL_Rt : (R_FINAL : ℤ) = Rtilde)
    (hMain_Z : ((Q_HI0 : ℤ) + 1) * D + R_FINAL = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0)
    (hr1_ge_ql_iff : (r1 ≥ ql) ↔ Q_LO ≤ r1.toNat)
    (hS_val : s1.toNat * 2 ^ 64 + s0.toNat = (R_FINAL + D) % 2 ^ 128)
    (hX_val : x1.toNat * 2 ^ 64 + x0.toNat
      = (2 ^ 128 - D + (s1.toNat * 2 ^ 64 + s0.toNat)) % 2 ^ 128)
    (hRtildeHi_disj : Rtilde < (2 ^ 128 : ℤ) - D ∨ Rtilde < (Q_LO : ℤ) * 2 ^ 64)
    (hDIV_ub_Z : (U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 < D * 2 ^ 64)
    (hcase_hi : r1 ≥ ql) :
    (s1 > d1 ∨ (s1 = d1 ∧ s0 ≥ d0)) ∧
    (qh0 + 1 - 1 + 1).toNat * D + (x1.toNat * 2 ^ 64 + x0.toNat)
        = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 ∧
    x1.toNat * 2 ^ 64 + x0.toNat < D := by
  have hQLO_le_r1N : Q_LO ≤ r1.toNat := hr1_ge_ql_iff.mp hcase_hi
  have hR_FINAL_ge_QLO : Q_LO * 2 ^ 64 ≤ R_FINAL := by
    rw [hR_FINAL_def]
    calc Q_LO * 2 ^ 64
        ≤ r1.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hQLO_le_r1N
      _ ≤ r1.toNat * 2 ^ 64 + r0.toNat := Nat.le_add_right _ _
  have hRt_ge_QLO_Z : (Q_LO : ℤ) * 2 ^ 64 ≤ Rtilde := by
    have h : ((Q_LO * 2 ^ 64 : ℕ) : ℤ) ≤ R_FINAL := by exact_mod_cast hR_FINAL_ge_QLO
    push_cast at h; linarith
  have hRt_lt_2_128_D : Rtilde < (2 ^ 128 : ℤ) - D := by
    rcases hRtildeHi_disj with h | h
    · exact h
    · linarith
  have hRt_lt_D : Rtilde < D := by linarith
  have hQ1_lt : Q_HI0 + 1 < 2 ^ 64 := by
    have h1 : ((Q_HI0 : ℤ) + 1) * D ≤ U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 := by
      have : (0 : ℤ) ≤ R_FINAL := Int.natCast_nonneg _
      linarith
    have h3 : ((Q_HI0 : ℤ) + 1) < 2 ^ 64 := div3By2_Q_bound hD_Z_pos h1 hDIV_ub_Z
    have h5 : (Q_HI0 + 1 : ℤ) < 2 ^ 64 := by linarith
    exact_mod_cast h5
  have hqh0_p1_toNat : (qh0 + 1).toNat = Q_HI0 + 1 := by
    rw [_root_.UInt64.toNat_add, ← hQ_HI0_def]
    show (Q_HI0 + (1 : UInt64).toNat) % 2 ^ 64 = Q_HI0 + 1
    exact Nat.mod_eq_of_lt hQ1_lt
  have hqh0_p1_m1_toNat : (qh0 + 1 - 1).toNat = Q_HI0 := by
    rw [_root_.UInt64.toNat_sub, hqh0_p1_toNat]
    show (2 ^ 64 - (1 : UInt64).toNat + (Q_HI0 + 1)) % 2 ^ 64 = Q_HI0
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  have hqh0_p1_m1_p1_toNat : (qh0 + 1 - 1 + 1).toNat = Q_HI0 + 1 := by
    rw [_root_.UInt64.toNat_add, hqh0_p1_m1_toNat]
    show (Q_HI0 + (1 : UInt64).toNat) % 2 ^ 64 = Q_HI0 + 1
    exact Nat.mod_eq_of_lt hQ1_lt
  have hRF_D_lt : R_FINAL + D < 2 ^ 128 := by
    have h : ((R_FINAL : ℤ) + D) < 2 ^ 128 := by linarith
    have h2 : ((R_FINAL + D : ℕ) : ℤ) < 2 ^ 128 := by push_cast; linarith
    exact_mod_cast h2
  have hSV : s1.toNat * 2 ^ 64 + s0.toNat = R_FINAL + D := by
    rw [hS_val]; exact Nat.mod_eq_of_lt hRF_D_lt
  have hD_le_S : D ≤ s1.toNat * 2 ^ 64 + s0.toNat := by rw [hSV]; omega
  have htest : s1 > d1 ∨ (s1 = d1 ∧ s0 ≥ d0) := by
    apply div3By2_h_test_of_128_ge
    rw [← hD_def]; exact hD_le_S
  have hXV : x1.toNat * 2 ^ 64 + x0.toNat = R_FINAL := by
    rw [hX_val, hSV]
    have hsum : 2 ^ 128 - D + (R_FINAL + D) = 2 ^ 128 + R_FINAL := by omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hR_FINAL_lt
  refine ⟨htest, ?_, ?_⟩
  · rw [hqh0_p1_m1_p1_toNat, hXV]
    have hZ : (((Q_HI0 + 1) * D + R_FINAL : ℕ) : ℤ)
        = ((U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 : ℕ) : ℤ) := by
      push_cast; exact hMain_Z
    exact_mod_cast hZ
  · rw [hXV]
    have h : (R_FINAL : ℤ) < D := by rw [hR_FINAL_Rt]; exact hRt_lt_D
    exact_mod_cast h

/-- Case A-LO-ge of `toNat_div3By2`: `Rtilde ≥ 0`, `r1 < ql`, and `(r1, r0) ≥ (d1, d0)`.
The result is `(qh0 + 1 + 1, w1, w0)` where `w = R_FINAL - D`. -/
private lemma toNat_div3By2_case_A_LO_ge
    {qh0 r1 r0 w1 w0 d1 d0 : UInt64}
    {D U0 U1 U2 Q_HI0 R_FINAL : ℕ}
    (hD_def : D = d1.toNat * 2 ^ 64 + d0.toNat)
    (hQ_HI0_def : Q_HI0 = qh0.toNat)
    (hD_Z_pos : (0 : ℤ) < D)
    (hD_lo : 2 ^ 127 ≤ D)
    (hR_FINAL_def : R_FINAL = r1.toNat * 2 ^ 64 + r0.toNat)
    (hR_FINAL_lt : R_FINAL < 2 ^ 128)
    (hMain_Z : ((Q_HI0 : ℤ) + 1) * D + R_FINAL = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0)
    (hW_val : w1.toNat * 2 ^ 64 + w0.toNat = (2 ^ 128 - D + R_FINAL) % 2 ^ 128)
    (hDIV_ub_Z : (U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 < D * 2 ^ 64)
    (hcase_ge_D : r1 > d1 ∨ (r1 = d1 ∧ r0 ≥ d0)) :
    (qh0 + 1 + 1).toNat * D + (w1.toNat * 2 ^ 64 + w0.toNat)
        = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 ∧
    w1.toNat * 2 ^ 64 + w0.toNat < D := by
  have hRF_ge_D : D ≤ R_FINAL := by
    rw [hD_def, hR_FINAL_def]
    exact div3By2_h128_ge_of_test _ _ _ _ hcase_ge_D
  have hRF_ge_D_Z : (D : ℤ) ≤ R_FINAL := by exact_mod_cast hRF_ge_D
  have hQ2_lt : Q_HI0 + 2 < 2 ^ 64 := by
    have h1 : ((Q_HI0 : ℤ) + 2) * D ≤ U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 := by
      have heq : ((Q_HI0 : ℤ) + 2) * D = ((Q_HI0 : ℤ) + 1) * D + D := by ring
      linarith
    have h3 : ((Q_HI0 : ℤ) + 2) < 2 ^ 64 :=
      div3By2_Q_bound hD_Z_pos h1 hDIV_ub_Z
    have : ((Q_HI0 + 2 : ℕ) : ℤ) < 2 ^ 64 := by push_cast; linarith
    exact_mod_cast this
  have hqh0_p1_toNat : (qh0 + 1).toNat = Q_HI0 + 1 := by
    rw [_root_.UInt64.toNat_add, ← hQ_HI0_def]
    show (Q_HI0 + (1 : UInt64).toNat) % 2 ^ 64 = Q_HI0 + 1
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  have hqh0_p1_p1_toNat : (qh0 + 1 + 1).toNat = Q_HI0 + 2 := by
    rw [_root_.UInt64.toNat_add, hqh0_p1_toNat]
    show (Q_HI0 + 1 + (1 : UInt64).toNat) % 2 ^ 64 = Q_HI0 + 2
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  have hWV : w1.toNat * 2 ^ 64 + w0.toNat = R_FINAL - D := by
    rw [hW_val]
    have hsum : 2 ^ 128 - D + R_FINAL = 2 ^ 128 + (R_FINAL - D) := by omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_⟩
  · rw [hqh0_p1_p1_toNat, hWV]
    have heq : (Q_HI0 + 2) * D + (R_FINAL - D) = (Q_HI0 + 1) * D + R_FINAL := by
      have hadd : (Q_HI0 + 2) * D = (Q_HI0 + 1) * D + D := by ring
      omega
    rw [heq]
    have hZ : (((Q_HI0 + 1) * D + R_FINAL : ℕ) : ℤ)
        = ((U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 : ℕ) : ℤ) := by
      push_cast; exact hMain_Z
    exact_mod_cast hZ
  · rw [hWV]
    have hRF_lt_2D : R_FINAL < 2 * D := by
      have : 2 ^ 128 ≤ 2 * D := by omega
      omega
    omega

/-- Case A-LO-lt of `toNat_div3By2`: `Rtilde ≥ 0`, `r1 < ql`, and `(r1, r0) < (d1, d0)`.
The result is `(qh0 + 1, r1, r0)` where the remainder is already `R_FINAL < D`. -/
private lemma toNat_div3By2_case_A_LO_lt
    {qh0 r1 r0 d1 d0 : UInt64}
    {D U0 U1 U2 Q_HI0 R_FINAL : ℕ}
    (hD_def : D = d1.toNat * 2 ^ 64 + d0.toNat)
    (hQ_HI0_def : Q_HI0 = qh0.toNat)
    (hD_Z_pos : (0 : ℤ) < D)
    (hR_FINAL_def : R_FINAL = r1.toNat * 2 ^ 64 + r0.toNat)
    (hMain_Z : ((Q_HI0 : ℤ) + 1) * D + R_FINAL = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0)
    (hDIV_ub_Z : (U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 < D * 2 ^ 64)
    (hcase_not_ge_D : ¬ (r1 > d1 ∨ (r1 = d1 ∧ r0 ≥ d0))) :
    (qh0 + 1).toNat * D + (r1.toNat * 2 ^ 64 + r0.toNat)
        = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 ∧
    r1.toNat * 2 ^ 64 + r0.toNat < D := by
  have hRF_lt_D : R_FINAL < D := by
    by_contra h
    push Not at h
    apply hcase_not_ge_D
    apply div3By2_h_test_of_128_ge
    rw [hD_def, hR_FINAL_def] at h
    exact h
  have hQ1_lt : Q_HI0 + 1 < 2 ^ 64 := by
    have hRF_Z_nn : (0 : ℤ) ≤ R_FINAL := Int.natCast_nonneg _
    have h1 : ((Q_HI0 : ℤ) + 1) * D ≤ U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 := by linarith
    have h3 : ((Q_HI0 : ℤ) + 1) < 2 ^ 64 :=
      div3By2_Q_bound hD_Z_pos h1 hDIV_ub_Z
    have : ((Q_HI0 + 1 : ℕ) : ℤ) < 2 ^ 64 := by push_cast; linarith
    exact_mod_cast this
  have hqh0_p1_toNat : (qh0 + 1).toNat = Q_HI0 + 1 := by
    rw [_root_.UInt64.toNat_add, ← hQ_HI0_def]
    show (Q_HI0 + (1 : UInt64).toNat) % 2 ^ 64 = Q_HI0 + 1
    exact Nat.mod_eq_of_lt hQ1_lt
  refine ⟨?_, ?_⟩
  · rw [hqh0_p1_toNat, ← hR_FINAL_def]
    have hZ : (((Q_HI0 + 1) * D + R_FINAL : ℕ) : ℤ)
        = ((U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 : ℕ) : ℤ) := by
      push_cast; exact hMain_Z
    exact_mod_cast hZ
  · rw [← hR_FINAL_def]; exact hRF_lt_D

/-- Case B-HI of `toNat_div3By2`: `Rtilde < 0` and `r1 ≥ ql`. The inner 128-bit test
on `(s1, s0) ≥ (d1, d0)` fails, and the result is `(qh0 + 1 - 1, s1, s0)` where
`s = R_FINAL + D - 2^128`. -/
private lemma toNat_div3By2_case_B_HI
    {qh0 s1 s0 d1 d0 : UInt64}
    {D U0 U1 U2 Q_HI0 R_FINAL : ℕ} {Rtilde : ℤ}
    (hD_def : D = d1.toNat * 2 ^ 64 + d0.toNat)
    (hD_hi : D < 2 ^ 128)
    (hQ_HI0_def : Q_HI0 = qh0.toNat)
    (hR_FINAL_lt : R_FINAL < 2 ^ 128)
    (hR_FINAL_Rt : (R_FINAL : ℤ) = Rtilde + 2 ^ 128)
    (hRtilde_def : Rtilde = (U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 - ((Q_HI0 : ℤ) + 1) * D)
    (hRt_ge_neg_D : -(D : ℤ) ≤ Rtilde)
    (hS_val : s1.toNat * 2 ^ 64 + s0.toNat = (R_FINAL + D) % 2 ^ 128) :
    ¬ (s1 > d1 ∨ (s1 = d1 ∧ s0 ≥ d0)) ∧
    (qh0 + 1 - 1).toNat * D + (s1.toNat * 2 ^ 64 + s0.toNat)
        = U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 ∧
    s1.toNat * 2 ^ 64 + s0.toNat < D := by
  have hRF_D_ge : 2 ^ 128 ≤ R_FINAL + D := by
    have h : ((2 ^ 128 : ℤ)) ≤ (R_FINAL : ℤ) + D := by
      rw [hR_FINAL_Rt]; linarith
    have h2 : ((2 ^ 128 : ℕ) : ℤ) ≤ ((R_FINAL + D : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h2
  have hRF_D_lt : R_FINAL + D < 2 ^ 128 + D := by
    have : R_FINAL < 2 ^ 128 := hR_FINAL_lt
    omega
  have hSV : s1.toNat * 2 ^ 64 + s0.toNat = R_FINAL + D - 2 ^ 128 := by
    have hlt : R_FINAL + D - 2 ^ 128 < 2 ^ 128 := by
      have h1 := hRF_D_lt
      have h2 := hD_hi
      omega
    rw [hS_val, Nat.mod_eq_sub_mod hRF_D_ge, Nat.mod_eq_of_lt hlt]
  have hs_lt_D : s1.toNat * 2 ^ 64 + s0.toNat < D := by
    rw [hSV]
    have h : ((R_FINAL + D - 2 ^ 128 : ℕ) : ℤ) < D := by
      rw [Nat.cast_sub hRF_D_ge]
      push_cast
      rw [hR_FINAL_Rt]; linarith
    exact_mod_cast h
  have hnot_test : ¬ (s1 > d1 ∨ (s1 = d1 ∧ s0 ≥ d0)) := by
    intro htest
    have h := div3By2_h128_ge_of_test _ _ _ _ htest
    have h' : D ≤ s1.toNat * 2 ^ 64 + s0.toNat := by rw [hD_def]; exact h
    exact absurd h' (Nat.not_le_of_lt hs_lt_D)
  have hqh0_p1_m1_toNat : (qh0 + 1 - 1).toNat = Q_HI0 := by
    rw [_root_.UInt64.toNat_sub, _root_.UInt64.toNat_add, ← hQ_HI0_def]
    show (2 ^ 64 - (1 : UInt64).toNat + (Q_HI0 + (1 : UInt64).toNat) % 2 ^ 64) % 2 ^ 64
        = Q_HI0
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h2 : Q_HI0 < 2 ^ 64 := by rw [hQ_HI0_def]; exact _root_.UInt64.toNat_lt _
    omega
  refine ⟨hnot_test, ?_, hs_lt_D⟩
  rw [hqh0_p1_m1_toNat, hSV]
  have hZ : ((Q_HI0 * D + (R_FINAL + D - 2 ^ 128) : ℕ) : ℤ)
      = ((U2 * 2 ^ 128 + U1 * 2 ^ 64 + U0 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub hRF_D_ge]
    push_cast
    rw [hR_FINAL_Rt, hRtilde_def]
    ring
  exact_mod_cast hZ

/-- Case B-LO of `toNat_div3By2`: `Rtilde < 0` and `r1 < ql` — impossible by the
lower bound on `Rtilde`. -/
private lemma toNat_div3By2_case_B_LO
    {ql r1 r0 : UInt64}
    {Q_LO R_FINAL : ℕ} {Rtilde : ℤ}
    (hR_FINAL_def : R_FINAL = r1.toNat * 2 ^ 64 + r0.toNat)
    (hR_FINAL_Rt : (R_FINAL : ℤ) = Rtilde + 2 ^ 128)
    (hRt_ge_QLO_shift : (Q_LO : ℤ) * 2 ^ 64 + 1 - 2 ^ 128 ≤ Rtilde)
    (hr1_ge_ql_iff : (r1 ≥ ql) ↔ Q_LO ≤ r1.toNat)
    (hcase_not_hi : ¬ r1 ≥ ql) : False := by
  have hr1N_lt_QLO : r1.toNat < Q_LO :=
    Nat.lt_of_not_le (fun h => hcase_not_hi (hr1_ge_ql_iff.mpr h))
  have hRF_lt_QLO : R_FINAL < Q_LO * 2 ^ 64 := by
    rw [hR_FINAL_def]
    have hr0_lt : r0.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
    have h1 : r1.toNat + 1 ≤ Q_LO := hr1N_lt_QLO
    have h2 : (r1.toNat + 1) * 2 ^ 64 ≤ Q_LO * 2 ^ 64 := Nat.mul_le_mul_right _ h1
    have h3 : (r1.toNat + 1) * 2 ^ 64 = r1.toNat * 2 ^ 64 + 2 ^ 64 := by ring
    omega
  have hRt_lt_QLO_sub : Rtilde < (Q_LO : ℤ) * 2 ^ 64 - 2 ^ 128 := by
    have h : ((R_FINAL : ℕ) : ℤ) < Q_LO * 2 ^ 64 := by exact_mod_cast hRF_lt_QLO
    linarith [hR_FINAL_Rt]
  linarith

/-- Packaging of the variables and hypotheses produced by the common setup of
`toNat_div3By2` (everything up to and including the case-independent bounds).
Splitting this out lets the dispatcher compile separately from the arithmetic
setup, avoiding the accumulated let-binding overhead of a single giant proof. -/
private structure Div3By2Setup (u2 u1 u0 d1 d0 v : UInt64) where
  qh0 : UInt64
  ql : UInt64
  r1 : UInt64
  r0 : UInt64
  s1 : UInt64
  s0 : UInt64
  w1 : UInt64
  w0 : UInt64
  x1 : UInt64
  x0 : UInt64
  D : ℕ
  Q_HI0 : ℕ
  Q_LO : ℕ
  R_FINAL : ℕ
  Rtilde : ℤ
  hD_def : D = d1.toNat * 2 ^ 64 + d0.toNat
  hQ_HI0_def : Q_HI0 = qh0.toNat
  hD_Z_pos : (0 : ℤ) < D
  hD_hi : D < 2 ^ 128
  hD_lo : 2 ^ 127 ≤ D
  hR_FINAL_def : R_FINAL = r1.toNat * 2 ^ 64 + r0.toNat
  hR_FINAL_lt : R_FINAL < 2 ^ 128
  hR_FINAL_Rtilde :
    (0 ≤ Rtilde → (R_FINAL : ℤ) = Rtilde) ∧
    (Rtilde < 0 → (R_FINAL : ℤ) = Rtilde + 2 ^ 128)
  hRtilde_def :
    Rtilde = (u2.toNat : ℤ) * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat
      - ((Q_HI0 : ℤ) + 1) * D
  hRtildeHi_disj : Rtilde < (2 ^ 128 : ℤ) - D ∨ Rtilde < (Q_LO : ℤ) * 2 ^ 64
  hRt_ge_neg_D : -(D : ℤ) ≤ Rtilde
  hRt_ge_QLO_shift : (Q_LO : ℤ) * 2 ^ 64 + 1 - 2 ^ 128 ≤ Rtilde
  hr1_ge_ql_iff : (r1 ≥ ql) ↔ Q_LO ≤ r1.toNat
  hS_val : s1.toNat * 2 ^ 64 + s0.toNat = (R_FINAL + D) % 2 ^ 128
  hW_val : w1.toNat * 2 ^ 64 + w0.toNat = (2 ^ 128 - D + R_FINAL) % 2 ^ 128
  hX_val : x1.toNat * 2 ^ 64 + x0.toNat
    = (2 ^ 128 - D + (s1.toNat * 2 ^ 64 + s0.toNat)) % 2 ^ 128
  hDIV_ub_Z :
    (u2.toNat : ℤ) * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat < D * 2 ^ 64
  hunfold :
    div3By2 u2 u1 u0 d1 d0 v
      = if r1 ≥ ql then
          if s1 > d1 ∨ (s1 = d1 ∧ s0 ≥ d0) then
            (qh0 + 1 - 1 + 1, x1, x0)
          else
            (qh0 + 1 - 1, s1, s0)
        else
          if r1 > d1 ∨ (r1 = d1 ∧ r0 ≥ d0) then
            (qh0 + 1 + 1, w1, w0)
          else
            (qh0 + 1, r1, r0)

/-- Core identity `R_FINAL - Rtilde = (3 + kA - kP - kI - kR - U2) * 2^128`, proved
from the `Nat.div_add_mod`-style witnesses `hR_rel`/`hI_rel`/`hP_rel`/`hA_rel` and
the decomposition `B = D0 * Q_HI0`, `D = D1 * 2^64 + D0`.

Extracting this into a standalone lemma shrinks the context seen by `linarith`,
making the four casting steps dramatically faster than when inlined in the
`toNat_div3By2_setup` body (which has ~30 `let`-bindings in scope). -/
private lemma div3By2_R_FINAL_Rtilde_identity
    {D D1 D0 U0 U1 U2 Q_HI0 A B R1_PRE_N INN R_FINAL kA kP kI kR : ℕ}
    (hD_def : D = D1 * 2 ^ 64 + D0)
    (hD_le : D ≤ 2 ^ 128)
    (hB_le : B ≤ 2 ^ 128)
    (hA_le : A ≤ 2 ^ 64)
    (hB_def : B = D0 * Q_HI0)
    (hR_rel : 2 ^ 128 - D + INN = R_FINAL + kR * 2 ^ 128)
    (hI_rel : 2 ^ 128 - B + R1_PRE_N * 2 ^ 64 + U0 = INN + kI * 2 ^ 128)
    (hP_rel : 2 ^ 64 - A + U1 = R1_PRE_N + kP * 2 ^ 64)
    (hA_rel : Q_HI0 * D1 = A + kA * 2 ^ 64) :
    (R_FINAL : ℤ) - ((U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 - ((Q_HI0 : ℤ) + 1) * D)
      = (3 + (kA : ℤ) - kP - kI - kR - U2) * 2 ^ 128 := by
  have hR_EQ : (R_FINAL : ℤ) = 2 ^ 128 - (D : ℤ) + INN - (kR : ℤ) * 2 ^ 128 := by
    have h := hR_rel; zify [hD_le] at h; linarith
  have hI_EQ : (INN : ℤ)
      = 2 ^ 128 - (B : ℤ) + (R1_PRE_N : ℤ) * 2 ^ 64 + U0 - (kI : ℤ) * 2 ^ 128 := by
    have h := hI_rel; zify [hB_le] at h; linarith
  have hP_EQ : (R1_PRE_N : ℤ) = 2 ^ 64 - (A : ℤ) + U1 - (kP : ℤ) * 2 ^ 64 := by
    have h := hP_rel; zify [hA_le] at h; linarith
  have hA_EQ : (A : ℤ) = (Q_HI0 : ℤ) * D1 - (kA : ℤ) * 2 ^ 64 := by
    have h := hA_rel; zify at h; linarith
  have hB_Z : (B : ℤ) = D0 * Q_HI0 := by exact_mod_cast hB_def
  have hD_split_Z : (D : ℤ) = D1 * 2 ^ 64 + D0 := by push_cast [hD_def]; ring
  rw [hR_EQ, hI_EQ, hP_EQ, hA_EQ, hB_Z, hD_split_Z]
  ring

set_option maxHeartbeats 800000 in
/-- Common setup for `toNat_div3By2`: runs the algorithm, destructures the
intermediate `wideMul`/`wideAdd`/`wideSub` operations, derives all the
case-independent bounds (including `Rtilde`'s upper/lower bounds and the
dividend bound `[u2,u1,u0] < D · 2^64`), and packages them into `Div3By2Setup`.

Isolating this lets the main dispatcher compile at default heartbeats, since
none of the ~20 local `set`-bindings needed here are in scope there. -/
private noncomputable def toNat_div3By2_setup {u2 u1 u0 d1 d0 v : UInt64}
    (hd1 : 2 ^ 63 ≤ d1.toNat)
    (hud : u2.toNat * 2 ^ 64 + u1.toNat < d1.toNat * 2 ^ 64 + d0.toNat)
    (hv : v = reciprocal3By2 d1 d0 hd1) :
    Div3By2Setup u2 u1 u0 d1 d0 v := by
  set D1 : ℕ := d1.toNat with hD1_def
  set D0 : ℕ := d0.toNat with hD0_def
  set U2 : ℕ := u2.toNat with hU2_def
  set U1 : ℕ := u1.toNat with hU1_def
  set U0 : ℕ := u0.toNat with hU0_def
  set V : ℕ := v.toNat with hV_def
  have hD1_lt : D1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD0_lt : D0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hU2_lt : U2 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hU1_lt : U1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hU0_lt : U0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hV_lt : V < 2 ^ 64 := _root_.UInt64.toNat_lt _
  set D : ℕ := D1 * 2 ^ 64 + D0 with hD_def
  have hD_lo : 2 ^ 127 ≤ D := by
    rw [hD_def]
    have h2 : 2 ^ 63 * 2 ^ 64 ≤ D1 * 2 ^ 64 := Nat.mul_le_mul_right _ hd1
    have hp : (2 : ℕ) ^ 63 * 2 ^ 64 = 2 ^ 127 := by norm_num
    linarith
  have hD_hi : D < 2 ^ 128 := by
    rw [hD_def]
    have h : (D1 + 1) * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ hD1_lt
    have hexp : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
    have hp : (D1 + 1) * 2 ^ 64 = D1 * 2 ^ 64 + 2 ^ 64 := by ring
    linarith
  have hD_pos : 0 < D := by linarith
  have hUD : U2 * 2 ^ 64 + U1 < D := hud
  -- Reciprocal specification.
  have hV_val : V = (2 ^ 192 - 1) / D - 2 ^ 64 := by
    rw [hV_def, hv]; exact toNat_reciprocal3By2 d1 d0 hd1
  have h_2_64_D_le : 2 ^ 64 * D ≤ 2 ^ 192 - 1 := by
    have h1 : 2 ^ 64 * D ≤ 2 ^ 64 * (2 ^ 128 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : (2 : ℕ) ^ 64 * (2 ^ 128 - 1) = 2 ^ 192 - 2 ^ 64 := by
      have hp : (2 : ℕ) ^ 64 * 2 ^ 128 = 2 ^ 192 := by norm_num
      have hb : (2 : ℕ) ^ 64 ≤ 2 ^ 128 := by norm_num
      have := @Nat.mul_sub_one (2^64) (2^128)
      omega
    omega
  have h_RD_ge : 2 ^ 64 ≤ (2 ^ 192 - 1) / D := by
    rw [Nat.le_div_iff_mul_le hD_pos]; linarith
  have hV_eq : 2 ^ 64 + V = (2 ^ 192 - 1) / D := by
    rw [hV_val]; omega
  have hInv_lo : (2 ^ 64 + V) * D ≤ 2 ^ 192 - 1 := by
    rw [hV_eq]; exact Nat.div_mul_le_self _ _
  have hInv_hi : 2 ^ 192 - 1 < (2 ^ 64 + V + 1) * D := by
    rw [hV_eq]
    have hdm : (2 ^ 192 - 1) / D * D + (2 ^ 192 - 1) % D = 2 ^ 192 - 1 :=
      Nat.div_add_mod' _ _
    have hmod_lt : (2 ^ 192 - 1) % D < D := Nat.mod_lt _ hD_pos
    have : ((2 ^ 192 - 1) / D + 1) * D = (2 ^ 192 - 1) / D * D + D := by ring
    omega
  -- Compute wideMul v u2.
  have hWM : (wideMul v u2).1.toNat * 2 ^ 64 + (wideMul v u2).2.toNat = V * U2 :=
    toNat_wideMul v u2
  -- Compute wideAdd (wideMul v u2) (u2, u1).
  rcases hQPeq : wideAdd (wideMul v u2) (u2, u1) with ⟨qh0, ql⟩
  set Q_HI0 : ℕ := qh0.toNat with hQ_HI0_def
  set Q_LO : ℕ := ql.toNat with hQ_LO_def
  have hQ_HI0_lt : Q_HI0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hQ_LO_lt : Q_LO < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hQPadd : Q_HI0 * 2 ^ 64 + Q_LO
      = ((wideMul v u2).1.toNat * 2 ^ 64 + (wideMul v u2).2.toNat
          + (U2 * 2 ^ 64 + U1)) % 2 ^ 128 := by
    have := toNat_wideAdd (wideMul v u2) (u2, u1)
    rw [hQPeq] at this
    exact this
  have h_sum_lt : (2 ^ 64 + V) * U2 + U1 < 2 ^ 128 :=
    div3By2_sum_lt hD_def hD0_lt hU1_lt hUD hInv_lo
  have hQP_val : Q_HI0 * 2 ^ 64 + Q_LO = (2 ^ 64 + V) * U2 + U1 := by
    rw [hQPadd, hWM]
    have heq : V * U2 + (U2 * 2 ^ 64 + U1) = (2 ^ 64 + V) * U2 + U1 := by ring
    rw [heq]
    exact Nat.mod_eq_of_lt h_sum_lt
  -- Apply Theorem 3 bounds.
  have hbounds := div3By2_rtilde_bounds (D := D) (u2 := U2) (u1 := U1) (u0 := U0)
    (q1 := Q_HI0) (q0 := Q_LO) (v := V)
    hD_lo hD_hi hU1_lt hU0_lt hQ_LO_lt hUD hInv_lo hInv_hi hQP_val
  obtain ⟨hRtildeLo, hRtildeHi⟩ := hbounds
  -- Compute r1_pre := u1 - qh0 * d1 at UInt64 level.
  set R1_PRE : UInt64 := u1 - qh0 * d1 with hR1_PRE_def
  set R1_PRE_N : ℕ := R1_PRE.toNat with hR1_PRE_N_def
  have hR1_PRE_N_val :
      R1_PRE_N = (2 ^ 64 - (Q_HI0 * d1.toNat) % 2 ^ 64 + U1) % 2 ^ 64 := by
    rw [hR1_PRE_N_def, hR1_PRE_def, _root_.UInt64.toNat_sub, _root_.UInt64.toNat_mul]
  -- Destructure wideMul d0 qh0.
  rcases hWMD : wideMul d0 qh0 with ⟨t1, t0⟩
  set T1_N : ℕ := t1.toNat with hT1_N_def
  set T0_N : ℕ := t0.toNat with hT0_N_def
  have hT_val : T1_N * 2 ^ 64 + T0_N = D0 * Q_HI0 := by
    have := toNat_wideMul d0 qh0
    rw [hWMD] at this
    exact this
  -- Destructure inner wideSub.
  rcases hIN : wideSub (R1_PRE, u0) (t1, t0) with ⟨inn_h, inn_l⟩
  set INN : ℕ := inn_h.toNat * 2 ^ 64 + inn_l.toNat with hINN_def
  have hINN_val : INN = (2 ^ 128 - D0 * Q_HI0 + (R1_PRE_N * 2 ^ 64 + U0)) % 2 ^ 128 := by
    have := toNat_wideSub (R1_PRE, u0) (t1, t0)
    rw [hIN] at this
    show inn_h.toNat * 2 ^ 64 + inn_l.toNat = _
    rw [this]
    congr 1
    simp only
    rw [hT_val]
  -- Destructure outer wideSub.
  rcases hOUT : wideSub (inn_h, inn_l) (d1, d0) with ⟨r1, r0⟩
  set R_FINAL : ℕ := r1.toNat * 2 ^ 64 + r0.toNat with hR_FINAL_def
  have hR_FINAL_val : R_FINAL = (2 ^ 128 - D + INN) % 2 ^ 128 := by
    have h := toNat_wideSub (inn_h, inn_l) (d1, d0)
    rw [hOUT] at h
    show r1.toNat * 2 ^ 64 + r0.toNat = _
    rw [h, ← hINN_def, ← hD1_def, ← hD0_def, ← hD_def]
  have hR_FINAL_lt : R_FINAL < 2 ^ 128 := by
    rw [hR_FINAL_val]; exact Nat.mod_lt _ (by norm_num)
  have hD0Q : D0 * Q_HI0 < 2 ^ 128 := by
    have hD0m : D0 ≤ 2 ^ 64 - 1 := by omega
    have hQm : Q_HI0 ≤ 2 ^ 64 - 1 := by omega
    calc D0 * Q_HI0
        ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul hD0m hQm
      _ < 2 ^ 128 := by norm_num
  have hD_le : D ≤ 2 ^ 128 := le_of_lt hD_hi
  have hR1_PRE_N_lt : R1_PRE_N < 2 ^ 64 := by
    rw [hR1_PRE_N_val]; exact Nat.mod_lt _ (by norm_num)
  have hQD1_lt : Q_HI0 * D1 < 2 ^ 128 := by
    calc Q_HI0 * D1
        ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 128 := by norm_num
  -- Nat modular identity: R_FINAL + (Q_HI0+1)*D ≡ U1*2^64 + U0 (mod 2^128).
  -- This is the cleanest statement as it avoids ℤ conversions for the base fact.
  set A : ℕ := Q_HI0 * D1 % 2 ^ 64 with hA_def
  set B : ℕ := D0 * Q_HI0 with hB_def
  have hA_lt : A < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hA_le : A ≤ 2 ^ 64 := le_of_lt hA_lt
  have hB_le : B ≤ 2 ^ 128 := le_of_lt hD0Q
  have hR1_PRE_N_val' : R1_PRE_N = (2 ^ 64 - A + U1) % 2 ^ 64 := hR1_PRE_N_val
  have hINN_val' : INN = (2 ^ 128 - B + R1_PRE_N * 2 ^ 64 + U0) % 2 ^ 128 := by
    rw [hINN_val]; congr 1; ring
  -- Integer version of Rtilde.
  set Rtilde : ℤ := (U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 - ((Q_HI0 : ℤ) + 1) * D with hRtilde_def
  -- Extract integer witnesses from each mod relation.
  set kA : ℕ := Q_HI0 * D1 / 2 ^ 64 with hkA_def
  have hA_rel : Q_HI0 * D1 = A + kA * 2 ^ 64 := by
    have := Nat.div_add_mod (Q_HI0 * D1) (2 ^ 64)
    show Q_HI0 * D1 = Q_HI0 * D1 % 2 ^ 64 + Q_HI0 * D1 / 2 ^ 64 * 2 ^ 64
    omega
  set kP : ℕ := (2 ^ 64 - A + U1) / 2 ^ 64 with hkP_def
  have hP_rel : 2 ^ 64 - A + U1 = R1_PRE_N + kP * 2 ^ 64 := by
    have h := Nat.div_add_mod (2 ^ 64 - A + U1) (2 ^ 64)
    rw [hR1_PRE_N_val']
    omega
  set kI : ℕ := (2 ^ 128 - B + R1_PRE_N * 2 ^ 64 + U0) / 2 ^ 128 with hkI_def
  have hI_rel : 2 ^ 128 - B + R1_PRE_N * 2 ^ 64 + U0 = INN + kI * 2 ^ 128 := by
    have h := Nat.div_add_mod (2 ^ 128 - B + R1_PRE_N * 2 ^ 64 + U0) (2 ^ 128)
    rw [hINN_val']
    omega
  set kR : ℕ := (2 ^ 128 - D + INN) / 2 ^ 128 with hkR_def
  have hR_rel : 2 ^ 128 - D + INN = R_FINAL + kR * 2 ^ 128 := by
    have h := Nat.div_add_mod (2 ^ 128 - D + INN) (2 ^ 128)
    rw [hR_FINAL_val]
    omega
  -- R_FINAL - Rtilde = (3 + kA - kP - kI - kR - U2) * 2^128, proved via the
  -- extracted helper lemma (keeps the linarith calls in a tiny context).
  have hEq' : (R_FINAL : ℤ) - Rtilde
      = (3 + (kA : ℤ) - kP - kI - kR - U2) * 2 ^ 128 := by
    rw [hRtilde_def]
    exact div3By2_R_FINAL_Rtilde_identity (U2 := U2) (U1 := U1) (U0 := U0)
      hD_def hD_le hB_le hA_le hB_def hR_rel hI_rel hP_rel hA_rel
  -- Bounds for Rtilde: -D ≤ Rtilde < 2^128 and specific tight bounds.
  have hQ_LO_Z_lt : (Q_LO : ℤ) < 2 ^ 64 := by exact_mod_cast hQ_LO_lt
  have hD_Z_lt : (D : ℤ) < 2 ^ 128 := by exact_mod_cast hD_hi
  have hD_Z_lo : (2 ^ 127 : ℤ) ≤ D := by exact_mod_cast hD_lo
  have hD_Z_pos : (0 : ℤ) < D := by linarith
  have hQLO_times_264 : (Q_LO : ℤ) * 2 ^ 64 ≤ 2 ^ 128 := by
    have h1 : (Q_LO : ℤ) ≤ 2 ^ 64 - 1 := by linarith
    have h2 : (Q_LO : ℤ) * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := by
      have : (0 : ℤ) ≤ 2 ^ 64 := by norm_num
      exact mul_le_mul_of_nonneg_right h1 this
    linarith
  have hRt_lt_2_128 : Rtilde < 2 ^ 128 := by
    have hmax_le : max ((2 ^ 128 : ℤ) - D) ((Q_LO : ℤ) * 2 ^ 64) ≤ 2 ^ 128 :=
      max_le (by linarith) hQLO_times_264
    linarith [hRtildeHi]
  have hRt_ge_neg_D : -(D : ℤ) ≤ Rtilde := by
    have h : (2 ^ 128 : ℤ) - D ≤ max ((2 ^ 128 : ℤ) - D) ((Q_LO : ℤ) * 2 ^ 64 + 1) :=
      le_max_left _ _
    linarith [hRtildeLo]
  have hRt_ge_QLO_shift : (Q_LO : ℤ) * 2 ^ 64 + 1 - 2 ^ 128 ≤ Rtilde := by
    have h : (Q_LO : ℤ) * 2 ^ 64 + 1 ≤ max ((2 ^ 128 : ℤ) - D) ((Q_LO : ℤ) * 2 ^ 64 + 1) :=
      le_max_right _ _
    linarith [hRtildeLo]
  -- Disjunctive upper bound.
  have hRtildeHi_disj : Rtilde < (2 ^ 128 : ℤ) - D ∨ Rtilde < (Q_LO : ℤ) * 2 ^ 64 :=
    lt_max_iff.mp hRtildeHi
  -- R_FINAL is the canonical representative of Rtilde mod 2^128.
  have hR_FINAL_Z_lt : (R_FINAL : ℤ) < 2 ^ 128 := by exact_mod_cast hR_FINAL_lt
  have hR_FINAL_Z_nn : (0 : ℤ) ≤ (R_FINAL : ℤ) := Int.natCast_nonneg _
  have hD_le_2_128_Z : -(2 ^ 128 : ℤ) ≤ Rtilde := by
    have : -(D : ℤ) ≤ Rtilde := hRt_ge_neg_D
    linarith
  have hR_FINAL_Rtilde :
      (0 ≤ Rtilde → (R_FINAL : ℤ) = Rtilde) ∧
      (Rtilde < 0 → (R_FINAL : ℤ) = Rtilde + 2 ^ 128) :=
    div3By2_rep_of_mod hR_FINAL_Z_lt hRt_lt_2_128 hD_le_2_128_Z hEq'
  -- Destructure the remaining wideAdd/wideSub operations in div3By2 / div3By2Tail.
  rcases hADD : wideAdd (r1, r0) (d1, d0) with ⟨s1, s0⟩
  rcases hSUB1 : wideSub (r1, r0) (d1, d0) with ⟨w1, w0⟩
  rcases hSUB2 : wideSub (s1, s0) (d1, d0) with ⟨x1, x0⟩
  have hunfold :
      div3By2 u2 u1 u0 d1 d0 v
        = if r1 ≥ ql then
            if s1 > d1 ∨ (s1 = d1 ∧ s0 ≥ d0) then
              (qh0 + 1 - 1 + 1, x1, x0)
            else
              (qh0 + 1 - 1, s1, s0)
          else
            if r1 > d1 ∨ (r1 = d1 ∧ r0 ≥ d0) then
              (qh0 + 1 + 1, w1, w0)
            else
              (qh0 + 1, r1, r0) := by
    simp only [div3By2, div3By2Tail, hQPeq, ← hR1_PRE_def, hWMD, hIN, hOUT,
      hADD, hSUB1, hSUB2]
  -- UInt64 ↔ Nat conversion helpers.
  have hr1_ge_ql_iff : (r1 ≥ ql) ↔ Q_LO ≤ r1.toNat := _root_.UInt64.le_iff_toNat_le
  have hS_val : s1.toNat * 2 ^ 64 + s0.toNat = (R_FINAL + D) % 2 ^ 128 := by
    have h := toNat_wideAdd (r1, r0) (d1, d0)
    rw [hADD] at h
    show s1.toNat * 2 ^ 64 + s0.toNat = _
    rw [h, ← hR_FINAL_def, ← hD_def]
  have hW_val : w1.toNat * 2 ^ 64 + w0.toNat = (2 ^ 128 - D + R_FINAL) % 2 ^ 128 := by
    have h := toNat_wideSub (r1, r0) (d1, d0)
    rw [hSUB1] at h
    show w1.toNat * 2 ^ 64 + w0.toNat = _
    rw [h, ← hR_FINAL_def, ← hD_def]
  have hX_val : x1.toNat * 2 ^ 64 + x0.toNat
      = (2 ^ 128 - D + (s1.toNat * 2 ^ 64 + s0.toNat)) % 2 ^ 128 := by
    have h := toNat_wideSub (s1, s0) (d1, d0)
    rw [hSUB2] at h
    show x1.toNat * 2 ^ 64 + x0.toNat = _
    rw [h, ← hD_def]
  -- [u2,u1,u0] < D * 2^64 (from hud and U0 < 2^64).
  have hDIV_ub_Z : (U2 : ℤ) * 2 ^ 128 + U1 * 2 ^ 64 + U0 < D * 2 ^ 64 := by
    have h1 : ((U2 * 2 ^ 64 + U1 : ℕ) : ℤ) < D := by exact_mod_cast hUD
    have h3 : ((U2 * 2 ^ 64 + U1 + 1 : ℕ) : ℤ) ≤ D := by push_cast; linarith
    have h2 : ((U2 * 2 ^ 64 + U1 + 1 : ℕ) : ℤ) * 2 ^ 64 ≤ D * 2 ^ 64 :=
      mul_le_mul_of_nonneg_right h3 (by norm_num)
    have h4 : (U0 : ℤ) < 2 ^ 64 := by exact_mod_cast hU0_lt
    push_cast at h2
    linarith [h2, h4]
  exact
    ⟨qh0, ql, r1, r0, s1, s0, w1, w0, x1, x0, D, Q_HI0, Q_LO, R_FINAL, Rtilde,
      hD_def, hQ_HI0_def, hD_Z_pos, hD_hi, hD_lo, hR_FINAL_def, hR_FINAL_lt,
      hR_FINAL_Rtilde, hRtilde_def, hRtildeHi_disj, hRt_ge_neg_D, hRt_ge_QLO_shift,
      hr1_ge_ql_iff, hS_val, hW_val, hX_val, hDIV_ub_Z, hunfold⟩

/-- Correctness of `div3By2` (Möller–Granlund Algorithm 5): for a normalized
128-bit divisor `(d1, d0)` (`2^63 ≤ d1.toNat`), a 192-bit dividend `[u2, u1, u0]`
with `(u2, u1) < (d1, d0)`, and the precomputed reciprocal
`v = reciprocal3By2 d1 d0 hd1`, the returned `(q, r1, r0)` satisfies
`q · D + (r1 · 2^64 + r0) = u2 · 2^128 + u1 · 2^64 + u0` and `r1 · 2^64 + r0 < D`,
where `D = d1 · 2^64 + d0`. -/
theorem toNat_div3By2 (u2 u1 u0 d1 d0 v : UInt64)
    (hd1 : 2 ^ 63 ≤ d1.toNat)
    (hud : u2.toNat * 2 ^ 64 + u1.toNat < d1.toNat * 2 ^ 64 + d0.toNat)
    (hv : v = reciprocal3By2 d1 d0 hd1) :
    (div3By2 u2 u1 u0 d1 d0 v).1.toNat * (d1.toNat * 2 ^ 64 + d0.toNat)
        + ((div3By2 u2 u1 u0 d1 d0 v).2.1.toNat * 2 ^ 64
            + (div3By2 u2 u1 u0 d1 d0 v).2.2.toNat)
      = u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat
    ∧ (div3By2 u2 u1 u0 d1 d0 v).2.1.toNat * 2 ^ 64
        + (div3By2 u2 u1 u0 d1 d0 v).2.2.toNat < d1.toNat * 2 ^ 64 + d0.toNat := by
  obtain ⟨qh0, ql, r1, r0, s1, s0, w1, w0, x1, x0, D, Q_HI0, Q_LO, R_FINAL, Rtilde,
      hD_def, hQ_HI0_def, hD_Z_pos, hD_hi, hD_lo, hR_FINAL_def, hR_FINAL_lt,
      hR_FINAL_Rtilde, hRtilde_def, hRtildeHi_disj, hRt_ge_neg_D, hRt_ge_QLO_shift,
      hr1_ge_ql_iff, hS_val, hW_val, hX_val, hDIV_ub_Z, hunfold⟩ :=
    toNat_div3By2_setup hd1 hud hv
  rw [hunfold, ← hD_def]
  -- Main case split on sign of Rtilde; dispatch to the corresponding case lemma.
  by_cases hrt_sign : 0 ≤ Rtilde
  · -- Case A: Rtilde ≥ 0 → R_FINAL = Rtilde.
    have hR_FINAL_Rt : (R_FINAL : ℤ) = Rtilde := hR_FINAL_Rtilde.1 hrt_sign
    have hMain_Z : ((Q_HI0 : ℤ) + 1) * D + R_FINAL
        = u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat := by
      rw [hR_FINAL_Rt, hRtilde_def]; ring
    by_cases hcase_hi : r1 ≥ ql
    · -- Case A-HI: output (qh0 + 1 - 1 + 1, x1, x0).
      rw [if_pos hcase_hi]
      obtain ⟨htest, hcorr, hrem⟩ := toNat_div3By2_case_A_HI
        hD_def hQ_HI0_def hD_Z_pos hD_lo hR_FINAL_def hR_FINAL_lt hR_FINAL_Rt
        hMain_Z hr1_ge_ql_iff hS_val hX_val hRtildeHi_disj hDIV_ub_Z hcase_hi
      rw [if_pos htest]; exact ⟨hcorr, hrem⟩
    · -- Case A-LO.
      rw [if_neg hcase_hi]
      by_cases hcase_ge_D : r1 > d1 ∨ (r1 = d1 ∧ r0 ≥ d0)
      · -- Case A-LO-ge: output (qh0 + 1 + 1, w1, w0).
        rw [if_pos hcase_ge_D]
        exact toNat_div3By2_case_A_LO_ge
          hD_def hQ_HI0_def hD_Z_pos hD_lo hR_FINAL_def hR_FINAL_lt hMain_Z
          hW_val hDIV_ub_Z hcase_ge_D
      · -- Case A-LO-lt: output (qh0 + 1, r1, r0).
        rw [if_neg hcase_ge_D]
        exact toNat_div3By2_case_A_LO_lt
          hD_def hQ_HI0_def hD_Z_pos hR_FINAL_def hMain_Z hDIV_ub_Z hcase_ge_D
  · -- Case B: Rtilde < 0 → R_FINAL = Rtilde + 2^128.
    push Not at hrt_sign
    have hR_FINAL_Rt : (R_FINAL : ℤ) = Rtilde + 2 ^ 128 := hR_FINAL_Rtilde.2 hrt_sign
    by_cases hcase_hi : r1 ≥ ql
    · -- Case B-HI: output (qh0 + 1 - 1, s1, s0).
      rw [if_pos hcase_hi]
      obtain ⟨hnot_test, hcorr, hrem⟩ := toNat_div3By2_case_B_HI
        hD_def hD_hi hQ_HI0_def hR_FINAL_lt hR_FINAL_Rt hRtilde_def hRt_ge_neg_D hS_val
      rw [if_neg hnot_test]; exact ⟨hcorr, hrem⟩
    · -- Case B-LO: impossible.
      exact (toNat_div3By2_case_B_LO hR_FINAL_def hR_FINAL_Rt hRt_ge_QLO_shift
        hr1_ge_ql_iff hcase_hi).elim

end UInt64
