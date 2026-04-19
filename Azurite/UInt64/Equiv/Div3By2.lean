import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Azurite.UInt64.Div3By2

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
  have hu2_nn : (0 : ℤ) ≤ (u2 : ℤ) := by positivity
  have hu1_nn : (0 : ℤ) ≤ (u1 : ℤ) := by positivity
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := by positivity
  have hq0_nn : (0 : ℤ) ≤ (q0 : ℤ) := by positivity
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := by positivity
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
  have hu2_nn : (0 : ℤ) ≤ (u2 : ℤ) := by positivity
  have hu1_nn : (0 : ℤ) ≤ (u1 : ℤ) := by positivity
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := by positivity
  have hq0_nn : (0 : ℤ) ≤ (q0 : ℤ) := by positivity
  have hd0_nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := by positivity
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
  have hu2_nn : (0 : ℤ) ≤ (u2 : ℤ) := by positivity
  have hu1_nn : (0 : ℤ) ≤ (u1 : ℤ) := by positivity
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := by positivity
  have hq0_nn : (0 : ℤ) ≤ (q0 : ℤ) := by positivity
  have hd0_nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := by positivity
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
  have hu0_nn : (0 : ℤ) ≤ (u0 : ℤ) := by positivity
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

end UInt64
