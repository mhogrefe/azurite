import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Azurite.UInt64.Div2By1
import Azurite.UInt64.Equiv.Reciprocal
import Azurite.UInt64.Equiv.WideAdd
import Azurite.UInt64.Equiv.WideMul

namespace UInt64

/-- Theorem 2 of Möller–Granlund: given a normalized divisor `D` (`2^63 ≤ D < 2^64`),
a dividend `[HI, LO]` with `HI < D` and `LO < 2^64`, and a reciprocal `INV`
characterized by `(2^64 + INV) * D ≤ 2^128 - 1 < (2^64 + INV + 1) * D`, the candidate
remainder `rtilde := HI * 2^64 + LO − (qhi + 1) * D`, where `(qhi, qlo)` is the
128-bit representation of `(2^64 + INV) * HI + LO`, satisfies the tight bound
`max(2^64 − D, qlo + 1) − 2^64 ≤ rtilde < max(2^64 − D, qlo)`. -/
theorem div2By1_rtilde_bounds
    {D HI LO qhi qlo INV : ℕ}
    (hD_lo : 2 ^ 63 ≤ D) (hD_hi : D < 2 ^ 64)
    (hHI : HI < D) (hLO : LO < 2 ^ 64) (hqlo : qlo < 2 ^ 64)
    (hInv_lo : (2 ^ 64 + INV) * D ≤ 2 ^ 128 - 1)
    (hInv_hi : 2 ^ 128 - 1 < (2 ^ 64 + INV + 1) * D)
    (hSum : qhi * 2 ^ 64 + qlo = (2 ^ 64 + INV) * HI + LO) :
    max ((2 ^ 64 : ℤ) - D) ((qlo : ℤ) + 1) - 2 ^ 64
      ≤ (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D
    ∧ (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D
        < max ((2 ^ 64 : ℤ) - D) (qlo : ℤ) := by
  have hD_Z_lo : (2 ^ 63 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD_lo
  have hD_Z_hi : (D : ℤ) < 2 ^ 64 := by exact_mod_cast hD_hi
  have hHI_Z_lt : (HI : ℤ) < (D : ℤ) := by exact_mod_cast hHI
  have hLO_Z_lt : (LO : ℤ) < 2 ^ 64 := by exact_mod_cast hLO
  have hqlo_Z_lt : (qlo : ℤ) < 2 ^ 64 := by exact_mod_cast hqlo
  have hHI_nn : (0 : ℤ) ≤ (HI : ℤ) := by positivity
  have hLO_nn : (0 : ℤ) ≤ (LO : ℤ) := by positivity
  have hqlo_nn : (0 : ℤ) ≤ (qlo : ℤ) := by positivity
  have hINV_nn : (0 : ℤ) ≤ (INV : ℤ) := by positivity
  have hInv_lo_Z : ((2 ^ 64 : ℤ) + INV) * D + 1 ≤ 2 ^ 128 := by
    have h : (2 ^ 64 + INV) * D + 1 ≤ 2 ^ 128 := by omega
    exact_mod_cast h
  have hInv_hi_Z : (2 ^ 128 : ℤ) ≤ ((2 ^ 64 : ℤ) + INV + 1) * D := by
    have h : (2 ^ 128 : ℕ) ≤ (2 ^ 64 + INV + 1) * D := by omega
    exact_mod_cast h
  have hSum_Z : (qhi : ℤ) * 2 ^ 64 + qlo = ((2 ^ 64 : ℤ) + INV) * HI + LO := by
    exact_mod_cast hSum
  have h2_64_D_nn : (0 : ℤ) ≤ (2 ^ 64 : ℤ) - D := by linarith
  have h2_64_D_pos : (1 : ℤ) ≤ (2 ^ 64 : ℤ) - D := by linarith
  have h2_64_qlo_pos : (1 : ℤ) ≤ (2 ^ 64 : ℤ) - qlo := by linarith
  have hk_ge : (1 : ℤ) ≤ 2 ^ 128 - ((2 ^ 64 : ℤ) + INV) * D := by linarith
  have hk_le : (2 ^ 128 : ℤ) - ((2 ^ 64 : ℤ) + INV) * D ≤ (D : ℤ) := by linarith
  have hkHI : (0 : ℤ) ≤ (2 ^ 128 - ((2 ^ 64 : ℤ) + INV) * D) * HI :=
    mul_nonneg (by linarith) hHI_nn
  have hLO2D : (0 : ℤ) ≤ (LO : ℤ) * ((2 ^ 64 : ℤ) - D) :=
    mul_nonneg hLO_nn h2_64_D_nn
  have hqlD : (0 : ℤ) ≤ (qlo : ℤ) * D := mul_nonneg hqlo_nn (by linarith)
  have h2_64_pos : (0 : ℤ) < 2 ^ 64 := by norm_num
  -- Key identity:
  -- (HI * 2^64 + LO - (qhi+1)*D) * 2^64
  --   = k * HI + LO * (2^64 - D) + qlo * D - D * 2^64
  -- where k := 2^128 - (2^64 + INV) * D.
  have key :
      ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D) * 2 ^ 64
        = (2 ^ 128 - ((2 ^ 64 : ℤ) + INV) * D) * HI + LO * (2 ^ 64 - D)
          + qlo * D - D * 2 ^ 64 := by
    linear_combination -(D : ℤ) * hSum_Z
  refine ⟨?_, ?_⟩
  · -- Lower bound: max(2^64 - D, qlo + 1) - 2^64 ≤ rtilde
    have h_ge_neg_D : -(D : ℤ) ≤ (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D := by
      have hmul : -(D : ℤ) * 2 ^ 64
          ≤ ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D) * 2 ^ 64 := by linarith
      exact le_of_mul_le_mul_right hmul h2_64_pos
    -- (rtilde + 2^64 - qlo) * 2^64 = k*HI + LO*(2^64-D) + (2^64-qlo)*(2^64-D) ≥ 1.
    have h_prod_id :
        ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D + 2 ^ 64 - qlo) * 2 ^ 64
          = (2 ^ 128 - ((2 ^ 64 : ℤ) + INV) * D) * HI + LO * (2 ^ 64 - D)
            + (2 ^ 64 - qlo) * (2 ^ 64 - D) := by linarith [key]
    have h_pair : (1 : ℤ) ≤ ((2 ^ 64 : ℤ) - qlo) * ((2 ^ 64 : ℤ) - D) := by
      have := mul_le_mul h2_64_qlo_pos h2_64_D_pos (by norm_num) (by linarith)
      linarith
    have h_prod_ge_1 :
        (1 : ℤ) ≤ ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D + 2 ^ 64 - qlo) * 2 ^ 64 := by
      linarith [h_prod_id]
    have h_ge_qlo1_sub_264 :
        (qlo : ℤ) + 1 - 2 ^ 64 ≤ (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D := by
      by_contra hc
      push Not at hc
      have h_neg :
          (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D + 2 ^ 64 - qlo ≤ 0 := by linarith
      have h_prod_le :
          ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D + 2 ^ 64 - qlo) * 2 ^ 64 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h_neg (by linarith)
      linarith [h_prod_ge_1]
    by_cases h : (2 ^ 64 : ℤ) - D ≤ (qlo : ℤ) + 1
    · rw [max_eq_right h]; linarith
    · push Not at h; rw [max_eq_left (le_of_lt h)]; linarith
  · -- Upper bound: rtilde < max(2^64 - D, qlo)
    have h_HI_ub : (HI : ℤ) ≤ (D : ℤ) - 1 := by linarith
    have h_LO_ub : (LO : ℤ) ≤ 2 ^ 64 - 1 := by linarith
    have hbound1 :
        (2 ^ 128 - ((2 ^ 64 : ℤ) + INV) * D) * HI ≤ (D : ℤ) * (D - 1) := by
      have hk_HI : (2 ^ 128 - ((2 ^ 64 : ℤ) + INV) * D) * HI ≤ (D : ℤ) * HI :=
        mul_le_mul_of_nonneg_right hk_le hHI_nn
      have hHI_Dm1 : (D : ℤ) * HI ≤ (D : ℤ) * (D - 1) :=
        mul_le_mul_of_nonneg_left h_HI_ub (by linarith)
      linarith [hk_HI, hHI_Dm1]
    have hbound2 :
        (LO : ℤ) * ((2 ^ 64 : ℤ) - D) ≤ (2 ^ 64 - 1) * ((2 ^ 64 : ℤ) - D) :=
      mul_le_mul_of_nonneg_right h_LO_ub h2_64_D_nn
    have h_ub_sum :
        ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D) * 2 ^ 64
          ≤ (D : ℤ) * (D - 1) + (2 ^ 64 - 1) * ((2 ^ 64 : ℤ) - D) + qlo * D - D * 2 ^ 64 := by
      linarith [key, hbound1, hbound2]
    -- Simplify RHS to (2^64-D)^2 + qlo*D - 2^64.
    have h_rhs_eq :
        (D : ℤ) * (D - 1) + (2 ^ 64 - 1) * ((2 ^ 64 : ℤ) - D) + qlo * D - D * 2 ^ 64
          = ((2 ^ 64 : ℤ) - D) * ((2 ^ 64 : ℤ) - D) + qlo * D - 2 ^ 64 := by ring
    rw [h_rhs_eq] at h_ub_sum
    rcases le_total ((2 ^ 64 : ℤ) - D) ((qlo : ℤ)) with h | h
    · rw [max_eq_right h]
      have hrel : ((2 ^ 64 : ℤ) - D) * ((2 ^ 64 : ℤ) - D) ≤ qlo * ((2 ^ 64 : ℤ) - D) :=
        mul_le_mul_of_nonneg_right h h2_64_D_nn
      have h_prod_le :
          ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D) * 2 ^ 64
            ≤ ((qlo : ℤ) - 1) * 2 ^ 64 := by nlinarith [h_ub_sum, hrel]
      have h_le : (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D ≤ (qlo : ℤ) - 1 :=
        le_of_mul_le_mul_right h_prod_le h2_64_pos
      linarith
    · rw [max_eq_left h]
      have hrel : (qlo : ℤ) * D ≤ ((2 ^ 64 : ℤ) - D) * D :=
        mul_le_mul_of_nonneg_right h (by linarith)
      have h_prod_le :
          ((HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D) * 2 ^ 64
            ≤ (((2 ^ 64 : ℤ) - D) - 1) * 2 ^ 64 := by nlinarith [h_ub_sum, hrel]
      have h_le : (HI : ℤ) * 2 ^ 64 + LO - ((qhi : ℤ) + 1) * D ≤ ((2 ^ 64 : ℤ) - D) - 1 :=
        le_of_mul_le_mul_right h_prod_le h2_64_pos
      linarith

/-- `HI * 2^64 + LO < D * 2^64` when `HI < D` and `LO < 2^64`. -/
private lemma div2By1_HI_mul_lt {D HI LO : ℕ} (hHI : HI < D) (hLO : LO < 2 ^ 64) :
    (HI : ℤ) * 2 ^ 64 + LO < (D : ℤ) * 2 ^ 64 := by
  have hHI_Z : (HI : ℤ) + 1 ≤ D := by exact_mod_cast hHI
  have hLO_Z : (LO : ℤ) < 2 ^ 64 := by exact_mod_cast hLO
  nlinarith only [hHI_Z, hLO_Z]

/-- When `Rtilde = HI*2^64 + LO - (Q_HI0+1)*D ≥ 0`, we have `Q_HI0 + 1 < 2^64`. -/
private lemma div2By1_Q_HI0_plus_one_lt
    {D HI LO Q_HI0 : ℕ}
    (hHI : HI < D) (hLO : LO < 2 ^ 64) (hD_pos : 0 < D)
    (hRt_nn : 0 ≤ (HI : ℤ) * 2 ^ 64 + LO - ((Q_HI0 : ℤ) + 1) * D) :
    Q_HI0 + 1 < 2 ^ 64 := by
  have hMle : ((Q_HI0 : ℤ) + 1) * D ≤ HI * 2 ^ 64 + LO := by linarith only [hRt_nn]
  have hHIbound : (HI : ℤ) * 2 ^ 64 + LO < (D : ℤ) * 2 ^ 64 := div2By1_HI_mul_lt hHI hLO
  have hD_pos_Z : (0 : ℤ) < D := by exact_mod_cast hD_pos
  have hQ_lt_Z : ((Q_HI0 : ℤ) + 1) * D < (2 ^ 64 : ℤ) * D := by
    linarith only [hMle, hHIbound]
  have hQ_lt : (Q_HI0 : ℤ) + 1 < 2 ^ 64 :=
    lt_of_mul_lt_mul_right hQ_lt_Z hD_pos_Z.le
  exact_mod_cast hQ_lt

/-- Helper: `(2^64 - D + R1N) % 2^64 = R1N - D` when `D ≤ R1N < 2^64`. -/
private lemma div2By1_sub_add_mod {D R1N : ℕ} (hD_lt : D < 2 ^ 64)
    (hR1N_lt : R1N < 2 ^ 64) (hD_le_R1N : D ≤ R1N) :
    (2 ^ 64 - D + R1N) % 2 ^ 64 = R1N - D := by
  have h : 2 ^ 64 - D + R1N = 2 ^ 64 + (R1N - D) := by omega
  rw [h, Nat.add_mod_left]; omega

/-- Helper: when `R1N + D ≥ 2^64` (and both `< 2^64`), `(R1N + D) % 2^64 = R1N + D - 2^64`. -/
private lemma div2By1_add_mod_overflow {D R1N : ℕ}
    (hR1N_lt : R1N < 2 ^ 64) (hD_lt : D < 2 ^ 64) (hge : 2 ^ 64 ≤ R1N + D) :
    (R1N + D) % 2 ^ 64 = R1N + D - 2 ^ 64 := by
  have h : R1N + D = 2 ^ 64 + (R1N + D - 2 ^ 64) := by omega
  rw [h, Nat.add_mod_left]; omega

/-- Rtilde < 0 branch arithmetic: bundles the three facts needed about `R1N + D`
when `R1N = Rtilde + 2^64` and `-D ≤ Rtilde < 0`. -/
private lemma div2By1_neg_branch {D R1N : ℕ} {Rtilde : ℤ}
    (hD_lt : D < 2 ^ 64) (hR1N_lt : R1N < 2 ^ 64)
    (hrt_sign : Rtilde < 0) (hR1N_Rt : (R1N : ℤ) = Rtilde + 2 ^ 64)
    (hRt_lo : -(D : ℤ) ≤ Rtilde) :
    2 ^ 64 ≤ R1N + D ∧ (R1N + D) % 2 ^ 64 = R1N + D - 2 ^ 64
      ∧ R1N + D - 2 ^ 64 < D := by
  have hge_Z : (2 ^ 64 : ℤ) ≤ (R1N : ℤ) + D := by linarith only [hR1N_Rt, hRt_lo]
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := Int.natCast_nonneg _
  have hge : 2 ^ 64 ≤ R1N + D := by exact_mod_cast hge_Z
  refine ⟨hge, div2By1_add_mod_overflow hR1N_lt hD_lt hge, ?_⟩
  have hlt_Z : ((R1N + D - 2 ^ 64 : ℕ) : ℤ) < D := by
    rw [Nat.cast_sub hge]; push_cast; linarith only [hR1N_Rt, hrt_sign]
  exact_mod_cast hlt_Z

/-- Nat identity for the Rtilde < 0 branch final step:
    `Q_HI0 * D + (R1N + D - 2^64) = HI * 2^64 + LO`. -/
private lemma div2By1_neg_branch_eq {D HI LO Q_HI0 R1N : ℕ} {Rtilde M : ℤ}
    (hge : 2 ^ 64 ≤ R1N + D)
    (hR1N_Rt : (R1N : ℤ) = Rtilde + 2 ^ 64)
    (hRt_Z : Rtilde = (HI : ℤ) * 2 ^ 64 + LO - M)
    (hM_Z_eq : (M : ℤ) = ((Q_HI0 : ℤ) + 1) * D) :
    Q_HI0 * D + (R1N + D - 2 ^ 64) = HI * 2 ^ 64 + LO := by
  have hZ : ((Q_HI0 * D + (R1N + D - 2 ^ 64) : ℕ) : ℤ)
      = ((HI * 2 ^ 64 + LO : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_sub hge]
    push_cast
    linarith only [hR1N_Rt, hRt_Z, hM_Z_eq]
  exact_mod_cast hZ

/-- When `Rtilde = HI*2^64 + LO - (Q_HI0+1)*D ≥ D`, we have `Q_HI0 + 2 < 2^64`. -/
private lemma div2By1_Q_HI0_plus_two_lt
    {D HI LO Q_HI0 : ℕ}
    (hHI : HI < D) (hLO : LO < 2 ^ 64) (hD_pos : 0 < D)
    (hRt_ge_D : (D : ℤ) ≤ (HI : ℤ) * 2 ^ 64 + LO - ((Q_HI0 : ℤ) + 1) * D) :
    Q_HI0 + 2 < 2 ^ 64 := by
  have hMD_le : ((Q_HI0 : ℤ) + 2) * D ≤ (HI : ℤ) * 2 ^ 64 + LO := by
    have hexp : ((Q_HI0 : ℤ) + 2) * D = ((Q_HI0 : ℤ) + 1) * D + D := by ring
    linarith only [hRt_ge_D, hexp]
  have hHIbound : (HI : ℤ) * 2 ^ 64 + LO < (D : ℤ) * 2 ^ 64 := div2By1_HI_mul_lt hHI hLO
  have hD_pos_Z : (0 : ℤ) < D := by exact_mod_cast hD_pos
  have hlt : ((Q_HI0 : ℤ) + 2) * D < (2 ^ 64 : ℤ) * D := by
    linarith only [hMD_le, hHIbound]
  have : (Q_HI0 : ℤ) + 2 < 2 ^ 64 := lt_of_mul_lt_mul_right hlt hD_pos_Z.le
  exact_mod_cast this

/-- Correctness of `div2By1` (Möller–Granlund Algorithm 4): for a normalized 64-bit
divisor `d` (`2^63 ≤ d.toNat`), a 128-bit dividend `(hi, lo)` with `hi.toNat < d.toNat`,
and the precomputed reciprocal `inv = reciprocal d hd`, the returned pair `(q, r)`
satisfies `q * d + r = hi * 2^64 + lo` and `r < d`. -/
theorem toNat_div2By1 (hi lo d inv : UInt64)
    (hd : 2 ^ 63 ≤ d.toNat)
    (hhi : hi.toNat < d.toNat)
    (hinv : inv = reciprocal d hd) :
    (div2By1 hi lo d inv).1.toNat * d.toNat + (div2By1 hi lo d inv).2.toNat
        = hi.toNat * 2 ^ 64 + lo.toNat
    ∧ (div2By1 hi lo d inv).2.toNat < d.toNat := by
  set D : ℕ := d.toNat with hD_def
  set HI : ℕ := hi.toNat with hHI_def
  set LO : ℕ := lo.toNat with hLO_def
  set INV : ℕ := inv.toNat with hINV_def
  have hD_lt : D < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hLO_lt : LO < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hHI_lt_264 : HI < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hINV_lt : INV < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_pos : 0 < D := by omega
  have hHI_D : HI < D := hhi
  -- Relate INV to the reciprocal specification.
  have hINV_val : INV = (2 ^ 128 - 1) / D - 2 ^ 64 := by
    rw [hINV_def, hinv]; exact toNat_reciprocal d hd
  have h_2_64_D_le : 2 ^ 64 * D ≤ 2 ^ 128 - 1 := by
    have h1 : 2 ^ 64 * D ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (2 : ℕ) ^ 64 * (2 ^ 64 - 1) = 2 ^ 128 - 2 ^ 64 := by
      have : (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 := by norm_num
      omega
    omega
  have h_RD_ge : 2 ^ 64 ≤ (2 ^ 128 - 1) / D := by
    rw [Nat.le_div_iff_mul_le hD_pos]; linarith
  have hINV_eq : 2 ^ 64 + INV = (2 ^ 128 - 1) / D := by
    rw [hINV_val]; omega
  have hInv_lo : (2 ^ 64 + INV) * D ≤ 2 ^ 128 - 1 := by
    rw [hINV_eq]; exact Nat.div_mul_le_self _ _
  have hInv_hi : 2 ^ 128 - 1 < (2 ^ 64 + INV + 1) * D := by
    rw [hINV_eq]
    have hdm : (2 ^ 128 - 1) / D * D + (2 ^ 128 - 1) % D = 2 ^ 128 - 1 :=
      Nat.div_add_mod' _ _
    have hmod_lt : (2 ^ 128 - 1) % D < D := Nat.mod_lt _ hD_pos
    have : ((2 ^ 128 - 1) / D + 1) * D = (2 ^ 128 - 1) / D * D + D := by ring
    omega
  -- Compute wideMul inv hi.
  have hWM : (wideMul inv hi).1.toNat * 2 ^ 64 + (wideMul inv hi).2.toNat = INV * HI :=
    toNat_wideMul inv hi
  have hWM1_lt : (wideMul inv hi).1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hWM2_lt : (wideMul inv hi).2.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  -- Compute wideAdd (wideMul inv hi) (hi, lo). Destructure directly so that the
  -- match in the definition of `div2By1` reduces.
  rcases hQPeq : wideAdd (wideMul inv hi) (hi, lo) with ⟨qh0, ql⟩
  set Q_HI0 : ℕ := qh0.toNat with hQ_HI0_def
  set Q_LO : ℕ := ql.toNat with hQ_LO_def
  have hQ_HI0_lt : Q_HI0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hQ_LO_lt : Q_LO < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hQPadd : Q_HI0 * 2 ^ 64 + Q_LO
      = ((wideMul inv hi).1.toNat * 2 ^ 64 + (wideMul inv hi).2.toNat
          + (HI * 2 ^ 64 + LO)) % 2 ^ 128 := by
    have := toNat_wideAdd (wideMul inv hi) (hi, lo)
    rw [hQPeq] at this
    exact this
  -- (2^64 + INV) * HI + LO < 2^128 so the mod is a no-op.
  have h_sum_lt : (2 ^ 64 + INV) * HI + LO < 2 ^ 128 := by
    have hle : (2 ^ 64 + INV) * HI ≤ (2 ^ 64 + INV) * (D - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have heq : (2 ^ 64 + INV) * (D - 1) + (2 ^ 64 + INV) = (2 ^ 64 + INV) * D := by
      have : 0 < D := hD_pos
      have hh : (2 ^ 64 + INV) * D = (2 ^ 64 + INV) * ((D - 1) + 1) := by
        congr 1; omega
      rw [hh]; ring
    have : (2 ^ 64 + INV) * HI + LO ≤ (2 ^ 64 + INV) * D - (2 ^ 64 + INV) + LO := by omega
    have h64 : 2 ^ 64 ≤ 2 ^ 64 + INV := by omega
    have : (2 ^ 64 + INV) * HI + LO ≤ 2 ^ 128 - 1 - 2 ^ 64 + LO := by omega
    omega
  have hQP_val : Q_HI0 * 2 ^ 64 + Q_LO = (2 ^ 64 + INV) * HI + LO := by
    rw [hQPadd, hWM]
    have heq : INV * HI + (HI * 2 ^ 64 + LO) = (2 ^ 64 + INV) * HI + LO := by ring
    rw [heq]
    exact Nat.mod_eq_of_lt h_sum_lt
  -- Apply Theorem 2 to obtain rtilde bounds.
  have hbounds := div2By1_rtilde_bounds (D := D) (HI := HI) (LO := LO)
    (qhi := Q_HI0) (qlo := Q_LO) (INV := INV)
    hd hD_lt hHI_D hLO_lt hQ_LO_lt hInv_lo hInv_hi hQP_val
  obtain ⟨hRtildeLo, hRtildeHi⟩ := hbounds
  -- Let Q' = Q_HI0 + 1 be the tentative quotient (integer); Rtilde = HI*2^64 + LO - Q'*D.
  -- Define the algorithm's intermediate values.
  set Q1 : UInt64 := qh0 + 1 with hQ1_def
  set R1 : UInt64 := lo - Q1 * d with hR1_def
  set Q1N : ℕ := Q1.toNat with hQ1N_def
  set R1N : ℕ := R1.toNat with hR1N_def
  have hQ1N : Q1N = (Q_HI0 + 1) % 2 ^ 64 := by
    rw [hQ1N_def, hQ1_def, _root_.UInt64.toNat_add]; rfl
  have hR1N : R1N = (2 ^ 64 - Q1N * D % 2 ^ 64 + LO) % 2 ^ 64 := by
    rw [hR1N_def, hR1_def, _root_.UInt64.toNat_sub, _root_.UInt64.toNat_mul]
  -- The integer "rtilde" = HI*2^64 + LO - (Q_HI0+1)*D.
  set Rtilde : ℤ := (HI : ℤ) * 2 ^ 64 + LO - ((Q_HI0 : ℤ) + 1) * D with hRtilde_def
  -- Algorithm has the form: split on R1 > ql, then on r ≥ d.
  have hunfold :
      div2By1 hi lo d inv
        = if R1 > ql then
            if R1 + d ≥ d then (Q1 - 1 + 1, R1 + d - d) else (Q1 - 1, R1 + d)
          else
            if R1 ≥ d then (Q1 + 1, R1 - d) else (Q1, R1) := by
    simp only [div2By1, hQPeq]
    split_ifs <;> rfl
  rw [hunfold]
  -- Common lemmas used in every branch.
  have hQ1N_lt : Q1N < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hR1N_lt : R1N < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hD_one : (1 : UInt64).toNat = 1 := rfl
  -- (Q_HI0 + 1) mod 2^64 = Q1N.
  have hQ1N' : Q1N = (Q_HI0 + 1) % 2 ^ 64 := hQ1N
  -- Q1N * D mod 2^64 = (Q_HI0 + 1) * D mod 2^64.
  have h_Q1D_mod : (Q1N * D) % 2 ^ 64 = ((Q_HI0 + 1) * D) % 2 ^ 64 := by
    conv_lhs => rw [Nat.mul_mod, hQ1N', Nat.mod_mod]
    rw [← Nat.mul_mod]
  -- R1N = (2^64 - ((Q_HI0+1)*D) % 2^64 + LO) % 2^64.
  have hR1N' : R1N = (2 ^ 64 - ((Q_HI0 + 1) * D) % 2 ^ 64 + LO) % 2 ^ 64 := by
    rw [hR1N, h_Q1D_mod]
  -- Set M := (Q_HI0 + 1) * D.
  set M : ℕ := (Q_HI0 + 1) * D with hM_def
  have hMmod_lt : M % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hM_div_mod : M / 2 ^ 64 * 2 ^ 64 + M % 2 ^ 64 = M := Nat.div_add_mod' _ _
  -- Integer bounds and casts used in what follows.
  have hHI_Z_lt : (HI : ℤ) < 2 ^ 64 := by exact_mod_cast hHI_lt_264
  have hHI_Z_nn : (0 : ℤ) ≤ (HI : ℤ) := Int.natCast_nonneg _
  have hLO_Z_nn : (0 : ℤ) ≤ (LO : ℤ) := Int.natCast_nonneg _
  have hLO_Z_lt : (LO : ℤ) < 2 ^ 64 := by exact_mod_cast hLO_lt
  have hR1N_Z_nn : (0 : ℤ) ≤ (R1N : ℤ) := Int.natCast_nonneg _
  have hR1N_Z_lt : (R1N : ℤ) < 2 ^ 64 := by exact_mod_cast hR1N_lt
  have hMm_Z_lt : ((M % 2 ^ 64 : ℕ) : ℤ) < 2 ^ 64 := by exact_mod_cast hMmod_lt
  have hMm_Z_nn : (0 : ℤ) ≤ ((M % 2 ^ 64 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hMd_Z_nn : (0 : ℤ) ≤ ((M / 2 ^ 64 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hM_div_mod_Z :
      ((M / 2 ^ 64 : ℕ) : ℤ) * 2 ^ 64 + ((M % 2 ^ 64 : ℕ) : ℤ) = (M : ℤ) := by
    exact_mod_cast hM_div_mod
  have hD_Z_lt : (D : ℤ) < 2 ^ 64 := by exact_mod_cast hD_lt
  have hD_Z_nn : (0 : ℤ) ≤ (D : ℤ) := Int.natCast_nonneg _
  have hD_Z_lo : (2 ^ 63 : ℤ) ≤ D := by exact_mod_cast hd
  have hM_Z_eq : (M : ℤ) = ((Q_HI0 : ℤ) + 1) * D := by
    rw [hM_def]; push_cast; ring
  -- Rtilde in a form suitable for omega (with M as an atom).
  have hRt_Z : Rtilde = (HI : ℤ) * 2 ^ 64 + LO - M := by
    rw [hRtilde_def, hM_Z_eq]
  -- Bounds on Rtilde.
  have hRtilde_bound_hi : Rtilde < (2 ^ 64 : ℤ) := by
    have hQ_LO_Z_lt : (Q_LO : ℤ) < 2 ^ 64 := by exact_mod_cast hQ_LO_lt
    have hmax_le : max ((2 ^ 64 : ℤ) - D) (Q_LO : ℤ) ≤ (2 ^ 64 : ℤ) :=
      max_le (by linarith) (by linarith)
    linarith [hRtildeHi]
  have hRtilde_bound_lo : -(D : ℤ) ≤ Rtilde := by
    have h : (2 ^ 64 : ℤ) - D ≤ max ((2 ^ 64 : ℤ) - D) ((Q_LO : ℤ) + 1) := le_max_left _ _
    linarith [hRtildeLo]
  -- R1N and Rtilde are equal mod 2^64.
  have hR1N_Rtilde :
      (0 ≤ Rtilde → (R1N : ℤ) = Rtilde) ∧
      (Rtilde < 0 → (R1N : ℤ) = Rtilde + 2 ^ 64) := by
    by_cases hcase : M % 2 ^ 64 > LO
    · have hinner_lt : 2 ^ 64 - M % 2 ^ 64 + LO < 2 ^ 64 := by omega
      have hR1N_eq : R1N = 2 ^ 64 - M % 2 ^ 64 + LO := by
        rw [hR1N']; exact Nat.mod_eq_of_lt hinner_lt
      have hR1N_Z : (R1N : ℤ) = 2 ^ 64 - ((M % 2 ^ 64 : ℕ) : ℤ) + LO := by
        have hle : M % 2 ^ 64 ≤ 2 ^ 64 := le_of_lt hMmod_lt
        have := hR1N_eq
        omega
      have hcase_Z : ((M % 2 ^ 64 : ℕ) : ℤ) > LO := by exact_mod_cast hcase
      refine ⟨fun hrt_nn => ?_, fun hrt_neg => ?_⟩
      · omega
      · omega
    · push Not at hcase
      have hR1N_eq : R1N = LO - M % 2 ^ 64 := by
        rw [hR1N']
        have hrw : 2 ^ 64 - M % 2 ^ 64 + LO = 2 ^ 64 + (LO - M % 2 ^ 64) := by omega
        rw [hrw, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hR1N_Z : (R1N : ℤ) = (LO : ℤ) - ((M % 2 ^ 64 : ℕ) : ℤ) := by
        have := hR1N_eq
        omega
      have hcase_Z : ((M % 2 ^ 64 : ℕ) : ℤ) ≤ LO := by exact_mod_cast hcase
      refine ⟨fun hrt_nn => ?_, fun hrt_neg => ?_⟩
      · omega
      · omega
  -- UInt64 ↔ Nat conversions for comparisons and operations.
  have hR1_gt_ql_iff : (R1 > ql) ↔ Q_LO < R1N := _root_.UInt64.lt_iff_toNat_lt
  have hR1_ge_d_iff : (R1 ≥ d) ↔ D ≤ R1N := _root_.UInt64.le_iff_toNat_le
  have hR1plusd_toNat : (R1 + d).toNat = (R1N + D) % 2 ^ 64 := by
    rw [_root_.UInt64.toNat_add]
  have hR1d_ge_d_iff : (R1 + d ≥ d) ↔ D ≤ (R1N + D) % 2 ^ 64 := by
    rw [← hR1plusd_toNat]; exact _root_.UInt64.le_iff_toNat_le
  have hQ1sub1_toNat : (Q1 - 1).toNat = (2 ^ 64 - 1 + Q1N) % 2 ^ 64 := by
    rw [_root_.UInt64.toNat_sub]; rfl
  have hQ1sub1add1_toNat : (Q1 - 1 + 1).toNat = Q1N := by
    rw [_root_.UInt64.toNat_add, hQ1sub1_toNat]; omega
  have hQ1add1_toNat : (Q1 + 1).toNat = (Q1N + 1) % 2 ^ 64 := by
    rw [_root_.UInt64.toNat_add]; rfl
  have hR1plusdsubd_toNat : (R1 + d - d).toNat = R1N := by
    rw [_root_.UInt64.toNat_sub, hR1plusd_toNat]; omega
  have hR1subd_toNat : (R1 - d).toNat = (2 ^ 64 - D + R1N) % 2 ^ 64 := by
    rw [_root_.UInt64.toNat_sub]
  -- Lower bound: Rtilde ≥ Q_LO + 1 - 2^64 (from max(2^64-D, Q_LO+1)).
  have hRt_ge_QLO_shift : (Q_LO : ℤ) + 1 - 2 ^ 64 ≤ Rtilde := by
    have h : (Q_LO : ℤ) + 1 ≤ max ((2 ^ 64 : ℤ) - D) ((Q_LO : ℤ) + 1) := le_max_right _ _
    linarith [hRtildeLo]
  -- Upper bound as a disjunction.
  have hRtildeHi_disj : Rtilde < (2 ^ 64 : ℤ) - D ∨ Rtilde < (Q_LO : ℤ) :=
    lt_max_iff.mp hRtildeHi
  -- Clear hypotheses no longer needed to shrink the context for later tactics.
  clear hWM hWM1_lt hWM2_lt hQPadd h_sum_lt hQPeq hInv_lo hInv_hi hINV_val
    hINV_eq h_2_64_D_le h_RD_ge hM_div_mod hM_div_mod_Z hMd_Z_nn hMm_Z_nn
    hRtildeLo hRtildeHi
  -- Clear definitional values to prevent unfolding and speed up tactics.
  clear_value D HI LO INV Q_HI0 Q_LO M Q1N R1N Rtilde
  -- Main case split on sign of Rtilde.
  by_cases hrt_sign : 0 ≤ Rtilde
  · -- Rtilde ≥ 0. Then R1N = Rtilde.
    have hR1N_Rt : (R1N : ℤ) = Rtilde := hR1N_Rtilde.1 hrt_sign
    -- Derive Q_HI0 + 1 < 2^64.
    have hQplus1_lt : Q_HI0 + 1 < 2 ^ 64 :=
      div2By1_Q_HI0_plus_one_lt hHI_D hLO_lt hD_pos
        (by linarith only [hrt_sign, hRt_Z, hM_Z_eq])
    have hQ1N_eq : Q1N = Q_HI0 + 1 := by rw [hQ1N']; exact Nat.mod_eq_of_lt hQplus1_lt
    have hQ1N_Z : (Q1N : ℤ) = Q_HI0 + 1 := by exact_mod_cast hQ1N_eq
    -- Main algebraic identity: Q1N * D + R1N = HI * 2^64 + LO (as ℤ).
    have hMain_Z : ((Q1N : ℤ)) * D + R1N = HI * 2 ^ 64 + LO := by
      rw [hQ1N_Z, hR1N_Rt, hRtilde_def]; ring
    by_cases hcase1 : R1 > ql
    · rw [ite_eq_left hcase1]
      have hQLO_lt_R1N : Q_LO < R1N := hR1_gt_ql_iff.mp hcase1
      have hQLO_lt_Rt : (Q_LO : ℤ) < Rtilde := by
        have h : ((Q_LO : ℤ)) < ((R1N : ℤ)) := by exact_mod_cast hQLO_lt_R1N
        linarith only [h, hR1N_Rt]
      have hRt_lt_2_64_D : Rtilde < (2 ^ 64 : ℤ) - D := by
        rcases hRtildeHi_disj with h | h
        · exact h
        · linarith only [h, hQLO_lt_Rt]
      have hRt_lt_D : Rtilde < D := by linarith only [hRt_lt_2_64_D, hD_Z_lo]
      have hR1NplusD_lt : R1N + D < 2 ^ 64 := by
        have h : ((R1N + D : ℕ) : ℤ) < 2 ^ 64 := by
          push_cast; linarith only [hRt_lt_2_64_D, hR1N_Rt]
        exact_mod_cast h
      have hR1plusD_val : (R1N + D) % 2 ^ 64 = R1N + D := Nat.mod_eq_of_lt hR1NplusD_lt
      have hc2 : D ≤ (R1N + D) % 2 ^ 64 := by
        rw [hR1plusD_val]; exact Nat.le_add_left _ _
      have hcase2 : R1 + d ≥ d := hR1d_ge_d_iff.mpr hc2
      rw [ite_eq_left hcase2, hQ1sub1add1_toNat, hR1plusdsubd_toNat]
      refine ⟨?_, ?_⟩
      · have hZ : ((Q1N * D + R1N : ℕ) : ℤ) = ((HI * 2 ^ 64 + LO : ℕ) : ℤ) := by
          push_cast; exact hMain_Z
        exact_mod_cast hZ
      · have h : (R1N : ℤ) < D := by linarith only [hR1N_Rt, hRt_lt_D]
        exact_mod_cast h
    · rw [ite_eq_right hcase1]
      have hR1N_le_QLO : R1N ≤ Q_LO :=
        Nat.le_of_not_lt (fun h => hcase1 (hR1_gt_ql_iff.mpr h))
      by_cases hcase3 : R1 ≥ d
      · rw [ite_eq_left hcase3]
        have hD_le_R1N : D ≤ R1N := hR1_ge_d_iff.mp hcase3
        have hD_le_Rt : (D : ℤ) ≤ Rtilde := by
          have h : (D : ℤ) ≤ R1N := by exact_mod_cast hD_le_R1N
          linarith only [h, hR1N_Rt]
        -- Q_HI0 + 2 < 2^64.
        have hQplus2_lt : Q_HI0 + 2 < 2 ^ 64 :=
          div2By1_Q_HI0_plus_two_lt hHI_D hLO_lt hD_pos
            (by linarith only [hD_le_Rt, hRt_Z, hM_Z_eq])
        have hQ1add1_val : (Q1N + 1) % 2 ^ 64 = Q_HI0 + 2 := by
          rw [hQ1N_eq]; exact Nat.mod_eq_of_lt hQplus2_lt
        rw [hQ1add1_toNat, hR1subd_toNat, hQ1add1_val]
        have hR1subd_val : (2 ^ 64 - D + R1N) % 2 ^ 64 = R1N - D :=
          div2By1_sub_add_mod hD_lt hR1N_lt hD_le_R1N
        rw [hR1subd_val]
        refine ⟨?_, ?_⟩
        · have hZ : (((Q_HI0 + 2) * D + (R1N - D) : ℕ) : ℤ) = ((HI * 2 ^ 64 + LO : ℕ) : ℤ) := by
            push_cast
            rw [Nat.cast_sub hD_le_R1N]
            have h1 : ((Q_HI0 : ℤ) + 2) * D + (R1N - D) = (Q_HI0 + 1) * D + R1N := by ring
            rw [h1, ← hQ1N_Z]
            exact hMain_Z
          exact_mod_cast hZ
        · have h : (R1N : ℤ) < D + D := by
            linarith only [hR1N_Rt, hRtilde_bound_hi, hD_Z_lo]
          have h1 : R1N < D + D := by exact_mod_cast h
          exact Nat.sub_lt_left_of_lt_add hD_le_R1N h1
      · rw [ite_eq_right hcase3]
        have hR1N_lt_D : R1N < D :=
          Nat.lt_of_not_le (fun h => hcase3 (hR1_ge_d_iff.mpr h))
        show Q1.toNat * D + R1.toNat = HI * 2 ^ 64 + LO ∧ R1.toNat < D
        rw [← hQ1N_def, ← hR1N_def]
        refine ⟨?_, hR1N_lt_D⟩
        have hZ : ((Q1N * D + R1N : ℕ) : ℤ) = ((HI * 2 ^ 64 + LO : ℕ) : ℤ) := by
          push_cast; exact hMain_Z
        exact_mod_cast hZ
  · -- Rtilde < 0. R1N = Rtilde + 2^64.
    push Not at hrt_sign
    have hR1N_Rt : (R1N : ℤ) = Rtilde + 2 ^ 64 := hR1N_Rtilde.2 hrt_sign
    have hR1N_gt_QLO : Q_LO < R1N := by
      have h : (Q_LO : ℤ) < R1N := by
        rw [hR1N_Rt]; linarith only [hRt_ge_QLO_shift]
      exact Nat.cast_lt.mp h
    have hcase1 : R1 > ql := hR1_gt_ql_iff.mpr hR1N_gt_QLO
    rw [ite_eq_left hcase1]
    -- R1N + D ≥ 2^64, and (R1N + D) % 2^64 = R1N + D - 2^64 = Rtilde + D < D.
    obtain ⟨hR1ND_ge, hR1ND_val, hR1ND_lt_D⟩ :=
      div2By1_neg_branch hD_lt hR1N_lt hrt_sign hR1N_Rt hRtilde_bound_lo
    have hnot_c2 : ¬ D ≤ (R1N + D) % 2 ^ 64 := by
      rw [hR1ND_val]; exact Nat.not_le_of_lt hR1ND_lt_D
    have hcase2 : ¬ (R1 + d ≥ d) := fun h => hnot_c2 (hR1d_ge_d_iff.mp h)
    rw [ite_eq_right hcase2, hQ1sub1_toNat, hR1plusd_toNat]
    -- (2^64 - 1 + Q1N) % 2^64 = Q_HI0.
    have hQ1sub1_val : (2 ^ 64 - 1 + Q1N) % 2 ^ 64 = Q_HI0 := by
      rw [hQ1N']; omega
    rw [hQ1sub1_val, hR1ND_val]
    exact ⟨div2By1_neg_branch_eq hR1ND_ge hR1N_Rt hRt_Z hM_Z_eq, hR1ND_lt_D⟩

end UInt64
