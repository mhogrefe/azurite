import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Azurite.UInt64.WideMul
import Azurite.UInt64.Equiv.SplitHalves

set_option maxRecDepth 2000

namespace UInt64

private lemma hiHalf_toNat_eq (u : UInt64) : u.hiHalf.toNat = u.toNat / 2^32 := by
  unfold hiHalf
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_shiftRight,
      show ((32 : UInt64).toNat = 32) from rfl,
      show ((32 : Nat) % 64 = 32) from by decide,
      Nat.shiftRight_eq_div_pow]
  have hu : u.toNat < 2^64 := _root_.UInt64.toNat_lt u
  have hdiv : u.toNat / 2^32 < 2^32 := by
    apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32) |>.mpr
    rw [show (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 from by rw [← Nat.pow_add]]
    exact hu
  exact Nat.mod_eq_of_lt hdiv

private lemma loHalf_toNat_eq (u : UInt64) : u.loHalf.toNat = u.toNat % 2^32 := by
  unfold loHalf
  rw [_root_.UInt64.toNat_toUInt32]

/-- Adding a conditional value equals the conditional of the additions.
Bridges the branchless carry shape used by the implementations
(`z + (if P then w else 0)`, which codegen keeps scalar) to the branching
shape (`if P then z + w else z`) that the correctness proofs case on. -/
theorem add_ite_zero (z w : UInt64) (P : Prop) [Decidable P] :
    z + (if P then w else 0) = if P then z + w else z := by
  by_cases h : P <;> simp [h]

/-- Pure-Nat version of the wideMul correctness identity. -/
private lemma wideMul_nat_eq
    (Xh Xl Yh Yl : Nat) (hXh : Xh < 2^32) (hXl : Xl < 2^32) (hYh : Yh < 2^32) (hYl : Yl < 2^32)
    (M A : Nat) (hA_def : A = Xl * Yl) (hM_def : M = Xl * Yh + A / 2^32 + Xh * Yl)
    (K : Nat) (hK1 : K ≤ 1)
    (hK2 : K = 0 → M < 2^64)
    (hK3 : K = 1 → M ≥ 2^64) :
    (Xh * Yh + K * 2^32 + M % 2^64 / 2^32) * 2^64 +
        (M % 2^64 % 2^32 * 2^32 + A % 2^32)
      = (Xh * 2^32 + Xl) * (Yh * 2^32 + Yl) := by
  have hCY : Xh * Yl ≤ (2^32 - 1) * (2^32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hBY : Xl * Yh ≤ (2^32 - 1) * (2^32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hAY : Xl * Yl ≤ (2^32 - 1) * (2^32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hDY : Xh * Yh ≤ (2^32 - 1) * (2^32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hpow : ((2^32 - 1) * (2^32 - 1) : Nat) < 2^64 := by decide
  have hA_split : A / 2^32 * 2^32 + A % 2^32 = A := Nat.div_add_mod' A (2^32)
  have hM_split : M / 2^32 * 2^32 + M % 2^32 = M := Nat.div_add_mod' M (2^32)
  have hprod : (Xh * 2^32 + Xl) * (Yh * 2^32 + Yl)
            = Xh * Yh * 2^64 + Xh * Yl * 2^32 + Xl * Yh * 2^32 + A := by
    rw [hA_def]; ring
  rw [hprod]
  rcases (show K = 0 ∨ K = 1 by omega) with rfl | rfl
  · -- K = 0
    have hM_lt : M < 2^64 := hK2 rfl
    rw [Nat.mod_eq_of_lt hM_lt]
    have lhs_eq :
        (Xh * Yh + 0 * 2^32 + M / 2^32) * 2^64 + (M % 2^32 * 2^32 + A % 2^32)
          = Xh * Yh * 2^64 + (M / 2^32 * 2^32) * 2^32
              + M % 2^32 * 2^32 + A % 2^32 := by ring
    rw [lhs_eq]
    linarith
  · -- K = 1
    have hM_ge : M ≥ 2^64 := hK3 rfl
    have hAh_lt : A / 2^32 < 2^32 := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32)).mpr
      rw [hA_def]; omega
    have hM_lt2 : M < 2 * 2^64 := by
      rw [hM_def]
      omega
    have hmod_eq : M % 2^64 = M - 2^64 := by omega
    rw [hmod_eq]
    have hN_split : (M - 2^64) / 2^32 * 2^32 + (M - 2^64) % 2^32 = M - 2^64 :=
      Nat.div_add_mod' (M - 2^64) (2^32)
    have hNMod : (M - 2^64) % 2^32 = M % 2^32 := by
      have h1 : M = (M - 2^64) + 2^64 := by omega
      conv_rhs => rw [h1]
      rw [Nat.add_mod, show ((2^64 : Nat) % 2^32 = 0) from by decide, Nat.add_zero, Nat.mod_mod]
    -- Key: (M-2^64)/2^32*2^32*2^32 + (M-2^64)%2^32*2^32 = (M-2^64)*2^32 = M*2^32 - 2^64*2^32
    have hN_mul : (M - 2^64) / 2^32 * 2^32 * 2^32 + (M - 2^64) % 2^32 * 2^32
                = M * 2^32 - 2^64 * 2^32 := by
      calc (M - 2^64) / 2^32 * 2^32 * 2^32 + (M - 2^64) % 2^32 * 2^32
          = ((M - 2^64) / 2^32 * 2^32 + (M - 2^64) % 2^32) * 2^32 := by ring
        _ = (M - 2^64) * 2^32 := by rw [hN_split]
        _ = M * 2^32 - 2^64 * 2^32 := by rw [Nat.sub_mul]
    have hM_times : M * 2^32 = Xl * Yh * 2^32 + A / 2^32 * 2^32 + Xh * Yl * 2^32 := by
      rw [hM_def]; ring
    calc (Xh * Yh + 1 * 2^32 + (M - 2^64) / 2^32) * 2^64
            + ((M - 2^64) % 2^32 * 2^32 + A % 2^32)
        = Xh * Yh * 2^64 + 2^32 * 2^64
            + ((M - 2^64) / 2^32 * 2^32) * 2^32
            + (M - 2^64) % 2^32 * 2^32 + A % 2^32 := by ring
      _ = Xh * Yh * 2^64 + 2^32 * 2^64 + (M * 2^32 - 2^64 * 2^32) + A % 2^32 := by
            rw [show
              Xh * Yh * 2^64 + 2^32 * 2^64
                + ((M - 2^64) / 2^32 * 2^32) * 2^32
                + (M - 2^64) % 2^32 * 2^32 + A % 2^32
              = Xh * Yh * 2^64 + 2^32 * 2^64
                + ((M - 2^64) / 2^32 * 2^32 * 2^32 + (M - 2^64) % 2^32 * 2^32)
                + A % 2^32 from by ring, hN_mul]
      _ = Xh * Yh * 2^64 + M * 2^32 + A % 2^32 := by
            have h1 : 2^64 * 2^32 ≤ M * 2^32 :=
              Nat.mul_le_mul_right _ hM_ge
            have h2 : (2^32 : Nat) * 2^64 = 2^64 * 2^32 := by ring
            have h3 : (2^32 : Nat) * 2^64 + (M * 2^32 - 2^64 * 2^32) = M * 2^32 := by
              rw [h2]; exact Nat.add_sub_cancel' h1
            linarith [h3]
      _ = Xh * Yh * 2^64 + Xl * Yh * 2^32 + Xh * Yl * 2^32
            + (A / 2^32 * 2^32 + A % 2^32) := by rw [hM_times]; ring
      _ = Xh * Yh * 2^64 + Xl * Yh * 2^32 + Xh * Yl * 2^32 + A := by rw [hA_split]
      _ = Xh * Yh * 2^64 + Xh * Yl * 2^32 + Xl * Yh * 2^32 + A := by ring

theorem toNat_wideMul (x y : UInt64) :
    (wideMul x y).1.toNat * 2^64 + (wideMul x y).2.toNat = x.toNat * y.toNat := by
  -- Bounds
  have hXh : x.hiHalf.toNat < 2^32 := _root_.UInt32.toNat_lt _
  have hXl : x.loHalf.toNat < 2^32 := _root_.UInt32.toNat_lt _
  have hYh : y.hiHalf.toNat < 2^32 := _root_.UInt32.toNat_lt _
  have hYl : y.loHalf.toNat < 2^32 := _root_.UInt32.toNat_lt _
  -- x and y decomposition
  have hx : x.toNat = x.hiHalf.toNat * 2^32 + x.loHalf.toNat := by
    rw [hiHalf_toNat_eq, loHalf_toNat_eq]
    have := Nat.div_add_mod x.toNat (2^32); omega
  have hy : y.toNat = y.hiHalf.toNat * 2^32 + y.loHalf.toNat := by
    rw [hiHalf_toNat_eq, loHalf_toNat_eq]
    have := Nat.div_add_mod y.toNat (2^32); omega
  -- Half-products fit in 64 bits
  have hpow : ((2^32 - 1) * (2^32 - 1) : Nat) < 2^64 := by decide
  have hA : (x.loHalf.toUInt64 * y.loHalf.toUInt64).toNat
            = x.loHalf.toNat * y.loHalf.toNat := by
    rw [_root_.UInt64.toNat_mul, _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt64]
    apply Nat.mod_eq_of_lt
    have : x.loHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hB : (x.loHalf.toUInt64 * y.hiHalf.toUInt64).toNat
            = x.loHalf.toNat * y.hiHalf.toNat := by
    rw [_root_.UInt64.toNat_mul, _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt64]
    apply Nat.mod_eq_of_lt
    have : x.loHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hC : (x.hiHalf.toUInt64 * y.loHalf.toUInt64).toNat
            = x.hiHalf.toNat * y.loHalf.toNat := by
    rw [_root_.UInt64.toNat_mul, _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt64]
    apply Nat.mod_eq_of_lt
    have : x.hiHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hD : (x.hiHalf.toUInt64 * y.hiHalf.toUInt64).toNat
            = x.hiHalf.toNat * y.hiHalf.toNat := by
    rw [_root_.UInt64.toNat_mul, _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt64]
    apply Nat.mod_eq_of_lt
    have : x.hiHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  -- hi-half of x₀y₀
  have hAh_lt : x.loHalf.toNat * y.loHalf.toNat / 2^32 < 2^32 := by
    have : x.loHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32)).mpr (by omega)
  have hAh : (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toNat
            = x.loHalf.toNat * y.loHalf.toNat / 2^32 := by
    rw [hiHalf_toNat_eq, hA]
  have hAl : (x.loHalf.toUInt64 * y.loHalf.toUInt64).loHalf.toNat
            = x.loHalf.toNat * y.loHalf.toNat % 2^32 := by
    rw [loHalf_toNat_eq, hA]
  -- middle1 = x₀y₁ + (x₀y₀)hi, fits in 64 bits
  have hmiddle1_sum_lt :
      x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32 < 2^64 := by
    have : x.loHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmiddle1 :
      (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
          (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64).toNat
        = x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32 := by
    rw [_root_.UInt64.toNat_add, hB, _root_.UInt32.toNat_toUInt64, hAh]
    exact Nat.mod_eq_of_lt hmiddle1_sum_lt
  -- middle2 toNat
  have hmiddle2 :
      (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
            (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
          x.hiHalf.toUInt64 * y.loHalf.toUInt64).toNat
        = (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
            + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 := by
    rw [_root_.UInt64.toNat_add, hmiddle1, hC]
  -- wideHiHalf middle2
  have hwideHi :
      (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
            (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
          x.hiHalf.toUInt64 * y.loHalf.toUInt64).wideHiHalf.toNat
        = (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
            + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 / 2^32 := by
    unfold wideHiHalf
    rw [_root_.UInt64.toNat_shiftRight,
        show ((32 : UInt64).toNat = 32) from rfl,
        show ((32 : Nat) % 64 = 32) from by decide,
        Nat.shiftRight_eq_div_pow, hmiddle2]
  -- loHalf middle2
  have hloHi :
      (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
            (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
          x.hiHalf.toUInt64 * y.loHalf.toUInt64).loHalf.toNat
        = (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
            + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 % 2^32 := by
    rw [loHalf_toNat_eq, hmiddle2]
  -- 1 <<< 32 as UInt64
  have hone_shl : ((1 : UInt64) <<< 32).toNat = 2^32 := by
    rw [_root_.UInt64.toNat_shiftLeft, show ((32 : UInt64).toNat = 32) from rfl,
        show ((32 : Nat) % 64 = 32) from by decide,
        show ((1 : UInt64).toNat = 1) from rfl]
    decide
  -- Carry condition
  have hcarry_iff :
      (decide (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
                  (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
                x.hiHalf.toUInt64 * y.loHalf.toUInt64 <
              x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
                (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64) = true)
        ↔ x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
            + x.hiHalf.toNat * y.loHalf.toNat ≥ 2^64 := by
    rw [decide_eq_true_eq, _root_.UInt64.lt_iff_toNat_lt, hmiddle2, hmiddle1]
    have hBY : x.loHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hCY : x.hiHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · intro h
      have : (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat) % 2^64
              = x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat - 2^64 := by omega
      rw [this]
      omega
  -- z₀.toNat
  have hz0 :
      (joinHalves
          (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
                (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
              x.hiHalf.toUInt64 * y.loHalf.toUInt64).loHalf
          (x.loHalf.toUInt64 * y.loHalf.toUInt64).loHalf).toNat
        = (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
            + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 % 2^32 * 2^32
          + x.loHalf.toNat * y.loHalf.toNat % 2^32 := by
    rw [toNat_joinHalves, hloHi, hAl]
  -- Now unfold wideMul (defeq: delta + pair projections + lets) and
  -- reduce to wideMul_nat_eq
  show (x.hiHalf.toUInt64 * y.hiHalf.toUInt64 +
        (if decide (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
              (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
              x.hiHalf.toUInt64 * y.loHalf.toUInt64 <
            x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
              (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64) = true
          then (1 : UInt64) <<< 32 else 0) +
        (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
            (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
          x.hiHalf.toUInt64 * y.loHalf.toUInt64).wideHiHalf).toNat * 2^64 +
      (joinHalves
          (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
              (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
            x.hiHalf.toUInt64 * y.loHalf.toUInt64).loHalf
          (x.loHalf.toUInt64 * y.loHalf.toUInt64).loHalf).toNat
    = x.toNat * y.toNat
  rw [add_ite_zero]
  split_ifs with h_if
  · -- carry = true
    have hK_true :
        x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
          + x.hiHalf.toNat * y.loHalf.toNat ≥ 2^64 := hcarry_iff.mp h_if
    -- D + 2^32 doesn't overflow
    have hD_plus_lt : x.hiHalf.toNat * y.hiHalf.toNat + 2^32 < 2^64 := by
      have : x.hiHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have hD_plus :
        (x.hiHalf.toUInt64 * y.hiHalf.toUInt64 + (1 : UInt64) <<< 32).toNat
          = x.hiHalf.toNat * y.hiHalf.toNat + 2^32 := by
      rw [_root_.UInt64.toNat_add, hD, hone_shl]
      exact Nat.mod_eq_of_lt hD_plus_lt
    -- z₁ doesn't overflow
    have hz1_lt :
        x.hiHalf.toNat * y.hiHalf.toNat + 2^32
          + (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
              + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 / 2^32 < 2^64 := by
      have hmod : (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                    + x.hiHalf.toNat * y.loHalf.toNat) % 2^64
                = x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                    + x.hiHalf.toNat * y.loHalf.toNat - 2^64 := by
        have hBY : x.loHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have hCY : x.hiHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have hAY : x.loHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      rw [hmod]
      have h1 : x.loHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : x.hiHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : x.hiHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hAY : x.loHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hAh_lt' : x.loHalf.toNat * y.loHalf.toNat / 2^32 < 2^32 :=
        (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32)).mpr (by omega)
      have hM_ub : x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                    + x.hiHalf.toNat * y.loHalf.toNat
                  ≤ 2 * ((2^32 - 1) * (2^32 - 1)) + (2^32 - 1) := by omega
      have h4 : (2 * ((2^32 - 1) * (2^32 - 1)) + (2^32 - 1) - 2^64) / 2^32 ≤ 2^32 - 2 := by decide
      have : (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
              + x.hiHalf.toNat * y.loHalf.toNat - 2^64) / 2^32 ≤ 2^32 - 2 :=
        le_trans (Nat.div_le_div_right (by omega)) h4
      omega
    have hz1 :
        (x.hiHalf.toUInt64 * y.hiHalf.toUInt64 + (1 : UInt64) <<< 32 +
            (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
                  (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
                x.hiHalf.toUInt64 * y.loHalf.toUInt64).wideHiHalf).toNat
          = x.hiHalf.toNat * y.hiHalf.toNat + 2^32
            + (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 / 2^32 := by
      rw [_root_.UInt64.toNat_add, hD_plus, hwideHi]
      exact Nat.mod_eq_of_lt hz1_lt
    rw [hz1, hz0, hx, hy]
    have := wideMul_nat_eq x.hiHalf.toNat x.loHalf.toNat y.hiHalf.toNat y.loHalf.toNat
              hXh hXl hYh hYl
              (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat)
              (x.loHalf.toNat * y.loHalf.toNat) rfl rfl 1 (by omega)
              (fun h => by omega) (fun _ => hK_true)
    linarith [this]
  · -- carry = false
    have hK_false : ¬ (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                        + x.hiHalf.toNat * y.loHalf.toNat ≥ 2^64) := fun h => h_if (hcarry_iff.mpr h)
    have hK_lt : x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                  + x.hiHalf.toNat * y.loHalf.toNat < 2^64 := by omega
    have hmod : (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                  + x.hiHalf.toNat * y.loHalf.toNat) % 2^64
              = x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                  + x.hiHalf.toNat * y.loHalf.toNat := Nat.mod_eq_of_lt hK_lt
    have hz1_lt :
        x.hiHalf.toNat * y.hiHalf.toNat
          + (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
              + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 / 2^32 < 2^64 := by
      rw [hmod]
      have h1 : x.loHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : x.hiHalf.toNat * y.loHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : x.hiHalf.toNat * y.hiHalf.toNat ≤ (2^32 - 1) * (2^32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hAh_lt' : x.loHalf.toNat * y.loHalf.toNat / 2^32 < 2^32 := hAh_lt
      have h4 : ((2^32 - 1) * (2^32 - 1) + (2^32 - 1) + (2^32 - 1) * (2^32 - 1)) / 2^32
                ≤ 2 * (2^32 - 1) := by decide
      have : (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat) / 2^32 ≤ 2 * (2^32 - 1) :=
        le_trans (Nat.div_le_div_right (by omega)) h4
      omega
    have hz1 :
        (x.hiHalf.toUInt64 * y.hiHalf.toUInt64 +
            (x.loHalf.toUInt64 * y.hiHalf.toUInt64 +
                  (x.loHalf.toUInt64 * y.loHalf.toUInt64).hiHalf.toUInt64 +
                x.hiHalf.toUInt64 * y.loHalf.toUInt64).wideHiHalf).toNat
          = x.hiHalf.toNat * y.hiHalf.toNat
            + (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat) % 2^64 / 2^32 := by
      rw [_root_.UInt64.toNat_add, hD, hwideHi]
      exact Nat.mod_eq_of_lt hz1_lt
    rw [hz1, hz0, hx, hy]
    have := wideMul_nat_eq x.hiHalf.toNat x.loHalf.toNat y.hiHalf.toNat y.loHalf.toNat
              hXh hXl hYh hYl
              (x.loHalf.toNat * y.hiHalf.toNat + x.loHalf.toNat * y.loHalf.toNat / 2^32
                + x.hiHalf.toNat * y.loHalf.toNat)
              (x.loHalf.toNat * y.loHalf.toNat) rfl rfl 0 (by omega)
              (fun _ => hK_lt) (fun h => by omega)
    linarith [this]

end UInt64
