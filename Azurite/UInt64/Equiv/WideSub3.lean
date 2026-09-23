import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Azurite.UInt64.Equiv.SubWithBorrow
import Azurite.UInt64.WideSub3

namespace UInt64

/-- Correctness of `wideSub3`: the returned triple represents the difference of
the two 192-bit inputs modulo `2^192`. -/
theorem toNat_wideSub3 (x y : UInt64 × UInt64 × UInt64) :
    (wideSub3 x y).1.toNat * 2 ^ 128 + (wideSub3 x y).2.1.toNat * 2 ^ 64
        + (wideSub3 x y).2.2.toNat
      = (2 ^ 192 - (y.1.toNat * 2 ^ 128 + y.2.1.toNat * 2 ^ 64 + y.2.2.toNat)
          + (x.1.toNat * 2 ^ 128 + x.2.1.toNat * 2 ^ 64 + x.2.2.toNat)) % 2 ^ 192 := by
  unfold wideSub3
  set X2 : ℕ := x.1.toNat
  set X1 : ℕ := x.2.1.toNat
  set X0 : ℕ := x.2.2.toNat
  set Y2 : ℕ := y.1.toNat
  set Y1 : ℕ := y.2.1.toNat
  set Y0 : ℕ := y.2.2.toNat
  have hX2 : X2 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hX1 : X1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hX0 : X0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY2 : Y2 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY1 : Y1 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hY0 : Y0 < 2 ^ 64 := _root_.UInt64.toNat_lt _
  set r0 := subWithBorrow x.2.2 y.2.2 false
  set r1 := subWithBorrow x.2.1 y.2.1 r0.2
  set r2 := subWithBorrow x.1 y.1 r1.2
  have he0 : r0.1.toNat + Y0 + 0 = X0 + (if r0.2 then 1 else 0) * 2 ^ 64 :=
    subWithBorrow_eq x.2.2 y.2.2 false
  have he1 : r1.1.toNat + Y1 + (if r0.2 then 1 else 0)
      = X1 + (if r1.2 then 1 else 0) * 2 ^ 64 :=
    subWithBorrow_eq x.2.1 y.2.1 r0.2
  have he2 : r2.1.toNat + Y2 + (if r1.2 then 1 else 0)
      = X2 + (if r2.2 then 1 else 0) * 2 ^ 64 :=
    subWithBorrow_eq x.1 y.1 r1.2
  have hr0_lt : r0.1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hr1_lt : r1.1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have hr2_lt : r2.1.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt _
  have h128 : (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 := by
    show (2 : ℕ) ^ (64 + 64) = 2 ^ 64 * 2 ^ 64; exact pow_add 2 64 64
  have h192 : (2 : ℕ) ^ 192 = 2 ^ 128 * 2 ^ 64 := by
    show (2 : ℕ) ^ (128 + 64) = 2 ^ 128 * 2 ^ 64; exact pow_add 2 128 64
  have hc0_range : (if r0.2 then 1 else 0 : ℕ) ≤ 1 := by split <;> simp
  have hc1_range : (if r1.2 then 1 else 0 : ℕ) ≤ 1 := by split <;> simp
  have hc2_range : (if r2.2 then 1 else 0 : ℕ) ≤ 1 := by split <;> simp
  -- Combine into: result + Y = X + c2 * 2^192.
  have hfull : r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat
      + (Y2 * 2 ^ 128 + Y1 * 2 ^ 64 + Y0)
      = X2 * 2 ^ 128 + X1 * 2 ^ 64 + X0
          + (if r2.2 then 1 else 0) * 2 ^ 192 := by
    have e0 : r0.1.toNat + Y0 = X0 + (if r0.2 then 1 else 0) * 2 ^ 64 := by linarith
    have e1 : r1.1.toNat + Y1 + (if r0.2 then 1 else 0)
        = X1 + (if r1.2 then 1 else 0) * 2 ^ 64 := he1
    have e2 : r2.1.toNat + Y2 + (if r1.2 then 1 else 0)
        = X2 + (if r2.2 then 1 else 0) * 2 ^ 64 := he2
    have step1 : r1.1.toNat * 2 ^ 64 + Y1 * 2 ^ 64 + (if r0.2 then 1 else 0) * 2 ^ 64
        = X1 * 2 ^ 64 + (if r1.2 then 1 else 0) * 2 ^ 128 := by
      have : (r1.1.toNat + Y1 + (if r0.2 then 1 else 0)) * 2 ^ 64
          = (X1 + (if r1.2 then 1 else 0) * 2 ^ 64) * 2 ^ 64 := by
        rw [e1]
      rw [h128]; linarith [this]
    have step2 : r2.1.toNat * 2 ^ 128 + Y2 * 2 ^ 128 + (if r1.2 then 1 else 0) * 2 ^ 128
        = X2 * 2 ^ 128 + (if r2.2 then 1 else 0) * 2 ^ 192 := by
      have : (r2.1.toNat + Y2 + (if r1.2 then 1 else 0)) * 2 ^ 128
          = (X2 + (if r2.2 then 1 else 0) * 2 ^ 64) * 2 ^ 128 := by
        rw [e2]
      rw [h192]; linarith [this]
    linarith [e0, step1, step2]
  have hresult_lt :
      r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat < 2 ^ 192 := by
    have hr1_bnd : r1.1.toNat * 2 ^ 64 + r0.1.toNat < 2 ^ 128 := by
      rw [h128]
      have : r1.1.toNat + 1 ≤ 2 ^ 64 := hr1_lt
      have h1 : (r1.1.toNat + 1) * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ this
      have h2 : (r1.1.toNat + 1) * 2 ^ 64 = r1.1.toNat * 2 ^ 64 + 2 ^ 64 := by ring
      linarith
    rw [h192]
    have : r2.1.toNat + 1 ≤ 2 ^ 64 := hr2_lt
    have h1 : (r2.1.toNat + 1) * 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 128 := Nat.mul_le_mul_right _ this
    have h2 : (r2.1.toNat + 1) * 2 ^ 128 = r2.1.toNat * 2 ^ 128 + 2 ^ 128 := by ring
    have hswap : 2 ^ 128 * 2 ^ 64 = 2 ^ 64 * 2 ^ 128 := by ring
    rw [hswap]
    linarith
  have hY_lt : Y2 * 2 ^ 128 + Y1 * 2 ^ 64 + Y0 < 2 ^ 192 := by
    have hY_low : Y1 * 2 ^ 64 + Y0 < 2 ^ 128 := by
      rw [h128]
      have : Y1 + 1 ≤ 2 ^ 64 := hY1
      have h1 : (Y1 + 1) * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ this
      have h2 : (Y1 + 1) * 2 ^ 64 = Y1 * 2 ^ 64 + 2 ^ 64 := by ring
      linarith
    rw [h192]
    have : Y2 + 1 ≤ 2 ^ 64 := hY2
    have h1 : (Y2 + 1) * 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 128 := Nat.mul_le_mul_right _ this
    have h2 : (Y2 + 1) * 2 ^ 128 = Y2 * 2 ^ 128 + 2 ^ 128 := by ring
    have hswap : 2 ^ 128 * 2 ^ 64 = 2 ^ 64 * 2 ^ 128 := by ring
    rw [hswap]
    linarith
  have hX_lt : X2 * 2 ^ 128 + X1 * 2 ^ 64 + X0 < 2 ^ 192 := by
    have hX_low : X1 * 2 ^ 64 + X0 < 2 ^ 128 := by
      rw [h128]
      have : X1 + 1 ≤ 2 ^ 64 := hX1
      have h1 : (X1 + 1) * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ this
      have h2 : (X1 + 1) * 2 ^ 64 = X1 * 2 ^ 64 + 2 ^ 64 := by ring
      linarith
    rw [h192]
    have : X2 + 1 ≤ 2 ^ 64 := hX2
    have h1 : (X2 + 1) * 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 128 := Nat.mul_le_mul_right _ this
    have h2 : (X2 + 1) * 2 ^ 128 = X2 * 2 ^ 128 + 2 ^ 128 := by ring
    have hswap : 2 ^ 128 * 2 ^ 64 = 2 ^ 64 * 2 ^ 128 := by ring
    rw [hswap]
    linarith
  -- Now derive result = (2^192 - Y + X) mod 2^192 from hfull.
  change r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat
      = (2 ^ 192 - (Y2 * 2 ^ 128 + Y1 * 2 ^ 64 + Y0)
          + (X2 * 2 ^ 128 + X1 * 2 ^ 64 + X0)) % 2 ^ 192
  -- Introduce abbreviations so omega doesn't choke on 2^192 numerals.
  set Xs : ℕ := X2 * 2 ^ 128 + X1 * 2 ^ 64 + X0 with hXs_def
  set Ys : ℕ := Y2 * 2 ^ 128 + Y1 * 2 ^ 64 + Y0 with hYs_def
  set Rs : ℕ := r2.1.toNat * 2 ^ 128 + r1.1.toNat * 2 ^ 64 + r0.1.toNat with hRs_def
  set P : ℕ := 2 ^ 192 with hP_def
  have hR_lt : Rs < P := hresult_lt
  have hY_lt' : Ys < P := hY_lt
  clear_value Xs Ys Rs P
  by_cases hc2 : r2.2
  · have hc2_val : (if r2.2 then 1 else 0 : ℕ) = 1 := by rw [ite_eq_left hc2]
    rw [hc2_val] at hfull
    -- hfull : Rs + Ys = Xs + 1 * P   (after rewrites)
    have hfull' : Rs + Ys = Xs + P := by linarith [hfull]
    have hXlt : Xs < Ys := by linarith
    have hval : Rs = P - Ys + Xs := by omega
    rw [hval]
    have hsum_lt : P - Ys + Xs < P := by omega
    exact (Nat.mod_eq_of_lt hsum_lt).symm
  · have hc2_val : (if r2.2 then 1 else 0 : ℕ) = 0 := by rw [ite_eq_right hc2]
    rw [hc2_val] at hfull
    have hfull' : Rs + Ys = Xs := by linarith [hfull]
    have hXge : Ys ≤ Xs := by linarith
    have hval : Rs = Xs - Ys := by omega
    rw [hval]
    have heq : P - Ys + Xs = P + (Xs - Ys) := by omega
    rw [heq]
    have hdiff_lt : Xs - Ys < P := by omega
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hdiff_lt]

end UInt64
