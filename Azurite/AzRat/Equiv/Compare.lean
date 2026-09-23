/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Compare
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.LogBase2
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Correctness of `AzRat.cmp`

`AzRat.cmp x y = compare (toRat x) (toRat y)`.

The proof verifies the staged algorithm against the ordered-field comparison directly. Each
limb-level ingredient of `AzRat.cmp` is bridged to the corresponding rational expression on
`toRat x` / `toRat y` (`AzNat.compare` ↔ `ℕ`-`compare`, `floorLogBase2Abs` ↔ `⌊log₂|·|⌋`), and
the staged algorithm is then verified against the ordered-field comparison directly.
-/

open Real

namespace Azurite.AzRat

-- `compare` on `Ordering` does not reduce under `simp` on its own.
@[local simp] private lemma cmp_ord_lt_lt : compare Ordering.lt Ordering.lt = Ordering.eq := by decide
@[local simp] private lemma cmp_ord_lt_eq : compare Ordering.lt Ordering.eq = Ordering.lt := by decide
@[local simp] private lemma cmp_ord_lt_gt : compare Ordering.lt Ordering.gt = Ordering.lt := by decide
@[local simp] private lemma cmp_ord_eq_lt : compare Ordering.eq Ordering.lt = Ordering.gt := by decide
@[local simp] private lemma cmp_ord_eq_eq : compare Ordering.eq Ordering.eq = Ordering.eq := by decide
@[local simp] private lemma cmp_ord_eq_gt : compare Ordering.eq Ordering.gt = Ordering.lt := by decide
@[local simp] private lemma cmp_ord_gt_lt : compare Ordering.gt Ordering.lt = Ordering.gt := by decide
@[local simp] private lemma cmp_ord_gt_eq : compare Ordering.gt Ordering.eq = Ordering.gt := by decide
@[local simp] private lemma cmp_ord_gt_gt : compare Ordering.gt Ordering.gt = Ordering.eq := by decide

-- `Ordering` is not a `LinearOrder`, so the generic `compare_*_iff_*` lemmas do not apply to it.
private lemma compare_ordering_self (o : Ordering) : compare o o = Ordering.eq := by
  cases o <;> decide
private lemma ordering_eq_of_compare_eq {a b : Ordering} (h : compare a b = Ordering.eq) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-! ### Rational-level helper lemmas (general `ℚ`) -/

private lemma compare_num_zero_neg (q : ℚ) (h : q < 0) : compare q.num 0 = Ordering.lt :=
  compare_lt_iff_lt.mpr (Rat.num_neg.mpr h)
private lemma compare_num_zero_zero : compare (0 : ℚ).num 0 = Ordering.eq := by decide
private lemma compare_num_zero_pos (q : ℚ) (h : 0 < q) : compare q.num 0 = Ordering.gt :=
  compare_gt_iff_gt.mpr (Rat.num_pos.mpr h)

/-- For two positive rationals the comparison equals the comparison of absolute values. -/
private lemma compare_pos (X Y : ℚ) (hX : 0 < X) (hY : 0 < Y) : compare X Y = compare |X| |Y| := by
  rw [abs_of_pos hX, abs_of_pos hY]

/-- For two negative rationals the comparison is the swapped comparison of absolute values. -/
private lemma compare_neg (X Y : ℚ) (hX : X < 0) (hY : Y < 0) :
    compare X Y = (compare |X| |Y|).swap := by
  rw [abs_of_neg hX, abs_of_neg hY]
  rcases lt_trichotomy X Y with h | rfl | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (neg_lt_neg h)]; rfl
  · simp
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (neg_lt_neg h)]; rfl

/-- The sign-stage value equals `compare x y` whenever the signs differ or `x = 0`. -/
private lemma sign_cmp_correct (x y : ℚ)
    (h : compare x.num 0 ≠ compare y.num 0 ∨ x = 0) :
    compare (compare x.num 0) (compare y.num 0) = compare x y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [compare_num_zero_neg _ hx, compare_num_zero_neg _ hy] at h
    simp at h; exact absurd h hx.ne
  · rw [compare_num_zero_neg _ hx, compare_num_zero_zero]
    exact (compare_lt_iff_lt.mpr hx).symm
  · rw [compare_num_zero_neg _ hx, compare_num_zero_pos _ hy]
    exact (compare_lt_iff_lt.mpr (hx.trans hy)).symm
  · rw [compare_num_zero_zero, compare_num_zero_neg _ hy]
    exact (compare_gt_iff_gt.mpr hy).symm
  · simp
  · rw [compare_num_zero_zero, compare_num_zero_pos _ hy]
    exact (compare_lt_iff_lt.mpr hy).symm
  · rw [compare_num_zero_pos _ hx, compare_num_zero_neg _ hy]
    exact (compare_gt_iff_gt.mpr (hy.trans hx)).symm
  · rw [compare_num_zero_pos _ hx, compare_num_zero_zero]
    exact (compare_gt_iff_gt.mpr hx).symm
  · rw [compare_num_zero_pos _ hx, compare_num_zero_pos _ hy] at h
    simp at h; exact absurd h (ne_of_gt hx)

/-- The numerator of `|x|` is `x.num.natAbs`. -/
private lemma rat_abs_num (x : ℚ) : (|x|).num = x.num.natAbs := by
  rw [Rat.abs_def, Rat.divInt_eq_div]
  exact Rat.num_div_eq_of_coprime (by exact_mod_cast Rat.pos x)
      (by rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact x.reduced)

private lemma abs_lt_one_iff (x : ℚ) : |x| < 1 ↔ x.num.natAbs < x.den := by
  rw [← Rat.num_lt_denom_iff, rat_abs_num, Rat.den_abs_eq_den]; exact_mod_cast Iff.rfl

/-- `compare x.num.natAbs x.den` equals `compare |x| 1`. -/
private lemma compare_natAbs_den_eq (x : ℚ) :
    compare x.num.natAbs x.den = compare |x| (1 : ℚ) := by
  rcases Nat.lt_trichotomy x.num.natAbs x.den with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr ((abs_lt_one_iff x).mpr h)]
  · have h4 : (|x|).num = (|x|.den : ℤ) := by
      rw [rat_abs_num, Rat.den_abs_eq_den]; exact_mod_cast h
    have hab : |x| = 1 := by
      conv_lhs => rw [← Rat.num_div_den |x|]; rw [h4]
      push_cast
      apply div_self
      rw [Rat.den_abs_eq_den]; exact_mod_cast (Rat.pos x).ne'
    rw [h]; simp [compare_eq_iff_eq.mpr hab]
  · have hge : 1 ≤ |x| := not_lt.mp ((abs_lt_one_iff x).not.mpr (Nat.not_lt.mpr h.le))
    have hgt : (|x|.den : ℤ) < (|x|).num := by
      rw [rat_abs_num, Rat.den_abs_eq_den]; exact_mod_cast h
    have hne1 : |x| ≠ 1 := by intro heq; rw [heq] at hgt; simp at hgt
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (lt_of_le_of_ne hge hne1.symm)]

/-- When `X` and `Y` are on different sides of `1`, comparing `compare X 1` with `compare Y 1`
gives the same result as comparing `X` with `Y`. -/
private lemma pos_one_cmp_eq_cmp (X Y : ℚ)
    (h_ne : compare (compare X 1) (compare Y 1) ≠ Ordering.eq) :
    compare (compare X 1) (compare Y 1) = compare X Y := by
  rcases lt_trichotomy X 1 with hx | rfl | hx <;>
  rcases lt_trichotomy Y 1 with hy | rfl | hy
  · simp [compare_lt_iff_lt.mpr hx, compare_lt_iff_lt.mpr hy] at h_ne
  · simp [compare_lt_iff_lt.mpr hx]
  · rw [compare_lt_iff_lt.mpr hx, compare_gt_iff_gt.mpr hy]
    simp [compare_lt_iff_lt.mpr (hx.trans hy)]
  · simp [compare_lt_iff_lt.mpr hy, compare_gt_iff_gt.mpr hy]
  · simp at h_ne
  · simp [compare_gt_iff_gt.mpr hy, compare_lt_iff_lt.mpr hy]
  · rw [compare_gt_iff_gt.mpr hx, compare_lt_iff_lt.mpr hy]
    simp [compare_gt_iff_gt.mpr (hy.trans hx)]
  · simp [compare_gt_iff_gt.mpr hx]
  · simp [compare_gt_iff_gt.mpr hx, compare_gt_iff_gt.mpr hy] at h_ne

/-- Same nonzero sign + equal numerator/denominator magnitudes ⇒ equal. -/
private lemma eq_of_same_sign_natAbs_den (x y : ℚ)
    (h_sign_eq : compare x.num 0 = compare y.num 0)
    (h_nz : x.num ≠ 0)
    (h_num : x.num.natAbs = y.num.natAbs)
    (h_den : x.den = y.den) : x = y := by
  have hnum_eq : x.num = y.num := by
    have hcast : (x.num.natAbs : ℤ) = y.num.natAbs := by exact_mod_cast h_num
    rcases lt_trichotomy x.num 0 with hneg | hzero | hpos
    · have hy_neg : y.num < 0 := by
        have h := h_sign_eq; rw [compare_lt_iff_lt.mpr hneg] at h
        exact compare_lt_iff_lt.mp h.symm
      rw [Int.ofNat_natAbs_of_nonpos hneg.le, Int.ofNat_natAbs_of_nonpos hy_neg.le] at hcast
      omega
    · exact absurd hzero h_nz
    · have hy_pos : 0 < y.num := by
        have h := h_sign_eq; rw [compare_gt_iff_gt.mpr hpos] at h
        exact compare_gt_iff_gt.mp h.symm
      rw [Int.natAbs_of_nonneg hpos.le, Int.natAbs_of_nonneg hy_pos.le] at hcast
      exact hcast
  exact Rat.ext hnum_eq h_den

private lemma abs_lt_abs_iff (x y : ℚ) :
    |x| < |y| ↔ x.num.natAbs * y.den < y.num.natAbs * x.den := by
  rw [Rat.lt_iff, rat_abs_num, rat_abs_num, Rat.den_abs_eq_den, Rat.den_abs_eq_den]
  exact_mod_cast Iff.rfl

/-- When `nd_cmp ≠ eq`, it encodes `compare |x| |y|`. -/
private lemma nd_cmp_of_ne (x y : ℚ) (h_nz : x.num ≠ 0)
    (h_ne : compare (compare x.num.natAbs y.num.natAbs) (compare x.den y.den) ≠ Ordering.eq) :
    compare (compare x.num.natAbs y.num.natAbs) (compare x.den y.den) = compare |x| |y| := by
  have den_pos : ∀ z : ℚ, 0 < z.den := Rat.pos
  have natAbs_pos : 0 < x.num.natAbs := Int.natAbs_pos.mpr h_nz
  rcases Nat.lt_trichotomy x.num.natAbs y.num.natAbs with hn | hn | hn <;>
  rcases Nat.lt_trichotomy x.den y.den with hd | hd | hd
  · simp [compare_lt_iff_lt.mpr hn, compare_lt_iff_lt.mpr hd] at h_ne
  · rw [compare_lt_iff_lt.mpr hn, compare_eq_iff_eq.mpr hd]; simp only [cmp_ord_lt_eq]
    exact (compare_lt_iff_lt.mpr ((abs_lt_abs_iff x y).mpr (by
      rw [hd]; exact Nat.mul_lt_mul_of_pos_right hn (den_pos y)))).symm
  · rw [compare_lt_iff_lt.mpr hn, compare_gt_iff_gt.mpr hd]; simp only [cmp_ord_lt_gt]
    exact (compare_lt_iff_lt.mpr ((abs_lt_abs_iff x y).mpr
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hn (den_pos y))
                           (Nat.mul_le_mul_left _ hd.le)))).symm
  · rw [compare_eq_iff_eq.mpr hn, compare_lt_iff_lt.mpr hd]; simp only [cmp_ord_eq_lt]
    refine (compare_gt_iff_gt.mpr ((abs_lt_abs_iff y x).mpr ?_)).symm
    rw [hn]; exact Nat.mul_lt_mul_of_pos_left hd (hn ▸ natAbs_pos)
  · simp [compare_eq_iff_eq.mpr hn, compare_eq_iff_eq.mpr hd] at h_ne
  · rw [compare_eq_iff_eq.mpr hn, compare_gt_iff_gt.mpr hd]; simp only [cmp_ord_eq_gt]
    refine (compare_lt_iff_lt.mpr ((abs_lt_abs_iff x y).mpr ?_)).symm
    rw [hn]; exact Nat.mul_lt_mul_of_pos_left hd (hn ▸ natAbs_pos)
  · rw [compare_gt_iff_gt.mpr hn, compare_lt_iff_lt.mpr hd]; simp only [cmp_ord_gt_lt]
    exact (compare_gt_iff_gt.mpr ((abs_lt_abs_iff y x).mpr
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hn (den_pos x))
                           (Nat.mul_le_mul_left _ hd.le)))).symm
  · rw [compare_gt_iff_gt.mpr hn, compare_eq_iff_eq.mpr hd]; simp only [cmp_ord_gt_eq]
    refine (compare_gt_iff_gt.mpr ((abs_lt_abs_iff y x).mpr ?_)).symm
    rw [hd]; exact Nat.mul_lt_mul_of_pos_right hn (den_pos y)
  · simp [compare_gt_iff_gt.mpr hn, compare_gt_iff_gt.mpr hd] at h_ne

/-- The cross-multiply comparison is always the comparison of absolute values. -/
private lemma cross_mul_eq_compare_abs (x y : ℚ) :
    compare (x.num.natAbs * y.den) (x.den * y.num.natAbs) = compare |x| |y| := by
  rw [show x.den * y.num.natAbs = y.num.natAbs * x.den from Nat.mul_comm _ _]
  rcases Nat.lt_trichotomy (x.num.natAbs * y.den) (y.num.natAbs * x.den) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    exact (compare_lt_iff_lt.mpr ((abs_lt_abs_iff x y).mpr h)).symm
  · have hxy : ¬ |x| < |y| := mt (abs_lt_abs_iff x y).mp (by omega)
    have hyx : ¬ |y| < |x| := mt (abs_lt_abs_iff y x).mp (by omega)
    have hab : |x| = |y| := le_antisymm (not_lt.mp hyx) (not_lt.mp hxy)
    rw [compare_eq_iff_eq.mpr h]; exact (compare_eq_iff_eq.mpr hab).symm
  · rw [compare_gt_iff_gt.mpr h]
    exact (compare_gt_iff_gt.mpr ((abs_lt_abs_iff y x).mpr h)).symm

/-! ### Bridges between `AzRat.cmp` ingredients and `toRat` -/

private lemma toRat_num_natAbs (x : AzRat) : (toRat x).num.natAbs = x.num.toNat := by
  show (if x.sign then (x.num.toNat : ℤ) else -(x.num.toNat : ℤ)).natAbs = x.num.toNat
  cases x.sign <;> simp

private lemma toRat_den_eq (x : AzRat) : (toRat x).den = x.den.toNat := rfl

private lemma signOrd_eq (x : AzRat) : signOrd x = compare (toRat x).num 0 := by
  have hnum : (toRat x).num = if x.sign then (x.num.toNat : ℤ) else -(x.num.toNat : ℤ) := rfl
  unfold signOrd
  by_cases h0 : x.num = 0
  · have hz : (toRat x).num = 0 := by
      have h := toRat_num_natAbs x; rw [h0, AzNat.toNat_zero] at h
      exact Int.natAbs_eq_zero.mp h
    rw [ite_eq_left h0, hz]; exact (compare_eq_iff_eq.mpr rfl).symm
  · have hposZ : (0 : ℤ) < x.num.toNat := by
      have : 0 < x.num.toNat :=
        Nat.pos_of_ne_zero (fun h => h0 (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm)))
      exact_mod_cast this
    rw [ite_eq_right h0]
    cases hs : x.sign
    · have hneg : (toRat x).num < 0 := by
        rw [hnum, hs]; simp only [Bool.false_eq_true, ite_false]; omega
      simp [compare_lt_iff_lt.mpr hneg]
    · have hgt : (0 : ℤ) < (toRat x).num := by rw [hnum, hs]; simpa using hposZ
      simp [compare_gt_iff_gt.mpr hgt]

private lemma cmp_num_den (x : AzRat) :
    AzNat.compare x.num x.den = compare (toRat x).num.natAbs (toRat x).den := by
  rw [AzNat.compare_eq_compare_toNat, toRat_num_natAbs, toRat_den_eq]

private lemma cmp_num_num (x y : AzRat) :
    AzNat.compare x.num y.num = compare (toRat x).num.natAbs (toRat y).num.natAbs := by
  rw [AzNat.compare_eq_compare_toNat, toRat_num_natAbs, toRat_num_natAbs]

private lemma cmp_den_den (x y : AzRat) :
    AzNat.compare x.den y.den = compare (toRat x).den (toRat y).den := by
  rw [AzNat.compare_eq_compare_toNat, toRat_den_eq, toRat_den_eq]

private lemma cmp_cross (x y : AzRat) :
    AzNat.compare (x.num * y.den) (x.den * y.num) =
      compare ((toRat x).num.natAbs * (toRat y).den) ((toRat x).den * (toRat y).num.natAbs) := by
  rw [AzNat.compare_eq_compare_toNat, AzNat.toNat_mul, AzNat.toNat_mul,
      toRat_num_natAbs, toRat_den_eq, toRat_den_eq, toRat_num_natAbs]

private lemma toRat_ne_zero (x : AzRat) (h : x.num ≠ 0) : toRat x ≠ 0 := by
  intro hz
  apply h
  have h1 : (toRat x).num.natAbs = x.num.toNat := toRat_num_natAbs x
  rw [hz] at h1
  simp only [Rat.num_zero, Int.natAbs_zero] at h1
  exact AzNat.toNat_injective (h1.symm.trans AzNat.toNat_zero.symm)

private lemma toRat_num_ne_zero (x : AzRat) (h : x.num ≠ 0) : (toRat x).num ≠ 0 :=
  fun hc => toRat_ne_zero x h (Rat.zero_of_num_zero hc)

/-- `toRat x = 0` exactly when `x.num = 0`. -/
private lemma num_zero_of_toRat_num_zero (x : AzRat) (h : (toRat x).num = 0) : x.num = 0 := by
  have h1 : (toRat x).num.natAbs = x.num.toNat := toRat_num_natAbs x
  rw [h] at h1
  simp only [Int.natAbs_zero] at h1
  exact AzNat.toNat_injective (h1.symm.trans AzNat.toNat_zero.symm)

/-- Same signs and `x.num ≠ 0` force `y.num ≠ 0`. -/
private lemma y_num_ne_zero (x y : AzRat)
    (h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0) (h_nz : x.num ≠ 0) :
    y.num ≠ 0 := by
  intro h0
  have hy0 : (toRat y).num = 0 := by
    have h1 : (toRat y).num.natAbs = y.num.toNat := toRat_num_natAbs y
    rw [h0, AzNat.toNat_zero] at h1
    exact Int.natAbs_eq_zero.mp h1
  exact toRat_num_ne_zero x h_nz
    (compare_eq_iff_eq.mp (h_sign_eq.trans (compare_eq_iff_eq.mpr hy0)))

/-- A larger floor-log forces a larger absolute value. -/
private lemma floorLog_lt_imp_abs_lt (x y : AzRat) (hx : x.num ≠ 0) (hy : y.num ≠ 0)
    (h_log_lt : floorLogBase2Abs x < floorLogBase2Abs y) : |toRat x| < |toRat y| := by
  have hfx := floorLogBase2Abs_eq x hx
  have hfy := floorLogBase2Abs_eq y hy
  have h_base : (1 : ℝ) < 2 := by norm_num
  have hax : 0 < |(toRat x : ℝ)| := abs_pos.mpr (by exact_mod_cast toRat_ne_zero x hx)
  have hay : 0 < |(toRat y : ℝ)| := abs_pos.mpr (by exact_mod_cast toRat_ne_zero y hy)
  have hbx : logb 2 |(toRat x : ℝ)| < (floorLogBase2Abs x : ℝ) + 1 := by
    have h := Int.lt_floor_add_one (logb 2 |(toRat x : ℝ)|); rwa [← hfx] at h
  have hby : (floorLogBase2Abs y : ℝ) ≤ logb 2 |(toRat y : ℝ)| := by
    have h := Int.floor_le (logb 2 |(toRat y : ℝ)|); rwa [← hfy] at h
  have hcast : (floorLogBase2Abs x : ℝ) + 1 ≤ (floorLogBase2Abs y : ℝ) := by exact_mod_cast h_log_lt
  have htrans : logb 2 |(toRat x : ℝ)| < logb 2 |(toRat y : ℝ)| := by
    calc logb 2 |(toRat x : ℝ)| < (floorLogBase2Abs x : ℝ) + 1 := hbx
      _ ≤ (floorLogBase2Abs y : ℝ) := hcast
      _ ≤ logb 2 |(toRat y : ℝ)| := hby
  have := (logb_lt_logb_iff h_base hax hay).mp htrans
  exact_mod_cast this

/-- When `log_cmp ≠ eq`, it encodes `compare |toRat x| |toRat y|`. -/
private lemma log_cmp_of_ne (x y : AzRat) (hx : x.num ≠ 0) (hy : y.num ≠ 0)
    (h_ne : compare (floorLogBase2Abs x) (floorLogBase2Abs y) ≠ Ordering.eq) :
    compare (floorLogBase2Abs x) (floorLogBase2Abs y) = compare |toRat x| |toRat y| := by
  rcases lt_trichotomy (floorLogBase2Abs x) (floorLogBase2Abs y) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    exact (compare_lt_iff_lt.mpr (floorLog_lt_imp_abs_lt x y hx hy h)).symm
  · exact absurd (compare_eq_iff_eq.mpr h) h_ne
  · rw [compare_gt_iff_gt.mpr h]
    exact (compare_gt_iff_gt.mpr (floorLog_lt_imp_abs_lt y x hy hx h)).symm

/-- Combine a magnitude comparison with the sign: positive returns it, negative swaps it. -/
private lemma combine_sign (x y : AzRat) (mag : Ordering)
    (h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0)
    (h_nz : x.num ≠ 0)
    (h_mag : mag = compare |toRat x| |toRat y|) :
    (if compare (toRat x).num 0 == Ordering.gt then mag else mag.swap)
      = compare (toRat x) (toRat y) := by
  have hx_ne : toRat x ≠ 0 := toRat_ne_zero x h_nz
  rcases lt_or_gt_of_ne hx_ne with hx | hx
  · have hxnum : compare (toRat x).num 0 = Ordering.lt :=
      compare_lt_iff_lt.mpr (Rat.num_neg.mpr hx)
    have hy : toRat y < 0 := Rat.num_neg.mp (compare_lt_iff_lt.mp (h_sign_eq ▸ hxnum))
    rw [hxnum, ite_eq_right (by decide), h_mag, compare_neg (toRat x) (toRat y) hx hy]
  · have hxnum : compare (toRat x).num 0 = Ordering.gt :=
      compare_gt_iff_gt.mpr (Rat.num_pos.mpr hx)
    have hy : 0 < toRat y := Rat.num_pos.mp (compare_gt_iff_gt.mp (h_sign_eq ▸ hxnum))
    rw [hxnum, ite_eq_left (by decide), h_mag, compare_pos (toRat x) (toRat y) hx hy]

/-! ### Staged correctness -/

private lemma toRat_eq_zero (x : AzRat) (h : x.num = 0) : toRat x = 0 := by
  apply Rat.zero_of_num_zero
  have h1 : (toRat x).num.natAbs = x.num.toNat := toRat_num_natAbs x
  rw [h, AzNat.toNat_zero] at h1
  exact Int.natAbs_eq_zero.mp h1

/-- When the sign stage exits, `cmp` returns the sign comparison. -/
private lemma cmp_sign_exit (x y : AzRat)
    (h : compare (compare (toRat x).num 0) (compare (toRat y).num 0) ≠ Ordering.eq
        ∨ (compare (toRat x).num 0 == Ordering.eq)) :
    cmp x y = compare (compare (toRat x).num 0) (compare (toRat y).num 0) := by
  unfold cmp
  rw [signOrd_eq x, signOrd_eq y, ite_eq_left h]

/-- Helper: the stage-1 condition is false when signs agree and `x.num ≠ 0`. -/
private lemma stage1_not_exit (x y : AzRat)
    (h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0)
    (h_nz : x.num ≠ 0) :
    ¬(compare (compare (toRat x).num 0) (compare (toRat y).num 0) ≠ Ordering.eq
        ∨ (compare (toRat x).num 0 == Ordering.eq)) := by
  have hxsign_ne : compare (toRat x).num 0 ≠ Ordering.eq :=
    fun h0 => toRat_num_ne_zero x h_nz (compare_eq_iff_eq.mp h0)
  rw [not_or]
  refine ⟨not_not.mpr ?_, ?_⟩
  · rw [h_sign_eq]; exact compare_ordering_self _
  · intro hc; exact hxsign_ne (beq_iff_eq.mp hc)

private lemma cmp_one_cmp_ne_eq (x y : AzRat)
    (h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0)
    (h_nz : x.num ≠ 0)
    (h_one_ne : compare (compare (toRat x).num.natAbs (toRat x).den)
                        (compare (toRat y).num.natAbs (toRat y).den) ≠ Ordering.eq) :
    cmp x y = compare (toRat x) (toRat y) := by
  unfold cmp
  rw [signOrd_eq x, signOrd_eq y, ite_eq_right (stage1_not_exit x y h_sign_eq h_nz),
      cmp_num_den x, cmp_num_den y, ite_eq_left h_one_ne]
  refine combine_sign x y _ h_sign_eq h_nz ?_
  rw [compare_natAbs_den_eq (toRat x), compare_natAbs_den_eq (toRat y)]
  rw [compare_natAbs_den_eq (toRat x), compare_natAbs_den_eq (toRat y)] at h_one_ne
  exact pos_one_cmp_eq_cmp |toRat x| |toRat y| h_one_ne

private lemma cmp_nd_cmp_ne_eq (x y : AzRat)
    (h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0)
    (h_nz : x.num ≠ 0)
    (h_one_eq : compare (compare (toRat x).num.natAbs (toRat x).den)
                        (compare (toRat y).num.natAbs (toRat y).den) = Ordering.eq)
    (h_not_both : ¬((toRat x).num.natAbs = (toRat y).num.natAbs ∧ (toRat x).den = (toRat y).den))
    (h_nd_ne : compare (compare (toRat x).num.natAbs (toRat y).num.natAbs)
                       (compare (toRat x).den (toRat y).den) ≠ Ordering.eq) :
    cmp x y = compare (toRat x) (toRat y) := by
  unfold cmp
  rw [signOrd_eq x, signOrd_eq y, ite_eq_right (stage1_not_exit x y h_sign_eq h_nz),
      cmp_num_den x, cmp_num_den y, ite_eq_right (by rwa [ne_eq, not_not]),
      cmp_num_num x y, cmp_den_den x y]
  rw [ite_eq_right (by
    rintro ⟨h1, h2⟩
    exact h_not_both ⟨compare_eq_iff_eq.mp (beq_iff_eq.mp h1), compare_eq_iff_eq.mp (beq_iff_eq.mp h2)⟩)]
  rw [ite_eq_left h_nd_ne]
  exact combine_sign x y _ h_sign_eq h_nz
    (nd_cmp_of_ne (toRat x) (toRat y) (toRat_num_ne_zero x h_nz) h_nd_ne)

private lemma cmp_log_cmp_ne_eq (x y : AzRat)
    (h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0)
    (h_nz : x.num ≠ 0)
    (h_one_eq : compare (compare (toRat x).num.natAbs (toRat x).den)
                        (compare (toRat y).num.natAbs (toRat y).den) = Ordering.eq)
    (h_not_both : ¬((toRat x).num.natAbs = (toRat y).num.natAbs ∧ (toRat x).den = (toRat y).den))
    (h_nd_eq : compare (compare (toRat x).num.natAbs (toRat y).num.natAbs)
                       (compare (toRat x).den (toRat y).den) = Ordering.eq)
    (h_log_ne : compare (floorLogBase2Abs x) (floorLogBase2Abs y) ≠ Ordering.eq) :
    cmp x y = compare (toRat x) (toRat y) := by
  have hy_nz : y.num ≠ 0 := y_num_ne_zero x y h_sign_eq h_nz
  unfold cmp
  rw [signOrd_eq x, signOrd_eq y, ite_eq_right (stage1_not_exit x y h_sign_eq h_nz),
      cmp_num_den x, cmp_num_den y, ite_eq_right (by rwa [ne_eq, not_not]),
      cmp_num_num x y, cmp_den_den x y]
  rw [ite_eq_right (by
    rintro ⟨h1, h2⟩
    exact h_not_both ⟨compare_eq_iff_eq.mp (beq_iff_eq.mp h1), compare_eq_iff_eq.mp (beq_iff_eq.mp h2)⟩)]
  rw [ite_eq_right (by rwa [ne_eq, not_not]), ite_eq_left h_log_ne]
  exact combine_sign x y _ h_sign_eq h_nz (log_cmp_of_ne x y h_nz hy_nz h_log_ne)

/-- **Correctness of `AzRat.cmp`.** -/
theorem cmp_eq_compare (x y : AzRat) : cmp x y = compare (toRat x) (toRat y) := by
  by_cases h1 : compare (compare (toRat x).num 0) (compare (toRat y).num 0) ≠ Ordering.eq
      ∨ x.num = 0
  · rcases h1 with h1 | hx0
    · -- signs differ
      rw [cmp_sign_exit x y (Or.inl h1)]
      exact sign_cmp_correct (toRat x) (toRat y)
        (Or.inl (fun h => h1 (by rw [h]; exact compare_ordering_self _)))
    · -- x.num = 0 ⇒ toRat x = 0, sign stage exits via the `== eq` disjunct
      have hx : toRat x = 0 := toRat_eq_zero x hx0
      have hxe : (compare (toRat x).num 0 == Ordering.eq) = true :=
        beq_iff_eq.mpr (compare_eq_iff_eq.mpr (by rw [hx]; rfl))
      rw [cmp_sign_exit x y (Or.inr hxe)]
      exact sign_cmp_correct (toRat x) (toRat y) (Or.inr hx)
  · rw [not_or] at h1
    obtain ⟨h_sign_cmp, h_nz⟩ := h1
    have h_sign_eq : compare (toRat x).num 0 = compare (toRat y).num 0 :=
      ordering_eq_of_compare_eq (not_not.mp h_sign_cmp)
    by_cases h2 : compare (compare (toRat x).num.natAbs (toRat x).den)
                          (compare (toRat y).num.natAbs (toRat y).den) ≠ Ordering.eq
    · exact cmp_one_cmp_ne_eq x y h_sign_eq h_nz h2
    rw [not_not] at h2
    by_cases h3 : (toRat x).num.natAbs = (toRat y).num.natAbs ∧ (toRat x).den = (toRat y).den
    · have hxy : toRat x = toRat y :=
        eq_of_same_sign_natAbs_den (toRat x) (toRat y) h_sign_eq (toRat_num_ne_zero x h_nz)
          h3.1 h3.2
      rw [hxy, show compare (toRat y) (toRat y) = Ordering.eq from compare_eq_iff_eq.mpr rfl]
      unfold cmp
      rw [signOrd_eq x, signOrd_eq y, ite_eq_right (stage1_not_exit x y h_sign_eq h_nz),
          cmp_num_den x, cmp_num_den y, ite_eq_right (by rwa [ne_eq, not_not]),
          cmp_num_num x y, cmp_den_den x y]
      rw [ite_eq_left ⟨beq_iff_eq.mpr (compare_eq_iff_eq.mpr h3.1),
                  beq_iff_eq.mpr (compare_eq_iff_eq.mpr h3.2)⟩]
    · by_cases h4 : compare (compare (toRat x).num.natAbs (toRat y).num.natAbs)
                            (compare (toRat x).den (toRat y).den) ≠ Ordering.eq
      · exact cmp_nd_cmp_ne_eq x y h_sign_eq h_nz h2 h3 h4
      rw [not_not] at h4
      by_cases h5 : compare (floorLogBase2Abs x) (floorLogBase2Abs y) ≠ Ordering.eq
      · exact cmp_log_cmp_ne_eq x y h_sign_eq h_nz h2 h3 h4 h5
      rw [not_not] at h5
      -- final stage: cross-multiply
      unfold cmp
      rw [signOrd_eq x, signOrd_eq y, ite_eq_right (stage1_not_exit x y h_sign_eq h_nz),
          cmp_num_den x, cmp_num_den y, ite_eq_right (by rwa [ne_eq, not_not]),
          cmp_num_num x y, cmp_den_den x y]
      rw [ite_eq_right (by
        rintro ⟨h1', h2'⟩
        exact h3 ⟨compare_eq_iff_eq.mp (beq_iff_eq.mp h1'), compare_eq_iff_eq.mp (beq_iff_eq.mp h2')⟩)]
      rw [ite_eq_right (by rwa [ne_eq, not_not]), ite_eq_right (by rwa [ne_eq, not_not]), cmp_cross x y]
      exact combine_sign x y _ h_sign_eq h_nz (cross_mul_eq_compare_abs (toRat x) (toRat y))

end Azurite.AzRat
