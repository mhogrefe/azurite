/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Int

/-!
# Round-to-nearest on the integers, and double rounding with a ternary

* `abs_sub_toInt_round_nearest_le`: the nearest integer is within `1/2`.
* `toInt_round_nearest_eq_of_abs_lt`: an integer within less than `1/2` is the rounding.
* `toInt_round_nearest_half`: at an exact half the even neighbour wins (`intTiebreak`).
* `abs_toInt_round_nearest_sub_le`: the rounding is at least as close as any integer.
* `NearestTernary y R o`: `R` is a nearest integer to `y`, an exact half resolved by `o`.
* `toInt_round_nearest_of_ternary`: **double rounding** — if `X` is at least as close to `w` as
  every integer and every half-integer (in range) and `R` is `NearestTernary` for `X` with the
  ternary `compare X w`, then `R` is the nearest integer to `w`.  This is the correctness of
  re-rounding a correctly rounded value with its ternary to a coarser grid whose points and
  midpoints lie on the finer one (MPFR's and Malachite's `subnormalize`).
-/

namespace Azurite
namespace RoundingTarget

theorem compare_coe_coe (a b : ℝ) : compare (a : EReal) (b : EReal) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (EReal.coe_lt_coe_iff.mpr h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (EReal.coe_lt_coe_iff.mpr h)]

private theorem coe_sub_coe (a b : ℝ) :
    ((a : ℝ) : EReal) - (b : EReal) = ((a - b : ℝ) : EReal) :=
  (EReal.coe_sub a b).symm

/-- An integer within less than `1/2` of `x` is its nearest rounding. -/
theorem toInt_round_nearest_eq_of_abs_lt {x : ℝ} {n : ℤ} (h : |x - n| < 1 / 2) :
    toInt (round intSet .Nearest x) = n := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have hF := val_roundFloor_intSet x
  have hC := val_roundCeiling_intSet x
  rcases lt_trichotomy (n : ℝ) x with hlt | heq | hgt
  · have hfl : ⌊x⌋ = n := by rw [Int.floor_eq_iff]; constructor <;> linarith
    have hceil : ⌈x⌉ = n + 1 := by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    have hcmp : (x : EReal) - (roundFloor intSet x).val
        < (roundCeiling intSet x).val - (x : EReal) := by
      rw [hF, hC, hfl, hceil, coe_sub_coe, coe_sub_coe, EReal.coe_lt_coe_iff]
      push_cast; linarith
    unfold round
    simp only []
    rw [compare_lt_iff_lt.mpr hcmp]
    exact toInt_eq_of_val (by rw [hF, hfl])
  · have hmem : ((x : ℝ) : EReal) ∈ intSet := ⟨n, by rw [heq]⟩
    exact toInt_eq_of_val (by rw [val_round_of_mem _ _ hmem, heq])
  · have hceil : ⌈x⌉ = n := by rw [Int.ceil_eq_iff]; constructor <;> linarith
    have hfl : ⌊x⌋ = n - 1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hcmp : (roundCeiling intSet x).val - (x : EReal)
        < (x : EReal) - (roundFloor intSet x).val := by
      rw [hF, hC, hfl, hceil, coe_sub_coe, coe_sub_coe, EReal.coe_lt_coe_iff]
      push_cast; linarith
    unfold round
    simp only []
    rw [compare_gt_iff_gt.mpr hcmp]
    exact toInt_eq_of_val (by rw [hC, hceil])

/-- At an exact half, the even neighbour wins. -/
theorem toInt_round_nearest_half (n : ℤ) :
    toInt (round intSet .Nearest ((n : ℝ) + 1 / 2)) = if Even n then n else n + 1 := by
  set x : ℝ := (n : ℝ) + 1 / 2 with hx
  have hF := val_roundFloor_intSet x
  have hC := val_roundCeiling_intSet x
  have hfl : ⌊x⌋ = n := by rw [Int.floor_eq_iff]; constructor <;> linarith
  have hceil : ⌈x⌉ = n + 1 := by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  have hcmp : (x : EReal) - (roundFloor intSet x).val
      = (roundCeiling intSet x).val - (x : EReal) := by
    rw [hF, hC, hfl, hceil, coe_sub_coe, coe_sub_coe, EReal.coe_eq_coe_iff]
    push_cast; linarith
  have hFn : toInt (roundFloor intSet x) = n := toInt_eq_of_val (by rw [hF, hfl])
  have hCn : toInt (roundCeiling intSet x) = n + 1 := toInt_eq_of_val (by rw [hC, hceil])
  unfold round
  simp only []
  rw [compare_eq_iff_eq.mpr hcmp]
  show toInt (intTiebreak (roundFloor intSet x) (roundCeiling intSet x)) = _
  unfold intTiebreak
  rw [hFn, hCn]
  by_cases he : Even n
  · have hno : ¬ Even (n + 1) := fun h => (Int.even_add_one.mp h) he
    split_ifs with h1 h2 <;>
      first | exact hFn | exact absurd h2.2 he | exact absurd ⟨he, hno⟩ h1
  · have hyes : Even (n + 1) := Int.even_add_one.mpr he
    split_ifs with h1 h2 <;>
      first | exact absurd h1.1 he | exact hCn | exact absurd ⟨hyes, he⟩ h2

/-- The nearest integer is within `1/2`. -/
theorem abs_sub_toInt_round_nearest_le (x : ℝ) :
    |x - toInt (round intSet .Nearest x)| ≤ 1 / 2 := by
  set n := ⌊x + 1 / 2⌋ with hn
  have h1 : (n : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < n + 1 := Int.lt_floor_add_one _
  rcases eq_or_lt_of_le h1 with heq | hlt
  · -- `x = n − 1/2 = (n − 1) + 1/2`
    have hx : x = ((n - 1 : ℤ) : ℝ) + 1 / 2 := by push_cast; linarith
    rw [hx, toInt_round_nearest_half]
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
  · rw [toInt_round_nearest_eq_of_abs_lt (n := n) (by rw [abs_lt]; constructor <;> linarith)]
    rw [abs_le]; constructor <;> linarith

/-- The nearest integer is at least as close as any integer. -/
theorem abs_toInt_round_nearest_sub_le (x : ℝ) (m : ℤ) :
    |x - toInt (round intSet .Nearest x)| ≤ |x - m| := by
  rcases lt_or_ge |x - m| (1 / 2) with hlt | hge
  · rw [toInt_round_nearest_eq_of_abs_lt hlt]
  · exact (abs_sub_toInt_round_nearest_le x).trans hge

/-- `R` is a nearest integer to `y`, an exact half resolved by the ternary `o` (`.lt`: the true
value is above `y`, round up; `.gt`: round down; `.eq`: to even). -/
def NearestTernary (y : ℝ) (R : ℤ) (o : Ordering) : Prop :=
  |y - R| ≤ 1 / 2 ∧ (|y - R| = 1 / 2 →
    (o = .lt → y < R) ∧ (o = .gt → (R : ℝ) < y) ∧ (o = .eq → Even R))

/-- Negating the value and the result swaps the ternary. -/
theorem nearestTernary_neg {y : ℝ} {R : ℤ} {o : Ordering} (h : NearestTernary y R o.swap) :
    NearestTernary (-y) (-R) o := by
  obtain ⟨h1, h2⟩ := h
  have e : |-y - ((-R : ℤ) : ℝ)| = |y - R| := by
    push_cast; rw [show -y - -(R : ℝ) = -(y - R) by ring, abs_neg]
  refine ⟨by rw [e]; exact h1, fun hh => ?_⟩
  rw [e] at hh
  obtain ⟨hlt, hgt, heq⟩ := h2 hh
  refine ⟨fun ho => ?_, fun ho => ?_, fun ho => ?_⟩
  · have := hgt (by rw [ho]; rfl)
    push_cast; linarith
  · have := hlt (by rw [ho]; rfl)
    push_cast; linarith
  · have := heq (by rw [ho]; rfl)
    exact even_neg.mpr this

/-- **Double rounding with a ternary.**  `X` is at least as close to `w` as every integer and
every half-integer in range (`|w| < B`, `1 ≤ B`), and `R` is `NearestTernary` for `X` with the
ternary `compare X w`; then `R` is the nearest integer to `w`. -/
theorem toInt_round_nearest_of_ternary {w X : ℝ} {R : ℤ} {B : ℤ} (hB : |w| < B)
    (hclose : ∀ m : ℤ, |m| ≤ B → |X - w| ≤ |(m : ℝ) - w|)
    (hclose' : ∀ m : ℤ, -B ≤ m → m ≤ B - 1 → |X - w| ≤ |(m : ℝ) + 1 / 2 - w|)
    (hR : NearestTernary X R (compare X w)) :
    toInt (round intSet .Nearest w) = R := by
  obtain ⟨hR1, hR2⟩ := hR
  set n := ⌊w⌋ with hn
  have hn1 : (n : ℝ) ≤ w := Int.floor_le w
  have hn2 : w < n + 1 := Int.lt_floor_add_one w
  obtain ⟨hw1, hw2⟩ := abs_lt.mp hB
  have hnB : -B ≤ n := Int.le_floor.mpr (by rw [Int.cast_neg]; linarith)
  have hnB' : n ≤ B - 1 := by
    have : (n : ℝ) < B := by linarith
    have : n < B := by exact_mod_cast this
    omega
  have hc1 := hclose n (by rw [abs_le]; constructor <;> omega)
  have hc3 := hclose (n + 1) (by rw [abs_le]; constructor <;> omega)
  have hc2 := hclose' n hnB hnB'
  have hRa := abs_le.mp hR1
  rcases lt_trichotomy w ((n : ℝ) + 1 / 2) with hw | hw | hw
  · -- `w` below the midpoint: the rounding is `n`
    rw [toInt_round_nearest_eq_of_abs_lt (n := n) (by rw [abs_lt]; constructor <;> linarith)]
    have hXlo : (n : ℝ) ≤ X := by
      rw [abs_of_nonpos (a := (n : ℝ) - w) (by linarith)] at hc1
      have := abs_le.mp hc1; linarith
    have hXhi : X ≤ (n : ℝ) + 1 / 2 := by
      rw [abs_of_nonneg (a := (n : ℝ) + 1 / 2 - w) (by linarith)] at hc2
      have := abs_le.mp hc2; linarith
    rcases lt_or_eq_of_le hXhi with hXlt | hXeq
    · have h1 : (R : ℝ) < n + 1 := by linarith
      have h2 : (n : ℝ) - 1 < R := by linarith
      have h1' : R < n + 1 := by exact_mod_cast h1
      have h2' : n - 1 < R := by exact_mod_cast h2
      omega
    · have hcmp : compare X w = .gt := compare_gt_iff_gt.mpr (by linarith)
      have hhalf : |X - R| = 1 / 2 := by
        rcases eq_or_lt_of_le hR1 with h | h
        · exact h
        · exfalso
          obtain ⟨h1, h2⟩ := abs_lt.mp h
          have h1' : n < R := by exact_mod_cast (by linarith : (n : ℝ) < R)
          have h2' : R < n + 1 := by exact_mod_cast (by linarith : (R : ℝ) < n + 1)
          omega
      have hlt := (hR2 hhalf).2.1 hcmp
      have h1' : n ≤ R := by exact_mod_cast (by linarith : (n : ℝ) ≤ R)
      have h2' : R < n + 1 := by exact_mod_cast (by linarith : (R : ℝ) < n + 1)
      omega
  · -- `w` is the midpoint: `X = w`, a genuine tie
    have hX : X = w := by
      have h0 : |(n : ℝ) + 1 / 2 - w| = 0 := by rw [hw]; simp
      rw [h0] at hc2
      have := abs_nonneg (X - w)
      have : |X - w| = 0 := le_antisymm hc2 this
      linarith [abs_eq_zero.mp this]
    have hcmp : compare X w = .eq := compare_eq_iff_eq.mpr hX
    rw [hw, toInt_round_nearest_half]
    have hhalf : |X - R| = 1 / 2 := by
      rcases eq_or_lt_of_le hR1 with h | h
      · exact h
      · exfalso
        obtain ⟨h1, h2⟩ := abs_lt.mp h
        rw [hX, hw] at h1 h2
        have h1' : n < R := by exact_mod_cast (by linarith : (n : ℝ) < R)
        have h2' : R < n + 1 := by exact_mod_cast (by linarith : (R : ℝ) < n + 1)
        omega
    have hev := (hR2 hhalf).2.2 hcmp
    rw [hX, hw] at hRa
    have h1' : n ≤ R := by exact_mod_cast (by linarith : (n : ℝ) ≤ R)
    have h2' : R ≤ n + 1 := by exact_mod_cast (by linarith : (R : ℝ) ≤ n + 1)
    rcases (by omega : R = n ∨ R = n + 1) with hRn | hRn
    · subst hRn
      simp only [hev, ↓reduceIte]
    · subst hRn
      have : ¬ Even n := Int.even_add_one.mp hev
      simp only [this, ↓reduceIte]
  · -- `w` above the midpoint: the rounding is `n + 1`
    rw [toInt_round_nearest_eq_of_abs_lt (n := n + 1)
      (by rw [abs_lt]; push_cast; constructor <;> linarith)]
    have hXhi : X ≤ (n : ℝ) + 1 := by
      rw [abs_of_nonneg (a := ((n + 1 : ℤ) : ℝ) - w) (by push_cast; linarith)] at hc3
      have := abs_le.mp hc3; push_cast at this
      linarith
    have hXlo : (n : ℝ) + 1 / 2 ≤ X := by
      rw [abs_of_nonpos (a := (n : ℝ) + 1 / 2 - w) (by linarith)] at hc2
      have := abs_le.mp hc2; linarith
    rcases lt_or_eq_of_le hXlo with hXlt | hXeq
    · have h1 : (R : ℝ) < n + 2 := by linarith
      have h2 : (n : ℝ) < R := by linarith
      have h1' : R < n + 2 := by exact_mod_cast h1
      have h2' : n < R := by exact_mod_cast h2
      omega
    · have hcmp : compare X w = .lt := compare_lt_iff_lt.mpr (by linarith)
      have hhalf : |X - R| = 1 / 2 := by
        rcases eq_or_lt_of_le hR1 with h | h
        · exact h
        · exfalso
          obtain ⟨h1, h2⟩ := abs_lt.mp h
          have h1' : n < R := by exact_mod_cast (by linarith : (n : ℝ) < R)
          have h2' : R < n + 1 := by exact_mod_cast (by linarith : (R : ℝ) < n + 1)
          omega
      have hlt := (hR2 hhalf).1 hcmp
      have h1' : n < R := by exact_mod_cast (by linarith : (n : ℝ) < R)
      have h2' : R ≤ n + 1 := by exact_mod_cast (by linarith : (R : ℝ) ≤ n + 1)
      omega

end RoundingTarget
end Azurite
