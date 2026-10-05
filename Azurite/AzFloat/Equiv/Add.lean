/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.Equiv.RoundScaled
import Azurite.AzNat.Equiv.Sub

/-!
# Correctness of addition and subtraction

The specification `Spec.add` is `EReal` addition with `∞ + (−∞)` undefined; the theorem
`addPrecRound_eq_liftVal₂` says `addPrecRound x y p mode = liftVal₂ Spec.add x y p mode`.
The proof goes through `roundScaled_eq_roundVal` (rounding an exact `±S · 2^w` is `roundVal`),
the exact near case, and the far case via `roundVal_congr_cell`: two reals with no integer or
half-integer strictly between them round identically in every mode, with equal comparison
tags.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real addition, undefined (`NaN`) for `∞ + (−∞)`. -/
noncomputable def add (a b : EReal) : Option EReal :=
  if (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) then none else some (a + b)

/-- Extended-real subtraction. -/
noncomputable def sub (a b : EReal) : Option EReal := add a (-b)

theorem add_coe_coe (x y : ℝ) : add (x : EReal) (y : EReal) = some ((x + y : ℝ) : EReal) := by
  unfold add
  rw [ite_eq_right (by simp), EReal.coe_add]

theorem add_zero_left (b : EReal) : add 0 b = some b := by
  unfold add
  rw [ite_eq_right (by simp), zero_add]

theorem add_zero_right (a : EReal) : add a 0 = some a := by
  unfold add
  rw [ite_eq_right (by simp), add_zero]

end Spec

/-- The value `B = nb · 2^(eb − |nb|)` is below `2^eb` by at least `2^(eb − |nb|)`. -/
theorem finiteVal_true_le (e : AzInt) (m : AzNat) :
    finiteVal true e m + (2 : ℝ) ^ (e.toInt - m.size) ≤ (2 : ℝ) ^ e.toInt := by
  rw [finiteVal_true_eq]
  have hhi : m.toNat + 1 ≤ 2 ^ m.size := by
    have : m.toNat < 2 ^ m.size := by rw [← Nat.size_le, AzNat.size_toNat]
    omega
  have hhi' : (m.toNat : ℝ) + 1 ≤ (2 : ℝ) ^ m.size := by exact_mod_cast hhi
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
  calc (m.toNat : ℝ) * 2 ^ (e.toInt - m.size) + 2 ^ (e.toInt - m.size)
      = ((m.toNat : ℝ) + 1) * 2 ^ (e.toInt - m.size) := by ring
    _ ≤ (2 : ℝ) ^ m.size * 2 ^ (e.toInt - m.size) := mul_le_mul_of_nonneg_right hhi' h2.le
    _ = (2 : ℝ) ^ e.toInt := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring

/-- The far case of addition and subtraction: with `T = max |nb| p` and `0 < C < 2^(eb − T − 2)`,
`B ± C` and the representative `B ± 2^(eb − T − 3)` round identically at precision `p`. -/
theorem roundVal_far (p : ℕ) [NeZero p] (mode : RoundingMode) (s add : Bool) (eb : AzInt)
    (nb : AzNat) (hnb : nb ≠ 0) (T : ℕ) (hT : nb.size ≤ T) (hTp : p ≤ T) (C : ℝ) (hC0 : 0 < C)
    (hC : C < (2 : ℝ) ^ (eb.toInt - T - 2)) :
    roundVal p mode (some (((if s then 1 else -1) *
        (finiteVal true eb nb + (if add then C else -C)) : ℝ) : EReal))
      = roundVal p mode (some (((if s then 1 else -1) *
        (finiteVal true eb nb + (if add then 1 else -1) * (2 : ℝ) ^ (eb.toInt - T - 3)) : ℝ)
          : EReal)) := by
  set B := finiteVal true eb nb with hB
  set j : ℤ := eb.toInt - T - 2 with hj
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) _
  have hhalf : (2 : ℝ) ^ (eb.toInt - T - 3) = 2 ^ j / 2 := by
    rw [hj, show eb.toInt - T - 3 = (eb.toInt - T - 2) - 1 by ring, zpow_sub_one₀ (by norm_num)]
    ring
  -- `B` is `K · 2^j` for the integer `K = nb · 2^(T − |nb| + 2) ≥ 4`
  set K : ℤ := (nb.toNat : ℤ) * 2 ^ (T - nb.size + 2) with hK
  have hBK : B = (K : ℝ) * 2 ^ j := by
    rw [hB, finiteVal_true_eq, hK, hj]
    push_cast
    rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 2
    push_cast
    rw [Nat.cast_sub hT]
    ring
  have hK4 : 4 ≤ K := by
    rw [hK]
    have h1 : (1 : ℤ) ≤ nb.toNat := by
      exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hnb)
    have h2 : (4 : ℤ) ≤ 2 ^ (T - nb.size + 2) := by
      calc (4 : ℤ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (T - nb.size + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  -- bounds on the binary logarithm of everything in the cell
  have hBlo : (2 : ℝ) ^ (eb.toInt - 1) ≤ B := by
    have := (abs_finiteVal_bounds' true eb nb hnb).1
    rwa [abs_of_pos (finiteVal_true_pos' eb nb hnb)] at this
  have hjlt : (2 : ℝ) ^ j ≤ 2 ^ (eb.toInt - 2) := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hlog_lb : ∀ z : ℝ, (2 : ℝ) ^ (eb.toInt - 2) ≤ z → eb.toInt - 2 ≤ Int.log 2 z := fun z hz =>
    (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (lt_of_lt_of_le (by positivity) hz)).mp
      (by simpa using hz)
  -- membership in a cell from its left endpoint
  have cell_of : ∀ (k : ℤ) (L z : ℝ), (k : ℝ) * 2 ^ j = L → L < z → z < L + 2 ^ j →
      (k : ℝ) * 2 ^ j < z ∧ z < ((k : ℝ) + 1) * 2 ^ j := by
    intro k L z hk h1 h2
    rw [add_mul, one_mul, hk]
    exact ⟨h1, h2⟩
  have hKm : (((K - 1 : ℤ) : ℝ)) * 2 ^ j = B - 2 ^ j := by push_cast; rw [hBK]; ring
  have hKn : (((-(K + 1) : ℤ) : ℝ)) * 2 ^ j = -(B + 2 ^ j) := by push_cast; rw [hBK]; ring
  have hKn' : (((-K : ℤ) : ℝ)) * 2 ^ j = -B := by push_cast; rw [hBK]; ring
  have hBpos : 0 < B := finiteVal_true_pos' eb nb hnb
  have h2e2 : (0 : ℝ) < 2 ^ (eb.toInt - 2) := zpow_pos (by norm_num) _
  have h12 : (2 : ℝ) ^ (eb.toInt - 1) = 2 * 2 ^ (eb.toInt - 2) := by
    rw [show eb.toInt - 1 = (eb.toInt - 2) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring
  cases add with
  | true =>
    simp only [↓reduceIte, one_mul]
    have hv := cell_of K B (B + C) hBK.symm (by linarith) (by linarith)
    have hv' := cell_of K B (B + 2 ^ j / 2) hBK.symm (by linarith) (by linarith)
    have hlog : Int.log 2 |B + C| = Int.log 2 |B + 2 ^ j / 2| := by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      exact log_eq_of_cell j K (by omega) _ _ hv hv'
    have hjle : j ≤ Int.log 2 |B + C| - p := by
      rw [abs_of_pos (by linarith)]
      have := hlog_lb (B + C) (by linarith)
      omega
    rw [hhalf]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
      exact roundVal_congr_cell p mode j (-(K + 1)) _ _
        (cell_of _ _ _ hKn (by linarith) (by linarith))
        (cell_of _ _ _ hKn (by linarith) (by linarith))
        (by rw [abs_neg, abs_neg]; exact hlog) (by rw [abs_neg]; exact hjle)
    · simp only [↓reduceIte, one_mul]
      exact roundVal_congr_cell p mode j K _ _ hv hv' hlog hjle
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    have hv := cell_of (K - 1) (B - 2 ^ j) (B + -C) hKm (by linarith) (by linarith)
    have hv' := cell_of (K - 1) (B - 2 ^ j) (B + -(2 ^ j / 2)) hKm (by linarith) (by linarith)
    have hlog : Int.log 2 |B + -C| = Int.log 2 |B + -(2 ^ j / 2)| := by
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      exact log_eq_of_cell j (K - 1) (by omega) _ _ hv hv'
    have hjle : j ≤ Int.log 2 |B + -C| - p := by
      rw [abs_of_pos (by linarith)]
      have := hlog_lb (B + -C) (by linarith)
      omega
    rw [hhalf]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
      exact roundVal_congr_cell p mode j (-K) _ _
        (cell_of _ _ _ hKn' (by linarith) (by linarith))
        (cell_of _ _ _ hKn' (by linarith) (by linarith))
        (by rw [abs_neg, abs_neg]; exact hlog) (by rw [abs_neg]; exact hjle)
    · simp only [↓reduceIte, one_mul]
      exact roundVal_congr_cell p mode j (K - 1) _ _ hv hv' hlog hjle

theorem toInt_far_scale (eb : AzInt) (T : ℕ) :
    (eb - (AzNat.ofNat (T + 3)).toAzInt).toInt = eb.toInt - T - 3 := by
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]; push_cast; ring

theorem far_gap (eb ec : AzInt) (T : ℕ) (h : (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec) :
    (T : ℤ) + 2 ≤ eb.toInt - ec.toInt := by
  have := (AzInt.le_iff_toInt_le _ _).mp h
  rw [toInt_toAzInt, AzNat.toNat_ofNat, AzInt.toInt_sub] at this
  push_cast at this
  exact this

/-- `C < 2^(e_c) ≤ 2^(e_b − T − 2)` in the far case. -/
theorem far_bound (eb ec : AzInt) (nc : AzNat) (hnc : nc ≠ 0) (T : ℕ)
    (h : (T : ℤ) + 2 ≤ eb.toInt - ec.toInt) :
    finiteVal true ec nc < (2 : ℝ) ^ (eb.toInt - T - 2) := by
  have := (abs_finiteVal_bounds' true ec nc hnc).2
  rw [abs_of_pos (finiteVal_true_pos' ec nc hnc)] at this
  exact lt_of_lt_of_le this (zpow_le_zpow_right₀ (by norm_num) (by omega))

/-- The representative `8·nb ± 1` at scale `e_b − T − 3`, as a real. -/
theorem far_representative (eb : AzInt) (nb : AzNat) (T : ℕ) (hT : nb.size ≤ T) :
    ((nb.shiftLeft (T - nb.size + 3)).toNat : ℝ) * (2 : ℝ) ^ (eb.toInt - T - 3)
      = finiteVal true eb nb := by
  rw [AzNat.toNat_shiftLeft, finiteVal_true_eq]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 2
  push_cast
  rw [Nat.cast_sub hT]
  ring

theorem alignShifts_eq (wb wc : AzInt) :
    alignShifts wb wc = (min wb wc, (wb - min wb wc).abs.toNat, (wc - min wb wc).abs.toNat) :=
  rfl

/-- A shifted significand on the common scale is the value. -/
theorem shifted_on_scale (e : AzInt) (n : AzNat) (k : ℕ) (w : AzInt)
    (hk : (k : ℤ) = (e - (AzNat.ofNat n.size).toAzInt).toInt - w.toInt) :
    ((n.shiftLeft k).toNat : ℝ) * (2 : ℝ) ^ w.toInt = finiteVal true e n := by
  rw [AzNat.toNat_shiftLeft, finiteVal_true_eq]
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
  congr 2
  rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat] at hk
  omega

/-- `addMagnitudes` is `roundVal` of `±(B + C)`. -/
theorem addMagnitudes_eq (s : Bool) (eb : AzInt) (nb : AzNat) (hnb : nb ≠ 0) (ec : AzInt)
    (nc : AzNat) (hnc : nc ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    addMagnitudes s eb nb ec nc p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true eb nb + finiteVal true ec nc) : ℝ) : EReal)) := by
  unfold addMagnitudes
  simp only
  set T := max nb.size p with hT
  have hT1 : nb.size ≤ T := le_max_left _ _
  have hT2 : p ≤ T := le_max_right _ _
  by_cases hfar : (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec
  · rw [ite_eq_left hfar, roundScaled_eq_roundVal, AzNat.toNat_addUInt64, toInt_far_scale]
    have hS : (((nb.shiftLeft (T - nb.size + 3)).toNat + (1 : UInt64).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (eb.toInt - T - 3)
        = finiteVal true eb nb + 1 * (2 : ℝ) ^ (eb.toInt - T - 3) := by
      rw [UInt64.toNat_one]
      push_cast
      rw [add_mul, far_representative eb nb T hT1]
    rw [mul_assoc, hS]
    have := roundVal_far p mode s true eb nb hnb T hT1 hT2 _ (finiteVal_true_pos' ec nc hnc)
      (far_bound eb ec nc hnc T (far_gap eb ec T hfar))
    simp only [↓reduceIte] at this
    exact this.symm
  · rw [ite_eq_right hfar, alignShifts_eq]
    simp only
    set w := min (eb - (AzNat.ofNat nb.size).toAzInt) (ec - (AzNat.ofNat nc.size).toAzInt)
      with hw_def
    have hkb : (((eb - (AzNat.ofNat nb.size).toAzInt - w).abs.toNat : ℕ) : ℤ)
        = (eb - (AzNat.ofNat nb.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_left _ _)
    have hkc : (((ec - (AzNat.ofNat nc.size).toAzInt - w).abs.toNat : ℕ) : ℤ)
        = (ec - (AzNat.ofNat nc.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_right _ _)
    have hS : (((nb.shiftLeft (eb - (AzNat.ofNat nb.size).toAzInt - w).abs.toNat +
        nc.shiftLeft (ec - (AzNat.ofNat nc.size).toAzInt - w).abs.toNat).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ w.toInt = finiteVal true eb nb + finiteVal true ec nc := by
      rw [AzNat.toNat_add]
      push_cast
      rw [add_mul, shifted_on_scale eb nb _ _ hkb, shifted_on_scale ec nc _ _ hkc]
    rw [roundScaled_eq_roundVal, mul_assoc, hS]

/-- `subMagnitudes` is `roundVal` of `±(B − C)` when `C < B`. -/
theorem subMagnitudes_eq (s : Bool) (eb : AzInt) (nb : AzNat) (hnb : nb ≠ 0) (ec : AzInt)
    (nc : AzNat) (hnc : nc ≠ 0) (hlt : finiteVal true ec nc < finiteVal true eb nb) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    subMagnitudes s eb nb ec nc p mode
      = roundVal p mode (some (((if s then 1 else -1) *
          (finiteVal true eb nb - finiteVal true ec nc) : ℝ) : EReal)) := by
  unfold subMagnitudes
  simp only
  set T := max nb.size p with hT
  have hT1 : nb.size ≤ T := le_max_left _ _
  have hT2 : p ≤ T := le_max_right _ _
  by_cases hfar : (AzNat.ofNat (T + 2)).toAzInt ≤ eb - ec
  · rw [ite_eq_left hfar, roundScaled_eq_roundVal, AzNat.toNat_sub, toInt_far_scale]
    have hpos : 1 ≤ (nb.shiftLeft (T - nb.size + 3)).toNat := by
      rw [AzNat.toNat_shiftLeft]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (toNat_ne_zero_of_ne_zero hnb)
        (pow_ne_zero _ (by norm_num)))
    have hS : (((nb.shiftLeft (T - nb.size + 3)).toNat - (1 : AzNat).toNat : ℕ) : ℝ) *
        (2 : ℝ) ^ (eb.toInt - T - 3)
        = finiteVal true eb nb + (-1) * (2 : ℝ) ^ (eb.toInt - T - 3) := by
      rw [AzNat.toNat_one, Nat.cast_sub hpos]
      push_cast
      rw [sub_mul, far_representative eb nb T hT1]
      ring
    rw [mul_assoc, hS]
    have := roundVal_far p mode s false eb nb hnb T hT1 hT2 _ (finiteVal_true_pos' ec nc hnc)
      (far_bound eb ec nc hnc T (far_gap eb ec T hfar))
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [← sub_eq_add_neg] at this
    exact this.symm
  · rw [ite_eq_right hfar, alignShifts_eq]
    simp only
    set w := min (eb - (AzNat.ofNat nb.size).toAzInt) (ec - (AzNat.ofNat nc.size).toAzInt)
      with hw_def
    set kb := (eb - (AzNat.ofNat nb.size).toAzInt - w).abs.toNat with hkb_def
    set kc := (ec - (AzNat.ofNat nc.size).toAzInt - w).abs.toNat with hkc_def
    have hkb : ((kb : ℕ) : ℤ) = (eb - (AzNat.ofNat nb.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_left _ _)
    have hkc : ((kc : ℕ) : ℤ) = (ec - (AzNat.ofNat nc.size).toAzInt).toInt - w.toInt :=
      AzInt.abs_toNat_sub _ _ (by rw [hw_def, AzInt.toInt_min]; exact min_le_right _ _)
    have hB := shifted_on_scale eb nb kb w hkb
    have hC := shifted_on_scale ec nc kc w hkc
    have hle : (nc.shiftLeft kc).toNat ≤ (nb.shiftLeft kb).toNat := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ w.toInt := zpow_pos (by norm_num) _
      have : ((nc.shiftLeft kc).toNat : ℝ) * 2 ^ w.toInt
          ≤ ((nb.shiftLeft kb).toNat : ℝ) * 2 ^ w.toInt := by
        rw [hB, hC]; exact hlt.le
      exact_mod_cast le_of_mul_le_mul_right this h2
    have hS : (((nb.shiftLeft kb - nc.shiftLeft kc).toNat : ℕ) : ℝ) * (2 : ℝ) ^ w.toInt
        = finiteVal true eb nb - finiteVal true ec nc := by
      rw [AzNat.toNat_sub, Nat.cast_sub hle, sub_mul, hB, hC]
    rw [roundScaled_eq_roundVal, mul_assoc, hS]

theorem signed_sum_sub (s : Bool) (A B : ℝ) :
    (if s then 1 else -1) * A + (if !s then 1 else -1) * B
      = (if s then 1 else -1) * (A - B) := by
  cases s <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] <;> ring

theorem signed_sum_sub' (s : Bool) (A B : ℝ) :
    (if s then 1 else -1) * A + (if !s then 1 else -1) * B
      = (if !s then 1 else -1) * (B - A) := by
  cases s <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] <;> ring

/-- Addition is the float lift of `EReal` addition (`∞ + (−∞)` being `NaN`). -/
theorem addPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    addPrecRound x y p mode = liftVal₂ Spec.add x y p mode := by
  unfold liftVal₂
  cases x with
  | nan => cases y <;> rfl
  | infinity s =>
    cases y with
    | nan => rfl
    | infinity t => cases s <;> cases t <;> simp [addPrecRound, Spec.add]
    | zero => cases s <;> simp [addPrecRound, Spec.add]
    | finite t e q m hv => cases s <;> simp [addPrecRound, Spec.add]
  | zero =>
    cases y with
    | nan => rfl
    | infinity t => cases t <;> simp [addPrecRound, Spec.add]
    | zero =>
      rw [show addPrecRound zero zero p mode = setPrecRound zero p mode from rfl,
        setPrecRound_eq_liftE]
      unfold liftE liftVal
      simp [Spec.add_zero_left]
    | finite t e q m hv =>
      rw [show addPrecRound zero (finite t e q m hv) p mode
        = setPrecRound (finite t e q m hv) p mode from rfl, setPrecRound_eq_liftE]
      unfold liftE liftVal
      simp [Spec.add_zero_left]
  | finite s e₁ p₁ m₁ h₁ =>
    cases y with
    | nan => rfl
    | infinity t => cases t <;> simp [addPrecRound, Spec.add]
    | zero =>
      rw [show addPrecRound (finite s e₁ p₁ m₁ h₁) zero p mode
        = setPrecRound (finite s e₁ p₁ m₁ h₁) p mode from rfl, setPrecRound_eq_liftE]
      unfold liftE liftVal
      simp [Spec.add_zero_right]
    | finite t e₂ p₂ m₂ h₂ =>
      simp only [addPrecRound, toVal_finite, Option.bind_some, Spec.add_coe_coe]
      have hn₁ := coreSignificand_ne_zero h₁
      have hn₂ := coreSignificand_ne_zero h₂
      rw [finiteVal_eq_core s e₁ h₁, finiteVal_eq_core t e₂ h₂, finiteVal_sign s e₁,
        finiteVal_sign t e₂]
      by_cases hst : s = t
      · subst hst
        rw [ite_eq_left rfl, ← mul_add]
        by_cases hlt : AzInt.compare e₁ e₂ = .lt
        · rw [ite_eq_left hlt, addMagnitudes_eq s e₂ _ hn₂ e₁ _ hn₁, add_comm]
        · rw [ite_eq_right hlt, addMagnitudes_eq s e₁ _ hn₁ e₂ _ hn₂]
      · rw [ite_eq_right hst]
        have ht : t = !s := by cases s <;> cases t <;> simp_all
        subst ht
        split <;> rename_i hcmp
        · rw [compareMagnitude_eq e₁ h₁ e₂ h₂, compare_eq_iff_eq, finiteVal_eq_core true e₁ h₁,
            finiteVal_eq_core true e₂ h₂] at hcmp
          rw [hcmp, signed_sum_sub, sub_self, mul_zero, EReal.coe_zero, roundVal_zero]
        · rw [compareMagnitude_eq e₁ h₁ e₂ h₂, compare_gt_iff_gt, finiteVal_eq_core true e₁ h₁,
            finiteVal_eq_core true e₂ h₂] at hcmp
          rw [subMagnitudes_eq s e₁ _ hn₁ e₂ _ hn₂ hcmp, signed_sum_sub]
        · rw [compareMagnitude_eq e₁ h₁ e₂ h₂, compare_lt_iff_lt, finiteVal_eq_core true e₁ h₁,
            finiteVal_eq_core true e₂ h₂] at hcmp
          rw [subMagnitudes_eq (!s) e₂ _ hn₂ e₁ _ hn₁ hcmp, signed_sum_sub']

/-- Subtraction is the float lift of `EReal` subtraction. -/
theorem subPrecRound_eq_liftVal₂ (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    subPrecRound x y p mode = liftVal₂ Spec.sub x y p mode := by
  unfold subPrecRound
  rw [addPrecRound_eq_liftVal₂]
  unfold liftVal₂
  rw [toVal_neg]
  congr 1
  cases toVal y <;> rfl

end Azurite.AzFloat
