/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Equiv.Cbrt
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Rsqrt
import Azurite.AzFloat.Equiv.Shift
import Azurite.AzFloat.Equiv.Sqrt
import Azurite.AzFloat.Equiv.Ziv
import Mathlib.NumberTheory.Real.Irrational

/-!
# The constants are lifts

Each `cPrecRound p mode` equals `liftVal₀ (some c) p mode` for its real value `c`: the square
roots and reciprocal square roots from the lifts of `sqrtPrecRound` and `rsqrtPrecRound` at the
exact floats `2`, `3`, `5` (`toVal_two`, `toVal_ofAzNat`).  For the golden ratio this file
proves the bracket `phiApprox_spec`/`phiApprox_encloses` (width `≤ 2^(1 − w)`), the
irrationality `irrational_phi` and the Ziv certificate `phiApprox_isSome_exists`; the loop and
its specification are in `Phi.lean`/`Equiv/Phi.lean`.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### Values of the exact floats -/

/-- The value of the constant `two`. -/
theorem toVal_two : toVal two = some ((2 : ℝ) : EReal) := by
  unfold two powerOf2
  rw [toVal_mkFinite _ _ _ _ (by decide)]
  congr 2
  unfold finiteVal
  rw [AzInt.toInt_add]
  simp only [↓reduceIte, one_mul, show (1 : AzNat).toNat = 1 from rfl, Nat.cast_one,
    show (1 : AzNat).size = 1 from rfl, show (1 : AzInt).toInt = 1 from rfl]
  norm_num

/-- The value of the constant `oneHalf`. -/
theorem toVal_oneHalf : toVal oneHalf = some ((1 / 2 : ℝ) : EReal) := by
  unfold oneHalf powerOf2
  rw [toVal_mkFinite _ _ _ _ (by decide)]
  congr 2
  unfold finiteVal
  rw [AzInt.toInt_add, AzInt.toInt_neg]
  simp only [↓reduceIte, one_mul, show (1 : AzNat).toNat = 1 from rfl, Nat.cast_one,
    show (1 : AzNat).size = 1 from rfl, show (1 : AzInt).toInt = 1 from rfl]
  norm_num

/-- The value of `ofAzNat (AzNat.ofNat n)`. -/
theorem toVal_ofAzNat_ofNat (n : ℕ) : toVal (ofAzNat (AzNat.ofNat n)) = some ((n : ℝ) : EReal) := by
  rw [toVal_ofAzNat, AzNat.toNat_ofNat]

/-! ### Square roots and reciprocal square roots -/

/-- `√2` is the lift of its value. -/
theorem sqrt2PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrt2PrecRound p mode = liftVal₀ (some ((Real.sqrt 2 : ℝ) : EReal)) p mode := by
  unfold sqrt2PrecRound liftVal₀
  rw [sqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_two, Option.bind_some, Spec.sqrt_coe 2 (by norm_num)]

/-- `∛2` is the lift of its value. -/
theorem cbrt2PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    cbrt2PrecRound p mode = liftVal₀ (some ((realCbrt 2 : ℝ) : EReal)) p mode := by
  unfold cbrt2PrecRound liftVal₀
  rw [cbrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_two, Option.bind_some, Spec.cbrt_coe]

/-- `√3` is the lift of its value. -/
theorem sqrt3PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrt3PrecRound p mode = liftVal₀ (some ((Real.sqrt 3 : ℝ) : EReal)) p mode := by
  unfold sqrt3PrecRound liftVal₀
  rw [sqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_ofAzNat_ofNat, Nat.cast_ofNat, Option.bind_some, Spec.sqrt_coe 3 (by norm_num)]

/-- `√5` is the lift of its value. -/
theorem sqrt5PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrt5PrecRound p mode = liftVal₀ (some ((Real.sqrt 5 : ℝ) : EReal)) p mode := by
  unfold sqrt5PrecRound liftVal₀
  rw [sqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_ofAzNat_ofNat, Nat.cast_ofNat, Option.bind_some, Spec.sqrt_coe 5 (by norm_num)]

/-- `1/√r = √r / r`. -/
theorem inv_sqrt_eq (r : ℝ) : (Real.sqrt r)⁻¹ = Real.sqrt r / r := by
  rw [inv_eq_one_div, ← Real.sqrt_div_self']

/-- `√2 / 2` is the lift of its value. -/
theorem sqrt2Over2PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrt2Over2PrecRound p mode = liftVal₀ (some ((Real.sqrt 2 / 2 : ℝ) : EReal)) p mode := by
  unfold sqrt2Over2PrecRound liftVal₀
  rw [rsqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_two, Option.bind_some, Spec.rsqrt_coe 2 (by norm_num), inv_sqrt_eq 2]

/-- `√3 / 3` is the lift of its value. -/
theorem sqrt3Over3PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrt3Over3PrecRound p mode = liftVal₀ (some ((Real.sqrt 3 / 3 : ℝ) : EReal)) p mode := by
  unfold sqrt3Over3PrecRound liftVal₀
  rw [rsqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_ofAzNat_ofNat, Nat.cast_ofNat, Option.bind_some, Spec.rsqrt_coe 3 (by norm_num),
    inv_sqrt_eq 3]

/-- `√5 / 5` is the lift of its value. -/
theorem sqrt5Over5PrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    sqrt5Over5PrecRound p mode = liftVal₀ (some ((Real.sqrt 5 / 5 : ℝ) : EReal)) p mode := by
  unfold sqrt5Over5PrecRound liftVal₀
  rw [rsqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_ofAzNat_ofNat, Nat.cast_ofNat, Option.bind_some, Spec.rsqrt_coe 5 (by norm_num),
    inv_sqrt_eq 5]

/-! ### The golden ratio -/

/-- Facts about `√5`. -/
theorem sqrt5_facts : Real.sqrt 5 ^ 2 = 5 ∧ 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  refine ⟨h, by nlinarith, by nlinarith⟩

/-- `√5` is irrational. -/
theorem irrational_sqrt5 : Irrational (Real.sqrt 5) := by
  have h5 : ¬ IsSquare 5 := by
    rintro ⟨r, hr⟩
    have : r ≤ 3 := by nlinarith
    interval_cases r <;> omega
  have := (irrational_sqrt_natCast_iff (n := 5)).mpr h5
  simpa using this

/-- The bracket of `φ` at working precision `w`: `l ≤ √5 ≤ l + ε` with `ε = 0` exactly when
the truncation is exact and `ε ≤ 2^(2 − w)`, and the two ends round `l/2 + 1/2` and
`(l + ε)/2 + 1/2`. -/
theorem phiApprox_spec (w : ℕ) [NeZero w] :
    ∃ lov e₁ : ℝ, lov ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ lov + e₁ ∧ (lov = Real.sqrt 5 → e₁ = 0) ∧
      0 ≤ e₁ ∧ e₁ ≤ (2 : ℝ) ^ (2 - (w : ℤ)) ∧
      Rounds (phiApprox w).1 (lov / 2 + 1 / 2) ∧
      Rounds (phiApprox w).2 ((lov + e₁) / 2 + 1 / 2) := by
  unfold phiApprox
  simp only
  rw [sqrtPrecRound_eq_liftVal]
  unfold liftVal
  rw [toVal_ofAzNat_ofNat, Nat.cast_ofNat, Option.bind_some, Spec.sqrt_coe 5 (by norm_num)]
  obtain ⟨lov, e₁, hlo, he₁, hlo1, hlo2, hlo3, hlo4, hlo5, hmem⟩ := truncError_spec w (Real.sqrt 5)
  obtain ⟨_, hs5gt, hs5lt⟩ := sqrt5_facts
  -- `0 ≤ l`, as `0` is a float below `√5`
  have hlofl : ((lov : ℝ) : EReal) = (roundFloor (precisionSet 2 w) (Real.sqrt 5)).val := by
    rw [fst_roundVal] at hlo
    change (ofEReal w .Floor (Real.sqrt 5 : ℝ)).toVal = _ at hlo
    have h := (ofEReal_spec w .Floor (Real.sqrt 5)).2
    rw [val_round_floatSet] at h
    rw [h, Option.some.injEq] at hlo
    exact hlo.symm
  have hlo0 : 0 ≤ lov := by
    have := (isGreatest_roundFloor (precisionSet 2 w) (Real.sqrt 5)).2
      ⟨Or.inl (by simp), EReal.coe_le_coe_iff.mpr (Real.sqrt_nonneg 5)⟩
    rw [← hlofl] at this
    exact EReal.coe_le_coe_iff.mp (by simpa using this)
  have hbound : e₁ ≤ (2 : ℝ) ^ (2 - (w : ℤ)) := by
    rcases eq_or_ne e₁ 0 with h0 | h0
    · rw [h0]; positivity
    · obtain ⟨k, hk, hk1, _⟩ := hlo5 h0
      rw [abs_of_nonneg hlo0] at hk1
      have : k - 1 < 2 := (zpow_lt_zpow_iff_right₀ (by norm_num)).mp
        (lt_of_le_of_lt hk1 (by linarith : lov < (2 : ℝ) ^ (2 : ℤ)))
      rw [hk]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the next float up
  have hhi : (addPrecRound (roundVal w .Floor (some ((Real.sqrt 5 : ℝ) : EReal))).1
      (truncError (roundVal w .Floor (some ((Real.sqrt 5 : ℝ) : EReal)))) w .Ceiling).1.toVal
      = some ((lov + e₁ : ℝ) : EReal) := by
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hlo, he₁, Option.bind_some, Option.bind_some, Spec.add_coe_coe, fst_roundVal]
    change (ofEReal w .Ceiling ((lov + e₁ : ℝ) : EReal)).toVal = _
    rw [(ofEReal_spec w .Ceiling (lov + e₁)).2, val_round_of_mem _ .Ceiling hmem]
  have hshift : ∀ (f : AzFloat) (v : ℝ), f.toVal = some (v : EReal) →
      (f >>> (1 : Nat)).toVal = some ((v / 2 : ℝ) : EReal) := by
    intro f v hf
    show (shiftRight f (AzNat.ofNat 1).toAzInt).toVal = _
    rw [toVal_shiftRight, hf, Option.map_some, toInt_toAzInt, AzNat.toNat_ofNat, ← EReal.coe_mul]
    congr 2
    push_cast
    rw [zpow_neg_one, div_eq_mul_inv]
  refine ⟨lov, e₁, hlo1, hlo2, hlo3, hlo4, hbound, ?_, ?_⟩
  · intro p'' _ mo
    beta_reduce
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hshift _ _ hlo, toVal_oneHalf, Option.bind_some, Option.bind_some, Spec.add_coe_coe]
  · intro p'' _ mo
    beta_reduce
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hshift _ _ hhi, toVal_oneHalf, Option.bind_some, Option.bind_some, Spec.add_coe_coe]

/-- `φ = (1 + √5)/2` is irrational. -/
theorem irrational_phi : Irrational ((1 + Real.sqrt 5) / 2) := by
  have h := (irrational_sqrt5.ratCast_add (q := 1)).div_natCast (by norm_num : (2 : ℕ) ≠ 0)
  simpa using h

/-- `phiApprox w` encloses `φ` with width at most `2^(1 − w)`, and the lower end is `φ` only
when the upper end is. -/
theorem phiApprox_encloses (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, Rounds (phiApprox w).1 lv ∧ Rounds (phiApprox w).2 hv ∧
      lv ≤ (1 + Real.sqrt 5) / 2 ∧ (1 + Real.sqrt 5) / 2 ≤ hv ∧
      (lv = (1 + Real.sqrt 5) / 2 → hv = (1 + Real.sqrt 5) / 2) ∧
      hv - lv ≤ (2 : ℝ) ^ (1 - (w : ℤ)) := by
  obtain ⟨lov, e₁, h1, h2, h3, h4, he₁, hl, hh⟩ := phiApprox_spec w
  refine ⟨_, _, hl, hh, by linarith, by linarith, ?_, ?_⟩
  · intro h
    have : lov = Real.sqrt 5 := by linarith
    rw [h3 this, add_zero, this]
    ring
  · have h2 : (2 : ℝ) ^ (2 - (w : ℤ)) / 2 = 2 ^ (1 - (w : ℤ)) := by
      rw [show (2 : ℤ) - w = (1 - (w : ℤ)) + 1 by ring, zpow_add_one₀ (by norm_num)]
      ring
    linarith

theorem tendsto_two_zpow_one_sub :
    Filter.Tendsto (fun w : ℕ => (2 : ℝ) ^ (1 - (w : ℤ))) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
  rw [mul_zero] at h
  refine h.congr fun w => ?_
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_one, zpow_neg, zpow_natCast, one_div_pow,
    one_div]

/-- The termination certificate for `φ`: at some working precision `w₀ · 2^f`, rounding is
possible. -/
theorem phiApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (phiApprox (w₀ * 2 ^ f)).1 (phiApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode phiApprox irrational_phi
    (fun w => (2 : ℝ) ^ (1 - (w : ℤ))) tendsto_two_zpow_one_sub 1
    (fun w hw => by
      have : NeZero w := ⟨by omega⟩
      obtain ⟨lv, hv, hl, hh, hlo, hhi, -, hwid⟩ := phiApprox_encloses w
      exact ⟨lv, hv, hl, hh, hlo, hhi, hwid⟩) w₀ hw₀

end Azurite.AzFloat
