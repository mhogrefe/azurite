/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
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
exact floats `2`, `3`, `5` (`toVal_two`, `toVal_ofAzNat`), and the golden ratio from
`zivLoop_eq` with the bracket `phiApprox_spec` and the termination theorem
`phiApprox_possible`: `φ` is irrational, so every boundary `b = M · 2^k` at precision `p` with
`1 ≤ b < 5/2` has `|φ − b| = |√5 − c| / 2` with `c = 2b − 1` a multiple of `2^-p`, and
`|√5 − c| = |5 − c²| / (√5 + c) ≥ 2^-2p / 8` since `5 − c²` is a nonzero multiple of `4^-p`.
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

/-- From the working precision `2p + 6` on, rounding `φ` is possible. -/
theorem phiApprox_possible (p : ℕ) [NeZero p] (mode : RoundingMode) (w : ℕ)
    (hw : 2 * p + 6 ≤ w) :
    (roundingPossible (phiApprox w).1 (phiApprox w).2 p mode).isSome = true := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨lov, e₁, h1, h2, h3, h4, he₁, hl, hh⟩ := phiApprox_spec w
  obtain ⟨hs5, hs5gt, hs5lt⟩ := sqrt5_facts
  set φ := (1 + Real.sqrt 5) / 2 with hφ
  have hφlo : 1 < φ := by rw [hφ]; linarith
  have hφhi : φ < 2 := by rw [hφ]; linarith
  have hφ0 : φ ≠ 0 := by linarith
  apply roundingPossible_isSome_of_no_boundary p mode hl hh (by linarith)
  -- `φ` is not a boundary: it is irrational
  have hφB : ((φ : ℝ) : EReal) ∉ floatSet (p + 1) := by
    intro hB
    obtain ⟨M, k, hMk, _⟩ := boundary_repr p φ hB hφ0
    set a : ℕ := (-k).toNat with ha
    have hka : 0 ≤ k + a := by have := Int.self_le_toNat (-k); omega
    have hpow : (2 : ℝ) ^ k * 2 ^ a = (2 : ℝ) ^ (k + a).toNat := by
      rw [← zpow_natCast (2 : ℝ) (k + a).toNat, Int.toNat_of_nonneg hka, zpow_add₀ (by norm_num),
        zpow_natCast]
    have h5 : Real.sqrt 5 = 2 * ((M : ℝ) * 2 ^ k) - 1 := by rw [← hMk, hφ]; ring
    have hrat : Real.sqrt 5
        = ((2 * M * 2 ^ (k + a).toNat - 2 ^ a : ℤ) : ℝ) / ((2 ^ a : ℤ) : ℝ) := by
      have hb : ((2 ^ a : ℤ) : ℝ) ≠ 0 := by positivity
      rw [eq_div_iff hb, h5]
      push_cast
      rw [← hpow]
      ring
    exact (irrational_iff_ne_rational _).mp irrational_sqrt5 _ _ (by positivity) hrat
  have hD : (0 : ℝ) < 2 ^ (-(2 * (p : ℤ)) - 4) := by positivity
  have hDsmall : (2 : ℝ) ^ (-(2 * (p : ℤ)) - 4) ≤ 1 / 16 := by
    calc (2 : ℝ) ^ (-(2 * (p : ℤ)) - 4) ≤ 2 ^ (-(4 : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ = 1 / 16 := by norm_num
  -- `φ` is at distance at least `2^(−2p−4)` from every boundary
  have hlogφ : Int.log 2 |φ| = 0 := by
    rw [abs_of_pos (by linarith)]
    apply le_antisymm
    · apply Int.lt_add_one_iff.mp
      apply (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (by linarith)).mp
      push_cast
      simpa using hφhi
    · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (by linarith)).mp
      push_cast
      simpa using hφlo.le
  have hdist : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → b ≠ φ →
      (b = 0 ∨ Int.log 2 |φ| ≤ Int.log 2 |b|) → 2 ^ (-(2 * (p : ℤ)) - 4) ≤ |φ - b| := by
    intro b hb hne hlog
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, sub_zero, abs_of_pos (by linarith)]
      linarith
    have hb1 : 1 ≤ |b| := by
      rcases hlog with h | h
      · exact absurd h hb0
      · rw [hlogφ] at h
        have := Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.mpr hb0)
        have h0 : (2 : ℝ) ^ (0 : ℤ) ≤ 2 ^ Int.log 2 |b| := zpow_le_zpow_right₀ (by norm_num) h
        push_cast at this h0
        linarith [h0, this]
    rcases le_or_gt b (-1) with hneg | hpos
    · rw [abs_of_pos (by linarith)]
      linarith
    have hbpos : 1 ≤ b := by
      rcases le_abs.mp hb1 with h | h
      · exact h
      · linarith
    rcases le_or_gt (5 / 2) b with hfar | hnear
    · rw [abs_of_neg (by linarith)]
      linarith
    -- `1 ≤ b < 5/2`: `b = M · 2^k` with `k ≥ −p`, so `c = 2b − 1` is a multiple of `2^-p`
    obtain ⟨M, k, hMk, hk⟩ := boundary_repr p b hb hb0
    have hlogb : 0 ≤ Int.log 2 |b| := by
      rcases hlog with h | h
      · exact absurd h hb0
      · rwa [hlogφ] at h
    have hkp : 0 ≤ k + p := by omega
    have hpow : (2 : ℝ) ^ k * 2 ^ p = (2 : ℝ) ^ (k + p).toNat := by
      rw [← zpow_natCast (2 : ℝ) (k + p).toNat, Int.toNat_of_nonneg hkp, zpow_add₀ (by norm_num),
        zpow_natCast]
    set c : ℝ := 2 * b - 1 with hc
    set N : ℤ := 2 * M * 2 ^ (k + p).toNat - 2 ^ p with hN
    have hcN : c * 2 ^ p = N := by
      rw [hc, hMk, hN]
      push_cast
      rw [← hpow]
      ring
    have hc1 : 1 ≤ c := by rw [hc]; linarith
    have hc4 : c < 4 := by rw [hc]; linarith
    -- `5 − c²` is a nonzero multiple of `4^-p`
    have hc5 : c ^ 2 ≠ 5 := by
      intro h
      have hceq : c = Real.sqrt 5 := by
        rw [← h, Real.sqrt_sq (by linarith)]
      have hrat : Real.sqrt 5 = (N : ℝ) / ((2 ^ p : ℤ) : ℝ) := by
        rw [← hceq, eq_div_iff (by positivity)]
        push_cast
        exact hcN
      exact (irrational_iff_ne_rational _).mp irrational_sqrt5 _ _ (by positivity) hrat
    have h4 : (4 : ℝ) ^ p = (2 ^ p) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hp2 : (0 : ℝ) < (2 ^ p) ^ 2 := by positivity
    have hint : (5 * 4 ^ p - N ^ 2 : ℤ) ≠ 0 := by
      intro h
      apply hc5
      have h' : (5 : ℝ) * 4 ^ p = (N : ℝ) ^ 2 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) h
        push_cast at this
        linarith
      rw [h4, ← hcN, mul_pow] at h'
      exact (mul_right_cancel₀ hp2.ne' (by linarith : 5 * (2 ^ p) ^ 2 = c ^ 2 * (2 ^ p) ^ 2)).symm
    have hone : (1 : ℝ) ≤ |((5 * 4 ^ p - N ^ 2 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hint
    have hdiff : |5 - c ^ 2| * (2 ^ p) ^ 2 = |((5 * 4 ^ p - N ^ 2 : ℤ) : ℝ)| := by
      have hx : ((5 * 4 ^ p - N ^ 2 : ℤ) : ℝ) = (5 - c ^ 2) * (2 ^ p) ^ 2 := by
        push_cast
        rw [h4, ← hcN]
        ring
      rw [hx, abs_mul, abs_of_pos hp2]
    have hdiff' : (1 : ℝ) / (2 ^ p) ^ 2 ≤ |5 - c ^ 2| := by
      rw [div_le_iff₀ hp2]
      linarith
    -- `|√5 − c| (√5 + c) = |5 − c²|`
    have hfactor : |Real.sqrt 5 - c| * (Real.sqrt 5 + c) = |5 - c ^ 2| := by
      rw [← abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt 5 + c), ← abs_mul]
      congr 1
      nlinarith [hs5]
    have hsum : Real.sqrt 5 + c < 8 := by linarith
    have hsc : |Real.sqrt 5 - c| ≥ 1 / (2 ^ p) ^ 2 / 8 := by
      have := hfactor
      have hpos : (0 : ℝ) < Real.sqrt 5 + c := by linarith
      rw [ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
      calc (1 : ℝ) / (2 ^ p) ^ 2 ≤ |5 - c ^ 2| := hdiff'
        _ = |Real.sqrt 5 - c| * (Real.sqrt 5 + c) := hfactor.symm
        _ ≤ |Real.sqrt 5 - c| * 8 := by
          apply mul_le_mul_of_nonneg_left hsum.le (abs_nonneg _)
    have hφb : |φ - b| = |Real.sqrt 5 - c| / 2 := by
      rw [hφ, hc, ← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_div]
      congr 1
      ring
    have hpow2 : (2 : ℝ) ^ (-(2 * (p : ℤ)) - 4) = 1 / (2 ^ p) ^ 2 / 8 / 2 := by
      rw [show -(2 * (p : ℤ)) - 4 = -((p * 2 + 4 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, pow_add, pow_mul]
      field_simp
      ring
    rw [hφb, hpow2]
    linarith
  -- the bracket is narrower than that distance
  have hwidth : (lov + e₁) / 2 + 1 / 2 - (lov / 2 + 1 / 2) < 2 ^ (-(2 * (p : ℤ)) - 4) := by
    have : (lov + e₁) / 2 + 1 / 2 - (lov / 2 + 1 / 2) = e₁ / 2 := by ring
    rw [this]
    have h2 : (2 : ℝ) ^ (2 - (w : ℤ)) / 2 = 2 ^ (1 - (w : ℤ)) := by
      rw [show (2 : ℤ) - w = (1 - (w : ℤ)) + 1 by ring, zpow_add_one₀ (by norm_num)]
      ring
    have h3 : (2 : ℝ) ^ (1 - (w : ℤ)) < 2 ^ (-(2 * (p : ℤ)) - 4) :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    linarith
  exact no_boundary_of_dist p φ _ _ _ hφ0 hφB (by rw [hφ]; linarith) (by rw [hφ]; linarith)
    hdist hwidth

/-- The golden ratio is the lift of its value. -/
theorem phiPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    phiPrecRound p mode = liftVal₀ (some (((1 + Real.sqrt 5) / 2 : ℝ) : EReal)) p mode := by
  unfold phiPrecRound liftVal₀
  have hstart : 0 < p + zivGuardBits := by unfold zivGuardBits; omega
  apply zivLoop_eq p mode phiApprox ((1 + Real.sqrt 5) / 2) ?_ (2 * p + 6) ?_ _ _ hstart
    (le_mul_two_pow_zivFuel _ _ hstart)
  · intro w hw
    have : NeZero w := ⟨hw.ne'⟩
    obtain ⟨lov, e₁, h1, h2, h3, _, _, hl, hh⟩ := phiApprox_spec w
    refine ⟨_, _, hl, hh, by linarith, by linarith, ?_⟩
    intro h
    have : lov = Real.sqrt 5 := by linarith
    rw [h3 this, add_zero, this]
    ring
  · intro w hw
    exact phiApprox_possible p mode w hw

end Azurite.AzFloat
