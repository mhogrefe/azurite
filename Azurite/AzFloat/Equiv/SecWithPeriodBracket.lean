/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SecWithPeriodBracket
import Azurite.AzFloat.Equiv.CosWithPeriodBracket
import Azurite.AzFloat.Equiv.SecBracket

/-!
# Equivalence: the brackets of `sec (2π x / u)` and of `sec q`

* `Spec.secPole θ`: `1 / cos θ`, and `+∞` at a pole (`cos θ = 0`: the cosine there is the unsigned
  zero, whose reciprocal is `+∞`); `secPole_congr` (it depends on `cos θ` only).
* A generic step `reciprocal_valid_or_none`/`reciprocal_isSome_exists` for the reciprocal of a
  cosine bracket of width `ε w → 0`, and its two instances: `secPeriodApprox_valid_or_none`,
  `secPeriodApprox_isSome_exists` (Niven), `secRatApprox_valid_or_none`,
  `secRatApprox_isSome_exists`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- The secant with poles: `1 / cos θ` where `cos θ ≠ 0`, and `+∞` at a pole. -/
noncomputable def secPole (θ : ℝ) : EReal :=
  if Real.cos θ = 0 then ⊤ else ((1 / Real.cos θ : ℝ) : EReal)

theorem secPole_of_cos_ne_zero {θ : ℝ} (h : Real.cos θ ≠ 0) :
    secPole θ = ((1 / Real.cos θ : ℝ) : EReal) := by
  unfold secPole
  rw [ite_eq_right h]

theorem secPole_of_cos_eq_zero {θ : ℝ} (h : Real.cos θ = 0) : secPole θ = ⊤ := by
  unfold secPole
  rw [ite_eq_left h]

theorem secPole_congr {a b : ℝ} (h : Real.cos a = Real.cos b) : secPole a = secPole b := by
  unfold secPole
  rw [h]

/-- The reduction of `secPole (2π x / U)` to the fractional part `ρ` of `|x| / U`. -/
theorem secPole_two_pi_div {xv U ρ : ℝ} (hU : 0 < U) {k : ℕ} (hk : |xv| / U = k + ρ) :
    secPole (2 * Real.pi * xv / U) = secPole (2 * Real.pi * ρ) := by
  refine secPole_congr ?_
  have hpi := Real.pi_pos
  rw [← Real.cos_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    abs_of_pos hU, mul_div_assoc, hk,
    show 2 * Real.pi * ((k : ℝ) + ρ) = 2 * Real.pi * ρ + k * (2 * Real.pi) by ring]
  exact Real.cos_add_nat_mul_two_pi _ k

end Spec

/-! ### The reciprocal of a cosine bracket -/

/-- The width of the reciprocal of a cosine bracket of width `ε` once `ε ≤ c / 2`,
`c = |cos|`. -/
noncomputable def recipEps (ε : ℕ → ℝ) (c : ℝ) (w : ℕ) : ℝ :=
  (0 + 2 * ε w / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

theorem tendsto_recipEps {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) (c : ℝ) :
    Filter.Tendsto (recipEps ε c) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := ((hε.const_mul (2 / (c / 2))).add (h2.const_mul 8)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, recipEps]
  ring

/-- The reciprocal of a cosine bracket encloses `1 / c` or is rejected. -/
theorem reciprocal_valid_or_none {C : Encl} {c δ : ℝ} (hC : IsEnclW C c δ) {w : ℕ} (hw : 64 ≤ w)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ,
        Rounds (negSwapApprox false (tanOfSinCos (Encl.exact one, C) (w + 12))).1 lv ∧
        Rounds (negSwapApprox false (tanOfSinCos (Encl.exact one, C) (w + 12))).2 hv ∧
        lv ≤ 1 / c ∧ 1 / c ≤ hv) ∨
      roundingPossible (negSwapApprox false (tanOfSinCos (Encl.exact one, C) (w + 12))).1
        (negSwapApprox false (tanOfSinCos (Encl.exact one, C) (w + 12))).2 p mode = none := by
  have hS : IsEnclW (Encl.exact one, C).1 1 0 := (isEncl0W_exact toVal_one' zero_le_one).toW
  have h := tanOfSinCos_valid_or_none false hS (b := (Encl.exact one, C)) hC (by norm_num)
    zero_le_one (V := w + 12) (by omega) p mode
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  exact h

/-- The Ziv certificate for the reciprocal of a cosine bracket family `C w` of width `ε w → 0`
around `c ≠ 0` with an irrational reciprocal. -/
theorem reciprocal_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {C : ℕ → Encl} {c : ℝ}
    {ε : ℕ → ℝ} (hε : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hC : ∀ w, 64 ≤ w → IsEnclW (C w) c (ε w)) (hc : c ≠ 0) (hirr : Irrational (1 / c))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (negSwapApprox false (tanOfSinCos (Encl.exact one, C (w₀ * 2 ^ f)) (w₀ * 2 ^ f + 12))).1
      (negSwapApprox false (tanOfSinCos (Encl.exact one, C (w₀ * 2 ^ f)) (w₀ * 2 ^ f + 12))).2 p
      mode).isSome = true := by
  have hc0 : 0 < |c| := abs_pos.mpr hc
  obtain ⟨W₁, hW₁⟩ := (hε.eventually (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  refine exists_isSome_of_irrational_threshold p mode
    (fun w => negSwapApprox false (tanOfSinCos (Encl.exact one, C w) (w + 12))) hirr
    (recipEps ε |c|) (tendsto_recipEps hε _) (max 64 W₁) (fun w hw => ?_) w₀ hw₀
  have hS : IsEnclW (Encl.exact one, C w).1 1 0 := (isEncl0W_exact toVal_one' zero_le_one).toW
  have hwid := tanOfSinCos_width hS (b := (Encl.exact one, C w)) (hC w (le_of_max_le_left hw))
    (by norm_num) zero_le_one (V := w + 12) (by omega) hc0 (hW₁ w (le_of_max_le_right hw)).le
  have h := negSwapApprox_of_isEnclW false hwid
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  exact h

/-! ### The two instances -/

theorem isEnclW_cosPeriodBracket (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (cosPeriodBracket r w) (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)))
      (cosPeriodEps w) :=
  cosPeriodBracket_spec r hr0 hr1 hw

/-- At every level `w ≥ 64` the bracket of `secPeriodApprox` encloses `sec (2πr)` or is rejected
by `roundingPossible`. -/
theorem secPeriodApprox_valid_or_none (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (secPeriodApprox r w).1 lv ∧ Rounds (secPeriodApprox r w).2 hv ∧
        lv ≤ 1 / Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ∧
        1 / Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)) ≤ hv) ∨
      roundingPossible (secPeriodApprox r w).1 (secPeriodApprox r w).2 p mode = none :=
  reciprocal_valid_or_none (isEnclW_cosPeriodBracket r hr0 hr1 hw) hw p mode

/-- `sec (2πr)` is irrational for an `AzRat` whose denominator is not `1, 2, 3, 4, 6`. -/
theorem irrational_sec_two_pi_mul_toRat (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h3 : r.den ≠ AzNat.ofNat 3) (h4 : r.den ≠ AzNat.ofNat 4)
    (h6 : r.den ≠ AzNat.ofNat 6) :
    Irrational (1 / Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))) := by
  rw [one_div]
  exact (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6).inv

/-- The Ziv certificate for `sec (2πr)`, `r ∈ [0, 1)` with an irrational cosine. -/
theorem secPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (r : AzRat)
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h3 : r.den ≠ AzNat.ofNat 3)
    (h4 : r.den ≠ AzNat.ofNat 4) (h6 : r.den ≠ AzNat.ofNat 6) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (secPeriodApprox r (w₀ * 2 ^ f)).1
      (secPeriodApprox r (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  reciprocal_isSome_exists p mode tendsto_cosPeriodEps
    (fun _ hw => isEnclW_cosPeriodBracket r hr0 hr1 hw)
    (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6).ne_zero
    (irrational_sec_two_pi_mul_toRat r h1 h2 h3 h4 h6) w₀ hw₀

/-- At every level `w ≥ 64` the bracket of `secRatApprox` encloses `sec q` or is rejected by
`roundingPossible`. -/
theorem secRatApprox_valid_or_none (q : AzRat) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (secRatApprox q w).1 lv ∧ Rounds (secRatApprox q w).2 hv ∧
        lv ≤ 1 / Real.cos (AzRat.toRat q : ℝ) ∧ 1 / Real.cos (AzRat.toRat q : ℝ) ≤ hv) ∨
      roundingPossible (secRatApprox q w).1 (secRatApprox q w).2 p mode = none :=
  reciprocal_valid_or_none (cosRatBracket_spec q hw) hw p mode

/-- `sec q` is irrational for a nonzero `AzRat`. -/
theorem irrational_sec_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (1 / Real.cos (AzRat.toRat q : ℝ)) := by
  rw [one_div]
  exact (irrational_cos_toRat q h0).inv

/-- The Ziv certificate for `sec q`, `q` a nonzero rational. -/
theorem secRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (secRatApprox q (w₀ * 2 ^ f)).1 (secRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  reciprocal_isSome_exists p mode (tendsto_cosRatEps q) (fun _ hw => cosRatBracket_spec q hw)
    (irrational_cos_toRat q h0).ne_zero (irrational_sec_toRat q h0) w₀ hw₀

end Azurite.AzFloat
