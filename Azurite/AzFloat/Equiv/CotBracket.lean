/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CotBracket
import Azurite.AzFloat.Equiv.CscBracket
import Azurite.AzFloat.Equiv.TanRatBracket
import Azurite.AzFloat.Equiv.TanWithPeriodBracket

/-!
# Equivalence: the brackets of `cot x`

* `Spec.cotSigned a θ`: `cos θ / sin θ`, and at a pole (`sin θ = 0`) the infinity whose sign is
  the sign of the argument `a` times the sign of `cos θ` (the quotient of `cos θ = ±1` by a zero
  carrying the sign of `a`; `+∞` at `a = 0`); `Spec.cotCore neg θ`: the same after the reduction;
  `cotSigned_two_pi_div`, `cotSigned_self`.
* `quotient_isSome_exists`: the Ziv certificate for the signed quotient of a family of pairs of
  brackets; the instances for `cotApprox`, `cotRatApprox`, `cotPeriodApprox`.
* `cot_bounds_of_small`, `cotTinyCore?_eq`, `cotTiny?_eq`, `cotTinyRat?_eq`, `cotPeriodTiny?_eq`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- The cotangent with poles: `cos θ / sin θ` where `sin θ ≠ 0`; at a pole, `+∞` when the
argument `a` and `cos θ` have the same sign (`a ≥ 0` counting as positive), `−∞` otherwise. -/
noncomputable def cotSigned (a θ : ℝ) : EReal :=
  if Real.sin θ = 0 then
    (if Real.cos θ < 0 then (if a < 0 then ⊤ else ⊥) else (if a < 0 then ⊥ else ⊤))
  else ((Real.cos θ / Real.sin θ : ℝ) : EReal)

open Classical in
/-- The cotangent after the reduction: `± cos θ / sin θ` (`neg`: the sign is negative), and at
a pole the infinity with the sign `± sign (cos θ)`. -/
noncomputable def cotCore (neg : Bool) (θ : ℝ) : EReal :=
  if Real.sin θ = 0 then
    (if Real.cos θ < 0 then (if neg then ⊤ else ⊥) else (if neg then ⊥ else ⊤))
  else (((if neg then -1 else 1) * (Real.cos θ / Real.sin θ) : ℝ) : EReal)

theorem cotCore_of_irrational {neg : Bool} {θ : ℝ} (h : Irrational (Real.cos θ / Real.sin θ)) :
    cotCore neg θ = (((if neg then -1 else 1) * (Real.cos θ / Real.sin θ) : ℝ) : EReal) := by
  unfold cotCore
  refine ite_eq_right fun hc => ?_
  rw [hc, div_zero] at h
  exact h ⟨0, by simp⟩

/-- `cotSigned a θ = cotCore neg θ'` when `neg` is the sign of `a`, `sin θ = ± sin θ'` with
that sign, and `cos θ = cos θ'`. -/
theorem cotSigned_eq_cotCore {a θ θ' : ℝ} {neg : Bool} (hneg : neg = true ↔ a < 0)
    (hs : Real.sin θ = (if neg then -1 else 1) * Real.sin θ')
    (hc : Real.cos θ = Real.cos θ') : cotSigned a θ = cotCore neg θ' := by
  unfold cotSigned cotCore
  rw [hc]
  cases neg with
  | false =>
    have ha : ¬ a < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hs ⊢
    rw [hs]
    simp only [ha, ↓reduceIte]
  | true =>
    have ha : a < 0 := hneg.mp rfl
    simp only [↓reduceIte, neg_one_mul] at hs ⊢
    rw [hs]
    simp only [ha, ↓reduceIte]
    by_cases h0 : Real.sin θ' = 0
    · rw [ite_eq_left h0, ite_eq_left (by rw [h0, neg_zero])]
    · rw [ite_eq_right h0, ite_eq_right (neg_ne_zero.mpr h0)]
      congr 1
      rw [div_neg]

/-- The reduction of `cotSigned x (2π x / U)` to the fractional part `ρ` of `|x| / U`. -/
theorem cotSigned_two_pi_div {xv U ρ : ℝ} {neg : Bool} (hneg : neg = true ↔ xv < 0)
    (hU : 0 < U) {k : ℕ} (hk : |xv| / U = k + ρ) :
    cotSigned xv (2 * Real.pi * xv / U) = cotCore neg (2 * Real.pi * ρ) := by
  have hpi := Real.pi_pos
  have habs : Real.sin (2 * Real.pi * (|xv| / U)) = Real.sin (2 * Real.pi * ρ) := by
    rw [hk, show 2 * Real.pi * ((k : ℝ) + ρ) = 2 * Real.pi * ρ + k * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi]
  have hcos : Real.cos (2 * Real.pi * xv / U) = Real.cos (2 * Real.pi * ρ) := by
    rw [← Real.cos_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hU, mul_div_assoc, hk,
      show 2 * Real.pi * ((k : ℝ) + ρ) = 2 * Real.pi * ρ + k * (2 * Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi _ k
  refine cotSigned_eq_cotCore hneg ?_ hcos
  cases neg with
  | false =>
    have ha : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [← habs, abs_of_nonneg (not_lt.mp ha)]
    congr 1
    ring
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    rw [← habs, abs_of_neg (hneg.mp rfl), ← Real.sin_neg]
    congr 1
    ring

/-- `cotSigned x x` in terms of `|x|`. -/
theorem cotSigned_self {xv : ℝ} {neg : Bool} (hneg : neg = true ↔ xv < 0) :
    cotSigned xv xv = cotCore neg |xv| := by
  refine cotSigned_eq_cotCore hneg ?_ (Real.cos_abs xv).symm
  cases neg with
  | false =>
    have ha : ¬ xv < 0 := fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg (not_lt.mp ha)]
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    rw [abs_of_neg (hneg.mp rfl), Real.sin_neg, neg_neg]

end Spec

/-! ### The signed quotient of a family of pairs of brackets -/

/-- The width of the quotient of brackets of widths `ε₁`, `ε₂` once `ε₂ ≤ c / 2`,
`c = |denominator|`. -/
noncomputable def quotEps (ε₁ ε₂ : ℕ → ℝ) (c : ℝ) (w : ℕ) : ℝ :=
  (ε₁ w + 2 * ε₂ w / (c / 2) + 8 * (1 / 2 : ℝ) ^ (w + 12)) / (c / 2)

theorem tendsto_quotEps {ε₁ ε₂ : ℕ → ℝ} (h₁ : Filter.Tendsto ε₁ Filter.atTop (nhds 0))
    (h₂ : Filter.Tendsto ε₂ Filter.atTop (nhds 0)) (c : ℝ) :
    Filter.Tendsto (quotEps ε₁ ε₂ c) Filter.atTop (nhds 0) := by
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp (Filter.tendsto_add_atTop_nat 12)
  have h := ((h₁.add (h₂.const_mul (2 / (c / 2)))).add (h2.const_mul 8)).div_const (c / 2)
  simp only [mul_zero, add_zero, zero_div] at h
  refine h.congr fun w => ?_
  simp only [Function.comp, quotEps]
  ring

/-- **The Ziv certificate for the signed quotient** of a family of pairs of brackets
`B w = ([s], [c])` with widths `ε₁ w, ε₂ w → 0`, `|s| ≤ 1`, `c ≠ 0`, `s / c` irrational. -/
theorem quotient_isSome_exists (neg : Bool) (p : ℕ) [NeZero p] (mode : RoundingMode)
    {B : ℕ → Encl × Encl} {s c : ℝ} {ε₁ ε₂ : ℕ → ℝ}
    (h₁ : Filter.Tendsto ε₁ Filter.atTop (nhds 0))
    (h₂ : Filter.Tendsto ε₂ Filter.atTop (nhds 0))
    (hS : ∀ w, 64 ≤ w → IsEnclW (B w).1 s (ε₁ w)) (hC : ∀ w, 64 ≤ w → IsEnclW (B w).2 c (ε₂ w))
    (hε : ∀ w, 64 ≤ w → ε₁ w ≤ 1) (hs : |s| ≤ 1) (hc : c ≠ 0) (hirr : Irrational (s / c))
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible
      (negSwapApprox neg (tanOfSinCos (B (w₀ * 2 ^ f)) (w₀ * 2 ^ f + 12))).1
      (negSwapApprox neg (tanOfSinCos (B (w₀ * 2 ^ f)) (w₀ * 2 ^ f + 12))).2 p
      mode).isSome = true := by
  have hc0 : 0 < |c| := abs_pos.mpr hc
  obtain ⟨W₁, hW₁⟩ := (h₂.eventually (gt_mem_nhds (half_pos hc0))).exists_forall_of_atTop
  refine exists_isSome_of_irrational_threshold p mode
    (fun w => negSwapApprox neg (tanOfSinCos (B w) (w + 12)))
    (irrational_sign_mul hirr neg) (quotEps ε₁ ε₂ |c|) (tendsto_quotEps h₁ h₂ _) (max 64 W₁)
    (fun w hw => ?_) w₀ hw₀
  have hw64 := le_of_max_le_left hw
  exact negSwapApprox_of_isEnclW neg (tanOfSinCos_width (hS w hw64) (hC w hw64) hs
    (hε w hw64) (V := w + 12) (by omega) hc0 (hW₁ w (le_of_max_le_right hw)).le)

/-! ### The three instances -/

theorem cot_eq_inv_tan (θ : ℝ) : Real.cos θ / Real.sin θ = (Real.tan θ)⁻¹ := by
  rw [Real.tan_eq_sin_div_cos, inv_div]

theorem irrational_tan_abs_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.tan |xv|) := by
  rcases abs_choice xv with h | h
  · rw [h]; exact irrational_tan_of_toVal hx hx0
  · rw [h, Real.tan_neg]; exact (irrational_tan_of_toVal hx hx0).neg

theorem irrational_cot_abs_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (Real.cos |xv| / Real.sin |xv|) := by
  rw [cot_eq_inv_tan]
  exact (irrational_tan_abs_of_toVal hx hx0).inv

theorem isEnclW_swap_sinCosBracket {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosBracket x ex w).swap.1 (Real.cos |xv|) (sinCosEps ex w) ∧
      IsEnclW (sinCosBracket x ex w).swap.2 (Real.sin |xv|) (sinCosEps ex w) := by
  obtain ⟨hS, hC⟩ := sinCosBracket_spec hx hex hw
  rw [Real.cos_abs]
  exact ⟨hC, hS⟩

/-- At every level `w ≥ 64` the bracket of `cotApprox neg` encloses `± cot |x|` or is
rejected. -/
theorem cotApprox_valid_or_none (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (cotApprox neg x ex w).1 lv ∧ Rounds (cotApprox neg x ex w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * (Real.cos |xv| / Real.sin |xv|) ∧
        (if neg then -1 else 1) * (Real.cos |xv| / Real.sin |xv|) ≤ hv) ∨
      roundingPossible (cotApprox neg x ex w).1 (cotApprox neg x ex w).2 p mode = none := by
  obtain ⟨hS, hC⟩ := isEnclW_swap_sinCosBracket hx hex hw
  exact tanOfSinCos_valid_or_none neg hS hC (Real.abs_cos_le_one _) (sinCosEps_le_one ex hw)
    (by omega) p mode

/-- The Ziv certificate for `cot x`, `x` a nonzero finite float. -/
theorem cotApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cotApprox neg x ex (w₀ * 2 ^ f)).1
      (cotApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  quotient_isSome_exists neg p mode (B := fun w => (sinCosBracket x ex w).swap)
    (tendsto_sinCosEps ex) (tendsto_sinCosEps ex)
    (fun _ hw => (isEnclW_swap_sinCosBracket hx hex hw).1)
    (fun _ hw => (isEnclW_swap_sinCosBracket hx hex hw).2)
    (fun _ hw => sinCosEps_le_one ex hw) (Real.abs_cos_le_one _)
    (irrational_sin_abs_of_toVal hx hx0).ne_zero (irrational_cot_abs_of_toVal hx hx0) w₀ hw₀

/-- `cosRatEps q w ≤ 1` from `w = 64` on. -/
theorem cosRatEps_le_one (q : AzRat) {w : ℕ} (hw : 64 ≤ w) : cosRatEps q w ≤ 1 := by
  have h2 := two_zpow_mul_half_pow_cosWork (ratExpBound q) w
  have hW : 64 ≤ cosWork (ratExpBound q) w := by unfold cosWork; omega
  have h3 := half_pow_small hW
  have hV : 64 ≤ w + 12 := by omega
  have h4 := half_pow_small hV
  have h := add_nine_mul_half_pow_le hV
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 12) := by positivity
  have : (73 : ℝ) * (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 16 := by norm_num
  have h5 : cosEps (ratExpBound q) w ≤ 1 / 2 := by
    unfold cosEps sinCosEps sinCosEpsW
    linarith
  unfold cosRatEps
  linarith

theorem irrational_cot_abs_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.cos |(AzRat.toRat q : ℝ)| / Real.sin |(AzRat.toRat q : ℝ)|) := by
  rw [cot_eq_inv_tan]
  rcases abs_choice (AzRat.toRat q : ℝ) with h | h
  · rw [h]; exact (irrational_tan_toRat q h0).inv
  · rw [h, Real.tan_neg]; exact (irrational_tan_toRat q h0).neg.inv

theorem isEnclW_swap_sinCosRatBracket (q : AzRat) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosRatBracket q w).swap.1 (Real.cos |(AzRat.toRat q : ℝ)|) (cosRatEps q w) ∧
      IsEnclW (sinCosRatBracket q w).swap.2 (Real.sin |(AzRat.toRat q : ℝ)|)
        (sinRatEps q w) := by
  obtain ⟨hS, hC⟩ := isEnclW_sinCosRatBracket q hw
  rw [Real.cos_abs]
  exact ⟨hC, hS⟩

/-- At every level `w ≥ 64` the bracket of `cotRatApprox` encloses `± cot |q|` or is rejected. -/
theorem cotRatApprox_valid_or_none (q : AzRat) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (cotRatApprox q w).1 lv ∧ Rounds (cotRatApprox q w).2 hv ∧
        lv ≤ (if (!q.sign) = true then -1 else 1)
          * (Real.cos |(AzRat.toRat q : ℝ)| / Real.sin |(AzRat.toRat q : ℝ)|) ∧
        (if (!q.sign) = true then -1 else 1)
          * (Real.cos |(AzRat.toRat q : ℝ)| / Real.sin |(AzRat.toRat q : ℝ)|) ≤ hv) ∨
      roundingPossible (cotRatApprox q w).1 (cotRatApprox q w).2 p mode = none := by
  obtain ⟨hS, hC⟩ := isEnclW_swap_sinCosRatBracket q hw
  exact tanOfSinCos_valid_or_none (!q.sign) hS hC (Real.abs_cos_le_one _)
    (cosRatEps_le_one q hw) (by omega) p mode

/-- The Ziv certificate for `cot q`, `q` a nonzero rational. -/
theorem cotRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cotRatApprox q (w₀ * 2 ^ f)).1 (cotRatApprox q (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  quotient_isSome_exists (!q.sign) p mode (B := fun w => (sinCosRatBracket q w).swap)
    (tendsto_cosRatEps q) (tendsto_sinRatEps q)
    (fun _ hw => (isEnclW_swap_sinCosRatBracket q hw).1)
    (fun _ hw => (isEnclW_swap_sinCosRatBracket q hw).2)
    (fun _ hw => cosRatEps_le_one q hw) (Real.abs_cos_le_one _)
    (irrational_sin_abs_toRat q h0).ne_zero (irrational_cot_abs_toRat q h0) w₀ hw₀

/-- `cosPeriodEps w ≤ 1` from `w = 64` on. -/
theorem cosPeriodEps_le_one {w : ℕ} (hw : 64 ≤ w) : cosPeriodEps w ≤ 1 := by
  have hW : 64 ≤ cosWork (AzInt.ofInt 3) w := by unfold cosWork; omega
  have h3 := half_pow_small hW
  have hV : 64 ≤ w + 12 := by omega
  have h := add_nine_mul_half_pow_le hV
  have h4 := half_pow_small hV
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 12) := by positivity
  have : (73 : ℝ) * (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 16 := by norm_num
  unfold cosPeriodEps cosEps sinCosEps sinCosEpsW
  linarith

/-- `cot (2πr)` is irrational for an `AzRat` whose denominator is not `1, 2, 4, 8`. -/
theorem irrational_cot_two_pi_mul_toRat (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4) (h8 : r.den ≠ AzNat.ofNat 8) :
    Irrational (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))
      / Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) := by
  rw [cot_eq_inv_tan]
  exact (irrational_tan_two_pi_mul_toRat r h1 h2 h4 h8).inv

theorem isEnclW_swap_sinCosPeriodBracket (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosPeriodBracket r w).swap.1 (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ)))
        (cosPeriodEps w) ∧
      IsEnclW (sinCosPeriodBracket r w).swap.2 (Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)))
        (sinPeriodEps w) := by
  obtain ⟨hS, hC⟩ := isEnclW_sinCosPeriodBracket r hr0 hr1 hw
  exact ⟨hC, hS⟩

/-- At every level `w ≥ 64` the bracket of `cotPeriodApprox neg` encloses `± cot (2πr)` or is
rejected. -/
theorem cotPeriodApprox_valid_or_none (neg : Bool) (r : AzRat)
    (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (cotPeriodApprox neg r w).1 lv ∧ Rounds (cotPeriodApprox neg r w).2 hv ∧
        lv ≤ (if neg then -1 else 1) * (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))
          / Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) ∧
        (if neg then -1 else 1) * (Real.cos (2 * Real.pi * (AzRat.toRat r : ℝ))
          / Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ))) ≤ hv) ∨
      roundingPossible (cotPeriodApprox neg r w).1 (cotPeriodApprox neg r w).2 p mode = none := by
  obtain ⟨hS, hC⟩ := isEnclW_swap_sinCosPeriodBracket r hr0 hr1 hw
  exact tanOfSinCos_valid_or_none neg hS hC (Real.abs_cos_le_one _) (cosPeriodEps_le_one hw)
    (by omega) p mode

/-- `sin (2πr) ≠ 0` unless the denominator of `r` is `1` or `2`. -/
theorem sin_two_pi_mul_toRat_ne_zero (r : AzRat) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4) (h8 : r.den ≠ AzNat.ofNat 8) :
    Real.sin (2 * Real.pi * (AzRat.toRat r : ℝ)) ≠ 0 := fun h => by
  have hirr := irrational_cot_two_pi_mul_toRat r h1 h2 h4 h8
  rw [h, div_zero] at hirr
  exact hirr ⟨0, by simp⟩

/-- The Ziv certificate for `± cot (2πr)`, `r ∈ [0, 1)` with an irrational cotangent. -/
theorem cotPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h4 : r.den ≠ AzNat.ofNat 4)
    (h8 : r.den ≠ AzNat.ofNat 8) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cotPeriodApprox neg r (w₀ * 2 ^ f)).1
      (cotPeriodApprox neg r (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  quotient_isSome_exists neg p mode (B := fun w => (sinCosPeriodBracket r w).swap)
    tendsto_cosPeriodEps tendsto_sinPeriodEps
    (fun _ hw => (isEnclW_swap_sinCosPeriodBracket r hr0 hr1 hw).1)
    (fun _ hw => (isEnclW_swap_sinCosPeriodBracket r hr0 hr1 hw).2)
    (fun _ hw => cosPeriodEps_le_one hw) (Real.abs_cos_le_one _)
    (sin_two_pi_mul_toRat_ne_zero r h1 h2 h4 h8) (irrational_cot_two_pi_mul_toRat r h1 h2 h4 h8)
    w₀ hw₀

/-! ### Tiny arguments -/

/-- `1/a − a ≤ cot a < 1/a` for `0 < a ≤ 1`. -/
theorem cot_bounds_of_small {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    1 / a - a ≤ Real.cos a / Real.sin a ∧ Real.cos a / Real.sin a < 1 / a := by
  have hpi := Real.pi_gt_three
  have hs0 : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith)
  have hs1 := Real.sin_lt ha0
  have hcos := Real.one_sub_sq_div_two_le_cos (x := a)
  have hc0 : 0 < Real.cos a := by nlinarith
  have htan := (tan_bounds_of_small ha0 ha1).1
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hc0] at htan
  constructor
  · rw [le_div_iff₀ hs0]
    have hnn : 0 ≤ 1 / a - a := by
      rw [sub_nonneg, le_div_iff₀ ha0]
      nlinarith
    calc (1 / a - a) * Real.sin a ≤ (1 / a - a) * a := mul_le_mul_of_nonneg_left hs1.le hnn
      _ = 1 - a ^ 2 := by field_simp
      _ ≤ Real.cos a := by nlinarith
  · rw [div_lt_div_iff₀ hs0 ha0]
    linarith

theorem cotTinyCore?_cond {neg : Bool} {alo ahi : AzFloat} {e : AzInt} {p : ℕ}
    {mode : RoundingMode} {r : AzFloat × Ordering}
    (h : cotTinyCore? neg alo ahi e p mode = some r) :
    e.sign = false ∧ p + zivGuardBits + 8 ≤ 2 * e.abs.toNat := by
  unfold cotTinyCore? at h
  by_contra hc
  rw [ite_eq_right hc] at h
  cases h

/-- **The tiny-argument test answers with the rounding of `± cot a`.** -/
theorem cotTinyCore?_eq {neg : Bool} {alo ahi : AzFloat} {e : AzInt} {p : ℕ} [NeZero p]
    {mode : RoundingMode} {r : AzFloat × Ordering} {a l h : ℝ}
    (hl : alo.toVal = some (l : EReal)) (hh : ahi.toVal = some (h : EReal)) (hl0 : 0 < l)
    (hla : l ≤ a) (hah : a ≤ h) (hlt : a < (2 : ℝ) ^ e.toInt)
    (hirr : Irrational (Real.cos a / Real.sin a))
    (hT : cotTinyCore? neg alo ahi e p mode = some r) :
    r = roundVal p mode
      (some (((if neg then -1 else 1) * (Real.cos a / Real.sin a) : ℝ) : EReal)) := by
  have hc := cotTinyCore?_cond hT
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hc.1] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  have ht1 : (2 : ℝ) ^ e.toInt ≤ 1 := by
    rw [htoInt, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have ha0 : 0 < a := lt_of_lt_of_le hl0 hla
  have hh0 : 0 < h := lt_of_lt_of_le ha0 hah
  obtain ⟨hb1, hb2⟩ := cot_bounds_of_small ha0 (hlt.le.trans ht1)
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  unfold cotTinyCore? at hT
  rw [ite_eq_left hc] at hT
  obtain ⟨c, hcv, hc1, -⟩ := divCeiling_abs toVal_one' hl hl0.ne' (p + zivGuardBits + 8)
  obtain ⟨f, hf, hf1, -⟩ := divFloor_abs toVal_one' hh hh0.ne' (p + zivGuardBits + 8)
  obtain ⟨d, hd, hd1, -⟩ := subFloor_abs hf hh (p + zivGuardBits + 8)
  have hnc : (-(divPrecRound one alo (p + zivGuardBits + 8) .Ceiling).1).toVal
      = some ((-c : ℝ) : EReal) := by
    rw [toVal_neg, hcv, Option.map_some, EReal.coe_neg]
  have hnd : (-(subPrecRound (divPrecRound one ahi (p + zivGuardBits + 8) .Floor).1 ahi
      (p + zivGuardBits + 8) .Floor).1).toVal = some ((-d : ℝ) : EReal) := by
    rw [toVal_neg, hd, Option.map_some, EReal.coe_neg]
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hnc)
  rw [fval_of_toVal_coe hnc] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hnd)
  rw [fval_of_toVal_coe hnd] at hR2
  have h1 : 1 / a ≤ 1 / l := one_div_le_one_div_of_le hl0 hla
  have h2 : 1 / h ≤ 1 / a := one_div_le_one_div_of_le ha0 hah
  have hlow : -c ≤ -(Real.cos a / Real.sin a) := by linarith
  have hup : -(Real.cos a / Real.sin a) ≤ -d := by linarith
  have hvB := not_mem_floatSet_of_irrational p hirr.neg
  cases neg with
  | true =>
    simp only [↓reduceIte, neg_one_mul] at hT ⊢
    exact roundingPossible_eq' p mode hR1 hR2 hlow hup (Or.inr hvB) hT
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hT ⊢
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp hT
    have hr := roundingPossible_eq' p (-mode) hR1 hR2 hlow hup (Or.inr hvB) hr'
    rw [hr]
    have hneg := roundVal_neg p mode (-(Real.cos a / Real.sin a))
    rw [neg_neg] at hneg
    exact hneg.symm

/-- The tiny-argument path of `cot (2π x / u)` answers with the rounding of `± cot y`. -/
theorem cotPeriodTiny?_eq {neg : Bool} {m u : AzNat} (hm : 0 < m.toNat) (hu : 0 < u.toNat)
    {E e' : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering}
    (hy : 2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat) < (2 : ℝ) ^ e'.toInt)
    (hirr : Irrational
      (Real.cos (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))
        / Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))))
    (hT : cotPeriodTiny? neg m u E e' p mode = some r) :
    r = roundVal p mode (some (((if neg then -1 else 1)
      * (Real.cos (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))
        / Real.sin (2 * Real.pi * ((m.toNat : ℝ) * (2 : ℝ) ^ E.toInt / u.toNat))) : ℝ)
        : EReal)) := by
  obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2⟩ := periodTinyArg_spec hm hu E
    (W := p + zivGuardBits + 8) (by unfold zivGuardBits; omega)
  exact cotTinyCore?_eq hlo hhi hlo0 h1 h2 hy hirr hT

/-- The tiny-argument path of `cot x` answers with the rounding of `± cot |x|`. -/
theorem cotTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : cotTiny? s (finite s e q m hv) e p mode = some r) :
    r = roundVal p mode (some (((if (!s) = true then -1 else 1)
      * (Real.cos |finiteVal s e m| / Real.sin |finiteVal s e m|) : ℝ) : EReal)) := by
  have hx : (finite s e q m hv).toVal = some ((finiteVal s e m : ℝ) : EReal) :=
    toVal_finite s e q m hv
  have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
  have habs : (finite s e q m hv).abs.toVal = some ((|finiteVal s e m| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  exact cotTinyCore?_eq habs habs (abs_pos.mpr hx0) le_rfl le_rfl
    (abs_finiteVal_bounds s e hv).2 (irrational_cot_abs_of_toVal hx hx0) h

/-- The tiny-argument path of `cot q` answers with the rounding of `± cot |q|`. -/
theorem cotTinyRat?_eq (q : AzRat) (h0 : q.num ≠ 0) {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} (hT : cotTinyRat? q p mode = some r) :
    r = roundVal p mode (some (((if (!q.sign) = true then -1 else 1)
      * (Real.cos |(AzRat.toRat q : ℝ)| / Real.sin |(AzRat.toRat q : ℝ)|) : ℝ) : EReal)) := by
  unfold cotTinyRat? at hT
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  have ha0 := abs_pos.mpr hq0
  have hus : (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ 1 / 10 ^ 18 :=
    half_pow_small (by unfold zivGuardBits; omega)
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q.abs (p + zivGuardBits + 8)
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q.abs (p + zivGuardBits + 8)
  rw [habs] at hl1 hl2 hc1
  rw [abs_abs] at hl2
  have hl0 : 0 < l := by nlinarith
  have hlt : |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ (ratExpBound q).toInt :=
    lt_of_lt_of_le (abs_toRat_lt_two_zpow q) (zpow_le_zpow_right₀ (by norm_num) (by omega))
  exact cotTinyCore?_eq hl hc hl0 hl1 hc1 hlt (irrational_cot_abs_toRat q h0) hT

end Azurite.AzFloat
