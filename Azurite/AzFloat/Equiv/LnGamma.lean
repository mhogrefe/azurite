/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Equiv.LnGammaBracket
import Azurite.AzFloat.Equiv.Ziv
import Azurite.AzFloat.Equiv.Pow
import Azurite.AzFloat.Equiv.Gamma
import Azurite.AzFloat.Equiv.LnEncl

/-!
# Equivalence: `ln Γ`

`Spec.lnGamma` on the extended reals (`+∞` at `0` and `+∞`, `NaN` below `0`, `ln Γ(x)` for
`x > 0`); `lnGammaApprox_spec` (the bracket, strict at the lower end); and
`lnGammaPrecRound_eq_or`: `lnGammaPrecRound x p mode` is the correctly rounded value
(`liftVal Spec.lnGamma`) unless the fuel runs out (`(nan, .eq)`).
-/

namespace Azurite.AzFloat

namespace Spec

/-- `ln Γ` on the extended reals: `+∞` at `0` (from the right) and at `+∞`, `NaN` below `0`. -/
noncomputable def lnGamma (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a < 0 then none else if a = 0 then some ⊤
  else some ((Real.log (Real.Gamma a.toReal) : ℝ) : EReal)

theorem lnGamma_top : lnGamma ⊤ = some ⊤ := by simp [lnGamma]

theorem lnGamma_bot : lnGamma ⊥ = none := by
  unfold lnGamma
  rw [ite_eq_right bot_ne_top, ite_eq_left (by exact EReal.bot_lt_zero)]

theorem lnGamma_zero : lnGamma 0 = some ⊤ := by
  unfold lnGamma
  rw [ite_eq_right EReal.zero_ne_top, ite_eq_right (lt_irrefl _), ite_eq_left rfl]

theorem lnGamma_coe_of_neg {xv : ℝ} (h : xv < 0) : lnGamma (xv : EReal) = none := by
  unfold lnGamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_left (by exact_mod_cast h)]

theorem lnGamma_coe_of_pos {xv : ℝ} (h : 0 < xv) :
    lnGamma (xv : EReal) = some ((Real.log (Real.Gamma xv) : ℝ) : EReal) := by
  unfold lnGamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (not_lt.mpr (by exact_mod_cast h.le)),
    ite_eq_right (by exact_mod_cast h.ne'), EReal.toReal_coe]

end Spec

/-- A bracket as `Roundable`s encloses its value, strictly from below. -/
theorem lnGammaApproxOf_spec {b : Encl} {v : ℝ} (hb : IsEncl b v) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (lnGammaApproxOf b w).1 lv ∧ Rounds (lnGammaApproxOf b w).2 hv ∧
      lv < v ∧ v ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := hb
  have : NeZero (2 * w + 64) := ⟨by omega⟩
  have ht : (powerOf2 (-(AzNat.ofNat (4 * w)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (4 * w) : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
      zpow_natCast, one_div_pow, one_div]
  obtain ⟨r, hr, hrle, -⟩ := subFloor_le hlo ht (2 * w + 64)
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (4 * w) := by positivity
  refine ⟨r, hi, ?_, ?_, by linarith, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hr)
    rw [fval_of_toVal_coe hr] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- The bracket as `Roundable`s encloses `ln Γ(x)`, strictly from below. -/
theorem lnGammaApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hpos : 0 < xv) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (lnGammaApprox x e w).1 lv ∧ Rounds (lnGammaApprox x e w).2 hv ∧
      lv < Real.log (Real.Gamma xv) ∧ Real.log (Real.Gamma xv) ≤ hv :=
  lnGammaApproxOf_spec (lnGammaBracket_spec hx hpos e hw) w

/-- **`ln Γ` is correctly rounded unless the fuel runs out.** -/
theorem lnGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnGammaPrecRound x p mode = liftVal Spec.lnGamma x p mode ∨
      lnGammaPrecRound x p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [lnGammaPrecRound, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [lnGammaPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.lnGamma_bot, roundVal_none]
    · simp only [lnGammaPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.lnGamma_top, roundVal_top]
  | zero =>
    left
    simp only [lnGammaPrecRound, toVal_zero, Option.bind_some, Spec.lnGamma_zero, roundVal_top]
  | finite s e q m hv =>
    cases s with
    | false =>
      left
      simp only [lnGammaPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.lnGamma_coe_of_neg (finiteVal_false_neg e hv), roundVal_none]
    | true =>
      have hpos := finiteVal_true_pos e hv
      have hx := toVal_finite true e q m hv
      simp only [lnGammaPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.lnGamma_coe_of_pos hpos]
      split_ifs with h12
      · left
        have hval : finiteVal true e m = 1 ∨ finiteVal true e m = 2 := by
          rcases Bool.or_eq_true _ _ ▸ h12 with h | h
          · left
            rw [eqIEEE_one_iff, toVal_finite, Option.some.injEq] at h
            exact_mod_cast h
          · right
            rw [eqIEEE_iff] at h
            obtain ⟨v, h1, h2⟩ := h
            rw [toVal_ofAzNat_ofNat] at h2
            rw [toVal_finite, ← h2, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
            exact_mod_cast h1
        have h0 : Real.log (Real.Gamma (finiteVal true e m)) = 0 := by
          rcases hval with h | h <;> rw [h]
          · rw [Real.Gamma_one, Real.log_one]
          · rw [Real.Gamma_two, Real.log_one]
        rw [h0, EReal.coe_zero, roundVal_zero]
      · rcases eq_or_ne (zivLoop (lnGammaApprox (finite true e q m hv) e) p mode lnGammaFuel
          (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))) (nan, .eq)
          with hz | hz
        · right; exact hz
        · left
          exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
            (fun w hw => by
              obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ := lnGammaApprox_spec hx hpos e hw
              exact ⟨lv, hv', hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
            _ _ (le_max_left _ _) hz

/-!
# `ln |Γ(x)|` and the sign of `Γ(x)`: correctness

* `Spec.lnAbsGamma`: `ln |Γ|` on the extended reals, `+∞` at `±∞` and at the poles.
* `lnAbsGammaReflect_spec`, `lnAbsGammaNegEncl_spec`: the reflection formula on enclosures.
* `Gamma_pos_iff_odd`, `Gamma_pos_iff_trunc_odd`: the sign of `Γ` at a negative non-integer.
* **`lnAbsGammaPrecRound_eq_or`**: the value is correctly rounded, or `NaN` (the fuel).
* **`lnAbsGammaPrecRound_sign`**: the sign is that of `Γ(x)` wherever `Γ(x)` is a nonzero real.
-/

section

open Real

namespace Spec

open Classical in
/-- `ln |Γ|` on the extended reals: `+∞` at `±∞` and at the poles `0, −1, −2, …`. -/
noncomputable def lnAbsGamma (a : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ then some ⊤
  else if a.toReal ≤ 0 ∧ ∃ k : ℤ, a.toReal = k then some ⊤
  else some ((Real.log |Real.Gamma a.toReal| : ℝ) : EReal)

theorem lnAbsGamma_top : lnAbsGamma ⊤ = some ⊤ := by simp [lnAbsGamma]

theorem lnAbsGamma_bot : lnAbsGamma ⊥ = some ⊤ := by simp [lnAbsGamma]

theorem lnAbsGamma_coe_of_pole {xv : ℝ} (h : xv ≤ 0) (hk : ∃ k : ℤ, xv = k) :
    lnAbsGamma (xv : EReal) = some ⊤ := by
  unfold lnAbsGamma
  rw [ite_eq_right (by simp), EReal.toReal_coe, ite_eq_left ⟨h, hk⟩]

theorem lnAbsGamma_coe {xv : ℝ} (h : ¬ (xv ≤ 0 ∧ ∃ k : ℤ, xv = k)) :
    lnAbsGamma (xv : EReal) = some ((Real.log |Real.Gamma xv| : ℝ) : EReal) := by
  unfold lnAbsGamma
  rw [ite_eq_right (by simp), EReal.toReal_coe, ite_eq_right h]

theorem lnAbsGamma_coe_of_pos {xv : ℝ} (h : 0 < xv) :
    lnAbsGamma (xv : EReal) = lnGamma (xv : EReal) := by
  rw [lnAbsGamma_coe (fun hc => absurd hc.1 (not_le.mpr h)), lnGamma_coe_of_pos h,
    abs_of_pos (Real.Gamma_pos_of_pos h)]

end Spec

/-- The reflection formula at a real that is not an integer. -/
theorem Gamma_eq_reflect {xv : ℝ} (hx1 : xv < 1) (hsin : Real.sin (π * xv) ≠ 0) :
    Real.Gamma xv = π / (Real.sin (π * xv) * Real.Gamma (-xv + 1)) := by
  have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hrefl := Real.Gamma_mul_Gamma_one_sub xv
  rw [show (1 : ℝ) - xv = -xv + 1 by ring] at hrefl
  rw [eq_div_iff (mul_ne_zero hsin hg0.ne'), mul_comm (Real.sin _), ← mul_assoc, hrefl]
  field_simp

/-- **The reflection formula for `ln |Γ(x)|` on enclosures**, `x < 0`. -/
theorem lnAbsGammaReflect_spec {S : Option (Bool × Encl)} {L : Encl} {xv : ℝ} (hx0 : xv < 0)
    {w : ℕ} (hw : 64 ≤ w)
    (hS : ∀ neg S', S = some (neg, S') →
      IsEnclPos S' ((if neg then -1 else 1) * Real.sin (π * xv)))
    (hL : IsEncl L (Real.log (Real.Gamma (-xv + 1)))) {b : Encl}
    (h : lnAbsGammaReflect S L w = some b) : IsEncl b (Real.log |Real.Gamma xv|) := by
  unfold lnAbsGammaReflect at h
  split at h
  · exact absurd h (by simp)
  · rename_i neg S'
    rw [Option.some.injEq] at h
    subst h
    have : NeZero (w + 16) := ⟨by omega⟩
    have hSe := hS neg S' rfl
    set c : ℝ := if neg then -1 else 1 with hc
    have hcs : 0 < c * Real.sin (π * xv) := by
      obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSe
      linarith
    have hsin : Real.sin (π * xv) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcs
      exact lt_irrefl _ hcs
    have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hD := (enclosesPos_pi (w := w + 16) (by omega)).div (by omega : 2 ≤ w + 16) hSe
    have hLn := lnOfEncl_pos hD (w := w + 16) (by omega)
    have hsub := hLn.sub (w := w + 16) hL
    convert hsub using 1
    have habs : |Real.Gamma xv| = π / (c * Real.sin (π * xv)) / Real.Gamma (-xv + 1) := by
      rw [Gamma_eq_reflect (by linarith) hsin, abs_div, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos hg0, div_div]
      congr 2
      rw [← abs_of_pos hcs, abs_mul]
      have : |c| = 1 := by
        rw [hc]
        split_ifs <;> simp
      rw [this, one_mul]
    rw [habs, Real.log_div (div_pos Real.pi_pos hcs).ne' hg0.ne']

/-- **`lnAbsGammaNegEncl` answers with an enclosure of `ln |Γ(x)|`**, `x < 0`. -/
theorem lnAbsGammaNegEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv < 0) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) {b : Encl}
    (h : lnAbsGammaNegEncl x e w = some b) : IsEncl b (Real.log |Real.Gamma xv|) := by
  unfold lnAbsGammaNegEncl at h
  dsimp only at h
  have : NeZero (w + 32) := ⟨by omega⟩
  have hnx : (-x).toVal = some ((-xv : ℝ) : EReal) := by
    rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
  have hX₁ : IsEnclPos (Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one)) (-xv + 1) :=
    (isEnclPos_exact hnx (by linarith)).add (by omega) enclosesPos_one.encloses0
  exact lnAbsGammaReflect_spec hx0 hw
    (fun _ _ hS => gammaSinEncl_spec hx (W := w + 16) (by omega) hw hS)
    (lnGammaBracketEncl_spec hX₁ ((if e.sign then e else 0) + 1) hw) h

/-- **The bracket of `lnAbsGammaApproxOf` encloses the value strictly from below or is
rejected**, when every answer is an enclosure of the value. -/
theorem lnAbsGammaApproxOf_valid_or_none {c : Option Encl} {v : ℝ}
    (hc : ∀ b, c = some b → IsEncl b v) (w p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (lnAbsGammaApproxOf c w).1 lv ∧
        Rounds (lnAbsGammaApproxOf c w).2 hv ∧ lv ≤ v ∧ v ≤ hv ∧ (lv = v → hv = v)) ∨
      roundingPossible (lnAbsGammaApproxOf c w).1 (lnAbsGammaApproxOf c w).2 p mode
        = none := by
  unfold lnAbsGammaApproxOf
  cases hc' : c with
  | none => right; exact roundingPossible_negSwapApprox_dummy false p mode
  | some b =>
    left
    obtain ⟨lv, hv, h1, h2, h3, h4⟩ := lnGammaApproxOf_spec (hc b hc') w
    exact ⟨lv, hv, h1, h2, h3.le, h4, fun h => absurd h h3.ne⟩

/-- **At every level `w ≥ 64` the bracket of `lnAbsGammaApprox` encloses `ln |Γ(x)|` strictly
from below or is rejected.** -/
theorem lnAbsGammaApprox_valid_or_none {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv < 0) (e : AzInt) {w : ℕ} (hw : 64 ≤ w)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (lnAbsGammaApprox x e w).1 lv ∧ Rounds (lnAbsGammaApprox x e w).2 hv ∧
        lv ≤ Real.log |Real.Gamma xv| ∧ Real.log |Real.Gamma xv| ≤ hv ∧
        (lv = Real.log |Real.Gamma xv| → hv = Real.log |Real.Gamma xv|)) ∨
      roundingPossible (lnAbsGammaApprox x e w).1 (lnAbsGammaApprox x e w).2 p mode = none :=
  lnAbsGammaApproxOf_valid_or_none (fun _ hc => lnAbsGammaNegEncl_spec hx hx0 e hw hc) w p mode

/-- **The sign of `Γ` at a negative real `x`** with an integer `k` in `(x, x + 1)`: positive
exactly when `k` is odd. -/
theorem Gamma_pos_iff_odd {xv : ℝ} (hx0 : xv < 0) {k : ℤ} (ht0 : xv - k < 0)
    (ht1 : -1 < xv - k) : Odd k ↔ 0 < Real.Gamma xv := by
  have hst : Real.sin (π * (xv - k)) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg Real.pi_pos ht0)
      (by nlinarith [Real.pi_pos])
  have hsx := sin_pi_mul_eq xv k
  have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos (by linarith)
  constructor
  · intro ho
    rw [ho.neg_one_zpow, neg_one_mul] at hsx
    have hs : 0 < Real.sin (π * xv) := by linarith
    rw [Gamma_eq_reflect (by linarith) hs.ne']
    exact div_pos Real.pi_pos (mul_pos hs hg0)
  · intro hG
    by_contra ho
    have he : Even k := Int.not_odd_iff_even.mp ho
    rw [he.neg_one_zpow, one_mul] at hsx
    have hs : Real.sin (π * xv) < 0 := by linarith
    rw [Gamma_eq_reflect (by linarith) hs.ne] at hG
    have : π / (Real.sin (π * xv) * Real.Gamma (-xv + 1)) < 0 :=
      div_neg_of_pos_of_neg Real.pi_pos (mul_neg_of_neg_of_pos hs hg0)
    linarith

/-- **The sign of `Γ` at a negative float that is not an integer**: positive exactly when the
truncation is odd. -/
theorem Gamma_pos_iff_trunc_odd {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv < 0) (hni : ¬ ∃ k : ℤ, xv = k) :
    (truncToAzInt x).isOdd = true ↔ 0 < Real.Gamma xv := by
  obtain ⟨h1, h2⟩ := truncToAzInt_spec hx
  set k := (truncToAzInt x).toInt with hk
  rw [abs_of_neg hx0] at h2
  have hkx : xv ≤ (k : ℝ) := by linarith [neg_abs_le (k : ℝ)]
  have hne : xv ≠ (k : ℝ) := fun h => hni ⟨k, h⟩
  have ht0 : xv - k < 0 := by
    rcases lt_or_eq_of_le hkx with h | h
    · linarith
    · exact absurd h hne
  have ht1 : -1 < xv - k := by linarith [(abs_lt.mp h1).2]
  rw [AzInt.isOdd_iff]
  exact Gamma_pos_iff_odd hx0 ht0 ht1

/-- **`ln |Γ|` is correctly rounded unless the fuel runs out.** -/
theorem lnAbsGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsGammaPrecRound x p mode).1 = liftVal Spec.lnAbsGamma x p mode ∨
      (lnAbsGammaPrecRound x p mode).1 = (nan, .eq) := by
  have hp := NeZero.ne p
  cases x with
  | nan => left; simp [lnAbsGammaPrecRound, liftVal, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [lnAbsGammaPrecRound, liftVal, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, Spec.lnAbsGamma_bot, roundVal_top]
    · simp only [lnAbsGammaPrecRound, liftVal, toVal_infinity, ↓reduceIte, Option.bind_some,
        Spec.lnAbsGamma_top, roundVal_top]
  | zero =>
    left
    simp only [lnAbsGammaPrecRound, liftVal, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.lnAbsGamma_coe_of_pole le_rfl ⟨0, by simp⟩, roundVal_top]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    cases s with
    | true =>
      have h := lnGammaPrecRound_eq_or (finite true e q m hv) p mode
      simp only [lnAbsGammaPrecRound, liftVal, toVal_finite, Option.bind_some] at h ⊢
      rwa [Spec.lnAbsGamma_coe_of_pos (finiteVal_true_pos e hv)]
    | false =>
      have hneg := finiteVal_false_neg e hv
      simp only [lnAbsGammaPrecRound, liftVal, toVal_finite, Option.bind_some]
      split_ifs with hi
      · left
        rw [Spec.lnAbsGamma_coe_of_pole hneg.le ((isInteger_finite false e hv).mp hi),
          roundVal_top]
      · have hni : ¬ ∃ k : ℤ, finiteVal false e m = k := fun hk =>
          hi ((isInteger_finite false e hv).mpr hk)
        rw [Spec.lnAbsGamma_coe (fun hc => hni hc.2)]
        rcases eq_or_ne (zivLoop (lnAbsGammaApprox (finite false e q m hv) e) p mode
          lnGammaFuel (max 64 (p + 32))) (nan, .eq) with hz | hz
        · right; exact hz
        · left
          exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
            (fun w hw => lnAbsGammaApprox_valid_or_none hx hneg e hw p mode)
            _ _ (le_max_left _ _) hz

/-- **The sign component is the sign of `Γ(x)`** at every finite `x` that is not a pole. -/
theorem lnAbsGammaPrecRound_sign {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hnp : ¬ (xv ≤ 0 ∧ ∃ k : ℤ, xv = k)) (p : ℕ) (mode : RoundingMode) :
    (lnAbsGammaPrecRound x p mode).2 = true ↔ 0 < Real.Gamma xv := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero =>
    rw [toVal_zero, Option.some.injEq] at hx
    have : xv = 0 := by exact_mod_cast hx.symm
    exact absurd ⟨this.le, 0, by simp [this]⟩ hnp
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    subst hx
    cases s with
    | true =>
      simp only [lnAbsGammaPrecRound, true_iff]
      exact Real.Gamma_pos_of_pos (finiteVal_true_pos e hv)
    | false =>
      have hneg := finiteVal_false_neg e hv
      have hni : ¬ ∃ k : ℤ, finiteVal false e m = k := fun hk => hnp ⟨hneg.le, hk⟩
      have hi : ¬ isInteger (finite false e q m hv) = true := fun h =>
        hni ((isInteger_finite false e hv).mp h)
      simp only [lnAbsGammaPrecRound, ite_eq_right hi, gammaSign]
      exact Gamma_pos_iff_trunc_odd (toVal_finite false e q m hv) hneg hni

end

end Azurite.AzFloat
