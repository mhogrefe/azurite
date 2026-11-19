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
import Azurite.AzFloat.Equiv.LnGammaCertificate

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

/-- The bracket as `Roundable`s encloses `ln Γ(x)`, strictly from below. -/
theorem lnGammaApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hpos : 0 < xv) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (lnGammaApprox x e w).1 lv ∧ Rounds (lnGammaApprox x e w).2 hv ∧
      lv < Real.log (Real.Gamma xv) ∧ Real.log (Real.Gamma xv) ≤ hv :=
  lnGammaApproxOf_spec (lnGammaBracket_spec hx hpos e hw) w

/-- **The branches of `lnGammaPrecRoundFuel`**: the correctly rounded value, whatever the
fuel, or — at a positive float that is not an integer — the fuel loop on `lnGammaApprox`. -/
theorem lnGammaPrecRoundFuel_eq_or_loop (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnGammaPrecRoundFuel fuel x p mode = liftVal Spec.lnGamma x p mode ∨
      (isInteger x = false ∧ ∃ (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite true e q m hv ∧ lnGammaPrecRoundFuel fuel x p mode
          = zivLoop (lnGammaApprox (finite true e q m hv) e) p mode fuel
            (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [lnGammaPrecRoundFuel, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [lnGammaPrecRoundFuel, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.lnGamma_bot, roundVal_none]
    · simp only [lnGammaPrecRoundFuel, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.lnGamma_top, roundVal_top]
  | zero =>
    left
    simp only [lnGammaPrecRoundFuel, toVal_zero, Option.bind_some, Spec.lnGamma_zero,
      roundVal_top]
  | finite s e q m hv =>
    cases s with
    | false =>
      left
      simp only [lnGammaPrecRoundFuel, toVal_finite, Option.bind_some]
      rw [Spec.lnGamma_coe_of_neg (finiteVal_false_neg e hv), roundVal_none]
    | true =>
      have hpos := finiteVal_true_pos e hv
      have hx := toVal_finite true e q m hv
      simp only [lnGammaPrecRoundFuel, toVal_finite, Option.bind_some]
      rw [Spec.lnGamma_coe_of_pos hpos]
      by_cases h12 : (eqIEEE (finite true e q m hv) one
          || eqIEEE (finite true e q m hv) (ofAzNat (AzNat.ofNat 2))) = true
      · left
        rw [dite_eq_left h12]
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
      · rw [dite_eq_right h12, dite_eq_right hp]
        by_cases hI : isInteger (finite true e q m hv) = true
        · left
          rw [dite_eq_left hI]
          obtain ⟨n, hn, hval⟩ := lnGammaInt_spec hv h12 hI
          have hirr := irrational_log_gamma_nat hn
          rw [← hval] at hirr
          refine zivLoopCertified_eq_or_none p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
            (by omega) (fun w hw => Or.inl ?_) _
          obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ :=
            lnGammaApprox_spec hx hpos e (le_trans (le_max_left _ _) hw)
          exact ⟨lv, hv', hl, hh, hlo.le, hhi⟩
        · rw [dite_eq_right hI]
          exact Or.inr ⟨by simpa using hI, e, q, m, hv, rfl, rfl⟩

/-- The value of `Spec.lnGamma` at a positive float. -/
theorem liftVal_lnGamma_finite (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    (finite true e q m hv).toVal.bind Spec.lnGamma
      = some ((Real.log (Real.Gamma (finiteVal true e m)) : ℝ) : EReal) := by
  rw [toVal_finite, Option.bind_some, Spec.lnGamma_coe_of_pos (finiteVal_true_pos e hv)]

/-- **`ln Γ` with explicit fuel is correctly rounded unless the fuel runs out**, which does
not happen at an integer. -/
theorem lnGammaPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnGammaPrecRoundFuel fuel x p mode = liftVal Spec.lnGamma x p mode ∨
      (lnGammaPrecRoundFuel fuel x p mode = (nan, .eq) ∧ isInteger x = false) := by
  rcases lnGammaPrecRoundFuel_eq_or_loop fuel x p mode with h | ⟨hI, e, q, m, hv, rfl, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (zivLoop (lnGammaApprox (finite true e q m hv) e) p mode fuel
      (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q))) (nan, .eq) with hz | hz
    · exact Or.inr ⟨h.trans hz, hI⟩
    · left
      rw [h]
      unfold liftVal
      rw [liftVal_lnGamma_finite e hv]
      exact zivLoop_eq_of_ne_nan_threshold p mode _ _ 64
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ :=
            lnGammaApprox_spec (toVal_finite true e q m hv) (finiteVal_true_pos e hv) e hw
          exact ⟨lv, hv', hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
        _ _ (le_max_left _ _) hz

/-- **`ln Γ` is correctly rounded unless the fuel runs out.** -/
theorem lnGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnGammaPrecRound x p mode = liftVal Spec.lnGamma x p mode ∨
      lnGammaPrecRound x p mode = (nan, .eq) :=
  (lnGammaPrecRoundFuel_eq_or (lnGammaFuel p) x p mode).imp_right And.left

/-- **`ln Γ` is correctly rounded, unconditionally, at the integers**: `0` at `1` and `2`,
and `ln (n − 1)!` is irrational from `3` on. -/
theorem lnGammaPrecRound_eq_of_isInteger (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h : isInteger x = true) : lnGammaPrecRound x p mode = liftVal Spec.lnGamma x p mode := by
  rcases lnGammaPrecRoundFuel_eq_or (lnGammaFuel p) x p mode with h' | ⟨-, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-- The fuel loop of `ln Γ` at a positive float is correct for every large enough fuel when
the value is no rounding boundary. -/
theorem lnGamma_zivLoop_eventually (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 64 ≤ w₀)
    (hB : ((Real.log (Real.Gamma (finiteVal true e m)) : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel →
      zivLoop (lnGammaApprox (finite true e q m hv) e) p mode fuel w₀
        = roundVal p mode (some ((Real.log (Real.Gamma (finiteVal true e m)) : ℝ) : EReal)) :=
  zivLoop_eventually_eq p mode _
    (lnGammaApprox_bracketConv (toVal_finite true e q m hv) (finiteVal_true_pos e hv) e)
    (ne_zero_of_not_mem_floatSet hB) hB w₀ (by omega) (fun w hw => Or.inl (by
      obtain ⟨lv, hv', hl, hh, hlo, hhi⟩ :=
        lnGammaApprox_spec (toVal_finite true e q m hv) (finiteVal_true_pos e hv) e
          (le_trans hw₀ hw)
      exact ⟨lv, hv', hl, hh, hlo.le, hhi⟩))

/-- The values of `ln Γ` that are known exactly: at `1` and `2`. -/
theorem isDyadic_of_lnGamma {a : EReal} (ha : ∀ t : ℝ, a = (t : EReal) → t ≤ 0 ∨ t = 1 ∨ t = 2)
    {v : ℝ} (hv : Spec.lnGamma a = some (v : EReal)) : IsDyadic v := by
  induction a using EReal.rec with
  | bot => rw [Spec.lnGamma_bot] at hv; exact absurd hv (by simp)
  | top =>
    rw [Spec.lnGamma_top, Option.some.injEq] at hv
    exact absurd hv (by simp)
  | coe t =>
    rcases ha t rfl with h | h | h
    · rcases h.lt_or_eq with h | h
      · rw [Spec.lnGamma_coe_of_neg h] at hv
        exact absurd hv (by simp)
      · rw [h, EReal.coe_zero, Spec.lnGamma_zero, Option.some.injEq] at hv
        exact absurd hv (by simp)
    · rw [h, Spec.lnGamma_coe_of_pos one_pos, Real.Gamma_one, Real.log_one, Option.some.injEq,
        EReal.coe_eq_coe_iff] at hv
      rw [← hv]
      exact isDyadic_zero
    · rw [h, Spec.lnGamma_coe_of_pos two_pos, Real.Gamma_two, Real.log_one, Option.some.injEq,
        EReal.coe_eq_coe_iff] at hv
      rw [← hv]
      exact isDyadic_zero

/-- **The specification of `ln Γ`** (`ZivSpec`): sound at every fuel; complete in the limit
of the fuel wherever the value is no rounding boundary; and correct at every fuel on the
arguments that are not finite, are not positive or are `1` or `2` (exact values) and on the
integers from `3` on (`ln (n − 1)!` is irrational). -/
theorem lnGammaPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.lnGamma) lnGammaPrecRoundFuel
      {x | ∀ v : ℝ, x.toVal = some (v : EReal) → v ≤ 0 ∨ v = 1 ∨ v = 2}
      {x | ∃ n : ℕ, 3 ≤ n ∧ x.toVal = some (((n : ℝ) : ℝ) : EReal)} where
  sound := fun fuel x p _ mode => (lnGammaPrecRoundFuel_eq_or fuel x p mode).imp_right And.left
  complete := fun x p _ mode hB => by
    by_cases hgen : ∃ (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite true e q m hv
    · obtain ⟨e, q, m, hv, rfl⟩ := hgen
      have hval := liftVal_lnGamma_finite e hv
      obtain ⟨F, hF⟩ := lnGamma_zivLoop_eventually e hv p mode
        (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q)) (le_max_left _ _)
        (hB _ hval)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases lnGammaPrecRoundFuel_eq_or_loop fuel (finite true e q m hv) p mode with
        h | ⟨-, e', q', m', hv', heq, h⟩
      · exact h
      · rw [h, hval]
        cases heq
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases lnGammaPrecRoundFuel_eq_or_loop fuel x p mode with h | ⟨-, e, q, m, hv, rfl, -⟩
      · exact h
      · exact absurd ⟨e, q, m, hv, rfl⟩ hgen
  dyadic := fun x hx v hv => by
    cases hxv : x.toVal with
    | none => rw [hxv] at hv; exact absurd hv (by simp)
    | some a =>
      rw [hxv, Option.bind_some] at hv
      exact isDyadic_of_lnGamma (fun t ht => hx t (by rw [hxv, ht])) hv
  nondyadic := fun x hx => by
    obtain ⟨n, hn, hx⟩ := hx
    refine ⟨_, ?_, not_isDyadic_of_irrational (irrational_log_gamma_nat hn)⟩
    rw [hx, Option.bind_some, Spec.lnGamma_coe_of_pos (by positivity)]
  correct := fun x hx fuel p _ mode => by
    rcases lnGammaPrecRoundFuel_eq_or_loop fuel x p mode with h | ⟨hI, e, q, m, hv, rfl, -⟩
    · exact h
    · exfalso
      have hxv := toVal_finite true e q m hv
      have hint : ∀ k : ℤ, finiteVal true e m ≠ k := fun k hk => by
        rw [(isInteger_iff_of_toVal hxv).mpr ⟨k, hk⟩] at hI
        exact Bool.noConfusion hI
      rcases hx with hD | ⟨n, -, hn⟩
      · rcases hD _ hxv with h | h | h
        · exact absurd (finiteVal_true_pos e hv) (not_lt.mpr h)
        · exact hint 1 (by rw [h]; simp)
        · exact hint 2 (by rw [h]; simp)
      · rw [hxv, Option.some.injEq, EReal.coe_eq_coe_iff] at hn
        exact hint n (by rw [hn]; simp)

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

/-! ### Convergence of the bracket at a negative argument -/

open Filter Topology in
/-- The reflection formula for `ln |Γ|` on widths. -/
theorem lnAbsGammaReflect_width {S' L : Encl} {neg : Bool} {xv lamS εL G B : ℝ} (hx0 : xv < 0)
    {w : ℕ} (hw : 64 ≤ w)
    (hS : LEncl S' ((if neg then -1 else 1) * Real.sin (π * xv)) lamS) (hlam0 : 0 ≤ lamS)
    (hlam : lamS + 9 * (1 / 2 : ℝ) ^ (w + 16) ≤ 1 / 2)
    (hL : AEncl L (Real.log (Real.Gamma (-xv + 1))) εL)
    (hG : |Real.log (π / ((if neg then -1 else 1) * Real.sin (π * xv)))| ≤ G)
    (hB : |Real.log (|Real.Gamma xv|)| + (lnW G (w + 16) + 5 * (lamS + 9 * (1 / 2 : ℝ) ^ (w + 16)))
      + εL ≤ B) :
    ∃ b, lnAbsGammaReflect (some (neg, S')) L w = some b ∧
      AEncl b (Real.log |Real.Gamma xv|)
        (lnW G (w + 16) + 5 * (lamS + 9 * (1 / 2 : ℝ) ^ (w + 16)) + εL
          + 4 * B * (1 / 2 : ℝ) ^ (w + 16)) := by
  have hV : 64 ≤ w + 16 := by omega
  have : NeZero (w + 16) := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ (w + 16) ≤ 1 / 8 := (half_pow_le_of_64 hV).trans (by norm_num)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (w + 16) := by positivity
  set c : ℝ := if neg then -1 else 1 with hc
  have hcs : 0 < c * Real.sin (π * xv) := hS.pos
  have hsin : Real.sin (π * xv) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcs
    exact lt_irrefl _ hcs
  have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos (by linarith)
  have habs : |Real.Gamma xv| = π / (c * Real.sin (π * xv)) / Real.Gamma (-xv + 1) := by
    rw [Gamma_eq_reflect (by linarith) hsin, abs_div, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos hg0, div_div]
    congr 2
    rw [← abs_of_pos hcs, abs_mul]
    have : |c| = 1 := by
      rw [hc]
      split_ifs <;> simp
    rw [this, one_mul]
  have hval : Real.log |Real.Gamma xv|
      = Real.log (π / (c * Real.sin (π * xv))) - Real.log (Real.Gamma (-xv + 1)) := by
    rw [habs, Real.log_div (div_pos Real.pi_pos hcs).ne' hg0.ne']
  have hD := ((LEncl.pi hV).div hu8 hS).mono (le_of_eq (by ring :
    3 * (1 / 2 : ℝ) ^ (w + 16) + lamS + 6 * (1 / 2 : ℝ) ^ (w + 16)
      = lamS + 9 * (1 / 2 : ℝ) ^ (w + 16)))
  have hLn := hD.lnOfEncl (by positivity) hlam hG hV
  rw [hval] at hB ⊢
  exact ⟨_, rfl, hLn.sub (w := w + 16) hL hB⟩

open Filter Topology in
/-- **The reflection formula for `ln |Γ(x)|` converges** at a negative non-integer `x`, from
enclosures `X w` of `1 − x` of relative width `6 · 2^(−w−32)` and a convergent sine. -/
theorem lnAbsGammaReflect_conv {xv : ℝ} (hneg : xv < 0) (e' : AzInt) {X : ℕ → Encl}
    (hX : ∀ w, LEncl (X w) (-xv + 1) (6 * (1 / 2 : ℝ) ^ (w + 32)))
    {S : ℕ → Option (Bool × Encl)} (hSc : SinConv S xv) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ b,
      lnAbsGammaReflect (S w) (lnGammaBracketEncl (X w) e' w) w = some b ∧
        AEncl b (Real.log |Real.Gamma xv|) (ε w) := by
  have hpos1 : 0 < -xv + 1 := by linarith
  obtain ⟨W₀, hW₀⟩ := lnGammaBracketEncl_eventually hpos1 e'
  obtain ⟨ES, htS, hevS⟩ := hSc
  set s := |Real.sin (π * xv)| with hs
  have hs0 : 0 < s := by
    obtain ⟨w, neg, S', -, hSp, -⟩ := hevS.exists
    exact abs_pos.mpr fun h0 => by
      obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSp
      rw [h0, mul_zero] at hl1
      linarith
  set G := |Real.log (π / s)| with hG
  set B := |Real.log (|Real.Gamma xv|)| + 2 with hB
  have hu : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 16)
  have hlam : Tendsto (fun w => 2 * ES w / s + 9 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := ((htS.const_mul 2).div_const s).add (hu.const_mul 9)
    simpa using this
  have hLn : Tendsto (fun w => lnW G (w + 16)
      + 5 * (2 * ES w / s + 9 * (1 / 2 : ℝ) ^ (w + 16))) atTop (𝓝 0) := by
    have hG0 : 0 ≤ G := abs_nonneg _
    have := (tendsto_lnW_add hG0 16).add (hlam.const_mul 5)
    simpa using this
  have hlg := tendsto_lgEps (-xv + 1) e'
  have hε : Tendsto (fun w => lnW G (w + 16)
      + 5 * (2 * ES w / s + 9 * (1 / 2 : ℝ) ^ (w + 16)) + lgEps (-xv + 1) e' w
      + 4 * B * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := (hLn.add hlg).add (hu.const_mul (4 * B))
    simpa using this
  refine ⟨_, hε, ?_⟩
  filter_upwards [hevS, eventually_ge_atTop W₀, eventually_ge_atTop 64,
    htS.eventually (ge_mem_nhds (by positivity : 0 < s / 2)),
    hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hLn.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlg.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with w h1 h2 h3 h4 h5 h6 h7
  obtain ⟨neg, S', hS, hSp, hSw⟩ := h1
  have hsv : (if neg then -1 else 1) * Real.sin (π * xv) = s := by
    obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSp
    exact sign_mul_eq_abs (by linarith)
  have h8 : 0 ≤ ES w := by
    obtain ⟨l, u, -, -, a1, a2, a3⟩ := hSw
    linarith
  have hSL : LEncl S' ((if neg then -1 else 1) * Real.sin (π * xv)) (2 * ES w / s) := by
    rw [hsv]
    exact LEncl.ofA hSw (by linarith) hs0
  have hL := hW₀ w h2 _ _ (hX w) (by positivity) (six_le_eight _)
  obtain ⟨b, hb, hbw⟩ := lnAbsGammaReflect_width (G := G) (B := B) hneg h3 hSL (by positivity)
    h5 hL (by rw [hsv]) (by rw [hB]; linarith)
  exact ⟨b, by rw [hS]; exact hb, hbw⟩

/-- **Brackets made from optional enclosures that are eventually answers of widths tending to
`0` converge.** -/
theorem lnAbsGammaApproxOf_bracketConv {c : ℕ → Option Encl} {v : ℝ}
    (h : ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ᶠ w in Filter.atTop, ∃ b, c w = some b ∧ AEncl b v (ε w)) :
    BracketConv (fun w => lnAbsGammaApproxOf (c w) w) v := by
  obtain ⟨ε, hε, hev⟩ := h
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp hev
  refine (lnGammaApproxOf_bracketConv (b := fun w => (c w).getD (Encl.exact one)) hε
    (Filter.eventually_atTop.mpr ⟨W₀, fun w hw => ?_⟩)).congr ⟨W₀, fun w hw => ?_⟩
  · obtain ⟨b, hb, hbw⟩ := hW₀ w hw
    rw [hb]
    exact hbw
  · obtain ⟨b, hb, -⟩ := hW₀ w hw
    rw [hb]
    rfl

/-- **The bracket of `ln |Γ(x)|` converges** at a negative float that is not an integer. -/
theorem lnAbsGammaApprox_bracketConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hneg : xv < 0) (hint : ∀ k : ℤ, xv ≠ k) (e : AzInt) :
    BracketConv (lnAbsGammaApprox x e) (Real.log |Real.Gamma xv|) := by
  have hnx : (-x).toVal = some ((-xv : ℝ) : EReal) := by
    rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
  refine lnAbsGammaApproxOf_bracketConv (lnAbsGammaReflect_conv hneg
    ((if e.sign then e else 0) + 1)
    (X := fun w => Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one)) (fun w => ?_)
    (gammaSinEncl_conv hx hint))
  have : NeZero (w + 32) := ⟨by omega⟩
  have hu32 : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have := LEncl.add_exact (w := w + 32) (b := Encl.exact one) hu32
    (LEncl.exact hnx (by linarith)) le_rfl toVal_one' toVal_one' zero_le_one
  rwa [zero_add] at this

/-! ### The specifications of `ln |Γ|` -/

/-- **The branches of `lnAbsGammaPrecRoundFuel`**: the correctly rounded value, whatever the
fuel, or — at a float that is not an integer — a fuel loop. -/
theorem lnAbsGammaPrecRoundFuel_eq_or_loop (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsGammaPrecRoundFuel fuel x p mode).1 = liftVal Spec.lnAbsGamma x p mode ∨
      (isInteger x = false ∧ ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat)
        (hv : FiniteValid q m), x = finite s e q m hv ∧
          (lnAbsGammaPrecRoundFuel fuel x p mode).1
            = zivLoop (if s then lnGammaApprox (finite s e q m hv) e
                else lnAbsGammaApprox (finite s e q m hv) e) p mode fuel
              (if s then max 64 (p + 32 + lnGammaCancelBits (finite s e q m hv) q)
                else max 64 (p + 32))) := by
  have hp := NeZero.ne p
  cases x with
  | nan => left; simp [lnAbsGammaPrecRoundFuel, liftVal, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_infinity, Bool.false_eq_true,
        ↓reduceIte, Option.bind_some, Spec.lnAbsGamma_bot, roundVal_top]
    · simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_infinity, ↓reduceIte,
        Option.bind_some, Spec.lnAbsGamma_top, roundVal_top]
  | zero =>
    left
    simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.lnAbsGamma_coe_of_pole le_rfl ⟨0, by simp⟩, roundVal_top]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    cases s with
    | true =>
      rcases lnGammaPrecRoundFuel_eq_or_loop fuel (finite true e q m hv) p mode with
        h | ⟨hI, e', q', m', hv', heq, h⟩
      · left
        simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_finite, Option.bind_some] at h ⊢
        rwa [Spec.lnAbsGamma_coe_of_pos (finiteVal_true_pos e hv)]
      · cases heq
        exact Or.inr ⟨hI, true, e, q, m, hv, rfl, h⟩
    | false =>
      have hneg := finiteVal_false_neg e hv
      simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_finite, Option.bind_some]
      by_cases hi : isInteger (finite false e q m hv) = true
      · left
        rw [ite_eq_left hi, Spec.lnAbsGamma_coe_of_pole hneg.le
          ((isInteger_finite false e hv).mp hi), roundVal_top]
      · right
        refine ⟨by simpa using hi, false, e, q, m, hv, rfl, ?_⟩
        rw [ite_eq_right hi]
        simp only [ite_eq_right hp, Bool.false_eq_true, ↓reduceIte]

/-- **`ln |Γ|` with explicit fuel is correctly rounded unless the fuel runs out**, which does
not happen at an integer. -/
theorem lnAbsGammaPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsGammaPrecRoundFuel fuel x p mode).1 = liftVal Spec.lnAbsGamma x p mode ∨
      ((lnAbsGammaPrecRoundFuel fuel x p mode).1 = (nan, .eq) ∧ isInteger x = false) := by
  have hp := NeZero.ne p
  cases x with
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    cases s with
    | true =>
      have h := lnGammaPrecRoundFuel_eq_or fuel (finite true e q m hv) p mode
      simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_finite, Option.bind_some] at h ⊢
      rwa [Spec.lnAbsGamma_coe_of_pos (finiteVal_true_pos e hv)]
    | false =>
      have hneg := finiteVal_false_neg e hv
      simp only [lnAbsGammaPrecRoundFuel, liftVal, toVal_finite, Option.bind_some]
      by_cases hi : isInteger (finite false e q m hv) = true
      · left
        rw [ite_eq_left hi, Spec.lnAbsGamma_coe_of_pole hneg.le
          ((isInteger_finite false e hv).mp hi), roundVal_top]
      · have hni : ¬ ∃ k : ℤ, finiteVal false e m = k := fun hk =>
          hi ((isInteger_finite false e hv).mpr hk)
        rw [ite_eq_right hi, Spec.lnAbsGamma_coe (fun hc => hni hc.2)]
        simp only [ite_eq_right hp]
        rcases eq_or_ne (zivLoop (lnAbsGammaApprox (finite false e q m hv) e) p mode
          fuel (max 64 (p + 32))) (nan, .eq) with hz | hz
        · right; exact ⟨hz, by simpa using hi⟩
        · left
          exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
            (fun w hw => lnAbsGammaApprox_valid_or_none hx hneg e hw p mode)
            _ _ (le_max_left _ _) hz
  | nan | zero | infinity s =>
    rcases lnAbsGammaPrecRoundFuel_eq_or_loop fuel _ p mode with h | ⟨-, s', e, q, m, hv, heq, -⟩
    · exact Or.inl h
    · exact absurd heq (by simp)

/-- **`ln |Γ|` is correctly rounded unless the fuel runs out.** -/
theorem lnAbsGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsGammaPrecRound x p mode).1 = liftVal Spec.lnAbsGamma x p mode ∨
      (lnAbsGammaPrecRound x p mode).1 = (nan, .eq) :=
  (lnAbsGammaPrecRoundFuel_eq_or (lnGammaFuel p) x p mode).imp_right And.left

/-- The values of `ln |Γ|` that are known exactly: `+∞` at the poles, `0` at `1` and `2`. -/
theorem isDyadic_of_lnAbsGamma {a : EReal}
    (ha : ∀ t : ℝ, a = (t : EReal) → (t ≤ 0 ∧ ∃ k : ℤ, t = k) ∨ t = 1 ∨ t = 2)
    {v : ℝ} (hv : Spec.lnAbsGamma a = some (v : EReal)) : IsDyadic v := by
  induction a using EReal.rec with
  | bot => rw [Spec.lnAbsGamma_bot, Option.some.injEq] at hv; exact absurd hv (by simp)
  | top => rw [Spec.lnAbsGamma_top, Option.some.injEq] at hv; exact absurd hv (by simp)
  | coe t =>
    rcases ha t rfl with h | h | h
    · rw [Spec.lnAbsGamma_coe_of_pole h.1 h.2, Option.some.injEq] at hv
      exact absurd hv (by simp)
    · rw [h, Spec.lnAbsGamma_coe_of_pos one_pos] at hv
      exact isDyadic_of_lnGamma (fun t ht => Or.inr (Or.inl (by exact_mod_cast ht.symm))) hv
    · rw [h, Spec.lnAbsGamma_coe_of_pos two_pos] at hv
      exact isDyadic_of_lnGamma (fun t ht => Or.inr (Or.inr (by exact_mod_cast ht.symm))) hv

/-- **The specification of `ln |Γ|`** (`ZivSpec`, for the rounded value): sound at every
fuel; complete in the limit of the fuel wherever the value is no rounding boundary; and
correct at every fuel at the arguments that are not finite, at the poles and at `1` and `2`
(exact values) and at the integers from `3` on. -/
theorem lnAbsGammaPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.lnAbsGamma)
      (fun fuel x p mode => (lnAbsGammaPrecRoundFuel fuel x p mode).1)
      {x | ∀ v : ℝ, x.toVal = some (v : EReal) → (v ≤ 0 ∧ ∃ k : ℤ, v = k) ∨ v = 1 ∨ v = 2}
      {x | ∃ n : ℕ, 3 ≤ n ∧ x.toVal = some (((n : ℝ) : ℝ) : EReal)} where
  sound := fun fuel x p _ mode =>
    (lnAbsGammaPrecRoundFuel_eq_or fuel x p mode).imp_right And.left
  complete := fun x p _ mode hB => by
    by_cases hgen : ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite s e q m hv ∧ isInteger x = false
    · obtain ⟨s, e, q, m, hv, rfl, hI⟩ := hgen
      have hx := toVal_finite s e q m hv
      have hint : ∀ k : ℤ, finiteVal s e m ≠ k := fun k hk => by
        rw [(isInteger_iff_of_toVal hx).mpr ⟨k, hk⟩] at hI
        exact Bool.noConfusion hI
      cases s with
      | true =>
        have hpos := finiteVal_true_pos e hv
        have hval : (finite true e q m hv).toVal.bind Spec.lnAbsGamma
            = some ((Real.log (Real.Gamma (finiteVal true e m)) : ℝ) : EReal) := by
          rw [toVal_finite, Option.bind_some, Spec.lnAbsGamma_coe_of_pos hpos,
            Spec.lnGamma_coe_of_pos hpos]
        obtain ⟨F, hF⟩ := lnGamma_zivLoop_eventually e hv p mode
          (max 64 (p + 32 + lnGammaCancelBits (finite true e q m hv) q)) (le_max_left _ _)
          (hB _ hval)
        refine ⟨F, fun fuel hfuel => ?_⟩
        rcases lnAbsGammaPrecRoundFuel_eq_or_loop fuel (finite true e q m hv) p mode with
          h | ⟨-, s', e', q', m', hv', heq, h⟩
        · exact h
        · cases heq
          simp only [↓reduceIte] at h
          rw [h, hval]
          exact hF fuel hfuel
      | false =>
        have hneg := finiteVal_false_neg e hv
        have hval : (finite false e q m hv).toVal.bind Spec.lnAbsGamma
            = some ((Real.log |Real.Gamma (finiteVal false e m)| : ℝ) : EReal) := by
          rw [toVal_finite, Option.bind_some,
            Spec.lnAbsGamma_coe (fun hc => by obtain ⟨k, hk⟩ := hc.2; exact hint k hk)]
        have hB' := hB _ hval
        obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode _
          (lnAbsGammaApprox_bracketConv hx hneg hint e) (ne_zero_of_not_mem_floatSet hB') hB'
          (max 64 (p + 32)) (by omega) (fun w hw => by
            rcases lnAbsGammaApprox_valid_or_none hx hneg e (w := w)
              (le_trans (le_max_left _ _) hw) p mode with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
            · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
            · exact Or.inr hn)
        refine ⟨F, fun fuel hfuel => ?_⟩
        rcases lnAbsGammaPrecRoundFuel_eq_or_loop fuel (finite false e q m hv) p mode with
          h | ⟨-, s', e', q', m', hv', heq, h⟩
        · exact h
        · cases heq
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          rw [h, hval]
          exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases lnAbsGammaPrecRoundFuel_eq_or_loop fuel x p mode with
        h | ⟨hI, s, e, q, m, hv, rfl, -⟩
      · exact h
      · exact absurd ⟨s, e, q, m, hv, rfl, hI⟩ hgen
  dyadic := fun x hx v hv => by
    cases hxv : x.toVal with
    | none => rw [hxv] at hv; exact absurd hv (by simp)
    | some a =>
      rw [hxv, Option.bind_some] at hv
      exact isDyadic_of_lnAbsGamma (fun t ht => hx t (by rw [hxv, ht])) hv
  nondyadic := fun x hx => by
    obtain ⟨n, hn, hx⟩ := hx
    refine ⟨_, ?_, not_isDyadic_of_irrational (irrational_log_gamma_nat hn)⟩
    have hpos : (0 : ℝ) < n := by positivity
    rw [hx, Option.bind_some, Spec.lnAbsGamma_coe_of_pos hpos, Spec.lnGamma_coe_of_pos hpos]
  correct := fun x hx fuel p _ mode => by
    rcases lnAbsGammaPrecRoundFuel_eq_or_loop fuel x p mode with
      h | ⟨hI, s, e, q, m, hv, rfl, -⟩
    · exact h
    · exfalso
      have hxv := toVal_finite s e q m hv
      have hint : ∀ k : ℤ, finiteVal s e m ≠ k := fun k hk => by
        rw [(isInteger_iff_of_toVal hxv).mpr ⟨k, hk⟩] at hI
        exact Bool.noConfusion hI
      rcases hx with hD | ⟨n, -, hn⟩
      · rcases hD _ hxv with ⟨-, k, hk⟩ | h | h
        · exact hint k hk
        · exact hint 1 (by rw [h]; simp)
        · exact hint 2 (by rw [h]; simp)
      · rw [hxv, Option.some.injEq, EReal.coe_eq_coe_iff] at hn
        exact hint n (by rw [hn]; simp)

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
      simp only [lnAbsGammaPrecRound, lnAbsGammaPrecRoundFuel, true_iff]
      exact Real.Gamma_pos_of_pos (finiteVal_true_pos e hv)
    | false =>
      have hneg := finiteVal_false_neg e hv
      have hni : ¬ ∃ k : ℤ, finiteVal false e m = k := fun hk => hnp ⟨hneg.le, hk⟩
      have hi : ¬ isInteger (finite false e q m hv) = true := fun h =>
        hni ((isInteger_finite false e hv).mp h)
      simp only [lnAbsGammaPrecRound, lnAbsGammaPrecRoundFuel, ite_eq_right hi, gammaSign]
      exact Gamma_pos_iff_trunc_odd (toVal_finite false e q m hv) hneg hni

end

end Azurite.AzFloat
