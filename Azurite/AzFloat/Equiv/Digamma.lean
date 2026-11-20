/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Digamma
import Azurite.AzFloat.Equiv.DigammaWidth
import Azurite.AzFloat.Equiv.DigammaBracket
import Azurite.AzFloat.Equiv.LnGamma

/-!
# Equivalence: the digamma function

`Spec.digamma : EReal → Option EReal` is the exact function on the extended reals (`none` is
`NaN`): `ψ(+∞) = +∞`, `ψ(0) = −∞`, `NaN` at the negative integers and at `−∞`, and
`DLMF.psiR x` (the real part of `ψ` at a real argument) elsewhere.
`digammaPrecRound_eq_or`: the result is the correct rounding of `Spec.digamma`, or `(nan, .eq)`
when the fuel of the Ziv loop runs out.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- `ψ` on the extended reals: `+∞ ↦ +∞`, `0 ↦ −∞` (the limit from the right), `NaN` at the
negative integers and at `−∞`. -/
noncomputable def digamma (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then none
  else if a.toReal = 0 then some ⊥
  else if a.toReal < 0 ∧ ∃ k : ℤ, a.toReal = k then none
  else some ((DLMF.psiR a.toReal : ℝ) : EReal)

theorem digamma_top : digamma ⊤ = some ⊤ := by simp [digamma]

theorem digamma_bot : digamma ⊥ = none := by
  unfold digamma
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

theorem digamma_zero : digamma ((0 : ℝ) : EReal) = some ⊥ := by
  unfold digamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe,
    ite_eq_left rfl]

theorem digamma_coe_of_pole {xv : ℝ} (h0 : xv < 0) (hk : ∃ k : ℤ, xv = k) :
    digamma (xv : EReal) = none := by
  unfold digamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe,
    ite_eq_right h0.ne, ite_eq_left ⟨h0, hk⟩]

theorem digamma_coe {xv : ℝ} (h0 : xv ≠ 0) (hnp : ¬ (xv < 0 ∧ ∃ k : ℤ, xv = k)) :
    digamma (xv : EReal) = some ((DLMF.psiR xv : ℝ) : EReal) := by
  unfold digamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe,
    ite_eq_right h0, ite_eq_right hnp]

end Spec

/-- **At every level `w ≥ 64` the bracket of `digammaApprox` encloses `ψ(x)` strictly from below
or is rejected.** -/
theorem digammaApprox_valid_or_none {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {pos : Bool} (hpos : pos = true → 0 < xv) (hneg : pos = false → xv < 0 ∧ ∀ n : ℤ, xv ≠ n)
    (e : AzInt) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (digammaApprox x e pos w).1 lv ∧
        Rounds (digammaApprox x e pos w).2 hv ∧ lv ≤ DLMF.psiR xv ∧ DLMF.psiR xv ≤ hv ∧
        (lv = DLMF.psiR xv → hv = DLMF.psiR xv)) ∨
      roundingPossible (digammaApprox x e pos w).1 (digammaApprox x e pos w).2 p mode = none :=
  lnAbsGammaApproxOf_valid_or_none (fun _ hc => digammaEncl_spec hx hpos hneg e hw hc) w p mode

/-- **`ψ` is correctly rounded, or it is the loop with fuel** at a finite argument that is
not `0` or a pole. -/
theorem digammaPrecRoundFuel_eq_or_loop (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    digammaPrecRoundFuel fuel x p mode = liftVal Spec.digamma x p mode ∨
      ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite s e q m hv ∧ (s = true → 0 < finiteVal s e m) ∧
        (s = false → finiteVal s e m < 0 ∧ ∀ n : ℤ, finiteVal s e m ≠ n) ∧
        digammaPrecRoundFuel fuel x p mode
          = zivLoop (digammaApprox (finite s e q m hv) e s) p mode fuel (digammaStart e p) := by
  have hp := NeZero.ne p
  cases x with
  | nan => left; simp [digammaPrecRoundFuel, liftVal, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [digammaPrecRoundFuel, liftVal, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, Spec.digamma_bot, roundVal_none]
    · simp only [digammaPrecRoundFuel, liftVal, toVal_infinity, ↓reduceIte, Option.bind_some,
        Spec.digamma_top, roundVal_top]
  | zero =>
    left
    simp only [digammaPrecRoundFuel, liftVal, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.digamma_zero, roundVal_bot]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
    simp only [digammaPrecRoundFuel, liftVal, toVal_finite, Option.bind_some]
    by_cases hpole : (!s && isInteger (finite s e q m hv)) = true
    · left
      rw [ite_eq_left hpole]
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hpole
      obtain ⟨hs, hi⟩ := hpole
      subst hs
      rw [Spec.digamma_coe_of_pole (finiteVal_false_neg e hv)
        ((isInteger_finite false e hv).mp hi), roundVal_none]
    · rw [ite_eq_right hpole, ite_eq_right hp]
      have hpos : s = true → 0 < finiteVal s e m := fun hs => by
        subst hs; exact finiteVal_true_pos e hv
      have hneg : s = false → finiteVal s e m < 0 ∧ ∀ n : ℤ, finiteVal s e m ≠ n := fun hs => by
        subst hs
        refine ⟨finiteVal_false_neg e hv, fun n hn => hpole ?_⟩
        rw [Bool.not_false, Bool.true_and]
        exact (isInteger_finite false e hv).mpr ⟨n, hn⟩
      have hnp : ¬ (finiteVal s e m < 0 ∧ ∃ k : ℤ, finiteVal s e m = k) := by
        rintro ⟨hlt, k, hk⟩
        cases s with
        | true => exact absurd (finiteVal_true_pos e hv) (not_lt.mpr hlt.le)
        | false => exact (hneg rfl).2 k hk
      rw [Spec.digamma_coe hx0 hnp]
      split
      · next r hT => left; exact digammaTiny?_eq hv p mode hT
      · exact Or.inr ⟨s, e, q, m, hv, rfl, hpos, hneg, rfl⟩

/-- **`ψ` is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem digammaPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    digammaPrecRoundFuel fuel x p mode = liftVal Spec.digamma x p mode ∨
      digammaPrecRoundFuel fuel x p mode = (nan, .eq) := by
  rcases digammaPrecRoundFuel_eq_or_loop fuel x p mode with
    h | ⟨s, e, q, m, hv, rfl, hpos, hneg, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (digammaPrecRoundFuel fuel (finite s e q m hv) p mode) (nan, .eq) with
      hz | hz
    · exact Or.inr hz
    · left
      have hx := toVal_finite s e q m hv
      have hnp : ¬ (finiteVal s e m < 0 ∧ ∃ k : ℤ, finiteVal s e m = k) := by
        rintro ⟨hlt, k, hk⟩
        cases s with
        | true => exact absurd (hpos rfl) (not_lt.mpr hlt.le)
        | false => exact (hneg rfl).2 k hk
      rw [h] at hz ⊢
      rw [liftVal, hx, Option.bind_some, Spec.digamma_coe (finiteVal_ne_zero s e hv) hnp]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => digammaApprox_valid_or_none hx hpos hneg e hw p mode)
        _ _ (le_max_left _ _) hz

/-- **`ψ` is correctly rounded, or the fuel ran out.** -/
theorem digammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    digammaPrecRound x p mode = liftVal Spec.digamma x p mode ∨
      digammaPrecRound x p mode = (nan, .eq) :=
  digammaPrecRoundFuel_eq_or (lnGammaFuel p) x p mode

/-- **The specification of `ψ`** (`ZivSpec`): sound at every fuel; complete in the limit of
the fuel wherever the value is no rounding boundary (the bracket converges,
`digammaApprox_bracketConv`); correct at every fuel where the value is not a real number
(`0`, the negative integers, the infinities).  No value of `ψ` at a float is known to be
irrational. -/
theorem digammaPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.digamma) digammaPrecRoundFuel
      {x | ∀ v : ℝ, x.toVal = some (v : EReal) → v = 0 ∨ (v < 0 ∧ ∃ k : ℤ, v = k)} ∅ where
  sound := fun fuel x p _ mode => digammaPrecRoundFuel_eq_or fuel x p mode
  complete := fun x p _ mode hB => by
    by_cases hgen : ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite s e q m hv ∧ (s = true → 0 < finiteVal s e m) ∧
        (s = false → finiteVal s e m < 0 ∧ ∀ n : ℤ, finiteVal s e m ≠ n)
    · obtain ⟨s, e, q, m, hv, rfl, hpos, hneg⟩ := hgen
      have hx := toVal_finite s e q m hv
      have hnp : ¬ (finiteVal s e m < 0 ∧ ∃ k : ℤ, finiteVal s e m = k) := by
        rintro ⟨hlt, k, hk⟩
        cases s with
        | true => exact absurd (hpos rfl) (not_lt.mpr hlt.le)
        | false => exact (hneg rfl).2 k hk
      have hval : ((finite s e q m hv).toVal.bind Spec.digamma)
          = some ((DLMF.psiR (finiteVal s e m) : ℝ) : EReal) := by
        rw [hx, Option.bind_some, Spec.digamma_coe (finiteVal_ne_zero s e hv) hnp]
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (digammaApprox (finite s e q m hv) e s)
        (digammaApprox_bracketConv hx hpos hneg e)
        (ne_zero_of_not_mem_floatSet hB') hB' (digammaStart e p)
        (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _))
        (fun w hw => (digammaApprox_valid_or_none hx hpos hneg e
          (le_trans (le_max_left _ _) hw) p mode).imp_left
            fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases digammaPrecRoundFuel_eq_or_loop fuel (finite s e q m hv) p mode with
        h | ⟨s', e', q', m', hv', heq, -, -, h⟩
      · exact h
      · rw [h, hval]
        cases heq
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases digammaPrecRoundFuel_eq_or_loop fuel x p mode with
        h | ⟨s, e, q, m, hv, heq, hpos, hneg, -⟩
      · exact h
      · exact absurd ⟨s, e, q, m, hv, heq, hpos, hneg⟩ hgen
  dyadic := fun x hx v hv => by
    exfalso
    cases hxv : x.toVal with
    | none => rw [hxv] at hv; exact absurd hv (by simp)
    | some a =>
      rw [hxv, Option.bind_some] at hv
      induction a using EReal.rec with
      | bot => rw [Spec.digamma_bot] at hv; exact absurd hv (by simp)
      | top =>
        rw [Spec.digamma_top, Option.some.injEq] at hv
        exact EReal.coe_ne_top v hv.symm
      | coe t =>
        rcases hx t hxv with rfl | ⟨h0, hk⟩
        · rw [Spec.digamma_zero, Option.some.injEq] at hv
          exact EReal.coe_ne_bot v hv.symm
        · rw [Spec.digamma_coe_of_pole h0 hk] at hv
          exact absurd hv (by simp)
  nondyadic := fun x h => absurd h (Set.notMem_empty _)
  correct := fun x hx fuel p _ mode => by
    rcases digammaPrecRoundFuel_eq_or_loop fuel x p mode with
      h | ⟨s, e, q, m, hv, rfl, hpos, hneg, -⟩
    · exact h
    · exfalso
      rcases hx with hD | hN
      · rcases hD _ (toVal_finite s e q m hv) with h0 | ⟨hlt, k, hk⟩
        · exact finiteVal_ne_zero s e hv h0
        · cases s with
          | true => exact absurd (hpos rfl) (not_lt.mpr hlt.le)
          | false => exact (hneg rfl).2 k hk
      · exact absurd hN (Set.notMem_empty _)

end Azurite.AzFloat
