/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnQGamma
import Azurite.AzFloat.Equiv.QGamma
import Azurite.AzFloat.Equiv.LnGamma
import Azurite.AzFloat.Equiv.LnGammaRat
import Azurite.AzFloat.Equiv.LnRat

/-!
# Equivalence: `ln |Γ_q|` and `ln Γ_q`

`Spec.lnAbsQGamma`, `Spec.lnQGamma` and the specifications of the eight functions of
`AzFloat/LnQGamma.lean`:

* **`lnAbsQGammaPrecRoundFuel_zivSpec`**, **`lnAbsQGammaFloatRatPrecRoundFuel_zivSpec`**,
  **`lnAbsQGammaRatFloatPrecRoundFuel_zivSpec`**, **`lnAbsQGammaRatPrecRoundFuel_zivSpec`**
  (the value component), with the sign theorems `…_sign`;
* **`lnQGammaPrecRoundFuel_zivSpec`**, **`lnQGammaFloatRatPrecRoundFuel_zivSpec`**,
  **`lnQGammaRatFloatPrecRoundFuel_zivSpec`**, **`lnQGammaRatPrecRoundFuel_zivSpec`**.

Each is sound at every fuel and complete in the limit of the fuel wherever the value is no
rounding boundary.  Correct at every fuel: on the trivial class, at `0`, the poles and
`n = 1, 2` (the dyadic set: the values are `+∞` and `0`), and **at the positive integers
`n ≥ 3` whose value is formed** (the non-dyadic set: `ln` of a rational `≠ 1` is irrational) —
in every base, rational or float.

The four `lnAbs` specifications are instances of `lnAbsQGamma_zivSpec_sides`, itself an
instance of `qBaseLift_zivSpec` (a function of a base and an argument that is `NaN` on a bad
base, another function at the base `1`, and given on the real class).  The `ln`
specifications follow by `ZivSpec.restrict` (`NaN` on the negative arguments) from
`Spec.lnQGamma_eq`.
-/

namespace Azurite.AzFloat

open Finset DLMF

namespace Spec

open Classical in
/-- A function of a base `q` on the extended reals and an argument: undefined for a base
`q ≤ 0` or `q = +∞`, `vΓ` at `q = 1`, and `vAt q` elsewhere. -/
noncomputable def qBaseLift {X : Type*} (vΓ : X → Option EReal) (vAt : ℝ → X → Option EReal)
    (q : EReal) (x : X) : Option EReal :=
  if q ≤ 0 ∨ q = ⊤ then none else if q = 1 then vΓ x else vAt q.toReal x

variable {X : Type*} {vΓ : X → Option EReal} {vAt : ℝ → X → Option EReal}

theorem qBaseLift_none {q : EReal} (hq : q ≤ 0 ∨ q = ⊤) (x : X) :
    qBaseLift vΓ vAt q x = none := by
  unfold qBaseLift
  rw [ite_eq_left hq]

theorem qBaseLift_one (x : X) : qBaseLift vΓ vAt 1 x = vΓ x := by
  unfold qBaseLift
  rw [ite_eq_right (by
      rintro (h | h)
      · have : (1 : ℝ) ≤ 0 := by exact_mod_cast h
        linarith
      · exact EReal.coe_ne_top 1 (by exact_mod_cast h)), ite_eq_left rfl]

theorem qBaseLift_coe {qv : ℝ} (hq0 : 0 < qv) (hq1 : qv ≠ 1) (x : X) :
    qBaseLift vΓ vAt (qv : EReal) x = vAt qv x := by
  unfold qBaseLift
  rw [ite_eq_right (by
      rintro (h | h)
      · have : qv ≤ 0 := by exact_mod_cast h
        linarith
      · exact EReal.coe_ne_top _ h),
    ite_eq_right (by
      intro h
      exact hq1 (by exact_mod_cast h)), EReal.toReal_coe]

open Classical in
/-- `ln |Γ_q|` for a real base `q > 0`, `q ≠ 1`, on the extended reals: `+∞` at `±∞` and at
the poles `0, −1, −2, …`. -/
noncomputable def lnAbsQGammaAt (qv : ℝ) (x : EReal) : Option EReal :=
  if x = ⊤ ∨ x = ⊥ then some ⊤
  else if x.toReal ≤ 0 ∧ ∃ k : ℤ, x.toReal = k then some ⊤
  else some ((Real.log |qGammaReal qv x.toReal| : ℝ) : EReal)

/-- **`ln |Γ_q(x)|` on the extended reals**: undefined for a base `q ≤ 0` or `q = +∞`,
`ln |Γ(x)|` at `q = 1`. -/
noncomputable def lnAbsQGamma (q x : EReal) : Option EReal :=
  qBaseLift lnAbsGamma lnAbsQGammaAt q x

open Classical in
/-- `ln Γ_q` for a real base `q > 0`, `q ≠ 1`, on the extended reals: undefined for `x < 0`,
`+∞` at `0` and at `+∞`. -/
noncomputable def lnQGammaAt (qv : ℝ) (x : EReal) : Option EReal :=
  if x = ⊤ then some ⊤ else if x < 0 then none else if x = 0 then some ⊤
  else some ((Real.log (qGammaReal qv x.toReal) : ℝ) : EReal)

/-- **`ln Γ_q(x)` on the extended reals**: undefined for a base `q ≤ 0` or `q = +∞` and for
`x < 0`, `ln Γ(x)` at `q = 1`. -/
noncomputable def lnQGamma (q x : EReal) : Option EReal := qBaseLift lnGamma lnQGammaAt q x

theorem lnAbsQGammaAt_top (qv : ℝ) : lnAbsQGammaAt qv ⊤ = some ⊤ := by simp [lnAbsQGammaAt]

theorem lnAbsQGammaAt_bot (qv : ℝ) : lnAbsQGammaAt qv ⊥ = some ⊤ := by simp [lnAbsQGammaAt]

theorem lnAbsQGammaAt_coe_of_pole (qv : ℝ) {xv : ℝ} (h : xv ≤ 0) (hk : ∃ k : ℤ, xv = k) :
    lnAbsQGammaAt qv (xv : EReal) = some ⊤ := by
  unfold lnAbsQGammaAt
  rw [ite_eq_right (by simp), EReal.toReal_coe, ite_eq_left ⟨h, hk⟩]

theorem lnAbsQGammaAt_coe (qv : ℝ) {xv : ℝ} (h : ¬ (xv ≤ 0 ∧ ∃ k : ℤ, xv = k)) :
    lnAbsQGammaAt qv (xv : EReal) = some ((Real.log |qGammaReal qv xv| : ℝ) : EReal) := by
  unfold lnAbsQGammaAt
  rw [ite_eq_right (by simp), EReal.toReal_coe, ite_eq_right h]

/-- The value of `ln |Γ_q|` at an argument that is no real is no real. -/
theorem lnAbsQGammaAt_nonreal (qv : ℝ) (x : EReal) (hx : ∀ xv : ℝ, x ≠ (xv : EReal)) (v : ℝ) :
    lnAbsQGammaAt qv x ≠ some (v : EReal) := by
  induction x using EReal.rec with
  | bot => rw [lnAbsQGammaAt_bot]; simp
  | top => rw [lnAbsQGammaAt_top]; simp
  | coe r => exact absurd rfl (hx r)

/-- `ln Γ_q` is `ln |Γ_q|` off the negative arguments. -/
theorem lnQGammaAt_eq (qv : ℝ) (x : EReal) :
    lnQGammaAt qv x = if x < 0 then none else lnAbsQGammaAt qv x := by
  induction x using EReal.rec with
  | bot =>
    unfold lnQGammaAt
    rw [ite_eq_right bot_ne_top, ite_eq_left EReal.bot_lt_zero, ite_eq_left EReal.bot_lt_zero]
  | top =>
    unfold lnQGammaAt
    rw [ite_eq_left rfl, ite_eq_right (not_lt.mpr le_top), lnAbsQGammaAt_top]
  | coe r =>
    unfold lnQGammaAt
    rw [ite_eq_right (EReal.coe_ne_top _)]
    rcases lt_trichotomy r 0 with h | h | h
    · have h' : (r : EReal) < 0 := by exact_mod_cast h
      rw [ite_eq_left h', ite_eq_left h']
    · subst h
      have h' : ¬ ((0 : ℝ) : EReal) < 0 := by simp
      rw [ite_eq_right h', ite_eq_left (by simp), ite_eq_right h',
        lnAbsQGammaAt_coe_of_pole qv le_rfl ⟨0, by simp⟩]
    · have h' : ¬ (r : EReal) < 0 := not_lt.mpr (by exact_mod_cast h.le)
      rw [ite_eq_right h', ite_eq_right (by exact_mod_cast h.ne'), ite_eq_right h',
        EReal.toReal_coe, lnAbsQGammaAt_coe qv (fun hc => absurd hc.1 (not_le.mpr h)),
        Real.log_abs]

/-- `ln Γ` is `ln |Γ|` off the negative arguments. -/
theorem lnGamma_eq (x : EReal) : lnGamma x = if x < 0 then none else lnAbsGamma x := by
  induction x using EReal.rec with
  | bot => rw [lnGamma_bot, ite_eq_left EReal.bot_lt_zero]
  | top => rw [lnGamma_top, ite_eq_right (not_lt.mpr le_top), lnAbsGamma_top]
  | coe r =>
    rcases lt_trichotomy r 0 with h | h | h
    · rw [lnGamma_coe_of_neg h, ite_eq_left (by exact_mod_cast h)]
    · subst h
      rw [ite_eq_right (by simp), lnAbsGamma_coe_of_pole le_rfl ⟨0, by simp⟩, EReal.coe_zero,
        lnGamma_zero]
    · rw [ite_eq_right (not_lt.mpr (by exact_mod_cast h.le)), lnAbsGamma_coe_of_pos h]

/-- **`ln Γ_q` is `ln |Γ_q|` off the negative arguments**, in every base. -/
theorem lnQGamma_eq (q x : EReal) :
    lnQGamma q x = if x < 0 then none else lnAbsQGamma q x := by
  unfold lnQGamma lnAbsQGamma
  by_cases hb : q ≤ 0 ∨ q = ⊤
  · rw [qBaseLift_none hb, qBaseLift_none hb]
    split_ifs <;> rfl
  · by_cases h1 : q = 1
    · rw [h1, qBaseLift_one, qBaseLift_one, lnGamma_eq]
    · induction q using EReal.rec with
      | bot => exact absurd (Or.inl bot_le) hb
      | top => exact absurd (Or.inr rfl) hb
      | coe r =>
        have h0 : 0 < r := by
          by_contra h
          exact hb (Or.inl (by exact_mod_cast not_lt.mp h))
        have hr1 : r ≠ 1 := fun h => h1 (by rw [h]; rfl)
        rw [qBaseLift_coe h0 hr1, qBaseLift_coe h0 hr1, lnQGammaAt_eq]

end Spec

/-! ### A function of a base and an argument -/

open Classical in
/-- **The specification of a function `f` of a base and an argument** with values `qe`, `xe`
in the extended reals: `NaN` on a base that is no positive real, the function `fΓ` at the base
`1`, the function `g` on the real class (a base `q > 0`, `q ≠ 1`, and a real argument), and
the rounding of the value at an argument that is no real.  `D` and `N` are the arguments of
the real class where `g` is known to be exact with dyadic and non-dyadic values. -/
theorem qBaseLift_zivSpec {α : Type*} {qe xe : α → Option EReal}
    {f fΓ g : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering}
    {vΓ : EReal → Option EReal} {vAt : ℝ → EReal → Option EReal} (D N : Set α)
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode = roundVal p mode ((xe a).bind vΓ) ∨ fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, (xe a).bind vΓ = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → fΓ fuel a p mode = roundVal p mode ((xe a).bind vΓ))
    (hgs : ∀ a (qv xv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) → ∀ fuel (p : ℕ) [NeZero p] mode,
      g fuel a p mode = roundVal p mode (vAt qv (xv : EReal)) ∨ g fuel a p mode = (nan, .eq))
    (hgc : ∀ a (qv xv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) → ∀ (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, vAt qv (xv : EReal) = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → g fuel a p mode = roundVal p mode (vAt qv (xv : EReal)))
    (hD : ∀ a ∈ D, ∀ qv xv : ℝ, qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) →
      (∀ v : ℝ, vAt qv (xv : EReal) = some (v : EReal) → IsDyadic v) ∧
        ∀ fuel (p : ℕ) [NeZero p] mode, g fuel a p mode = roundVal p mode (vAt qv (xv : EReal)))
    (hN : ∀ a ∈ N, ∀ qv xv : ℝ, qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) →
      (∃ v : ℝ, vAt qv (xv : EReal) = some (v : EReal) ∧ ¬ IsDyadic v) ∧
        ∀ fuel (p : ℕ) [NeZero p] mode, g fuel a p mode = roundVal p mode (vAt qv (xv : EReal)))
    (hvn : ∀ (qv : ℝ) (x : EReal), (∀ xv : ℝ, x ≠ (xv : EReal)) → ∀ v : ℝ,
      vAt qv x ≠ some (v : EReal))
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv xv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) → f fuel a p mode = g fuel a p mode)
    (hf_nonreal : ∀ fuel a (p : ℕ) [NeZero p] mode (qv : ℝ), qe a = some (qv : EReal) →
      0 < qv → qv ≠ 1 → (∀ xv : ℝ, xe a ≠ some (xv : EReal)) →
      f fuel a p mode = roundVal p mode ((xe a).bind (vAt qv))) :
    ZivSpec (fun a => (qe a).bind fun q => (xe a).bind fun x => Spec.qBaseLift vΓ vAt q x) f
      {a | QTrivial qe xe a ∨ (QReal qe xe a ∧ a ∈ D)} {a | QReal qe xe a ∧ a ∈ N} := by
  have hval_bad : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      ((qe a).bind fun q => (xe a).bind fun x => Spec.qBaseLift vΓ vAt q x) = none := by
    intro a hb
    cases hq : qe a with
    | none => rfl
    | some e =>
      rw [Option.bind_some]
      have hn : e ≤ 0 ∨ e = ⊤ := by
        induction e using EReal.rec with
        | bot => exact Or.inl bot_le
        | top => exact Or.inr rfl
        | coe r => exact Or.inl (by exact_mod_cast hb r hq)
      simp only [Spec.qBaseLift_none hn]
      exact bind_const_none _
  have hval_one : ∀ a, qe a = some ((1 : ℝ) : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => Spec.qBaseLift vΓ vAt q x)
        = (xe a).bind vΓ := by
    intro a hq
    rw [hq, Option.bind_some]
    congr 1
    funext x
    rw [EReal.coe_one, Spec.qBaseLift_one]
  have hval_pos : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      ((qe a).bind fun q => (xe a).bind fun x => Spec.qBaseLift vΓ vAt q x)
        = (xe a).bind (vAt qv) := by
    intro a qv hq h0 h1
    rw [hq, Option.bind_some]
    congr 1
    funext x
    exact Spec.qBaseLift_coe h0 h1 x
  have hval_real : ∀ a (qv xv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => Spec.qBaseLift vΓ vAt q x)
        = vAt qv (xv : EReal) := by
    intro a qv xv hq h0 h1 hx
    rw [hval_pos a qv hq h0 h1, hx, Option.bind_some]
  have hnr : ∀ a (qv : ℝ), (∀ xv : ℝ, xe a ≠ some (xv : EReal)) → ∀ v : ℝ,
      (xe a).bind (vAt qv) ≠ some (v : EReal) := by
    intro a qv hx v hv
    cases hxe : xe a with
    | none =>
      rw [hxe] at hv
      exact absurd hv (by simp)
    | some e =>
      rw [hxe, Option.bind_some] at hv
      exact hvn qv e (fun xv he => hx xv (by rw [hxe, he])) v hv
  have hcases : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) ∨
      qe a = some ((1 : ℝ) : EReal) ∨
      ∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1 ∧
        ((∃ xv : ℝ, xe a = some (xv : EReal)) ∨ ∀ xv : ℝ, xe a ≠ some (xv : EReal)) := by
    intro a
    by_cases hb : ∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0
    · exact Or.inl hb
    · push Not at hb
      obtain ⟨qv, hq, h0⟩ := hb
      by_cases h1 : qv = 1
      · exact Or.inr (Or.inl (h1 ▸ hq))
      · by_cases hx : ∃ xv : ℝ, xe a = some (xv : EReal)
        · exact Or.inr (Or.inr ⟨qv, hq, h0, h1, Or.inl hx⟩)
        · exact Or.inr (Or.inr ⟨qv, hq, h0, h1, Or.inr fun xv h => hx ⟨xv, h⟩⟩)
  refine ⟨fun fuel a p _ mode => ?_, fun a p _ mode hB => ?_, fun a ha v hv => ?_,
    fun a ha => ?_, fun a ha fuel p _ mode => ?_⟩
  · rcases hcases a with hb | h1 | ⟨qv, hq, h0, h1, ⟨xv, hx⟩ | hx⟩
    · left
      rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]
    · rw [hf_one fuel a p mode h1, hval_one a h1]
      exact hΓs fuel a p mode
    · rw [hf_real fuel a p mode qv xv hq h0 h1 hx, hval_real a qv xv hq h0 h1 hx]
      exact hgs a qv xv hq h0 h1 hx fuel p mode
    · left
      rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]
  · rcases hcases a with hb | h1 | ⟨qv, hq, h0, h1, ⟨xv, hx⟩ | hx⟩
    · exact ⟨0, fun fuel _ => by rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]⟩
    · rw [hval_one a h1] at hB ⊢
      obtain ⟨F, hF⟩ := hΓc a p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hf_one fuel a p mode h1]; exact hF fuel hfuel⟩
    · rw [hval_real a qv xv hq h0 h1 hx] at hB ⊢
      obtain ⟨F, hF⟩ := hgc a qv xv hq h0 h1 hx p mode hB
      exact ⟨F, fun fuel hfuel => by
        rw [hf_real fuel a p mode qv xv hq h0 h1 hx]; exact hF fuel hfuel⟩
    · exact ⟨0, fun fuel _ => by
        rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]⟩
  · rcases ha with (hb | ⟨⟨qv, hq, h0, h1⟩, hx⟩) | ⟨⟨qv, xv, hq, h0, h1, hx⟩, hD'⟩
    · rw [hval_bad a hb] at hv
      exact absurd hv (by simp)
    · rw [hval_pos a qv hq h0 h1] at hv
      exact absurd hv (hnr a qv hx v)
    · rw [hval_real a qv xv hq h0 h1 hx] at hv
      exact (hD a hD' qv xv hq h0 h1 hx).1 v hv
  · obtain ⟨⟨qv, xv, hq, h0, h1, hx⟩, hN'⟩ := ha
    rw [hval_real a qv xv hq h0 h1 hx]
    exact (hN a hN' qv xv hq h0 h1 hx).1
  · rcases ha with ((hb | ⟨⟨qv, hq, h0, h1⟩, hx⟩) | ⟨⟨qv, xv, hq, h0, h1, hx⟩, hD'⟩) |
      ⟨⟨qv, xv, hq, h0, h1, hx⟩, hN'⟩
    · rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]
    · rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]
    · rw [hf_real fuel a p mode qv xv hq h0 h1 hx, hval_real a qv xv hq h0 h1 hx]
      exact (hD a hD' qv xv hq h0 h1 hx).2 fuel p mode
    · rw [hf_real fuel a p mode qv xv hq h0 h1 hx, hval_real a qv xv hq h0 h1 hx]
      exact (hN a hN' qv xv hq h0 h1 hx).2 fuel p mode

/-- **A specification restricted**: `NaN` on the arguments with `neg`, where the value is set
undefined. -/
theorem ZivSpec.restrict {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} {D N : Set α} (h : ZivSpec val f D N)
    (neg : α → Prop) [DecidablePred neg] :
    ZivSpec (fun a => if neg a then none else val a)
      (fun fuel a p mode => if neg a then (nan, .eq) else f fuel a p mode)
      {a | neg a ∨ a ∈ D} {a | ¬ neg a ∧ a ∈ N} where
  sound := fun fuel a p _ mode => by
    by_cases hn : neg a
    · left
      show (if neg a then _ else _) = roundVal p mode (if neg a then _ else _)
      rw [ite_eq_left hn, ite_eq_left hn, roundVal_none]
    · show (if neg a then _ else _) = roundVal p mode (if neg a then _ else _) ∨
        (if neg a then _ else _) = _
      rw [ite_eq_right hn, ite_eq_right hn]
      exact h.sound fuel a p mode
  complete := fun a p _ mode hB => by
    by_cases hn : neg a
    · refine ⟨0, fun fuel _ => ?_⟩
      show (if neg a then _ else _) = roundVal p mode (if neg a then _ else _)
      rw [ite_eq_left hn, ite_eq_left hn, roundVal_none]
    · have hB' : ∀ v : ℝ, val a = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1) :=
        fun v hv => hB v (by
          show (if neg a then _ else _) = _
          rw [ite_eq_right hn, hv])
      obtain ⟨F, hF⟩ := h.complete a p mode hB'
      refine ⟨F, fun fuel hfuel => ?_⟩
      show (if neg a then _ else _) = roundVal p mode (if neg a then _ else _)
      rw [ite_eq_right hn, ite_eq_right hn]
      exact hF fuel hfuel
  dyadic := fun a ha v hv => by
    have hv' : (if neg a then none else val a) = some (v : EReal) := hv
    by_cases hn : neg a
    · rw [ite_eq_left hn] at hv'
      exact absurd hv' (by simp)
    · rw [ite_eq_right hn] at hv'
      rcases ha with ha | ha
      · exact absurd ha hn
      · exact h.dyadic a ha v hv'
  nondyadic := fun a ha => by
    obtain ⟨hn, hN⟩ := ha
    obtain ⟨v, hv, hd⟩ := h.nondyadic a hN
    refine ⟨v, ?_, hd⟩
    show (if neg a then _ else _) = _
    rw [ite_eq_right hn, hv]
  correct := fun a ha fuel p _ mode => by
    show (if neg a then _ else _) = roundVal p mode (if neg a then _ else _)
    by_cases hn : neg a
    · rw [ite_eq_left hn, ite_eq_left hn, roundVal_none]
    · rw [ite_eq_right hn, ite_eq_right hn]
      rcases ha with (ha | ha) | ha
      · exact absurd ha hn
      · exact h.correct a (Or.inl ha) fuel p mode
      · exact h.correct a (Or.inr ha.2) fuel p mode

/-! ### `ln |Γ_q|` on a base and an argument -/

variable {Q : QBase} {S : QArg} {qv xv : ℝ}

/-- An argument that is no `−m` is no pole. -/
theorem not_pole_of_ne_neg_nat {xv : ℝ} (hnz : ∀ m : ℕ, xv ≠ -m) :
    ¬ (xv ≤ 0 ∧ ∃ k : ℤ, xv = k) := by
  rintro ⟨hle, k, hk⟩
  have hk0 : k ≤ 0 := by exact_mod_cast (hk ▸ hle : (k : ℝ) ≤ 0)
  refine hnz (-k).toNat ?_
  have : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  have h2 : (((-k).toNat : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by rw [this]
  push_cast at h2
  rw [hk]
  linarith

theorem lnAbsQGammaAt_of_ne (qv : ℝ) {xv : ℝ} (hnz : ∀ m : ℕ, xv ≠ -m) :
    Spec.lnAbsQGammaAt qv (xv : EReal)
      = some ((Real.log |qGammaReal qv xv| : ℝ) : EReal) :=
  Spec.lnAbsQGammaAt_coe qv (not_pole_of_ne_neg_nat hnz)

theorem posInt_ne_neg_nat {n : ℕ} (hn1 : 1 ≤ n) {xv : ℝ} (hxn : xv = n) (m : ℕ) :
    xv ≠ -m := fun h => by
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [hxn] at h
  linarith

/-- The enclosure of the bracket in terms of `Γ_q(x)`. -/
theorem qGammaLnEnclOf_real_spec (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) {w : ℕ}
    {neg : Bool} {L : Encl} (hc : qGammaLnEnclOf (qGammaInOf Q S) w = some (neg, L)) :
    0 < (if neg then (-1 : ℝ) else 1) * qGammaReal qv xv ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * qGammaReal qv xv)) := by
  have := qGammaLnEnclOf_spec (qGammaArg_of hQ hS) hc
  rwa [qGammaVal_of hQ] at this

/-- The logarithm of an exact value is the value of `ln |Γ_q|`. -/
theorem lnRat_qGammaExact (hQ : QBaseSpec Q qv) {n p : ℕ} [NeZero p] {r : AzRat} (hn1 : 1 ≤ n)
    (hxn : xv = n) (hex : qGammaExact? Q n p = some r) (mode : RoundingMode) :
    lnRatPrecRound r p mode = roundVal p mode (Spec.lnAbsQGammaAt qv (xv : EReal)) := by
  have hpos : 0 < qGammaReal qv (n : ℝ) := qGammaReal_pos hQ.pos (by exact_mod_cast hn1)
  rw [lnRatPrecRound_eq, qGammaExact?_spec hQ hn1 hex, Spec.log_coe _ hpos,
    lnAbsQGammaAt_of_ne qv (posInt_ne_neg_nat hn1 hxn), hxn, abs_of_pos hpos]

/-- **`ln |Γ_q|` on a base and an argument is correctly rounded with the sign `true`
(and `Γ_q(x) > 0` off the poles), or it is the loop** off the poles. -/
theorem lnAbsQGammaOf_eq_or_loop (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (fuel p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (lnAbsQGammaOf Q S fuel p mode
        = (roundVal p mode (Spec.lnAbsQGammaAt qv (xv : EReal)), true) ∧
        ((∀ m : ℕ, xv ≠ -m) → 0 < qGammaReal qv xv)) ∨
      ((∀ m : ℕ, xv ≠ -m) ∧ lnAbsQGammaOf Q S fuel p mode
        = lnAbsLoop (qGammaLnEnclOf (qGammaInOf Q S)) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  have hk := hS.kind
  unfold lnAbsQGammaOf
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    left
    have h0 : xv = 0 := hk
    dsimp only
    rw [h0, Spec.lnAbsQGammaAt_coe_of_pole qv le_rfl ⟨0, by simp⟩, roundVal_top]
    exact ⟨rfl, fun hnz => absurd (by simp) (hnz 0)⟩
  | pole =>
    rw [hkind] at hk
    left
    obtain ⟨m, hm⟩ := hk
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    dsimp only
    rw [hm, Spec.lnAbsQGammaAt_coe_of_pole qv (by linarith)
      ⟨-((m : ℤ) + 1), by push_cast; ring⟩, roundVal_top]
    exact ⟨rfl, fun hnz => absurd (by push_cast; ring) (hnz (m + 1))⟩
  | posInt n =>
    rw [hkind] at hk
    obtain ⟨hn1, hxn⟩ := hk
    have hnz := posInt_ne_neg_nat hn1 hxn
    dsimp only
    rw [ite_eq_right hp]
    cases hex : qGammaExact? Q n p with
    | none => exact Or.inr ⟨hnz, rfl⟩
    | some r =>
      left
      dsimp only
      rw [lnRat_qGammaExact hQ hn1 hxn hex]
      refine ⟨rfl, fun _ => ?_⟩
      rw [hxn]
      exact qGammaReal_pos hQ.pos (by exact_mod_cast hn1)
  | general =>
    rw [hkind] at hk
    dsimp only
    rw [ite_eq_right hp]
    exact Or.inr ⟨hk, rfl⟩

/-- **`ln |Γ_q|` with the sign**: `NaN`, or the rounding of `ln |Γ_q(x)|` with, off the
poles, `Γ_q(x) > 0` as the sign. -/
theorem lnAbsQGammaOf_main (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQGammaOf Q S fuel p mode).1 = (nan, .eq) ∨
      ((lnAbsQGammaOf Q S fuel p mode).1
          = roundVal p mode (Spec.lnAbsQGammaAt qv (xv : EReal)) ∧
        ((∀ m : ℕ, xv ≠ -m) →
          ((lnAbsQGammaOf Q S fuel p mode).2 = true ↔ 0 < qGammaReal qv xv))) := by
  rcases lnAbsQGammaOf_eq_or_loop hQ hS fuel p mode with ⟨h, hpos⟩ | ⟨hnz, h⟩
  · right
    rw [h]
    exact ⟨rfl, fun hnz => ⟨fun _ => hpos hnz, fun _ => rfl⟩⟩
  · rw [h, lnAbsQGammaAt_of_ne qv hnz]
    rcases lnAbsLoop_spec (v := qGammaReal qv xv) (w₀ := 64)
      (fun w _ neg L hc => qGammaLnEnclOf_real_spec hQ hS hc) p mode fuel _
      (le_max_left _ _) with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, fun _ => h2⟩

/-- **`ln |Γ_q|` is correctly rounded for every large enough fuel** where the value is no
rounding boundary. -/
theorem lnAbsQGammaOf_complete (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (p : ℕ) [NeZero p]
    (mode : RoundingMode)
    (hB : ∀ v : ℝ, Spec.lnAbsQGammaAt qv (xv : EReal) = some (v : EReal) →
      ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → (lnAbsQGammaOf Q S fuel p mode).1
      = roundVal p mode (Spec.lnAbsQGammaAt qv (xv : EReal)) := by
  by_cases hnz : ∀ m : ℕ, xv ≠ -m
  · have hB' := hB _ (lnAbsQGammaAt_of_ne qv hnz)
    have hconv := qGammaLnEnclOf_conv (qGammaArg_of hQ hS) hnz
    rw [qGammaVal_of hQ] at hconv
    obtain ⟨F, hF⟩ := lnAbsLoop_eventually (v := Real.log |qGammaReal qv xv|) p mode
      (core := qGammaLnEnclOf (qGammaInOf Q S)) (w₀ := max 64 (p + 32)) (by omega)
      (fun w hw neg L hc => by
        obtain ⟨hpos, hL⟩ := qGammaLnEnclOf_real_spec hQ hS hc
        rwa [sign_mul_eq_abs hpos] at hL)
      hconv hB'
    refine ⟨F, fun fuel hfuel => ?_⟩
    rcases lnAbsQGammaOf_eq_or_loop hQ hS fuel p mode with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h]
    · rw [h, lnAbsQGammaAt_of_ne qv hnz]
      exact hF fuel hfuel
  · refine ⟨0, fun fuel _ => ?_⟩
    rcases lnAbsQGammaOf_eq_or_loop hQ hS fuel p mode with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
    · exact absurd h hnz

/-- **On the exact class the result is correctly rounded at every fuel**, with the sign
`true`. -/
theorem lnAbsQGammaOf_exact (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (hE : QExact Q S)
    (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnAbsQGammaOf Q S fuel p mode
      = (roundVal p mode (Spec.lnAbsQGammaAt qv (xv : EReal)), true) := by
  rcases lnAbsQGammaOf_eq_or_loop hQ hS fuel p mode with ⟨h, -⟩ | ⟨-, -⟩
  · exact h
  · have hp := NeZero.ne p
    have hk := hS.kind
    unfold QExact at hE
    unfold lnAbsQGammaOf
    cases hkind : S.kind with
    | zero =>
      rw [hkind] at hk
      have h0 : xv = 0 := hk
      dsimp only
      rw [h0, Spec.lnAbsQGammaAt_coe_of_pole qv le_rfl ⟨0, by simp⟩, roundVal_top]
    | pole =>
      rw [hkind] at hk
      obtain ⟨m, hm⟩ := hk
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      dsimp only
      rw [hm, Spec.lnAbsQGammaAt_coe_of_pole qv (by linarith)
        ⟨-((m : ℤ) + 1), by push_cast; ring⟩, roundVal_top]
    | posInt n =>
      rw [hkind] at hk hE
      obtain ⟨hn1, hxn⟩ := hk
      dsimp only
      rw [ite_eq_right hp]
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (qGammaExact?_isSome_mono hE p)
      rw [hr]
      dsimp only
      rw [lnRat_qGammaExact hQ hn1 hxn hr]
    | general =>
      rw [hkind] at hE
      exact hE.elim

/-- **The sign component is the sign of `Γ_q(x)`** off the poles, whenever the value is not
`NaN`. -/
theorem lnAbsQGammaOf_sign (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (hnz : ∀ m : ℕ, xv ≠ -m)
    (fuel p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQGammaOf Q S fuel p mode).1 ≠ (nan, .eq)) :
    (lnAbsQGammaOf Q S fuel p mode).2 = true ↔ 0 < qGammaReal qv xv := by
  rcases lnAbsQGammaOf_main hQ hS fuel p mode with h | h
  · exact absurd h hne
  · exact h.2 hnz

/-! ### The classes of exact values -/

/-- The class with the values `+∞` and `0`: `0`, a pole, `1` or `2`. -/
def QLnZero (S : QArg) : Prop :=
  match S.kind with
  | .zero => True
  | .pole => True
  | .posInt n => n ≤ 2
  | .general => False

/-- The class with irrational values: a positive integer `n ≥ 3` whose value `Γ_q(n)` is
formed at every precision. -/
def QLnIrr (Q : QBase) (S : QArg) : Prop :=
  match S.kind with
  | .zero => False
  | .pole => False
  | .posInt n => 3 ≤ n ∧ (qGammaExact? Q n 0).isSome = true
  | .general => False

theorem QLnZero.qExact (h : QLnZero S) : QExact Q S := by
  unfold QLnZero at h
  unfold QExact
  cases hkind : S.kind with
  | zero => trivial
  | pole => trivial
  | posInt n =>
    rw [hkind] at h
    have h2 : n ≤ 2 := h
    show (qGammaExact? Q n 0).isSome = true
    unfold qGammaExact?
    rw [ite_eq_left h2]
    rfl
  | general =>
    rw [hkind] at h
    exact h.elim

theorem QLnIrr.qExact (h : QLnIrr Q S) : QExact Q S := by
  unfold QLnIrr at h
  unfold QExact
  cases hkind : S.kind with
  | zero => trivial
  | pole => trivial
  | posInt n =>
    rw [hkind] at h
    exact h.2
  | general =>
    rw [hkind] at h
    exact h.elim

/-- On the class `QLnZero` the real values are `0`. -/
theorem isDyadic_of_qLnZero (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (h : QLnZero S) {v : ℝ}
    (hv : Spec.lnAbsQGammaAt qv (xv : EReal) = some (v : EReal)) : IsDyadic v := by
  have hk := hS.kind
  unfold QLnZero at h
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    have h0 : xv = 0 := hk
    rw [h0, Spec.lnAbsQGammaAt_coe_of_pole qv le_rfl ⟨0, by simp⟩] at hv
    exact absurd hv (by simp)
  | pole =>
    rw [hkind] at hk
    obtain ⟨m, hm⟩ := hk
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hm, Spec.lnAbsQGammaAt_coe_of_pole qv (by linarith)
      ⟨-((m : ℤ) + 1), by push_cast; ring⟩] at hv
    exact absurd hv (by simp)
  | posInt n =>
    rw [hkind] at hk h
    obtain ⟨hn1, hxn⟩ := hk
    have h2 : n ≤ 2 := h
    have hex : qGammaExact? Q n 0 = some 1 := by
      unfold qGammaExact?
      rw [ite_eq_left h2]
    have hone := qGammaExact?_spec hQ hn1 hex
    rw [AzRat.toRat_one] at hone
    rw [lnAbsQGammaAt_of_ne qv (posInt_ne_neg_nat hn1 hxn), hxn, ← hone, Option.some.injEq,
      EReal.coe_eq_coe_iff] at hv
    rw [← hv]
    simpa using isDyadic_zero
  | general =>
    rw [hkind] at h
    exact h.elim

/-- **On the class `QLnIrr` the value is irrational**: the logarithm of a rational above
`1`. -/
theorem not_isDyadic_of_qLnIrr (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (h : QLnIrr Q S) :
    ∃ v : ℝ, Spec.lnAbsQGammaAt qv (xv : EReal) = some (v : EReal) ∧ ¬ IsDyadic v := by
  have hk := hS.kind
  unfold QLnIrr at h
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at h
    exact h.elim
  | pole =>
    rw [hkind] at h
    exact h.elim
  | posInt n =>
    rw [hkind] at hk h
    obtain ⟨hn1, hxn⟩ := hk
    obtain ⟨hn3, hsome⟩ : 3 ≤ n ∧ (qGammaExact? Q n 0).isSome = true := h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
    have hspec := qGammaExact?_spec hQ hn1 hr
    have hG := qGammaReal_nat hQ.pos hQ.ne_one (n - 1)
    have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    rw [hcast] at hG
    have hlt : 1 < qGammaReal qv (n : ℝ) := by
      rw [hG]
      exact one_lt_qFactorial hQ.pos (by omega)
    have hr1 : (1 : ℝ) < ((AzRat.toRat r : ℚ) : ℝ) := by rw [hspec]; exact hlt
    have hirr : Irrational (Real.log ((AzRat.toRat r : ℚ) : ℝ)) :=
      irrational_log_rat (by exact_mod_cast lt_trans one_pos hr1)
        (fun h1 => by
          rw [h1] at hr1
          norm_num at hr1)
    refine ⟨_, lnAbsQGammaAt_of_ne qv (posInt_ne_neg_nat hn1 hxn),
      not_isDyadic_of_irrational ?_⟩
    rw [hxn, abs_of_pos (lt_trans one_pos hlt), ← hspec]
    exact hirr
  | general =>
    rw [hkind] at h
    exact h.elim

/-- On the class `QLnIrr` the argument is positive. -/
theorem QLnIrr.pos (h : QLnIrr Q S) (hS : QArgSpec S xv) : 0 < xv := by
  have hk := hS.kind
  unfold QLnIrr at h
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at h
    exact h.elim
  | pole =>
    rw [hkind] at h
    exact h.elim
  | posInt n =>
    rw [hkind] at hk
    obtain ⟨hn1, hxn⟩ := hk
    rw [hxn]
    exact_mod_cast hn1
  | general =>
    rw [hkind] at h
    exact h.elim

/-! ### The specification, generically -/

/-- **The specification of a function that is `ln |Γ_q|`** on a base and an argument with
values `qe`, `xe` in the extended reals: `NaN` on a base that is no positive real, the function
`fΓ` (a function that is `ln |Γ|`) at the base `1`, the special values at an argument that is
no real, and `lnAbsQGammaOf` elsewhere. -/
theorem lnAbsQGamma_zivSpec_sides {α : Type*} {qe xe : α → Option EReal}
    {f fΓ : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (Q : α → QBase) (S : α → QArg)
    (hbase : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 → QBaseSpec (Q a) qv)
    (harg : ∀ a (xv : ℝ), xe a = some (xv : EReal) → QArgSpec (S a) xv)
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode = roundVal p mode ((xe a).bind Spec.lnAbsGamma) ∨
        fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, (xe a).bind Spec.lnAbsGamma = some (v : EReal) →
        ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel →
        fΓ fuel a p mode = roundVal p mode ((xe a).bind Spec.lnAbsGamma))
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv xv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) →
      f fuel a p mode = (lnAbsQGammaOf (Q a) (S a) fuel p mode).1)
    (hf_nonreal : ∀ fuel a (p : ℕ) [NeZero p] mode (qv : ℝ), qe a = some (qv : EReal) →
      0 < qv → qv ≠ 1 → (∀ xv : ℝ, xe a ≠ some (xv : EReal)) →
      f fuel a p mode = roundVal p mode ((xe a).bind (Spec.lnAbsQGammaAt qv))) :
    ZivSpec (fun a => (qe a).bind fun q => (xe a).bind fun x => Spec.lnAbsQGamma q x) f
      {a | QTrivial qe xe a ∨ (QReal qe xe a ∧ QLnZero (S a))}
      {a | QReal qe xe a ∧ QLnIrr (Q a) (S a)} :=
  qBaseLift_zivSpec (g := fun fuel a p mode => (lnAbsQGammaOf (Q a) (S a) fuel p mode).1)
    {a | QLnZero (S a)} {a | QLnIrr (Q a) (S a)} hΓs hΓc
    (fun a qv xv hq h0 h1 hx fuel p _ mode => by
      rcases lnAbsQGammaOf_main (hbase a qv hq h0 h1) (harg a xv hx) fuel p mode with h | h
      · exact Or.inr h
      · exact Or.inl h.1)
    (fun a qv xv hq h0 h1 hx p _ mode hB =>
      lnAbsQGammaOf_complete (hbase a qv hq h0 h1) (harg a xv hx) p mode hB)
    (fun a ha qv xv hq h0 h1 hx =>
      ⟨fun v hv => isDyadic_of_qLnZero (hbase a qv hq h0 h1) (harg a xv hx) ha hv,
        fun fuel p _ mode => by
          rw [lnAbsQGammaOf_exact (hbase a qv hq h0 h1) (harg a xv hx)
            (QLnZero.qExact ha) fuel p mode]⟩)
    (fun a ha qv xv hq h0 h1 hx =>
      ⟨not_isDyadic_of_qLnIrr (hbase a qv hq h0 h1) (harg a xv hx) ha,
        fun fuel p _ mode => by
          rw [lnAbsQGammaOf_exact (hbase a qv hq h0 h1) (harg a xv hx)
            (QLnIrr.qExact ha) fuel p mode]⟩)
    Spec.lnAbsQGammaAt_nonreal hf_bad hf_one hf_real hf_nonreal

/-! ### Negative arguments -/

/-- `lt x zero` is "the value is negative". -/
theorem bind_restrict_float (x : AzFloat) (F : EReal → Option EReal) :
    (x.toVal.bind fun e => if e < 0 then none else F e)
      = if lt x zero = true then none else x.toVal.bind F := by
  rcases exists_real_or_not x with ⟨xv, hx⟩ | rfl | rfl | rfl
  · rw [hx, Option.bind_some, Option.bind_some]
    by_cases h : xv < 0
    · rw [ite_eq_left (by exact_mod_cast h), ite_eq_left ((lt_eq_true_iff hx toVal_zero').mpr h)]
    · rw [ite_eq_right (not_lt.mpr (by exact_mod_cast not_lt.mp h)),
        ite_eq_right (mt (lt_eq_true_iff hx toVal_zero').mp h)]
  · rfl
  · have h : lt (infinity true) zero = false := by decide
    rw [h]
    simp
  · have h : lt (infinity false) zero = true := by decide
    rw [h]
    simp

/-- A rational is negative iff its sign is `false` and it is not `0`. -/
theorem ratIsNeg_iff (x : AzRat) : ratIsNeg x = true ↔ ((AzRat.toRat x : ℚ) : ℝ) < 0 := by
  have hden := den_pos_real x
  have hval := coe_toRat_eq_sign_mul x
  unfold ratIsNeg
  rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨hs, h0⟩
    have hn : (0 : ℝ) < x.num.toNat := by exact_mod_cast AzRat.num_toNat_pos x h0
    have hd := div_pos hn hden
    rw [hs] at hval
    simp only [Bool.false_eq_true, ↓reduceIte] at hval
    linarith
  · intro hneg
    refine ⟨?_, fun h0 => ?_⟩
    · by_contra hs
      have hs' : x.sign = true := by simpa using hs
      rw [hs'] at hval
      simp only [↓reduceIte, one_mul] at hval
      have hnn : (0 : ℝ) ≤ (x.num.toNat : ℝ) / x.den.toNat := by positivity
      linarith
    · have := coe_toRat_eq_zero_of_num_eq_zero x h0
      linarith

/-! ### The functions on the real class -/

theorem lnAbsQGammaPrecRoundFuel_eq_of (fuel : ℕ) {q x : AzFloat} {qv xv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    (hx : x.toVal = some (xv : EReal)) (p : ℕ) (mode : RoundingMode) :
    lnAbsQGammaPrecRoundFuel fuel q x p mode
      = lnAbsQGammaOf (qBaseFloat q) (qArgFloat x) fuel p mode := by
  have hne : (le q one && le one q) = false := by
    rw [← Bool.not_eq_true]
    exact mt (qFloatBase_one_iff hq).mp h1
  unfold lnAbsQGammaPrecRoundFuel
  rw [qFloatBase_pos hq h0, hne]
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero => rfl
  | finite s e pr m hv => rfl

theorem lnAbsQGammaFloatRatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1) (x : AzRat) (p : ℕ)
    (mode : RoundingMode) :
    lnAbsQGammaFloatRatPrecRoundFuel fuel q x p mode
      = lnAbsQGammaOf (qBaseFloat q) (qArgRat x) fuel p mode := by
  have hne : (le q one && le one q) = false := by
    rw [← Bool.not_eq_true]
    exact mt (qFloatBase_one_iff hq).mp h1
  unfold lnAbsQGammaFloatRatPrecRoundFuel
  rw [qFloatBase_pos hq h0, hne]
  rfl

theorem lnAbsQGammaRatFloatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (p : ℕ) (mode : RoundingMode) :
    lnAbsQGammaRatFloatPrecRoundFuel fuel q x p mode
      = lnAbsQGammaOf (qBaseRat q) (qArgFloat x) fuel p mode := by
  have hpos := (qRatBase_pos_iff q).mpr h0
  have hne : ¬ q.num = q.den := fun hc => h1 ((qRatBase_one_iff q hpos.1).mp hc)
  unfold lnAbsQGammaRatFloatPrecRoundFuel
  rw [ite_eq_left hpos, ite_eq_right hne]
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero => rfl
  | finite s e pr m hv => rfl

theorem lnAbsQGammaRatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1) (x : AzRat)
    (p : ℕ) (mode : RoundingMode) :
    lnAbsQGammaRatPrecRoundFuel fuel q x p mode
      = lnAbsQGammaOf (qBaseRat q) (qArgRat x) fuel p mode := by
  have hpos := (qRatBase_pos_iff q).mpr h0
  have hne : ¬ q.num = q.den := fun hc => h1 ((qRatBase_one_iff q hpos.1).mp hc)
  unfold lnAbsQGammaRatPrecRoundFuel
  rw [ite_eq_left hpos, ite_eq_right hne]

/-! ### The specifications of `ln |Γ_q|` -/

/-- **The specification of `ln |Γ_q(x)|` for floats** (the value component; `ZivSpec`): sound
at every fuel; complete in the limit of the fuel wherever the value is no rounding boundary;
correct at every fuel on the trivial class, at `0`, the poles, `1` and `2` (the values `+∞`
and `0`), and at the integers `n ≥ 3` whose value is formed (irrational values). -/
theorem lnAbsQGammaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.toVal.bind fun x => Spec.lnAbsQGamma q x)
      (fun fuel a p mode => (lnAbsQGammaPrecRoundFuel fuel a.1 a.2 p mode).1)
      {a | QTrivial (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∨
        (QReal (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∧
          QLnZero (qArgFloat a.2))}
      {a | QReal (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∧
        QLnIrr (qBaseFloat a.1) (qArgFloat a.2)} :=
  lnAbsQGamma_zivSpec_sides (α := AzFloat × AzFloat) (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.toVal)
    (f := fun fuel a p mode => (lnAbsQGammaPrecRoundFuel fuel a.1 a.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsGammaPrecRoundFuel fuel a.2 p mode).1)
    (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1) (fun a xv hx => qArgFloat_spec hx)
    (fun fuel a p _ mode => lnAbsGammaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsGammaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      show (lnAbsQGammaPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaPrecRoundFuel
      rw [qFloatBase_bad hb]
      rfl)
    (fun fuel a p mode hq => by
      show (lnAbsQGammaPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaPrecRoundFuel
      rw [qFloatBase_pos hq one_pos, (qFloatBase_one_iff hq).mpr rfl]
      rfl)
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      show (lnAbsQGammaPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      rw [lnAbsQGammaPrecRoundFuel_eq_of fuel hq h0 h1 hx])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      obtain ⟨q, x⟩ := a
      have hne : (le q one && le one q) = false := by
        rw [← Bool.not_eq_true]
        exact mt (qFloatBase_one_iff hq).mp h1
      show (lnAbsQGammaPrecRoundFuel fuel q x p mode).1 = _
      unfold lnAbsQGammaPrecRoundFuel
      rw [qFloatBase_pos hq h0, hne]
      cases x with
      | nan => simp
      | infinity s => cases s <;> simp [Spec.lnAbsQGammaAt_top, Spec.lnAbsQGammaAt_bot]
      | zero => exact absurd toVal_zero' (hx 0)
      | finite s e pr m hv => exact absurd (toVal_finite s e pr m hv) (hx _))

/-- **The specification of `ln |Γ_q(x)|` for a float `q` and a rational `x`.** -/
theorem lnAbsQGammaFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzRat =>
        a.1.toVal.bind fun q => Spec.lnAbsQGamma q (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => (lnAbsQGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode).1)
      {a | QTrivial (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∨
        (QReal (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧ QLnZero (qArgRat a.2))}
      {a | QReal (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧
        QLnIrr (qBaseFloat a.1) (qArgRat a.2)} :=
  lnAbsQGamma_zivSpec_sides (α := AzFloat × AzRat) (qe := fun a => a.1.toVal)
    (xe := fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => (lnAbsQGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsGammaRatPrecRoundFuel fuel a.2 p mode).1)
    (fun a => qBaseFloat a.1) (fun a => qArgRat a.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a xv hx => by
      rw [Option.some.injEq, EReal.coe_eq_coe_iff] at hx
      rw [← hx]
      exact qArgRat_spec a.2)
    (fun fuel a p _ mode => lnAbsGammaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsGammaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      show (lnAbsQGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaFloatRatPrecRoundFuel
      rw [qFloatBase_bad hb]
      rfl)
    (fun fuel a p mode hq => by
      show (lnAbsQGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaFloatRatPrecRoundFuel
      rw [qFloatBase_pos hq one_pos, (qFloatBase_one_iff hq).mpr rfl]
      rfl)
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      show (lnAbsQGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      rw [lnAbsQGammaFloatRatPrecRoundFuel_eq_of fuel hq h0 h1])
    (fun fuel a p _ mode qv hq h0 h1 hx => absurd rfl (hx _))

/-- **The specification of `ln |Γ_q(x)|` for a rational `q` and a float `x`.** -/
theorem lnAbsQGammaRatFloatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat =>
        a.2.toVal.bind fun x => Spec.lnAbsQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x)
      (fun fuel a p mode => (lnAbsQGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode).1)
      {a | QTrivial (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∨
        (QReal (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∧ QLnZero (qArgFloat a.2))}
      {a | QReal (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∧ QLnIrr (qBaseRat a.1) (qArgFloat a.2)} := by
  have hposof : ∀ (q : AzRat) (qv : ℝ),
      some (((AzRat.toRat q : ℚ) : ℝ) : EReal) = some (qv : EReal) →
      ((AzRat.toRat q : ℚ) : ℝ) = qv := fun q qv h => by
    rwa [Option.some.injEq, EReal.coe_eq_coe_iff] at h
  exact lnAbsQGamma_zivSpec_sides (α := AzRat × AzFloat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)) (xe := fun a => a.2.toVal)
    (f := fun fuel a p mode => (lnAbsQGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsGammaPrecRoundFuel fuel a.2 p mode).1)
    (fun a => qBaseRat a.1) (fun a => qArgFloat a.2)
    (fun a qv hq h0 h1 => by
      have e := hposof a.1 qv hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a xv hx => qArgFloat_spec hx)
    (fun fuel a p _ mode => lnAbsGammaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsGammaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      have hle := hb _ rfl
      show (lnAbsQGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaRatFloatPrecRoundFuel
      rw [ite_eq_right (fun hc => by linarith [(qRatBase_pos_iff a.1).mp hc])])
    (fun fuel a p mode hq => by
      have e := hposof a.1 1 hq
      have hpos := (qRatBase_pos_iff a.1).mpr (by rw [e]; exact one_pos)
      show (lnAbsQGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaRatFloatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_left ((qRatBase_one_iff a.1 hpos.1).mpr e)])
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      have e := hposof a.1 qv hq
      rw [← e] at h0 h1
      show (lnAbsQGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      rw [lnAbsQGammaRatFloatPrecRoundFuel_eq_of fuel h0 h1 hx])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      obtain ⟨q, x⟩ := a
      have e := hposof q qv hq
      have hpos := (qRatBase_pos_iff q).mpr (by rw [e]; exact h0)
      have hne : ¬ q.num = q.den := fun hc => h1 (e ▸ (qRatBase_one_iff q hpos.1).mp hc)
      show (lnAbsQGammaRatFloatPrecRoundFuel fuel q x p mode).1 = _
      unfold lnAbsQGammaRatFloatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_right hne]
      cases x with
      | nan => simp
      | infinity s => cases s <;> simp [Spec.lnAbsQGammaAt_top, Spec.lnAbsQGammaAt_bot]
      | zero => exact absurd toVal_zero' (hx 0)
      | finite s e pr m hv => exact absurd (toVal_finite s e pr m hv) (hx _))

/-- **The specification of `ln |Γ_q(x)|` for rationals `q` and `x`.** -/
theorem lnAbsQGammaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzRat => Spec.lnAbsQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => (lnAbsQGammaRatPrecRoundFuel fuel a.1 a.2 p mode).1)
      {a | QTrivial (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∨
        (QReal (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧ QLnZero (qArgRat a.2))}
      {a | QReal (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧
        QLnIrr (qBaseRat a.1) (qArgRat a.2)} := by
  have hposof : ∀ (q : AzRat) (qv : ℝ),
      some (((AzRat.toRat q : ℚ) : ℝ) : EReal) = some (qv : EReal) →
      ((AzRat.toRat q : ℚ) : ℝ) = qv := fun q qv h => by
    rwa [Option.some.injEq, EReal.coe_eq_coe_iff] at h
  exact lnAbsQGamma_zivSpec_sides (α := AzRat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => (lnAbsQGammaRatPrecRoundFuel fuel a.1 a.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsGammaRatPrecRoundFuel fuel a.2 p mode).1)
    (fun a => qBaseRat a.1) (fun a => qArgRat a.2)
    (fun a qv hq h0 h1 => by
      have e := hposof a.1 qv hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a xv hx => by
      rw [Option.some.injEq, EReal.coe_eq_coe_iff] at hx
      rw [← hx]
      exact qArgRat_spec a.2)
    (fun fuel a p _ mode => lnAbsGammaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsGammaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      have hle := hb _ rfl
      show (lnAbsQGammaRatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaRatPrecRoundFuel
      rw [ite_eq_right (fun hc => by linarith [(qRatBase_pos_iff a.1).mp hc])])
    (fun fuel a p mode hq => by
      have e := hposof a.1 1 hq
      have hpos := (qRatBase_pos_iff a.1).mpr (by rw [e]; exact one_pos)
      show (lnAbsQGammaRatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      unfold lnAbsQGammaRatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_left ((qRatBase_one_iff a.1 hpos.1).mpr e)])
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      have e := hposof a.1 qv hq
      rw [← e] at h0 h1
      show (lnAbsQGammaRatPrecRoundFuel fuel a.1 a.2 p mode).1 = _
      rw [lnAbsQGammaRatPrecRoundFuel_eq_of fuel h0 h1])
    (fun fuel a p _ mode qv hq h0 h1 hx => absurd rfl (hx _))

/-! ### The sign -/

/-- **The sign component is the sign of `Γ_q(x)`** off the poles, whenever the value is not
`NaN` (floats). -/
theorem lnAbsQGammaPrecRoundFuel_sign (fuel : ℕ) {q x : AzFloat} {qv xv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    (hx : x.toVal = some (xv : EReal)) (hnz : ∀ m : ℕ, xv ≠ -m) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (hne : (lnAbsQGammaPrecRoundFuel fuel q x p mode).1 ≠ (nan, .eq)) :
    (lnAbsQGammaPrecRoundFuel fuel q x p mode).2 = true ↔ 0 < qGammaReal qv xv := by
  rw [lnAbsQGammaPrecRoundFuel_eq_of fuel hq h0 h1 hx] at hne ⊢
  exact lnAbsQGammaOf_sign (qBaseFloat_spec hq h0 h1) (qArgFloat_spec hx) hnz fuel p mode hne

/-- The sign component, for a float `q` and a rational `x`. -/
theorem lnAbsQGammaFloatRatPrecRoundFuel_sign (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1) (x : AzRat)
    (hnz : ∀ m : ℕ, ((AzRat.toRat x : ℚ) : ℝ) ≠ -m) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQGammaFloatRatPrecRoundFuel fuel q x p mode).1 ≠ (nan, .eq)) :
    (lnAbsQGammaFloatRatPrecRoundFuel fuel q x p mode).2 = true
      ↔ 0 < qGammaReal qv ((AzRat.toRat x : ℚ) : ℝ) := by
  rw [lnAbsQGammaFloatRatPrecRoundFuel_eq_of fuel hq h0 h1] at hne ⊢
  exact lnAbsQGammaOf_sign (qBaseFloat_spec hq h0 h1) (qArgRat_spec x) hnz fuel p mode hne

/-- The sign component, for a rational `q` and a float `x`. -/
theorem lnAbsQGammaRatFloatPrecRoundFuel_sign (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hnz : ∀ m : ℕ, xv ≠ -m) (p : ℕ) [NeZero p]
    (mode : RoundingMode)
    (hne : (lnAbsQGammaRatFloatPrecRoundFuel fuel q x p mode).1 ≠ (nan, .eq)) :
    (lnAbsQGammaRatFloatPrecRoundFuel fuel q x p mode).2 = true
      ↔ 0 < qGammaReal ((AzRat.toRat q : ℚ) : ℝ) xv := by
  rw [lnAbsQGammaRatFloatPrecRoundFuel_eq_of fuel h0 h1 hx] at hne ⊢
  exact lnAbsQGammaOf_sign (qBaseRat_spec q h0 h1) (qArgFloat_spec hx) hnz fuel p mode hne

/-- The sign component, for rationals. -/
theorem lnAbsQGammaRatPrecRoundFuel_sign (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1) (x : AzRat)
    (hnz : ∀ m : ℕ, ((AzRat.toRat x : ℚ) : ℝ) ≠ -m) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQGammaRatPrecRoundFuel fuel q x p mode).1 ≠ (nan, .eq)) :
    (lnAbsQGammaRatPrecRoundFuel fuel q x p mode).2 = true
      ↔ 0 < qGammaReal ((AzRat.toRat q : ℚ) : ℝ) ((AzRat.toRat x : ℚ) : ℝ) := by
  rw [lnAbsQGammaRatPrecRoundFuel_eq_of fuel h0 h1] at hne ⊢
  exact lnAbsQGammaOf_sign (qBaseRat_spec q h0 h1) (qArgRat_spec x) hnz fuel p mode hne

/-! ### The specifications of `ln Γ_q` -/

/-- **The specification of `ln Γ_q(x)` for floats** (`ZivSpec`): that of `ln |Γ_q(x)|`, and
`NaN` at every fuel for `x < 0`. -/
theorem lnQGammaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.toVal.bind fun x => Spec.lnQGamma q x)
      (fun fuel a p mode => lnQGammaPrecRoundFuel fuel a.1 a.2 p mode)
      {a | lt a.2 zero = true ∨
        QTrivial (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∨
        (QReal (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∧
          QLnZero (qArgFloat a.2))}
      {a | QReal (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∧
        QLnIrr (qBaseFloat a.1) (qArgFloat a.2)} := by
  have hval : (fun a : AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.toVal.bind fun x => Spec.lnQGamma q x)
      = fun a => if lt a.2 zero = true then none
        else a.1.toVal.bind fun q => a.2.toVal.bind fun x => Spec.lnAbsQGamma q x := by
    funext a
    simp only [Spec.lnQGamma_eq, bind_restrict_float]
    by_cases h : lt a.2 zero = true
    · simp only [h, ite_true]
      exact bind_const_none _
    · simp only [h]
      rfl
  rw [hval]
  refine (lnAbsQGammaPrecRoundFuel_zivSpec.restrict
    (fun a : AzFloat × AzFloat => lt a.2 zero = true)).mono ?_ ?_
  · rintro a (h | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro a ⟨hR, hI⟩
    refine ⟨fun hneg => ?_, hR, hI⟩
    obtain ⟨qv, xv, -, -, -, hx⟩ := hR
    have hx' : a.2.toVal = some (xv : EReal) := hx
    have hpos := hI.pos (qArgFloat_spec hx')
    exact absurd ((lt_eq_true_iff hx' toVal_zero').mp hneg) (not_lt.mpr hpos.le)

/-- **The specification of `ln Γ_q(x)` for a rational `q` and a float `x`.** -/
theorem lnQGammaRatFloatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat =>
        a.2.toVal.bind fun x => Spec.lnQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x)
      (fun fuel a p mode => lnQGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode)
      {a | lt a.2 zero = true ∨
        QTrivial (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∨
        (QReal (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∧ QLnZero (qArgFloat a.2))}
      {a | QReal (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∧ QLnIrr (qBaseRat a.1) (qArgFloat a.2)} := by
  have hval : (fun a : AzRat × AzFloat =>
        a.2.toVal.bind fun x => Spec.lnQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x)
      = fun a => if lt a.2 zero = true then none
        else a.2.toVal.bind fun x =>
          Spec.lnAbsQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x := by
    funext a
    simp only [Spec.lnQGamma_eq, bind_restrict_float]
  rw [hval]
  refine (lnAbsQGammaRatFloatPrecRoundFuel_zivSpec.restrict
    (fun a : AzRat × AzFloat => lt a.2 zero = true)).mono ?_ ?_
  · rintro a (h | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro a ⟨hR, hI⟩
    refine ⟨fun hneg => ?_, hR, hI⟩
    obtain ⟨qv, xv, -, -, -, hx⟩ := hR
    have hx' : a.2.toVal = some (xv : EReal) := hx
    have hpos := hI.pos (qArgFloat_spec hx')
    exact absurd ((lt_eq_true_iff hx' toVal_zero').mp hneg) (not_lt.mpr hpos.le)

/-- **The specification of `ln Γ_q(x)` for a float `q` and a rational `x`.** -/
theorem lnQGammaFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzRat =>
        a.1.toVal.bind fun q => Spec.lnQGamma q (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => lnQGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode)
      {a | ratIsNeg a.2 = true ∨
        QTrivial (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∨
        (QReal (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧ QLnZero (qArgRat a.2))}
      {a | QReal (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧
        QLnIrr (qBaseFloat a.1) (qArgRat a.2)} := by
  have hval : (fun a : AzFloat × AzRat =>
        a.1.toVal.bind fun q => Spec.lnQGamma q (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      = fun a => if ratIsNeg a.2 = true then none
        else a.1.toVal.bind fun q =>
          Spec.lnAbsQGamma q (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal) := by
    funext a
    simp only [Spec.lnQGamma_eq]
    by_cases h : ratIsNeg a.2 = true
    · have h' : ((((AzRat.toRat a.2 : ℚ) : ℝ) : ℝ) : EReal) < 0 := by
        exact_mod_cast (ratIsNeg_iff a.2).mp h
      simp only [h, h', ite_true]
      exact bind_const_none _
    · have h' : ¬ ((((AzRat.toRat a.2 : ℚ) : ℝ) : ℝ) : EReal) < 0 := fun hc =>
        h ((ratIsNeg_iff a.2).mpr (by exact_mod_cast hc))
      simp only [h, h', ite_false]
      rfl
  rw [hval]
  refine (lnAbsQGammaFloatRatPrecRoundFuel_zivSpec.restrict
    (fun a : AzFloat × AzRat => ratIsNeg a.2 = true)).mono ?_ ?_
  · rintro a (h | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro a ⟨hR, hI⟩
    refine ⟨fun hneg => ?_, hR, hI⟩
    have hpos := hI.pos (qArgRat_spec a.2)
    exact absurd ((ratIsNeg_iff a.2).mp hneg) (not_lt.mpr hpos.le)

/-- **The specification of `ln Γ_q(x)` for rationals `q` and `x`.** -/
theorem lnQGammaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzRat => Spec.lnQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => lnQGammaRatPrecRoundFuel fuel a.1 a.2 p mode)
      {a | ratIsNeg a.2 = true ∨
        QTrivial (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∨
        (QReal (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧ QLnZero (qArgRat a.2))}
      {a | QReal (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧
        QLnIrr (qBaseRat a.1) (qArgRat a.2)} := by
  have hval : (fun a : AzRat × AzRat => Spec.lnQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      = fun a => if ratIsNeg a.2 = true then none
        else Spec.lnAbsQGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)
          (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal) := by
    funext a
    simp only [Spec.lnQGamma_eq]
    by_cases h : ratIsNeg a.2 = true
    · have h' : ((((AzRat.toRat a.2 : ℚ) : ℝ) : ℝ) : EReal) < 0 := by
        exact_mod_cast (ratIsNeg_iff a.2).mp h
      simp only [h, h', ite_true]
    · have h' : ¬ ((((AzRat.toRat a.2 : ℚ) : ℝ) : ℝ) : EReal) < 0 := fun hc =>
        h ((ratIsNeg_iff a.2).mpr (by exact_mod_cast hc))
      simp only [h, h', ite_false]
      rfl
  rw [hval]
  refine (lnAbsQGammaRatPrecRoundFuel_zivSpec.restrict
    (fun a : AzRat × AzRat => ratIsNeg a.2 = true)).mono ?_ ?_
  · rintro a (h | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro a ⟨hR, hI⟩
    refine ⟨fun hneg => ?_, hR, hI⟩
    have hpos := hI.pos (qArgRat_spec a.2)
    exact absurd ((ratIsNeg_iff a.2).mp hneg) (not_lt.mpr hpos.le)

/-! ### At the default fuel -/

/-- **`ln |Γ_q(x)|` for floats is correctly rounded, or the fuel ran out.** -/
theorem lnAbsQGammaPrecRound_eq_or (q x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsQGammaPrecRound q x p mode).1 = roundVal p mode
        (q.toVal.bind fun qe => x.toVal.bind fun xe => Spec.lnAbsQGamma qe xe) ∨
      (lnAbsQGammaPrecRound q x p mode).1 = (nan, .eq) :=
  lnAbsQGammaPrecRoundFuel_zivSpec.sound (qGammaFuel (lt x zero) p) (q, x) p mode

theorem lnAbsQGammaFloatRatPrecRound_eq_or (q : AzFloat) (x : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQGammaFloatRatPrecRound q x p mode).1 = roundVal p mode
        (q.toVal.bind fun qe => Spec.lnAbsQGamma qe (((AzRat.toRat x : ℚ) : ℝ) : EReal)) ∨
      (lnAbsQGammaFloatRatPrecRound q x p mode).1 = (nan, .eq) :=
  lnAbsQGammaFloatRatPrecRoundFuel_zivSpec.sound (qGammaFuel (!x.sign) p) (q, x) p mode

theorem lnAbsQGammaRatFloatPrecRound_eq_or (q : AzRat) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQGammaRatFloatPrecRound q x p mode).1 = roundVal p mode
        (x.toVal.bind fun xe => Spec.lnAbsQGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal) xe) ∨
      (lnAbsQGammaRatFloatPrecRound q x p mode).1 = (nan, .eq) :=
  lnAbsQGammaRatFloatPrecRoundFuel_zivSpec.sound (qGammaFuel (lt x zero) p) (q, x) p mode

theorem lnAbsQGammaRatPrecRound_eq_or (q x : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsQGammaRatPrecRound q x p mode).1 = roundVal p mode
        (Spec.lnAbsQGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)
          (((AzRat.toRat x : ℚ) : ℝ) : EReal)) ∨
      (lnAbsQGammaRatPrecRound q x p mode).1 = (nan, .eq) :=
  lnAbsQGammaRatPrecRoundFuel_zivSpec.sound (qGammaFuel (!x.sign) p) (q, x) p mode

/-- **`ln Γ_q(x)` for floats is correctly rounded, or the fuel ran out.** -/
theorem lnQGammaPrecRound_eq_or (q x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnQGammaPrecRound q x p mode = roundVal p mode
        (q.toVal.bind fun qe => x.toVal.bind fun xe => Spec.lnQGamma qe xe) ∨
      lnQGammaPrecRound q x p mode = (nan, .eq) :=
  lnQGammaPrecRoundFuel_zivSpec.sound (qGammaFuel false p) (q, x) p mode

theorem lnQGammaFloatRatPrecRound_eq_or (q : AzFloat) (x : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQGammaFloatRatPrecRound q x p mode = roundVal p mode
        (q.toVal.bind fun qe => Spec.lnQGamma qe (((AzRat.toRat x : ℚ) : ℝ) : EReal)) ∨
      lnQGammaFloatRatPrecRound q x p mode = (nan, .eq) :=
  lnQGammaFloatRatPrecRoundFuel_zivSpec.sound (qGammaFuel false p) (q, x) p mode

theorem lnQGammaRatFloatPrecRound_eq_or (q : AzRat) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQGammaRatFloatPrecRound q x p mode = roundVal p mode
        (x.toVal.bind fun xe => Spec.lnQGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal) xe) ∨
      lnQGammaRatFloatPrecRound q x p mode = (nan, .eq) :=
  lnQGammaRatFloatPrecRoundFuel_zivSpec.sound (qGammaFuel false p) (q, x) p mode

theorem lnQGammaRatPrecRound_eq_or (q x : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnQGammaRatPrecRound q x p mode = roundVal p mode
        (Spec.lnQGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal)
          (((AzRat.toRat x : ℚ) : ℝ) : EReal)) ∨
      lnQGammaRatPrecRound q x p mode = (nan, .eq) :=
  lnQGammaRatPrecRoundFuel_zivSpec.sound (qGammaFuel false p) (q, x) p mode

end Azurite.AzFloat
