/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma
import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.AzFloat.Equiv.Pow2
import Azurite.AzFloat.Equiv.Div
import Azurite.AzNat.Equiv.Factorial

/-!
# Equivalence: `Γ` and `1/Γ`

`Spec.gamma` and `Spec.reciprocalGamma` on the extended reals, and the specifications

* `gammaPrecRound_eq_or`: `gammaPrecRound x p mode = liftVal Spec.gamma x p mode`, or
  `(nan, .eq)` if the fuel runs out;
* `reciprocalGammaPrecRound_eq_or`: the same for `1/Γ` and `Spec.reciprocalGamma`.

`Spec.gamma` is `+∞` at `0` and `+∞`, undefined at the negative integers and at `−∞`.
`Spec.reciprocalGamma` is `0` at `+∞`, undefined at `−∞`, and `(Γ x)⁻¹` elsewhere — Mathlib's
`Real.Gamma` is `0` at the poles, which is the value of the entire function `1/Γ` there.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- `Γ` on the extended reals: `+∞` at `0` (from the right) and at `+∞`; undefined at the poles
`−1, −2, …` and at `−∞`. -/
noncomputable def gamma (a : EReal) : Option EReal :=
  if a = ⊤ then some ⊤ else if a = ⊥ then none else if a = 0 then some ⊤
  else if a < 0 ∧ ∃ k : ℤ, a.toReal = k then none
  else some ((Real.Gamma a.toReal : ℝ) : EReal)

/-- `1/Γ` on the extended reals: `0` at `+∞` (and at the poles of `Γ`); undefined at `−∞`. -/
noncomputable def reciprocalGamma (a : EReal) : Option EReal :=
  if a = ⊤ then some 0 else if a = ⊥ then none
  else some (((Real.Gamma a.toReal)⁻¹ : ℝ) : EReal)

theorem gamma_top : gamma ⊤ = some ⊤ := by simp [gamma]

theorem gamma_bot : gamma ⊥ = none := by
  unfold gamma
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

theorem gamma_zero : gamma 0 = some ⊤ := by
  unfold gamma
  rw [ite_eq_right EReal.zero_ne_top, ite_eq_right EReal.zero_ne_bot, ite_eq_left rfl]

theorem gamma_coe_of_pole {xv : ℝ} (h : xv < 0) (hk : ∃ k : ℤ, xv = k) :
    gamma (xv : EReal) = none := by
  unfold gamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    ite_eq_right (by exact_mod_cast h.ne), ite_eq_left ⟨by exact_mod_cast h, by simpa using hk⟩]

theorem gamma_coe {xv : ℝ} (h0 : xv ≠ 0) (h : ¬ (xv < 0 ∧ ∃ k : ℤ, xv = k)) :
    gamma (xv : EReal) = some ((Real.Gamma xv : ℝ) : EReal) := by
  unfold gamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    ite_eq_right (by exact_mod_cast h0),
    ite_eq_right (fun hc => h ⟨by exact_mod_cast hc.1, by simpa using hc.2⟩), EReal.toReal_coe]

theorem reciprocalGamma_top : reciprocalGamma ⊤ = some 0 := by simp [reciprocalGamma]

theorem reciprocalGamma_bot : reciprocalGamma ⊥ = none := by
  unfold reciprocalGamma
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

theorem reciprocalGamma_coe (xv : ℝ) :
    reciprocalGamma (xv : EReal) = some (((Real.Gamma xv)⁻¹ : ℝ) : EReal) := by
  unfold reciprocalGamma
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _), EReal.toReal_coe]

end Spec

/-- `Γ` vanishes (in Mathlib's convention) at the nonpositive integers. -/
theorem Gamma_eq_zero_of_int_nonpos {xv : ℝ} (h : xv ≤ 0) (hk : ∃ k : ℤ, xv = k) :
    Real.Gamma xv = 0 := by
  obtain ⟨k, rfl⟩ := hk
  have hk0 : k ≤ 0 := by exact_mod_cast h
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hk0
  have := Real.Gamma_neg_nat_eq_zero n
  push_cast
  exact this

/-- A small positive integer float, as a natural number. -/
theorem gammaSmallInt_spec {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    {B : ℕ} (h : gammaSmallInt (finite s e q m hv) B = true) :
    ∃ n : ℕ, (truncToAzInt (finite s e q m hv)).abs.toNat = n + 1 ∧
      finiteVal s e m = ((n : ℝ) + 1) := by
  unfold gammaSmallInt at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hi, hp⟩, -⟩ := h
  have hpos : 0 < finiteVal s e m :=
    (lt_eq_true_iff toVal_zero' (toVal_finite s e q m hv)).mp hp
  have ht := truncToAzInt_of_isInteger s e hv hi
  set z := truncToAzInt (finite s e q m hv) with hz
  have htoInt : z.toInt = if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ) := rfl
  have hzpos : 0 < z.toInt := by
    have : (0 : ℝ) < (z.toInt : ℝ) := by rw [ht]; exact hpos
    exact_mod_cast this
  have hzn : z.toInt = (z.abs.toNat : ℤ) := by
    rw [htoInt] at hzpos ⊢
    split_ifs at hzpos ⊢ with hs
    · rfl
    · omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, z.abs.toNat = n + 1 := ⟨z.abs.toNat - 1, by omega⟩
  refine ⟨n, hn, ?_⟩
  rw [← ht, hzn, hn]
  push_cast
  ring

/-- **`Γ` is correctly rounded unless the fuel runs out.** -/
theorem gammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaPrecRound x p mode = liftVal Spec.gamma x p mode ∨
      gammaPrecRound x p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [gammaPrecRound, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [gammaPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.gamma_bot, roundVal_none]
    · simp only [gammaPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.gamma_top, roundVal_top]
  | zero =>
    left
    simp only [gammaPrecRound, toVal_zero, Option.bind_some, Spec.gamma_zero, roundVal_top]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
    simp only [gammaPrecRound, toVal_finite, Option.bind_some]
    by_cases hpole : (isInteger (finite s e q m hv) && !s) = true
    · left
      rw [ite_eq_left hpole]
      rw [Bool.and_eq_true] at hpole
      obtain ⟨hi, hs⟩ := hpole
      have hs' : s = false := by simpa using hs
      subst hs'
      rw [Spec.gamma_coe_of_pole (finiteVal_false_neg e hv) ((isInteger_finite false e hv).mp hi),
        roundVal_none]
    · rw [ite_eq_right hpole, ite_eq_right hp]
      have hnot : ¬ (finiteVal s e m < 0 ∧ ∃ k : ℤ, finiteVal s e m = k) := by
        rintro ⟨hneg, hk⟩
        apply hpole
        rw [Bool.and_eq_true]
        refine ⟨(isInteger_finite s e hv).mpr hk, ?_⟩
        cases s
        · rfl
        · exact absurd hneg (not_lt.mpr (finiteVal_true_pos e hv).le)
      rw [Spec.gamma_coe hx0 hnot]
      split
      · rename_i r hr
        left
        exact gammaTiny?_eq hv p mode hr
      · split_ifs with hsm
        · left
          obtain ⟨n, hn, hval⟩ := gammaSmallInt_spec hv hsm
          rw [hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
            setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_factorial]
        · rcases eq_or_ne (zivLoop (gammaApprox false (finite s e q m hv) e s) p mode gammaFuel
            (max 64 (p + 32))) (nan, .eq) with hz | hz
          · right; exact hz
          · left
            exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
              (fun w hw => gammaApprox_valid_or_none false hx e
                (fun h => by subst h; exact finiteVal_true_pos e hv)
                (fun h => by subst h; exact finiteVal_false_neg e hv) hw p mode)
              _ _ (le_max_left _ _) hz

/-- **`1/Γ` is correctly rounded unless the fuel runs out.** -/
theorem reciprocalGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    reciprocalGammaPrecRound x p mode = liftVal Spec.reciprocalGamma x p mode ∨
      reciprocalGammaPrecRound x p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [reciprocalGammaPrecRound, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [reciprocalGammaPrecRound, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.reciprocalGamma_bot, roundVal_none]
    · simp only [reciprocalGammaPrecRound, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.reciprocalGamma_top, roundVal_zero]
  | zero =>
    left
    simp only [reciprocalGammaPrecRound, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.reciprocalGamma_coe, Real.Gamma_zero, inv_zero, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    simp only [reciprocalGammaPrecRound, toVal_finite, Option.bind_some]
    rw [Spec.reciprocalGamma_coe]
    by_cases hpole : (isInteger (finite s e q m hv) && !s) = true
    · left
      rw [ite_eq_left hpole]
      rw [Bool.and_eq_true] at hpole
      obtain ⟨hi, hs⟩ := hpole
      have hs' : s = false := by simpa using hs
      subst hs'
      rw [Gamma_eq_zero_of_int_nonpos (finiteVal_false_neg e hv).le
        ((isInteger_finite false e hv).mp hi), inv_zero, EReal.coe_zero, roundVal_zero]
    · rw [ite_eq_right hpole, ite_eq_right hp]
      split
      · rename_i r hr
        left
        exact reciprocalGammaTiny?_eq hv p mode hr
      · split_ifs with hsm
        · left
          obtain ⟨n, hn, hval⟩ := gammaSmallInt_spec hv hsm
          have hf0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
            divPrecRound_eq_liftVal₂, liftVal₂, toVal_one', toVal_ofAzNat, Option.bind_some,
            Option.bind_some, AzNat.toNat_factorial, Spec.div_coe_coe _ _ hf0, one_div]
        · rcases eq_or_ne (zivLoop (gammaApprox true (finite s e q m hv) e s) p mode gammaFuel
            (max 64 (p + 32))) (nan, .eq) with hz | hz
          · right; exact hz
          · left
            exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
              (fun w hw => gammaApprox_valid_or_none true hx e
                (fun h => by subst h; exact finiteVal_true_pos e hv)
                (fun h => by subst h; exact finiteVal_false_neg e hv) hw p mode)
              _ _ (le_max_left _ _) hz

end Azurite.AzFloat
