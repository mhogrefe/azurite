/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma
import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.AzFloat.Equiv.GammaConstants
import Azurite.AzFloat.Equiv.GammaSpecial
import Azurite.AzFloat.Equiv.ZivSpec
import Azurite.AzFloat.Equiv.Pow2
import Azurite.AzFloat.Equiv.Div
import Azurite.AzNat.Equiv.Factorial

/-!
# Equivalence: `Γ` and `1/Γ`

`Spec.gamma` and `Spec.reciprocalGamma` on the extended reals, and the specifications

* `gammaPrecRound_eq_or`: `gammaPrecRound x p mode = liftVal Spec.gamma x p mode`, or
  `(nan, .eq)` if the fuel runs out;
* `reciprocalGammaPrecRound_eq_or`: the same for `1/Γ` and `Spec.reciprocalGamma`;
* `gammaPrecRound_eq_of_special`, `reciprocalGammaPrecRound_eq_of_special`: no `NaN` at the
  quarter-integers (`gammaSpecial`, `gammaSpecial_iff`), where the loops are certified.

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

/-- `isQuarter` recognizes `1/4`. -/
theorem isQuarter_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (h : isQuarter x = true) : xv = 1 / 4 := by
  unfold isQuarter at h
  rw [Bool.and_eq_true] at h
  have hq : (one <<< AzInt.ofInt (-2)).toVal = some (((1 / 4 : ℝ) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (-2)), AzInt.toInt_ofInt]
    norm_num
  exact le_antisymm ((le_eq_true_iff hx hq).mp h.1) ((le_eq_true_iff hq hx).mp h.2)

/-- **The certified loop at a quarter-integer** gives the correctly rounded value. -/
theorem gammaCertified_eq (recip : Bool) {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hc : gammaSpecial (finite s e q m hv) = true) (p : ℕ) [NeZero p]
    (mode : RoundingMode)
    (h : ∃ f : ℕ, (roundingPossible
      (gammaApprox recip (finite s e q m hv) e s (max 64 (p + 32) * 2 ^ f)).1
      (gammaApprox recip (finite s e q m hv) e s (max 64 (p + 32) * 2 ^ f)).2 p mode).isSome
        = true) :
    zivLoopCertified (gammaApprox recip (finite s e q m hv) e s) p mode (max 64 (p + 32)) h
      = roundVal p mode (some ((gammaVal recip (finiteVal s e m) : ℝ) : EReal)) := by
  have hx := toVal_finite s e q m hv
  obtain ⟨r, hr, hden⟩ := gammaSpecial_spec hx hc
  have hirr := irrational_gammaVal recip r (by
    rcases hden with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h)))
  rw [hr] at hirr
  refine zivLoopCertified_eq_or_none p mode _ _ (not_mem_floatSet_of_irrational p hirr) _
    (by omega) (fun w hw => ?_) h
  rcases gammaApprox_valid_or_none recip hx e (pos := s)
    (fun h => by subst h; exact finiteVal_true_pos e hv)
    (fun h => by subst h; exact finiteVal_false_neg e hv) (w := w)
    (le_trans (le_max_left _ _) hw) p mode with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
  · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
  · exact Or.inr hn

theorem quarter_coprime {r : ℕ} (h0 : r ≠ 0) (h4 : r < 4) : Nat.Coprime r 4 ∨ 2 * r = 4 := by
  interval_cases r
  · exact absurd rfl h0
  · exact Or.inl (by norm_num)
  · exact Or.inr rfl
  · exact Or.inl (by norm_num)

/-- The numerator `4 |x|` of a quarter-integer float. -/
theorem gammaSpecial_num {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hc : gammaSpecial (finite s e q m hv) = true) :
    (if s then (1 : ℝ) else -1)
        * ((((truncToAzInt (finite s e q m hv <<< AzInt.ofInt 2)).abs.toNat : ℕ) : ℝ)
          / ((4 : ℕ) : ℝ)) = finiteVal s e m ∧
      (truncToAzInt (finite s e q m hv <<< AzInt.ofInt 2)).abs.toNat % 4 ≠ 0 := by
  have hx := toVal_finite s e q m hv
  have hx4 := toVal_shiftLeft_of_toVal hx (AzInt.ofInt 2)
  rw [AzInt.toInt_ofInt] at hx4
  have h4 : finiteVal s e m * (2 : ℝ) ^ (2 : ℤ) = 4 * finiteVal s e m := by norm_num; ring
  rw [h4] at hx4
  unfold gammaSpecial at hc
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hi4, hni⟩ := hc
  have habs := truncToAzInt_abs_of_int hx4 hi4
  set N := (truncToAzInt (finite s e q m hv <<< AzInt.ofInt 2)).abs.toNat with hN
  have hval : (if s then (1 : ℝ) else -1) * ((N : ℝ) / ((4 : ℕ) : ℝ)) = finiteVal s e m := by
    rw [habs]
    cases s
    · have := finiteVal_false_neg e hv
      rw [abs_of_neg (by linarith)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    · have := finiteVal_true_pos e hv
      rw [abs_of_pos (by linarith)]
      simp only [↓reduceIte]
      push_cast
      ring
  refine ⟨hval, fun hmod => ?_⟩
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hint : isInteger (finite s e q m hv) = true := by
    rw [isInteger_iff_of_toVal hx, ← hval, hk]
    cases s
    · exact ⟨-(k : ℤ), by simp only [Bool.false_eq_true, ↓reduceIte]; push_cast; ring⟩
    · exact ⟨(k : ℤ), by simp only [↓reduceIte]; push_cast; ring⟩
  rw [hni] at hint
  exact Bool.noConfusion hint

/-- **The branches of `gammaPrecRoundFuel`**: the correctly rounded value, whatever the fuel,
or — at a finite argument that is neither an integer nor a quarter-integer — the fuel loop on
`gammaApprox`. -/
theorem gammaPrecRoundFuel_eq_or_loop (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    gammaPrecRoundFuel fuel x p mode = liftVal Spec.gamma x p mode ∨
      (gammaSpecial x = false ∧ isInteger x = false ∧
        ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
          x = finite s e q m hv ∧ gammaPrecRoundFuel fuel x p mode
            = zivLoop (gammaApprox false (finite s e q m hv) e s) p mode fuel
              (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [gammaPrecRoundFuel, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [gammaPrecRoundFuel, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.gamma_bot, roundVal_none]
    · simp only [gammaPrecRoundFuel, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.gamma_top, roundVal_top]
  | zero =>
    left
    simp only [gammaPrecRoundFuel, toVal_zero, Option.bind_some, Spec.gamma_zero, roundVal_top]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
    simp only [gammaPrecRoundFuel, toVal_finite, Option.bind_some]
    by_cases hpole : (isInteger (finite s e q m hv) && !s) = true
    · left
      rw [dite_eq_left hpole]
      rw [Bool.and_eq_true] at hpole
      obtain ⟨hi, hs⟩ := hpole
      have hs' : s = false := by simpa using hs
      subst hs'
      rw [Spec.gamma_coe_of_pole (finiteVal_false_neg e hv) ((isInteger_finite false e hv).mp hi),
        roundVal_none]
    · rw [dite_eq_right hpole, dite_eq_right hp]
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
      · split_ifs with hsm hc hI
        · left
          obtain ⟨n, hn, hval⟩ := gammaSmallInt_spec hv hsm
          rw [hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
            setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_factorial]
        · left
          obtain ⟨hval, hmod⟩ := gammaSpecial_num hv hc
          split
          · rename_i r hr
            have h4 := gammaSpecialFast?_eq_or false s (d := 4) (by norm_num) hmod
              (quarter_coprime hmod (Nat.mod_lt _ (by norm_num))) p mode hr
            rw [hval] at h4
            exact nanOrElse_eq h4 (gammaCertified_eq false hv hc p mode _)
          · exact gammaCertified_eq false hv hc p mode _
        · left
          obtain ⟨-, n, hn, hval⟩ := gammaBigInt_spec hv hpole hsm hI
          have hG : Real.Gamma (finiteVal s e m) = ((n.factorial : ℕ) : ℝ) := by
            rw [hval]
            exact Real.Gamma_nat_eq_factorial n
          refine zivLoopCertified_eq_or_none p mode _ _ ?_ _ (by omega) (fun w hw => ?_) _
          · rw [hG]
            exact factorial_not_boundary p (by unfold gammaIntBound at hn; omega)
          · rcases gammaApprox_valid_or_none false hx e (pos := s)
              (fun h => by subst h; exact finiteVal_true_pos e hv)
              (fun h => by subst h; exact finiteVal_false_neg e hv) (w := w)
              (le_trans (le_max_left _ _) hw) p mode with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn'
            · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
            · exact Or.inr hn'
        · right
          exact ⟨by simpa using hc, by simpa using hI, s, e, q, m, hv, rfl, rfl⟩

/-- The fuel loop on `gammaApprox` is correct when it does not give up. -/
theorem gammaApprox_zivLoop (recip : Bool) {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (p : ℕ) [NeZero p] (mode : RoundingMode) (fuel : ℕ) :
    zivLoop (gammaApprox recip (finite s e q m hv) e s) p mode fuel (max 64 (p + 32))
        = roundVal p mode (some ((gammaVal recip (finiteVal s e m) : ℝ) : EReal)) ∨
      zivLoop (gammaApprox recip (finite s e q m hv) e s) p mode fuel (max 64 (p + 32))
        = (nan, .eq) := by
  rcases eq_or_ne (zivLoop (gammaApprox recip (finite s e q m hv) e s) p mode fuel
    (max 64 (p + 32))) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApprox_valid_or_none recip (toVal_finite s e q m hv) e
        (fun h => by subst h; exact finiteVal_true_pos e hv)
        (fun h => by subst h; exact finiteVal_false_neg e hv) hw p mode)
      _ _ (le_max_left _ _) hz

/-- The value of `Spec.gamma` at a finite non-integer float. -/
theorem liftVal_gamma_finite {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hI : isInteger (finite s e q m hv) = false) :
    (finite s e q m hv).toVal.bind Spec.gamma
      = some ((Real.Gamma (finiteVal s e m) : ℝ) : EReal) := by
  rw [toVal_finite, Option.bind_some]
  refine Spec.gamma_coe (finiteVal_ne_zero s e hv) ?_
  rintro ⟨-, hk⟩
  rw [(isInteger_finite s e hv).mpr hk] at hI
  exact Bool.noConfusion hI

/-- **`Γ` with explicit fuel is correctly rounded unless the fuel runs out**, which happens
neither at an integer nor at a quarter-integer. -/
theorem gammaPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    gammaPrecRoundFuel fuel x p mode = liftVal Spec.gamma x p mode ∨
      (gammaPrecRoundFuel fuel x p mode = (nan, .eq) ∧ gammaSpecial x = false ∧
        isInteger x = false) := by
  rcases gammaPrecRoundFuel_eq_or_loop fuel x p mode with h | ⟨hc, hI, s, e, q, m, hv, rfl, h⟩
  · exact Or.inl h
  · rcases gammaApprox_zivLoop false hv p mode fuel with hz | hz
    · left
      rw [h, hz]
      unfold liftVal
      rw [liftVal_gamma_finite hv hI]
      rfl
    · exact Or.inr ⟨h.trans hz, hc, hI⟩

/-- **`Γ` is correctly rounded unless the fuel runs out**, which does not happen at a
quarter-integer. -/
theorem gammaPrecRound_eq_or' (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaPrecRound x p mode = liftVal Spec.gamma x p mode ∨
      (gammaPrecRound x p mode = (nan, .eq) ∧ gammaSpecial x = false) :=
  (gammaPrecRoundFuel_eq_or (gammaFuel p) x p mode).imp_right fun h => ⟨h.1, h.2.1⟩

/-- **`Γ` is correctly rounded unless the fuel runs out.** -/
theorem gammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaPrecRound x p mode = liftVal Spec.gamma x p mode ∨
      gammaPrecRound x p mode = (nan, .eq) :=
  (gammaPrecRound_eq_or' x p mode).imp_right And.left

/-- **`Γ` is correctly rounded, unconditionally, at the integers**: the exact factorial, or —
beyond `gammaIntBound p`, where `(n − 1)!` is no rounding boundary — a certified loop. -/
theorem gammaPrecRound_eq_of_isInteger (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h : isInteger x = true) : gammaPrecRound x p mode = liftVal Spec.gamma x p mode := by
  rcases gammaPrecRoundFuel_eq_or (gammaFuel p) x p mode with h' | ⟨-, -, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-- **`Γ` is correctly rounded, unconditionally, at the quarter-integers** (`x = n/4` not an
integer, as recognized by `gammaSpecial`): there `Γ(x)` is irrational by Chudnovsky's theorem
(`Azurite.Chudnovsky.irrational_gamma_of_den`) and the Ziv loop carries no fuel. -/
theorem gammaPrecRound_eq_of_special (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (h : gammaSpecial x = true) : gammaPrecRound x p mode = liftVal Spec.gamma x p mode := by
  rcases gammaPrecRound_eq_or' x p mode with h' | ⟨-, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-- `gammaSpecial` recognizes the non-integers `n/4`. -/
theorem gammaSpecial_iff {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    gammaSpecial x = true ↔ (∃ n : ℤ, 4 * xv = n) ∧ ¬ ∃ k : ℤ, xv = k := by
  have hx4 := toVal_shiftLeft_of_toVal hx (AzInt.ofInt 2)
  rw [AzInt.toInt_ofInt] at hx4
  have h4 : xv * (2 : ℝ) ^ (2 : ℤ) = 4 * xv := by norm_num; ring
  unfold gammaSpecial
  rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, isInteger_iff_of_toVal hx4,
    isInteger_iff_of_toVal hx, h4]

/-- **The branches of `reciprocalGammaPrecRoundFuel`**: the correctly rounded value, whatever
the fuel, or — at a finite argument that is neither an integer nor a quarter-integer — the fuel
loop on `gammaApprox`. -/
theorem reciprocalGammaPrecRoundFuel_eq_or_loop (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaPrecRoundFuel fuel x p mode = liftVal Spec.reciprocalGamma x p mode ∨
      (gammaSpecial x = false ∧ isInteger x = false ∧
        ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
          x = finite s e q m hv ∧ reciprocalGammaPrecRoundFuel fuel x p mode
            = zivLoop (gammaApprox true (finite s e q m hv) e s) p mode fuel
              (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold liftVal
  cases x with
  | nan => left; simp [reciprocalGammaPrecRoundFuel, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [reciprocalGammaPrecRoundFuel, Bool.false_eq_true, ↓reduceIte, toVal_infinity,
        Option.bind_some, Spec.reciprocalGamma_bot, roundVal_none]
    · simp only [reciprocalGammaPrecRoundFuel, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.reciprocalGamma_top, roundVal_zero]
  | zero =>
    left
    simp only [reciprocalGammaPrecRoundFuel, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.reciprocalGamma_coe, Real.Gamma_zero, inv_zero, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    simp only [reciprocalGammaPrecRoundFuel, toVal_finite, Option.bind_some]
    rw [Spec.reciprocalGamma_coe]
    by_cases hpole : (isInteger (finite s e q m hv) && !s) = true
    · left
      rw [dite_eq_left hpole]
      rw [Bool.and_eq_true] at hpole
      obtain ⟨hi, hs⟩ := hpole
      have hs' : s = false := by simpa using hs
      subst hs'
      rw [Gamma_eq_zero_of_int_nonpos (finiteVal_false_neg e hv).le
        ((isInteger_finite false e hv).mp hi), inv_zero, EReal.coe_zero, roundVal_zero]
    · rw [dite_eq_right hpole, dite_eq_right hp]
      split
      · rename_i r hr
        left
        exact reciprocalGammaTiny?_eq hv p mode hr
      · split_ifs with hsm hc hI
        · left
          obtain ⟨n, hn, hval⟩ := gammaSmallInt_spec hv hsm
          have hf0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hn, Nat.add_sub_cancel, hval, Real.Gamma_nat_eq_factorial,
            divPrecRound_eq_liftVal₂, liftVal₂, toVal_one', toVal_ofAzNat, Option.bind_some,
            Option.bind_some, AzNat.toNat_factorial, Spec.div_coe_coe _ _ hf0, one_div]
        · left
          obtain ⟨hval, hmod⟩ := gammaSpecial_num hv hc
          split
          · rename_i r hr
            have h4 := gammaSpecialFast?_eq_or true s (d := 4) (by norm_num) hmod
              (quarter_coprime hmod (Nat.mod_lt _ (by norm_num))) p mode hr
            rw [hval] at h4
            exact nanOrElse_eq h4 (gammaCertified_eq true hv hc p mode _)
          · exact gammaCertified_eq true hv hc p mode _
        · left
          obtain ⟨-, n, hn, hval⟩ := gammaBigInt_spec hv hpole hsm hI
          have hG : (Real.Gamma (finiteVal s e m))⁻¹ = (((n.factorial : ℕ) : ℝ))⁻¹ := by
            rw [hval]
            exact congrArg (·⁻¹) (Real.Gamma_nat_eq_factorial n)
          refine zivLoopCertified_eq_or_none p mode _ _ ?_ _ (by omega) (fun w hw => ?_) _
          · rw [hG]
            exact not_mem_floatSet_of_not_isDyadic p
              (not_isDyadic_inv_factorial (by unfold gammaIntBound at hn; omega))
          · rcases gammaApprox_valid_or_none true hx e (pos := s)
              (fun h => by subst h; exact finiteVal_true_pos e hv)
              (fun h => by subst h; exact finiteVal_false_neg e hv) (w := w)
              (le_trans (le_max_left _ _) hw) p mode with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn'
            · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
            · exact Or.inr hn'
        · right
          exact ⟨by simpa using hc, by simpa using hI, s, e, q, m, hv, rfl, rfl⟩

/-- **`1/Γ` with explicit fuel is correctly rounded unless the fuel runs out**, which happens
neither at an integer nor at a quarter-integer. -/
theorem reciprocalGammaPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaPrecRoundFuel fuel x p mode = liftVal Spec.reciprocalGamma x p mode ∨
      (reciprocalGammaPrecRoundFuel fuel x p mode = (nan, .eq) ∧ gammaSpecial x = false ∧
        isInteger x = false) := by
  rcases reciprocalGammaPrecRoundFuel_eq_or_loop fuel x p mode with
    h | ⟨hc, hI, s, e, q, m, hv, rfl, h⟩
  · exact Or.inl h
  · rcases gammaApprox_zivLoop true hv p mode fuel with hz | hz
    · left
      rw [h, hz]
      unfold liftVal
      rw [toVal_finite, Option.bind_some, Spec.reciprocalGamma_coe]
      rfl
    · exact Or.inr ⟨h.trans hz, hc, hI⟩

/-- **`1/Γ` is correctly rounded unless the fuel runs out**, which does not happen at a
quarter-integer. -/
theorem reciprocalGammaPrecRound_eq_or' (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    reciprocalGammaPrecRound x p mode = liftVal Spec.reciprocalGamma x p mode ∨
      (reciprocalGammaPrecRound x p mode = (nan, .eq) ∧ gammaSpecial x = false) :=
  (reciprocalGammaPrecRoundFuel_eq_or (gammaFuel p) x p mode).imp_right fun h => ⟨h.1, h.2.1⟩

/-- **`1/Γ` is correctly rounded unless the fuel runs out.** -/
theorem reciprocalGammaPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    reciprocalGammaPrecRound x p mode = liftVal Spec.reciprocalGamma x p mode ∨
      reciprocalGammaPrecRound x p mode = (nan, .eq) :=
  (reciprocalGammaPrecRound_eq_or' x p mode).imp_right And.left

/-- **`1/Γ` is correctly rounded, unconditionally, at the integers.** -/
theorem reciprocalGammaPrecRound_eq_of_isInteger (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (h : isInteger x = true) :
    reciprocalGammaPrecRound x p mode = liftVal Spec.reciprocalGamma x p mode := by
  rcases reciprocalGammaPrecRoundFuel_eq_or (gammaFuel p) x p mode with h' | ⟨-, -, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-- **`1/Γ` is correctly rounded, unconditionally, at the quarter-integers.** -/
theorem reciprocalGammaPrecRound_eq_of_special (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (h : gammaSpecial x = true) :
    reciprocalGammaPrecRound x p mode = liftVal Spec.reciprocalGamma x p mode := by
  rcases reciprocalGammaPrecRound_eq_or' x p mode with h' | ⟨-, h'⟩
  · exact h'
  · rw [h] at h'
    exact Bool.noConfusion h'

/-! ### The specification of `Γ` as a fuel-bound function -/

/-- `Γ` at an integer is dyadic when it is a real number. -/
theorem isDyadic_of_gamma_int (n : ℤ) {v : ℝ}
    (hv : Spec.gamma (((n : ℝ) : ℝ) : EReal) = some (v : EReal)) : IsDyadic v := by
  by_cases h0 : (n : ℝ) = 0
  · rw [h0, EReal.coe_zero, Spec.gamma_zero, Option.some.injEq] at hv
    exact absurd hv (by simp)
  by_cases hneg : (n : ℝ) < 0
  · rw [Spec.gamma_coe_of_pole hneg ⟨n, rfl⟩] at hv
    exact absurd hv (by simp)
  · rw [Spec.gamma_coe h0 (fun h => hneg h.1), Option.some.injEq,
      EReal.coe_eq_coe_iff] at hv
    have hn1 : 1 ≤ n := by
      have : (0 : ℝ) < n := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm h0)
      exact_mod_cast this
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    rw [← hv]
    have : Real.Gamma (((k : ℤ) + 1 : ℤ) : ℝ) = ((k.factorial : ℕ) : ℝ) := by
      push_cast
      exact Real.Gamma_nat_eq_factorial k
    rw [this]
    exact isDyadic_natCast _

/-- `1/Γ(n)` is dyadic for an integer `n ≤ 3`: `0`, `1`, `1` or `1/2`. -/
theorem isDyadic_reciprocalGamma_int {n : ℤ} (hn3 : n ≤ 3) :
    IsDyadic (Real.Gamma (n : ℝ))⁻¹ := by
  by_cases hn0 : n ≤ 0
  · rw [Gamma_eq_zero_of_int_nonpos (by exact_mod_cast hn0) ⟨n, rfl⟩, inv_zero]
    exact isDyadic_zero
  · push Not at hn0
    have h12 : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases h12 with rfl | rfl | rfl
    · rw [Int.cast_one, Real.Gamma_one, inv_one]
      exact ⟨1, 0, by norm_num⟩
    · rw [Int.cast_ofNat, Real.Gamma_two, inv_one]
      exact ⟨1, 0, by norm_num⟩
    · have h3 : Real.Gamma ((3 : ℤ) : ℝ) = 2 := by
        have := Real.Gamma_nat_eq_factorial 2
        norm_num at this ⊢
      rw [h3]
      exact ⟨1, -1, by norm_num⟩

/-- `1/Γ(n) = 1/(n − 1)!` is not dyadic for an integer `n ≥ 4`. -/
theorem not_isDyadic_reciprocalGamma_int {n : ℤ} (hn : 4 ≤ n) :
    ¬ IsDyadic (Real.Gamma (n : ℝ))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  have : Real.Gamma (((k : ℤ) + 1 : ℤ) : ℝ) = ((k.factorial : ℕ) : ℝ) := by
    push_cast
    exact Real.Gamma_nat_eq_factorial k
  rw [this]
  exact not_isDyadic_inv_factorial (by omega)

/-- A float recognized by `gammaSpecial` is finite. -/
theorem exists_finite_of_gammaSpecial {x : AzFloat} (h : gammaSpecial x = true) :
    ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
      x = finite s e q m hv := by
  cases x with
  | finite s e q m hv => exact ⟨s, e, q, m, hv, rfl⟩
  | nan => exact absurd h (by decide)
  | infinity s => cases s <;> exact absurd h (by decide)
  | zero => exact absurd h (by decide)

/-- **The specification of `Γ`** (`ZivSpec`): sound at every fuel; complete in the limit of
the fuel wherever the value is no rounding boundary; and correct at every fuel on the
arguments that are not finite or are integers (exact values: `+∞`, undefined, factorials) and
on the quarter-integers (irrational values, by Chudnovsky's theorem). -/
theorem gammaPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.gamma) gammaPrecRoundFuel
      {x | ∀ v : ℝ, x.toVal = some (v : EReal) → ∃ n : ℤ, v = n}
      {x | gammaSpecial x = true} where
  sound := fun fuel x p _ mode =>
    (gammaPrecRoundFuel_eq_or fuel x p mode).imp_right And.left
  complete := fun x p _ mode hB => by
    by_cases hgen : ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite s e q m hv ∧ isInteger x = false
    · obtain ⟨s, e, q, m, hv, rfl, hI⟩ := hgen
      have hval := liftVal_gamma_finite hv hI
      have hx := toVal_finite s e q m hv
      have hni : ∀ k : ℤ, finiteVal s e m ≠ k := fun k hk => by
        rw [(isInteger_finite s e hv).mpr ⟨k, hk⟩] at hI
        exact Bool.noConfusion hI
      have hG0 : Real.Gamma (finiteVal s e m) ≠ 0 := by
        refine Real.Gamma_ne_zero fun n hn => hni (-(n : ℤ)) (by rw [hn]; push_cast; rfl)
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode
        (gammaApprox false (finite s e q m hv) e s)
        (gammaApprox_bracketConv false hx e (pos := s)
          (fun h => by subst h; exact finiteVal_true_pos e hv)
          (fun h => by subst h; exact ⟨finiteVal_false_neg e hv, hni⟩))
        hG0 (hB _ hval) (max 64 (p + 32)) (by omega) (fun w hw => by
          rcases gammaApprox_valid_or_none false hx e (pos := s)
            (fun h => by subst h; exact finiteVal_true_pos e hv)
            (fun h => by subst h; exact finiteVal_false_neg e hv) (w := w)
            (le_trans (le_max_left _ _) hw) p mode with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
          · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
          · exact Or.inr hn)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases gammaPrecRoundFuel_eq_or_loop fuel (finite s e q m hv) p mode with
        h | ⟨-, -, s', e', q', m', hv', heq, h⟩
      · exact h
      · rw [h, hval]
        cases heq
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases gammaPrecRoundFuel_eq_or_loop fuel x p mode with h | ⟨-, hI, s, e, q, m, hv, rfl, -⟩
      · exact h
      · exact absurd ⟨s, e, q, m, hv, rfl, hI⟩ hgen
  dyadic := fun x hx v hv => by
    cases hxv : x.toVal with
    | none => rw [hxv] at hv; exact absurd hv (by simp)
    | some a =>
      rw [hxv, Option.bind_some] at hv
      induction a using EReal.rec with
      | bot => rw [Spec.gamma_bot] at hv; exact absurd hv (by simp)
      | top =>
        rw [Spec.gamma_top, Option.some.injEq] at hv
        exact absurd hv (by simp)
      | coe t =>
        obtain ⟨n, rfl⟩ := hx t hxv
        exact isDyadic_of_gamma_int n hv
  nondyadic := fun x hx => by
    have hx : gammaSpecial x = true := hx
    obtain ⟨s, e, q, m, hv, rfl⟩ := exists_finite_of_gammaSpecial hx
    obtain ⟨r, hr, hden⟩ := gammaSpecial_spec (toVal_finite s e q m hv) hx
    have hirr := irrational_gammaVal false r (by
      rcases hden with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h)))
    rw [hr] at hirr
    have hI : isInteger (finite s e q m hv) = false := by
      unfold gammaSpecial at hx
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hx
      exact hx.2
    exact ⟨_, liftVal_gamma_finite hv hI, not_isDyadic_of_irrational hirr⟩
  correct := fun x hx fuel p _ mode => by
    rcases gammaPrecRoundFuel_eq_or fuel x p mode with h | ⟨-, hc, hI⟩
    · exact h
    · rcases gammaPrecRoundFuel_eq_or_loop fuel x p mode with h | ⟨-, -, s, e, q, m, hv, rfl, -⟩
      · exact h
      · rcases hx with hD | hN
        · obtain ⟨n, hn⟩ := hD _ (toVal_finite s e q m hv)
          rw [(isInteger_finite s e hv).mpr ⟨n, hn⟩] at hI
          exact Bool.noConfusion hI
        · have hN' : gammaSpecial (finite s e q m hv) = true := hN
          rw [hc] at hN'
          exact Bool.noConfusion hN'

/-- `gammaPrecRound` is `gammaPrecRoundFuel` at the fuel `gammaFuel p`. -/
theorem gammaPrecRound_eq_fuel (x : AzFloat) (p : ℕ) (mode : RoundingMode) :
    gammaPrecRound x p mode = gammaPrecRoundFuel (gammaFuel p) x p mode := rfl

/-- The value of `Spec.reciprocalGamma` at a float with a real value. -/
theorem liftVal_reciprocalGamma_coe {x : AzFloat} {t : ℝ} (hx : x.toVal = some (t : EReal)) :
    x.toVal.bind Spec.reciprocalGamma = some (((Real.Gamma t)⁻¹ : ℝ) : EReal) := by
  rw [hx, Option.bind_some, Spec.reciprocalGamma_coe]

/-- **The specification of `1/Γ`** (`ZivSpec`): sound at every fuel; complete in the limit of
the fuel wherever the value is no rounding boundary; and correct at every fuel on the
arguments that are not finite or are integers up to `3` (the values `0`, `1`, `1/2`), on the
integers from `4` on (`1/(n − 1)!` is not dyadic) and on the quarter-integers. -/
theorem reciprocalGammaPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.reciprocalGamma) reciprocalGammaPrecRoundFuel
      {x | ∀ v : ℝ, x.toVal = some (v : EReal) → ∃ n : ℤ, v = n ∧ n ≤ 3}
      {x | gammaSpecial x = true ∨ ∃ n : ℤ, 4 ≤ n ∧ x.toVal = some (((n : ℝ) : ℝ) : EReal)} where
  sound := fun fuel x p _ mode =>
    (reciprocalGammaPrecRoundFuel_eq_or fuel x p mode).imp_right And.left
  complete := fun x p _ mode hB => by
    by_cases hgen : ∃ (s : Bool) (e : AzInt) (q : ℕ) (m : AzNat) (hv : FiniteValid q m),
        x = finite s e q m hv ∧ isInteger x = false
    · obtain ⟨s, e, q, m, hv, rfl, hI⟩ := hgen
      have hx := toVal_finite s e q m hv
      have hval := liftVal_reciprocalGamma_coe hx
      have hni : ∀ k : ℤ, finiteVal s e m ≠ k := fun k hk => by
        rw [(isInteger_finite s e hv).mpr ⟨k, hk⟩] at hI
        exact Bool.noConfusion hI
      have hG0 : (Real.Gamma (finiteVal s e m))⁻¹ ≠ 0 := by
        refine inv_ne_zero (Real.Gamma_ne_zero fun n hn => hni (-(n : ℤ)) ?_)
        rw [hn]; push_cast; rfl
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode
        (gammaApprox true (finite s e q m hv) e s)
        (gammaApprox_bracketConv true hx e (pos := s)
          (fun h => by subst h; exact finiteVal_true_pos e hv)
          (fun h => by subst h; exact ⟨finiteVal_false_neg e hv, hni⟩))
        hG0 (hB _ hval) (max 64 (p + 32)) (by omega) (fun w hw => by
          rcases gammaApprox_valid_or_none true hx e (pos := s)
            (fun h => by subst h; exact finiteVal_true_pos e hv)
            (fun h => by subst h; exact finiteVal_false_neg e hv) (w := w)
            (le_trans (le_max_left _ _) hw) p mode with ⟨lv, hv', h1, h2, h3, h4, -⟩ | hn
          · exact Or.inl ⟨lv, hv', h1, h2, h3, h4⟩
          · exact Or.inr hn)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases reciprocalGammaPrecRoundFuel_eq_or_loop fuel (finite s e q m hv) p mode with
        h | ⟨-, -, s', e', q', m', hv', heq, h⟩
      · exact h
      · rw [h, hval]
        cases heq
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases reciprocalGammaPrecRoundFuel_eq_or_loop fuel x p mode with
        h | ⟨-, hI, s, e, q, m, hv, rfl, -⟩
      · exact h
      · exact absurd ⟨s, e, q, m, hv, rfl, hI⟩ hgen
  dyadic := fun x hx v hv => by
    cases hxv : x.toVal with
    | none => rw [hxv] at hv; exact absurd hv (by simp)
    | some a =>
      rw [hxv, Option.bind_some] at hv
      induction a using EReal.rec with
      | bot => rw [Spec.reciprocalGamma_bot] at hv; exact absurd hv (by simp)
      | top =>
        rw [Spec.reciprocalGamma_top, Option.some.injEq] at hv
        have : v = 0 := by exact_mod_cast hv.symm
        rw [this]
        exact isDyadic_zero
      | coe t =>
        obtain ⟨n, rfl, hn3⟩ := hx t hxv
        rw [Spec.reciprocalGamma_coe, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
        rw [← hv]
        exact isDyadic_reciprocalGamma_int hn3
  nondyadic := fun x hx => by
    rcases hx with hx | ⟨n, hn, hx⟩
    · obtain ⟨s, e, q, m, hv, rfl⟩ := exists_finite_of_gammaSpecial hx
      obtain ⟨r, hr, hden⟩ := gammaSpecial_spec (toVal_finite s e q m hv) hx
      have hirr := irrational_gammaVal true r (by
        rcases hden with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h)))
      rw [hr] at hirr
      exact ⟨_, liftVal_reciprocalGamma_coe (toVal_finite s e q m hv),
        not_isDyadic_of_irrational hirr⟩
    · exact ⟨_, liftVal_reciprocalGamma_coe hx, not_isDyadic_reciprocalGamma_int hn⟩
  correct := fun x hx fuel p _ mode => by
    rcases reciprocalGammaPrecRoundFuel_eq_or fuel x p mode with h | ⟨-, hc, hI⟩
    · exact h
    · rcases reciprocalGammaPrecRoundFuel_eq_or_loop fuel x p mode with
        h | ⟨-, -, s, e, q, m, hv, rfl, -⟩
      · exact h
      · have hxv := toVal_finite s e q m hv
        rcases hx with hD | hN | ⟨n, -, hn⟩
        · obtain ⟨n, hn, -⟩ := hD _ hxv
          rw [(isInteger_finite s e hv).mpr ⟨n, hn⟩] at hI
          exact Bool.noConfusion hI
        · rw [hc] at hN
          exact Bool.noConfusion hN
        · rw [hxv, Option.some.injEq, EReal.coe_eq_coe_iff] at hn
          rw [(isInteger_finite s e hv).mpr ⟨n, hn⟩] at hI
          exact Bool.noConfusion hI

/-- `reciprocalGammaPrecRound` is `reciprocalGammaPrecRoundFuel` at the fuel `gammaFuel p`. -/
theorem reciprocalGammaPrecRound_eq_fuel (x : AzFloat) (p : ℕ) (mode : RoundingMode) :
    reciprocalGammaPrecRound x p mode = reciprocalGammaPrecRoundFuel (gammaFuel p) x p mode :=
  rfl

end Azurite.AzFloat
