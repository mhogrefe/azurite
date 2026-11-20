/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Equiv.SumProduct
import Azurite.AzFloat.Beta
import Azurite.AzFloat.Equiv.BetaBracket
import Azurite.AzFloat.Equiv.ZivSpec
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzFloat.Equiv.Add
import Azurite.AzFloat.Equiv.Div
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzNat.Equiv.Factorial
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.LogBase2
import Azurite.AzNat.Equiv.Gcd.HalfBinary
import Azurite.AzInt.Equiv.Pow
import Azurite.AzFloat.Equiv.RatPow

/-!
# Equivalence: the Beta function

`Spec.beta : EReal → EReal → Option EReal` is the exact function on the extended reals (`none`
is `NaN`), and `betaPrecRound_eq_or` says that `betaPrecRound a b p mode` is its correct
rounding, or `(nan, .eq)` when the fuel of the Ziv loop runs out.  On finite arguments off the
special values, `Spec.beta` is `Γ(a) Γ(b) / Γ(a + b)` with Mathlib's `Real.Gamma`, which is `0`
at the poles: the quotient is `0` exactly when `a + b` is a non-positive integer.

The steps: `isInteger_iff_of_toVal`, `sumIsNonposInt_iff` (the exact decision whether `a + b`
is a non-positive integer), `betaReal_eq_or`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- `B` on the extended reals.  `NaN` at `−∞` and when an argument is a negative integer;
`B(+∞, b) = 0` for `b > 0`; `+∞` when an argument is `0`; otherwise `Γ(a) Γ(b) / Γ(a + b)`
(`0` when `a + b` is a non-positive integer). -/
noncomputable def beta (a b : EReal) : Option EReal :=
  if a = ⊥ ∨ b = ⊥ then none
  else if a = ⊤ then (if 0 < b then some 0 else none)
  else if b = ⊤ then (if 0 < a then some 0 else none)
  else if (a.toReal < 0 ∧ ∃ k : ℤ, a.toReal = k) ∨ (b.toReal < 0 ∧ ∃ k : ℤ, b.toReal = k)
  then none
  else if a.toReal = 0 ∨ b.toReal = 0 then some ⊤
  else some ((Real.Gamma a.toReal * Real.Gamma b.toReal / Real.Gamma (a.toReal + b.toReal) :
    ℝ) : EReal)

theorem beta_bot_left (b : EReal) : beta ⊥ b = none := by simp [beta]

theorem beta_bot_right (a : EReal) : beta a ⊥ = none := by simp [beta]

theorem beta_top_coe (yv : ℝ) :
    beta ⊤ (yv : EReal) = if 0 < yv then some 0 else none := by
  unfold beta
  rw [ite_eq_right (by simp), ite_eq_left rfl]
  simp only [EReal.coe_pos]

theorem beta_coe_top (xv : ℝ) :
    beta (xv : EReal) ⊤ = if 0 < xv then some 0 else none := by
  unfold beta
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _), ite_eq_left rfl]
  simp only [EReal.coe_pos]

theorem beta_top_top : beta ⊤ ⊤ = some 0 := by simp [beta]

theorem beta_coe_of_pole {xv yv : ℝ}
    (h : (xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)) :
    beta (xv : EReal) (yv : EReal) = none := by
  unfold beta
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_left h]

theorem beta_coe_of_zero {xv yv : ℝ}
    (hnp : ¬ ((xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)))
    (h0 : xv = 0 ∨ yv = 0) : beta (xv : EReal) (yv : EReal) = some ⊤ := by
  unfold beta
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_right hnp,
    ite_eq_left h0]

theorem beta_coe {xv yv : ℝ}
    (hnp : ¬ ((xv < 0 ∧ ∃ k : ℤ, xv = k) ∨ (yv < 0 ∧ ∃ k : ℤ, yv = k)))
    (h0 : ¬ (xv = 0 ∨ yv = 0)) :
    beta (xv : EReal) (yv : EReal)
      = some ((Real.Gamma xv * Real.Gamma yv / Real.Gamma (xv + yv) : ℝ) : EReal) := by
  unfold beta
  rw [ite_eq_right (by simp), ite_eq_right (EReal.coe_ne_top _),
    ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe, EReal.toReal_coe, ite_eq_right hnp,
    ite_eq_right h0]

end Spec

/-! ### The tests on values -/

theorem isZeroVal_iff {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    isZeroVal x = true ↔ xv = 0 := by
  unfold isZeroVal
  rw [Bool.and_eq_true, le_eq_true_iff hx toVal_zero', le_eq_true_iff toVal_zero' hx]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem isOneVal_iff {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    isOneVal x = true ↔ xv = 1 := by
  unfold isOneVal
  rw [Bool.and_eq_true, le_eq_true_iff hx toVal_one', le_eq_true_iff toVal_one' hx]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem isNegInt_iff {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    isNegInt x = true ↔ xv < 0 ∧ ∃ k : ℤ, xv = k := by
  unfold isNegInt
  rw [Bool.and_eq_true, lt_eq_true_iff hx toVal_zero', isInteger_iff_of_toVal hx]

/-! ### The driver -/

/-- `B(a, 1) = 1/a` off the poles of `Γ`. -/
theorem gamma_mul_gamma_one_div {xv : ℝ} (h0 : xv ≠ 0) (hnp : ¬ (xv < 0 ∧ ∃ k : ℤ, xv = k)) :
    Real.Gamma xv * Real.Gamma 1 / Real.Gamma (xv + 1) = 1 / xv := by
  have hG : Real.Gamma xv ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff xv).mp h
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact h0 (by simpa using hm)
    · refine hnp ⟨?_, -(m : ℤ), by rw [hm]; push_cast; rfl⟩
      have : (0 : ℝ) < m := by exact_mod_cast hm0
      linarith
  rw [Real.Gamma_one, mul_one, Real.Gamma_add_one h0]
  field_simp

/-! ### `B(a, n)` for a small positive integer `n` -/

/-- `Γ(x + n) = Γ(x) · x (x + 1) ⋯ (x + n − 1)` off the poles of `Γ`. -/
theorem gamma_add_nat_of_ne {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ j ∈ Finset.range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : x + n ≠ 0 := fun h => hx n (by linarith)
    rw [Finset.prod_range_succ, show x + ((n + 1 : ℕ) : ℝ) = (x + n) + 1 by push_cast; ring,
      Real.Gamma_add_one hne, ih]
    ring

/-- `B(x, n) = (n − 1)! / (x (x + 1) ⋯ (x + n − 1))` for `n ≥ 1`, off the poles of `Γ`. -/
theorem beta_nat_eq {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) {n : ℕ} (hn : 1 ≤ n) :
    Real.Gamma x * Real.Gamma n / Real.Gamma (x + n)
      = ((n - 1).factorial : ℝ) / ∏ j ∈ Finset.range n, (x + j) := by
  have hG := Real.Gamma_ne_zero hx
  have hP : ∏ j ∈ Finset.range n, (x + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ h => hx j (by linarith)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [gamma_add_nat_of_ne hx, show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; rfl,
    Real.Gamma_nat_eq_factorial, Nat.add_sub_cancel]
  field_simp

theorem toInt_risingInt (N D : AzInt) (n : ℕ) :
    (risingInt N D n).toInt = ∏ j ∈ Finset.range n, (N.toInt + j * D.toInt) := by
  rw [risingInt, AzInt.toInt_product, List.map_map]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ,
      List.map_singleton, List.prod_singleton, Function.comp_apply, AzInt.toInt_add,
      AzInt.toInt_mul, AzInt.toInt_natCast]

/-- `(n − 1)! Dⁿ / ∏ (N + j D) = (n − 1)! / ∏ (N/D + j)`. -/
theorem factorial_mul_pow_div_prod {N D : ℝ} (hD : D ≠ 0) (c : ℝ) (n : ℕ) :
    c * D ^ n / ∏ j ∈ Finset.range n, (N + j * D) = c / ∏ j ∈ Finset.range n, (N / D + j) := by
  have hterm : ∀ j ∈ Finset.range n, N / D + (j : ℝ) = (N + j * D) / D := fun j _ => by
    field_simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    div_div_eq_mul_div]

/-- A real that is neither `0` nor a negative integer is not minus a natural number. -/
theorem ne_neg_nat_of_not_pole {av : ℝ} (ha0 : av ≠ 0) (hnp : ¬ (av < 0 ∧ ∃ k : ℤ, av = k)) :
    ∀ m : ℕ, av ≠ -m := by
  intro m hm
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact ha0 (by simpa using hm)
  · refine hnp ⟨?_, -(m : ℤ), by rw [hm]; push_cast; rfl⟩
    have : (0 : ℝ) < m := by exact_mod_cast hm0
    linarith

/-- `Γ` vanishes (in Mathlib's convention) at the non-positive integers. -/
theorem gamma_eq_zero_of_nonpos_int {sv : ℝ} (hle : sv ≤ 0) {k : ℤ} (hk : sv = k) :
    Real.Gamma sv = 0 := by
  rw [Real.Gamma_eq_zero_iff]
  refine ⟨(-k).toNat, ?_⟩
  have hk0 : k ≤ 0 := by exact_mod_cast (hk ▸ hle : (k : ℝ) ≤ 0)
  rw [hk]
  have : (((-k).toNat : ℤ) : ℝ) = -(k : ℝ) := by
    rw [Int.toNat_of_nonneg (by omega)]; push_cast; rfl
  rw [show (((-k).toNat : ℕ) : ℝ) = (((-k).toNat : ℤ) : ℝ) by push_cast; rfl, this, neg_neg]

/-- **`betaIntQuot N D n` is the rounding of `B(N/D, n)`**, `n ≥ 1`, off the poles. -/
theorem betaIntQuot_eq {N D : AzInt} {av : ℝ} (hD : (0 : ℝ) < (D.toInt : ℝ))
    (hN : (N.toInt : ℝ) / (D.toInt : ℝ) = av) (hx : ∀ m : ℕ, av ≠ -m) {n : ℕ} (hn : 1 ≤ n)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaIntQuot N D n p mode = roundVal p mode
      (some ((Real.Gamma av * Real.Gamma n / Real.Gamma (av + n) : ℝ) : EReal)) := by
  have hPne : ((risingInt N D n).toInt : ℝ) ≠ 0 := by
    rw [toInt_risingInt]
    push_cast
    refine Finset.prod_ne_zero_iff.mpr fun j _ h0 => hx j ?_
    rw [← hN]
    field_simp
    linarith
  unfold betaIntQuot
  rw [divPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzInt, toVal_ofAzInt, Option.bind_some,
    Option.bind_some, Spec.div_coe_coe _ _ hPne, beta_nat_eq hx hn]
  congr 3
  rw [AzInt.toInt_mul, AzInt.toInt_pow, toInt_risingInt, AzRat.toInt_toAzInt',
    AzNat.toNat_factorial, ← hN]
  push_cast
  exact factorial_mul_pow_div_prod hD.ne' _ n

/-- **The exact path answers with the rounding of `B(a, b)`.** -/
theorem betaSmallInt?_eq {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (ha0 : av ≠ 0) (hnp : ¬ (av < 0 ∧ ∃ k : ℤ, av = k))
    (p : ℕ) [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : betaSmallInt? a b p mode = some r) :
    r = roundVal p mode
      (some ((Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) : ℝ) : EReal)) := by
  unfold betaSmallInt? at h
  split_ifs at h with hc
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hint, hpos⟩, -⟩, -⟩ := hc
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  have hav := toVal_of_toAzRat? a q hq
  rw [ha, Option.some.injEq, EReal.coe_eq_coe_iff] at hav
  rw [lt_eq_true_iff toVal_zero' hb] at hpos
  obtain ⟨k, hk⟩ := (isInteger_iff_of_toVal hb).mp hint
  -- the truncation of an integer is that integer
  obtain ⟨ht, -⟩ := truncToAzInt_spec hb
  have hkt : (truncToAzInt b).toInt = k := by
    rw [hk, ← Int.cast_sub, ← Int.cast_abs] at ht
    have : |(truncToAzInt b).toInt - k| < 1 := by exact_mod_cast ht
    have := abs_lt.mp this
    omega
  have hk0 : 0 < k := by exact_mod_cast (hk ▸ hpos : (0 : ℝ) < (k : ℝ))
  set n := (truncToAzInt b).abs.toNat with hn
  have hnk : (n : ℤ) = k := by rw [hn, AzInt.abs_toNat_eq, hkt, abs_of_pos hk0]
  have hbn : bv = (n : ℕ) := by rw [hk]; exact_mod_cast hnk.symm
  have hn1 : 1 ≤ n := by omega
  have hden : (0 : ℝ) < q.den.toNat := den_pos_real q
  have hN : ((AzInt.mkNorm q.sign q.num).toInt : ℝ) / ((q.den.toAzInt).toInt : ℝ) = av := by
    rw [hav, coe_toRat_eq_sign_mul, AzNat.toInt_mkNorm, AzRat.toInt_toAzInt']
    cases q.sign <;> simp [neg_div]
  dsimp only
  rw [hbn]
  exact betaIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast hden) hN
    (ne_neg_nat_of_not_pole ha0 hnp) hn1 p mode

/-- **`betaRealFuel` on finite arguments**: the correct rounding of `Spec.beta`, or the
general case — neither a special value nor an argument with a known irrational value — where
it is the loop with fuel. -/
theorem betaRealFuel_eq_or_loop (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaRealFuel fuel a b p mode = roundVal p mode (Spec.beta (av : EReal) (bv : EReal)) ∨
      (¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) ∧ av ≠ 0 ∧ bv ≠ 0 ∧
        ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k) ∧ betaSpecial a b = false ∧
        betaRealFuel fuel a b p mode
          = zivLoop (betaApprox a b) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold betaRealFuel
  by_cases hpole : (isNegInt a || isNegInt b) = true
  · left
    rw [ite_eq_left hpole]
    rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb] at hpole
    rw [Spec.beta_coe_of_pole hpole, roundVal_none]
  rw [ite_eq_right hpole]
  rw [Bool.or_eq_true, isNegInt_iff ha, isNegInt_iff hb] at hpole
  by_cases hzero : (isZeroVal a || isZeroVal b) = true
  · left
    rw [ite_eq_left hzero]
    rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb] at hzero
    rw [Spec.beta_coe_of_zero hpole hzero, roundVal_top]
  rw [ite_eq_right hzero, dite_eq_right hp]
  rw [Bool.or_eq_true, isZeroVal_iff ha, isZeroVal_iff hb] at hzero
  rw [Spec.beta_coe hpole hzero]
  push Not at hzero
  obtain ⟨ha0, hb0⟩ := hzero
  by_cases hb1 : isOneVal b = true
  · left
    rw [ite_eq_left hb1, (isOneVal_iff hb).mp hb1,
      gamma_mul_gamma_one_div ha0 (fun h => hpole (Or.inl h)), divPrecRound_eq_liftVal₂,
      liftVal₂, toVal_one', ha, Option.bind_some, Option.bind_some, Spec.div_coe_coe 1 av ha0]
  rw [ite_eq_right hb1]
  by_cases ha1 : isOneVal a = true
  · left
    have hv : Real.Gamma 1 * Real.Gamma bv / Real.Gamma (1 + bv) = 1 / bv := by
      rw [mul_comm, add_comm]
      exact gamma_mul_gamma_one_div hb0 (fun h => hpole (Or.inr h))
    rw [ite_eq_left ha1, (isOneVal_iff ha).mp ha1, hv, divPrecRound_eq_liftVal₂,
      liftVal₂, toVal_one', hb, Option.bind_some, Option.bind_some, Spec.div_coe_coe 1 bv hb0]
  rw [ite_eq_right ha1]
  split
  · next r hr =>
    left
    exact betaSmallInt?_eq ha hb ha0 (fun h => hpole (Or.inl h)) p mode hr
  split
  · next r hr =>
    left
    have := betaSmallInt?_eq hb ha hb0 (fun h => hpole (Or.inr h)) p mode hr
    rw [this, mul_comm (Real.Gamma bv), add_comm bv]
  by_cases hs : sumIsNonposInt a b = true
  · left
    rw [dite_eq_left hs]
    obtain ⟨hle, k, hk⟩ := (sumIsNonposInt_iff ha hb).mp hs
    have hG := gamma_eq_zero_of_nonpos_int hle hk
    rw [hG, div_zero, EReal.coe_zero, roundVal_zero]
  rw [dite_eq_right hs]
  by_cases hc : betaSpecial a b = true
  · left
    rw [dite_eq_left hc]
    exact zivLoopBacked_eq p mode (betaApprox a b)
      (not_mem_floatSet_of_irrational p (irrational_beta_of_special ha hb hc hs)) 64
      (fun w hw => (gammaApproxOf_valid_or_none
        (fun _ _ hc' => betaCore_spec ha hb hw hc') w p mode).imp_left
          fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
      fuel _ (le_max_left _ _) (by omega) _
  · right
    rw [dite_eq_right hc]
    exact ⟨hpole, ha0, hb0, fun h => hs ((sumIsNonposInt_iff ha hb).mpr h), by simpa using hc,
      rfl⟩

/-- The bracket of `B(a, b)` is valid, or rejected. -/
theorem betaApprox_valid_or_none {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (betaApprox a b w).1 lv ∧ Rounds (betaApprox a b w).2 hv ∧
        lv ≤ Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) ∧
        Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) ≤ hv ∧
        (lv = Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) →
          hv = Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv))) ∨
      roundingPossible (betaApprox a b w).1 (betaApprox a b w).2 p mode = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => betaCore_spec ha hb hw hc) w p mode

/-- **`betaRealFuel` is the correct rounding of `Spec.beta` on finite arguments, or the fuel
ran out.** -/
theorem betaRealFuel_eq_or (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaRealFuel fuel a b p mode = roundVal p mode (Spec.beta (av : EReal) (bv : EReal)) ∨
      betaRealFuel fuel a b p mode = (nan, .eq) := by
  rcases betaRealFuel_eq_or_loop fuel ha hb p mode with h | ⟨hpole, ha0, hb0, -, -, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (betaRealFuel fuel a b p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      rw [h] at hz ⊢
      rw [Spec.beta_coe hpole (by push Not; exact ⟨ha0, hb0⟩)]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => betaApprox_valid_or_none ha hb hw p mode) _ _ (le_max_left _ _) hz

/-- **`betaReal` is the correct rounding of `Spec.beta` on finite arguments, or the fuel ran
out.** -/
theorem betaReal_eq_or {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaReal a b p mode = roundVal p mode (Spec.beta (av : EReal) (bv : EReal)) ∨
      betaReal a b p mode = (nan, .eq) :=
  betaRealFuel_eq_or (gammaFuel p) ha hb p mode

/-- `betaInfinite` is the rounding of `B(+∞, y)` for a real `y`. -/
theorem betaInfinite_eq {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    betaInfinite y = roundVal p mode (if 0 < yv then some 0 else none) := by
  unfold betaInfinite
  by_cases h : 0 < yv
  · rw [ite_eq_left ((lt_eq_true_iff toVal_zero' hy).mpr h), ite_eq_left h, roundVal_zero]
  · rw [ite_eq_right (fun h' => h ((lt_eq_true_iff toVal_zero' hy).mp h')), ite_eq_right h,
      roundVal_none]

/-- **`B` is correctly rounded, or it is the loop with fuel** on finite arguments in the
general case. -/
theorem betaPrecRoundFuel_eq_or_loop (fuel : ℕ) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaPrecRoundFuel fuel a b p mode = liftVal₂ Spec.beta a b p mode ∨
      ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal) ∧
        ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) ∧ av ≠ 0 ∧ bv ≠ 0 ∧
        ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k) ∧ betaSpecial a b = false ∧
        betaPrecRoundFuel fuel a b p mode
          = zivLoop (betaApprox a b) p mode fuel (max 64 (p + 32)) := by
  have key : ∀ {a b : AzFloat} {av bv : ℝ}, a.toVal = some (av : EReal) →
      b.toVal = some (bv : EReal) →
      betaPrecRoundFuel fuel a b p mode = betaRealFuel fuel a b p mode →
      (betaPrecRoundFuel fuel a b p mode = liftVal₂ Spec.beta a b p mode ∨
        ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal) ∧
          ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) ∧ av ≠ 0 ∧ bv ≠ 0 ∧
          ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k) ∧ betaSpecial a b = false ∧
          betaPrecRoundFuel fuel a b p mode
            = zivLoop (betaApprox a b) p mode fuel (max 64 (p + 32))) := by
    intro a b av bv ha hb heq
    rw [heq]
    rcases betaRealFuel_eq_or_loop fuel ha hb p mode with h | ⟨h1, h2, h3, h4, h5, h6⟩
    · left
      rw [h, liftVal₂, ha, hb, Option.bind_some, Option.bind_some]
    · exact Or.inr ⟨av, bv, ha, hb, h1, h2, h3, h4, h5, h6⟩
  have hz : zero.toVal = some ((0 : ℝ) : EReal) := toVal_zero'
  cases a with
  | nan => left; cases b <;> rfl
  | infinity sa =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sa <;> cases sb <;>
        simp [betaPrecRoundFuel, betaInfinite, liftVal₂, Spec.beta_bot_left, Spec.beta_bot_right,
          Spec.beta_top_top, lt, partialCompare]
    | zero =>
      left
      cases sa
      · simp [betaPrecRoundFuel, liftVal₂, Spec.beta_bot_left]
      · simp only [betaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some, hz,
          Spec.beta_top_coe]
        exact betaInfinite_eq hz p mode
    | finite s e q m hv =>
      left
      cases sa
      · simp [betaPrecRoundFuel, liftVal₂, Spec.beta_bot_left]
      · simp only [betaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.beta_top_coe]
        exact betaInfinite_eq (toVal_finite s e q m hv) p mode
  | zero =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [betaPrecRoundFuel, liftVal₂, Spec.beta_bot_right]
      · simp only [betaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some, hz,
          Spec.beta_coe_top]
        exact betaInfinite_eq hz p mode
    | zero =>
      exact key hz hz rfl
    | finite s e q m hv =>
      exact key hz (toVal_finite s e q m hv) rfl
  | finite s e q m hv =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [betaPrecRoundFuel, liftVal₂, Spec.beta_bot_right]
      · simp only [betaPrecRoundFuel, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.beta_coe_top]
        exact betaInfinite_eq (toVal_finite s e q m hv) p mode
    | zero =>
      exact key (toVal_finite s e q m hv) hz rfl
    | finite s' e' q' m' hv' =>
      exact key (toVal_finite s e q m hv) (toVal_finite s' e' q' m' hv') rfl

/-- **`B` is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem betaPrecRoundFuel_eq_or (fuel : ℕ) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    betaPrecRoundFuel fuel a b p mode = liftVal₂ Spec.beta a b p mode ∨
      betaPrecRoundFuel fuel a b p mode = (nan, .eq) := by
  rcases betaPrecRoundFuel_eq_or_loop fuel a b p mode with
    h | ⟨av, bv, ha, hb, hpole, ha0, hb0, -, -, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (betaPrecRoundFuel fuel a b p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      rw [h] at hz ⊢
      rw [liftVal₂, ha, hb, Option.bind_some, Option.bind_some,
        Spec.beta_coe hpole (by push Not; exact ⟨ha0, hb0⟩)]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => betaApprox_valid_or_none ha hb hw p mode) _ _ (le_max_left _ _) hz

/-- **`B` is correctly rounded, or the fuel ran out.** -/
theorem betaPrecRound_eq_or (a b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaPrecRound a b p mode = liftVal₂ Spec.beta a b p mode ∨
      betaPrecRound a b p mode = (nan, .eq) :=
  betaPrecRoundFuel_eq_or (gammaFuel p) a b p mode

/-- A real value of `Spec.beta` is `0`, or the value at real arguments off the special
values. -/
theorem Spec.beta_eq_coe_cases {a b : EReal} {v : ℝ} (h : Spec.beta a b = some (v : EReal)) :
    v = 0 ∨ ∃ av bv : ℝ, a = av ∧ b = bv ∧
      ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) ∧ ¬ (av = 0 ∨ bv = 0) ∧
      v = Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) := by
  have h0 : ∀ {o : Option EReal}, o = some ((v : ℝ) : EReal) → o = some 0 → v = 0 := by
    intro o h1 h2
    rw [h1, Option.some.injEq] at h2
    exact_mod_cast h2
  induction a using EReal.rec with
  | bot => rw [Spec.beta_bot_left] at h; exact absurd h (by simp)
  | top =>
    induction b using EReal.rec with
    | bot => rw [Spec.beta_bot_right] at h; exact absurd h (by simp)
    | top => exact Or.inl (h0 h Spec.beta_top_top)
    | coe y =>
      rw [Spec.beta_top_coe] at h
      by_cases hy : 0 < y
      · rw [ite_eq_left hy] at h
        exact Or.inl (h0 h rfl)
      · rw [ite_eq_right hy] at h
        exact absurd h (by simp)
  | coe x =>
    induction b using EReal.rec with
    | bot => rw [Spec.beta_bot_right] at h; exact absurd h (by simp)
    | top =>
      rw [Spec.beta_coe_top] at h
      by_cases hx : 0 < x
      · rw [ite_eq_left hx] at h
        exact Or.inl (h0 h rfl)
      · rw [ite_eq_right hx] at h
        exact absurd h (by simp)
    | coe y =>
      by_cases hpole : (x < 0 ∧ ∃ k : ℤ, x = k) ∨ (y < 0 ∧ ∃ k : ℤ, y = k)
      · rw [Spec.beta_coe_of_pole hpole] at h
        exact absurd h (by simp)
      · by_cases hzero : x = 0 ∨ y = 0
        · rw [Spec.beta_coe_of_zero hpole hzero, Option.some.injEq] at h
          exact absurd h.symm (EReal.coe_ne_top v)
        · rw [Spec.beta_coe hpole hzero, Option.some.injEq, EReal.coe_eq_coe_iff] at h
          exact Or.inr ⟨x, y, rfl, rfl, hpole, hzero, h.symm⟩

/-- **The specification of `B`** (`ZivSpec`): sound at every fuel; complete in the limit of
the fuel wherever the value is no rounding boundary (the bracket converges at every pair of
arguments, `betaApprox_bracketConv`); and correct at every fuel on the special values (`NaN`,
`+∞`, the zeros where `a + b` is a non-positive integer) and on the arguments recognized by
`betaSpecial`, where the value is irrational: `a + b` a positive integer, or `a`, `b`
quarter-integers. -/
theorem betaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun xy : AzFloat × AzFloat => xy.1.toVal.bind fun a => xy.2.toVal.bind fun b =>
        Spec.beta a b)
      (fun fuel xy p mode => betaPrecRoundFuel fuel xy.1 xy.2 p mode)
      {xy | ∀ av bv : ℝ, xy.1.toVal = some (av : EReal) → xy.2.toVal = some (bv : EReal) →
        (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k) ∨ av = 0 ∨ bv = 0 ∨
          (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)}
      {xy | betaSpecial xy.1 xy.2 = true ∧ ¬ sumIsNonposInt xy.1 xy.2 = true} where
  sound := fun fuel xy p _ mode => betaPrecRoundFuel_eq_or fuel xy.1 xy.2 p mode
  complete := fun xy p _ mode hB => by
    by_cases hgen : ∃ av bv : ℝ, xy.1.toVal = some (av : EReal) ∧
        xy.2.toVal = some (bv : EReal) ∧
        ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) ∧ av ≠ 0 ∧ bv ≠ 0 ∧
        ¬ (av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k)
    · obtain ⟨av, bv, ha, hb, hpole, ha0, hb0, hs⟩ := hgen
      have hval : (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.beta a b)
          = some ((Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv) : ℝ) : EReal) := by
        rw [ha, hb, Option.bind_some, Option.bind_some,
          Spec.beta_coe hpole (by push Not; exact ⟨ha0, hb0⟩)]
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (betaApprox xy.1 xy.2)
        (betaApprox_bracketConv ha hb (beta_arg_cases ha0 fun h => hpole (Or.inl h))
          (beta_arg_cases hb0 fun h => hpole (Or.inr h)) (beta_sum_cases hs))
        (ne_zero_of_not_mem_floatSet hB') hB' (max 64 (p + 32)) (by omega)
        (fun w hw =>
          (betaApprox_valid_or_none ha hb (le_trans (le_max_left _ _) hw) p mode).imp_left
            fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases betaPrecRoundFuel_eq_or_loop fuel xy.1 xy.2 p mode with
        h | ⟨-, -, -, -, -, -, -, -, -, h⟩
      · exact h
      · show betaPrecRoundFuel fuel xy.1 xy.2 p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases betaPrecRoundFuel_eq_or_loop fuel xy.1 xy.2 p mode with
        h | ⟨av, bv, ha, hb, h1, h2, h3, h4, -, -⟩
      · exact h
      · exact absurd ⟨av, bv, ha, hb, h1, h2, h3, h4⟩ hgen
  dyadic := fun xy hxy v hv => by
    cases hx : xy.1.toVal with
    | none => rw [hx] at hv; exact absurd hv (by simp)
    | some a' =>
      cases hy : xy.2.toVal with
      | none => rw [hx, hy] at hv; exact absurd hv (by simp)
      | some b' =>
        rw [hx, hy, Option.bind_some, Option.bind_some] at hv
        rcases Spec.beta_eq_coe_cases hv with rfl | ⟨av, bv, rfl, rfl, hpole, hzero, rfl⟩
        · exact isDyadic_zero
        · rcases hxy av bv hx hy with h | h | h | h | ⟨hle, k, hk⟩
          · exact absurd (Or.inl h) hpole
          · exact absurd (Or.inr h) hpole
          · exact absurd (Or.inl h) hzero
          · exact absurd (Or.inr h) hzero
          · rw [gamma_eq_zero_of_nonpos_int hle hk, div_zero]
            exact isDyadic_zero
  nondyadic := fun xy h => by
    obtain ⟨hc, hs⟩ := h
    obtain ⟨av, bv, ha, hb, hia, hib, -⟩ := betaSpecial_spec hc
    have hirr := irrational_beta_of_special ha hb hc hs
    have hpole : ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) := by
      rintro (h | h)
      · exact hia ((isInteger_iff_of_toVal ha).mpr h.2)
      · exact hib ((isInteger_iff_of_toVal hb).mpr h.2)
    have hzero : ¬ (av = 0 ∨ bv = 0) := by
      rintro (h | h)
      · exact hia ((isInteger_iff_of_toVal ha).mpr ⟨0, by simpa using h⟩)
      · exact hib ((isInteger_iff_of_toVal hb).mpr ⟨0, by simpa using h⟩)
    refine ⟨_, ?_, not_isDyadic_of_irrational hirr⟩
    show (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.beta a b) = _
    rw [ha, hb, Option.bind_some, Option.bind_some, Spec.beta_coe hpole hzero]
  correct := fun xy hxy fuel p _ mode => by
    rcases betaPrecRoundFuel_eq_or_loop fuel xy.1 xy.2 p mode with
      h | ⟨av, bv, ha, hb, hpole, ha0, hb0, hs, hc, -⟩
    · exact h
    · exfalso
      rcases hxy with hD | hN
      · rcases hD av bv ha hb with h | h | h | h | h
        · exact hpole (Or.inl h)
        · exact hpole (Or.inr h)
        · exact ha0 h
        · exact hb0 h
        · exact hs h
      · rw [hN.1] at hc
        exact Bool.noConfusion hc

end Azurite.AzFloat
