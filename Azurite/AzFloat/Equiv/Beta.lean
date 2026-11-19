/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Equiv.SumProduct
import Azurite.AzFloat.Beta
import Azurite.AzFloat.Equiv.BetaBracket
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

/-- A float that is not an integer is a finite one, below `2` to its precision. -/
theorem abs_lt_of_not_isInteger {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hni : ¬ isInteger x = true) : |xv| < (2 : ℝ) ^ (x.precision?.getD 1) := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero => exact absurd rfl hni
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
    rw [← hx]
    have hqe : e.toInt < q := by
      by_contra hcon
      push Not at hcon
      apply hni
      simp only [isInteger, Bool.or_eq_true, decide_eq_true_eq, AzInt.le_iff_toInt_le,
        toInt_toAzInt, AzNat.toNat_ofNat]
      exact Or.inl hcon
    have hb := (abs_finiteVal_bounds s e hv).2
    show |finiteVal s e m| < (2 : ℝ) ^ q
    refine lt_of_lt_of_le hb ?_
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) hqe.le

/-- **`sumIsNonposInt` decides whether `a + b` is a non-positive integer.** -/
theorem sumIsNonposInt_iff {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) :
    sumIsNonposInt a b = true ↔ av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k := by
  unfold sumIsNonposInt
  have hnb : (-b).toVal = some ((-bv : ℝ) : EReal) := by
    rw [toVal_neg, hb, Option.map_some, EReal.coe_neg]
  by_cases hia : isInteger a = true
  · rw [ite_eq_left hia, Bool.and_eq_true, isInteger_iff_of_toVal hb, le_eq_true_iff ha hnb]
    obtain ⟨na, hna⟩ := (isInteger_iff_of_toVal ha).mp hia
    constructor
    · rintro ⟨⟨nb, hnb'⟩, hle⟩
      exact ⟨by linarith, na + nb, by rw [hna, hnb']; push_cast; ring⟩
    · rintro ⟨hle, k, hk⟩
      exact ⟨⟨k - na, by push_cast; linarith⟩, by linarith⟩
  · rw [ite_eq_right hia]
    by_cases hib : isInteger b = true
    · rw [ite_eq_left hib]
      obtain ⟨nb, hnb'⟩ := (isInteger_iff_of_toVal hb).mp hib
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨-, k, hk⟩
        exact absurd ((isInteger_iff_of_toVal ha).mpr ⟨k - nb, by push_cast; linarith⟩) hia
    · rw [ite_eq_right hib]
      dsimp only
      set P := a.precision?.getD 1 + b.precision?.getD 1 + 2 with hP
      have : NeZero P := ⟨by omega⟩
      have hr : addPrecRound a b P .Nearest
          = roundVal P .Nearest (some ((av + bv : ℝ) : EReal)) := by
        rw [addPrecRound_eq_liftVal₂, liftVal₂, ha, hb, Option.bind_some, Option.bind_some,
          Spec.add_coe_coe]
      rw [hr]
      obtain ⟨h1, h2⟩ := roundVal_coe P .Nearest (av + bv)
      constructor
      · intro h
        split_ifs at h with heq
        rw [Bool.and_eq_true] at h
        rw [h2, compare_eq_iff_eq] at heq
        rw [heq] at h1
        exact ⟨(le_eq_true_iff h1 toVal_zero').mp h.2, (isInteger_iff_of_toVal h1).mp h.1⟩
      · rintro ⟨hle, k, hk⟩
        have hba := abs_lt_of_not_isInteger ha hia
        have hbb := abs_lt_of_not_isInteger hb hib
        have hkabs : |k| ≤ 2 ^ P := by
          have h3 : |(k : ℝ)| < (2 : ℝ) ^ P := by
            rw [← hk]
            have hpa : (2 : ℝ) ^ (a.precision?.getD 1) ≤ 2 ^ (P - 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have hpb : (2 : ℝ) ^ (b.precision?.getD 1) ≤ 2 ^ (P - 1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have hPP : (2 : ℝ) ^ P = 2 * 2 ^ (P - 1) := by
              rw [← pow_succ', show P - 1 + 1 = P by omega]
            calc |av + bv| ≤ |av| + |bv| := abs_add_le _ _
              _ < 2 ^ P := by linarith
          have h4 : ((|k| : ℤ) : ℝ) < ((2 ^ P : ℤ) : ℝ) := by push_cast; exact h3
          exact (Int.cast_lt.mp h4).le
        have hmem := mem_floatSet_mul_zpow P k 0 hkabs
        rw [zpow_zero, mul_one, ← hk] at hmem
        obtain ⟨m1, m2⟩ := roundVal_of_mem P .Nearest (av + bv) hmem
        rw [ite_eq_left m2, Bool.and_eq_true]
        exact ⟨(isInteger_iff_of_toVal m1).mpr ⟨k, hk⟩, (le_eq_true_iff m1 toVal_zero').mpr hle⟩

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

/-- **`betaReal` is the correct rounding of `Spec.beta` on finite arguments, or the fuel ran
out.** -/
theorem betaReal_eq_or {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaReal a b p mode = roundVal p mode (Spec.beta (av : EReal) (bv : EReal)) ∨
      betaReal a b p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold betaReal
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
  rw [ite_eq_right hzero, ite_eq_right hp]
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
    rw [ite_eq_left hs]
    obtain ⟨hle, k, hk⟩ := (sumIsNonposInt_iff ha hb).mp hs
    have hG := gamma_eq_zero_of_nonpos_int hle hk
    rw [hG, div_zero, EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right hs]
  rcases eq_or_ne (zivLoop (betaApprox a b) p mode (gammaFuel p) (max 64 (p + 32)))
    (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApproxOf_valid_or_none
        (fun _ _ hc => betaCore_spec ha hb hw hc) w p mode)
      _ _ (le_max_left _ _) hz

/-- `betaInfinite` is the rounding of `B(+∞, y)` for a real `y`. -/
theorem betaInfinite_eq {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    betaInfinite y = roundVal p mode (if 0 < yv then some 0 else none) := by
  unfold betaInfinite
  by_cases h : 0 < yv
  · rw [ite_eq_left ((lt_eq_true_iff toVal_zero' hy).mpr h), ite_eq_left h, roundVal_zero]
  · rw [ite_eq_right (fun h' => h ((lt_eq_true_iff toVal_zero' hy).mp h')), ite_eq_right h,
      roundVal_none]

/-- **`B` is correctly rounded, or the fuel ran out.** -/
theorem betaPrecRound_eq_or (a b : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    betaPrecRound a b p mode = liftVal₂ Spec.beta a b p mode ∨
      betaPrecRound a b p mode = (nan, .eq) := by
  have hz : zero.toVal = some ((0 : ℝ) : EReal) := toVal_zero'
  cases a with
  | nan => left; cases b <;> rfl
  | infinity sa =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sa <;> cases sb <;>
        simp [betaPrecRound, betaInfinite, liftVal₂, Spec.beta_bot_left, Spec.beta_bot_right,
          Spec.beta_top_top, lt, partialCompare]
    | zero =>
      left
      cases sa
      · simp [betaPrecRound, liftVal₂, Spec.beta_bot_left]
      · simp only [betaPrecRound, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some, hz,
          Spec.beta_top_coe]
        exact betaInfinite_eq hz p mode
    | finite s e q m hv =>
      left
      cases sa
      · simp [betaPrecRound, liftVal₂, Spec.beta_bot_left]
      · simp only [betaPrecRound, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.beta_top_coe]
        exact betaInfinite_eq (toVal_finite s e q m hv) p mode
  | zero =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [betaPrecRound, liftVal₂, Spec.beta_bot_right]
      · simp only [betaPrecRound, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some, hz,
          Spec.beta_coe_top]
        exact betaInfinite_eq hz p mode
    | zero =>
      simp only [betaPrecRound, liftVal₂, hz, Option.bind_some]
      exact betaReal_eq_or hz hz p mode
    | finite s e q m hv =>
      simp only [betaPrecRound, liftVal₂, hz, toVal_finite, Option.bind_some]
      exact betaReal_eq_or hz (toVal_finite s e q m hv) p mode
  | finite s e q m hv =>
    cases b with
    | nan => left; rfl
    | infinity sb =>
      left
      cases sb
      · simp [betaPrecRound, liftVal₂, Spec.beta_bot_right]
      · simp only [betaPrecRound, ↓reduceIte, liftVal₂, toVal_infinity, Option.bind_some,
          toVal_finite, Spec.beta_coe_top]
        exact betaInfinite_eq (toVal_finite s e q m hv) p mode
    | zero =>
      simp only [betaPrecRound, liftVal₂, hz, toVal_finite, Option.bind_some]
      exact betaReal_eq_or (toVal_finite s e q m hv) hz p mode
    | finite s' e' q' m' hv' =>
      simp only [betaPrecRound, liftVal₂, toVal_finite, Option.bind_some]
      exact betaReal_eq_or (toVal_finite s e q m hv) (toVal_finite s' e' q' m' hv') p mode

end Azurite.AzFloat
