/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowInt
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Div
import Azurite.AzFloat.Equiv.Mul
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzNat.Equiv.Parity
import Azurite.AzNat.Equiv.Pow

/-!
# Equivalence: `x^n` for an integer `n`

* `Spec.powInt n`: the extended-real `a^n` (`a^0 = 1`; `0^n = +∞` for `n < 0`; `(±∞)^n = 0` for
  `n < 0`, `+∞` or `±∞` by parity for `n > 0`).
* `finiteVal_pow`: `(±m 2^E)^k = (±1)^k m^k 2^(E k)`.
* `powIntPrecRound_eq_liftVal : powIntPrecRound x n p mode = liftVal (Spec.powInt n) x p mode`:
  `x^n` is correctly rounded in every mode, with the exact comparison.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `a^n`: `a^0 = 1`; `(+∞)^n = +∞` and `(−∞)^n = ±∞` by the parity of `n > 0`,
`(±∞)^n = 0` for `n < 0`; `0^n = +∞` for `n < 0`; otherwise the real integer power. -/
noncomputable def powInt (n : ℤ) (a : EReal) : Option EReal :=
  if n = 0 then some 1
  else if a = ⊤ then (if 0 < n then some ⊤ else some 0)
  else if a = ⊥ then (if 0 < n then (if Even n then some ⊤ else some ⊥) else some 0)
  else if a.toReal = 0 ∧ n < 0 then some ⊤
  else some ((a.toReal ^ n : ℝ) : EReal)

theorem powInt_coe (n : ℤ) (r : ℝ) :
    powInt n (r : EReal) = if n = 0 then some 1
      else if r = 0 ∧ n < 0 then some ⊤ else some ((r ^ n : ℝ) : EReal) := by
  unfold powInt
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

theorem powInt_top (n : ℤ) :
    powInt n ⊤ = if n = 0 then some 1 else if 0 < n then some ⊤ else some 0 := by
  unfold powInt
  by_cases h : n = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_left rfl]

theorem powInt_bot (n : ℤ) :
    powInt n ⊥ = if n = 0 then some 1
      else if 0 < n then (if Even n then some ⊤ else some ⊥) else some 0 := by
  unfold powInt
  by_cases h : n = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- `(±m 2^E)^k = (±1)^k m^k 2^(E k)`. -/
theorem finiteVal_pow (s : Bool) (e : AzInt) (m : AzNat) (k : ℕ) :
    finiteVal s e m ^ k
      = (if s then 1 else (-1 : ℝ) ^ k) * (m.toNat : ℝ) ^ k
        * (2 : ℝ) ^ ((e.toInt - m.size) * k) := by
  unfold finiteVal
  rw [mul_pow, mul_pow, ← zpow_natCast ((2 : ℝ) ^ (e.toInt - m.size)), ← zpow_mul]
  cases s <;> simp

/-- The sign `(±1)^k` as a Boolean: negative exactly for `s = false` and odd `k`. -/
theorem sign_pow_eq (s : Bool) (k : ℕ) (b : Bool) (hb : b = true ↔ Odd k) :
    (if s then (1 : ℝ) else (-1 : ℝ) ^ k) = if (!s && b) = true then -1 else 1 := by
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
    by_cases hodd : Odd k
    · rw [Odd.neg_one_pow hodd, ite_eq_left (hb.mpr hodd)]
    · rw [Even.neg_one_pow (Nat.not_odd_iff_even.mp hodd),
        ite_eq_right (fun h => hodd (hb.mp h))]
  · simp

/-- The parity of `|n|` as an `AzNat` is the parity of `n`. -/
theorem abs_isEven_iff (n : AzInt) : n.abs.isEven = true ↔ Even n.toInt := by
  rw [AzNat.isEven_iff, ← Int.even_coe_nat, AzInt.abs_toNat_eq, even_abs]

theorem abs_isOdd_iff (n : AzInt) : n.abs.isOdd = true ↔ Odd n.abs.toNat := AzNat.isOdd_iff _

/-- `n ≠ 0` as an `AzInt` gives `n.toInt ≠ 0`. -/
theorem toInt_ne_zero_of_ne_zero {n : AzInt} (hn : n ≠ 0) : n.toInt ≠ 0 := fun h =>
  hn (by rw [← AzInt.ofInt_toInt n, h, AzInt.ofInt_zero])

/-- The rounding of `1` as `roundVal`. -/
theorem setPrecRound_one_eq (p : ℕ) [NeZero p] (mode : RoundingMode) :
    setPrecRound one p mode = roundVal p mode (some (1 : EReal)) := by
  rw [setPrecRound_eq_roundVal toVal_one', EReal.coe_one]

/-- **`x^n` is correctly rounded.** -/
theorem powIntPrecRound_eq_liftVal (x : AzFloat) (n : AzInt) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    powIntPrecRound x n p mode = liftVal (Spec.powInt n.toInt) x p mode := by
  unfold liftVal powIntPrecRound
  have hsign : n.sign = true ↔ 0 ≤ n.toInt := AzInt.sign_eq_true_iff n
  cases x with
  | nan => rfl
  | infinity s =>
    simp only [toVal_infinity, Option.bind_some]
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, ite_eq_right (NeZero.ne p), hn0, AzInt.toInt_zero,
        setPrecRound_one_eq]
      cases s <;> simp [Spec.powInt_top, Spec.powInt_bot]
    have hnZ : n.toInt ≠ 0 := toInt_ne_zero_of_ne_zero hn0
    rw [ite_eq_right hn0]
    by_cases hs : n.sign = true
    · have hpos : 0 < n.toInt := lt_of_le_of_ne (hsign.mp hs) (Ne.symm hnZ)
      cases s
      · simp only [hs, ↓reduceIte, Bool.false_or, Bool.false_eq_true, Spec.powInt_bot, hnZ,
          hpos]
        by_cases he : n.abs.isEven = true
        · rw [he, ite_eq_left ((abs_isEven_iff n).mp he)]; simp
        · have he' : n.abs.isEven = false := by simpa using he
          rw [he', ite_eq_right (c := Even n.toInt) (fun h => he ((abs_isEven_iff n).mpr h))]
          simp
      · simp [hs, hnZ, hpos, Spec.powInt_top]
    · have hneg : n.toInt < 0 := by
        have := hsign.not.mp hs
        push Not at this
        exact this
      cases s <;> simp [hs, hnZ, not_lt.mpr hneg.le, Spec.powInt_top, Spec.powInt_bot]
  | zero =>
    simp only [toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.powInt_coe]
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, ite_eq_right (NeZero.ne p), hn0, AzInt.toInt_zero, ite_eq_left rfl,
        setPrecRound_one_eq]
    have hnZ : n.toInt ≠ 0 := toInt_ne_zero_of_ne_zero hn0
    rw [ite_eq_right hn0, ite_eq_right hnZ]
    by_cases hs : n.sign = true
    · have hpos : 0 < n.toInt := lt_of_le_of_ne (hsign.mp hs) (Ne.symm hnZ)
      rw [ite_eq_left hs, ite_eq_right (c := (0 : ℝ) = 0 ∧ n.toInt < 0)
        (fun h => lt_asymm hpos h.2), zero_zpow _ hnZ]
      simp
    · have hneg : n.toInt < 0 := by
        have := hsign.not.mp hs
        push Not at this
        exact this
      rw [ite_eq_right hs, ite_eq_left (c := (0 : ℝ) = 0 ∧ n.toInt < 0) ⟨rfl, hneg⟩]
      simp
  | finite s e q m hv =>
    simp only [toVal_finite, Option.bind_some, Spec.powInt_coe]
    rw [ite_eq_right (NeZero.ne p)]
    by_cases hn0 : n = 0
    · rw [ite_eq_left hn0, hn0, AzInt.toInt_zero, ite_eq_left rfl, setPrecRound_one_eq]
    have hnZ : n.toInt ≠ 0 := toInt_ne_zero_of_ne_zero hn0
    rw [ite_eq_right hn0, ite_eq_right hnZ]
    have hv0 : finiteVal s e m ≠ 0 := by
      have h := (abs_finiteVal_bounds s e hv).1
      have : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - 1) := by positivity
      exact fun h0 => by rw [h0, abs_zero] at h; linarith
    -- the exact ingredients
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = n.abs.toNat := ⟨_, rfl⟩
    have hkZ : (k : ℤ) = |n.toInt| := by rw [hk]; exact AzInt.abs_toNat_eq n
    have hm0 : (m.toNat : ℝ) ≠ 0 := by
      intro h0
      apply hv0
      unfold finiteVal
      rw [h0, mul_zero, zero_mul]
    have ht : ((e - (AzNat.ofNat m.size).toAzInt) * n.abs.toAzInt).toInt
        = (e.toInt - m.size) * k := by
      rw [AzInt.toInt_mul, AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, hk]
    have hmk : (ofAzNat (m.pow k)).toVal = some (((m.toNat : ℝ) ^ k : ℝ) : EReal) := by
      rw [toVal_ofAzNat, AzNat.toNat_pow, Nat.cast_pow]
    have hsgn := sign_pow_eq s k n.abs.isOdd (by rw [hk]; exact abs_isOdd_iff n)
    have hpow := finiteVal_pow s e m k
    rw [hsgn] at hpow
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = if (!s && n.abs.isOdd) = true then (-1 : ℝ) else 1 := ⟨_, rfl⟩
    rw [← hσ] at hpow
    have hσmk : (if (!s && n.abs.isOdd) = true then -ofAzNat (m.pow k) else ofAzNat (m.pow k)).toVal
        = some ((σ * (m.toNat : ℝ) ^ k : ℝ) : EReal) := by
      rw [hσ]
      split_ifs
      · rw [toVal_neg, hmk, Option.map_some, neg_one_mul, EReal.coe_neg]
      · rw [hmk, one_mul]
    have hσp2 : (if (!s && n.abs.isOdd) = true
        then -powerOf2 (-((e - (AzNat.ofNat m.size).toAzInt) * n.abs.toAzInt))
        else powerOf2 (-((e - (AzNat.ofNat m.size).toAzInt) * n.abs.toAzInt))).toVal
        = some ((σ * (2 : ℝ) ^ (-((e.toInt - m.size) * k)) : ℝ) : EReal) := by
      rw [hσ]
      split_ifs
      · rw [toVal_neg, toVal_powerOf2, AzInt.toInt_neg, ht, Option.map_some, neg_one_mul,
          EReal.coe_neg]
      · rw [toVal_powerOf2, AzInt.toInt_neg, ht, one_mul]
    simp only [← hk]
    by_cases hs : n.sign = true
    · -- `n = k ≥ 0`
      have hnk : n.toInt = k := by rw [hkZ, abs_of_nonneg (hsign.mp hs)]
      rw [ite_eq_left hs, ite_eq_right (c := finiteVal s e m = 0 ∧ n.toInt < 0) (fun h => hv0 h.1),
        mulPrecRound_eq_liftVal₂, liftVal₂, hσmk, toVal_powerOf2, ht, Option.bind_some,
        Option.bind_some, Spec.mul_coe_coe, hnk, zpow_natCast, hpow]
    · -- `n = −k < 0`
      have hneg : n.toInt < 0 := by
        have := hsign.not.mp hs
        push Not at this
        exact this
      have hnk : n.toInt = -k := by rw [hkZ, abs_of_neg hneg, neg_neg]
      rw [ite_eq_right hs, ite_eq_right (c := finiteVal s e m = 0 ∧ n.toInt < 0) (fun h => hv0 h.1),
        divPrecRound_eq_liftVal₂, liftVal₂, hσp2, hmk, Option.bind_some, Option.bind_some,
        Spec.div_coe_coe _ _ (pow_ne_zero _ hm0), hnk, zpow_neg (finiteVal s e m), zpow_natCast,
        hpow]
      congr 3
      have hσ2 : σ * σ = 1 := by rw [hσ]; split_ifs <;> norm_num
      have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
      rw [mul_inv, mul_inv, hσinv, zpow_neg]
      ring

end Azurite.AzFloat
