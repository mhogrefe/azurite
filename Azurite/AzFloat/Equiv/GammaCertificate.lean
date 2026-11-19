/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.GammaRatBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzNat.Equiv.Compare
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.Chudnovsky.GammaValues
import Azurite.AzFloat.Equiv.PowBracket
import Mathlib.Data.Nat.Multiplicity

/-!
# The Ziv certificates of `Γ` at the rationals with denominator `2, 3, 4, 6`

By Chudnovsky's theorem (`Azurite.Chudnovsky.irrational_gamma_of_den`) `Γ(q)` is irrational for
a rational `q` with denominator `2, 3, 4` or `6`; the brackets of `Γ` converge (`gammaCore_conv`,
`gammaRatCore_conv`); so `roundingPossible` accepts the bracket at some level, and the Ziv loops
of `gammaPrecRound`, `reciprocalGammaPrecRound`, `gammaRatPrecRound` and
`reciprocalGammaRatPrecRound` run without fuel there.

* `gammaSpecial_spec`, `gammaApprox_cert`: floats `n/4` that are not integers.
* `gammaRatSpecial_spec`, `gammaRatApprox_cert`: rationals with denominator `2, 3, 4, 6`.
-/

namespace Azurite.AzFloat

/-- `Γ(q)` and `1/Γ(q)` are irrational for a rational `q` with denominator `2, 3, 4, 6`. -/
theorem irrational_gammaVal (recip : Bool) (q : ℚ)
    (hden : q.den = 2 ∨ q.den = 3 ∨ q.den = 4 ∨ q.den = 6) :
    Irrational (gammaVal recip (q : ℝ)) := by
  have h := Azurite.Chudnovsky.irrational_gamma_of_den q hden
  unfold gammaVal
  cases recip
  · simpa using h
  · simpa using h.inv

/-- A rational with denominator other than `1` is not an integer. -/
theorem ne_int_of_den_ne_one {q : ℚ} (h : q.den ≠ 1) (k : ℤ) : (q : ℝ) ≠ k := by
  intro hk
  apply h
  have : q = (k : ℚ) := by exact_mod_cast hk
  rw [this]
  exact Rat.den_intCast k

/-- A float recognized by `gammaSpecial` is a rational with denominator `2` or `4`. -/
theorem gammaSpecial_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (h : gammaSpecial x = true) : ∃ q : ℚ, (q : ℝ) = xv ∧ (q.den = 2 ∨ q.den = 4) := by
  unfold gammaSpecial at h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h4, hni⟩ := h
  have hx4 := toVal_shiftLeft_of_toVal hx (AzInt.ofInt 2)
  rw [AzInt.toInt_ofInt] at hx4
  obtain ⟨n, hn⟩ := (isInteger_iff_of_toVal hx4).mp h4
  have hxv : xv = (n : ℝ) / 4 := by
    have : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
    rw [this] at hn
    linarith
  refine ⟨(n : ℚ) / 4, by rw [hxv]; push_cast; rfl, ?_⟩
  have hdvd : ((n : ℚ) / 4).den ∣ 2 ^ 2 := by
    have h1 := Rat.den_dvd n 4
    rw [Rat.divInt_eq_div] at h1
    have h2 : (((n : ℚ) / ((4 : ℤ) : ℚ)).den : ℤ) ∣ ((4 : ℕ) : ℤ) := by exact_mod_cast h1
    have h3 := Int.natCast_dvd_natCast.mp h2
    simpa using h3
  have hne : ((n : ℚ) / 4).den ≠ 1 := by
    intro h1
    have hq : (((n : ℚ) / 4 : ℚ) : ℝ) = xv := by rw [hxv]; push_cast; rfl
    have hint : xv = ((((n : ℚ) / 4).num : ℤ) : ℝ) := by
      rw [← hq]
      have := Rat.coe_int_num_of_den_eq_one h1
      exact_mod_cast this.symm
    have : isInteger x = true := (isInteger_iff_of_toVal hx).mpr ⟨_, hint⟩
    rw [hni] at this
    exact Bool.noConfusion this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · exact absurd hk' hne
  · left; simpa using hk'
  · right; simpa using hk'

/-- **The Ziv certificate of `Γ(x)` and `1/Γ(x)` at a float `x = n/4` that is not an
integer.** -/
theorem gammaApprox_cert (recip : Bool) {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (h : gammaSpecial (finite s e q m hv) = true) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaApprox recip (finite s e q m hv) e s (w₀ * 2 ^ f)).1
      (gammaApprox recip (finite s e q m hv) e s (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hx := toVal_finite s e q m hv
  obtain ⟨r, hr, hden⟩ := gammaSpecial_spec hx h
  have hden' : r.den = 2 ∨ r.den = 3 ∨ r.den = 4 ∨ r.den = 6 := by
    rcases hden with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  have hne : r.den ≠ 1 := by rcases hden with h | h <;> rw [h] <;> norm_num
  have hirr := irrational_gammaVal recip r hden'
  rw [hr] at hirr
  refine gammaApprox_isSome_exists recip hx e
    (fun hs => by subst hs; exact finiteVal_true_pos e hv)
    (fun hs => by
      subst hs
      exact ⟨finiteVal_false_neg e hv, fun k => by rw [← hr]; exact ne_int_of_den_ne_one hne k⟩)
    hirr p mode w₀ hw₀

/-- A rational recognized by `gammaRatSpecial` has denominator `2, 3, 4` or `6`. -/
theorem gammaRatSpecial_spec {q : AzRat} (h : gammaRatSpecial q = true) :
    (AzRat.toRat q).den = 2 ∨ (AzRat.toRat q).den = 3 ∨ (AzRat.toRat q).den = 4 ∨
      (AzRat.toRat q).den = 6 := by
  have hden : (AzRat.toRat q).den = q.den.toNat := rfl
  unfold gammaRatSpecial at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rw [hden]
  rcases h with ((h | h) | h) | h <;> rw [h, AzNat.toNat_ofNat] <;> simp

/-- A rational recognized by `gammaRatSpecial` is not `0`. -/
theorem num_ne_zero_of_gammaRatSpecial {q : AzRat} (h : gammaRatSpecial q = true) :
    q.num ≠ 0 := by
  intro h0
  have hz : AzRat.toRat q = 0 := by
    exact_mod_cast (AzRat.toRat_eq_zero_iff q).mpr h0
  have hd := gammaRatSpecial_spec h
  rw [hz] at hd
  simp at hd

/-- **The Ziv certificate of `Γ(q)` and `1/Γ(q)` at a rational `q` with denominator
`2, 3, 4` or `6`.** -/
theorem gammaRatApprox_cert (recip : Bool) {q : AzRat} (h : gammaRatSpecial q = true)
    (e : AzInt) (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaRatApprox recip q e q.sign (w₀ * 2 ^ f)).1
      (gammaRatApprox recip q e q.sign (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hden := gammaRatSpecial_spec h
  have h0 := num_ne_zero_of_gammaRatSpecial h
  have hne : (AzRat.toRat q).den ≠ 1 := by
    rcases hden with h | h | h | h <;> rw [h] <;> norm_num
  exact gammaRatApprox_isSome_exists recip q e (fun hs => (toRat_sign_iff q h0).mp hs)
    (fun hs => ⟨toRat_neg_of_sign_false q h0 hs, ne_int_of_den_ne_one hne⟩)
    (irrational_gammaVal recip _ hden) p mode w₀ hw₀

/-! ### Large positive integers -/

/-- `m!` is no rounding boundary at precision `p` once `m ≥ 2p + 16`: its odd part has more
than `p + 1` bits. -/
theorem factorial_not_boundary (p : ℕ) [NeZero p] {m : ℕ} (hm : 2 * p + 16 ≤ m) :
    (((m.factorial : ℕ) : ℝ) : EReal) ∉ floatSet (p + 1) := by
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.factorial_ne_zero m)
  have hk : k < m := by
    have h1 : (k : ℕ∞) ≤ emultiplicity 2 m.factorial :=
      pow_dvd_iff_le_emultiplicity.mp ⟨o, hko⟩
    have h2 := Nat.emultiplicity_two_factorial_lt (n := m) (by omega)
    exact_mod_cast lt_of_le_of_lt h1 h2
  -- `m! ≥ 8^(m − 7)`
  have hbig : 2 ^ (3 * (m - 7)) ≤ m.factorial := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 7) (n := m - 7)
    rw [show 7 + (m - 7) = m by omega] at h
    calc 2 ^ (3 * (m - 7)) = (7 + 1) ^ (m - 7) := by rw [pow_mul]; norm_num
      _ ≤ Nat.factorial 7 * (7 + 1) ^ (m - 7) :=
          Nat.le_mul_of_pos_left _ (Nat.factorial_pos 7)
      _ ≤ m.factorial := h
  have ho2 : 2 ^ (p + 1) ≤ o := by
    by_contra hlt
    push Not at hlt
    have h1 : m.factorial < 2 ^ k * 2 ^ (p + 1) := by
      rw [hko]
      exact Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    have h2 : 2 ^ k * 2 ^ (p + 1) ≤ 2 ^ (3 * (m - 7)) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h := not_mem_floatSet_of_odd_mul p ho ho2 (k : ℤ) (σ := 1) (by norm_num)
  have e : ((m.factorial : ℕ) : ℝ) = 1 * (o : ℝ) * (2 : ℝ) ^ (k : ℤ) := by
    rw [hko, zpow_natCast]
    push_cast
    ring
  rw [e]
  exact h

/-- A positive integer float beyond the factorial bound: its value is `m + 1` with
`B ≤ m`. -/
theorem gammaBigInt_spec {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    {B : ℕ} (hpole : ¬ (isInteger (finite s e q m hv) && !s) = true)
    (hsm : ¬ gammaSmallInt (finite s e q m hv) B = true)
    (hI : isInteger (finite s e q m hv) = true) :
    s = true ∧ ∃ n : ℕ, B ≤ n ∧ finiteVal s e m = ((n : ℝ) + 1) := by
  have hs : s = true := by
    cases s
    · exact absurd (by simp [hI]) hpole
    · rfl
  subst hs
  refine ⟨rfl, ?_⟩
  have hx := toVal_finite true e q m hv
  have hpos := finiteVal_true_pos e hv
  obtain ⟨k, hk⟩ := (isInteger_iff_of_toVal hx).mp hI
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := hk ▸ hpos
    exact_mod_cast this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  refine ⟨n, ?_, by rw [hk, hn]; push_cast; rfl⟩
  by_contra hlt
  push Not at hlt
  apply hsm
  unfold gammaSmallInt
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hI, (lt_eq_true_iff toVal_zero' hx).mpr hpos⟩, ?_⟩
  rw [le_eq_true_iff hx (toVal_ofAzNat _), AzNat.toNat_ofNat, hk, hn]
  have : n + 1 ≤ B := hlt
  exact_mod_cast this

/-- **The Ziv certificate of `Γ(n)` at a positive integer beyond the factorial bound**: the
value `(n − 1)!` is no rounding boundary at precision `p`. -/
theorem gammaApprox_cert_int {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (hpole : ¬ (isInteger (finite s e q m hv) && !s) = true)
    (hsm : ¬ gammaSmallInt (finite s e q m hv) (gammaIntBound p) = true)
    (hI : isInteger (finite s e q m hv) = true) (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaApprox false (finite s e q m hv) e s (w₀ * 2 ^ f)).1
      (gammaApprox false (finite s e q m hv) e s (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨rfl, n, hn, hval⟩ := gammaBigInt_spec hv hpole hsm hI
  have hx := toVal_finite true e q m hv
  have hconv := gammaApprox_bracketConv false hx e (pos := true)
    (fun _ => finiteVal_true_pos e hv) (fun h => by simp at h)
  have hG : gammaVal false (finiteVal true e m) = ((n.factorial : ℕ) : ℝ) := by
    rw [hval]
    exact Real.Gamma_nat_eq_factorial n
  rw [hG] at hconv
  exact hconv.exists_isSome (by positivity) p
    (factorial_not_boundary p (by unfold gammaIntBound at hn; omega)) mode w₀ hw₀

/-- `1/m!` is not dyadic for `m ≥ 3`. -/
theorem not_isDyadic_inv_factorial {m : ℕ} (hm : 3 ≤ m) :
    ¬ IsDyadic (((m.factorial : ℕ) : ℝ)⁻¹) := by
  rintro ⟨a, k, h⟩
  obtain ⟨t, ht⟩ : 3 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
  have hf0 : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 : ((m.factorial : ℕ) : ℝ) * (a * (2 : ℝ) ^ k) = 1 := by
    rw [← h]
    exact mul_inv_cancel₀ hf0
  rw [ht] at h1
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at h1
    have h2 : ((3 * t : ℕ) : ℤ) * (a * 2 ^ j) = 1 := by exact_mod_cast h1
    have h3 : (3 : ℤ) ∣ 1 := ⟨(t : ℤ) * (a * 2 ^ j), by rw [← h2]; push_cast; ring⟩
    omega
  · rw [zpow_neg, zpow_natCast] at h1
    have hp : ((2 : ℝ) ^ j) ≠ 0 := by positivity
    have h2 : ((3 * t : ℕ) : ℝ) * a = 2 ^ j := by
      field_simp at h1
      linarith
    have h2' : ((3 * t : ℕ) : ℤ) * a = 2 ^ j := by exact_mod_cast h2
    have h3 : (3 : ℤ) ∣ 2 ^ j := ⟨(t : ℤ) * a, by rw [← h2']; push_cast; ring⟩
    have h4 := (Int.prime_three).dvd_of_dvd_pow h3
    omega

/-- **The Ziv certificate of `1/Γ(n)` at a positive integer beyond the factorial bound**: the
value `1/(n − 1)!` is not dyadic. -/
theorem gammaApprox_cert_int_recip {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (p : ℕ) [NeZero p]
    (hpole : ¬ (isInteger (finite s e q m hv) && !s) = true)
    (hsm : ¬ gammaSmallInt (finite s e q m hv) (gammaIntBound p) = true)
    (hI : isInteger (finite s e q m hv) = true) (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaApprox true (finite s e q m hv) e s (w₀ * 2 ^ f)).1
      (gammaApprox true (finite s e q m hv) e s (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨rfl, n, hn, hval⟩ := gammaBigInt_spec hv hpole hsm hI
  have hx := toVal_finite true e q m hv
  have hconv := gammaApprox_bracketConv true hx e (pos := true)
    (fun _ => finiteVal_true_pos e hv) (fun h => by simp at h)
  have hG : gammaVal true (finiteVal true e m) = (((n.factorial : ℕ) : ℝ))⁻¹ := by
    rw [hval]
    exact congrArg (·⁻¹) (Real.Gamma_nat_eq_factorial n)
  rw [hG] at hconv
  exact hconv.exists_isSome (by positivity) p
    (not_mem_floatSet_of_not_isDyadic p
      (not_isDyadic_inv_factorial (by unfold gammaIntBound at hn; omega))) mode w₀ hw₀

/-- A positive integer rational beyond the factorial bound: its value is `n + 1` with
`B ≤ n`. -/
theorem gammaRatBigInt_spec {q : AzRat} {B : ℕ} (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false)) (hsm : ¬ gammaRatSmallInt q B = true)
    (hI : q.den = 1) :
    q.sign = true ∧ ∃ n : ℕ, B ≤ n ∧ ((AzRat.toRat q : ℚ) : ℝ) = (n : ℝ) + 1 := by
  have hs : q.sign = true := by
    by_contra hs
    exact hpole ⟨hI, by simpa using hs⟩
  refine ⟨hs, q.num.toNat - 1, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    apply hsm
    unfold gammaRatSmallInt
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      AzNat.le_iff_toNat_le, AzNat.toNat_ofNat]
    exact ⟨⟨hI, hs⟩, by omega⟩
  · have hn0 : q.num.toNat ≠ 0 := fun h =>
      h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
    rw [toRat_eq_of_int_den_one q hs hI]
    have : q.num.toNat = (q.num.toNat - 1) + 1 := by omega
    conv_lhs => rw [this]
    push_cast
    ring

/-- The value of `Γ` or `1/Γ` at a positive integer `n + 1` is no rounding boundary at
precision `p` once `n` is beyond the factorial bound. -/
theorem gammaVal_int_not_boundary (recip : Bool) (p : ℕ) [NeZero p] {n : ℕ}
    (hn : gammaIntBound p ≤ n) :
    ((gammaVal recip ((n : ℝ) + 1) : ℝ) : EReal) ∉ floatSet (p + 1) := by
  unfold gammaIntBound at hn
  cases recip with
  | false =>
    rw [show gammaVal false ((n : ℝ) + 1) = ((n.factorial : ℕ) : ℝ) from
      Real.Gamma_nat_eq_factorial n]
    exact factorial_not_boundary p (by omega)
  | true =>
    rw [show gammaVal true ((n : ℝ) + 1) = (((n.factorial : ℕ) : ℝ))⁻¹ from
      congrArg (·⁻¹) (Real.Gamma_nat_eq_factorial n)]
    exact not_mem_floatSet_of_not_isDyadic p (not_isDyadic_inv_factorial (by omega))

theorem gammaVal_int_ne_zero (recip : Bool) (n : ℕ) : gammaVal recip ((n : ℝ) + 1) ≠ 0 := by
  have h : Real.Gamma ((n : ℝ) + 1) ≠ 0 := by
    rw [Real.Gamma_nat_eq_factorial]
    positivity
  cases recip
  · exact h
  · exact inv_ne_zero h

/-- **The Ziv certificate of `Γ(q)` and `1/Γ(q)` at a positive integer rational beyond the
factorial bound.** -/
theorem gammaRatApprox_cert_int (recip : Bool) {q : AzRat} {p : ℕ} [NeZero p] (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false))
    (hsm : ¬ gammaRatSmallInt q (gammaIntBound p) = true) (hI : q.den = 1) (e : AzInt)
    (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaRatApprox recip q e q.sign (w₀ * 2 ^ f)).1
      (gammaRatApprox recip q e q.sign (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨hs, n, hn, hval⟩ := gammaRatBigInt_spec h0 hpole hsm hI
  have hconv := gammaRatApprox_bracketConv recip q e (pos := q.sign)
    (fun _ => by rw [hval]; positivity) (fun h => by rw [hs] at h; exact Bool.noConfusion h)
  rw [hval] at hconv
  exact hconv.exists_isSome (gammaVal_int_ne_zero recip n) p
    (gammaVal_int_not_boundary recip p hn) mode w₀ hw₀

end Azurite.AzFloat
