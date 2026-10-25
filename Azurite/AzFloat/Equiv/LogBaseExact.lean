/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LogBaseExact
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.RoundToInteger
import Azurite.AzNat.Equiv.LogBase
import Azurite.AzNat.Equiv.RootInt
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.TrailingZeros
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.LogBase
import Azurite.AzRat.Equiv.LogBase2
import Azurite.AzRat.Equiv.Unary
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# When `log_b x` is rational: correctness

* `maxRootBase_spec`: `b = c^s`, `2 ≤ c`, and `c` is not a perfect power (for a base below
  `2^64`): any `c = d^t` with `t ≥ 2` would make `b` a perfect `(t s)`-th power with
  `t s ≤ 63`, found before `s`.
* `logBaseExact?_some`: the rational returned is `ln x / ln b`.
* `irrational_of_logBaseExact?_none`: otherwise `ln x / ln b` is irrational.  A rational
  `r = n/d` would give `x^d = b^n`.  A non-integer float `x = o / 2^t` (`o` odd, `t ≥ 1`) is
  impossible by parity unless `b` is a power of two; an integer `x = N` gives, by
  `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow` and `Nat.exists_eq_pow_of_pow_eq_pow`, a
  common root with the primitive root `c` of `b`, so `N` is a power of `c` and
  `AzNat.checkedLogBase` would have found it.
-/

namespace Azurite.AzFloat

/-! ### The primitive root -/

theorem maxPowExp_spec (b : AzNat) (t : ℕ) :
    1 ≤ maxPowExp b t ∧
      (maxPowExp b t = 1 ∨
        (2 ≤ maxPowExp b t ∧ maxPowExp b t ≤ t ∧ b.isPow (maxPowExp b t) = true)) ∧
      ∀ u, maxPowExp b t < u → u ≤ t → b.isPow u = false := by
  induction t with
  | zero => exact ⟨le_rfl, Or.inl rfl, fun u h1 h2 => by simp [maxPowExp] at h1; omega⟩
  | succ t ih =>
    cases t with
    | zero => exact ⟨le_rfl, Or.inl rfl, fun u h1 h2 => by simp [maxPowExp] at h1; omega⟩
    | succ s =>
      unfold maxPowExp
      split_ifs with h
      · refine ⟨by omega, Or.inr ⟨by omega, le_rfl, h⟩, fun u h1 h2 => by omega⟩
      · obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨h1, ?_, fun u hu1 hu2 => ?_⟩
        · rcases h2 with h2 | ⟨h2a, h2b, h2c⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h2a, by omega, h2c⟩
        · rcases Nat.lt_or_ge u (s + 2) with hu | hu
          · exact h3 u hu1 (by omega)
          · have : u = s + 2 := by omega
            rw [this]; exact Bool.eq_false_iff.mpr h

theorem maxRootBaseBounded_spec (b : AzNat) (t : ℕ) (hb : 2 ≤ b.toNat) :
    b.toNat = (maxRootBaseBounded b t).1.toNat ^ (maxRootBaseBounded b t).2 ∧
      1 ≤ (maxRootBaseBounded b t).2 ∧
      2 ≤ (maxRootBaseBounded b t).1.toNat ∧
      ∀ u, (maxRootBaseBounded b t).2 < u → u ≤ t → ¬ ∃ y, y ^ u = b.toNat := by
  obtain ⟨h1, h2, h3⟩ := maxPowExp_spec b t
  unfold maxRootBaseBounded
  simp only []
  set s := maxPowExp b t with hs
  have hmax : ∀ u, s < u → u ≤ t → ¬ ∃ y, y ^ u = b.toNat := by
    intro u hu1 hu2 hy
    have := (AzNat.isPow_eq_true_iff b u (by omega)).mpr hy
    rw [h3 u hu1 hu2] at this
    cases this
  rcases h2 with h2 | ⟨h2a, h2b, h2c⟩
  · rw [ite_eq_left h2, h2, pow_one]
    exact ⟨rfl, le_rfl, hb, by rw [h2] at hmax; exact hmax⟩
  · rw [ite_eq_right (by omega)]
    have hpow : (b.rootInt s).toNat ^ s = b.toNat := by
      unfold AzNat.isPow at h2c
      rw [decide_eq_true_iff] at h2c
      have := congrArg AzNat.toNat h2c
      rwa [AzNat.toNat_pow] at this
    refine ⟨hpow.symm, h1, ?_, hmax⟩
    by_contra hlt
    push Not at hlt
    have : (b.rootInt s).toNat ^ s ≤ 1 := by
      calc (b.rootInt s).toNat ^ s ≤ 1 ^ s := Nat.pow_le_pow_left (by omega) s
        _ = 1 := one_pow s
    omega

/-- The primitive root is not a perfect power (base below `2^(t+1)`). -/
theorem maxRootBaseBounded_not_pow (b : AzNat) (t : ℕ) (hb : 2 ≤ b.toNat)
    (hbt : b.toNat < 2 ^ (t + 1)) :
    ∀ u, 2 ≤ u → ¬ ∃ d, (maxRootBaseBounded b t).1.toNat = d ^ u := by
  obtain ⟨hcs, hs1, hc2, hmax⟩ := maxRootBaseBounded_spec b t hb
  rintro u hu ⟨d, hd⟩
  set c := (maxRootBaseBounded b t).1.toNat with hc
  set s := (maxRootBaseBounded b t).2 with hs
  have hd2 : 2 ≤ d := by
    by_contra h
    push Not at h
    have : d ^ u ≤ 1 := by
      calc d ^ u ≤ 1 ^ u := Nat.pow_le_pow_left (by omega) u
        _ = 1 := one_pow u
    omega
  have hbd : b.toNat = d ^ (u * s) := by rw [hcs, hd, ← pow_mul]
  have hus : u * s ≤ t := by
    by_contra h
    push Not at h
    have : 2 ^ (t + 1) ≤ d ^ (u * s) := by
      calc 2 ^ (t + 1) ≤ 2 ^ (u * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ d ^ (u * s) := Nat.pow_le_pow_left hd2 _
    omega
  exact hmax (u * s) (by nlinarith) hus ⟨d, hbd.symm⟩

/-- The 64-bit instances. -/
theorem maxRootBase_spec (b : AzNat) (hb : 2 ≤ b.toNat) :
    b.toNat = (maxRootBase b).1.toNat ^ (maxRootBase b).2 ∧ 1 ≤ (maxRootBase b).2 ∧
      2 ≤ (maxRootBase b).1.toNat ∧
      ∀ u, (maxRootBase b).2 < u → u ≤ 63 → ¬ ∃ y, y ^ u = b.toNat :=
  maxRootBaseBounded_spec b 63 hb

theorem maxRootBase_not_pow (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64) :
    ∀ t, 2 ≤ t → ¬ ∃ d, (maxRootBase b).1.toNat = d ^ t :=
  maxRootBaseBounded_not_pow b 63 hb (by simpa using hb64)

/-! ### The exact value -/

theorem toRat_eq_of_int_den_one (q : AzRat) (hs : q.sign = true) (hd : q.den = 1) :
    (AzRat.toRat q : ℝ) = q.num.toNat := by
  rw [AzRat.toRat_cast_eq, hs, hd]
  simp

theorem log_pos_of_two_le {n : ℕ} (h : 2 ≤ n) : 0 < Real.log n :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < n))

/-- The rational returned by `logBaseExact?` is `ln x / ln b`. -/
theorem logBaseExact?_some (x : AzFloat) (b : AzNat) (hb : 2 ≤ b.toNat) (r : AzRat)
    (h : logBaseExact? x b = some r) :
    ∃ v : ℝ, x.toVal = some (v : EReal) ∧ 0 < v ∧
      Real.log v / Real.log b.toNat = (AzRat.toRat r : ℝ) := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
  unfold logBaseExact? at h
  rcases hq : x.toAzRat? with _ | q
  · rw [hq] at h; cases h
  · rw [hq] at h
    simp only [] at h
    split_ifs at h with hg
    · obtain ⟨hsg, hd1, hn0⟩ := hg
      rcases hr : AzNat.checkedLogBase (maxRootBase b).1 q.num with _ | e
      · rw [hr] at h; cases h
      · rw [hr, Option.map_some, Option.some.injEq] at h
        have hne : q.num.toNat = (maxRootBase b).1.toNat ^ e :=
          (AzNat.checkedLogBase_eq_some_iff _ _ hc2 hn0 e).mp hr
        have hv := toVal_of_toAzRat? x q hq
        rw [toRat_eq_of_int_den_one q hsg hd1] at hv
        have hnpos : (0 : ℝ) < q.num.toNat := by
          exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0)
        refine ⟨_, hv, hnpos, ?_⟩
        rw [← h, AzRat.toRat_ofAzInts, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
          AzNat.toNat_ofNat]
        push_cast
        have hlogc : 0 < Real.log (maxRootBase b).1.toNat := log_pos_of_two_le hc2
        rw [hne, hcs, Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
        field_simp

/-! ### Irrationality otherwise -/

/-- `v^d = B^n` from `ln v / ln B = n / d`. -/
theorem pow_eq_zpow_of_log_div_log {v B : ℝ} (hv : 0 < v) (hB : 0 < B) (hB1 : B ≠ 1) (r : ℚ)
    (hr : (r : ℝ) = Real.log v / Real.log B) : v ^ r.den = B ^ r.num := by
  have hlogB : Real.log B ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hB hB1
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hrq : (r : ℝ) * r.den = r.num := by rw [Rat.cast_def]; field_simp
  have key : (r.den : ℝ) * Real.log v = r.num * Real.log B := by
    rw [← hrq, hr, div_mul_eq_mul_div, div_mul_cancel₀ _ hlogB, mul_comm]
  have h1 : v ^ r.den = Real.exp (r.den * Real.log v) := by
    rw [Real.exp_nat_mul, Real.exp_log hv]
  have h2 : B ^ r.num = Real.exp (r.num * Real.log B) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hB, mul_comm]
  rw [h1, h2, key]

/-- A float is `o · 2^j` with `o` odd. -/
theorem finiteVal_eq_odd_mul_zpow (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    ∃ (o : ℕ) (j : ℤ), Odd o ∧ finiteVal true e m = (o : ℝ) * (2 : ℝ) ^ j := by
  have hc := coreSignificand_ne_zero hv
  obtain ⟨k, o, hodd, hko⟩ := Nat.exists_eq_two_pow_mul_odd (toNat_ne_zero_of_ne_zero hc)
  refine ⟨o, k + (e.toInt - q), hodd, ?_⟩
  rw [finiteVal_eq_core_mul true e hv, hko]
  simp only [↓reduceIte, one_mul]
  push_cast
  rw [zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_natCast]
  ring

theorem odd_pow_eq_two_pow {o d i : ℕ} (ho : Odd o) (hd : 1 ≤ d) (h : o ^ d = 2 ^ i) : o = 1 := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · rw [hi, pow_zero] at h
    exact (Nat.pow_eq_one.mp h).resolve_right (by omega)
  · exfalso
    have : Even (o ^ d) := by rw [h]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [Nat.even_pow] at this
    exact (Nat.not_even_iff_odd.mpr ho) this.1

/-- A non-integer float has an irrational `log_b` for a base that is not a power of two. -/
theorem irrational_log_div_log_of_not_int (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (b : AzNat) (hb : 2 ≤ b.toNat) (hnp : ∀ i, b.toNat ≠ 2 ^ i)
    (hni : ¬ ∃ n : ℤ, finiteVal true e m = n) :
    Irrational (Real.log (finiteVal true e m) / Real.log b.toNat) := by
  obtain ⟨o, j, hodd, hval⟩ := finiteVal_eq_odd_mul_zpow e hv
  have hv0 := finiteVal_true_pos e hv
  have hB : (0 : ℝ) < b.toNat := by exact_mod_cast (by omega : 0 < b.toNat)
  have hB1 : (b.toNat : ℝ) ≠ 1 := by exact_mod_cast (by omega : b.toNat ≠ 1)
  have ho0 : 0 < o := hodd.pos
  -- the exponent is negative
  have hj : j < 0 := by
    by_contra hj
    push Not at hj
    apply hni
    refine ⟨o * 2 ^ j.toNat, ?_⟩
    rw [hval]; push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg hj]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, j = -(t : ℤ) ∧ 1 ≤ t := ⟨j.natAbs, by omega, by omega⟩
  obtain ⟨ht, ht1⟩ := ht
  rw [ht, zpow_neg, zpow_natCast] at hval
  rintro ⟨r, hr⟩
  have key := pow_eq_zpow_of_log_div_log hv0 hB hB1 r hr
  rw [hval] at key
  have hd : 1 ≤ r.den := r.den_pos
  rcases le_or_gt 0 r.num with hn | hn
  · -- `o^d = B^n · 2^(t d)`: even against odd
    obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = n := ⟨r.num.toNat, by omega⟩
    rw [hn', zpow_natCast] at key
    have hnat : o ^ r.den = b.toNat ^ n * 2 ^ (t * r.den) := by
      have : ((o : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ r.den = (b.toNat : ℝ) ^ n := key
      rw [mul_pow, inv_pow, ← pow_mul] at this
      have h2 : ((2 : ℝ) ^ (t * r.den)) ≠ 0 := by positivity
      have := (mul_inv_eq_iff_eq_mul₀ h2).mp this
      exact_mod_cast this
    have heven : Even (o ^ r.den) := by
      rw [hnat]
      exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).mul_left _
    rw [Nat.even_pow] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven.1
  · -- `o^d · B^(−n) = 2^(t d)`: `o = 1` and `B` a power of two
    obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = -(n : ℤ) := ⟨r.num.natAbs, by omega⟩
    rw [hn', zpow_neg, zpow_natCast] at key
    have hnat : o ^ r.den * b.toNat ^ n = 2 ^ (t * r.den) := by
      have : ((o : ℝ) * ((2 : ℝ) ^ t)⁻¹) ^ r.den = ((b.toNat : ℝ) ^ n)⁻¹ := key
      rw [mul_pow, inv_pow, ← pow_mul] at this
      have h2 : ((2 : ℝ) ^ (t * r.den)) ≠ 0 := by positivity
      have hb' : ((b.toNat : ℝ) ^ n) ≠ 0 := by positivity
      field_simp at this
      exact_mod_cast this
    have hdvd : o ^ r.den ∣ 2 ^ (t * r.den) := ⟨_, hnat.symm⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have ho1 : o = 1 := odd_pow_eq_two_pow hodd hd hi
    rw [ho1, one_pow, one_mul] at hnat
    have hbdvd : b.toNat ∣ 2 ^ (t * r.den) := by
      rw [← hnat]
      exact dvd_pow_self _ (by
        intro h; rw [h, pow_zero] at hnat
        have : 1 < 2 ^ (t * r.den) := Nat.one_lt_two_pow (by positivity)
        omega)
    obtain ⟨i', -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hbdvd
    exact hnp i' hi'

/-- `N^d = b^n` with `N, d ≥ 1` forces `N` to be a power of the primitive root of `b` (bounded
version). -/
theorem exists_eq_pow_maxRootBounded_of_pow_eq_pow (b : AzNat) (t : ℕ) (hb : 2 ≤ b.toNat)
    (hbt : b.toNat < 2 ^ (t + 1)) {N d n : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d)
    (hnat : N ^ d = b.toNat ^ n) : ∃ k, N = (maxRootBaseBounded b t).1.toNat ^ k := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBaseBounded_spec b t hb
  have hnotpow := maxRootBaseBounded_not_pow b t hb hbt
  set c := (maxRootBaseBounded b t).1.toNat with hc
  set s := (maxRootBaseBounded b t).2 with hs
  -- reduce the exponents to coprime ones
  set g := Nat.gcd d n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  set d' := d / g with hd'
  set n' := n / g with hn''
  have hcop : Nat.Coprime d' n' := Nat.coprime_div_gcd_div_gcd hg0
  have hdg : d = g * d' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hng : n = g * n' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have hred : N ^ d' = b.toNat ^ n' := by
    have : (N ^ d') ^ g = (b.toNat ^ n') ^ g := by
      rw [← pow_mul, ← pow_mul, mul_comm d', mul_comm n', ← hdg, ← hng]; exact hnat
    exact (pow_left_inj₀ (by positivity) (by positivity) hg0.ne').mp this
  obtain ⟨C, hNC, hbC⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcop hred
  -- `c^s = C^d'`: a common root, and `c` is primitive
  have hcC : c ^ s = C ^ d' := by rw [← hcs, hbC]
  obtain ⟨D, hcD, hCD⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (by omega)) hcC
  set g' := Nat.gcd s d' with hg'
  have hd'1 : 1 ≤ d' := Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_left _ _)) hg0
  have hg'0 : 0 < g' := Nat.gcd_pos_of_pos_left _ (by omega : 0 < s)
  have hq1 : d' / g' = 1 := by
    have hq1' : 1 ≤ d' / g' :=
      Nat.div_pos (Nat.le_of_dvd hd'1 (Nat.gcd_dvd_right _ _)) hg'0
    by_contra h
    exact hnotpow (d' / g') (by omega) ⟨D, hcD⟩
  rw [hq1, pow_one] at hcD
  have hg'd : g' = d' := by
    have := Nat.div_mul_cancel (Nat.gcd_dvd_right s d')
    rw [hq1, one_mul] at this; exact this
  have hdvd : d' ∣ s := by rw [← hg'd]; exact Nat.gcd_dvd_left _ _
  obtain ⟨k, hk⟩ := hdvd
  have hCc : C = c ^ k := by
    rw [hCD, hcD, hk, hg'd, Nat.mul_div_cancel_left _ hd'1]
  exact ⟨n' * k, by rw [hNC, hCc, ← pow_mul, mul_comm]⟩

/-- `N^d = b^n` with `N, d ≥ 1` forces `N` to be a power of the primitive root of `b`. -/
theorem exists_eq_pow_maxRoot_of_pow_eq_pow (b : AzNat) (hb : 2 ≤ b.toNat)
    (hb64 : b.toNat < 2 ^ 64) {N d n : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d)
    (hnat : N ^ d = b.toNat ^ n) : ∃ k, N = (maxRootBase b).1.toNat ^ k :=
  exists_eq_pow_maxRootBounded_of_pow_eq_pow b 63 hb (by simpa using hb64) hN hd hnat

/-- An integer float that is not a power of the primitive root has an irrational `log_b`. -/
theorem irrational_log_div_log_of_int (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64)
    (N : ℕ) (hN : 1 ≤ N)
    (hno : ∀ r, N ≠ (maxRootBase b).1.toNat ^ r) :
    Irrational (Real.log N / Real.log b.toNat) := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
  have hnotpow := maxRootBase_not_pow b hb hb64
  set c := (maxRootBase b).1.toNat with hc
  set s := (maxRootBase b).2 with hs
  have hB : (0 : ℝ) < b.toNat := by exact_mod_cast (by omega : 0 < b.toNat)
  have hB1 : (b.toNat : ℝ) ≠ 1 := by exact_mod_cast (by omega : b.toNat ≠ 1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rintro ⟨r, hr⟩
  have key := pow_eq_zpow_of_log_div_log hNpos hB hB1 r hr
  have hd : 1 ≤ r.den := r.den_pos
  -- the exponent is nonnegative
  have hn0 : 0 ≤ r.num := by
    by_contra hn
    push Not at hn
    obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = -(n : ℤ) := ⟨r.num.natAbs, by omega⟩
    rw [hn', zpow_neg, zpow_natCast] at key
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ r.den := one_le_pow₀ (by exact_mod_cast hN)
    have h2 : ((b.toNat : ℝ) ^ n)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right
      exact one_lt_pow₀ (by exact_mod_cast (by omega : 1 < b.toNat)) (by omega)
    linarith
  obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = n := ⟨r.num.toNat, by omega⟩
  rw [hn', zpow_natCast] at key
  have hnat : N ^ r.den = b.toNat ^ n := by exact_mod_cast key
  obtain ⟨k, hk⟩ := exists_eq_pow_maxRoot_of_pow_eq_pow b hb hb64 hN hd hnat
  exact hno k hk

/-- A positive rational that is not an integer power of the primitive root has an irrational
`log_b`: a rational `n/d` gives `q^d = b^n`, so the reduced numerator and denominator are
coprime powers whose quotient is a power of `b`; one of them is `1` and the other is a power of
the primitive root. -/
theorem irrational_log_div_log_of_rat (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64)
    (q : ℚ) (hq : 0 < q) (hno : ∀ r : ℤ, (q : ℝ) ≠ ((maxRootBase b).1.toNat : ℝ) ^ r) :
    Irrational (Real.log q / Real.log b.toNat) := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
  have hB : (0 : ℝ) < b.toNat := by exact_mod_cast (by omega : 0 < b.toNat)
  have hB1 : (b.toNat : ℝ) ≠ 1 := by exact_mod_cast (by omega : b.toNat ≠ 1)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hnum := Rat.num_pos.mpr hq
  obtain ⟨N, hN⟩ : ∃ N : ℕ, q.num = N := ⟨q.num.toNat, by omega⟩
  have hN1 : 1 ≤ N := by omega
  have hcop : Nat.Coprime N q.den := by
    have := q.reduced
    rwa [hN, Int.natAbs_natCast] at this
  have hqND : (q : ℝ) = (N : ℝ) / q.den := by
    conv_lhs => rw [← Rat.num_div_den q, hN]
    push_cast
    rfl
  rintro ⟨r, hr⟩
  have key := pow_eq_zpow_of_log_div_log hqr hB hB1 r hr
  have hd : 1 ≤ r.den := r.den_pos
  rw [hqND, div_pow] at key
  have hDd : ((q.den : ℝ) ^ r.den) ≠ 0 := by positivity
  rcases le_or_gt 0 r.num with hn | hn
  · -- `N^d = b^n · D^d`: the denominator is `1`
    obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = n := ⟨r.num.toNat, by omega⟩
    rw [hn', zpow_natCast, div_eq_iff hDd] at key
    have hnat : N ^ r.den = b.toNat ^ n * q.den ^ r.den := by exact_mod_cast key
    have hdvd : q.den ^ r.den ∣ N ^ r.den := ⟨_, by rw [hnat, mul_comm]⟩
    have hD1 : q.den ^ r.den = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow _ _ hcop.symm) hdvd
    rw [hD1, mul_one] at hnat
    obtain ⟨k, hk⟩ := exists_eq_pow_maxRoot_of_pow_eq_pow b hb hb64 hN1 hd hnat
    have hD1' : q.den = 1 := (Nat.pow_eq_one.mp hD1).resolve_right (by omega)
    apply hno k
    rw [hqND, hD1', hk, zpow_natCast]
    push_cast
    ring
  · -- `N^d · b^(−n) = D^d`: the numerator is `1`
    obtain ⟨n, hn'⟩ : ∃ n : ℕ, r.num = -(n : ℤ) := ⟨r.num.natAbs, by omega⟩
    rw [hn', zpow_neg, zpow_natCast] at key
    have hnat : N ^ r.den * b.toNat ^ n = q.den ^ r.den := by
      have hb' : ((b.toNat : ℝ) ^ n) ≠ 0 := by positivity
      field_simp at key
      exact_mod_cast key
    have hdvd : N ^ r.den ∣ q.den ^ r.den := ⟨_, hnat.symm⟩
    have hN1' : N ^ r.den = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow _ _ hcop) hdvd
    rw [hN1', one_mul] at hnat
    obtain ⟨k, hk⟩ := exists_eq_pow_maxRoot_of_pow_eq_pow b hb hb64 q.den_pos hd hnat.symm
    have hNone : N = 1 := (Nat.pow_eq_one.mp hN1').resolve_right (by omega)
    apply hno (-k)
    rw [hqND, hNone, hk, zpow_neg, zpow_natCast]
    push_cast
    ring

/-- A positive integer float converts to the rational `Nn / 1` (sign `true`, denominator `1`). -/
theorem toAzRat?_of_nat (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (Nn : ℕ)
    (hN : finiteVal true e m = Nn) :
    ∃ qr, (finite true e q m hv).toAzRat? = some qr ∧ qr.sign = true ∧ qr.den = 1 ∧
      qr.num ≠ 0 ∧ qr.num.toNat = Nn := by
  have hv0 := finiteVal_true_pos e hv
  have hNn0 : 0 < Nn := by exact_mod_cast (hN ▸ hv0)
  obtain ⟨qr, hqr⟩ : ∃ qr, (finite true e q m hv).toAzRat? = some qr := ⟨_, rfl⟩
  have hval := toVal_of_toAzRat? _ qr hqr
  rw [toVal_finite, hN] at hval
  simp only [Option.some.injEq, EReal.coe_eq_coe_iff] at hval
  -- the rational is the integer `Nn`: sign `true`, denominator `1`
  have hD : (0 : ℝ) < qr.den.toNat := by exact_mod_cast AzRat.den_toNat_pos qr
  have hcast := AzRat.toRat_cast_eq qr
  have hsg : qr.sign = true := by
    by_contra hs
    rw [Bool.not_eq_true] at hs
    rw [hcast, hs] at hval
    simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast] at hval
    have : -(qr.num.toNat : ℝ) / qr.den.toNat ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hD.le
    have : (0 : ℝ) < Nn := by exact_mod_cast hNn0
    linarith
  rw [hcast, hsg] at hval
  simp only [↓reduceIte, Int.cast_natCast] at hval
  have hnum : qr.num.toNat = Nn * qr.den.toNat := by
    have : (qr.num.toNat : ℝ) = Nn * qr.den.toNat := by
      rw [eq_div_iff hD.ne'] at hval; linarith
    exact_mod_cast this
  have hcop : Nat.Coprime qr.num.toNat qr.den.toNat := (AzNat.coprime_iff _ _).mp qr.reduced
  have hden1 : qr.den.toNat = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop ⟨_, by rw [hnum, Nat.mul_comm]⟩ (dvd_refl _)
  rw [hden1, mul_one] at hnum
  have hd1 : qr.den = 1 := AzNat.toNat_injective (by rw [hden1]; rfl)
  have hn0 : qr.num ≠ 0 := fun h0 => by
    rw [h0, AzNat.toNat_zero] at hnum; omega
  exact ⟨qr, hqr, hsg, hd1, hn0, hnum⟩

/-- `logBaseExact? = none` for a positive float and a base that is not a power of two: the
logarithm is irrational. -/
theorem irrational_of_logBaseExact?_none (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64) (hnp : ∀ i, b.toNat ≠ 2 ^ i)
    (h : logBaseExact? (finite true e q m hv) b = none) :
    Irrational (Real.log (finiteVal true e m) / Real.log b.toNat) := by
  by_cases hint : ∃ n : ℤ, finiteVal true e m = n
  · obtain ⟨N, hN⟩ := hint
    have hv0 := finiteVal_true_pos e hv
    have hNpos : 0 < N := by exact_mod_cast (hN ▸ hv0)
    obtain ⟨Nn, hNn⟩ : ∃ Nn : ℕ, N = Nn := ⟨N.toNat, by omega⟩
    rw [hNn, Int.cast_natCast] at hN
    rw [hN]
    apply irrational_log_div_log_of_int b hb hb64 Nn (by omega)
    intro r hr
    -- `logBaseExact?` would have found it
    obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
    unfold logBaseExact? at h
    obtain ⟨qr, hqr, hsg, hd1, hn0, hnum⟩ := toAzRat?_of_nat e hv Nn hN
    rw [hqr] at h
    simp only [] at h
    rw [ite_eq_left ⟨hsg, hd1, hn0⟩] at h
    rw [Option.map_eq_none_iff] at h
    have := (AzNat.checkedLogBase_eq_none_iff _ _ hc2 hn0).mp h r
    rw [hnum] at this
    exact this hr
  · exact irrational_log_div_log_of_not_int e hv b hb hnp hint

/-! ### The rational version -/

/-- The primitive root fits in 64 bits. -/
theorem maxRootBase_lt_size (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64) :
    (maxRootBase b).1.toNat < UInt64.size := by
  obtain ⟨hcs, hs1, -, -⟩ := maxRootBase_spec b hb
  have : (maxRootBase b).1.toNat ≤ b.toNat := by
    rw [hcs]; exact Nat.le_self_pow (by omega) _
  have hsize : UInt64.size = 2 ^ 64 := by decide
  omega

theorem toNat_rootUInt (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64) :
    (UInt64.ofNat (maxRootBase b).1.toNat).toNat = (maxRootBase b).1.toNat :=
  UInt64.toNat_ofNat_of_lt' (maxRootBase_lt_size b hb hb64)

/-- The rational returned by `logBaseExactRat?` is `ln q / ln b`. -/
theorem logBaseExactRat?_some (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q) (b : AzNat)
    (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64) (r : AzRat) (h : logBaseExactRat? q b = some r) :
    Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat = (AzRat.toRat r : ℝ) := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
  have hcU := toNat_rootUInt b hb hb64
  unfold logBaseExactRat? at h
  simp only [] at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  rw [AzRat.checkedLogBaseAbs_eq_some_iff _ (by rw [hcU]; exact hc2) q e, hcU] at he
  have hqr : (0 : ℝ) < AzRat.toRat q := by exact_mod_cast hq
  rw [abs_of_pos hqr] at he
  have hlogc : 0 < Real.log (maxRootBase b).1.toNat := log_pos_of_two_le hc2
  rw [AzRat.toRat_ofAzInts, AzInt.toInt_ofInt, toInt_toAzInt, AzNat.toNat_ofNat, he, hcs,
    Real.log_zpow, Nat.cast_pow, Real.log_pow]
  push_cast
  field_simp

/-- `logBaseExactRat? = none` for a positive rational: the logarithm is irrational. -/
theorem irrational_of_logBaseExactRat?_none (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q)
    (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64) (h : logBaseExactRat? q b = none) :
    Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log b.toNat) := by
  obtain ⟨-, -, hc2, -⟩ := maxRootBase_spec b hb
  have hcU := toNat_rootUInt b hb hb64
  unfold logBaseExactRat? at h
  simp only [] at h
  rw [Option.map_eq_none_iff, AzRat.checkedLogBaseAbs_eq_none_iff _ (by rw [hcU]; exact hc2),
    hcU] at h
  have hqr : (0 : ℝ) < AzRat.toRat q := by exact_mod_cast hq
  refine irrational_log_div_log_of_rat b hb hb64 _ hq fun e he => h e ?_
  rw [abs_of_pos hqr]
  exact he

/-! ### `log_b (1 + x)` -/

/-- The rational returned by `logBaseP1Exact?` is `ln (1 + x) / ln b`. -/
theorem logBaseP1Exact?_some (x : AzFloat) (b : AzNat) (hb : 2 ≤ b.toNat) (r : AzRat)
    (h : logBaseP1Exact? x b = some r) :
    ∃ v : ℝ, x.toVal = some (v : EReal) ∧ 0 < v ∧
      Real.log (1 + v) / Real.log b.toNat = (AzRat.toRat r : ℝ) := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
  unfold logBaseP1Exact? at h
  split_ifs at h with hint
  rcases hq : x.toAzRat? with _ | q
  · rw [hq] at h; cases h
  · rw [hq] at h
    simp only [] at h
    split_ifs at h with hg
    obtain ⟨hsg, hd1, hn0⟩ := hg
    have h10 : (q.num + 1).toNat = q.num.toNat + 1 := by rw [AzNat.toNat_add]; rfl
    have hne1 : q.num + 1 ≠ 0 := fun h0 => by rw [h0, AzNat.toNat_zero] at h10; omega
    rcases hr : AzNat.checkedLogBase (maxRootBase b).1 (q.num + 1) with _ | e
    · rw [hr] at h; cases h
    · rw [hr, Option.map_some, Option.some.injEq] at h
      have hne : (q.num + 1).toNat = (maxRootBase b).1.toNat ^ e :=
        (AzNat.checkedLogBase_eq_some_iff _ _ hc2 hne1 e).mp hr
      have hv := toVal_of_toAzRat? x q hq
      rw [toRat_eq_of_int_den_one q hsg hd1] at hv
      have hnpos : (0 : ℝ) < q.num.toNat := by
        exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0)
      refine ⟨_, hv, hnpos, ?_⟩
      rw [← h, AzRat.toRat_ofAzInts, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat,
        AzNat.toNat_ofNat]
      push_cast
      have hlogc : 0 < Real.log (maxRootBase b).1.toNat := log_pos_of_two_le hc2
      rw [h10] at hne
      have h1v : (1 : ℝ) + q.num.toNat = (maxRootBase b).1.toNat ^ e := by
        rw [add_comm]; exact_mod_cast hne
      rw [h1v, hcs, Nat.cast_pow, Real.log_pow, Real.log_pow]
      field_simp

/-- `1 + (±o) · 2^(−t) = u / 2^t` with `u` odd (`o` odd, `t ≥ 1`, and `o < 2^t` for the minus
sign). -/
theorem one_add_odd_mul_eq (o t : ℕ) (hodd : Odd o) (ht : 1 ≤ t) (σ : Bool)
    (hlt : σ = false → o < 2 ^ t) :
    ∃ u : ℕ, Odd u ∧
      1 + (if σ then 1 else -1 : ℝ) * (o * ((2 : ℝ) ^ t)⁻¹) = u / 2 ^ t := by
  have h2 : (2 : ℝ) ^ t ≠ 0 := by positivity
  have heven : Even (2 ^ t) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  cases σ with
  | true =>
    refine ⟨2 ^ t + o, heven.add_odd hodd, ?_⟩
    simp only [↓reduceIte, one_mul]
    push_cast
    field_simp
  | false =>
    refine ⟨2 ^ t - o, Nat.Even.sub_odd (hlt rfl).le heven hodd, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    rw [Nat.cast_sub (hlt rfl).le]
    push_cast
    field_simp
    ring

/-- For a non-integer float `x > −1`, `1 + x = u / 2^t` with `u` odd and `t ≥ 1`. -/
theorem one_add_finiteVal_eq_odd_div_two_pow (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (hni : ¬ ∃ n : ℤ, finiteVal s e m = n) :
    ∃ u t : ℕ, Odd u ∧ 1 ≤ t ∧ 1 + finiteVal s e m = u / 2 ^ t := by
  obtain ⟨o, j, hodd, hval⟩ := finiteVal_eq_odd_mul_zpow e hv
  -- the exponent is negative
  have hj : j < 0 := by
    by_contra hj
    push Not at hj
    apply hni
    cases s with
    | true =>
      refine ⟨o * 2 ^ j.toNat, ?_⟩
      rw [hval]; push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hj]
    | false =>
      refine ⟨-(o * 2 ^ j.toNat), ?_⟩
      rw [finiteVal_false, hval]; push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hj]
  obtain ⟨t, ht, ht1⟩ : ∃ t : ℕ, j = -(t : ℤ) ∧ 1 ≤ t := ⟨j.natAbs, by omega, by omega⟩
  have hsv : finiteVal s e m = (if s then 1 else -1 : ℝ) * (o * ((2 : ℝ) ^ t)⁻¹) := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
      rw [finiteVal_false, hval, ht, zpow_neg, zpow_natCast]
    · simp only [↓reduceIte, one_mul]
      rw [hval, ht, zpow_neg, zpow_natCast]
  have hlt : s = false → o < 2 ^ t := by
    intro hs
    subst hs
    simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] at hsv
    rw [hsv] at hgt
    have h2 : (0 : ℝ) < 2 ^ t := by positivity
    have h1 : (o : ℝ) * ((2 : ℝ) ^ t)⁻¹ < 1 := by linarith
    rw [mul_inv_lt_iff₀ h2, one_mul] at h1
    exact_mod_cast h1
  obtain ⟨u, hu, hu'⟩ := one_add_odd_mul_eq o t hodd ht1 s hlt
  exact ⟨u, t, hu, ht1, by rw [hsv]; exact hu'⟩

/-- A non-integer float `x > −1` has an irrational `log_b (1 + x)` for a base that is not a
power of two. -/
theorem irrational_log_div_log_one_add_of_not_int (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64)
    (hnp : ∀ i, b.toNat ≠ 2 ^ i) (hgt : -1 < finiteVal s e m)
    (hni : ¬ ∃ n : ℤ, finiteVal s e m = n) :
    Irrational (Real.log (1 + finiteVal s e m) / Real.log b.toNat) := by
  obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
  obtain ⟨u, t, hu, ht1, hval⟩ := one_add_finiteVal_eq_odd_div_two_pow s e hv hgt hni
  obtain ⟨qr, hqr⟩ : ∃ qr, (finite s e q m hv).toAzRat? = some qr := ⟨_, rfl⟩
  have hrx := toVal_of_toAzRat? _ qr hqr
  rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hrx
  have hpos : 0 < 1 + finiteVal s e m := by linarith
  have h1rx : ((1 + AzRat.toRat qr : ℚ) : ℝ) = 1 + finiteVal s e m := by push_cast; rw [hrx]
  rw [← h1rx]
  apply irrational_log_div_log_of_rat b hb hb64 (1 + AzRat.toRat qr)
    (by exact_mod_cast (h1rx ▸ hpos))
  intro r hr
  rw [h1rx, hval] at hr
  set c := (maxRootBase b).1.toNat with hc
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  rcases le_or_gt 0 r with hn | hn
  · -- `u = c^n · 2^t`: even against odd
    obtain ⟨n, hn'⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, by omega⟩
    rw [hn', zpow_natCast, div_eq_iff h2.ne'] at hr
    have hnat : u = c ^ n * 2 ^ t := by exact_mod_cast hr
    have heven : Even u := by
      rw [hnat]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left _
    exact (Nat.not_even_iff_odd.mpr hu) heven
  · -- `u · c^n = 2^t`: `c` is a power of two
    obtain ⟨n, hn', hn1⟩ : ∃ n : ℕ, r = -(n : ℤ) ∧ 1 ≤ n := ⟨r.natAbs, by omega, by omega⟩
    rw [hn', zpow_neg, zpow_natCast] at hr
    have hnat : u * c ^ n = 2 ^ t := by
      have hc' : ((c : ℝ) ^ n) ≠ 0 := by positivity
      field_simp at hr
      exact_mod_cast hr
    have hdvd : c ^ n ∣ 2 ^ t := ⟨_, by rw [← hnat, mul_comm]⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hcdvd : c ∣ 2 ^ i := by rw [← hi]; exact dvd_pow_self _ (by omega)
    obtain ⟨i', -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcdvd
    exact hnp (i' * (maxRootBase b).2) (by rw [hcs, hi', ← pow_mul])

/-- `logBaseP1Exact? = none` for a float `x > −1` and a base that is not a power of two: the
logarithm `log_b (1 + x)` is irrational. -/
theorem irrational_of_logBaseP1Exact?_none (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (b : AzNat) (hb : 2 ≤ b.toNat) (hb64 : b.toNat < 2 ^ 64)
    (hnp : ∀ i, b.toNat ≠ 2 ^ i) (hgt : -1 < finiteVal s e m)
    (h : logBaseP1Exact? (finite s e q m hv) b = none) :
    Irrational (Real.log (1 + finiteVal s e m) / Real.log b.toNat) := by
  by_cases hint : ∃ n : ℤ, finiteVal s e m = n
  · obtain ⟨N, hN⟩ := hint
    cases s with
    | false =>
      -- a negative integer above `−1`: impossible
      exfalso
      have hpos := finiteVal_true_pos e hv
      rw [finiteVal_false] at hN hgt
      have h1 : (-1 : ℝ) < N := by rw [← hN]; exact hgt
      have h2 : (N : ℝ) < 0 := by rw [← hN]; linarith
      have h1' : (-1 : ℤ) < N := by exact_mod_cast h1
      have h2' : N < 0 := by exact_mod_cast h2
      omega
    | true =>
      have hv0 := finiteVal_true_pos e hv
      have hNpos : 0 < N := by exact_mod_cast (hN ▸ hv0)
      obtain ⟨Nn, hNn⟩ : ∃ Nn : ℕ, N = Nn := ⟨N.toNat, by omega⟩
      rw [hNn, Int.cast_natCast] at hN
      rw [hN]
      have h1N : (1 : ℝ) + Nn = ((Nn + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h1N]
      apply irrational_log_div_log_of_int b hb hb64 (Nn + 1) (by omega)
      intro r hr
      -- `logBaseP1Exact?` would have found it
      obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBase_spec b hb
      obtain ⟨qr, hqr, hsg, hd1, hn0, hnum⟩ := toAzRat?_of_nat e hv Nn hN
      unfold logBaseP1Exact? at h
      rw [ite_eq_left ((isInteger_finite true e hv).mpr ⟨Nn, by rw [Int.cast_natCast]; exact hN⟩),
        hqr] at h
      simp only [] at h
      rw [ite_eq_left ⟨hsg, hd1, hn0⟩, Option.map_eq_none_iff] at h
      have h10 : (qr.num + 1).toNat = Nn + 1 := by rw [AzNat.toNat_add, hnum]; rfl
      have hne1 : qr.num + 1 ≠ 0 := fun h0 => by rw [h0, AzNat.toNat_zero] at h10; omega
      have := (AzNat.checkedLogBase_eq_none_iff _ _ hc2 hne1).mp h r
      rw [h10] at this
      exact this hr
  · exact irrational_log_div_log_one_add_of_not_int s e hv b hb hb64 hnp hgt hint

/-! ### A float base: the odd part and the dyadic exponent -/

theorem toInt_ne_zero_of_ne_zero' {k : AzInt} (hk : k ≠ 0) : k.toInt ≠ 0 := fun h =>
  hk (by rw [← AzInt.ofInt_toInt k, h, AzInt.ofInt_zero])

/-- `m = 2^(twoAdic m) · oddPart m` with `oddPart m` odd, and `twoAdic m < size m`. -/
theorem oddPart_spec (m : AzNat) (hm : m ≠ 0) :
    m.toNat = 2 ^ twoAdic m * (oddPart m).toNat ∧ Odd (oddPart m).toNat ∧ twoAdic m < m.size := by
  have hk : twoAdic m = m.toNat.factorization 2 := by
    unfold twoAdic
    rw [AzNat.trailingZeros_eq_padicValNat m hm, Nat.factorization_def _ Nat.prime_two]
    rfl
  have hn : m.toNat ≠ 0 := toNat_ne_zero_of_ne_zero hm
  have hdvd : 2 ^ m.toNat.factorization 2 ∣ m.toNat := Nat.ordProj_dvd _ _
  have hop : (oddPart m).toNat = m.toNat / 2 ^ twoAdic m := by
    unfold oddPart
    exact AzNat.toNat_shiftRight m (twoAdic m)
  refine ⟨?_, ?_, ?_⟩
  · rw [hop, hk, Nat.mul_div_cancel' hdvd]
  · rw [hop, hk]
    have := Nat.not_dvd_ordCompl Nat.prime_two hn
    exact Nat.odd_iff.mpr (by omega)
  · obtain ⟨-, hsz⟩ := AzNat.size_bounds m hm
    have : 2 ^ twoAdic m ≤ m.toNat := by rw [hk]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    by_contra hge
    push Not at hge
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hge
    omega

/-- A positive finite float is `oddPart · 2^dyadicExp`. -/
theorem finiteVal_eq_oddPart (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal true e m = ((oddPart m).toNat : ℝ) * (2 : ℝ) ^ (dyadicExp e m).toInt := by
  have hm : m ≠ 0 := by
    intro h
    have := (toNat_bounds_of_valid hv).1
    rw [h, AzNat.toNat_zero] at this
    have := Nat.one_le_two_pow (n := alignedBits q - 1)
    omega
  obtain ⟨hdec, -, hlt⟩ := oddPart_spec m hm
  have hexp : (dyadicExp e m).toInt = e.toInt - m.size + twoAdic m := by
    unfold dyadicExp
    rw [AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat, Nat.cast_sub hlt.le]
    ring
  unfold finiteVal
  simp only [↓reduceIte, one_mul]
  rw [hdec, hexp, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_natCast]
  push_cast
  ring

/-- `o · 2^I = s · 2^J` with `o`, `s` odd forces `o = s` and `I = J`. -/
theorem odd_mul_two_zpow_inj {o s : ℕ} (ho : Odd o) (hs : Odd s) {I J : ℤ}
    (h : (o : ℝ) * (2 : ℝ) ^ I = (s : ℝ) * (2 : ℝ) ^ J) : o = s ∧ I = J := by
  have key : ∀ {o s : ℕ} {I J : ℤ}, Odd o → I ≤ J →
      (o : ℝ) * (2 : ℝ) ^ I = (s : ℝ) * (2 : ℝ) ^ J → o = s ∧ I = J := by
    intro o s I J ho hIJ h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, J = I + k := ⟨(J - I).toNat, by omega⟩
    have h2 : (0 : ℝ) < (2 : ℝ) ^ I := zpow_pos two_pos _
    have hnat : o = s * 2 ^ k := by
      have : (o : ℝ) * (2 : ℝ) ^ I = ((s * 2 ^ k : ℕ) : ℝ) * (2 : ℝ) ^ I := by
        rw [h, hk, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_natCast]
        push_cast
        ring
      exact_mod_cast mul_right_cancel₀ h2.ne' this
    rcases k with _ | k
    · rw [pow_zero, mul_one] at hnat
      exact ⟨hnat, by omega⟩
    · exfalso
      have : Even o := by
        rw [hnat]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left _
      exact (Nat.not_even_iff_odd.mpr ho) this
  rcases le_total I J with hIJ | hIJ
  · exact key ho hIJ h
  · obtain ⟨h1, h2⟩ := key hs hIJ h.symm
    exact ⟨h1.symm, h2.symm⟩

/-- Separating `x^d = b^n` for `x = o · 2^i`, `b = s · 2^j` (`o`, `s` odd): the odd parts and the
2-exponents match. -/
theorem pow_eq_zpow_sep {o s : ℕ} (ho : Odd o) (hs : Odd s) {i j : ℤ} {d : ℕ} (hd : 1 ≤ d)
    {n : ℤ} (key : ((o : ℝ) * 2 ^ i) ^ d = ((s : ℝ) * 2 ^ j) ^ n) :
    o ^ d = s ^ n.toNat ∧ (n < 0 → o = 1 ∧ s = 1) ∧ i * d = j * n := by
  have ho0 : 0 < o := ho.pos
  have hs0 : 0 < s := hs.pos
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
    have hG : ((o ^ d : ℕ) : ℝ) * 2 ^ (i * d) = ((s ^ N : ℕ) : ℝ) * 2 ^ (j * N) := by
      push_cast
      rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
      rw [hN, zpow_natCast] at key
      exact key
    obtain ⟨h1, h2⟩ := odd_mul_two_zpow_inj ho.pow hs.pow hG
    refine ⟨?_, fun h => absurd h (by omega), by rw [hN]; exact h2⟩
    rw [hN, Int.toNat_natCast]
    exact h1
  · obtain ⟨N, hN, hN1⟩ : ∃ N : ℕ, n = -(N : ℤ) ∧ 1 ≤ N := ⟨n.natAbs, by omega, by omega⟩
    have hG : ((o ^ d * s ^ N : ℕ) : ℝ) * 2 ^ (i * d + j * N) = ((1 : ℕ) : ℝ) * 2 ^ (0 : ℤ) := by
      push_cast
      rw [zpow_zero, mul_one, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_mul, zpow_mul,
        zpow_natCast, zpow_natCast]
      rw [hN, zpow_neg, zpow_natCast] at key
      have hkey1 : ((o : ℝ) * 2 ^ i) ^ d * ((s : ℝ) * 2 ^ j) ^ N = 1 := by
        rw [key]; exact inv_mul_cancel₀ (by positivity)
      rw [mul_pow, mul_pow] at hkey1
      linear_combination hkey1
    obtain ⟨h1, h2⟩ := odd_mul_two_zpow_inj (ho.pow.mul hs.pow) odd_one hG
    have ho1 := Nat.eq_one_of_mul_eq_one_right h1
    have hs1 := Nat.eq_one_of_mul_eq_one_left h1
    have ho1' : o = 1 := (Nat.pow_eq_one.mp ho1).resolve_right (by omega)
    have hs1' : s = 1 := (Nat.pow_eq_one.mp hs1).resolve_right (by omega)
    refine ⟨?_, fun _ => ⟨ho1', hs1'⟩, ?_⟩
    · rw [ho1', hN, one_pow, hs1', one_pow]
    · rw [hN]; linarith

/-- The reduced fraction `n / d` of a rational: numerator and denominator. -/
theorem num_den_of_div {n : ℤ} {d : ℕ} (hd : 1 ≤ d) (hcop : Nat.Coprime n.natAbs d) :
    ((n : ℚ) / d).num = n ∧ ((n : ℚ) / d).den = d := by
  have hd0 : (0 : ℤ) < d := by omega
  have h1 := Rat.num_div_eq_of_coprime hd0 (by simpa using hcop)
  have h2 := Rat.den_div_eq_of_coprime hd0 (by simpa using hcop)
  push_cast at h1 h2
  exact ⟨h1, by exact_mod_cast h2⟩

theorem toRat_num (q : AzRat) :
    (AzRat.toRat q).num = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl

theorem toRat_den (q : AzRat) : (AzRat.toRat q).den = q.den.toNat := rfl

/-- The rational returned by `logBaseFloatExact?` is `ln x / ln b`. -/
theorem logBaseFloatExact?_some (i : AzInt) (o : AzNat) (j : AzInt) (s : AzNat)
    (ho : Odd o.toNat) (hs : Odd s.toNat) (hb1 : (s.toNat : ℝ) * (2 : ℝ) ^ j.toInt ≠ 1) (r : AzRat)
    (h : logBaseFloatExact? i o j s = some r) :
    Real.log ((o.toNat : ℝ) * 2 ^ i.toInt) / Real.log ((s.toNat : ℝ) * 2 ^ j.toInt)
      = (AzRat.toRat r : ℝ) := by
  have ho0 : 0 < o.toNat := ho.pos
  have hs0 : 0 < s.toNat := hs.pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlogb : Real.log ((s.toNat : ℝ) * 2 ^ j.toInt) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) hb1
  unfold logBaseFloatExact? at h
  simp only [] at h
  split_ifs at h with hj hi hsign hchk hone
  · -- an odd integer base
    subst hj; subst hi
    simp only [AzInt.toInt_zero, zpow_zero, mul_one] at hlogb ⊢
    have hs2 : 2 ≤ s.toNat := by
      rcases Nat.lt_or_ge s.toNat 2 with h2 | h2
      · exfalso
        have : s.toNat = 1 := by omega
        apply hlogb
        rw [this, Nat.cast_one, Real.log_one]
      · exact h2
    obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBaseBounded_spec s s.size hs2
    rw [Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hok := (AzNat.checkedLogBase_eq_some_iff _ _ hc2
      (fun h0 => by rw [h0, AzNat.toNat_zero] at ho0; omega) k).mp hk
    have hlogc : 0 < Real.log (maxRootBaseBounded s s.size).1.toNat := log_pos_of_two_le hc2
    rw [AzRat.toRat_ofAzInts, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat,
      hok, hcs, Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
    push_cast
    field_simp
  · -- `b = s · 2^j` with `j ≠ 0`, `a > 0`: `o = c^a`, `s = c^e`
    rw [Option.some.injEq] at h
    subst h
    set r := AzRat.ofAzInts i j with hr
    obtain ⟨hpow_s, hpow_o, hroot⟩ := hchk
    have hj' : j.toInt ≠ 0 := toInt_ne_zero_of_ne_zero' hj
    have hd : 1 ≤ r.den.toNat := Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero r.den_nz)
    -- the common root `c`
    set c := (s.rootInt r.den.toNat).toNat with hc
    have hsc : s.toNat = c ^ r.den.toNat := by
      have := (AzNat.isPow_eq_true_iff s _ hd).mp hpow_s
      rw [hc, AzNat.toNat_rootInt]
      exact ((AzNat.rootIntNat_pow_eq_iff _ _ hd).mpr this).symm
    have hoc : o.toNat = c ^ r.num.toNat := by
      rcases Nat.eq_zero_or_pos r.num.toNat with h0 | h0
      · -- `a = 0`: `o = 1`
        rw [h0, pow_zero]
        unfold AzNat.isPow at hpow_o
        rw [h0, decide_eq_true_iff] at hpow_o
        have := congrArg AzNat.toNat hpow_o
        rw [AzNat.toNat_pow, pow_zero] at this
        exact this.symm
      · have := (AzNat.isPow_eq_true_iff o _ h0).mp hpow_o
        rw [hc, hroot, AzNat.toNat_rootInt]
        exact ((AzNat.rootIntNat_pow_eq_iff _ _ h0).mpr this).symm
    -- the value `i / j` is `a / e`
    have hval : (AzRat.toRat r : ℝ) = (i.toInt : ℝ) / j.toInt := by
      rw [hr, AzRat.toRat_ofAzInts]; push_cast; rfl
    have hval' : (AzRat.toRat r : ℝ) = (r.num.toNat : ℝ) / r.den.toNat := by
      rw [AzRat.toRat_cast_eq, hsign]; push_cast; rfl
    have hid : (i.toInt : ℝ) * r.den.toNat = j.toInt * r.num.toNat := by
      have hdr : (r.den.toNat : ℝ) ≠ 0 := by positivity
      have := hval.symm.trans hval'
      rw [div_eq_div_iff (by exact_mod_cast hj') hdr] at this
      linarith
    have hc0 : (c : ℝ) ≠ 0 := by
      intro h0
      have : c = 0 := by exact_mod_cast h0
      rw [this, zero_pow (by omega)] at hsc
      omega
    rw [hval, div_eq_div_iff hlogb (by exact_mod_cast hj'), hsc, hoc, Nat.cast_pow, Nat.cast_pow,
      Real.log_mul (pow_ne_zero _ hc0) (zpow_ne_zero _ two_ne_zero),
      Real.log_mul (pow_ne_zero _ hc0) (zpow_ne_zero _ two_ne_zero),
      Real.log_pow, Real.log_pow, Real.log_zpow, Real.log_zpow]
    linear_combination (-(Real.log (c : ℝ))) * hid
  · -- `a < 0`: `o = s = 1`, `x = 2^i`, `b = 2^j`
    rw [Option.some.injEq] at h
    subst h
    obtain ⟨ho1, hs1⟩ := hone
    subst ho1; subst hs1
    rw [AzRat.toRat_ofAzInts, AzNat.toNat_one, Nat.cast_one, one_mul, one_mul, Real.log_zpow,
      Real.log_zpow]
    push_cast
    have hj' : (j.toInt : ℝ) ≠ 0 := by exact_mod_cast toInt_ne_zero_of_ne_zero' hj
    field_simp

/-- `logBaseFloatExact? = none` for `x ≠ 1` and `b ≠ 1`: the logarithm is irrational. -/
theorem irrational_of_logBaseFloatExact?_none (i : AzInt) (o : AzNat) (j : AzInt) (s : AzNat)
    (ho : Odd o.toNat) (hs : Odd s.toNat) (hb1 : (s.toNat : ℝ) * (2 : ℝ) ^ j.toInt ≠ 1)
    (hx1 : (o.toNat : ℝ) * (2 : ℝ) ^ i.toInt ≠ 1) (h : logBaseFloatExact? i o j s = none) :
    Irrational
      (Real.log ((o.toNat : ℝ) * 2 ^ i.toInt) / Real.log ((s.toNat : ℝ) * 2 ^ j.toInt)) := by
  have ho0 : 0 < o.toNat := ho.pos
  have hs0 : 0 < s.toNat := hs.pos
  have hxpos : (0 : ℝ) < (o.toNat : ℝ) * 2 ^ i.toInt := by positivity
  have hbpos : (0 : ℝ) < (s.toNat : ℝ) * 2 ^ j.toInt := by positivity
  rintro ⟨r, hr⟩
  have key := pow_eq_zpow_of_log_div_log hxpos hbpos hb1 r hr
  have hd : 1 ≤ r.den := r.den_pos
  have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
  obtain ⟨h1, hneg, h2⟩ := pow_eq_zpow_sep ho hs hd key
  -- `x = 1` is excluded: `o = 1` and `i = 0` together
  have hnot1 : ¬ (o.toNat = 1 ∧ i.toInt = 0) := fun ⟨h1', h2'⟩ => hx1 (by
    rw [h1', h2', Nat.cast_one, zpow_zero, mul_one])
  unfold logBaseFloatExact? at h
  simp only [] at h
  split_ifs at h with hj hi hsign hchk hone
  · -- an odd integer base
    subst hj; subst hi
    rw [AzInt.toInt_zero, zpow_zero, mul_one] at hb1
    rw [AzInt.toInt_zero] at hnot1
    have hs2 : 2 ≤ s.toNat := by
      rcases Nat.lt_or_ge s.toNat 2 with h2 | h2
      · exfalso
        have : s.toNat = 1 := by omega
        apply hb1
        rw [this, Nat.cast_one]
      · exact h2
    obtain ⟨hcs, hs1, hc2, -⟩ := maxRootBaseBounded_spec s s.size hs2
    have hn0 : 0 ≤ r.num := by
      by_contra hn
      push Not at hn
      obtain ⟨-, hs1'⟩ := hneg hn
      omega
    have hN1 : 1 ≤ r.num.toNat := by
      by_contra hN
      push Not at hN
      have hN0 : r.num.toNat = 0 := by omega
      rw [hN0, pow_zero] at h1
      exact hnot1 ⟨(Nat.pow_eq_one.mp h1).resolve_right (by omega), rfl⟩
    have hbt : s.toNat < 2 ^ (s.size + 1) := by
      have := (AzNat.size_bounds s (fun h0 => by rw [h0, AzNat.toNat_zero] at hs0; omega)).2
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨k, hk⟩ := exists_eq_pow_maxRootBounded_of_pow_eq_pow s s.size hs2 hbt ho0 hd h1
    rw [Option.map_eq_none_iff] at h
    exact (AzNat.checkedLogBase_eq_none_iff _ _ hc2
      (fun h0 => by rw [h0, AzNat.toNat_zero] at ho0; omega)).mp h k hk
  · -- `j = 0`, `i ≠ 0`: impossible, `i d = j n = 0`
    subst hj
    rw [AzInt.toInt_zero, zero_mul] at h2
    have : i.toInt = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · omega
    exact hi (by rw [← AzInt.ofInt_toInt i, this, AzInt.ofInt_zero])
  · -- `j ≠ 0`, the reduced fraction is positive: the check would have passed
    set r' := AzRat.ofAzInts i j with hr'
    have hj' : j.toInt ≠ 0 := toInt_ne_zero_of_ne_zero' hj
    -- `toRat r' = n / d`
    have hval : AzRat.toRat r' = (r.num : ℚ) / r.den := by
      rw [hr', AzRat.toRat_ofAzInts, div_eq_div_iff (by exact_mod_cast hj') (by positivity)]
      exact_mod_cast (by linarith : i.toInt * r.den = r.num * j.toInt)
    obtain ⟨hnum, hden⟩ := num_den_of_div hd hcop
    rw [← hval, toRat_num] at hnum
    rw [← hval, toRat_den] at hden
    simp only [hsign, ↓reduceIte] at hnum
    have hN : r.num.toNat = r'.num.toNat := by omega
    have hN1 : 1 ≤ r'.num.toNat := by
      by_contra hN0
      push Not at hN0
      have : r.num.toNat = 0 := by omega
      rw [this, pow_zero] at h1
      have ho1 : o.toNat = 1 := (Nat.pow_eq_one.mp h1).resolve_right (by omega)
      have : r.num = 0 := by omega
      rw [this, mul_zero] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact hnot1 ⟨ho1, h⟩
      · omega
    rw [hN, ← hden] at h1
    have hcop' : Nat.Coprime r'.den.toNat r'.num.toNat := by
      have hna : r.num.natAbs = r.num.toNat := by omega
      rw [hden, ← hN, ← hna]; exact hcop.symm
    obtain ⟨c, hoc, hsc⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcop' h1
    have hd' : 1 ≤ r'.den.toNat := by omega
    apply hchk
    refine ⟨(AzNat.isPow_eq_true_iff s _ hd').mpr ⟨c, hsc.symm⟩,
      (AzNat.isPow_eq_true_iff o _ hN1).mpr ⟨c, hoc.symm⟩, ?_⟩
    apply AzNat.toNat_injective
    rw [AzNat.toNat_rootInt, AzNat.toNat_rootInt]
    have e1 : AzNat.rootIntNat s.toNat r'.den.toNat = c := by
      apply Nat.pow_left_injective (by omega : r'.den.toNat ≠ 0)
      show AzNat.rootIntNat s.toNat r'.den.toNat ^ r'.den.toNat = c ^ r'.den.toNat
      rw [(AzNat.rootIntNat_pow_eq_iff _ _ hd').mpr ⟨c, hsc.symm⟩, hsc]
    have e2 : AzNat.rootIntNat o.toNat r'.num.toNat = c := by
      apply Nat.pow_left_injective (by omega : r'.num.toNat ≠ 0)
      show AzNat.rootIntNat o.toNat r'.num.toNat ^ r'.num.toNat = c ^ r'.num.toNat
      rw [(AzNat.rootIntNat_pow_eq_iff _ _ hN1).mpr ⟨c, hoc.symm⟩, hoc]
    rw [e1, e2]
  · -- the reduced fraction is negative or zero: `o = s = 1`, or `x = 1`
    set r' := AzRat.ofAzInts i j with hr'
    have hj' : j.toInt ≠ 0 := toInt_ne_zero_of_ne_zero' hj
    have hval : AzRat.toRat r' = (r.num : ℚ) / r.den := by
      rw [hr', AzRat.toRat_ofAzInts, div_eq_div_iff (by exact_mod_cast hj') (by positivity)]
      exact_mod_cast (by linarith : i.toInt * r.den = r.num * j.toInt)
    obtain ⟨hnum, -⟩ := num_den_of_div hd hcop
    rw [← hval, toRat_num] at hnum
    simp only [hsign, Bool.false_eq_true, ↓reduceIte] at hnum
    rcases lt_or_eq_of_le (by omega : r.num ≤ 0) with hn | hn
    · obtain ⟨ho1, hs1⟩ := hneg hn
      exact hone ⟨AzNat.toNat_injective (by rw [ho1]; rfl),
        AzNat.toNat_injective (by rw [hs1]; rfl)⟩
    · have : r.num.toNat = 0 := by omega
      rw [this, pow_zero] at h1
      have ho1 : o.toNat = 1 := (Nat.pow_eq_one.mp h1).resolve_right (by omega)
      rw [hn, mul_zero] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact hnot1 ⟨ho1, h⟩
      · omega

/-! ### The float forms -/

theorem significand_ne_zero_of_valid {q : ℕ} {m : AzNat} (hv : FiniteValid q m) : m ≠ 0 := by
  intro h
  have := (toNat_bounds_of_valid hv).1
  rw [h, AzNat.toNat_zero] at this
  have := Nat.one_le_two_pow (n := alignedBits q - 1)
  omega

/-- `x = 1` is excluded by a failed `eqIEEE` test against `one`. -/
theorem finiteVal_ne_one_of_not_eqIEEE (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h : ¬ eqIEEE (finite true e q m hv) one = true) : finiteVal true e m ≠ 1 := fun h1 =>
  h ((eqIEEE_iff _ _).mpr ⟨((1 : ℝ) : EReal), by rw [toVal_finite, h1], toVal_one'⟩)

/-- The value of `logBaseFloatExact?` on the odd-part decompositions of two floats. -/
theorem logBaseFloat_exact_value (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (r : AzRat)
    (h : logBaseFloatExact? (dyadicExp ex mx) (oddPart mx) (dyadicExp eb mb) (oddPart mb)
      = some r) :
    Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb) = (AzRat.toRat r : ℝ) := by
  rw [finiteVal_eq_oddPart eb hvb] at hb1 ⊢
  rw [finiteVal_eq_oddPart ex hvx]
  exact logBaseFloatExact?_some _ _ _ _ (oddPart_spec mx (significand_ne_zero_of_valid hvx)).2.1
    (oddPart_spec mb (significand_ne_zero_of_valid hvb)).2.1 hb1 r h

/-- Irrationality of `log_b x` when `logBaseFloatExact?` finds nothing. -/
theorem irrational_logBaseFloat_of_none (ex : AzInt) {qx : ℕ} {mx : AzNat}
    (hvx : FiniteValid qx mx) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (hx1 : finiteVal true ex mx ≠ 1)
    (h : logBaseFloatExact? (dyadicExp ex mx) (oddPart mx) (dyadicExp eb mb) (oddPart mb)
      = none) :
    Irrational (Real.log (finiteVal true ex mx) / Real.log (finiteVal true eb mb)) := by
  rw [finiteVal_eq_oddPart eb hvb] at hb1 ⊢
  rw [finiteVal_eq_oddPart ex hvx] at hx1 ⊢
  exact irrational_of_logBaseFloatExact?_none _ _ _ _
    (oddPart_spec mx (significand_ne_zero_of_valid hvx)).2.1
    (oddPart_spec mb (significand_ne_zero_of_valid hvb)).2.1 hb1 hx1 h

/-! ### `1 + x` -/

theorem abs_toNat_eq_natAbs (k : AzInt) : k.abs.toNat = k.toInt.natAbs := by
  unfold AzInt.toInt
  cases k.sign <;> simp

theorem toNat_hShiftLeft (a : AzNat) (k : ℕ) : (a <<< k).toNat = a.toNat * 2 ^ k :=
  AzNat.toNat_shiftLeft a k

/-- `u · 2^(k − t) = (1 + x)` from `u = (1 + x) · 2^t` and `u = 2^k · o'`. -/
theorem one_add_eq_of_scaled {v : ℝ} {u o' k t : ℕ} (hdec : u = 2 ^ k * o')
    (huv : (u : ℝ) = (1 + v) * 2 ^ t) :
    1 + v = (o' : ℝ) * (2 : ℝ) ^ ((k : ℤ) - t) := by
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have key : (1 + v) * 2 ^ t = (o' : ℝ) * 2 ^ k := by
    rw [← huv, hdec]; push_cast; ring
  calc 1 + v = (1 + v) * 2 ^ t / 2 ^ t := by field_simp
    _ = (o' : ℝ) * 2 ^ k / 2 ^ t := by rw [key]
    _ = (o' : ℝ) * (2 : ℝ) ^ ((k : ℤ) - t) := by
        rw [zpow_sub₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]; ring

/-- `onePlusDyadic` decomposes `1 + x` into an odd part and a dyadic exponent. -/
theorem onePlusDyadic_spec (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (hgt : -1 < finiteVal s e m) :
    Odd (onePlusDyadic s (dyadicExp e m) (oddPart m)).1.toNat ∧
      1 + finiteVal s e m
        = ((onePlusDyadic s (dyadicExp e m) (oddPart m)).1.toNat : ℝ)
          * (2 : ℝ) ^ (onePlusDyadic s (dyadicExp e m) (oddPart m)).2.toInt := by
  have hm := significand_ne_zero_of_valid hv
  obtain ⟨-, hodd, -⟩ := oddPart_spec m hm
  have hval := finiteVal_eq_oddPart e hv
  set o := oddPart m with ho
  set i := dyadicExp e m with hi
  have hab : (i.abs.toNat : ℤ) = |i.toInt| := by
    rw [abs_toNat_eq_natAbs]; exact Int.natCast_natAbs _
  have ho0 : 0 < o.toNat := hodd.pos
  have hcancel : i.toInt < 0 → (2 : ℝ) ^ i.toInt * 2 ^ i.abs.toNat = 1 := by
    intro hneg
    rw [← zpow_natCast, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
      show i.toInt + (i.abs.toNat : ℤ) = 0 by rw [hab, abs_of_neg hneg]; ring, zpow_zero]
  unfold onePlusDyadic
  cases s with
  | true =>
    simp only [↓reduceIte]
    split_ifs with hsg
    · -- `i ≥ 0`: the integer `o · 2^i + 1`
      rw [AzInt.sign_eq_true_iff] at hsg
      have hi' : (i.abs.toNat : ℤ) = i.toInt := by rw [hab, abs_of_nonneg hsg]
      set n := (o <<< i.abs.toNat) + 1 with hn
      have hn0 : n ≠ 0 := by
        intro h0
        have := congrArg AzNat.toNat h0
        rw [hn, AzNat.toNat_add, AzNat.toNat_one, AzNat.toNat_zero] at this
        omega
      obtain ⟨hdec, hodd', -⟩ := oddPart_spec n hn0
      refine ⟨hodd', ?_⟩
      rw [toInt_toAzInt, AzNat.toNat_ofNat, zpow_natCast]
      have hnv : (n.toNat : ℝ) = 1 + finiteVal true e m := by
        rw [hval, hn, AzNat.toNat_add, AzNat.toNat_one, toNat_hShiftLeft]
        push_cast
        rw [← hi', zpow_natCast]
        ring
      rw [← hnv, hdec]
      push_cast
      ring
    · -- `i < 0`: `(2^t + o) / 2^t`
      rw [AzInt.sign_eq_true_iff] at hsg
      push Not at hsg
      set u := ((1 : AzNat) <<< i.abs.toNat) + o with hu
      have huN : u.toNat = 2 ^ i.abs.toNat + o.toNat := by
        rw [hu, AzNat.toNat_add, toNat_hShiftLeft, AzNat.toNat_one, one_mul]
      have hu0 : u ≠ 0 := by
        intro h0
        have := congrArg AzNat.toNat h0
        have h2 : 0 < 2 ^ i.abs.toNat := by positivity
        rw [huN, AzNat.toNat_zero] at this
        omega
      obtain ⟨hdec, hodd', -⟩ := oddPart_spec u hu0
      refine ⟨hodd', ?_⟩
      rw [AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat]
      apply one_add_eq_of_scaled hdec
      rw [huN, hval]
      push_cast
      linear_combination (-(o.toNat : ℝ)) * hcancel hsg
  | false =>
    -- `x < 0` above `−1`: `i < 0` and `o < 2^t`, the sum is `(2^t − o) / 2^t`
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [finiteVal_false, hval] at hgt
    have hneg : i.toInt < 0 := by
      by_contra h
      push Not at h
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ i.toInt := one_le_zpow₀ one_le_two h
      have h2 : (1 : ℝ) ≤ o.toNat := by exact_mod_cast ho0
      nlinarith
    have hlt : o.toNat < 2 ^ i.abs.toNat := by
      have h2 : (0 : ℝ) < 2 ^ i.abs.toNat := by positivity
      have : (o.toNat : ℝ) * (2 : ℝ) ^ i.toInt * 2 ^ i.abs.toNat < 1 * 2 ^ i.abs.toNat :=
        mul_lt_mul_of_pos_right (by linarith) h2
      rw [mul_assoc, hcancel hneg, mul_one, one_mul] at this
      exact_mod_cast this
    set u := ((1 : AzNat) <<< i.abs.toNat) - o with hu
    have huN : u.toNat = 2 ^ i.abs.toNat - o.toNat := by
      rw [hu, AzNat.toNat_sub, toNat_hShiftLeft, AzNat.toNat_one, one_mul]
    have hu0 : u ≠ 0 := by
      intro h0
      have := congrArg AzNat.toNat h0
      rw [huN, AzNat.toNat_zero] at this
      omega
    obtain ⟨hdec, hodd', -⟩ := oddPart_spec u hu0
    refine ⟨hodd', ?_⟩
    rw [AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat,
      finiteVal_false, hval]
    apply one_add_eq_of_scaled hdec
    rw [huN, Nat.cast_sub hlt.le]
    push_cast
    linear_combination (o.toNat : ℝ) * hcancel hneg

/-- The value of `logBaseFloatExact?` on `1 + x` and the base. -/
theorem logBaseFloatP1_exact_value (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (eb : AzInt) {qb : ℕ} {mb : AzNat}
    (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1) (r : AzRat)
    (h : logBaseFloatExact? (onePlusDyadic s (dyadicExp e m) (oddPart m)).2
      (onePlusDyadic s (dyadicExp e m) (oddPart m)).1 (dyadicExp eb mb) (oddPart mb) = some r) :
    Real.log (1 + finiteVal s e m) / Real.log (finiteVal true eb mb) = (AzRat.toRat r : ℝ) := by
  obtain ⟨hodd, hval⟩ := onePlusDyadic_spec s e hv hgt
  rw [finiteVal_eq_oddPart eb hvb] at hb1 ⊢
  rw [hval]
  exact logBaseFloatExact?_some _ _ _ _ hodd
    (oddPart_spec mb (significand_ne_zero_of_valid hvb)).2.1 hb1 r h

/-- Irrationality of `log_b (1 + x)` when `logBaseFloatExact?` finds nothing. -/
theorem irrational_logBaseFloatP1_of_none (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (eb : AzInt) {qb : ℕ} {mb : AzNat}
    (hvb : FiniteValid qb mb) (hb1 : finiteVal true eb mb ≠ 1)
    (h : logBaseFloatExact? (onePlusDyadic s (dyadicExp e m) (oddPart m)).2
      (onePlusDyadic s (dyadicExp e m) (oddPart m)).1 (dyadicExp eb mb) (oddPart mb) = none) :
    Irrational (Real.log (1 + finiteVal s e m) / Real.log (finiteVal true eb mb)) := by
  obtain ⟨hodd, hval⟩ := onePlusDyadic_spec s e hv hgt
  have hx1 : 1 + finiteVal s e m ≠ 1 := fun h1 => finiteVal_ne_zero s e hv (by linarith)
  rw [finiteVal_eq_oddPart eb hvb] at hb1 ⊢
  rw [hval] at hx1 ⊢
  exact irrational_of_logBaseFloatExact?_none _ _ _ _ hodd
    (oddPart_spec mb (significand_ne_zero_of_valid hvb)).2.1 hb1 hx1 h

/-! ### A rational argument -/

/-- A positive rational is `(n / d) · 2^i` with `n`, `d` its odd parts. -/
theorem toRat_eq_oddParts (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) :
    (AzRat.toRat q : ℝ)
      = ((oddPart q.num).toNat : ℝ) / (oddPart q.den).toNat * (2 : ℝ) ^ (ratDyadicExp q).toInt := by
  obtain ⟨hn, -, -⟩ := oddPart_spec q.num h0
  obtain ⟨hd, -, -⟩ := oddPart_spec q.den q.den_nz
  rw [AzRat.toRat_cast_eq, hs]
  simp only [↓reduceIte, Int.cast_natCast]
  unfold ratDyadicExp
  rw [AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.toNat_ofNat, AzNat.toNat_ofNat,
    zpow_sub₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast, hn, hd]
  push_cast
  have h1 : ((oddPart q.den).toNat : ℝ) ≠ 0 := by
    have := (oddPart_spec q.den q.den_nz).2.1.pos
    positivity
  field_simp

/-- The rational returned by `logBaseRatFloatExact?` is `ln q / ln b`. -/
theorem logBaseRatFloatExact?_some (i : AzInt) (n d : AzNat) (j : AzInt) (s : AzNat)
    (hn : Odd n.toNat) (hd : Odd d.toNat) (hs : Odd s.toNat)
    (hb1 : (s.toNat : ℝ) * (2 : ℝ) ^ j.toInt ≠ 1) (r : AzRat)
    (h : logBaseRatFloatExact? i n d j s = some r) :
    Real.log ((n.toNat : ℝ) / d.toNat * 2 ^ i.toInt) / Real.log ((s.toNat : ℝ) * 2 ^ j.toInt)
      = (AzRat.toRat r : ℝ) := by
  unfold logBaseRatFloatExact? at h
  split_ifs at h with hd1 hn1
  · subst hd1
    rw [AzNat.toNat_one, Nat.cast_one, div_one]
    exact logBaseFloatExact?_some i n j s hn hs hb1 r h
  · subst hn1
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have hv := logBaseFloatExact?_some (-i) d j s hd hs hb1 r' hr'
    rw [AzRat.toRat_neg, Rat.cast_neg, ← hv, AzNat.toNat_one, Nat.cast_one, ← neg_div,
      ← Real.log_inv, AzInt.toInt_neg, zpow_neg]
    congr 2
    have : (d.toNat : ℝ) ≠ 0 := by have := hd.pos; positivity
    field_simp

/-- `logBaseRatFloatExact? = none` for `q ≠ 1` and `b ≠ 1`: the logarithm is irrational.  When
`n, d > 1`, a rational `n'/d'` gives `q^d' = b^n'`, whose odd parts force `d^d' ∣ n^d'` (or the
reverse), impossible for coprime `n, d > 1`. -/
theorem irrational_of_logBaseRatFloatExact?_none (i : AzInt) (n d : AzNat) (j : AzInt)
    (s : AzNat) (hn : Odd n.toNat) (hd : Odd d.toNat) (hs : Odd s.toNat)
    (hcop : Nat.Coprime n.toNat d.toNat) (hb1 : (s.toNat : ℝ) * (2 : ℝ) ^ j.toInt ≠ 1)
    (hq1 : (n.toNat : ℝ) / d.toNat * (2 : ℝ) ^ i.toInt ≠ 1)
    (h : logBaseRatFloatExact? i n d j s = none) :
    Irrational (Real.log ((n.toNat : ℝ) / d.toNat * 2 ^ i.toInt)
      / Real.log ((s.toNat : ℝ) * 2 ^ j.toInt)) := by
  have hn0 : 0 < n.toNat := hn.pos
  have hd0 : 0 < d.toNat := hd.pos
  have hdr : (d.toNat : ℝ) ≠ 0 := by positivity
  unfold logBaseRatFloatExact? at h
  split_ifs at h with hd1 hn1
  · subst hd1
    rw [AzNat.toNat_one, Nat.cast_one, div_one] at hq1 ⊢
    exact irrational_of_logBaseFloatExact?_none i n j s hn hs hb1 hq1 h
  · subst hn1
    rw [Option.map_eq_none_iff] at h
    have hinv : (((1 : AzNat).toNat : ℝ) / d.toNat * (2 : ℝ) ^ i.toInt)
        = ((d.toNat : ℝ) * (2 : ℝ) ^ (-i).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      field_simp
    rw [hinv] at hq1 ⊢
    rw [Real.log_inv, neg_div]
    exact (irrational_of_logBaseFloatExact?_none (-i) d j s hd hs hb1
      (fun h1 => hq1 (by rw [h1, inv_one])) h).neg
  · -- `n, d > 1`
    have hn1' : n.toNat ≠ 1 := fun h1 => hn1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hd1' : d.toNat ≠ 1 := fun h1 => hd1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hs0 : 0 < s.toNat := hs.pos
    have hxpos : (0 : ℝ) < (n.toNat : ℝ) / d.toNat * 2 ^ i.toInt := by positivity
    have hbpos : (0 : ℝ) < (s.toNat : ℝ) * 2 ^ j.toInt := by positivity
    rintro ⟨r, hr⟩
    have key := pow_eq_zpow_of_log_div_log hxpos hbpos hb1 r hr
    have he : 1 ≤ r.den := r.den_pos
    have hmul : ∀ e : ℕ, ((n.toNat : ℝ) * 2 ^ i.toInt) ^ e
        = ((n.toNat : ℝ) / d.toNat * 2 ^ i.toInt) ^ e * (d.toNat : ℝ) ^ e := by
      intro e
      rw [← mul_pow]
      congr 1
      field_simp
    rcases le_or_gt 0 r.num with hnn | hnn
    · obtain ⟨N, hN⟩ : ∃ N : ℕ, r.num = N := ⟨r.num.toNat, by omega⟩
      rw [hN, zpow_natCast] at key
      have hG : ((n.toNat ^ r.den : ℕ) : ℝ) * 2 ^ (i.toInt * r.den)
          = ((s.toNat ^ N * d.toNat ^ r.den : ℕ) : ℝ) * 2 ^ (j.toInt * N) := by
        push_cast
        rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, hmul, key, mul_pow]
        ring
      obtain ⟨h1, -⟩ := odd_mul_two_zpow_inj hn.pow (hs.pow.mul hd.pow) hG
      have hdvd : d.toNat ^ r.den ∣ n.toNat ^ r.den := ⟨_, by rw [h1, mul_comm]⟩
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow _ _ hcop.symm) hdvd
      exact hd1' ((Nat.pow_eq_one.mp this).resolve_right (by omega))
    · obtain ⟨N, hN, -⟩ : ∃ N : ℕ, r.num = -(N : ℤ) ∧ 1 ≤ N := ⟨r.num.natAbs, by omega, by omega⟩
      rw [hN, zpow_neg, zpow_natCast] at key
      have hkey1 : ((n.toNat : ℝ) * 2 ^ i.toInt) ^ r.den * ((s.toNat : ℝ) * 2 ^ j.toInt) ^ N
          = (d.toNat : ℝ) ^ r.den := by
        rw [hmul, key, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ hbpos.ne'), one_mul]
      have hG : ((n.toNat ^ r.den * s.toNat ^ N : ℕ) : ℝ) * 2 ^ (i.toInt * r.den + j.toInt * N)
          = ((d.toNat ^ r.den : ℕ) : ℝ) * 2 ^ (0 : ℤ) := by
        push_cast
        rw [zpow_zero, mul_one, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_mul, zpow_mul,
          zpow_natCast, zpow_natCast, ← hkey1, mul_pow, mul_pow]
        ring
      obtain ⟨h1, -⟩ := odd_mul_two_zpow_inj (hn.pow.mul hs.pow) hd.pow hG
      have hdvd : n.toNat ^ r.den ∣ d.toNat ^ r.den := ⟨_, h1.symm⟩
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow _ _ hcop) hdvd
      exact hn1' ((Nat.pow_eq_one.mp this).resolve_right (by omega))

/-- The value of `logBaseRatFloatExact?` on a positive rational and a float base. -/
theorem logBaseRatFloat_exact_value (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0)
    (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1) (r : AzRat)
    (h : logBaseRatFloatExact? (ratDyadicExp q) (oddPart q.num) (oddPart q.den) (dyadicExp eb mb)
      (oddPart mb) = some r) :
    Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb) = (AzRat.toRat r : ℝ) := by
  rw [finiteVal_eq_oddPart eb hvb] at hb1 ⊢
  rw [toRat_eq_oddParts q hs h0]
  exact logBaseRatFloatExact?_some _ _ _ _ _ (oddPart_spec q.num h0).2.1
    (oddPart_spec q.den q.den_nz).2.1 (oddPart_spec mb (significand_ne_zero_of_valid hvb)).2.1
    hb1 r h

/-- Irrationality of `log_b q` when `logBaseRatFloatExact?` finds nothing. -/
theorem irrational_logBaseRatFloat_of_none (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (eb : AzInt) {qb : ℕ} {mb : AzNat} (hvb : FiniteValid qb mb)
    (hb1 : finiteVal true eb mb ≠ 1)
    (h : logBaseRatFloatExact? (ratDyadicExp q) (oddPart q.num) (oddPart q.den) (dyadicExp eb mb)
      (oddPart mb) = none) :
    Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log (finiteVal true eb mb)) := by
  have hcop : Nat.Coprime (oddPart q.num).toNat (oddPart q.den).toNat := by
    have h := (AzNat.coprime_iff _ _).mp q.reduced
    exact Nat.Coprime.coprime_dvd_left ⟨_, by rw [(oddPart_spec q.num h0).1, mul_comm]⟩
      (Nat.Coprime.coprime_dvd_right ⟨_, by rw [(oddPart_spec q.den q.den_nz).1, mul_comm]⟩ h)
  rw [finiteVal_eq_oddPart eb hvb] at hb1 ⊢
  rw [toRat_eq_oddParts q hs h0] at hq1 ⊢
  exact irrational_of_logBaseRatFloatExact?_none _ _ _ _ _ (oddPart_spec q.num h0).2.1
    (oddPart_spec q.den q.den_nz).2.1 (oddPart_spec mb (significand_ne_zero_of_valid hvb)).2.1
    hcop hb1 hq1 h

/-! ### Rational helpers -/

/-- `toRat q = 1` exactly when `q` is the fraction `1 / 1` with sign `true`. -/
theorem toRat_eq_one_iff (q : AzRat) (hs : q.sign = true) :
    AzRat.toRat q = 1 ↔ (q.num = 1 ∧ q.den = 1) := by
  constructor
  · intro h
    have hn := congrArg Rat.num h
    have hd := congrArg Rat.den h
    rw [toRat_num, hs] at hn
    rw [toRat_den] at hd
    simp only [↓reduceIte, Rat.num_one, Rat.den_one] at hn hd
    exact ⟨AzNat.toNat_injective (by rw [AzNat.toNat_one]; exact_mod_cast hn),
      AzNat.toNat_injective (by rw [AzNat.toNat_one]; exact hd)⟩
  · rintro ⟨hn, hd⟩
    have := AzRat.toRat_cast_eq q
    rw [hs, hn, hd, AzNat.toNat_one] at this
    simp only [↓reduceIte, Int.cast_one, Nat.cast_one, div_one] at this
    exact_mod_cast this

theorem toRat_ne_one_of_not_one (q : AzRat) (hs : q.sign = true) (h : ¬ (q.num = 1 ∧ q.den = 1)) :
    (AzRat.toRat q : ℝ) ≠ 1 := fun h1 =>
  h ((toRat_eq_one_iff q hs).mp (by exact_mod_cast h1))

theorem sign_eq_true_of_toRat_pos (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q) : q.sign = true := by
  by_contra hs
  rw [Bool.not_eq_true] at hs
  have := AzRat.toRat_cast_eq q
  rw [hs] at this
  simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast] at this
  have hqr : (0 : ℝ) < (AzRat.toRat q : ℝ) := by exact_mod_cast hq
  rw [this] at hqr
  have : -(q.num.toNat : ℝ) / q.den.toNat ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  linarith

theorem num_ne_zero_of_toRat_pos (q : AzRat) (hq : (0 : ℚ) < AzRat.toRat q) : q.num ≠ 0 :=
  fun h0 => by
    have h : (AzRat.toRat q : ℝ) = 0 := (AzRat.toRat_eq_zero_iff q).mpr h0
    have h' : AzRat.toRat q = 0 := by exact_mod_cast h
    rw [h'] at hq
    exact lt_irrefl _ hq

/-! ### A rational base -/

/-- The rational returned by `logBaseRatBaseExact?` is `ln x / ln b`. -/
theorem logBaseRatBaseExact?_some (i : AzInt) (o : AzNat) (j : AzInt) (n d : AzNat)
    (ho : Odd o.toNat) (hn : Odd n.toNat) (hd : Odd d.toNat)
    (hb1 : (n.toNat : ℝ) / d.toNat * (2 : ℝ) ^ j.toInt ≠ 1) (r : AzRat)
    (h : logBaseRatBaseExact? i o j n d = some r) :
    Real.log ((o.toNat : ℝ) * 2 ^ i.toInt) / Real.log ((n.toNat : ℝ) / d.toNat * 2 ^ j.toInt)
      = (AzRat.toRat r : ℝ) := by
  unfold logBaseRatBaseExact? at h
  split_ifs at h with hd1 hn1
  · subst hd1
    rw [AzNat.toNat_one, Nat.cast_one, div_one] at hb1 ⊢
    exact logBaseFloatExact?_some i o j n ho hn hb1 r h
  · subst hn1
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have hdr : (d.toNat : ℝ) ≠ 0 := by have := hd.pos; positivity
    have hinv : ((1 : AzNat).toNat : ℝ) / d.toNat * (2 : ℝ) ^ j.toInt
        = ((d.toNat : ℝ) * (2 : ℝ) ^ (-j).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      field_simp
    rw [hinv] at hb1 ⊢
    have hv := logBaseFloatExact?_some i o (-j) d ho hd (fun h1 => hb1 (by rw [h1, inv_one])) r' hr'
    rw [AzRat.toRat_neg, Rat.cast_neg, ← hv, Real.log_inv, div_neg]

/-- `logBaseRatBaseExact? = none` for `x ≠ 1` and `b ≠ 1`: the logarithm is irrational. -/
theorem irrational_of_logBaseRatBaseExact?_none (i : AzInt) (o : AzNat) (j : AzInt) (n d : AzNat)
    (ho : Odd o.toNat) (hn : Odd n.toNat) (hd : Odd d.toNat)
    (hcop : Nat.Coprime n.toNat d.toNat)
    (hb1 : (n.toNat : ℝ) / d.toNat * (2 : ℝ) ^ j.toInt ≠ 1)
    (hx1 : (o.toNat : ℝ) * (2 : ℝ) ^ i.toInt ≠ 1) (h : logBaseRatBaseExact? i o j n d = none) :
    Irrational (Real.log ((o.toNat : ℝ) * 2 ^ i.toInt)
      / Real.log ((n.toNat : ℝ) / d.toNat * 2 ^ j.toInt)) := by
  have ho0 : 0 < o.toNat := ho.pos
  have hn0 : 0 < n.toNat := hn.pos
  have hd0 : 0 < d.toNat := hd.pos
  have hdr : (d.toNat : ℝ) ≠ 0 := by positivity
  unfold logBaseRatBaseExact? at h
  split_ifs at h with hd1 hn1
  · subst hd1
    rw [AzNat.toNat_one, Nat.cast_one, div_one] at hb1 ⊢
    exact irrational_of_logBaseFloatExact?_none i o j n ho hn hb1 hx1 h
  · subst hn1
    rw [Option.map_eq_none_iff] at h
    have hinv : ((1 : AzNat).toNat : ℝ) / d.toNat * (2 : ℝ) ^ j.toInt
        = ((d.toNat : ℝ) * (2 : ℝ) ^ (-j).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      field_simp
    rw [hinv] at hb1 ⊢
    rw [Real.log_inv, div_neg]
    exact (irrational_of_logBaseFloatExact?_none i o (-j) d ho hd
      (fun h1 => hb1 (by rw [h1, inv_one])) hx1 h).neg
  · -- `n, d > 1`
    have hn1' : n.toNat ≠ 1 := fun h1 => hn1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hd1' : d.toNat ≠ 1 := fun h1 => hd1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hxpos : (0 : ℝ) < (o.toNat : ℝ) * 2 ^ i.toInt := by positivity
    have hbpos : (0 : ℝ) < (n.toNat : ℝ) / d.toNat * 2 ^ j.toInt := by positivity
    have hnot1 : ¬ (o.toNat = 1 ∧ i.toInt = 0) := fun ⟨h1', h2'⟩ => hx1 (by
      rw [h1', h2', Nat.cast_one, zpow_zero, mul_one])
    rintro ⟨r, hr⟩
    have key := pow_eq_zpow_of_log_div_log hxpos hbpos hb1 r hr
    have he : 1 ≤ r.den := r.den_pos
    have hmul : ∀ N : ℕ, ((n.toNat : ℝ) * 2 ^ j.toInt) ^ N
        = ((n.toNat : ℝ) / d.toNat * 2 ^ j.toInt) ^ N * (d.toNat : ℝ) ^ N := by
      intro N
      rw [← mul_pow]
      congr 1
      field_simp
    rcases le_or_gt 0 r.num with hnn | hnn
    · obtain ⟨N, hN⟩ : ∃ N : ℕ, r.num = N := ⟨r.num.toNat, by omega⟩
      rw [hN, zpow_natCast] at key
      have hG : ((o.toNat ^ r.den * d.toNat ^ N : ℕ) : ℝ) * 2 ^ (i.toInt * r.den)
          = ((n.toNat ^ N : ℕ) : ℝ) * 2 ^ (j.toInt * N) := by
        push_cast
        rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, hmul, ← key, mul_pow]
        ring
      obtain ⟨h1, h2⟩ := odd_mul_two_zpow_inj (ho.pow.mul hd.pow) hn.pow hG
      rcases Nat.eq_zero_or_pos N with hN0 | hN0
      · -- `a = 0`: `x = 1`
        rw [hN0, pow_zero, pow_zero, mul_one] at h1
        rw [hN0, Nat.cast_zero, mul_zero] at h2
        refine hnot1 ⟨(Nat.pow_eq_one.mp h1).resolve_right (by omega), ?_⟩
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · omega
      · have hdvd : d.toNat ^ N ∣ n.toNat ^ N := ⟨_, by rw [← h1, mul_comm]⟩
        have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow _ _ hcop.symm) hdvd
        exact hd1' ((Nat.pow_eq_one.mp this).resolve_right (by omega))
    · obtain ⟨N, hN, hN1⟩ : ∃ N : ℕ, r.num = -(N : ℤ) ∧ 1 ≤ N := ⟨r.num.natAbs, by omega, by omega⟩
      rw [hN, zpow_neg, zpow_natCast] at key
      have hkey1 : ((o.toNat : ℝ) * 2 ^ i.toInt) ^ r.den * ((n.toNat : ℝ) * 2 ^ j.toInt) ^ N
          = (d.toNat : ℝ) ^ N := by
        rw [hmul, ← mul_assoc, key, inv_mul_cancel₀ (pow_ne_zero _ hbpos.ne'), one_mul]
      have hG : ((o.toNat ^ r.den * n.toNat ^ N : ℕ) : ℝ) * 2 ^ (i.toInt * r.den + j.toInt * N)
          = ((d.toNat ^ N : ℕ) : ℝ) * 2 ^ (0 : ℤ) := by
        push_cast
        rw [zpow_zero, mul_one, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_mul, zpow_mul,
          zpow_natCast, zpow_natCast, ← hkey1, mul_pow, mul_pow]
        ring
      obtain ⟨h1, -⟩ := odd_mul_two_zpow_inj (ho.pow.mul hn.pow) hd.pow hG
      have hdvd : n.toNat ^ N ∣ d.toNat ^ N := ⟨_, by rw [← h1, mul_comm]⟩
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow _ _ hcop) hdvd
      exact hn1' ((Nat.pow_eq_one.mp this).resolve_right (by omega))

/-- The value of `logBaseRatBaseExact?` on a positive float and a positive rational base. -/
theorem logBaseRatBase_exact_value (ex : AzInt) {qx : ℕ} {mx : AzNat} (hvx : FiniteValid qx mx)
    (b : AzRat) (hs : b.sign = true) (h0 : b.num ≠ 0) (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (r : AzRat)
    (h : logBaseRatBaseExact? (dyadicExp ex mx) (oddPart mx) (ratDyadicExp b) (oddPart b.num)
      (oddPart b.den) = some r) :
    Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ) = (AzRat.toRat r : ℝ) := by
  rw [toRat_eq_oddParts b hs h0] at hb1 ⊢
  rw [finiteVal_eq_oddPart ex hvx]
  exact logBaseRatBaseExact?_some _ _ _ _ _ (oddPart_spec mx (significand_ne_zero_of_valid hvx)).2.1
    (oddPart_spec b.num h0).2.1 (oddPart_spec b.den b.den_nz).2.1 hb1 r h

/-- Irrationality of `log_b x` when `logBaseRatBaseExact?` finds nothing. -/
theorem irrational_logBaseRatBase_of_none (ex : AzInt) {qx : ℕ} {mx : AzNat}
    (hvx : FiniteValid qx mx) (hx1 : finiteVal true ex mx ≠ 1) (b : AzRat) (hs : b.sign = true)
    (h0 : b.num ≠ 0) (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (h : logBaseRatBaseExact? (dyadicExp ex mx) (oddPart mx) (ratDyadicExp b) (oddPart b.num)
      (oddPart b.den) = none) :
    Irrational (Real.log (finiteVal true ex mx) / Real.log (AzRat.toRat b : ℝ)) := by
  have hcop : Nat.Coprime (oddPart b.num).toNat (oddPart b.den).toNat := by
    have h := (AzNat.coprime_iff _ _).mp b.reduced
    exact Nat.Coprime.coprime_dvd_left ⟨_, by rw [(oddPart_spec b.num h0).1, mul_comm]⟩
      (Nat.Coprime.coprime_dvd_right ⟨_, by rw [(oddPart_spec b.den b.den_nz).1, mul_comm]⟩ h)
  rw [toRat_eq_oddParts b hs h0] at hb1 ⊢
  rw [finiteVal_eq_oddPart ex hvx] at hx1 ⊢
  exact irrational_of_logBaseRatBaseExact?_none _ _ _ _ _
    (oddPart_spec mx (significand_ne_zero_of_valid hvx)).2.1 (oddPart_spec b.num h0).2.1
    (oddPart_spec b.den b.den_nz).2.1 hcop hb1 hx1 h

/-- For a positive rational, `1 < q` exactly when the denominator is below the numerator. -/
theorem one_lt_toRat_iff (q : AzRat) (hs : q.sign = true) :
    1 < (AzRat.toRat q : ℝ) ↔ q.den < q.num := by
  rw [AzRat.toRat_cast_eq, hs, AzNat.lt_iff_toNat_lt]
  simp only [↓reduceIte, Int.cast_natCast]
  have hd : (0 : ℝ) < q.den.toNat := by exact_mod_cast AzRat.den_toNat_pos q
  rw [lt_div_iff₀ hd, one_mul]
  exact Nat.cast_lt

/-! ### `1 + x` with a rational base -/

/-- The value of `logBaseRatBaseExact?` on `1 + x` and a positive rational base. -/
theorem logBaseRatBaseP1_exact_value (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (b : AzRat) (hs : b.sign = true)
    (h0 : b.num ≠ 0) (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (r : AzRat)
    (h : logBaseRatBaseExact? (onePlusDyadic s (dyadicExp e m) (oddPart m)).2
      (onePlusDyadic s (dyadicExp e m) (oddPart m)).1 (ratDyadicExp b) (oddPart b.num)
      (oddPart b.den) = some r) :
    Real.log (1 + finiteVal s e m) / Real.log (AzRat.toRat b : ℝ) = (AzRat.toRat r : ℝ) := by
  obtain ⟨hodd, hval⟩ := onePlusDyadic_spec s e hv hgt
  rw [toRat_eq_oddParts b hs h0] at hb1 ⊢
  rw [hval]
  exact logBaseRatBaseExact?_some _ _ _ _ _ hodd (oddPart_spec b.num h0).2.1
    (oddPart_spec b.den b.den_nz).2.1 hb1 r h

/-- Irrationality of `log_b (1 + x)` when `logBaseRatBaseExact?` finds nothing. -/
theorem irrational_logBaseRatBaseP1_of_none (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (hgt : -1 < finiteVal s e m) (b : AzRat) (hs : b.sign = true)
    (h0 : b.num ≠ 0) (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (h : logBaseRatBaseExact? (onePlusDyadic s (dyadicExp e m) (oddPart m)).2
      (onePlusDyadic s (dyadicExp e m) (oddPart m)).1 (ratDyadicExp b) (oddPart b.num)
      (oddPart b.den) = none) :
    Irrational (Real.log (1 + finiteVal s e m) / Real.log (AzRat.toRat b : ℝ)) := by
  obtain ⟨hodd, hval⟩ := onePlusDyadic_spec s e hv hgt
  have hx1 : 1 + finiteVal s e m ≠ 1 := fun h1 => finiteVal_ne_zero s e hv (by linarith)
  have hcop : Nat.Coprime (oddPart b.num).toNat (oddPart b.den).toNat := by
    have h := (AzNat.coprime_iff _ _).mp b.reduced
    exact Nat.Coprime.coprime_dvd_left ⟨_, by rw [(oddPart_spec b.num h0).1, mul_comm]⟩
      (Nat.Coprime.coprime_dvd_right ⟨_, by rw [(oddPart_spec b.den b.den_nz).1, mul_comm]⟩ h)
  rw [toRat_eq_oddParts b hs h0] at hb1 ⊢
  rw [hval] at hx1 ⊢
  exact irrational_of_logBaseRatBaseExact?_none _ _ _ _ _ hodd (oddPart_spec b.num h0).2.1
    (oddPart_spec b.den b.den_nz).2.1 hcop hb1 hx1 h

/-! ### A rational argument and a rational base -/

theorem logOddExact?_some (n₁ n₂ : AzNat) (h₁ : Odd n₁.toNat) (h₂ : Odd n₂.toNat)
    (hn₂ : n₂.toNat ≠ 1) (r : AzRat) (h : logOddExact? n₁ n₂ = some r) :
    Real.log (n₁.toNat : ℝ) / Real.log (n₂.toNat : ℝ) = (AzRat.toRat r : ℝ) := by
  have := logBaseFloatExact?_some 0 n₁ 0 n₂ h₁ h₂
    (by rw [AzInt.toInt_zero, zpow_zero, mul_one]; exact_mod_cast hn₂) r h
  rwa [AzInt.toInt_zero, zpow_zero, mul_one, mul_one] at this

theorem irrational_of_logOddExact?_none (n₁ n₂ : AzNat) (h₁ : Odd n₁.toNat) (h₂ : Odd n₂.toNat)
    (hn₁ : n₁.toNat ≠ 1) (hn₂ : n₂.toNat ≠ 1) (h : logOddExact? n₁ n₂ = none) :
    Irrational (Real.log (n₁.toNat : ℝ) / Real.log (n₂.toNat : ℝ)) := by
  have := irrational_of_logBaseFloatExact?_none 0 n₁ 0 n₂ h₁ h₂
    (by rw [AzInt.toInt_zero, zpow_zero, mul_one]; exact_mod_cast hn₂)
    (by rw [AzInt.toInt_zero, zpow_zero, mul_one]; exact_mod_cast hn₁) h
  rwa [AzInt.toInt_zero, zpow_zero, mul_one, mul_one] at this

/-- A rational `log_{n₂} n₁` is found by `logOddExact?`. -/
theorem logOddExact?_eq_some_of_rat (n₁ n₂ : AzNat) (h₁ : Odd n₁.toNat) (h₂ : Odd n₂.toNat)
    (hn₁ : n₁.toNat ≠ 1) (hn₂ : n₂.toNat ≠ 1) (v : ℚ)
    (hv : Real.log (n₁.toNat : ℝ) / Real.log (n₂.toNat : ℝ) = v) :
    ∃ r, logOddExact? n₁ n₂ = some r ∧ (AzRat.toRat r : ℝ) = v := by
  rcases hr : logOddExact? n₁ n₂ with _ | r
  · exact absurd ⟨v, hv.symm⟩ (irrational_of_logOddExact?_none n₁ n₂ h₁ h₂ hn₁ hn₂ hr)
  · exact ⟨r, rfl, by rw [← logOddExact?_some n₁ n₂ h₁ h₂ hn₂ r hr, hv]⟩

theorem logOddPairExact?_some (n₁ d₁ n₂ d₂ : AzNat) (v : AzRat)
    (h : logOddPairExact? n₁ d₁ n₂ d₂ = some v) :
    logOddExact? n₁ n₂ = some v ∧ logOddExact? d₁ d₂ = some v := by
  unfold logOddPairExact? at h
  rcases h₁ : logOddExact? n₁ n₂ with _ | v₁ <;> rcases h₂ : logOddExact? d₁ d₂ with _ | v₂ <;>
    simp only [h₁, h₂] at h
  · cases h
  · cases h
  · cases h
  · split_ifs at h with heq
    rw [Option.some.injEq] at h
    subst h
    exact ⟨rfl, by rw [heq]⟩

theorem logOddPairExact?_eq_some (n₁ d₁ n₂ d₂ : AzNat) (v : AzRat)
    (h₁ : logOddExact? n₁ n₂ = some v) (h₂ : logOddExact? d₁ d₂ = some v) :
    logOddPairExact? n₁ d₁ n₂ d₂ = some v := by
  unfold logOddPairExact?
  rw [h₁, h₂]
  simp

/-- The 2-adic condition as a statement about values. -/
theorem dyadicOK_eq_true_iff (i j : AzInt) (v : AzRat) :
    dyadicOK i j v = true ↔ (j = 0 ∧ i = 0) ∨ (j ≠ 0 ∧ v = AzRat.ofAzInts i j) := by
  unfold dyadicOK
  split_ifs with hj
  · simp only [decide_eq_true_iff]
    constructor
    · intro h; exact Or.inl ⟨hj, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd hj h
  · simp only [decide_eq_true_iff]
    constructor
    · intro h; exact Or.inr ⟨hj, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hj
      · exact h

/-- `log_b q` from the pair values and the 2-adic condition. -/
theorem log_div_log_of_pair (n₁ d₁ n₂ d₂ : ℕ) (i j : ℤ) (v : ℝ)
    (hn₁ : 0 < n₁) (hd₁ : 0 < d₁) (hn₂ : 0 < n₂) (hd₂ : 0 < d₂)
    (hlogb : Real.log ((n₂ : ℝ) / d₂ * 2 ^ j) ≠ 0)
    (hodd : Real.log (n₁ : ℝ) - Real.log (d₁ : ℝ) = v * (Real.log (n₂ : ℝ) - Real.log (d₂ : ℝ)))
    (hdy : (j = 0 ∧ i = 0) ∨ (j ≠ 0 ∧ v = i / j)) :
    Real.log ((n₁ : ℝ) / d₁ * 2 ^ i) / Real.log ((n₂ : ℝ) / d₂ * 2 ^ j) = v := by
  have hn₁' : (n₁ : ℝ) ≠ 0 := by positivity
  have hd₁' : (d₁ : ℝ) ≠ 0 := by positivity
  have hn₂' : (n₂ : ℝ) ≠ 0 := by positivity
  have hd₂' : (d₂ : ℝ) ≠ 0 := by positivity
  rw [div_eq_iff hlogb, Real.log_mul (div_ne_zero hn₁' hd₁') (zpow_ne_zero _ two_ne_zero),
    Real.log_mul (div_ne_zero hn₂' hd₂') (zpow_ne_zero _ two_ne_zero), Real.log_div hn₁' hd₁',
    Real.log_div hn₂' hd₂', Real.log_zpow, Real.log_zpow]
  rcases hdy with ⟨hj, hi⟩ | ⟨hj, hv⟩
  · subst hj; subst hi
    push_cast
    linear_combination hodd
  · have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    have hvj : v * j = i := by rw [hv]; field_simp
    linear_combination hodd - Real.log 2 * hvj

/-- The 2-adic condition in terms of values. -/
theorem dyadic_values (i j : AzInt) (v : AzRat) (h : dyadicOK i j v = true) :
    (j.toInt = 0 ∧ i.toInt = 0) ∨ (j.toInt ≠ 0 ∧ (AzRat.toRat v : ℝ) = i.toInt / j.toInt) := by
  rcases (dyadicOK_eq_true_iff i j v).mp h with ⟨hj, hi⟩ | ⟨hj, hv⟩
  · subst hj; subst hi
    exact Or.inl ⟨AzInt.toInt_zero, AzInt.toInt_zero⟩
  · refine Or.inr ⟨toInt_ne_zero_of_ne_zero' hj, ?_⟩
    rw [hv, AzRat.toRat_ofAzInts]
    push_cast
    rfl

/-- Separating `q^e = b^a` for `q = (n₁/d₁) · 2^i`, `b = (n₂/d₂) · 2^j` with odd coprime pairs:
the odd parts match pairwise (crosswise for `a < 0`) and the 2-exponents match. -/
theorem pow_eq_zpow_sep_rat {n₁ d₁ n₂ d₂ : ℕ} (h₁ : Odd n₁) (h₂ : Odd d₁) (h₃ : Odd n₂)
    (h₄ : Odd d₂) (hc₁ : Nat.Coprime n₁ d₁) (hc₂ : Nat.Coprime n₂ d₂) {i j : ℤ} {e : ℕ} {a : ℤ}
    (key : ((n₁ : ℝ) / d₁ * 2 ^ i) ^ e = ((n₂ : ℝ) / d₂ * 2 ^ j) ^ a) :
    (0 ≤ a → n₁ ^ e = n₂ ^ a.toNat ∧ d₁ ^ e = d₂ ^ a.toNat) ∧
      (a < 0 → n₁ ^ e = d₂ ^ a.natAbs ∧ d₁ ^ e = n₂ ^ a.natAbs) ∧ i * e = j * a := by
  have hn₁ : 0 < n₁ := h₁.pos
  have hd₁ : 0 < d₁ := h₂.pos
  have hn₂ : 0 < n₂ := h₃.pos
  have hd₂ : 0 < d₂ := h₄.pos
  have hd₁' : (d₁ : ℝ) ≠ 0 := by positivity
  have hd₂' : (d₂ : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_pow] at key
  rcases le_or_gt 0 a with hn | hn
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, a = N := ⟨a.toNat, by omega⟩
    rw [hN, zpow_natCast, div_pow,
      div_eq_div_iff (pow_ne_zero _ hd₁') (pow_ne_zero _ hd₂')] at key
    have hG : ((n₁ ^ e * d₂ ^ N : ℕ) : ℝ) * 2 ^ (i * e)
        = ((n₂ ^ N * d₁ ^ e : ℕ) : ℝ) * 2 ^ (j * N) := by
      rw [mul_pow, mul_pow] at key
      push_cast
      rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      linear_combination key
    obtain ⟨hodd, h2⟩ := odd_mul_two_zpow_inj (h₁.pow.mul h₄.pow) (h₃.pow.mul h₂.pow) hG
    have hdd : d₁ ^ e = d₂ ^ N := by
      apply Nat.dvd_antisymm
      · exact (Nat.Coprime.pow e e hc₁.symm).dvd_of_dvd_mul_left
          ⟨n₂ ^ N, by rw [hodd, mul_comm]⟩
      · exact (Nat.Coprime.pow N N hc₂.symm).dvd_of_dvd_mul_left
          ⟨n₁ ^ e, by rw [← hodd, mul_comm]⟩
    have hnn : n₁ ^ e = n₂ ^ N := by
      have hpos : 0 < d₂ ^ N := by positivity
      rw [hdd] at hodd
      exact Nat.eq_of_mul_eq_mul_right hpos hodd
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd h (by omega), by rw [hN]; exact h2⟩
    · rw [hN, Int.toNat_natCast]; exact hnn
    · rw [hN, Int.toNat_natCast]; exact hdd
  · obtain ⟨N, hN, hN1⟩ : ∃ N : ℕ, a = -(N : ℤ) ∧ 1 ≤ N := ⟨a.natAbs, by omega, by omega⟩
    have hb0 : ((n₂ : ℝ) * 2 ^ j) ^ N ≠ 0 := pow_ne_zero _ (by positivity)
    rw [hN, zpow_neg, zpow_natCast, div_pow, inv_div,
      div_eq_div_iff (pow_ne_zero _ hd₁') hb0] at key
    have hG : ((n₁ ^ e * n₂ ^ N : ℕ) : ℝ) * 2 ^ (i * e + j * N)
        = ((d₂ ^ N * d₁ ^ e : ℕ) : ℝ) * 2 ^ (0 : ℤ) := by
      rw [mul_pow, mul_pow] at key
      push_cast
      rw [zpow_zero, mul_one, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), zpow_mul, zpow_mul,
        zpow_natCast, zpow_natCast]
      linear_combination key
    obtain ⟨hodd, h2⟩ := odd_mul_two_zpow_inj (h₁.pow.mul h₃.pow) (h₄.pow.mul h₂.pow) hG
    have hnd : n₁ ^ e = d₂ ^ N := by
      apply Nat.dvd_antisymm
      · exact (Nat.Coprime.pow e e hc₁).dvd_of_dvd_mul_right ⟨n₂ ^ N, by rw [← hodd]⟩
      · exact (Nat.Coprime.pow N N hc₂.symm).dvd_of_dvd_mul_right ⟨d₁ ^ e, by rw [hodd]⟩
    have hdn : d₁ ^ e = n₂ ^ N := by
      have hpos : 0 < d₂ ^ N := by positivity
      rw [hnd] at hodd
      exact (Nat.eq_of_mul_eq_mul_left hpos hodd).symm
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩, by rw [hN]; linarith⟩
    · rw [hN, Int.natAbs_neg, Int.natAbs_natCast]; exact hnd
    · rw [hN, Int.natAbs_neg, Int.natAbs_natCast]; exact hdn

/-- The rational returned by `logBaseRatRatExact?` is `ln q / ln b`. -/
theorem logBaseRatRatExact?_some (i : AzInt) (n₁ d₁ : AzNat) (j : AzInt) (n₂ d₂ : AzNat)
    (h₁ : Odd n₁.toNat) (h₂ : Odd d₁.toNat) (h₃ : Odd n₂.toNat) (h₄ : Odd d₂.toNat)
    (hb1 : (n₂.toNat : ℝ) / d₂.toNat * (2 : ℝ) ^ j.toInt ≠ 1) (r : AzRat)
    (h : logBaseRatRatExact? i n₁ d₁ j n₂ d₂ = some r) :
    Real.log ((n₁.toNat : ℝ) / d₁.toNat * 2 ^ i.toInt)
      / Real.log ((n₂.toNat : ℝ) / d₂.toNat * 2 ^ j.toInt) = (AzRat.toRat r : ℝ) := by
  have hn₁ := h₁.pos
  have hd₁ := h₂.pos
  have hn₂ := h₃.pos
  have hd₂ := h₄.pos
  unfold logBaseRatRatExact? at h
  split_ifs at h with hd₂1 hn₂1 hd₁1 hn₁1
  · subst hd₂1
    rw [AzNat.toNat_one, Nat.cast_one, div_one] at hb1 ⊢
    exact logBaseRatFloatExact?_some i n₁ d₁ j n₂ h₁ h₂ h₃ hb1 r h
  · subst hn₂1
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have hinv : ((1 : AzNat).toNat : ℝ) / d₂.toNat * (2 : ℝ) ^ j.toInt
        = ((d₂.toNat : ℝ) * (2 : ℝ) ^ (-j).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      have : (d₂.toNat : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hinv] at hb1 ⊢
    have hv := logBaseRatFloatExact?_some i n₁ d₁ (-j) d₂ h₁ h₂ h₄
      (fun h1 => hb1 (by rw [h1, inv_one])) r' hr'
    rw [AzRat.toRat_neg, Rat.cast_neg, ← hv, Real.log_inv, div_neg]
  · subst hd₁1
    rw [AzNat.toNat_one, Nat.cast_one, div_one]
    exact logBaseRatBaseExact?_some i n₁ j n₂ d₂ h₁ h₃ h₄ hb1 r h
  · subst hn₁1
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have hinv : ((1 : AzNat).toNat : ℝ) / d₁.toNat * (2 : ℝ) ^ i.toInt
        = ((d₁.toNat : ℝ) * (2 : ℝ) ^ (-i).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      have : (d₁.toNat : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hinv]
    have hv := logBaseRatBaseExact?_some (-i) d₁ j n₂ d₂ h₂ h₃ h₄ hb1 r' hr'
    rw [AzRat.toRat_neg, Rat.cast_neg, ← hv, Real.log_inv, neg_div]
  · -- all odd parts above `1`
    have hn₂1' : n₂.toNat ≠ 1 := fun h1 => hn₂1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hd₂1' : d₂.toNat ≠ 1 := fun h1 => hd₂1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hlogb : Real.log ((n₂.toNat : ℝ) / d₂.toNat * 2 ^ j.toInt) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) hb1
    have hlogn₂ : Real.log (n₂.toNat : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by exact_mod_cast hn₂1')
    have hlogd₂ : Real.log (d₂.toNat : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by exact_mod_cast hd₂1')
    have hneg : ∀ r, logBaseRatRatNeg? i n₁ d₁ j n₂ d₂ = some r →
        Real.log ((n₁.toNat : ℝ) / d₁.toNat * 2 ^ i.toInt)
          / Real.log ((n₂.toNat : ℝ) / d₂.toNat * 2 ^ j.toInt) = (AzRat.toRat r : ℝ) := by
      intro r h
      unfold logBaseRatRatNeg? at h
      rcases hP : logOddPairExact? n₁ d₁ d₂ n₂ with _ | u
      · rw [hP] at h; simp only [] at h; cases h
      · rw [hP] at h
        simp only [] at h
        split_ifs at h with hdy
        rw [Option.some.injEq] at h
        subst h
        obtain ⟨hu₁, hu₂⟩ := logOddPairExact?_some n₁ d₁ d₂ n₂ u hP
        have e₁ := logOddExact?_some n₁ d₂ h₁ h₄ hd₂1' u hu₁
        have e₂ := logOddExact?_some d₁ n₂ h₂ h₃ hn₂1' u hu₂
        rw [div_eq_iff hlogd₂] at e₁
        rw [div_eq_iff hlogn₂] at e₂
        rw [AzRat.toRat_neg, Rat.cast_neg]
        apply log_div_log_of_pair _ _ _ _ _ _ _ hn₁ hd₁ hn₂ hd₂ hlogb
        · rw [e₁, e₂]; ring
        · have := dyadic_values i j (-u) hdy
          rwa [AzRat.toRat_neg, Rat.cast_neg] at this
    rcases hP : logOddPairExact? n₁ d₁ n₂ d₂ with _ | v
    · rw [hP] at h
      simp only [] at h
      exact hneg r h
    · rw [hP] at h
      simp only [] at h
      split_ifs at h with hdy
      · rw [Option.some.injEq] at h
        subst h
        obtain ⟨hv₁, hv₂⟩ := logOddPairExact?_some n₁ d₁ n₂ d₂ v hP
        have e₁ := logOddExact?_some n₁ n₂ h₁ h₃ hn₂1' v hv₁
        have e₂ := logOddExact?_some d₁ d₂ h₂ h₄ hd₂1' v hv₂
        rw [div_eq_iff hlogn₂] at e₁
        rw [div_eq_iff hlogd₂] at e₂
        apply log_div_log_of_pair _ _ _ _ _ _ _ hn₁ hd₁ hn₂ hd₂ hlogb
        · rw [e₁, e₂]; ring
        · exact dyadic_values i j v hdy
      · exact hneg r h

/-- `logBaseRatRatExact? = none` for `q ≠ 1` and `b ≠ 1`: the logarithm is irrational. -/
theorem irrational_of_logBaseRatRatExact?_none (i : AzInt) (n₁ d₁ : AzNat) (j : AzInt)
    (n₂ d₂ : AzNat) (h₁ : Odd n₁.toNat) (h₂ : Odd d₁.toNat) (h₃ : Odd n₂.toNat)
    (h₄ : Odd d₂.toNat) (hc₁ : Nat.Coprime n₁.toNat d₁.toNat)
    (hc₂ : Nat.Coprime n₂.toNat d₂.toNat)
    (hb1 : (n₂.toNat : ℝ) / d₂.toNat * (2 : ℝ) ^ j.toInt ≠ 1)
    (hq1 : (n₁.toNat : ℝ) / d₁.toNat * (2 : ℝ) ^ i.toInt ≠ 1)
    (h : logBaseRatRatExact? i n₁ d₁ j n₂ d₂ = none) :
    Irrational (Real.log ((n₁.toNat : ℝ) / d₁.toNat * 2 ^ i.toInt)
      / Real.log ((n₂.toNat : ℝ) / d₂.toNat * 2 ^ j.toInt)) := by
  have hn₁ := h₁.pos
  have hd₁ := h₂.pos
  have hn₂ := h₃.pos
  have hd₂ := h₄.pos
  unfold logBaseRatRatExact? at h
  split_ifs at h with hd₂1 hn₂1 hd₁1 hn₁1
  · subst hd₂1
    rw [AzNat.toNat_one, Nat.cast_one, div_one] at hb1 ⊢
    exact irrational_of_logBaseRatFloatExact?_none i n₁ d₁ j n₂ h₁ h₂ h₃ hc₁ hb1 hq1 h
  · subst hn₂1
    rw [Option.map_eq_none_iff] at h
    have hinv : ((1 : AzNat).toNat : ℝ) / d₂.toNat * (2 : ℝ) ^ j.toInt
        = ((d₂.toNat : ℝ) * (2 : ℝ) ^ (-j).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      have : (d₂.toNat : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hinv] at hb1 ⊢
    rw [Real.log_inv, div_neg]
    exact (irrational_of_logBaseRatFloatExact?_none i n₁ d₁ (-j) d₂ h₁ h₂ h₄ hc₁
      (fun h1 => hb1 (by rw [h1, inv_one])) hq1 h).neg
  · subst hd₁1
    rw [AzNat.toNat_one, Nat.cast_one, div_one] at hq1 ⊢
    exact irrational_of_logBaseRatBaseExact?_none i n₁ j n₂ d₂ h₁ h₃ h₄ hc₂ hb1 hq1 h
  · subst hn₁1
    rw [Option.map_eq_none_iff] at h
    have hinv : ((1 : AzNat).toNat : ℝ) / d₁.toNat * (2 : ℝ) ^ i.toInt
        = ((d₁.toNat : ℝ) * (2 : ℝ) ^ (-i).toInt)⁻¹ := by
      rw [AzNat.toNat_one, Nat.cast_one, AzInt.toInt_neg, zpow_neg]
      have : (d₁.toNat : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hinv] at hq1 ⊢
    rw [Real.log_inv, neg_div]
    exact (irrational_of_logBaseRatBaseExact?_none (-i) d₁ j n₂ d₂ h₂ h₃ h₄ hc₂ hb1
      (fun h1 => hq1 (by rw [h1, inv_one])) h).neg
  · -- all odd parts above `1`
    have hn₁1' : n₁.toNat ≠ 1 := fun h1 => hn₁1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hd₁1' : d₁.toNat ≠ 1 := fun h1 => hd₁1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hn₂1' : n₂.toNat ≠ 1 := fun h1 => hn₂1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hd₂1' : d₂.toNat ≠ 1 := fun h1 => hd₂1 (AzNat.toNat_injective (by rw [h1]; rfl))
    have hxpos : (0 : ℝ) < (n₁.toNat : ℝ) / d₁.toNat * 2 ^ i.toInt := by positivity
    have hbpos : (0 : ℝ) < (n₂.toNat : ℝ) / d₂.toNat * 2 ^ j.toInt := by positivity
    rintro ⟨r, hr⟩
    have key := pow_eq_zpow_of_log_div_log hxpos hbpos hb1 r hr
    have he : 1 ≤ r.den := r.den_pos
    obtain ⟨hpos', hneg', h2⟩ := pow_eq_zpow_sep_rat h₁ h₂ h₃ h₄ hc₁ hc₂ key
    -- a pair equation gives a rational logarithm
    have hdiv : ∀ {x y N : ℕ}, 0 < x → 0 < y → y ≠ 1 → x ^ r.den = y ^ N →
        Real.log (x : ℝ) / Real.log (y : ℝ) = (((N : ℚ) / r.den : ℚ) : ℝ) := by
      intro x y N hx hy hy1 hxy
      have hlogy : Real.log (y : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by exact_mod_cast hy1)
      have hden : (r.den : ℝ) ≠ 0 := by positivity
      have hlog : (r.den : ℝ) * Real.log (x : ℝ) = (N : ℝ) * Real.log (y : ℝ) := by
        have := congrArg (fun t : ℕ => Real.log (t : ℝ)) hxy
        simp only [Nat.cast_pow, Real.log_pow] at this
        exact this
      rw [div_eq_iff hlogy]
      push_cast
      field_simp
      linear_combination hlog
    -- `i = 0` when `j = 0`
    have hi0 : j = 0 → i = 0 := by
      intro hj
      subst hj
      rw [AzInt.toInt_zero, zero_mul] at h2
      have : i.toInt = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · omega
      rw [← AzInt.ofInt_toInt i, this, AzInt.ofInt_zero]
    rcases le_or_gt 0 r.num with hn | hn
    · obtain ⟨hnn, hdd⟩ := hpos' hn
      rcases Nat.eq_zero_or_pos r.num.toNat with hN0 | hN0
      · rw [hN0, pow_zero] at hnn
        exact hn₁1' ((Nat.pow_eq_one.mp hnn).resolve_right (by omega))
      obtain ⟨v₁, hv₁, hv₁'⟩ :=
        logOddExact?_eq_some_of_rat n₁ n₂ h₁ h₃ hn₁1' hn₂1' _ (hdiv hn₁ hn₂ hn₂1' hnn)
      obtain ⟨v₂, hv₂, hv₂'⟩ :=
        logOddExact?_eq_some_of_rat d₁ d₂ h₂ h₄ hd₁1' hd₂1' _ (hdiv hd₁ hd₂ hd₂1' hdd)
      have hv : v₁ = v₂ := AzRat.toRat_injective (by exact_mod_cast hv₁'.trans hv₂'.symm)
      subst hv
      have hP := logOddPairExact?_eq_some n₁ d₁ n₂ d₂ v₁ hv₁ hv₂
      have hdy : dyadicOK i j v₁ = true := by
        rw [dyadicOK_eq_true_iff]
        by_cases hj : j = 0
        · exact Or.inl ⟨hj, hi0 hj⟩
        · refine Or.inr ⟨hj, ?_⟩
          apply AzRat.toRat_injective
          have hj' : (j.toInt : ℚ) ≠ 0 := by exact_mod_cast toInt_ne_zero_of_ne_zero' hj
          have hvq : AzRat.toRat v₁ = (r.num.toNat : ℚ) / r.den := by exact_mod_cast hv₁'
          rw [hvq, AzRat.toRat_ofAzInts, div_eq_div_iff (by positivity) hj']
          have hnum : (r.num : ℚ) = r.num.toNat := by exact_mod_cast (Int.toNat_of_nonneg hn).symm
          have h2q : (i.toInt : ℚ) * r.den = j.toInt * r.num := by exact_mod_cast h2
          rw [hnum] at h2q
          linarith
      rw [hP] at h
      simp only [] at h
      rw [ite_eq_left hdy] at h
      cases h
    · obtain ⟨hnd, hdn⟩ := hneg' hn
      obtain ⟨u₁, hu₁, hu₁'⟩ :=
        logOddExact?_eq_some_of_rat n₁ d₂ h₁ h₄ hn₁1' hd₂1' _ (hdiv hn₁ hd₂ hd₂1' hnd)
      obtain ⟨u₂, hu₂, hu₂'⟩ :=
        logOddExact?_eq_some_of_rat d₁ n₂ h₂ h₃ hd₁1' hn₂1' _ (hdiv hd₁ hn₂ hn₂1' hdn)
      have hu : u₁ = u₂ := AzRat.toRat_injective (by exact_mod_cast hu₁'.trans hu₂'.symm)
      subst hu
      have hP' := logOddPairExact?_eq_some n₁ d₁ d₂ n₂ u₁ hu₁ hu₂
      have hdy : dyadicOK i j (-u₁) = true := by
        rw [dyadicOK_eq_true_iff]
        by_cases hj : j = 0
        · exact Or.inl ⟨hj, hi0 hj⟩
        · refine Or.inr ⟨hj, ?_⟩
          apply AzRat.toRat_injective
          have hj' : (j.toInt : ℚ) ≠ 0 := by exact_mod_cast toInt_ne_zero_of_ne_zero' hj
          have huq : AzRat.toRat u₁ = (r.num.natAbs : ℚ) / r.den := by exact_mod_cast hu₁'
          rw [AzRat.toRat_neg, huq, AzRat.toRat_ofAzInts, ← neg_div,
            div_eq_div_iff (by positivity) hj']
          have hnum : (r.num : ℤ) = -(r.num.natAbs : ℤ) := by omega
          have hnumq : (r.num : ℚ) = -(r.num.natAbs : ℚ) := by exact_mod_cast hnum
          have h2q : (i.toInt : ℚ) * r.den = j.toInt * r.num := by exact_mod_cast h2
          rw [hnumq] at h2q
          linarith
      have hres : logBaseRatRatNeg? i n₁ d₁ j n₂ d₂ = some (-u₁) := by
        unfold logBaseRatRatNeg?
        rw [hP']
        simp only []
        rw [ite_eq_left hdy]
      rcases hP : logOddPairExact? n₁ d₁ n₂ d₂ with _ | v
      · rw [hP] at h
        simp only [] at h
        rw [hres] at h
        cases h
      · rw [hP] at h
        simp only [] at h
        split_ifs at h with hdyv
        rw [hres] at h
        cases h

/-- The odd parts of a reduced fraction are coprime. -/
theorem coprime_oddParts (q : AzRat) (h0 : q.num ≠ 0) :
    Nat.Coprime (oddPart q.num).toNat (oddPart q.den).toNat := by
  have h := (AzNat.coprime_iff _ _).mp q.reduced
  exact Nat.Coprime.coprime_dvd_left ⟨_, by rw [(oddPart_spec q.num h0).1, mul_comm]⟩
    (Nat.Coprime.coprime_dvd_right ⟨_, by rw [(oddPart_spec q.den q.den_nz).1, mul_comm]⟩ h)

/-- The value of `logBaseRatRatExact?` on positive rationals `q` and `b`. -/
theorem logBaseRatRat_exact_value (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) (b : AzRat)
    (hs' : b.sign = true) (h0' : b.num ≠ 0) (hb1 : (AzRat.toRat b : ℝ) ≠ 1) (r : AzRat)
    (h : logBaseRatRatExact? (ratDyadicExp q) (oddPart q.num) (oddPart q.den) (ratDyadicExp b)
      (oddPart b.num) (oddPart b.den) = some r) :
    Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ) = (AzRat.toRat r : ℝ) := by
  rw [toRat_eq_oddParts b hs' h0'] at hb1 ⊢
  rw [toRat_eq_oddParts q hs h0]
  exact logBaseRatRatExact?_some _ _ _ _ _ _ (oddPart_spec q.num h0).2.1
    (oddPart_spec q.den q.den_nz).2.1 (oddPart_spec b.num h0').2.1
    (oddPart_spec b.den b.den_nz).2.1 hb1 r h

/-- Irrationality of `log_b q` when `logBaseRatRatExact?` finds nothing. -/
theorem irrational_logBaseRatRat_of_none (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0)
    (hq1 : (AzRat.toRat q : ℝ) ≠ 1) (b : AzRat) (hs' : b.sign = true) (h0' : b.num ≠ 0)
    (hb1 : (AzRat.toRat b : ℝ) ≠ 1)
    (h : logBaseRatRatExact? (ratDyadicExp q) (oddPart q.num) (oddPart q.den) (ratDyadicExp b)
      (oddPart b.num) (oddPart b.den) = none) :
    Irrational (Real.log (AzRat.toRat q : ℝ) / Real.log (AzRat.toRat b : ℝ)) := by
  rw [toRat_eq_oddParts b hs' h0'] at hb1 ⊢
  rw [toRat_eq_oddParts q hs h0] at hq1 ⊢
  exact irrational_of_logBaseRatRatExact?_none _ _ _ _ _ _ (oddPart_spec q.num h0).2.1
    (oddPart_spec q.den q.den_nz).2.1 (oddPart_spec b.num h0').2.1
    (oddPart_spec b.den b.den_nz).2.1 (coprime_oddParts q h0) (coprime_oddParts b h0') hb1 hq1 h

end Azurite.AzFloat
