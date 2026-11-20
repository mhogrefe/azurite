/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.PolygammaStirling
import Azurite.DLMF.Chapter5.Section15
import Azurite.Feldman.Theorem4
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Irrational values of the polygamma functions

For an odd `n`, `ψ⁽ⁿ⁾(1) = n! ζ(n + 1)` is a nonzero rational multiple of `π^(n+1)`, hence
irrational (`π` is transcendental).  The recurrence moves this to the positive integers, the
relation `ψ⁽ⁿ⁾(1/2) = (2^(n+1) − 1) ψ⁽ⁿ⁾(1)` (the series over the odd and the even integers)
to `1/2`, and the recurrence again to every half-integer:

* `irrational_polygammaR_nat`: `ψ⁽ⁿ⁾(m)`, `m ≥ 1`;
* `irrational_polygammaR_half`: `ψ⁽ⁿ⁾(j + 1/2)`, `j ∈ ℤ`;
* `irrational_polygammaR_div_two`: both, as `ψ⁽ⁿ⁾(N/2)` for `N` odd or positive.
-/

namespace Azurite

open Finset
open scoped Nat

theorem isAlgebraic_int_ratCast (r : ℚ) : IsAlgebraic ℤ (r : ℝ) :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) r)

/-- A positive power of `π` is irrational. -/
theorem irrational_pi_pow {k : ℕ} (hk : 0 < k) : Irrational (Real.pi ^ k) := by
  rintro ⟨r, hr⟩
  apply Azurite.Feldman.transcendental_pi_real
  refine IsAlgebraic.of_pow hk ?_
  rw [← hr]
  exact isAlgebraic_int_ratCast r

/-- `ψ⁽ⁿ⁾(1)` is a rational multiple of `π^(n+1)` for an odd `n`. -/
theorem polygammaR_one_eq {n : ℕ} (hn : Odd n) :
    ∃ q : ℚ, polygammaR n 1 = q * Real.pi ^ (n + 1) := by
  obtain ⟨j, rfl⟩ := hn
  have h := DLMF.dlmf_5_15_2 (n := 2 * j + 1) (by omega)
  have hz := riemannZeta_two_mul_nat (k := j + 1) (by omega)
  have e : ((2 * j + 1 : ℕ) : ℂ) + 1 = 2 * ((j + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [e, hz] at h
  refine ⟨(-1) ^ (2 * j + 1 + 1) * ((2 * j + 1)! : ℚ) * ((-1) ^ (j + 1 + 1) * 2 ^ (2 * (j + 1) - 1)
    * bernoulli (2 * (j + 1)) / ((2 * (j + 1))! : ℚ)), ?_⟩
  have hre : polygammaR (2 * j + 1) 1 = (DLMF.polygamma (2 * j + 1) (1 : ℂ)).re := by
    unfold polygammaR
    norm_num
  rw [hre, h]
  have : ((-1 : ℂ) ^ (2 * j + 1 + 1) * ((2 * j + 1)! : ℂ)
      * ((-1) ^ (j + 1 + 1) * (2 : ℂ) ^ (2 * (j + 1) - 1) * (Real.pi : ℂ) ^ (2 * (j + 1))
        * bernoulli (2 * (j + 1)) / ((2 * (j + 1))! : ℂ)))
      = (((((-1) ^ (2 * j + 1 + 1) * ((2 * j + 1)! : ℚ) * ((-1) ^ (j + 1 + 1)
        * 2 ^ (2 * (j + 1) - 1) * bernoulli (2 * (j + 1)) / ((2 * (j + 1))! : ℚ)) : ℚ) : ℝ)
        * Real.pi ^ (2 * j + 1 + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.ofReal_re]

/-- `ψ⁽ⁿ⁾(x) > 0` for an odd `n` and `x > 0`. -/
theorem polygammaR_pos_of_odd {n : ℕ} (hn : Odd n) {x : ℝ} (hx : 0 < x) :
    0 < polygammaR n x := by
  have hn1 : 1 ≤ n := hn.pos
  have hnp : ∀ m : ℕ, x ≠ -m := fun m hm => by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h := hasSum_polygammaR hn1 hnp
  have hs : (-1 : ℝ) ^ (n + 1) = 1 := (Odd.add_one hn).neg_one_pow
  have hterm : ∀ k : ℕ, 0 ≤ (-1 : ℝ) ^ (n + 1) * (n ! : ℝ) / ((k : ℝ) + x) ^ (n + 1) := by
    intro k
    rw [hs]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    positivity
  refine lt_of_lt_of_le ?_ (le_hasSum h 0 fun k _ => hterm k)
  rw [hs]
  simp only [Nat.cast_zero, zero_add, one_mul]
  positivity

/-- `ψ⁽ⁿ⁾(1)` is irrational for an odd `n`. -/
theorem irrational_polygammaR_one {n : ℕ} (hn : Odd n) : Irrational (polygammaR n 1) := by
  obtain ⟨q, hq⟩ := polygammaR_one_eq hn
  have hpos := polygammaR_pos_of_odd hn one_pos
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [hq] at hpos
    simp at hpos
  rw [hq]
  exact (irrational_pi_pow (Nat.succ_pos n)).ratCast_mul hq0

/-- A rational shift: `ψ⁽ⁿ⁾(x) − ψ⁽ⁿ⁾(x + K)` is rational at a rational `x`. -/
theorem polygammaR_sub_add_nat_rat {n : ℕ} (hn : 1 ≤ n) {x : ℚ} (hx : ∀ m : ℕ, (x : ℝ) ≠ -m)
    (K : ℕ) : ∃ ρ : ℚ, polygammaR n (x : ℝ) = polygammaR n ((x : ℝ) + K) + ρ := by
  refine ⟨(-1) ^ (n + 1) * (n ! : ℚ) * ∑ j ∈ range K, 1 / (x + j) ^ (n + 1), ?_⟩
  rw [polygammaR_add_nat hn hx K]
  push_cast
  rfl

/-- **`ψ⁽ⁿ⁾(m)` is irrational** for an odd `n` and an integer `m ≥ 1`. -/
theorem irrational_polygammaR_nat {n : ℕ} (hn : Odd n) {m : ℕ} (hm : 1 ≤ m) :
    Irrational (polygammaR n m) := by
  obtain ⟨K, rfl⟩ : ∃ K, m = 1 + K := ⟨m - 1, by omega⟩
  obtain ⟨ρ, hρ⟩ := polygammaR_sub_add_nat_rat (n := n) hn.pos (x := 1) (fun k hk => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
    rw [h1] at hk
    linarith) K
  have h1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  rw [h1] at hρ
  have hirr := irrational_polygammaR_one hn
  rw [hρ] at hirr
  have := hirr.sub_ratCast ρ
  rw [add_sub_cancel_right] at this
  convert this using 2
  push_cast
  rfl

/-- `ψ⁽ⁿ⁾(1/2) = (2^(n+1) − 1) ψ⁽ⁿ⁾(1)`: the series over the odd and the even integers. -/
theorem polygammaR_half {n : ℕ} (hn : 1 ≤ n) :
    polygammaR n (1 / 2) = (2 ^ (n + 1) - 1) * polygammaR n 1 := by
  have hnp1 : ∀ m : ℕ, (1 : ℝ) ≠ -m := fun m hm => by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hnp2 : ∀ m : ℕ, (1 / 2 : ℝ) ≠ -m := fun m hm => by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h1 := hasSum_polygammaR hn hnp1
  have h2 := hasSum_polygammaR hn hnp2
  have he : HasSum (fun k : ℕ => (-1 : ℝ) ^ (n + 1) * (n ! : ℝ)
      / (((2 * k : ℕ) : ℝ) + 1) ^ (n + 1)) ((1 / 2) ^ (n + 1) * polygammaR n (1 / 2)) := by
    convert h2.mul_left ((1 / 2 : ℝ) ^ (n + 1)) using 1
    funext k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e : (((2 * k : ℕ) : ℝ) + 1) ^ (n + 1) = 2 ^ (n + 1) * ((k : ℝ) + 1 / 2) ^ (n + 1) := by
      rw [← mul_pow]
      push_cast
      ring_nf
    rw [e]
    field_simp
    rw [← mul_pow]
    norm_num
  have ho : HasSum (fun k : ℕ => (-1 : ℝ) ^ (n + 1) * (n ! : ℝ)
      / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ (n + 1)) ((1 / 2) ^ (n + 1) * polygammaR n 1) := by
    convert h1.mul_left ((1 / 2 : ℝ) ^ (n + 1)) using 1
    funext k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e : (((2 * k + 1 : ℕ) : ℝ) + 1) ^ (n + 1) = 2 ^ (n + 1) * ((k : ℝ) + 1) ^ (n + 1) := by
      rw [← mul_pow]
      push_cast
      ring_nf
    rw [e]
    field_simp
    rw [← mul_pow]
    norm_num
  have hsum := (HasSum.even_add_odd
    (f := fun k : ℕ => (-1 : ℝ) ^ (n + 1) * (n ! : ℝ) / ((k : ℝ) + 1) ^ (n + 1)) he ho).unique h1
  have e2 : (1 / 2 : ℝ) ^ (n + 1) = 1 / 2 ^ (n + 1) := by rw [one_div_pow]
  rw [e2] at hsum
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 2 ^ (n + 1) := ⟨_, rfl⟩
  rw [← hP] at hsum ⊢
  have hP0 : 0 < P := by rw [hP]; positivity
  have h3 : polygammaR n (1 / 2) + polygammaR n 1 = P * polygammaR n 1 := by
    field_simp at hsum
    linarith only [hsum]
  linarith only [h3]

/-- **`ψ⁽ⁿ⁾(j + 1/2)` is irrational** for an odd `n` and an integer `j`. -/
theorem irrational_polygammaR_half {n : ℕ} (hn : Odd n) (j : ℤ) :
    Irrational (polygammaR n ((j : ℝ) + 1 / 2)) := by
  have hn1 := hn.pos
  have hhalf : Irrational (polygammaR n (1 / 2)) := by
    rw [polygammaR_half hn1]
    have h := (irrational_polygammaR_one hn).ratCast_mul
      (q := (2 ^ (n + 1) - 1 : ℚ)) (by
        have : (2 : ℚ) ≤ 2 ^ (n + 1) := by
          calc (2 : ℚ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith)
    convert h using 2
    push_cast
    rfl
  have hni : ∀ (i : ℤ) (m : ℕ), ((i : ℝ) + 1 / 2) ≠ -m := by
    intro i m hm
    have h2 : (2 * i + 1 : ℤ) = -2 * (m : ℤ) := by
      have : (2 : ℝ) * i + 1 = -2 * m := by linarith
      exact_mod_cast this
    omega
  rcases le_or_gt 0 j with hj | hj
  · -- `j ≥ 0`: `ψ(1/2) = ψ(1/2 + j) + ρ`
    obtain ⟨K, rfl⟩ : ∃ K : ℕ, j = K := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
    obtain ⟨ρ, hρ⟩ := polygammaR_sub_add_nat_rat (n := n) hn1 (x := 1 / 2) (fun m hm => by
      have := hni 0 m
      push_cast at hm this
      exact this (by linarith)) K
    have e : (((1 / 2 : ℚ) : ℝ)) = 1 / 2 := by norm_num
    rw [e] at hρ
    rw [hρ] at hhalf
    have := hhalf.sub_ratCast ρ
    rw [add_sub_cancel_right] at this
    convert this using 2
    push_cast
    ring
  · -- `j < 0`: `ψ(j + 1/2) = ψ(1/2) + ρ`
    obtain ⟨K, hK⟩ : ∃ K : ℕ, j = -(K : ℤ) := ⟨(-j).toNat, by omega⟩
    obtain ⟨ρ, hρ⟩ := polygammaR_sub_add_nat_rat (n := n) hn1 (x := (j : ℚ) + 1 / 2)
      (fun m hm => by
        have := hni j m
        push_cast at hm
        exact this hm) K
    have e : (((j : ℚ) + 1 / 2 : ℚ) : ℝ) = (j : ℝ) + 1 / 2 := by push_cast; ring
    rw [e] at hρ
    have e2 : (j : ℝ) + 1 / 2 + K = 1 / 2 := by
      rw [hK]
      push_cast
      ring
    rw [e2] at hρ
    rw [hρ]
    exact hhalf.add_ratCast ρ

/-- **`ψ⁽ⁿ⁾(N/2)` is irrational** for an odd `n` when `N` is odd, or positive. -/
theorem irrational_polygammaR_div_two {n : ℕ} (hn : Odd n) {N : ℤ} (h : N % 2 = 1 ∨ 0 < N) :
    Irrational (polygammaR n ((N : ℝ) / 2)) := by
  rcases Int.emod_two_eq_zero_or_one N with h0 | h1
  · have hpos : 0 < N := h.resolve_left (by omega)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, N = 2 * (m : ℤ) := ⟨(N / 2).toNat, by omega⟩
    have e : (N : ℝ) / 2 = (m : ℕ) := by
      rw [hm]
      push_cast
      ring
    rw [e]
    exact irrational_polygammaR_nat hn (by omega)
  · have e : (N : ℝ) / 2 = ((N / 2 : ℤ) : ℝ) + 1 / 2 := by
      have : N = 2 * (N / 2) + 1 := by omega
      have h2 : (N : ℝ) = 2 * ((N / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast this
      rw [h2]
      ring
    rw [e]
    exact irrational_polygammaR_half hn _

end Azurite
