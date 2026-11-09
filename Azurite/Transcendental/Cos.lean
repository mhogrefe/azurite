/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# `cos q` and `sin q` are irrational for rational `q ≠ 0`

The Hermite–Lindemann argument at the conjugate pair `±in` (`n` a nonzero integer), from
Mathlib's analytic lemma `LindemannWeierstrass.exp_polynomial_approx` applied to
`f = X² + n² ∈ ℤ[X]`, whose roots `±in` are algebraic integers:

* For every large prime `p` there are `nₚ ∈ ℤ` with `p ∤ nₚ` and `gₚ ∈ ℤ[X]` with
  `|nₚ e^{±in} − p gₚ(±in)| ≤ c^p/(p−1)!`.  Summing the two, `gₚ(in) + gₚ(−in)` is an integer `m`
  (only the even powers survive, `(in)^{2j} = (−1)^j n^{2j}`; `exists_int_aeval_add_aeval_neg`),
  and `e^{in} + e^{−in} = 2 cos n`.  If `cos n = c/d` then the integer `E = 2c nₚ − p d m`
  satisfies `|E| ≤ 2d c^p/(p−1)! < 1`, so `E = 0` and `p ∣ 2c nₚ`; as `p ∤ nₚ`, `p ∣ 2c`, which
  fails for `p > 2|c|` once `c ≠ 0` (`not_cos_int_eq_div`).
* `cos n = 0` is excluded through `cos (2n) = −1` (`irrational_cos_int`), and a rational
  `q = a/b` reduces to the integer `a` by Chebyshev's `cos a = T_b(cos q)` with `T_b ∈ ℤ[X]`
  (`irrational_cos_rat`); `sin q` follows from `cos (2q) = 1 − 2 sin² q` (`irrational_sin_rat`).
-/

namespace Azurite

open Polynomial Finset Filter Topology
open scoped Nat

/-- `g(in) + g(−in)` is an integer for `g ∈ ℤ[X]`: only the even powers survive. -/
theorem exists_int_aeval_add_aeval_neg (g : ℤ[X]) (n : ℤ) :
    ∃ m : ℤ, aeval ((n : ℂ) * Complex.I) g + aeval (-((n : ℂ) * Complex.I)) g = (m : ℂ) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    simp only [map_add, Int.cast_add]
    linear_combination ha + hb
  | monomial k a =>
    simp only [aeval_monomial, algebraMap_int_eq, eq_intCast]
    rcases Nat.even_or_odd k with hk | hk
    · obtain ⟨j, hj⟩ := id hk
      refine ⟨2 * a * (-1) ^ j * n ^ (j + j), ?_⟩
      rw [hk.neg_pow, hj, show j + j = 2 * j by ring, pow_mul, mul_pow, Complex.I_sq]
      push_cast
      ring
    · refine ⟨0, ?_⟩
      rw [hk.neg_pow]
      push_cast
      ring

/-- `in` is a root of `X² + n²`. -/
theorem mul_I_mem_aroots (n : ℤ) (hn : n ≠ 0) :
    (n : ℂ) * Complex.I ∈ (X ^ 2 + C (n ^ 2) : ℤ[X]).aroots ℂ := by
  rw [mem_aroots]
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun P : ℤ[X] => P.eval 0) h
    simp at this
    exact hn this
  · simp [mul_pow, Complex.I_sq]

theorem neg_mul_I_mem_aroots (n : ℤ) (hn : n ≠ 0) :
    -((n : ℂ) * Complex.I) ∈ (X ^ 2 + C (n ^ 2) : ℤ[X]).aroots ℂ := by
  rw [mem_aroots]
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun P : ℤ[X] => P.eval 0) h
    simp at this
    exact hn this
  · simp [mul_pow, Complex.I_sq]

/-- **Hermite–Lindemann at `±in`**: `cos n` is not a rational with nonzero numerator. -/
theorem not_cos_int_eq_div {n : ℤ} (hn : n ≠ 0) {c d : ℤ} (hd : 0 < d) (hc : c ≠ 0)
    (h : Real.cos n = (c : ℝ) / d) : False := by
  set f : ℤ[X] := X ^ 2 + C (n ^ 2) with hf
  have hf0 : f.eval 0 ≠ 0 := by simp [hf, hn]
  obtain ⟨cst, hcst⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  -- `2d cst^p/(p−1)! → 0`
  have hlim : Tendsto (fun p : ℕ => (2 * d : ℝ) * (cst ^ p / ((p - 1)! : ℝ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun p : ℕ => cst ^ (p - 1) / ((p - 1)! : ℝ)) atTop (𝓝 0) :=
      (FloorSemiring.tendsto_pow_div_factorial_atTop cst).comp (tendsto_sub_atTop_nat 1)
    have h3 : Tendsto (fun p : ℕ => (2 * d : ℝ) * cst * (cst ^ (p - 1) / ((p - 1)! : ℝ))) atTop
        (𝓝 0) := by
      simpa using h2.const_mul ((2 * d : ℝ) * cst)
    refine h3.congr' (eventually_atTop.mpr ⟨1, fun p hp => ?_⟩)
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
  -- a large prime
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes
    (max N (max (f.eval 0).natAbs (2 * c).natAbs) + 1)
  obtain ⟨nₚ, hnp, gₚ, -, hbound⟩ := hcst p (by omega) hp
  have hb₁ := hbound (mul_I_mem_aroots n hn)
  have hb₂ := hbound (neg_mul_I_mem_aroots n hn)
  rw [zsmul_eq_mul, nsmul_eq_mul] at hb₁ hb₂
  obtain ⟨m, hm⟩ := exists_int_aeval_add_aeval_neg gₚ n
  -- `e^{in} + e^{−in} = 2 cos n`
  have hcos : Complex.exp ((n : ℂ) * Complex.I) + Complex.exp (-((n : ℂ) * Complex.I))
      = 2 * ((c : ℂ) / d) := by
    have := Complex.two_cos (x := (n : ℂ))
    rw [neg_mul] at this
    rw [← this, ← Complex.ofReal_intCast, ← Complex.ofReal_cos, h]
    push_cast
    ring
  -- the integer `E`
  set E : ℤ := 2 * c * nₚ - p * d * m with hEdef
  have hE : (E : ℂ) = (d : ℂ) * ((nₚ * Complex.exp ((n : ℂ) * Complex.I)
      - p * aeval ((n : ℂ) * Complex.I) gₚ)
      + (nₚ * Complex.exp (-((n : ℂ) * Complex.I)) - p * aeval (-((n : ℂ) * Complex.I)) gₚ)) := by
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have e1 : (d : ℂ) * ((nₚ * Complex.exp ((n : ℂ) * Complex.I)
        - p * aeval ((n : ℂ) * Complex.I) gₚ)
        + (nₚ * Complex.exp (-((n : ℂ) * Complex.I)) - p * aeval (-((n : ℂ) * Complex.I)) gₚ))
        = (d : ℂ) * (nₚ * (Complex.exp ((n : ℂ) * Complex.I)
          + Complex.exp (-((n : ℂ) * Complex.I)))
          - p * (aeval ((n : ℂ) * Complex.I) gₚ + aeval (-((n : ℂ) * Complex.I)) gₚ)) := by ring
    rw [e1, hcos, hm, hEdef]
    push_cast
    field_simp
  have hEle : ‖(E : ℂ)‖ ≤ (2 * d : ℝ) * (cst ^ p / ((p - 1)! : ℝ)) := by
    rw [hE, norm_mul, Complex.norm_intCast, abs_of_pos (by exact_mod_cast hd)]
    have := (norm_add_le _ _).trans (add_le_add hb₁ hb₂)
    calc (d : ℝ) * ‖_‖ ≤ (d : ℝ) * (cst ^ p / ((p - 1)! : ℝ) + cst ^ p / ((p - 1)! : ℝ)) :=
          mul_le_mul_of_nonneg_left this (by exact_mod_cast hd.le)
      _ = (2 * d : ℝ) * (cst ^ p / ((p - 1)! : ℝ)) := by ring
  have hlt : ‖(E : ℂ)‖ < 1 := hEle.trans_lt (hN p (by omega))
  have hE0 : E = 0 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs] at hlt
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  -- `p ∣ 2c nₚ`, impossible
  have hdvd : (p : ℤ) ∣ 2 * c * nₚ := ⟨d * m, by linear_combination hE0⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h2 | h2
  · have h1 : p ∣ (2 * c).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h2
      simpa using this
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.mpr (by positivity)) h1
    omega
  · exact hnp h2

/-- `cos n` is irrational for every nonzero integer `n`. -/
theorem irrational_cos_int {n : ℤ} (hn : n ≠ 0) : Irrational (Real.cos n) := by
  rintro ⟨q, hq⟩
  by_cases hq0 : q = 0
  · -- `cos n = 0`, so `cos (2n) = −1`
    subst hq0
    rw [Rat.cast_zero] at hq
    have h2 : Real.cos ((2 * n : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) / (1 : ℤ) := by
      push_cast
      rw [Real.cos_two_mul, ← hq]
      ring
    exact not_cos_int_eq_div (by omega) one_pos (by norm_num) h2
  · have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
    have hden : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
    exact not_cos_int_eq_div hn hden hnum (by rw [← hq, Rat.cast_def]; push_cast; ring)

/-- `cos q` is irrational for every nonzero rational `q`: `cos (num q) = T_{den q}(cos q)`. -/
theorem irrational_cos_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.cos q) := by
  rintro ⟨s, hs⟩
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  apply irrational_cos_int hnum
  -- `cos (num q) = (T ℝ den).eval (cos q)`, a rational
  have h1 : Real.cos (q.num : ℝ) = (Chebyshev.T ℝ q.den).eval (Real.cos q) := by
    rw [Chebyshev.T_real_cos]
    congr 1
    have := Rat.mul_den_eq_num q
    have h := congrArg (fun x : ℚ => (x : ℝ)) this
    push_cast at h
    rw [← h]
    push_cast
    ring
  refine ⟨(Chebyshev.T ℚ q.den).eval s, ?_⟩
  rw [h1, ← hs, ← Chebyshev.map_T (algebraMap ℚ ℝ), eval_map]
  exact (eval₂_at_apply (algebraMap ℚ ℝ) s).symm

/-- `sin q` is irrational for every nonzero rational `q`: `cos (2q) = 1 − 2 sin² q`. -/
theorem irrational_sin_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.sin q) := by
  rintro ⟨s, hs⟩
  have h2 : (2 * q : ℚ) ≠ 0 := by positivity
  apply irrational_cos_rat h2
  refine ⟨1 - 2 * s ^ 2, ?_⟩
  push_cast
  rw [Real.cos_two_mul, Real.cos_sq', ← hs]
  ring

end Azurite
