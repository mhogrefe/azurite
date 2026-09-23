/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter10.Section10_1.Notation_10_5
import Mathlib.Algebra.Order.Chebyshev

/-!
# BPR Lemma 10.6: the modified Cauchy bound bounds the roots

`lemma_10_6`: every root of `P ≠ 0` has absolute value strictly smaller than
the modified Cauchy bound `C′(P)` of Notation 10.5. BPR's proof: from
`aₚx^p = −∑_{i<p} aᵢxⁱ`, squaring and applying the Cauchy–Schwarz inequality
(Mathlib's `sq_sum_le_card_mul_sum_sq`), for `|x| ≥ 1` each `(x²)^i ≤
(x²)^{p−1}` gives `x² ≤ p·(∑_{i<p} aᵢ²/aₚ²)`, hence
`|x| ≤ x² < C′(P)`; for `|x| ≤ 1` the bound follows from `C′(P) ≥ 1`.
-/

namespace Azurite.BPR

open Polynomial Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **BPR Lemma 10.6.** The absolute value of any root of `P` is smaller than
the modified Cauchy bound `C′(P)`. -/
theorem lemma_10_6 {P : K[X]} (hP : P ≠ 0) {x : K} (hx : P.IsRoot x) :
    |x| < cauchyBound' P := by
  set p := P.natDegree with hp
  -- a nonzero polynomial with a root has positive degree
  have hdP : 0 < p := by
    by_contra h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0)
    rw [hC, Polynomial.IsRoot, Polynomial.eval_C] at hx
    exact hP (by rw [hC, hx, Polynomial.C_0])
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rcases lt_or_ge |x| 1 with hx1 | hx1
  -- |x| ≤ 1: immediate from C′(P) ≥ 1
  · exact lt_of_lt_of_le hx1 (one_le_cauchyBound' hP)
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx1
    linarith
  have hx2 : (1 : K) ≤ x ^ 2 := by
    have := sq_abs x
    nlinarith [hx1]
  -- normalized vanishing evaluation
  have heval : ∑ i ∈ Finset.range (p + 1), (P.coeff i / P.leadingCoeff) * x ^ i = 0 := by
    have h0 : ∑ i ∈ Finset.range (p + 1), P.coeff i * x ^ i = 0 := by
      have h := hx
      rwa [Polynomial.IsRoot, Polynomial.eval_eq_sum_range] at h
    calc ∑ i ∈ Finset.range (p + 1), (P.coeff i / P.leadingCoeff) * x ^ i
        = (∑ i ∈ Finset.range (p + 1), P.coeff i * x ^ i) / P.leadingCoeff := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [h0, zero_div]
  rw [Finset.sum_range_succ, show P.coeff p / P.leadingCoeff = 1 from by
    rw [show P.coeff p = P.leadingCoeff from rfl, div_self hlc], one_mul] at heval
  have hxp : x ^ p = -∑ i ∈ Finset.range p, (P.coeff i / P.leadingCoeff) * x ^ i := by
    linarith [heval]
  set S := ∑ i ∈ Finset.range (p + 1), (P.coeff i / P.leadingCoeff) ^ 2 with hS
  have hS1 : 1 ≤ S := one_le_sum_sq_div_leadingCoeff hP
  have hsplit : ∑ i ∈ Finset.range p, (P.coeff i / P.leadingCoeff) ^ 2 = S - 1 := by
    rw [hS, Finset.sum_range_succ, show P.coeff p / P.leadingCoeff = 1 from by
      rw [show P.coeff p = P.leadingCoeff from rfl, div_self hlc], one_pow]
    ring
  -- square, apply Cauchy–Schwarz, and bound the powers of `x²`
  have hkey : (x ^ p) ^ 2 ≤ (p : K) * ((S - 1) * (x ^ 2) ^ (p - 1)) := by
    calc (x ^ p) ^ 2
        = (∑ i ∈ Finset.range p, (P.coeff i / P.leadingCoeff) * x ^ i) ^ 2 := by
          rw [hxp, neg_sq]
      _ ≤ ((Finset.range p).card : K)
            * ∑ i ∈ Finset.range p, ((P.coeff i / P.leadingCoeff) * x ^ i) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = (p : K) * ∑ i ∈ Finset.range p, ((P.coeff i / P.leadingCoeff) * x ^ i) ^ 2 := by
          rw [Finset.card_range]
      _ ≤ (p : K) * ((S - 1) * (x ^ 2) ^ (p - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← hsplit, Finset.sum_mul]
          apply Finset.sum_le_sum
          intro i hi
          rw [mul_pow, show (x ^ i) ^ 2 = (x ^ 2) ^ i from by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hx2 (by
              have := Finset.mem_range.mp hi
              omega : i ≤ p - 1)) (sq_nonneg _)
  -- divide by `(x²)^{p−1}`
  have hxpow : (0 : K) < (x ^ 2) ^ (p - 1) := by positivity
  have hdiv : x ^ 2 ≤ (p : K) * (S - 1) := by
    have h := hkey
    rw [show (x ^ p) ^ 2 = x ^ 2 * (x ^ 2) ^ (p - 1) from by
        rw [← pow_succ', pow_right_comm]
        congr 1
        omega,
      show (p : K) * ((S - 1) * (x ^ 2) ^ (p - 1))
        = ((p : K) * (S - 1)) * (x ^ 2) ^ (p - 1) from by ring] at h
    exact le_of_mul_le_mul_right h hxpow
  -- conclude: |x| ≤ x² ≤ p(S − 1) < (p+1)S = C′(P)
  have habs : |x| ≤ x ^ 2 := by
    have h1 : |x| * 1 ≤ |x| * |x| := mul_le_mul_of_nonneg_left hx1 (abs_nonneg x)
    have h2 : |x| * |x| = x ^ 2 := by rw [← sq_abs]; ring
    linarith [h1, h2.le]
  have hfinal : (p : K) * (S - 1) < ((p : K) + 1) * S := by
    have hp0 : (0 : K) ≤ (p : K) := Nat.cast_nonneg p
    nlinarith [hS1]
  calc |x| ≤ x ^ 2 := habs
    _ ≤ (p : K) * (S - 1) := hdiv
    _ < ((p : K) + 1) * S := hfinal
    _ = cauchyBound' P := by rw [cauchyBound', ← hp, ← hS]

end Azurite.BPR
