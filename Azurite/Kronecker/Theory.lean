/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Kronecker substitution at two points: the arithmetic

A product of polynomials with nonnegative integer coefficients can be read off the product of
their values at one large number `B` (Kronecker substitution).  It can also be read off the
products of their values at `B` and at `−B` for a `B` of half the length (D. Harvey, *Faster
polynomial multiplication via multipoint Kronecker substitution*, J. Symbolic Comput. 44
(2009), §3): with `R = P Q`,

  `R(B) = P(B) Q(B)`,  `R(−B) = P(−B) Q(−B)`,

and `(R(B) + R(−B)) / 2`, `(R(B) − R(−B)) / 2` are the sums of the terms `rₖ Bᵏ` of even and
of odd `k`, in which the coefficients are `2` digits apart and do not overlap when
`rₖ < B²`.  Two products of half the size instead of one.

This file is independent of any limb representation.

* `evenPart R`, `oddPart R`: the polynomials with coefficients `r₀, r₂, …` and `r₁, r₃, …`.
* `evenValue R B`, `oddValue R B`: `∑ r₂ⱼ B^(2j)` and `∑ r₂ⱼ₊₁ B^(2j+1)`.
* `eval_eq_even_add_odd`, `eval_neg_eq_even_sub_odd`: `R(±B) = evenValue ± oddValue`.
* `two_mul_evenValue_mul`, `two_mul_oddValue_mul`: the two half sums for a product, from the
  four values of the factors.
-/

open Polynomial

namespace Azurite.Kronecker

/-- The polynomial with coefficients `r₀, r₂, r₄, …`. -/
noncomputable def evenPart (R : ℕ[X]) : ℕ[X] := contract 2 R

/-- The polynomial with coefficients `r₁, r₃, r₅, …`. -/
noncomputable def oddPart (R : ℕ[X]) : ℕ[X] := contract 2 R.divX

@[simp] theorem evenPart_coeff (R : ℕ[X]) (j : ℕ) : (evenPart R).coeff j = R.coeff (2 * j) := by
  rw [evenPart, coeff_contract (by norm_num), Nat.mul_comm]

@[simp] theorem oddPart_coeff (R : ℕ[X]) (j : ℕ) :
    (oddPart R).coeff j = R.coeff (2 * j + 1) := by
  rw [oddPart, coeff_contract (by norm_num), coeff_divX, Nat.mul_comm]

/-- `R(X) = E(X²) + X · O(X²)`. -/
theorem eq_expand_even_add_odd (R : ℕ[X]) :
    R = expand ℕ 2 (evenPart R) + X * expand ℕ 2 (oddPart R) := by
  ext n
  rw [coeff_add, coeff_expand (by norm_num)]
  rcases n with _ | n
  · simp
  · rw [coeff_X_mul, coeff_expand (by norm_num)]
    rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
    · have h1 : ¬ 2 ∣ 2 * j + 1 := by omega
      have h2 : 2 ∣ 2 * j := ⟨j, rfl⟩
      simp only [h1, h2, ↓reduceIte, oddPart_coeff, zero_add]
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
    · have h1 : 2 ∣ 2 * j + 1 + 1 := ⟨j + 1, by ring⟩
      have h2 : ¬ 2 ∣ 2 * j + 1 := by omega
      simp only [h1, h2, ↓reduceIte, evenPart_coeff, add_zero]
      congr 1
      omega

/-- `∑ r₂ⱼ B^(2j)`. -/
noncomputable def evenValue (R : ℕ[X]) (B : ℕ) : ℕ := (evenPart R).eval (B ^ 2)

/-- `∑ r₂ⱼ₊₁ B^(2j+1)`. -/
noncomputable def oddValue (R : ℕ[X]) (B : ℕ) : ℕ := B * (oddPart R).eval (B ^ 2)

theorem eval_eq_even_add_odd (R : ℕ[X]) (B : ℕ) :
    R.eval B = evenValue R B + oddValue R B := by
  conv_lhs => rw [eq_expand_even_add_odd R]
  simp [evenValue, oddValue, expand_eval]

/-- The value at `−B`, as an integer. -/
theorem eval_neg_eq_even_sub_odd (R : ℕ[X]) (B : ℕ) :
    (R.map (Nat.castRingHom ℤ)).eval (-(B : ℤ)) = (evenValue R B : ℤ) - oddValue R B := by
  conv_lhs => rw [eq_expand_even_add_odd R]
  simp only [Polynomial.map_add, Polynomial.map_mul, map_X, map_expand, eval_add, eval_mul,
    eval_X, expand_eval, evenValue, oddValue, neg_sq, eval_map]
  rw [← Nat.cast_pow, eval₂_at_natCast, eval₂_at_natCast]
  push_cast
  ring

/-- **The even half sum of a product**: `2 ∑ r₂ⱼ B^(2j) = P(B) Q(B) + P(−B) Q(−B)`. -/
theorem two_mul_evenValue_mul (P Q : ℕ[X]) (B : ℕ) :
    (2 * evenValue (P * Q) B : ℤ) =
      (P.eval B * Q.eval B : ℕ) +
        ((evenValue P B : ℤ) - oddValue P B) * ((evenValue Q B : ℤ) - oddValue Q B) := by
  have h1 := eval_eq_even_add_odd (P * Q) B
  have h2 := eval_neg_eq_even_sub_odd (P * Q) B
  rw [Polynomial.map_mul, eval_mul, eval_neg_eq_even_sub_odd, eval_neg_eq_even_sub_odd] at h2
  rw [eval_mul] at h1
  have h1' : ((P.eval B * Q.eval B : ℕ) : ℤ) = evenValue (P * Q) B + oddValue (P * Q) B := by
    exact_mod_cast h1
  rw [h1', h2]
  ring

/-- **The odd half sum of a product**: `2 ∑ r₂ⱼ₊₁ B^(2j+1) = P(B) Q(B) − P(−B) Q(−B)`. -/
theorem two_mul_oddValue_mul (P Q : ℕ[X]) (B : ℕ) :
    (2 * oddValue (P * Q) B : ℤ) =
      (P.eval B * Q.eval B : ℕ) -
        ((evenValue P B : ℤ) - oddValue P B) * ((evenValue Q B : ℤ) - oddValue Q B) := by
  have h1 := eval_eq_even_add_odd (P * Q) B
  have h2 := eval_neg_eq_even_sub_odd (P * Q) B
  rw [Polynomial.map_mul, eval_mul, eval_neg_eq_even_sub_odd, eval_neg_eq_even_sub_odd] at h2
  rw [eval_mul] at h1
  have h1' : ((P.eval B * Q.eval B : ℕ) : ℤ) = evenValue (P * Q) B + oddValue (P * Q) B := by
    exact_mod_cast h1
  rw [h1', h2]
  ring

end Azurite.Kronecker
