/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.Reciprocal
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Brent–Zimmermann §4.2.4: Newton's method for formal power series

Newton's method applies to formal power series `A(z) = a_0 + a_1 z + …` with `ord A = 0` as well
as to real functions.  The reciprocal iteration (4.5) with `y = 1 − z` and `x_0 = 1` converges
quadratically to `(1 − z)^(−1) = ∑ z^n`: here "quadratically" means that `ord e_j`, the order
of the error, grows like `2^j`.  With the notation of §4.2.2, `u_0 = z`, `u_j = z^(2^j)` and
`x_j = (1 − u_j) / (1 − z) = 1/(1 − z) + O(z^(2^j))`.

The section also recalls the formal derivative `A' = ∑ j a_j z^(j−1)` and the formal integral
`∑ a_j / (j + 1) z^(j+1)`, and remarks that neither has a useful analogue for integers
`∑ a_j β^j`, so that some fast power-series algorithms have no integer counterpart (Exercise
4.1) — a remark, not a theorem.

The reciprocal iteration and its error identities (4.6), (4.7) are purely algebraic, so they are
stated here over an arbitrary commutative ring (`ringReciprocalStep`, `ringRecipError`), which
covers both `ℝ` (§4.2.2) and `R⟦X⟧`; the worked example is then the ring identity
`x_j = ∑_{n < 2^j} z^n` for `y = 1 − z`.

* `ringReciprocalStep`, `ringReciprocalSeq`, `ringRecipError` — (4.5) and `u` over a
  commutative ring; `ringRecipError_step` (4.6), `ringRecipError_seq` (4.7),
  `reciprocalStep_eq_ringReciprocalStep`.
* `ringReciprocalSeq_one_sub` — the example: from `x_0 = 1` with `y = 1 − z`,
  `x_j = ∑_{n < 2^j} z^n` and `(1 − z) x_j = 1 − z^(2^j)`.
* `powerSeriesReciprocalSeq_sub_inv`, `order_powerSeriesReciprocalSeq_sub_inv` — in `R⟦X⟧`,
  `x_j − (1 − X)^(−1) = −X^(2^j) · ∑ X^n`, of order exactly `2^j`.
* `coeff_derivative'` — the formal derivative in the text's indexing,
  `coeff n A' = (n + 1) a_{n+1}`; `integral` — the formal integral over a field of
  characteristic zero, with `coeff_integral_zero`/`coeff_integral_succ`, `constantCoeff_integral`, `derivative_integral`
  and `integral_derivative` (`= A − a_0`).
-/

namespace Azurite

namespace BZ

open Finset PowerSeries

/-! ### The reciprocal iteration over a commutative ring -/

section Ring

variable {α : Type*} [CommRing α]

/-- (4.5) over a commutative ring: `x + x (1 − x y)`. -/
def ringReciprocalStep (y x : α) : α := x + x * (1 - x * y)

/-- The iterates of (4.5) from `x₀`. -/
def ringReciprocalSeq (y x₀ : α) : ℕ → α
  | 0 => x₀
  | n + 1 => ringReciprocalStep y (ringReciprocalSeq y x₀ n)

@[simp] theorem ringReciprocalSeq_zero (y x₀ : α) : ringReciprocalSeq y x₀ 0 = x₀ := rfl

@[simp] theorem ringReciprocalSeq_succ (y x₀ : α) (n : ℕ) :
    ringReciprocalSeq y x₀ (n + 1) = ringReciprocalStep y (ringReciprocalSeq y x₀ n) := rfl

/-- `u = 1 − x y`. -/
def ringRecipError (y x : α) : α := 1 - x * y

/-- (4.6) over a commutative ring. -/
theorem ringRecipError_step (y x : α) :
    ringRecipError y (ringReciprocalStep y x) = ringRecipError y x ^ 2 := by
  unfold ringRecipError ringReciprocalStep
  ring

/-- (4.7) over a commutative ring. -/
theorem ringRecipError_seq (y x₀ : α) (j : ℕ) :
    ringRecipError y (ringReciprocalSeq y x₀ j) = ringRecipError y x₀ ^ (2 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [ringReciprocalSeq_succ, ringRecipError_step, ih, ← pow_mul, pow_succ]

/-- The real iteration of §4.2.2 is the ring one at `α = ℝ`. -/
theorem reciprocalStep_eq_ringReciprocalStep (y x : ℝ) :
    reciprocalStep y x = ringReciprocalStep y x := rfl

/-- The example of the text: with `y = 1 − z` and `x_0 = 1`, `u_0 = z`, `u_j = z^(2^j)`, and the
`j`-th iterate is the partial geometric sum `∑_{n < 2^j} z^n`, with `(1 − z) x_j = 1 − z^(2^j)`. -/
theorem ringReciprocalSeq_one_sub (z : α) (j : ℕ) :
    ringReciprocalSeq (1 - z) 1 j = ∑ n ∈ range (2 ^ j), z ^ n ∧
      (1 - z) * ringReciprocalSeq (1 - z) 1 j = 1 - z ^ (2 ^ j) := by
  have hu : ∀ j, ringRecipError (1 - z) (ringReciprocalSeq (1 - z) 1 j) = z ^ (2 ^ j) := by
    intro j; rw [ringRecipError_seq]; unfold ringRecipError; ring_nf
  refine ⟨?_, ?_⟩
  · induction j with
    | zero => simp
    | succ j ih =>
      -- `x_{j+1} = x_j (1 + u_j) = x_j (1 + z^(2^j))`
      have hstep : ringReciprocalSeq (1 - z) 1 (j + 1)
          = ringReciprocalSeq (1 - z) 1 j * (1 + z ^ (2 ^ j)) := by
        rw [ringReciprocalSeq_succ, ← hu j]
        unfold ringReciprocalStep ringRecipError
        ring
      rw [hstep, ih, pow_succ, mul_two, Finset.sum_range_add, mul_add, mul_one, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
  · have h := hu j
    unfold ringRecipError at h
    linear_combination -h

end Ring

/-! ### Formal power series -/

section PowerSeries

variable {R : Type*} [CommRing R]

/-- In `R⟦X⟧`, the error of the `j`-th iterate for `(1 − X)^(−1) = ∑ X^n` is `−X^(2^j) ∑ X^n`. -/
theorem powerSeriesReciprocalSeq_sub_inv (j : ℕ) :
    ringReciprocalSeq (1 - X : R⟦X⟧) 1 j - mk 1 = -(X ^ (2 ^ j) * mk 1) := by
  have h := (ringReciprocalSeq_one_sub (X : R⟦X⟧) j).2
  have hinv : (mk 1 : R⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one R
  -- multiply the target by the unit `1 − X`
  have hunit : IsUnit (1 - X : R⟦X⟧) :=
    ⟨⟨1 - X, mk 1, by rw [mul_comm]; exact hinv, hinv⟩, rfl⟩
  apply hunit.mul_left_cancel
  linear_combination h - (1 - X ^ (2 ^ j)) * hinv

/-- Quadratic convergence for formal power series: the error of the `j`-th iterate has order
exactly `2^j`. -/
theorem order_powerSeriesReciprocalSeq_sub_inv [Nontrivial R] (j : ℕ) :
    order (ringReciprocalSeq (1 - X : R⟦X⟧) 1 j - mk 1) = ((2 ^ j : ℕ) : ℕ∞) := by
  rw [powerSeriesReciprocalSeq_sub_inv, order_eq_nat]
  constructor
  · rw [map_neg, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, coeff_mk, Pi.one_apply]
    exact neg_ne_zero.mpr one_ne_zero
  · intro i hi
    rw [map_neg, coeff_X_pow_mul', ite_eq_right (not_le.mpr hi), neg_zero]

/-- The formal derivative in the text's indexing: `coeff n A' = (n + 1) a_{n+1}`. -/
theorem coeff_derivative' (A : R⟦X⟧) (n : ℕ) :
    coeff n (derivative A) = (n + 1) * coeff (n + 1) A := by
  rw [coeff_derivative, mul_comm]

end PowerSeries

section Field

variable {K : Type*} [Field K]

/-- The formal integral `∑ a_j / (j + 1) z^(j+1)`, over a field of characteristic zero. -/
noncomputable def integral (A : K⟦X⟧) : K⟦X⟧ :=
  mk fun n => if n = 0 then 0 else coeff (n - 1) A / n

theorem coeff_integral_zero (A : K⟦X⟧) : coeff 0 (integral A) = 0 := by
  simp [integral]

theorem coeff_integral_succ (A : K⟦X⟧) (j : ℕ) :
    coeff (j + 1) (integral A) = coeff j A / (j + 1) := by
  simp [integral]

theorem constantCoeff_integral (A : K⟦X⟧) : constantCoeff (integral A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_integral_zero]

/-- Differentiating the integral gives back the series. -/
theorem derivative_integral [CharZero K] (A : K⟦X⟧) : derivative (integral A) = A := by
  ext n
  rw [coeff_derivative', coeff_integral_succ]
  have : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

/-- Integrating the derivative loses only the constant term: `∫ A' = A − a_0`. -/
theorem integral_derivative [CharZero K] (A : K⟦X⟧) :
    integral (derivative A) = A - C (constantCoeff A) := by
  ext n
  cases n with
  | zero => simp [coeff_integral_zero]
  | succ n =>
    rw [coeff_integral_succ, coeff_derivative', map_sub, coeff_C, ite_eq_right (Nat.succ_ne_zero n),
      sub_zero]
    have : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp

end Field

end BZ

end Azurite
