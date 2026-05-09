import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Algebraic.Basic

/-! # BPR Section 2.1 — Example 2.10: ℝ and ℝ_alg are real closed

> The field ℝ of real numbers is of course real closed. The real
> algebraic numbers, i.e. those real numbers that satisfy an equation
> with integer coefficients, form a real closed field denoted Ralg
> (see Exercise 2.11).

The first claim is a Mathlib instance (`IsRealClosed ℝ`); the second is
Exercise 2.11, formalised in
`Azurite.BasuPollackRoy.Chapter2.Exercise_2_11`. This file defines the
underlying set `realAlgebraicNumbers` (with notation `ℝ_alg`) and a few
trivial closure lemmas.
-/

namespace Azurite.BPR

/-- **BPR p.38.** The set of *real algebraic numbers* `R_alg`:
    those `x : ℝ` satisfying some nonzero polynomial with integer coefficients.

    Formally: `IsAlgebraic ℤ x`, i.e., `∃ p : ℤ[X], p ≠ 0 ∧ aeval x p = 0`. -/
def realAlgebraicNumbers : Set ℝ :=
  {x : ℝ | IsAlgebraic ℤ x}

scoped notation "ℝ_alg" => realAlgebraicNumbers

/-- The zero element 0 is real algebraic, witnessed by the polynomial `X`. -/
theorem zero_mem_realAlgebraicNumbers : (0 : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_zero

/-- The element 1 is real algebraic, witnessed by the polynomial `X - 1`. -/
theorem one_mem_realAlgebraicNumbers : (1 : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_one

/-- Every integer is a real algebraic number. -/
theorem intCast_mem_realAlgebraicNumbers (n : ℤ) : (n : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_algebraMap n

end Azurite.BPR
