/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # BPR Section 2.1 — Root multiplicity and Lemma 2.2

**Definition (BPR p.33).** Let `x ∈ K` and `P ∈ K[X]`. The
**multiplicity** of `x` as a root of `P` is the natural number `µ`
such that there exists `Q ∈ K[X]` with `P = (X − x)^µ · Q(X)` and
`Q(x) ≠ 0`. If `x` is not a root of `P`, the multiplicity is `0`.

Mathlib already provides:
```
def Polynomial.rootMultiplicity (a : R) (p : R[X]) : ℕ
```
defined via `multiplicity (X - C a) p`. Key matching theorems:
- `Polynomial.pow_rootMultiplicity_dvd`
- `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`
- `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`

**Lemma 2.2 (BPR p.33).** Let `K` be a field of characteristic zero.
The element `x ∈ K` is a root of `P ∈ K[X]` of multiplicity `µ` iff
`P^{(µ)}(x) ≠ 0` and `P^{(µ−1)}(x) = ⋯ = P′(x) = P(x) = 0`.

Proved via Mathlib's `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative`
and `Polynomial.eval_iterate_derivative_rootMultiplicity`.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- **BPR Definition (Root Multiplicity).**
    `IsRootMultiplicity x P μ` holds when there exists Q ∈ K[X] such that
    P = (X − x)^μ · Q and Q(x) ≠ 0. -/
def IsRootMultiplicity (x : K) (P : K[X]) (μ : ℕ) : Prop :=
  ∃ Q : K[X], P = (X - C x) ^ μ * Q ∧ Q.eval x ≠ 0

/-- **BPR Lemma 2.2.** x is a root of P of multiplicity μ iff
    P(x) = P'(x) = ⋯ = P^{(μ−1)}(x) = 0 and P^{(μ)}(x) ≠ 0. -/
theorem lemma_2_2 (P : K[X]) (t : K) (hP : P ≠ 0) (μ : ℕ) :
    μ = rootMultiplicity t P ↔
      (∀ i < μ, (derivative^[i] P).IsRoot t) ∧
      ¬(derivative^[μ] P).IsRoot t := by
  constructor
  · -- forward: μ = rootMultiplicity → derivatives vanish below, nonzero at μ
    rintro rfl
    exact ⟨
      fun i hi => (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).mp (by omega) i le_rfl,
      by rw [Polynomial.IsRoot, Polynomial.eval_iterate_derivative_rootMultiplicity]
         exact smul_ne_zero_iff.mpr
           ⟨Nat.cast_ne_zero.mpr (rootMultiplicity t P).factorial_ne_zero,
            eval_divByMonic_pow_rootMultiplicity_ne_zero t hP⟩⟩
  · -- backward: conditions → μ = rootMultiplicity
    rintro ⟨hvanish, hnonzero⟩
    apply le_antisymm
    · -- μ ≤ rootMultiplicity: if not, derivative^[rootMultiplicity] vanishes, contradiction
      by_contra h; push Not at h
      have hne : ¬(derivative^[rootMultiplicity t P] P).IsRoot t := by
        rw [Polynomial.IsRoot, Polynomial.eval_iterate_derivative_rootMultiplicity]
        exact smul_ne_zero_iff.mpr
          ⟨Nat.cast_ne_zero.mpr (rootMultiplicity t P).factorial_ne_zero,
           eval_divByMonic_pow_rootMultiplicity_ne_zero t hP⟩
      exact hne (hvanish _ h)
    · -- rootMultiplicity ≤ μ: if not, derivative^[μ] vanishes, contradiction
      by_contra h; push Not at h
      exact hnonzero
        ((Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).mp h μ le_rfl)

end Azurite.BPR
