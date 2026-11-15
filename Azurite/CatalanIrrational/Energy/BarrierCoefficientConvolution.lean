/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/Energy/BarrierCoefficientConvolution.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Rat.Cast.Defs

namespace OAI

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def barrierCoeffConv (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2

theorem barrier_coeff_mul_eq_conv (p q : ℚ[X]) (a b : ℕ → ℚ)
    (hp : ∀ k, p.coeff k = a k) (hq : ∀ k, q.coeff k = b k) (n : ℕ) :
    (p * q).coeff n = barrierCoeffConv a b n := by
  rw [Polynomial.coeff_mul]
  unfold barrierCoeffConv
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hp, hq]

end InternalCatalan

end OAI
