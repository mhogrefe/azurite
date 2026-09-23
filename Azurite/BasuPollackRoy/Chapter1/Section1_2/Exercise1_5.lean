/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain

/-!
# Exercise 1.5

Over a field $K$, if $Q \ne 0$, there exists a unique pair $(A, R)$ in
$K[X]^2$ such that $P = A Q + R$ and $\deg R < \deg Q$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- Exercise 1.5: If Q ≠ 0, there exists a unique pair (A, R) in K[X]²
    such that P = AQ + R and deg(R) < deg(Q). -/
theorem exercise_1_5 (P Q : K[X]) (hQ : Q ≠ 0) :
    ∃! p : K[X] × K[X],
      P = p.1 * Q + p.2 ∧ p.2.degree < Q.degree := by
  -- p.1 = A (quotient), p.2 = R (remainder)
  have hmod : Q * (P / Q) + P % Q = P := EuclideanDomain.div_add_mod P Q
  -- Existence
  refine ⟨(P / Q, P % Q), ⟨?_, Polynomial.degree_mod_lt P hQ⟩, ?_⟩
  · show P = P / Q * Q + P % Q
    rw [mul_comm]; exact hmod.symm
  -- Uniqueness
  · rintro ⟨A, R⟩ ⟨hAR : P = A * Q + R, hDeg : R.degree < Q.degree⟩
    have hEq : A * Q + R = P / Q * Q + P % Q :=
      hAR.symm.trans (by rw [mul_comm]; exact hmod.symm)
    suffices hA : A = P / Q from
      Prod.ext hA (add_left_cancel (show P / Q * Q + R = P / Q * Q + P % Q from
        hA ▸ hEq))
    by_contra hne
    have hsub : (A - P / Q) * Q = P % Q - R := by
      have : A * Q - P / Q * Q = P % Q - R :=
        calc A * Q - P / Q * Q
            = (A * Q + R) - R - P / Q * Q := by ring
          _ = (P / Q * Q + P % Q) - R - P / Q * Q := by rw [hEq]
          _ = P % Q - R := by ring
      rwa [← sub_mul] at this
    have hDegSub : (P % Q - R).degree < Q.degree :=
      lt_of_le_of_lt (degree_sub_le _ _)
        (max_lt (Polynomial.degree_mod_lt P hQ) hDeg)
    rw [← hsub] at hDegSub
    have hDegProd : Q.degree ≤ ((A - P / Q) * Q).degree := by
      rw [degree_mul]
      have h1 := degree_eq_bot.not.mpr (sub_ne_zero.mpr hne)
      cases hd : (A - P / Q).degree with
      | bot => exact absurd hd h1
      | coe n =>
        cases hq : Q.degree with
        | bot => exact absurd (degree_eq_bot.mp hq) hQ
        | coe m => exact_mod_cast Nat.le_add_left m n
    exact absurd hDegSub (not_lt.mpr hDegProd)

end Azurite.BPR
