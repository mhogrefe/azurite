/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_2.Proposition_8_14
import Azurite.BasuPollackRoy.Chapter8.Section8_3.SignedSubresultant

/-!
# BPR §8.3.4 Proposition 8.49: degree of signed subresultants

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4.

**Proposition 8.49.** If `P, Q` have degrees `p, q` and coefficients in `R[Y₁,…,Y_k]` of degree
`≤ d` in `Y₁,…,Y_k`, then `sResP_j(P,Q)` has degree at most `d(p+q-2j)` in `Y₁,…,Y_k`.

Proof (BPR): each coefficient (in `X`) of `sResP_j` is a determinant of a `(p+q-2j)×(p+q-2j)`
matrix whose entries are coefficients of `P, Q` (total degree `≤ d`), so Proposition 8.14 bounds
its total degree by `d(p+q-2j)`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

/-- A coefficient of `X^s · P` is a coefficient of `P` (or `0`), hence has total degree `≤ d`
    when `P`'s coefficients do. -/
theorem totalDegree_coeff_X_pow_mul {R : Type*} [CommRing R] {k : ℕ}
    {P : (MvPolynomial (Fin k) R)[X]} {d : ℕ}
    (hP : ∀ i, (P.coeff i).totalDegree ≤ d) (s c : ℕ) :
    ((X ^ s * P).coeff c).totalDegree ≤ d := by
  rw [mul_comm, Polynomial.coeff_mul_X_pow']
  split_ifs
  · exact hP _
  · simp

/-- **BPR Proposition 8.49 (degree of signed subresultants).**  With coefficients in
    `R[Y₁,…,Y_k]` of total degree `≤ d`, every coefficient (in `X`) of `sResP_j(P,Q)` has total
    degree at most `d·(p+q-2j)` in the `Y`'s. -/
theorem proposition_8_49 {R : Type*} [CommRing R] {k : ℕ}
    (P Q : (MvPolynomial (Fin k) R)[X]) {d : ℕ}
    (hP : ∀ i, (P.coeff i).totalDegree ≤ d) (hQ : ∀ i, (Q.coeff i).totalDegree ≤ d)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j ≤ Q.natDegree) (a : ℕ) :
    ((sResP P Q j).coeff a).totalDegree ≤ d * (P.natDegree + Q.natDegree - 2 * j) := by
  by_cases ha : a ≤ j
  · rw [sResP, ite_eq_left hjq,
      pdetRing_coeff _ (show a ≤ P.natDegree + Q.natDegree - j - (P.natDegree + Q.natDegree - 2 * j)
        by omega), pdetMinorRing]
    refine Azurite.BPR.proposition_8_14 _ (fun r c => ?_)
    rw [pdetMinorMatRing]
    by_cases hr : (r : ℕ) < Q.natDegree - j
    · simp only [hr, ite_true]; exact totalDegree_coeff_X_pow_mul hP _ _
    · simp only [hr, ite_false]; exact totalDegree_coeff_X_pow_mul hQ _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hjq)) (by omega))]
    simp

end Azurite.BPR.Chapter8
