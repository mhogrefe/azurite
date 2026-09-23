/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_2.Proposition_8_15
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_49

/-!
# BPR §8.3.4 Proposition 8.50: degree and bitsize of signed subresultants over `ℤ[Y]`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.4.

**Proposition 8.50.** If `P, Q` have degrees `p, q` and coefficients in `ℤ[Y₁,…,Y_k]` of degree
`≤ d` and integer bitsize `≤ τ`, then `sResP_j(P,Q)` has degree `≤ d(p+q-2j)` in the `Y`'s, and its
integer coefficients have bitsize `≤ (p+q-2j)(τ + bit(p+q-2j) + k·bit(d+1))`.

Proof (BPR): each coefficient (in `X`) of `sResP_j` is a determinant of a `(p+q-2j)×(p+q-2j)`
matrix whose entries are coefficients of `P, Q` (degree `≤ d`, bitsize `≤ τ`), so Proposition 8.15
bounds it.

The bitsize bound above is the one Proposition 8.15 gives directly.  BPR's stated form
`(τ + (k+1)·bit(p+q))(p+q-2j)` is a (looser) consequence valid when `d < p+q`: then
`bit(p+q-2j) ≤ bit(p+q)` and `bit(d+1) ≤ bit(p+q)`, so
`bit(p+q-2j) + k·bit(d+1) ≤ (k+1)·bit(p+q)`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

/-- An integer coefficient of `X^s · P` is one of `P` (or `0`), hence has bitsize `≤ τ`. -/
theorem int_size_coeff_coeff_X_pow_mul {k : ℕ} {P : Polynomial (MvPolynomial (Fin k) ℤ)} {τ : ℕ}
    (hP : ∀ i r, Int.size ((P.coeff i).coeff r) ≤ τ) (s c : ℕ) (r : Fin k →₀ ℕ) :
    Int.size (((Polynomial.X ^ s * P).coeff c).coeff r) ≤ τ := by
  rw [mul_comm, Polynomial.coeff_mul_X_pow']
  split_ifs
  · exact hP _ _
  · simp [Int.size]

/-- **BPR Proposition 8.50.**  Degree and integer-coefficient bitsize of `sResP_j(P,Q)` over
    `ℤ[Y₁,…,Y_k]`. -/
theorem proposition_8_50 {k : ℕ} (P Q : Polynomial (MvPolynomial (Fin k) ℤ)) {d τ : ℕ}
    (hPd : ∀ i, (P.coeff i).totalDegree ≤ d) (hQd : ∀ i, (Q.coeff i).totalDegree ≤ d)
    (hPτ : ∀ i r, Int.size ((P.coeff i).coeff r) ≤ τ)
    (hQτ : ∀ i r, Int.size ((Q.coeff i).coeff r) ≤ τ)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hjq : j ≤ Q.natDegree) (a : ℕ) :
    ((sResP P Q j).coeff a).totalDegree ≤ d * (P.natDegree + Q.natDegree - 2 * j)
      ∧ ∀ r, Int.size (((sResP P Q j).coeff a).coeff r)
          ≤ (P.natDegree + Q.natDegree - 2 * j)
              * (τ + Nat.size (P.natDegree + Q.natDegree - 2 * j) + k * Nat.size (d + 1)) := by
  refine ⟨proposition_8_49 P Q hPd hQd hpq hjq a, fun r => ?_⟩
  by_cases ha : a ≤ j
  · rw [sResP, ite_eq_left hjq,
      pdetRing_coeff _ (show a ≤ P.natDegree + Q.natDegree - j - (P.natDegree + Q.natDegree - 2 * j)
        by omega), pdetMinorRing]
    refine (proposition_8_15 _ (show 0 < P.natDegree + Q.natDegree - 2 * j by omega)
      (fun i' c => ?_) (fun i' c r' => ?_)).2 r
    · rw [pdetMinorMatRing]
      by_cases hr : (i' : ℕ) < Q.natDegree - j
      · simp only [hr, ite_true]; exact totalDegree_coeff_X_pow_mul hPd _ _
      · simp only [hr, ite_false]; exact totalDegree_coeff_X_pow_mul hQd _ _
    · rw [pdetMinorMatRing]
      by_cases hr : (i' : ℕ) < Q.natDegree - j
      · simp only [hr, ite_true]; exact int_size_coeff_coeff_X_pow_mul hPτ _ _ _
      · simp only [hr, ite_false]; exact int_size_coeff_coeff_X_pow_mul hQτ _ _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hjq)) (by omega))]
    simp [Int.size]

end Azurite.BPR.Chapter8
