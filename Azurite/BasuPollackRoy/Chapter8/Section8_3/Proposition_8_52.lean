/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.StructureTheorem

/-!
# BPR §8.3.5 Proposition 8.52: specialization of signed subresultants

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, Springer 2006, §8.3.5.

**Proposition 8.52.** Let `f : D → D'` be a ring homomorphism (also denoting the induced
homomorphism `D[X] → D'[X]`).  If `deg(f(P)) = deg(P)` and `deg(f(Q)) = deg(Q)`, then for all
`j ≤ p`,
`sResP_j(f(P), f(Q)) = f(sResP_j(P, Q))`.

The signed subresultant is a polynomial determinant — multilinear in its rows — whose matrix shape
is determined by `deg(P)` and `deg(Q)`.  Under the degree-preservation hypothesis the shape is
unchanged, and the determinant commutes with `f` (`pdetRing_map`); the boundary conventions
(`sResP_p = P`, `sResP_{p-1} = Q`, `0` in the gap) are likewise preserved by any ring
homomorphism, which gives the result.

We also formalize the **degenerate case** (the "Note" after Proposition 8.52): if instead
`deg(f(P)) = deg(P)` but `deg(f(Q)) < deg(Q)`, then for `j ≤ deg(f(Q))`,
`f(sResP_j(P, Q)) = lcof(f(P))^{deg(Q) - deg(f(Q))} · sResP_j(f(P), f(Q))`,
proved with Lemma 8.31 (triangular reduction `pdetRing_triangular`): collapsing `f` lowers the
`Q`-block degrees, and the top `deg(Q) - deg(f(Q))` rows of `f(P)`-shifts triangulate out, each
contributing a factor `lcof(f(P))`, leaving exactly the determinant of `sResP_j(f(P), f(Q))`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {D E : Type*} [CommRing D] [CommRing E]

/-- **BPR Proposition 8.52 (specialization of signed subresultants).**  A ring homomorphism `f`
    commutes with `sResP` whenever it preserves the degrees of both polynomials. -/
theorem proposition_8_52 (f : D →+* E) (P Q : D[X])
    (hP : (P.map f).natDegree = P.natDegree) (hQ : (Q.map f).natDegree = Q.natDegree) (j : ℕ) :
    sResP (P.map f) (Q.map f) j = (sResP P Q j).map f := by
  rw [sResP, sResP, hP, hQ]
  by_cases hjq : j ≤ Q.natDegree
  · rw [ite_eq_left hjq, ite_eq_left hjq, ← pdetRing_map f]
    congr 1
    funext r
    by_cases hr : (r : ℕ) < Q.natDegree - j
    · simp only [hr, ite_true, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    · simp only [hr, ite_false, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  · rw [ite_eq_right hjq, ite_eq_right hjq]
    by_cases hjp : j = P.natDegree
    · rw [ite_eq_left hjp, ite_eq_left hjp]
    · rw [ite_eq_right hjp, ite_eq_right hjp]
      by_cases hjp1 : j = P.natDegree - 1
      · rw [ite_eq_left hjp1, ite_eq_left hjp1]
      · rw [ite_eq_right hjp1, ite_eq_right hjp1, Polynomial.map_zero]

/-- **BPR Proposition 8.52, degenerate case (the "Note").**  If `f` preserves the degree of `P`
    but strictly lowers the degree of `Q`, then for `j ≤ deg(f(Q))`,
    `f(sResP_j(P, Q)) = lcof(f(P))^{deg(Q) - deg(f(Q))} · sResP_j(f(P), f(Q))`.  Proved with the
    triangular reduction of Lemma 8.31 (`pdetRing_triangular`). -/
theorem proposition_8_52_degenerate (f : D →+* E) (P Q : D[X])
    (hpq : Q.natDegree < P.natDegree) (hP : (P.map f).natDegree = P.natDegree)
    (hQ : (Q.map f).natDegree < Q.natDegree) {j : ℕ} (hj : j ≤ (Q.map f).natDegree) :
    (sResP P Q j).map f
      = C ((P.map f).leadingCoeff ^ (Q.natDegree - (Q.map f).natDegree))
        * sResP (P.map f) (Q.map f) j := by
  have hjq : j ≤ Q.natDegree := le_trans hj (le_of_lt hQ)
  -- coefficient-vanishing and leading-coefficient helpers for the shifted rows
  have hvanP : ∀ k j' : ℕ, P.natDegree + k < j' → (X ^ k * (P.map f)).coeff j' = 0 := by
    intro k j' hjk
    rw [show j' = (j' - k) + k from by omega, Polynomial.coeff_X_pow_mul]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP]; omega)
  have hvanQ : ∀ k j' : ℕ, (Q.map f).natDegree + k < j' → (X ^ k * (Q.map f)).coeff j' = 0 := by
    intro k j' hjk
    rw [show j' = (j' - k) + k from by omega, Polynomial.coeff_X_pow_mul]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hleadP : ∀ k : ℕ, (X ^ k * (P.map f)).coeff (P.natDegree + k) = (P.map f).leadingCoeff := by
    intro k; rw [Polynomial.coeff_X_pow_mul, Polynomial.leadingCoeff, hP]
  -- unfold the left side to a polynomial determinant of the mapped rows
  rw [sResP, ite_eq_left hjq, ← pdetRing_map f]
  set R : Fin (P.natDegree + Q.natDegree - 2 * j) → E[X] :=
    fun r => (if (r : ℕ) < Q.natDegree - j then X ^ (Q.natDegree - j - 1 - (r : ℕ)) * P
      else X ^ ((r : ℕ) - (Q.natDegree - j)) * Q).map f with hR
  -- apply the triangular reduction (Lemma 8.31) with `ℓ = q - q'`
  have hℓm : Q.natDegree - (Q.map f).natDegree < P.natDegree + Q.natDegree - 2 * j := by omega
  have hmn : P.natDegree + Q.natDegree - 2 * j ≤ P.natDegree + Q.natDegree - j := by omega
  have hdeg1 : ∀ r : Fin (P.natDegree + Q.natDegree - 2 * j),
      (r : ℕ) < Q.natDegree - (Q.map f).natDegree →
      ∀ j', P.natDegree + Q.natDegree - j - 1 - (r : ℕ) < j' → (R r).coeff j' = 0 := by
    intro r hr j' hj'
    simp only [hR, ite_eq_left (show (r : ℕ) < Q.natDegree - j by omega),
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    exact hvanP _ _ (by omega)
  have hdeg2 : ∀ r : Fin (P.natDegree + Q.natDegree - 2 * j),
      Q.natDegree - (Q.map f).natDegree ≤ (r : ℕ) →
      ∀ j', P.natDegree + Q.natDegree - j - 1 - (Q.natDegree - (Q.map f).natDegree) < j' →
        (R r).coeff j' = 0 := by
    intro r hr j' hj'
    have hrm := r.isLt
    simp only [hR]
    by_cases hrc : (r : ℕ) < Q.natDegree - j
    · rw [ite_eq_left hrc, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
      exact hvanP _ _ (by omega)
    · rw [ite_eq_right hrc, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
      exact hvanQ _ _ (by omega)
  rw [pdetRing_triangular hℓm hmn R hdeg1 hdeg2]
  congr 1
  · -- the product of leading coefficients is `lcof(f(P))^{q - q'}`
    congr 1
    rw [show ((P.map f).leadingCoeff ^ (Q.natDegree - (Q.map f).natDegree))
        = ∏ _i : Fin (Q.natDegree - (Q.map f).natDegree), (P.map f).leadingCoeff from by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    apply Finset.prod_congr rfl
    intro i _
    have hil := i.isLt
    simp only [hR, ite_eq_left (show (i : ℕ) < Q.natDegree - j by omega),
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      show P.natDegree + Q.natDegree - j - 1 - (i : ℕ)
        = P.natDegree + (Q.natDegree - j - 1 - (i : ℕ)) from by omega]
    exact hleadP _
  · -- the remaining determinant is `sResP_j(f(P), f(Q))`
    rw [sResP, ite_eq_left hj,
      show P.natDegree + Q.natDegree - j - (Q.natDegree - (Q.map f).natDegree)
        = (P.map f).natDegree + (Q.map f).natDegree - j from by rw [hP]; omega]
    refine pdetRing_congr_cast (by rw [hP]; omega) _ _ (fun i => ?_)
    have hii := i.isLt
    simp only [hR, Fin.val_cast]
    by_cases hc : (i : ℕ) < (Q.map f).natDegree - j
    · rw [ite_eq_left (show Q.natDegree - (Q.map f).natDegree + (i : ℕ) < Q.natDegree - j by omega),
        ite_eq_left hc, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        show Q.natDegree - j - 1 - (Q.natDegree - (Q.map f).natDegree + (i : ℕ))
          = (Q.map f).natDegree - j - 1 - (i : ℕ) from by omega]
    · rw [ite_eq_right (show ¬ Q.natDegree - (Q.map f).natDegree + (i : ℕ) < Q.natDegree - j by omega),
        ite_eq_right hc, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        show Q.natDegree - (Q.map f).natDegree + (i : ℕ) - (Q.natDegree - j)
          = (i : ℕ) - ((Q.map f).natDegree - j) from by omega]

end Azurite.BPR.Chapter8
