/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMatrix.CharPoly
import Azurite.AzMatrix.Parse
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_32
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement
import Azurite.BasuPollackRoy.Chapter8.Section8_2.Proposition_8_24
import Azurite.AzMatrix.Equiv.CharPoly
import Azurite.AzPolynomial.Equiv.Add

/-!
# BPR §8.2.4 Algorithm 8.18: Signature Through Descartes

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.2.4.

**Algorithm 8.18 (Signature Through Descartes).**
* **Structure:** an ordered integral domain `D`.
* **Input:** an `n × n` symmetric matrix `M = [m_{i,j}]` with coefficients in `D`.
* **Output:** the signature of the quadratic form associated to `M`.
* **Procedure:** compute the characteristic polynomial
  `CharPol(M) = det(X·Idₙ − M) = Xⁿ + a_{n−1}Xⁿ⁻¹ + ⋯ + a₀` using Algorithm 8.17,
  and output `Var(1, a_{n−1}, …, a₀) − Var((−1)ⁿ, (−1)ⁿ⁻¹a_{n−1}, …, a₀)`.

This is the computable counterpart of Proposition 8.24
(`Azurite.BPR.Chapter4.proposition_8_24`). The characteristic polynomial is
`Azurite.AzMatrix.charPoly` (Algorithm 8.17), which divides by `1, …, n` in the
Newton-sum recovery, so the computable structure here is an ordered **field**
(e.g. `AzRat`) rather than a bare ordered integral domain; an integer symmetric
matrix is handled by casting its entries into `AzRat`.

The two sign-variation counts are `Azurite.BPR.Var` (BPR Notation 2.32). The
output is an integer (the difference of two counts), which can be negative.
-/

namespace Azurite.AzMatrix

open Azurite.BPR

variable {n : ℕ}

/-- **BPR Algorithm 8.18 (Signature Through Descartes).** The signature of the
    quadratic form of the symmetric matrix `M`, computed from the sign variations
    of the coefficient sequences of `CharPol(M)` and `CharPol(M)(−X)`.

    With `CharPol(M) = Xⁿ + a_{n−1}Xⁿ⁻¹ + ⋯ + a₀`, this returns
    `Var(1, a_{n−1}, …, a₀) − Var((−1)ⁿ, (−1)ⁿ⁻¹a_{n−1}, …, a₀)`, where the lists
    are written in decreasing degree exactly as in BPR. The coefficient
    `aᵢ = CharPol(M).coeff i` is read off `charPoly` (Algorithm 8.17). -/
def signature {A : Type _} [Field A] [LinearOrder A] (M : AzMatrix A n n) : ℤ :=
  let p := M.charPoly
  -- Degrees `n, n−1, …, 0`, so the coefficient lists are in decreasing degree.
  let degs : List ℕ := (List.range (n + 1)).reverse
  let L₁ : List A := degs.map (fun i => p.coeff i)
  let L₂ : List A := degs.map (fun i => (-1 : A) ^ i * p.coeff i)
  (Azurite.BPR.Var L₁ : ℤ) - (Azurite.BPR.Var L₂ : ℤ)

/-! ## Worked examples (over `AzRat`)

`charPoly` requires a field, so the tests use `AzMatrix AzRat`. The expected
output is `#positive eigenvalues − #negative eigenvalues`. -/

section Tests

-- `diag(1, 2, 3)`: three positive eigenvalues, signature `3`.
#guard (AzMatrix.parseStr "[1, 0, 0; 0, 2, 0; 0, 0, 3]" :
  Option (AzMatrix AzRat 3 3)).map (·.signature) == some (3 : ℤ)

-- `[[2, 1], [1, 2]]`: eigenvalues `3, 1`, signature `2`.
#guard (AzMatrix.parseStr "[2, 1; 1, 2]" :
  Option (AzMatrix AzRat 2 2)).map (·.signature) == some (2 : ℤ)

-- `[[0, 1], [1, 0]]`: eigenvalues `1, −1`, signature `0`.
#guard (AzMatrix.parseStr "[0, 1; 1, 0]" :
  Option (AzMatrix AzRat 2 2)).map (·.signature) == some (0 : ℤ)

-- `diag(1, 1, −1)`: two positive, one negative eigenvalue, signature `1`.
#guard (AzMatrix.parseStr "[1, 0, 0; 0, 1, 0; 0, 0, -1]" :
  Option (AzMatrix AzRat 3 3)).map (·.signature) == some (1 : ℤ)

-- `diag(−1, −2, −3)`: three negative eigenvalues, signature `−3`.
#guard (AzMatrix.parseStr "[-1, 0, 0; 0, -2, 0; 0, 0, -3]" :
  Option (AzMatrix AzRat 3 3)).map (·.signature) == some (-3 : ℤ)

-- The `2 × 2` identity: signature `2`.
#guard (1 : AzMatrix AzRat 2 2).signature == (2 : ℤ)

end Tests

/-! ## Correctness

`signature` computes exactly the signature of Proposition 8.24
(`Azurite.BPR.Chapter4.proposition_8_24`): the sign-variation counts of the
two coefficient lists (in decreasing degree) coincide with `varPoly` of the
characteristic polynomial and of its `(−X)`-substitution, by reversal-invariance
of `Var` (`Azurite.BPR.Var_reverse`) and the coefficient bridge
`AzPolynomial.coeff_toPoly` ∘ `toPoly_charPoly`. -/

open Polynomial in
/-- **Correctness of Algorithm 8.18.** For a symmetric matrix over a real closed
    field, `signature` equals the signature `Sign` of the associated quadratic
    form (Proposition 8.24). -/
theorem signature_eq_Sign {A : Type _} [Field A] [LinearOrder A] [IsStrictOrderedRing A]
    [IsRealClosed A] (M : AzMatrix A n n) (hM : (toMat M).IsSymm) :
    M.signature = Azurite.BPR.Chapter4.Sign (Azurite.BPR.Chapter4.quadraticForm (toMat M)) := by
  classical
  set P := (toMat M).charpoly with hP
  -- Coefficient bridge: `charPoly`'s coefficients agree with Mathlib's `charpoly`.
  have hcoeff : ∀ i, M.charPoly.coeff i = P.coeff i := by
    intro i
    rw [hP, ← toPoly_charPoly M, Azurite.AzPolynomial.coeff_toPoly]
  have hdeg : P.natDegree = n := by
    rw [hP, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- The `(−X)`-substitution: coefficient of `Xⁱ` is `(−1)ⁱ aᵢ`.
  have hQcoeff : ∀ i, (P.comp (-X)).coeff i = (-1) ^ i * P.coeff i := by
    intro i
    rw [show (-X : A[X]) = C (-1) * X by rw [map_neg, map_one, neg_one_mul],
      comp_C_mul_X_coeff, mul_comm]
  have hQdeg : (P.comp (-X)).natDegree = n := by
    rw [Polynomial.natDegree_comp]; simp [hdeg]
  -- A `Var` of a decreasing-degree coefficient list equals `varPoly`.
  have varVar : ∀ (Q : A[X]) (f : ℕ → A), Q.natDegree = n → (∀ i, f i = Q.coeff i) →
      Azurite.BPR.Var ((List.range (n + 1)).reverse.map f) = Azurite.BPR.varPoly Q := by
    intro Q f hQn hf
    have hlist : (List.range (n + 1)).reverse.map f
        = ((List.range (Q.natDegree + 1)).map Q.coeff).reverse := by
      rw [List.map_reverse, hQn]
      congr 1
      exact List.map_congr_left (fun i _ => hf i)
    rw [hlist, Azurite.BPR.Var_reverse]
    rfl
  -- Assemble via Proposition 8.24.
  rw [Azurite.BPR.Chapter4.proposition_8_24 (toMat M) hM]
  dsimp only [signature]
  rw [varVar P (fun i => M.charPoly.coeff i) hdeg hcoeff,
      varVar (P.comp (-X)) (fun i => (-1 : A) ^ i * M.charPoly.coeff i) hQdeg
        (fun i => by rw [hQcoeff i, hcoeff i])]

end Azurite.AzMatrix
