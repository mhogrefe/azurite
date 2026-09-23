/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  BPR Algorithm 8.16 (Dodgson-Jordan-Bareiss): fraction-free determinant.

  At each step `k` of the elimination, an entry `b_{i, j}^{(k+1)}` is computed
  from level-`k` entries via the Sylvester-style recurrence

    b_{i,j}^{(k+1)} := (b_{k+1,k+1}^{(k)} · b_{i,j}^{(k)}
                       - b_{i,k+1}^{(k)} · b_{k+1,j}^{(k)}) /ₑ b_{k,k}^{(k-1)}   (8.9)

  with the convention `b_{0,0}^{(-1)} := 1`. After `n - 1` steps the
  bottom-right entry holds `b_{n,n}^{(n-1)}`, and the determinant is
  `(-1)^s · b_{n,n}^{(n-1)}` where `s` is the number of column swaps
  (equation (8.10)).

  **Fraction-free over a domain.** By BPR Proposition 8.20, the divisions
  performed in (8.9) are always exact when the entries of `M` lie in a
  domain `D`: each intermediate `b_{i,j}^{(k)}` is a determinant of a
  submatrix of `M` and so belongs to `D`. The implementation requires
  `[ExactDiv D]` (`Azurite/Algorithm/ExactDiv.lean`), which is satisfied by
  any field via the default instance and by integral domains for which a
  computable exact division has been provided (e.g., `AzInt`).
-/
import Azurite.AzMatrix.Bareiss
import Azurite.AzMatrix.Det
import Azurite.AzMatrix.RowEchelon
import Azurite.Algorithm.ExactDiv
import Azurite.AzInt.ExactDiv
import Azurite.AzInt.Instances
import Azurite.AzInt.Conversion
import Azurite.AzInt.ParsableElement
import Azurite.AzInt.ToString
import Azurite.AzPolynomial.ExactDiv
import Azurite.AzPolynomial.Equiv.ExactDiv
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.ParsableElement
import Azurite.AzMvPolynomial.ExactDivCommRing
import Azurite.AzMvPolynomial.Equiv.ExactDivCR
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.ParsableElement
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement
import Azurite.AzRat.Conversion

namespace Azurite

variable {D : Type _} {n : Nat}

/-! ### One step of Bareiss elimination (BPR equation 8.9) -/

/-- One Bareiss elimination step using (8.9). For row `i > k` and column
    `j > k`:

      `M'[i][j] := (M[k][k] · M[i][j] − M[i][k] · M[k][j]) /ₑ b_prev`,

    where `/ₑ` is exact division. Column `k` below the pivot is zeroed;
    rows `≤ k` and columns `< k` (which the algorithm's loop invariant
    keeps at zero below the diagonal) are unchanged. -/
def AzMatrix.bareissEliminate [CommRing D] [ExactDiv D]
    (M : AzMatrix D n n) (k : Fin n) (b_prev : D) : AzMatrix D n n :=
  AzMatrix.ofFn fun i j =>
    if i.val ≤ k.val then M.get i j
    else if j.val < k.val then M.get i j
    else if j = k then 0
    else ExactDiv.exactDiv
      (M.get k k * M.get i j - M.get i k * M.get k j) b_prev

/-! ### Recursive algorithm -/

/-- Recursive helper for `bareissDet`. At step `start`, look for a column
    pivot in row `start`; on `none` return `0` (early-abort, signaling
    `det = 0`); on a non-pivot index, swap columns (incrementing `s`); then
    apply one `bareissEliminate` step using `b_prev = b_{start, start}^{(start - 1)}`
    as the divisor, and recurse with the new divisor `M[start][start]`. -/
def AzMatrix.bareissAux [CommRing D] [DecidableEq D] [ExactDiv D]
    (M : AzMatrix D n n) (start : Nat) (s : Nat) (b_prev : D) : D :=
  if h : start + 1 < n then
    let kp : Fin n := ⟨start, by omega⟩
    match M.findPivot kp with
    | none => 0
    | some j =>
      if j = kp then
        AzMatrix.bareissAux (M.bareissEliminate kp b_prev) (start + 1) s
          (M.get kp kp)
      else
        let M' := M.swapCols kp j
        AzMatrix.bareissAux (M'.bareissEliminate kp b_prev) (start + 1) (s + 1)
          (M'.get kp kp)
  else
    if hn : 0 < n then
      (-1 : D) ^ s * M.get ⟨n - 1, by omega⟩ ⟨n - 1, by omega⟩
    else
      1
termination_by n - start

/-- **BPR Algorithm 8.16 (Dodgson-Jordan-Bareiss).** Determinant of `M`
    computed by the fraction-free Bareiss recurrence (8.9), with output
    formula (8.10):

      `det(M) = (-1)^s · b_{n, n}^{(n - 1)}`.

    Requires `[ExactDiv D]` because each step's division is guaranteed
    exact by BPR Proposition 8.20 — so the algorithm stays in the entry
    ring `D` without needing fractions. -/
def AzMatrix.bareissDet [CommRing D] [DecidableEq D] [ExactDiv D]
    (M : AzMatrix D n n) : D :=
  AzMatrix.bareissAux M 0 0 1

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- 2×2 over AzRat: det [[1, 2], [3, 4]] = 1·4 − 2·3 = −2.
#guard
  match (AzMatrix.parseStr "[1, 2; 3, 4]" : Option (AzMatrix AzRat 2 2)) with
  | some M => Azurite.AzRat.toString M.bareissDet == "-2"
  | none => False

-- 4×4 over AzRat matching the Gauss-based `gaussDet`.
#guard
  match (AzMatrix.parseStr "[2, 1, 1; 1, 3, 2; 1, 0, 0]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => Azurite.AzRat.toString M.bareissDet == "-1"
  | none => False

-- Identity over AzRat has determinant 1.
#guard Azurite.AzRat.toString ((1 : AzMatrix AzRat 4 4).bareissDet) == "1"

-- Singular matrix (rank-deficient): determinant 0.
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => Azurite.AzRat.toString M.bareissDet == "0"
  | none => False

-- Column-pivoting test: zero in the (0, 0) position forces a swap.
#guard
  match (AzMatrix.parseStr "[0, 1; 1, 0]" : Option (AzMatrix AzRat 2 2)) with
  | some M => Azurite.AzRat.toString M.bareissDet == "-1"
  | none => False

-- 4×4 — Bareiss agrees with Gauss-based `det`.
#guard
  match (AzMatrix.parseStr "[2, 1, 3, 4; 1, 0, 2, 1; 3, 2, 1, 0; 4, 1, 1, 2]" :
      Option (AzMatrix AzRat 4 4)) with
  | some M => Azurite.AzRat.toString M.bareissDet == Azurite.AzRat.toString M.gaussDet
  | none => False

/-! #### `bareissDet` over `AzInt` (fraction-free over a domain) -/

-- Identical 3×3 to the AzRat test above, but stays in `AzInt`.
#guard
  match (AzMatrix.parseStr "[2, 1, 1; 1, 3, 2; 1, 0, 0]" :
      Option (AzMatrix AzInt 3 3)) with
  | some M => Azurite.AzInt.toString M.bareissDet == "-1"
  | none => False

-- 4×4 over `AzInt` — fraction-free determinant. Cross-checked against the
-- AzRat Gauss-det computation on the same matrix.
#guard
  match
    ((AzMatrix.parseStr "[2, 1, 3, 4; 1, 0, 2, 1; 3, 2, 1, 0; 4, 1, 1, 2]" :
        Option (AzMatrix AzInt 4 4)),
     (AzMatrix.parseStr "[2, 1, 3, 4; 1, 0, 2, 1; 3, 2, 1, 0; 4, 1, 1, 2]" :
        Option (AzMatrix AzRat 4 4))) with
  | (some Mz, some Mq) =>
    Azurite.AzRat.toString Mz.bareissDet.toAzRat == Azurite.AzRat.toString Mq.gaussDet
  | _ => False

/-! #### `bareissDet` over `AzPolynomial AzInt`

This is the headline use case: a matrix whose entries are polynomials in
`AzInt[x]`. The `ExactDiv` chain is `ExactDiv AzInt → ExactDiv (AzPolynomial
AzInt)`, so `bareissDet` runs purely inside `AzInt[x]` — no fraction
field, no Mathlib detour. -/

-- det [[x, 1], [2, x]] = x² − 2 in AzInt[x].
#guard
  match (AzMatrix.parseStr "[x, 1; 2, x]" :
      Option (AzMatrix (AzPolynomial AzInt) 2 2)) with
  | some M => toString M.bareissDet = "x^2-2"
  | none => False

/-! #### `bareissDet` over `AzMvPolynomial 1 AzInt _` -/

-- Generic 2×2 with distinct entries in `AzMvPolynomial 4 AzInt .Degrevlex`,
-- yielding the symbolic determinant `x₀·x₃ − x₁·x₂` (printed in degrevlex
-- order). The `ExactDiv` chain `ExactDiv AzInt → ExactDiv (AzMvPolynomial 4
-- AzInt _)` gives `bareissDet` automatically — no fraction-field detour.
-- Variables are displayed and parsed using Unicode subscripts: `x₀`, `x₁`, …
#guard
  match (AzMatrix.parseStr "[x₀, x₁; x₂, x₃]" :
      Option (AzMatrix
        (AzMvPolynomial 4 AzInt MonomialOrder.Degrevlex) 2 2)) with
  | some M => toString M.bareissDet = "-x₁*x₂+x₀*x₃"
  | none => False

end Tests

end Azurite
