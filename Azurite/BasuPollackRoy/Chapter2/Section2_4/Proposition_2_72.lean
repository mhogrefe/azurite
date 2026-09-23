/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Notation_2_71

/-!
# BPR Proposition 2.72: `Mat(A, Σ) = Mₛ`

Let `𝒬` be a finite set of `s` polynomials (index type `Fin s`), with
`A = {0,1,2}^𝒬` and `Σ = {0,1,-1}^𝒬` ordered lexicographically. Then the
matrix of signs `Mat(A, Σ)` equals `Mₛ` (Notation 2.71).

The lex orderings are formalized by the enumerations `expFn s` and
`signFn s`, which list the elements of `A` and `Σ` (each indexed by
`Fin (3^s)`). Recursively, the `r`-th element extends the
`(finProdFinEquiv.symm r).1`-th element on `Fin s` by appending, at the
last coordinate, the single exponent/sign chosen by
`(finProdFinEquiv.symm r).2` — exactly the `Mₛ ⊗ M₁` block structure, with
the last (`s`-th) polynomial least significant.

The proof is by induction on `s`. The base `s = 0` is the empty product
`1`. The step uses `M_{s+1} = Mₛ ⊗ M₁`: the `(i, j)`-entry splits as an
`Mₛ`-entry times an `M₁`-entry, matching the split of the order-`(s+1)`
product `σ_j^{α_i} = ∏_k σ_j(k)^{α_i(k)}` into its `Fin s` part and its
last coordinate (`Fin.prod_univ_castSucc`). The `s = 1` instance is the
single-polynomial computation of `SinglePolynomialMatrix` (BPR's Equation
(2.6)).
-/

namespace Azurite.BPR

open Polynomial

/-- The lex-ordered enumeration of `A = {0,1,2}^{Fin s}` (index `0` most
significant): `expFn s r` is the `r`-th exponent assignment. The `(s+1)`
case appends, at the last coordinate, the exponent `0`/`1`/`2` chosen by
`(finProdFinEquiv.symm r).2`. -/
def expFn : (s : Nat) → Fin (3 ^ s) → Fin s → ℕ
  | 0 => fun _ => Fin.elim0
  | s + 1 => fun r =>
      Fin.snoc (expFn s ((@finProdFinEquiv (3 ^ s) 3).symm r).1)
        (((@finProdFinEquiv (3 ^ s) 3).symm r).2 : ℕ)

/-- The lex-ordered enumeration of `Σ = {0,1,-1}^{Fin s}` (index `0` most
significant, sign order `0 ≺ 1 ≺ -1`): `signFn s r` is the `r`-th sign
condition. The `(s+1)` case appends, at the last coordinate, the sign
`![0,1,-1]` chosen by `(finProdFinEquiv.symm r).2`. -/
def signFn : (s : Nat) → Fin (3 ^ s) → Fin s → SignType
  | 0 => fun _ => Fin.elim0
  | s + 1 => fun r =>
      Fin.snoc (signFn s ((@finProdFinEquiv (3 ^ s) 3).symm r).1)
        (![0, 1, -1] ((@finProdFinEquiv (3 ^ s) 3).symm r).2)

/-- The `(a, b)`-entry of the single-polynomial matrix `M₁` is
`(sign b)^a` (BPR's Equation (2.6), the `s = 1` base). -/
theorem exampleM_toFn (a b : Fin 3) : exampleM.toFn a b = (![0, 1, -1] b) ^ (a : ℕ) := by
  fin_cases a <;> fin_cases b <;> decide

/-- **Entrywise form of BPR Proposition 2.72.** The `(i, j)`-entry of `Mₛ`
is `σ_j^{α_i} = ∏_k σ_j(k)^{α_i(k)}`, the matrix-of-signs entry. Proved by
induction on `s` using `M_{s+1} = Mₛ ⊗ M₁`. -/
theorem signMatrix_toFn_eq_pow (s : Nat) : ∀ (i j : Fin (3 ^ s)),
    (signMatrix s).toFn i j = SignCondition.pow (signFn s j) (expFn s i) := by
  induction s with
  | zero =>
    intro i j
    simp only [SignCondition.pow, Finset.univ_eq_empty, Finset.prod_empty]
    fin_cases i; fin_cases j; decide
  | succ s ih =>
    intro i j
    show ((signMatrix s).kronecker exampleM).toFn i j = _
    erw [AzMatrix.toFn_kronecker_apply]
    rw [ih, exampleM_toFn]
    simp only [SignCondition.pow, signFn, expFn, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last]

/-- The lex-ordered list `A = {0,1,2}^{Fin s}`. -/
def expList (s : Nat) : List (Fin s → ℕ) := List.ofFn (expFn s)

/-- The lex-ordered list `Σ = {0,1,-1}^{Fin s}`. -/
def signList (s : Nat) : List (SignCondition (Fin s)) := List.ofFn (signFn s)

/-- **BPR Proposition 2.72.** `Mat(A, Σ) = Mₛ` for `A = {0,1,2}^{Fin s}`
and `Σ = {0,1,-1}^{Fin s}` in lexicographic order. The `submatrix` by
`Fin.cast` is the (identity) relabeling of `Mₛ`'s `Fin (3^s)` indices to
the list-length indices `Fin |A|`, `Fin |Σ|` of `matrixOfSigns`. -/
theorem proposition_2_72 (s : Nat) :
    matrixOfSigns (expList s) (signList s)
      = Matrix.submatrix (Matrix.of (signMatrix s).toFn)
          (Fin.cast (by simp [expList])) (Fin.cast (by simp [signList])) := by
  ext i j
  rw [matrixOfSigns_apply, Matrix.submatrix_apply, Matrix.of_apply,
    signMatrix_toFn_eq_pow]
  exact congrArg₂ SignCondition.pow (List.get_ofFn (signFn s) j)
    (List.get_ofFn (expFn s) i)

end Azurite.BPR
