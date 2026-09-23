/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The single-polynomial case of BPR Proposition 2.68

When `𝒬 = {Q}` (index type `Fin 1`), `A = {0,1,2}^𝒬` and
`Σ = {0,1,-1}^𝒬`, the matrix of signs is the `3 × 3` matrix

`!![1, 1, 1; 0, 1, -1; 0, 1, 1]`,

so the conclusion of Proposition 2.68 reads

`!![1,1,1; 0,1,-1; 0,1,1] · (c(Q=0,Z), c(Q>0,Z), c(Q<0,Z)) = (TaQ(1,P), TaQ(Q,P), TaQ(Q²,P))`.

For a single polynomial every root realizes one of the three sign
conditions `0, 1, -1`, so the covering hypothesis of Proposition 2.68 is
automatic and the equation holds with no extra hypothesis. (Read row by
row, this is exactly Proposition 2.65.)
-/

namespace Azurite.BPR

open Polynomial
open scoped Matrix

/-- The single-polynomial exponent list `{0,1,2}` (lex-ordered). -/
def singleExponents : List (Fin 1 → ℕ) := [![0], ![1], ![2]]

/-- The single-polynomial sign conditions `{0,1,-1}` in BPR order
(`0 ≺ 1 ≺ -1`). -/
def singleSignConditions : List (SignCondition (Fin 1)) := [![0], ![1], ![-1]]

/-- The `3 × 3` matrix of signs for a single polynomial. -/
example :
    matrixOfSigns singleExponents singleSignConditions =
      !![ 1, 1, 1; 0, 1, -1; 0, 1, 1] := by
  ext i j
  simp only [matrixOfSigns, singleExponents, singleSignConditions,
    SignCondition.pow, Fin.prod_univ_one]
  fin_cases i <;> fin_cases j <;> decide

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [IsStrictOrderedRing R] in
/-- For a single polynomial the three sign conditions `0, 1, -1` cover the
zero set: every root realizes one of them. -/
theorem singleSignConditions_cover (P Q : R[X]) :
    ∀ x, P.IsRoot x →
      (fun _ : Fin 1 => SignType.sign (Q.eval x)) ∈ singleSignConditions := by
  intro x _
  generalize SignType.sign (Q.eval x) = s
  fin_cases s <;> decide

/-- **Single-polynomial case of BPR Proposition 2.68.** With `𝒬 = {Q}`,
`A = {0,1,2}^𝒬`, `Σ = {0,1,-1}^𝒬`, the conclusion of Proposition 2.68 is
the `3 × 3` system

`!![1,1,1; 0,1,-1; 0,1,1] · (c(Q=0,Z), c(Q>0,Z), c(Q<0,Z)) = (TaQ(1,P), TaQ(Q,P), TaQ(Q²,P))`,

holding unconditionally (the covering hypothesis is automatic). Reading it
row by row recovers Proposition 2.65. -/
theorem proposition_2_68_single (P Q : R[X]) :
    (!![(1 : ℤ), 1, 1; 0, 1, -1; 0, 1, 1]) *ᵥ
        ![ ((SignCondition.realizationOverFinset ![0] P (fun _ => Q)).card : ℤ),
           ((SignCondition.realizationOverFinset ![1] P (fun _ => Q)).card : ℤ),
           ((SignCondition.realizationOverFinset ![-1] P (fun _ => Q)).card : ℤ) ]
      = ![tarskiQuery 1 P, tarskiQuery Q P, tarskiQuery (Q ^ 2) P] := by
  have h := proposition_2_68 P (fun _ => Q) singleExponents singleSignConditions
    (by decide) (singleSignConditions_cover P Q)
  have hM : (fun i j => ((matrixOfSigns singleExponents singleSignConditions i j : SignType) : ℤ))
      = !![(1 : ℤ), 1, 1; 0, 1, -1; 0, 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> decide
  have hv : (fun j => (((singleSignConditions.get j).realizationOverFinset P (fun _ => Q)).card : ℤ))
      = ![ ((SignCondition.realizationOverFinset ![0] P (fun _ => Q)).card : ℤ),
           ((SignCondition.realizationOverFinset ![1] P (fun _ => Q)).card : ℤ),
           ((SignCondition.realizationOverFinset ![-1] P (fun _ => Q)).card : ℤ) ] := by
    funext j; fin_cases j <;> rfl
  have hr : (fun i => tarskiQuery (familyPow (fun _ => Q) (singleExponents.get i)) P)
      = ![tarskiQuery 1 P, tarskiQuery Q P, tarskiQuery (Q ^ 2) P] := by
    funext i
    fin_cases i <;>
      simp [singleExponents, familyPow]
  rw [hM, hv] at h
  exact h.trans hr

end Azurite.BPR
