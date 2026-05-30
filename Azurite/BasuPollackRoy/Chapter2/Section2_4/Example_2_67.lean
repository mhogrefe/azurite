import Azurite.BasuPollackRoy.Chapter2.Section2_4.Definition_2_66
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# BPR Example 2.67: the `9 × 9` matrix of signs for two polynomials

For `𝒬 = {Q₁, Q₂}` (index type `Fin 2`, with `0 ↦ Q₁`, `1 ↦ Q₂`), take
`A = {0,1,2}^𝒬` and `Σ = {0,1,-1}^𝒬`, both in BPR lexicographic order
(`Q₁` most significant; sign order `0 ≺ 1 ≺ -1`). Then `𝒬^A` is the list

`1, Q₂, Q₂², Q₁, Q₁Q₂, Q₁Q₂², Q₁², Q₁²Q₂, Q₁²Q₂²`,

and `Σ` is the nine sign conditions in the order
`(=,=), (=,>), (=,<), (>,=), (>,>), (>,<), (<,=), (<,>), (<,<)`.

This file pins down `A` and `Σ` as those lex-ordered lists and verifies
that `matrixOfSigns A Σ` is the exact `9 × 9` matrix of BPR Example 2.67
(by kernel `decide` after reducing the two-factor products) — a check
both of `matrixOfSigns` (Definition~2.66) and of the prescribed orders.
-/

namespace Azurite.BPR

open Polynomial

/-- The nine exponent assignments `{0,1,2}^{Fin 2}` in lexicographic order
(`Q₁ = `index `0` most significant), matching `𝒬^A`. -/
def exampleExponents : List (Fin 2 → ℕ) :=
  [![0, 0], ![0, 1], ![0, 2], ![1, 0], ![1, 1], ![1, 2], ![2, 0], ![2, 1], ![2, 2]]

/-- The nine sign conditions `{0,1,-1}^{Fin 2}` in BPR lexicographic order
(`Q₁` most significant, sign order `0 ≺ 1 ≺ -1`). -/
def exampleSignConditions : List (SignCondition (Fin 2)) :=
  [![0, 0], ![0, 1], ![0, -1], ![1, 0], ![1, 1], ![1, -1], ![-1, 0], ![-1, 1], ![-1, -1]]

/-- **BPR Example 2.67.** The matrix of signs of `𝒬^A` on `Σ` for two
polynomials is the displayed `9 × 9` matrix. -/
example :
    matrixOfSigns exampleExponents exampleSignConditions =
      !![ 1,  1,  1,  1,  1,  1,  1,  1,  1;
          0,  1, -1,  0,  1, -1,  0,  1, -1;
          0,  1,  1,  0,  1,  1,  0,  1,  1;
          0,  0,  0,  1,  1,  1, -1, -1, -1;
          0,  0,  0,  0,  1, -1,  0, -1,  1;
          0,  0,  0,  0,  1,  1,  0, -1, -1;
          0,  0,  0,  1,  1,  1,  1,  1,  1;
          0,  0,  0,  0,  1, -1,  0,  1, -1;
          0,  0,  0,  0,  1,  1,  0,  1,  1] := by
  ext i j
  simp only [matrixOfSigns, exampleExponents, exampleSignConditions,
    SignCondition.pow, Fin.prod_univ_two]
  fin_cases i <;> fin_cases j <;> decide

end Azurite.BPR
