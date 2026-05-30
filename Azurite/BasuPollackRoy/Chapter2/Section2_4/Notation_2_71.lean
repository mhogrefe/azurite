import Azurite.BasuPollackRoy.Chapter2.Section2_4.Example_2_70

/-!
# BPR Notation 2.71: the matrices `Mₛ`

`Mₛ` is the `3ˢ × 3ˢ` matrix defined inductively by `M₁ = ` the
single-polynomial matrix of signs

`M₁ = !![1, 1, 1; 0, 1, -1; 0, 1, 1]`

and `M_{t+1} = M_t ⊗ M₁` (tensor / Kronecker product, Notation 2.69).

In Lean we index from `0`, taking `M₀` to be the `1 × 1` matrix `(1)` (the
empty tensor product); then `signMatrix s` is BPR's `Mₛ` for every `s ≥ 1`
and `signMatrix 1` is the base `3 × 3` matrix (`signMatrix_one`). The
return type `AzMatrix SignType (3 ^ s) (3 ^ s)` typechecks because
`3 ^ (s + 1)` reduces to `3 ^ s * 3`, the dimension produced by
`AzMatrix.kronecker`.
-/

namespace Azurite.BPR

open Polynomial

/-- **BPR Notation 2.71.** The `3ˢ × 3ˢ` matrix `Mₛ`, defined inductively
by `M₀ = (1)`, `M_{s+1} = Mₛ ⊗ M₁`, where `M₁ = exampleM` is the
single-polynomial matrix of signs. For `s ≥ 1` this is BPR's `Mₛ`. -/
def signMatrix : (s : Nat) → AzMatrix SignType (3 ^ s) (3 ^ s)
  | 0 => AzMatrix.ofLists [[1]]
  | s + 1 => (signMatrix s).kronecker exampleM

/-- `M₁` is the base single-polynomial matrix of signs (the `3 × 3`
matrix), as BPR's inductive definition prescribes. -/
theorem signMatrix_one : signMatrix 1 = exampleM := by decide

/-- `M₂ = M₁ ⊗ M₁` is the `9 × 9` matrix of Example 2.70. -/
theorem signMatrix_two : signMatrix 2 = exampleM.kronecker exampleM := by decide

end Azurite.BPR
