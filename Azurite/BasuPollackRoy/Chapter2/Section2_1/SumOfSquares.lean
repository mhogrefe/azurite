import Azurite.BasuPollackRoy.Chapter2.Section2_1.Cones
import Mathlib.Algebra.Ring.SumsOfSquares

/-! # BPR Section 2.1 — Squares and sums of squares

For a field `K`:

- `K^{(2)}` denotes the set of *squares* of elements of `K`,
  i.e., `{x² | x ∈ K}`. In Mathlib this is `{x | IsSquare x}`.
- `ΣK^{(2)}` denotes the `Subsemiring` of *sums of squares* of elements
  of `K`. In Mathlib this is `Subsemiring.sumSq K`, built from the
  inductive predicate `IsSumSq`.

The set `ΣK^{(2)}` is a cone: it is closed under addition and
multiplication, contains 0 = 0² and 1 = 1², and every element of
`K^{(2)}` belongs to it. Moreover it is the *smallest* cone: it is
contained in every cone of `K`.
-/

namespace Azurite.BPR

variable (F : Type*) [CommRing F]

/-- **BPR Notation.** `ΣF^{(2)}`: the `Subsemiring` of sums of squares in `F`.
    An element `s : F` belongs to `Subsemiring.sumSq F` iff `IsSumSq s`,
    i.e., `s` can be written as a finite sum `a₁·a₁ + a₂·a₂ + ⋯ + aₙ·aₙ`. -/
abbrev sumOfSquares : Subsemiring F := Subsemiring.sumSq F

/-- `ΣF^{(2)}` is a cone: every square `x²` is a sum of squares. -/
lemma isCone_sumOfSquares : IsCone (sumOfSquares F) :=
  fun x => Subsemiring.mem_sumSq.mpr (by rw [sq]; exact IsSumSq.mul_self x)

/-- `ΣF^{(2)}` is contained in every cone of `F` —
    it is the smallest cone. -/
lemma sumOfSquares_le_cone (C : Subsemiring F) (hC : IsCone C) :
    sumOfSquares F ≤ C := by
  intro x hx
  rw [Subsemiring.mem_sumSq] at hx
  induction hx with
  | zero => exact C.zero_mem
  | sq_add a _ ih => exact C.add_mem (by rw [← sq]; exact hC a) ih

end Azurite.BPR
