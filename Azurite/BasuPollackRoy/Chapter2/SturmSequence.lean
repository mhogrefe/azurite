import Azurite.BasuPollackRoy.Chapter1.Section1_2
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 2, Section 2.2: Sturm sequence

Let `P` be a non-zero polynomial with coefficients in a real closed field
`R`. The sequence of signed remainders of `P` and `P'`, `SRemS(P, P')`
(see Definition 1.7), is the **Sturm sequence** of `P`.

The underlying construction `SRemS` (BPR Definition 1.7) is total over any
field, so we define `sturmSequence` on any field as well. The "non-zero `P`
in a real closed field" hypothesis becomes a precondition for downstream
theorems rather than for the definition itself.
-/

namespace Azurite.BPR

open Polynomial

/-- **BPR Chapter 2.2.** The Sturm sequence of `P`, defined as the signed
    remainder sequence `SRemS(P, P')` of `P` and its derivative. -/
noncomputable def sturmSequence {K : Type*} [Field K] (P : Polynomial K) :
    ℕ → Polynomial K :=
  SRemS P P.derivative

@[simp] theorem sturmSequence_zero {K : Type*} [Field K] (P : Polynomial K) :
    sturmSequence P 0 = P := rfl

@[simp] theorem sturmSequence_one {K : Type*} [Field K] (P : Polynomial K) :
    sturmSequence P 1 = P.derivative := rfl

end Azurite.BPR
