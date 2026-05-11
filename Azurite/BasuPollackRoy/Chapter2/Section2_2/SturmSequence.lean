import Azurite.BasuPollackRoy.Chapter1.Section1_2.Coprime
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Corollary1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Divisor
import Azurite.BasuPollackRoy.Chapter1.Section1_2.EuclideanDivision
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_6
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_7
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14Corollaries
import Azurite.BasuPollackRoy.Chapter1.Section1_2.PolynomialBasics
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_5
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_9
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_12
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Remark1_4
import Azurite.BasuPollackRoy.Chapter1.Section1_2.RootCharacterizations
import Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination
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
