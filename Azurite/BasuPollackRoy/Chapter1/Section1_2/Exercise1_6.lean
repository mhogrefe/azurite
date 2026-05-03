import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Exercise 1.6

Over a field $K$, $x \in K$ is a root of $P \in K[X]$ if and only if
$(X - x)$ divides $P$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- Exercise 1.6: x is a root of P iff (X − x) divides P in K[X]. -/
theorem exercise_1_6 (P : K[X]) (x : K) :
    Polynomial.eval x P = 0 ↔ (X - Polynomial.C x) ∣ P :=
  dvd_iff_isRoot.symm

end Azurite.BPR
