import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_4
import Mathlib.Algebra.Polynomial.Derivative

/-! # BPR §3.3 — polynomials with semialgebraic continuous coefficients

The setting for §3.3 (semialgebraic germs) is a univariate polynomial `P` in `Y` whose coefficients
are semialgebraic continuous functions on a semialgebraic set `S ⊆ R^k`. We model `P` literally as a
`Polynomial` whose coefficient ring is the (pointwise) ring of functions `(Fin k → R) → R`:

  `P : Polynomial ((Fin k → R) → R)`.

For a fixed `x`, the specialization `P(x, Y)` is the genuine univariate polynomial over `R` obtained
by evaluating each coefficient function at `x` — `P.map (Pi.evalRingHom _ x) : R[Y]` — on which all
the root/derivative analysis takes place. -/

namespace Azurite.BPR

open Polynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A scalar function `(Fin k → R) → R` viewed as a map into the line `R^1 = Fin 1 → R`. -/
def scalarFun (c : (Fin k → R) → R) : (Fin k → R) → (Fin 1 → R) := fun u => constPt (c u)

/-- A scalar function is **semialgebraic and continuous on `S`** if its view into the line `R^1` is a
semialgebraic continuous function. -/
def IsSemialgContinuousOn (S : Set (Fin k → R)) (c : (Fin k → R) → R) : Prop :=
  IsSemialgebraicFunction S (scalarFun c) ∧ ContinuousOn (scalarFun c) S

/-- `P` has **semialgebraic continuous coefficients on `S`**: every coefficient function
`P.coeff i : (Fin k → R) → R` is semialgebraic and continuous on `S`. -/
def HasSemialgContinuousCoeffs (S : Set (Fin k → R)) (P : Polynomial ((Fin k → R) → R)) : Prop :=
  ∀ i, IsSemialgContinuousOn S (P.coeff i)

/-- **Specialization** `P(x, Y)`: evaluate `P`'s coefficient functions at the point `x`, giving a
genuine univariate polynomial over `R`. -/
noncomputable def specializeAt (P : Polynomial ((Fin k → R) → R)) (x : Fin k → R) : Polynomial R :=
  P.map (Pi.evalRingHom (fun _ : Fin k → R => R) x)

/-- `y` is a **simple root** of `Q ∈ R[Y]`: `Q(y) = 0` and `Q'(y) ≠ 0`. -/
def IsSimpleRoot (Q : Polynomial R) (y : R) : Prop := Q.eval y = 0 ∧ Q.derivative.eval y ≠ 0

end Azurite.BPR
