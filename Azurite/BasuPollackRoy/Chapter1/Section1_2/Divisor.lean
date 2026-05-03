import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Section 1.2: Divisor

In this section, $C$ is an algebraically closed field, $D$ is a subring
of $C$, and $K$ is the quotient field of $D$.

Suppose $P$ and $Q$ are polynomials in $D[X]$. The polynomial $Q$ is a
*divisor* of $P$ if $P = A Q$ for some $A \in K[X]$.

This is **not** a separate definition in Mathlib. It is simply standard
divisibility `∣` in `K[X]` applied after mapping $P$ and $Q$ from $D[X]$
into `K[X]` via `Polynomial.map (algebraMap D K)`.
-/

open Polynomial

/-- `Q` is a divisor of `P` over `K` if `Q ∣ P` after embedding both
    into `K[X]`. Equivalently, there exists `A : K[X]` such that
    `P.map = A * Q.map`. Defined at the root `Polynomial` namespace
    so that dot notation `Q.DivisorOver K P` works on `Q : D[X]`. -/
def Polynomial.DivisorOver
    {D : Type*} [CommRing D]
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (Q P : D[X]) : Prop :=
  (Q.map (algebraMap D K)) ∣ (P.map (algebraMap D K))

namespace Azurite.BPR

variable {D : Type*} [CommRing D]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]

theorem divisorOver_zero (P : D[X]) : Polynomial.DivisorOver K P 0 := by
  simp [Polynomial.DivisorOver, Polynomial.map_zero]

/-- 0 divides P over K if and only if P = 0. -/
theorem zero_divisorOver_iff (P : D[X]) :
    Polynomial.DivisorOver K (0 : D[X]) P ↔ P = 0 := by
  constructor
  · intro h
    simp only [Polynomial.DivisorOver, Polynomial.map_zero, zero_dvd_iff] at h
    exact Polynomial.map_injective _ (IsFractionRing.injective D K) (by simp [h])
  · rintro rfl; simp [Polynomial.DivisorOver]

end Azurite.BPR
