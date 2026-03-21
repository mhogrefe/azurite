import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.2: Euclidean Division and Greatest Common Divisor

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

In this section, C is an algebraically closed field, D is a subring of C,
and K is the quotient field of D.

### Polynomial Basics in Mathlib

The **degree** of a polynomial is defined in `Mathlib.Algebra.Polynomial.Degree.Defs`:

```
def Polynomial.degree : Polynomial R → WithBot ℕ :=
  fun p ↦ p.support.max
```

The degree uses `WithBot ℕ`, so the zero polynomial has degree `⊥` (minus infinity).
There is also `natDegree`, which maps `⊥` to `0`:

```
def Polynomial.natDegree : Polynomial R → ℕ :=
  fun p ↦ WithBot.unbotD 0 p.degree
```

The **coefficient** of Xⁿ in a polynomial is defined in
`Mathlib.Algebra.Polynomial.Defs`:

```
def Polynomial.coeff : Polynomial R → ℕ → R :=
  fun x ↦ match x with
  | { toFinsupp := p } => ⇑p
```

A polynomial is represented as a `Finsupp ℕ R` (a finitely-supported
function ℕ → R), so `coeff p n` is just evaluation of that function at `n`.

The **leading coefficient** is defined in `Mathlib.Algebra.Polynomial.Degree.Defs`:

```
def Polynomial.leadingCoeff : Polynomial R → R :=
  fun p ↦ p.coeff p.natDegree
```
-/

namespace Azurite.BPR

open Polynomial

/-!
C is an algebraically closed field, D is a subring of C, and K is
the quotient field of D.
-/
variable {C : Type*} [Field C] [IsAlgClosed C]
variable {D : Type*} [CommRing D] [IsDomain D] [Algebra D C]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]

/-!
### Definition 1.4 (Divisor)
Suppose that P and Q are two polynomials in D[X]. The polynomial Q is a
*divisor* of P if P = AQ for some A ∈ K[X].

This is **not** a separate definition in Mathlib. It is simply standard
divisibility `∣` in K[X] applied after mapping P and Q from D[X] into K[X]
via `Polynomial.map (algebraMap D K)`:

```
Dvd.dvd : α → α → Prop
a ∣ b  ↔  ∃ c, b = a * c
```
-/

/-- BPR Definition 1.4: `Q` is a divisor of `P` over `K` if `Q ∣ P`
    after embedding both into `K[X]`.  Equivalently, there exists
    `A : K[X]` such that `P.map = A * Q.map`. -/
def Polynomial.DivisorOver
    (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (Q P : D[X]) : Prop :=
  (Q.map (algebraMap D K)) ∣ (P.map (algebraMap D K))

omit [IsDomain D] in
theorem divisorOver_zero (P : D[X]) : Polynomial.DivisorOver K P 0 := by
  simp [Polynomial.DivisorOver, Polynomial.map_zero]

omit [IsDomain D] in
/-- 0 divides P over K if and only if P = 0. -/
theorem zero_divisorOver_iff (P : D[X]) :
    Polynomial.DivisorOver K (0 : D[X]) P ↔ P = 0 := by
  constructor
  · intro h
    simp only [Polynomial.DivisorOver, Polynomial.map_zero, zero_dvd_iff] at h
    exact Polynomial.map_injective _ (IsFractionRing.injective D K) (by simp [h])
  · rintro rfl; simp [Polynomial.DivisorOver]

end Azurite.BPR
