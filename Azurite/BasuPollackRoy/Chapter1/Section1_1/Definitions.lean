/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.1: Definitions and First Properties

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

A field K is **algebraically closed** if every polynomial of positive degree
with coefficients in K has a root in K.

This is already formalized in Mathlib as `IsAlgClosed`:

```
/-- An algebraically closed field is one where every polynomial splits. Equivalently, all
non-constant polynomials have a root. See `IsAlgClosed.exists_root` and
`IsAlgClosed.of_exists_root`. -/
class IsAlgClosed (k : Type u) [Field k] : Prop where
  splits : ∀ p : k[X], p.Splits
```

See: `Mathlib.FieldTheory.IsAlgClosed.Basic`

The equivalent characterization via roots (BPR's formulation) is:

```
theorem IsAlgClosed.exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree ≠ 0) :
    ∃ x, IsRoot p x
```

Key Mathlib API:
- `IsAlgClosed.exists_root`: every nonconstant polynomial has a root
- `IsAlgClosed.of_exists_root`: constructing `IsAlgClosed` from the root property
- `IsAlgClosed.degree_eq_one_of_irreducible`: irreducible polynomials are linear
- `IsAlgClosure`: typeclass for an algebraic closure of a ring
- `IsAlgClosure.equiv`: any two algebraic closures are isomorphic

### Notation: D[X₁, …, Xₖ]

BPR defines polynomials over a ring D in k variables. In Lean, this is:

```
-- D[X₁, …, Xₖ] is expressed as:
MvPolynomial (Fin k) D    -- where [CommSemiring D]

-- The variable Xᵢ (1-indexed in BPR, 0-indexed in Lean):
MvPolynomial.X (i : Fin k)

-- A constant from D:
MvPolynomial.C (d : D)
```

See: `Mathlib.RingTheory.MvPolynomial.Basic`
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

-- C is an algebraically closed field, used throughout BPR Chapter 1.
variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

end Azurite.BPR
