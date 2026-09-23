/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Typeclass-dispatched determinant `AzMatrix.det`.

  This file provides a single `AzMatrix.det` function that statically
  dispatches between the Gauss-based `AzMatrix.gaussDet` (over a field)
  and the Bareiss-based `AzMatrix.bareissDet` (over an integral domain
  with `ExactDiv`), based on which typeclasses the entry ring satisfies.

  The dispatch happens at elaboration time via Lean's typeclass resolution
  (with instance priorities). For an entry type that is a `Field`, Lean
  picks the Gauss branch; otherwise it falls back to Bareiss, which works
  over any integral domain with the bundled `ExactDiv` typeclass.

  Both branches come with a correctness theorem
  `AzMatrix.det_eq_Matrix_det : M.det = Matrix.det M.toFn`, which is the
  uniform spec regardless of which algorithm runs underneath.
-/
import Azurite.AzMatrix.Det
import Azurite.AzMatrix.BareissDet
import Azurite.AzMatrix.Equiv.Det
import Azurite.AzMatrix.Equiv.BareissDet
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement

namespace Azurite

/-! ### `HasDet` typeclass -/

/-- `HasDet D` bundles a determinant function for matrices over `D`,
    together with the spec that it agrees with `Matrix.det`. Two priority-
    ordered instances exist: the high-priority `Field` instance (Gauss)
    and the lower-priority integral-domain-with-`ExactDiv` instance
    (Bareiss). -/
class AzMatrix.HasDet (D : Type _) [CommRing D] [DecidableEq D] where
  /-- The determinant of `M`. -/
  det {n : Nat} : AzMatrix D n n → D
  /-- The determinant agrees with `Matrix.det`. -/
  det_eq_Matrix_det : ∀ {n : Nat} (M : AzMatrix D n n),
    det M = Matrix.det M.toFn

/-! ### Field instance: dispatches to `gaussDet` -/

instance (priority := 200) AzMatrix.instHasDetField {K : Type _}
    [Field K] [DecidableEq K] : AzMatrix.HasDet K where
  det := AzMatrix.gaussDet
  det_eq_Matrix_det M := M.gaussDet_eq_Matrix_det

/-! ### Domain instance: dispatches to `bareissDet` -/

instance (priority := 100) AzMatrix.instHasDetDomain {D : Type _}
    [CommRing D] [IsDomain D] [DecidableEq D] [Azurite.ExactDiv D] :
    AzMatrix.HasDet D where
  det := AzMatrix.bareissDet
  det_eq_Matrix_det M := M.bareissDet_eq_Matrix_det

/-! ### User-facing wrapper -/

/-- The determinant of `M`. Statically dispatched: Gauss for fields,
    Bareiss for integral domains with `ExactDiv`. The two algorithms
    return the same value, namely `Matrix.det M.toFn`. -/
def AzMatrix.det {D : Type _} [CommRing D] [DecidableEq D]
    [AzMatrix.HasDet D] {n : Nat} (M : AzMatrix D n n) : D :=
  AzMatrix.HasDet.det M

theorem AzMatrix.det_eq_Matrix_det {D : Type _} [CommRing D] [DecidableEq D]
    [AzMatrix.HasDet D] {n : Nat} (M : AzMatrix D n n) :
    M.det = Matrix.det M.toFn :=
  AzMatrix.HasDet.det_eq_Matrix_det M

/-! ### Tests -/

section Tests

-- Over AzRat (a field), `det` dispatches to Gauss.
example (M : AzMatrix AzRat 3 3) : M.det = M.gaussDet := rfl

-- Over a Domain without Field (here AzInt), `det` dispatches to Bareiss.
example (M : AzMatrix AzInt 3 3) : M.det = M.bareissDet := rfl

end Tests

end Azurite
