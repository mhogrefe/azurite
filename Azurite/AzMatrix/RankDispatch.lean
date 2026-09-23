/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Typeclass-dispatched rank `AzMatrix.rank`.

  Mirrors `AzMatrix.DetDispatch`: one `AzMatrix.rank` function that
  statically dispatches between `AzMatrix.gaussRank` (over a field) and
  `AzMatrix.bareissRank` (over an integral domain with `ExactDiv`).
  Dispatch happens at elaboration time via Lean's typeclass resolution
  with instance priorities.

  Both branches come with a correctness theorem
  `AzMatrix.rank_eq_rank : M.rank = Matrix.rank (Matrix.of M.toFn)`,
  which is the uniform spec regardless of which algorithm runs
  underneath.
-/
import Azurite.AzMatrix.GaussRank
import Azurite.AzMatrix.BareissRank
import Azurite.AzMatrix.Equiv.GaussRank
import Azurite.AzMatrix.Equiv.BareissRank
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement

namespace Azurite

/-! ### `HasRank` typeclass -/

/-- `HasRank D` bundles a rank function for matrices over `D`, together
    with the spec that it agrees with `Matrix.rank`. Two priority-ordered
    instances exist: the high-priority `Field` instance (Gauss) and the
    lower-priority integral-domain-with-`ExactDiv` instance (Bareiss). -/
class AzMatrix.HasRank (D : Type _) [CommRing D] [DecidableEq D] where
  /-- The rank of `M`. -/
  rank {n : Nat} : AzMatrix D n n → Nat
  /-- The rank agrees with `Matrix.rank`. -/
  rank_eq_rank : ∀ {n : Nat} (M : AzMatrix D n n),
    rank M = Matrix.rank (Matrix.of M.toFn)

/-! ### Field instance: dispatches to `gaussRank` -/

instance (priority := 200) AzMatrix.instHasRankField {K : Type _}
    [Field K] [DecidableEq K] : AzMatrix.HasRank K where
  rank := AzMatrix.gaussRank
  rank_eq_rank M := M.gaussRank_eq_rank

/-! ### Domain instance: dispatches to `bareissRank` -/

instance (priority := 100) AzMatrix.instHasRankDomain {D : Type _}
    [CommRing D] [IsDomain D] [DecidableEq D] [Azurite.ExactDiv D] :
    AzMatrix.HasRank D where
  rank := AzMatrix.bareissRank
  rank_eq_rank M := M.bareissRank_eq_rank

/-! ### User-facing wrapper -/

/-- The rank of `M`. Statically dispatched: Gauss for fields, Bareiss for
    integral domains with `ExactDiv`. The two algorithms return the same
    value, namely `Matrix.rank (Matrix.of M.toFn)`. -/
def AzMatrix.rank {D : Type _} [CommRing D] [DecidableEq D]
    [AzMatrix.HasRank D] {n : Nat} (M : AzMatrix D n n) : Nat :=
  AzMatrix.HasRank.rank M

theorem AzMatrix.rank_eq_rank {D : Type _} [CommRing D] [DecidableEq D]
    [AzMatrix.HasRank D] {n : Nat} (M : AzMatrix D n n) :
    M.rank = Matrix.rank (Matrix.of M.toFn) :=
  AzMatrix.HasRank.rank_eq_rank M

/-! ### Tests -/

section Tests

-- Over AzRat (a field), `rank` dispatches to Gauss.
example (M : AzMatrix AzRat 3 3) : M.rank = M.gaussRank := rfl

-- Over `AzInt` (a domain, not a field), `rank` dispatches to Bareiss.
example (M : AzMatrix AzInt 3 3) : M.rank = M.bareissRank := rfl

-- Concrete examples via the dispatcher.
#guard
  match (AzMatrix.parseStr "[1, 2, 3; 4, 5, 6; 7, 8, 10]" :
      Option (AzMatrix AzRat 3 3)) with
  | some M => M.rank = 3
  | none => False

#guard
  match (AzMatrix.parseStr "[1, 2, 3; 2, 4, 6; 1, 1, 1]" :
      Option (AzMatrix AzInt 3 3)) with
  | some M => M.rank = 2
  | none => False

end Tests

end Azurite
