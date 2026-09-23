/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# BPR Notation 4.1: Discriminant

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*, §4.1.

Throughout this chapter, `K` denotes a field of characteristic zero, `C` an
algebraically closed field containing `K`, and `R` (when `K` is ordered) a
real closed field containing `K`.

For a monic polynomial `P` of degree `p` with roots `x_1, …, x_p` in `C`
(counted with multiplicity), BPR defines the discriminant by

  `Disc(P) = ∏_{p ≥ i > j ≥ 1} (x_i − x_j)^2`.

The Lean definition follows BPR's formula directly via the multiset-friendly
symmetric reformulation

  `(-1)^{p(p−1)/2} · ∏_{(a,b) off-diagonal in s ×ˢ s} (a − b)`,

where `s` is the multiset of roots in `C`. The two forms are equal by the
elementary identity
`∏_{i ≠ j}(x_i − x_j) = (-1)^{p(p−1)/2} · (∏_{i > j}(x_i − x_j))^2`.
Equivalence to Mathlib's `Polynomial.discr` (the universal Sylvester-matrix
definition) is deferred to §4.2, where the resultant infrastructure lives.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

/-- **BPR Notation 4.1** (Discriminant). For a monic polynomial `P : K[X]`
    of degree `p` with roots `x_1, …, x_p` in `C` (counted with
    multiplicity), `disc P = ∏_{p ≥ i > j ≥ 1} (x_i − x_j)^2`.

    Implemented via the symmetric reformulation
    `(-1)^{p(p−1)/2} · ∏_{(a,b) off-diagonal in s ×ˢ s} (a − b)`,
    where `s = P.aroots C` is the multiset of roots in `C`. -/
noncomputable def disc (P : K[X]) : C := by
  classical
  let s := P.aroots C
  let p := s.card
  exact (-1 : C) ^ (p * (p - 1) / 2) *
    ((s ×ˢ s - s.map (fun a => (a, a))).map (fun ab => ab.1 - ab.2)).prod

end Azurite.BPR.Chapter4
