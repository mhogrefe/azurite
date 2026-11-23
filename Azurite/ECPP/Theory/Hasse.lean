/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic

/-!
# The Hasse bound (statement)

`HasseBound`: for every elliptic curve `y² = x³ + ax + b` over a prime field `𝔽_p`, `p ≥ 5`,
`(#E(𝔽_p) − (p + 1))² ≤ 4p`.  **A statement only**: it is not in Mathlib and not yet proven
here; the primality criterion (`Theory/Criterion.lean`) takes it as a hypothesis.  The proof
to be formalized is Manin's, after Chahal and Osserman, *The Riemann hypothesis for elliptic
curves*, Amer. Math. Monthly 115 (2008) — which is for curves in this short form and
characteristic `≠ 2, 3`; hence the form of the statement.  Its arithmetic end is in
`Theory/Manin.lean`.  See `docs/ecpp_plan.md`.

Also: `shortW a b`, the curve `y² = x³ + ax + b`; the group of points of a curve over a finite
field is finite.
-/

namespace Azurite.ECPP

open WeierstrassCurve

/-- The points of a Weierstrass curve over a finite field are finitely many. -/
instance finite_point {F : Type*} [Field F] [Finite F] (W : Affine F) : Finite W.Point :=
  Finite.of_injective
    (fun P : W.Point => match P with
      | .zero => (none : Option (F × F))
      | .some x y _ => some (x, y))
    (by
      rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) heq
      · rfl
      · exact absurd heq (by simp)
      · exact absurd heq (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rfl)

/-- The curve `y² = x³ + ax + b`. -/
def shortW {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R := ⟨0, 0, 0, a, b⟩

theorem shortW_Δ {R : Type*} [CommRing R] (a b : R) :
    (shortW a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortW_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) :
    (shortW a b).map f = shortW (f a) (f b) := by
  simp [shortW, WeierstrassCurve.map]

/-- **The Hasse bound over the prime fields** `𝔽_p`, `p ≥ 5`, for the curves
`y² = x³ + ax + b` with `4a³ + 27b² ≠ 0`: `|#E(𝔽_p) − (p + 1)| ≤ 2√p`, as
`(#E(𝔽_p) − (p + 1))² ≤ 4p`. -/
def HasseBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ a b : ZMod p, 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ((Nat.card (shortW a b).toAffine.Point : ℤ) - (p + 1)) ^ 2 ≤ 4 * p

end Azurite.ECPP
