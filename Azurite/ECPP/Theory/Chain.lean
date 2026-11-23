/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-!
# Scalar multiplication on a Weierstrass curve over a ring, by formulas

The theory behind the arithmetic of elliptic curve primality proving, on Mathlib's objects
only (no `Az*` type here: see `docs/ecpp_plan.md`).

Over a commutative ring `R` — in the application `ℤ/Nℤ` with `N` of unknown nature — a
"point" is a triple of Jacobian coordinates, and the group law is not available: only the
formulas `dblXYZ` and `addXYZ` of Mathlib are.  `MulChain W U k T` says that the triple `T` is
obtained from `U` by these formulas along a computation of `k · U`, **with the `Z`-coordinate
of every addition a unit**.

`MulChain.toAffine`: under any ring homomorphism `f` to a field under which `U` is a
nonsingular point, `T` reduces to the point `k • U` of the curve over that field.  The unit
condition is what makes the incomplete addition formula right in the field: `addZ T S` is
`X_T Z_S² − X_S Z_T²`, and it vanishes exactly when the two points have the same `x`.  No
condition is needed at a doubling, whose formula is complete.

The constructor `scale` (another representative of the same point) is there so that an
implementation is free in its normalization of the coordinates.
-/

namespace Azurite.ECPP

open WeierstrassCurve WeierstrassCurve.Jacobian

variable {R : Type*} [CommRing R]

/-- **`T` is `k · U` by the formulas**: obtained from `U` by doublings, additions whose
`Z`-coordinate is a unit, and changes of representative. -/
inductive MulChain (W : Jacobian R) (U : Fin 3 → R) : ℕ → (Fin 3 → R) → Prop
  | base : MulChain W U 1 U
  | dbl {k : ℕ} {T : Fin 3 → R} : MulChain W U k T → MulChain W U (2 * k) (W.dblXYZ T)
  | add {k l : ℕ} {T S : Fin 3 → R} : MulChain W U k T → MulChain W U l S →
      IsUnit (addZ T S) → MulChain W U (k + l) (W.addXYZ T S)
  | scale {k : ℕ} {T : Fin 3 → R} (u : R) : IsUnit u → MulChain W U k T →
      MulChain W U k (u • T)

/-- **A chain reduces to the scalar multiple** in every field: if `U` is a nonsingular point
of the curve over the field `F` (through `f`), then so is `T`, and it is `k • U`. -/
theorem MulChain.toAffine {F : Type*} [Field F] [DecidableEq F] (f : R →+* F) {W : Jacobian R}
    {U : Fin 3 → R} (hU : (W.map f).Nonsingular (f ∘ U)) {k : ℕ} {T : Fin 3 → R}
    (h : MulChain W U k T) :
    (W.map f).Nonsingular (f ∘ T) ∧
      Point.toAffine (W.map f) (f ∘ T) = k • Point.toAffine (W.map f) (f ∘ U) := by
  induction h with
  | base => exact ⟨hU, (one_nsmul _).symm⟩
  | dbl _ ih =>
    obtain ⟨hT, e⟩ := ih
    rw [← map_dblXYZ, ← add_self]
    exact ⟨nonsingular_add hT hT, by rw [Point.toAffine_add hT hT, e, two_mul, add_nsmul]⟩
  | add _ _ hu ihT ihS =>
    obtain ⟨hT, eT⟩ := ihT
    obtain ⟨hS, eS⟩ := ihS
    rename_i T S _ _
    have hne : ¬ (f ∘ T) ≈ (f ∘ S) := by
      intro heq
      have h0 := addZ_of_X_eq (X_eq_of_equiv heq)
      rw [map_addZ] at h0
      exact (hu.map f).ne_zero h0
    rw [← map_addXYZ, ← add_of_not_equiv hne]
    exact ⟨nonsingular_add hT hS, by rw [Point.toAffine_add hT hS, eT, eS, add_nsmul]⟩
  | scale u hu _ ih =>
    obtain ⟨hT, e⟩ := ih
    rw [comp_smul]
    exact ⟨(nonsingular_smul _ (hu.map f)).mpr hT, by rw [Point.toAffine_smul _ (hu.map f), e]⟩

end Azurite.ECPP
