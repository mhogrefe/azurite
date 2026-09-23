/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Equiv.Eval2
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra

/-!
# Constant coefficient ring hom for `AzMvPolynomial`

Provides `AzMvPolynomial.constantCoeff : AzMvPolynomial n R ord →+* R`,
the ring homomorphism extracting the constant term of a multivariate
polynomial. Defined computationally as evaluation at the zero point, and
shown to agree with `MvPolynomial.constantCoeff` across the bridge.

Fin-only counterpart of Mathlib's `MvPolynomial.constantCoeff`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    {n : ℕ} {ord : MonomialOrder}

/-- The constant-coefficient ring homomorphism on `AzMvPolynomial`: sends
    a polynomial to its constant term. Defined computationally as
    evaluation at the zero point, so it runs directly on the sparse
    representation without materializing the `MvPolynomial` image. -/
def AzMvPolynomial.constantCoeff : AzMvPolynomial n R ord →+* R where
  toFun p := p.eval₂ (RingHom.id R) (fun _ => 0)
  map_zero' := by
    show (0 : AzMvPolynomial n R ord).eval₂ (RingHom.id R) (fun _ => 0) = 0
    rw [toMvPoly_eval₂,
        show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero,
        MvPolynomial.eval₂_zero]
  map_one' := by
    show (1 : AzMvPolynomial n R ord).eval₂ (RingHom.id R) (fun _ => 0) = 1
    rw [toMvPoly_eval₂,
        show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one]
    exact map_one (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0))
  map_add' p q := by
    show (p + q).eval₂ (RingHom.id R) (fun _ => 0) =
         p.eval₂ (RingHom.id R) (fun _ => 0) + q.eval₂ (RingHom.id R) (fun _ => 0)
    rw [toMvPoly_eval₂, toMvPoly_eval₂, toMvPoly_eval₂, toMvPoly_add]
    exact map_add (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)) _ _
  map_mul' p q := by
    show (p * q).eval₂ (RingHom.id R) (fun _ => 0) =
         p.eval₂ (RingHom.id R) (fun _ => 0) * q.eval₂ (RingHom.id R) (fun _ => 0)
    rw [toMvPoly_eval₂, toMvPoly_eval₂, toMvPoly_eval₂, toMvPoly_mul]
    exact map_mul (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 0)) _ _

/-- `AzMvPolynomial.constantCoeff` matches `MvPolynomial.constantCoeff`
    across the bridge. -/
@[simp] theorem AzMvPolynomial.toMvPoly_constantCoeff
    (p : AzMvPolynomial n R ord) :
    AzMvPolynomial.constantCoeff p =
      MvPolynomial.constantCoeff p.toMvPoly := by
  show p.eval₂ (RingHom.id R) (fun _ => 0) = _
  rw [toMvPoly_eval₂,
      show (MvPolynomial.eval₂ (RingHom.id R) (fun _ : Fin n => (0 : R)) p.toMvPoly) =
           (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : Fin n => (0 : R))) p.toMvPoly
        from rfl,
      MvPolynomial.eval₂Hom_zero'_apply]
  rfl

@[simp] theorem AzMvPolynomial.constantCoeff_C (r : R) :
    AzMvPolynomial.constantCoeff (AzMvPolynomial.C r : AzMvPolynomial n R ord) = r := by
  rw [toMvPoly_constantCoeff, toMvPoly_C, MvPolynomial.constantCoeff_C]

@[simp] theorem AzMvPolynomial.constantCoeff_X (i : Fin n) :
    AzMvPolynomial.constantCoeff (AzMvPolynomial.X i : AzMvPolynomial n R ord) = 0 := by
  rw [toMvPoly_constantCoeff, toMvPoly_X, MvPolynomial.constantCoeff_X]

end Azurite
