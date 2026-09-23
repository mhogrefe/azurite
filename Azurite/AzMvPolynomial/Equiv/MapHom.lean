/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Equiv.Map
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Bundled ring-hom / alg-hom / alg-equiv forms of `AzMvPolynomial.map`

Provides:

* `AzMvPolynomial.mapRingHom` — wraps `AzMvPolynomial.map` (applied to a
  `RingHom`) as a bundled ring homomorphism between the polynomial rings.
* `AzMvPolynomial.mapAlgHom` — wraps `mapRingHom` for an `R`-algebra
  homomorphism as a bundled `R`-algebra homomorphism between the
  polynomial rings (inner coefficient rings both `R`-algebras).
* `AzMvPolynomial.mapAlgEquiv` — upgrades `mapAlgHom` applied to an
  `R`-algebra equivalence to an `R`-algebra equivalence on the polynomial
  rings.

Ring-hom axioms are proved by transfer along `toMvPoly_map` through the
bridge to `MvPolynomial.map`.
-/

namespace Azurite

open AzMvPolynomial

/-! ### `mapRingHom` -/

section MapRingHom

variable {R S : Type _}
    [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
    {n : ℕ} {ord : MonomialOrder}

/-- Bundled ring-hom form of `AzMvPolynomial.map`. -/
def AzMvPolynomial.mapRingHom (f : R →+* S) :
    AzMvPolynomial n R ord →+* AzMvPolynomial n S ord where
  toFun p := p.map f
  map_zero' := toMvPoly_injective (by
    rw [toMvPoly_map,
        show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero,
        map_zero,
        show (0 : AzMvPolynomial n S ord).toMvPoly = (0 : MvPolynomial (Fin n) S)
          from toMvPoly_zero])
  map_one' := toMvPoly_injective (by
    rw [toMvPoly_map,
        show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one,
        map_one,
        show (1 : AzMvPolynomial n S ord).toMvPoly = (1 : MvPolynomial (Fin n) S)
          from toMvPoly_one])
  map_add' p q := toMvPoly_injective (by
    rw [toMvPoly_map, toMvPoly_add, map_add, toMvPoly_add,
        toMvPoly_map, toMvPoly_map])
  map_mul' p q := toMvPoly_injective (by
    rw [toMvPoly_map, toMvPoly_mul, map_mul, toMvPoly_mul,
        toMvPoly_map, toMvPoly_map])

@[simp] theorem AzMvPolynomial.mapRingHom_C (f : R →+* S) (r : R) :
    (AzMvPolynomial.mapRingHom (n := n) (ord := ord) f)
        (AzMvPolynomial.C r : AzMvPolynomial n R ord) =
      (AzMvPolynomial.C (f r) : AzMvPolynomial n S ord) :=
  toMvPoly_injective (by
    show ((AzMvPolynomial.C r : AzMvPolynomial n R ord).map f).toMvPoly =
         (AzMvPolynomial.C (f r) : AzMvPolynomial n S ord).toMvPoly
    rw [toMvPoly_map, toMvPoly_C, toMvPoly_C, MvPolynomial.map_C])

@[simp] theorem AzMvPolynomial.mapRingHom_X (f : R →+* S) (i : Fin n) :
    (AzMvPolynomial.mapRingHom (ord := ord) f)
        (AzMvPolynomial.X i : AzMvPolynomial n R ord) =
      (AzMvPolynomial.X i : AzMvPolynomial n S ord) :=
  toMvPoly_injective (by
    show ((AzMvPolynomial.X i : AzMvPolynomial n R ord).map f).toMvPoly =
         (AzMvPolynomial.X i : AzMvPolynomial n S ord).toMvPoly
    rw [toMvPoly_map, toMvPoly_X, toMvPoly_X, MvPolynomial.map_X])

end MapRingHom

/-! ### `mapAlgHom` and `mapAlgEquiv` -/

section MapAlg

variable {R A₁ A₂ : Type _}
    [CommSemiring R]
    [CommSemiring A₁] [NoZeroDivisors A₁] [DecidableEq A₁] [Algebra R A₁]
    [CommSemiring A₂] [NoZeroDivisors A₂] [DecidableEq A₂] [Algebra R A₂]
    {n : ℕ} {ord : MonomialOrder}

/-- Bundled `R`-algebra-hom form of `AzMvPolynomial.map` along an algebra
    homomorphism `f : A₁ →ₐ[R] A₂`. -/
def AzMvPolynomial.mapAlgHom (f : A₁ →ₐ[R] A₂) :
    AzMvPolynomial n A₁ ord →ₐ[R] AzMvPolynomial n A₂ ord where
  __ := AzMvPolynomial.mapRingHom (f : A₁ →+* A₂)
  commutes' r := by
    show (AzMvPolynomial.mapRingHom (f : A₁ →+* A₂))
          (AzMvPolynomial.C ((algebraMap R A₁) r) : AzMvPolynomial n A₁ ord)
        = (AzMvPolynomial.C ((algebraMap R A₂) r) : AzMvPolynomial n A₂ ord)
    rw [AzMvPolynomial.mapRingHom_C]
    congr 1
    exact f.commutes r

/-- Bundled `R`-algebra-equivalence form of `AzMvPolynomial.map` along an
    algebra equivalence `e : A₁ ≃ₐ[R] A₂`. -/
def AzMvPolynomial.mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) :
    AzMvPolynomial n A₁ ord ≃ₐ[R] AzMvPolynomial n A₂ ord where
  __ := AzMvPolynomial.mapAlgHom (e : A₁ →ₐ[R] A₂)
  invFun p := (AzMvPolynomial.mapRingHom (e.symm : A₂ →+* A₁)) p
  left_inv p := toMvPoly_injective (by
    show ((p.map (e : A₁ →+* A₂)).map (e.symm : A₂ →+* A₁)).toMvPoly = p.toMvPoly
    rw [toMvPoly_map, toMvPoly_map, MvPolynomial.map_map,
        show ((e.symm : A₂ →+* A₁).comp (e : A₁ →+* A₂)) = RingHom.id A₁ by
          ext x; exact e.symm_apply_apply x,
        MvPolynomial.map_id])
  right_inv p := toMvPoly_injective (by
    show ((p.map (e.symm : A₂ →+* A₁)).map (e : A₁ →+* A₂)).toMvPoly = p.toMvPoly
    rw [toMvPoly_map, toMvPoly_map, MvPolynomial.map_map,
        show ((e : A₁ →+* A₂).comp (e.symm : A₂ →+* A₁)) = RingHom.id A₂ by
          ext x; exact e.apply_symm_apply x,
        MvPolynomial.map_id])

end MapAlg

end Azurite
