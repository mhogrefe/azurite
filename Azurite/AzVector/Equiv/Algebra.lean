/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Algebraic typeclass instances and linear equivalence for AzVector.

  Transfers `AddCommMonoid`, `AddCommGroup`, and `Module` from
  `Fin n → R` to `AzVector R n` via the injective `toFn` map.
  Provides a `LinearEquiv` between `AzVector R n` and `Fin n → R`.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Equiv.Defs

namespace Azurite
variable {R : Type _} {n : Nat}

/-! ### Auxiliary nsmul/zsmul -/

def nsmulAz [AddMonoid R] (k : Nat) (v : AzVector R n) : AzVector R n :=
  AzVector.ofFn (k • v.toFn)

def zsmulAz [SubNegMonoid R] (k : Int) (v : AzVector R n) : AzVector R n :=
  AzVector.ofFn (k • v.toFn)

private theorem toFn_nsmulAz [AddMonoid R] (v : AzVector R n) (k : Nat) :
    (nsmulAz k v).toFn = k • v.toFn := by
  ext i; simp [nsmulAz, AzVector.toFn, AzVector.ofFn, Vector.get]
  rfl

private theorem toFn_zsmulAz [SubNegMonoid R] (v : AzVector R n) (k : Int) :
    (zsmulAz k v).toFn = k • v.toFn := by
  ext i; simp [zsmulAz, AzVector.toFn, AzVector.ofFn, Vector.get]
  rfl

/-! ### AddCommMonoid -/

/-- `AzVector R n` forms an additive commutative monoid. -/
noncomputable instance instAzVectorAddCommMonoid [AddCommMonoid R] : AddCommMonoid (AzVector R n) :=
  letI : SMul Nat (AzVector R n) := ⟨fun k v => nsmulAz k v⟩
  Function.Injective.addCommMonoid AzVector.toFn AzVector.toFn_injective
    AzVector.toFn_zero AzVector.toFn_add toFn_nsmulAz

/-! ### AddCommGroup -/

/-- `AzVector R n` forms an additive commutative group. -/
noncomputable instance instAzVectorAddCommGroup [AddCommGroup R] : AddCommGroup (AzVector R n) :=
  letI : SMul Nat (AzVector R n) := ⟨fun k v => nsmulAz k v⟩
  letI : SMul Int (AzVector R n) := ⟨fun k v => zsmulAz k v⟩
  Function.Injective.addCommGroup AzVector.toFn AzVector.toFn_injective
    AzVector.toFn_zero AzVector.toFn_add AzVector.toFn_neg AzVector.toFn_sub
    toFn_nsmulAz toFn_zsmulAz

/-! ### Module -/

/-- `AzVector R n` forms an `R`-module when `R` is a commutative semiring. -/
noncomputable instance instAzVectorModule [CommSemiring R] : Module R (AzVector R n) :=
  Function.Injective.module R
    { toFun := AzVector.toFn,
      map_zero' := AzVector.toFn_zero,
      map_add' := AzVector.toFn_add}
    AzVector.toFn_injective AzVector.toFn_smul

/-! ### Linear map -/

/-- The canonical `R`-linear map from `AzVector R n` to `Fin n → R`. -/
noncomputable def AzVector.toFnLM [CommSemiring R] : AzVector R n →ₗ[R] (Fin n → R) where
  toFun := AzVector.toFn
  map_add' := AzVector.toFn_add
  map_smul' := AzVector.toFn_smul

/-! ### Linear equivalence -/

/-- The `R`-linear equivalence between `AzVector R n` and `Fin n → R`. -/
noncomputable def AzVector.linearEquivPi [CommSemiring R] :
    AzVector R n ≃ₗ[R] (Fin n → R) :=
  { AzVector.toFnLM with
    invFun := AzVector.ofFn
    left_inv := AzVector.ofFn_toFn
    right_inv := fun f => funext (AzVector.toFn_ofFn f) }

@[simp]
theorem AzVector.linearEquivPi_apply [CommSemiring R] (v : AzVector R n) :
    AzVector.linearEquivPi v = v.toFn := rfl

@[simp]
theorem AzVector.linearEquivPi_symm_apply [CommSemiring R] (f : Fin n → R) :
    AzVector.linearEquivPi.symm f = AzVector.ofFn f := rfl

end Azurite
