/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Algebraic typeclass instances for `AzMvPolynomial`.

  Uses `Function.Injective.commSemiring` and `.commRing` to transfer the
  algebraic structure from `MvPolynomial (Fin n) R` to
  `AzMvPolynomial n R ord` via the injective `toMvPoly` map.

  All instances are computable. Each parent class instance is defined at
  top level using `fast_instance%`, following the pattern used in
  Mathlib's `MeasureTheory.Function.SimpleFunc`. This is needed so that
  `fast_instance%` can substitute parent instances into the constructor
  application, avoiding any reference to the noncomputable `toMvPoly`
  in the resulting term.
-/
import Azurite.AzMvPolynomial.Equiv.Add
import Azurite.AzMvPolynomial.Equiv.Mul
import Azurite.AzMvPolynomial.Equiv.Neg
import Azurite.AzMvPolynomial.Equiv.Sub
import Azurite.AzMvPolynomial.Equiv.Pow
import Azurite.AzMvPolynomial.Equiv.SMul
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.FastInstance

namespace Azurite
open AzMvPolynomial

/-! ### Computable nat-related data instances -/

section NatData

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Computable `ℕ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def AzMvPolynomial.natCastAz (k : ℕ) : AzMvPolynomial n R ord :=
  AzMvPolynomial.C ((k : R))

instance : NatCast (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.natCastAz⟩

/-- Computable `ℕ`-action on `AzMvPolynomial`: scales every coefficient by
    `(k : R)` via the existing `AzMvPolynomial.smul`. -/
@[irreducible] def AzMvPolynomial.nsmulAz (k : ℕ) (p : AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord :=
  AzMvPolynomial.smul ((k : R)) p

instance : SMul ℕ (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.nsmulAz⟩

end NatData

/-! ### Computable Pow instance -/

section PowData

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

instance : Pow (AzMvPolynomial n R ord) ℕ := ⟨fun p k => p.pow k⟩

end PowData

/-! ### Computable int-related data instances -/

section IntData

variable {R : Type _} [CommRing R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Computable `ℤ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def AzMvPolynomial.intCastAz (k : ℤ) : AzMvPolynomial n R ord :=
  AzMvPolynomial.C ((k : R))

instance : IntCast (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.intCastAz⟩

/-- Computable `ℤ`-action on `AzMvPolynomial`. -/
@[irreducible] def AzMvPolynomial.zsmulAz (k : ℤ) (p : AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord :=
  AzMvPolynomial.smul ((k : R)) p

instance : SMul ℤ (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.zsmulAz⟩

end IntData

/-! ### Compatibility lemmas for the data instances -/

section EquivLemmasSemiring

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [NoZeroDivisors R] in
theorem toMvPoly_nsmul (k : ℕ) (p : AzMvPolynomial n R ord) :
    AzMvPolynomial.toMvPoly (k • p) = k • AzMvPolynomial.toMvPoly p := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.nsmulAz k p) = _
  unfold AzMvPolynomial.nsmulAz
  show AzMvPolynomial.toMvPoly (((k : R)) • p) = _
  rw [toMvPoly_smul]
  exact Nat.cast_smul_eq_nsmul (R := R) _ _

omit [NoZeroDivisors R] in
theorem toMvPoly_natCast (k : ℕ) :
    AzMvPolynomial.toMvPoly ((k : AzMvPolynomial n R ord)) =
    (k : MvPolynomial (Fin n) R) := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.natCastAz k) = _
  unfold AzMvPolynomial.natCastAz
  rw [toMvPoly_C]
  simp

end EquivLemmasSemiring

section EquivLemmasRing

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [NoZeroDivisors R] in
theorem toMvPoly_zsmul (k : ℤ) (p : AzMvPolynomial n R ord) :
    AzMvPolynomial.toMvPoly (k • p) = k • AzMvPolynomial.toMvPoly p := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.zsmulAz k p) = _
  unfold AzMvPolynomial.zsmulAz
  show AzMvPolynomial.toMvPoly (((k : R)) • p) = _
  rw [toMvPoly_smul]
  exact Int.cast_smul_eq_zsmul (R := R) _ _

omit [NoZeroDivisors R] in
theorem toMvPoly_intCast (k : ℤ) :
    AzMvPolynomial.toMvPoly ((k : AzMvPolynomial n R ord)) =
    (k : MvPolynomial (Fin n) R) := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.intCastAz k) = _
  unfold AzMvPolynomial.intCastAz
  rw [toMvPoly_C]
  simp

end EquivLemmasRing

/-! ### Algebraic instances chain (CommSemiring) -/

section CommSemiringSection

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

instance : AddMonoid (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.addMonoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add (fun _ _ => toMvPoly_nsmul _ _)

instance instAzMvPolynomialAddCommMonoid : AddCommMonoid (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.addCommMonoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add (fun _ _ => toMvPoly_nsmul _ _)

instance : Monoid (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.monoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_one toMvPoly_mul toMvPoly_pow

instance : CommMonoid (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.commMonoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_one toMvPoly_mul toMvPoly_pow

instance : NonUnitalNonAssocSemiring (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonUnitalNonAssocSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul (fun _ _ => toMvPoly_nsmul _ _)

instance : NonUnitalSemiring (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonUnitalSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul (fun _ _ => toMvPoly_nsmul _ _)

instance : NonAssocSemiring (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonAssocSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul
    (fun _ _ => toMvPoly_nsmul _ _) toMvPoly_natCast

instance : NonUnitalCommSemiring (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonUnitalCommSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul (fun _ _ => toMvPoly_nsmul _ _)

/-- `AzMvPolynomial n R ord` forms a semiring when `R` is a commutative semiring
    with no zero divisors. -/
instance instAzMvPolynomialSemiring : Semiring (AzMvPolynomial n R ord) where
  __ := (inferInstance : NonUnitalSemiring (AzMvPolynomial n R ord))
  one_mul := one_mul
  mul_one := mul_one
  npow := fun n p => p ^ n
  npow_zero := fun _ => pow_zero _
  npow_succ := fun _ _ => pow_succ _ _
  natCast_zero := toMvPoly_injective (by
    rw [toMvPoly_natCast,
        show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero]
    simp)
  natCast_succ := fun k => toMvPoly_injective (by
    rw [toMvPoly_natCast, toMvPoly_add, toMvPoly_natCast,
        show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one]
    push_cast; ring)

/-- `AzMvPolynomial n R ord` forms a commutative semiring. -/
instance instAzMvPolynomialCommSemiring : CommSemiring (AzMvPolynomial n R ord) where
  __ := (inferInstance : Semiring (AzMvPolynomial n R ord))
  mul_comm := mul_comm

/-- The constant polynomial embedding `C : R →+* AzMvPolynomial n R ord` as a
    bundled ring homomorphism. -/
def AzMvPolynomial.CHom : R →+* AzMvPolynomial n R ord where
  toFun := AzMvPolynomial.C
  map_zero' := toMvPoly_injective (by
    rw [toMvPoly_C,
      show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
        from toMvPoly_zero]
    simp)
  map_one' := toMvPoly_injective (by
    rw [toMvPoly_C,
      show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
        from toMvPoly_one]
    simp)
  map_add' := fun r s => toMvPoly_injective (by
    rw [toMvPoly_add, toMvPoly_C, toMvPoly_C, toMvPoly_C]
    simp)
  map_mul' := fun r s => toMvPoly_injective (by
    rw [toMvPoly_mul, toMvPoly_C, toMvPoly_C, toMvPoly_C]
    simp)

/-- The canonical ring homomorphism from `AzMvPolynomial n R ord` to
    `MvPolynomial (Fin n) R`. -/
noncomputable def AzMvPolynomial.toMvPolyHom :
    AzMvPolynomial n R ord →+* MvPolynomial (Fin n) R where
  toFun := AzMvPolynomial.toMvPoly
  map_zero' := toMvPoly_zero
  map_one' := toMvPoly_one
  map_add' := toMvPoly_add
  map_mul' := toMvPoly_mul

/-- `AzMvPolynomial n R ord` has no zero divisors when `R` doesn't. Proved by
    transfer along the injective ring hom `toMvPolyHom`. -/
instance : NoZeroDivisors (AzMvPolynomial n R ord) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have h' : AzMvPolynomial.toMvPoly a * AzMvPolynomial.toMvPoly b = 0 := by
      rw [← toMvPoly_mul, h,
          show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
            from toMvPoly_zero]
    rcases mul_eq_zero.mp h' with hl | hr
    · left
      exact toMvPoly_injective (by
        rw [hl,
            show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
              from toMvPoly_zero])
    · right
      exact toMvPoly_injective (by
        rw [hr,
            show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
              from toMvPoly_zero])

/-- `AzMvPolynomial n R ord` is an `R`-algebra via the constant polynomial
    embedding `C`. -/
instance instAzMvPolynomialAlgebra : Algebra R (AzMvPolynomial n R ord) where
  algebraMap := AzMvPolynomial.CHom
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := fun r p => toMvPoly_injective (by
    rw [toMvPoly_smul, toMvPoly_mul]
    show _ = (AzMvPolynomial.CHom r).toMvPoly * _
    rw [show (AzMvPolynomial.CHom r).toMvPoly = MvPolynomial.C r
        from toMvPoly_C r]
    exact MvPolynomial.C_mul'.symm)

end CommSemiringSection

/-! ### Algebraic instances chain (CommRing) -/

section CommRingSection

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

instance : AddGroup (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.addGroup AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance instAzMvPolynomialAddCommGroup : AddCommGroup (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.addCommGroup AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : NonUnitalNonAssocRing (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonUnitalNonAssocRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : NonUnitalRing (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonUnitalRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : NonAssocRing (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonAssocRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul
    toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)
    toMvPoly_natCast toMvPoly_intCast

instance : NonUnitalCommRing (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.nonUnitalCommRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance instAzMvPolynomialRing : Ring (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.ring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul
    toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _) toMvPoly_pow
    toMvPoly_natCast toMvPoly_intCast

/-- `AzMvPolynomial n R ord` forms a commutative ring when `R` is a
    commutative ring with no zero divisors. -/
instance instAzMvPolynomialCommRing : CommRing (AzMvPolynomial n R ord) := fast_instance%
  Function.Injective.commRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul
    toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _) toMvPoly_pow
    toMvPoly_natCast toMvPoly_intCast

/-! ### Ring isomorphism -/

/-- The ring isomorphism between `AzMvPolynomial n R ord` and
    Mathlib's `MvPolynomial (Fin n) R`. -/
noncomputable def ringEquivMvPolynomial :
    AzMvPolynomial n R ord ≃+* MvPolynomial (Fin n) R where
  toFun := AzMvPolynomial.toMvPoly
  invFun := AzMvPolynomial.ofMvPoly
  left_inv := ofMvPoly_toMvPoly
  right_inv := toMvPoly_ofMvPoly
  map_mul' := toMvPoly_mul
  map_add' := toMvPoly_add

/-! ### Integral domain -/

/-- `AzMvPolynomial n R ord` is an integral domain when `R` is. -/
noncomputable instance [IsDomain R] :
    IsDomain (AzMvPolynomial n R ord) :=
  Function.Injective.isDomain AzMvPolynomial.toMvPolyHom
    (fun _ _ h => toMvPoly_injective h)

end CommRingSection

end Azurite
