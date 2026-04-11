/-
  Algebraic typeclass instances for `AzMvPolynomialNew`.

  Uses `Function.Injective.commSemiring` and `.commRing` to transfer the
  algebraic structure from `MvPolynomial (Fin n) R` to
  `AzMvPolynomialNew n R ord` via the injective `toMvPoly` map.

  All instances are computable. Each parent class instance is defined at
  top level using `fast_instance%`, following the pattern used in
  Mathlib's `MeasureTheory.Function.SimpleFunc`. This is needed so that
  `fast_instance%` can substitute parent instances into the constructor
  application, avoiding any reference to the noncomputable `toMvPoly`
  in the resulting term.
-/
import Azurite.AzMvPolynomial.New.Equiv.Add
import Azurite.AzMvPolynomial.New.Equiv.Mul
import Azurite.AzMvPolynomial.New.Equiv.Neg
import Azurite.AzMvPolynomial.New.Equiv.Sub
import Azurite.AzMvPolynomial.New.Equiv.Pow
import Azurite.AzMvPolynomial.New.Equiv.SMul
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.FastInstance

namespace Azurite
open AzMvPolynomialNew

/-! ### Computable nat-related data instances -/

section NatData

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Computable `ℕ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def AzMvPolynomialNew.natCastAz (k : ℕ) : AzMvPolynomialNew n R ord :=
  AzMvPolynomialNew.C ((k : R))

instance : NatCast (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.natCastAz⟩

/-- Computable `ℕ`-action on `AzMvPolynomialNew`: scales every coefficient by
    `(k : R)` via the existing `AzMvPolynomialNew.smul`. -/
@[irreducible] def AzMvPolynomialNew.nsmulAz (k : ℕ) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew n R ord :=
  AzMvPolynomialNew.smul ((k : R)) p

instance : SMul ℕ (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.nsmulAz⟩

end NatData

/-! ### Computable Pow instance -/

section PowData

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

instance : Pow (AzMvPolynomialNew n R ord) ℕ := ⟨fun p k => p.pow k⟩

end PowData

/-! ### Computable int-related data instances -/

section IntData

variable {R : Type _} [CommRing R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Computable `ℤ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def AzMvPolynomialNew.intCastAz (k : ℤ) : AzMvPolynomialNew n R ord :=
  AzMvPolynomialNew.C ((k : R))

instance : IntCast (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.intCastAz⟩

/-- Computable `ℤ`-action on `AzMvPolynomialNew`. -/
@[irreducible] def AzMvPolynomialNew.zsmulAz (k : ℤ) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew n R ord :=
  AzMvPolynomialNew.smul ((k : R)) p

instance : SMul ℤ (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.zsmulAz⟩

end IntData

/-! ### Compatibility lemmas for the data instances -/

section EquivLemmasSemiring

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [NoZeroDivisors R] in
theorem toMvPoly_nsmul_new (k : ℕ) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew.toMvPoly (k • p) = k • AzMvPolynomialNew.toMvPoly p := by
  show AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.nsmulAz k p) = _
  unfold AzMvPolynomialNew.nsmulAz
  show AzMvPolynomialNew.toMvPoly (((k : R)) • p) = _
  rw [toMvPoly_smul_new]
  exact Nat.cast_smul_eq_nsmul (R := R) _ _

omit [NoZeroDivisors R] in
theorem toMvPoly_natCast_new (k : ℕ) :
    AzMvPolynomialNew.toMvPoly ((k : AzMvPolynomialNew n R ord)) =
    (k : MvPolynomial (Fin n) R) := by
  show AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.natCastAz k) = _
  unfold AzMvPolynomialNew.natCastAz
  rw [toMvPoly_C_new]
  simp

end EquivLemmasSemiring

section EquivLemmasRing

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

omit [NoZeroDivisors R] in
theorem toMvPoly_zsmul_new (k : ℤ) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew.toMvPoly (k • p) = k • AzMvPolynomialNew.toMvPoly p := by
  show AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.zsmulAz k p) = _
  unfold AzMvPolynomialNew.zsmulAz
  show AzMvPolynomialNew.toMvPoly (((k : R)) • p) = _
  rw [toMvPoly_smul_new]
  exact Int.cast_smul_eq_zsmul (R := R) _ _

omit [NoZeroDivisors R] in
theorem toMvPoly_intCast_new (k : ℤ) :
    AzMvPolynomialNew.toMvPoly ((k : AzMvPolynomialNew n R ord)) =
    (k : MvPolynomial (Fin n) R) := by
  show AzMvPolynomialNew.toMvPoly (AzMvPolynomialNew.intCastAz k) = _
  unfold AzMvPolynomialNew.intCastAz
  rw [toMvPoly_C_new]
  simp

end EquivLemmasRing

/-! ### Algebraic instances chain (CommSemiring) -/

section CommSemiringSection

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

instance : AddMonoid (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.addMonoid AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new (fun _ _ => toMvPoly_nsmul_new _ _)

instance : AddCommMonoid (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.addCommMonoid AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new (fun _ _ => toMvPoly_nsmul_new _ _)

instance : Monoid (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.monoid AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_one_new toMvPoly_mul_new toMvPoly_pow_new

instance : CommMonoid (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.commMonoid AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_one_new toMvPoly_mul_new toMvPoly_pow_new

instance : NonUnitalNonAssocSemiring (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonUnitalNonAssocSemiring AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_mul_new (fun _ _ => toMvPoly_nsmul_new _ _)

instance : NonUnitalSemiring (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonUnitalSemiring AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_mul_new (fun _ _ => toMvPoly_nsmul_new _ _)

instance : NonAssocSemiring (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonAssocSemiring AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_one_new toMvPoly_add_new toMvPoly_mul_new
    (fun _ _ => toMvPoly_nsmul_new _ _) toMvPoly_natCast_new

instance : NonUnitalCommSemiring (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonUnitalCommSemiring AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_mul_new (fun _ _ => toMvPoly_nsmul_new _ _)

/-- `AzMvPolynomialNew n R ord` forms a semiring when `R` is a commutative semiring
    with no zero divisors. -/
instance : Semiring (AzMvPolynomialNew n R ord) where
  __ := (inferInstance : NonUnitalSemiring (AzMvPolynomialNew n R ord))
  one_mul := one_mul
  mul_one := mul_one
  npow := fun n p => p ^ n
  npow_zero := fun _ => pow_zero _
  npow_succ := fun _ _ => pow_succ _ _
  natCast_zero := toMvPoly_injective_new (by
    rw [toMvPoly_natCast_new,
        show (0 : AzMvPolynomialNew n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero_new]
    simp)
  natCast_succ := fun k => toMvPoly_injective_new (by
    rw [toMvPoly_natCast_new, toMvPoly_add_new, toMvPoly_natCast_new,
        show (1 : AzMvPolynomialNew n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one_new]
    push_cast; ring)

/-- `AzMvPolynomialNew n R ord` forms a commutative semiring. -/
instance : CommSemiring (AzMvPolynomialNew n R ord) where
  __ := (inferInstance : Semiring (AzMvPolynomialNew n R ord))
  mul_comm := mul_comm

/-- The constant polynomial embedding `C : R →+* AzMvPolynomialNew n R ord` as a
    bundled ring homomorphism. -/
def AzMvPolynomialNew.CHom : R →+* AzMvPolynomialNew n R ord where
  toFun := AzMvPolynomialNew.C
  map_zero' := toMvPoly_injective_new (by
    rw [toMvPoly_C_new,
      show (0 : AzMvPolynomialNew n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
        from toMvPoly_zero_new]
    simp)
  map_one' := toMvPoly_injective_new (by
    rw [toMvPoly_C_new,
      show (1 : AzMvPolynomialNew n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
        from toMvPoly_one_new]
    simp)
  map_add' := fun r s => toMvPoly_injective_new (by
    rw [toMvPoly_add_new, toMvPoly_C_new, toMvPoly_C_new, toMvPoly_C_new]
    simp)
  map_mul' := fun r s => toMvPoly_injective_new (by
    rw [toMvPoly_mul_new, toMvPoly_C_new, toMvPoly_C_new, toMvPoly_C_new]
    simp)

/-- The canonical ring homomorphism from `AzMvPolynomialNew n R ord` to
    `MvPolynomial (Fin n) R`. -/
noncomputable def AzMvPolynomialNew.toMvPolyHom :
    AzMvPolynomialNew n R ord →+* MvPolynomial (Fin n) R where
  toFun := AzMvPolynomialNew.toMvPoly
  map_zero' := toMvPoly_zero_new
  map_one' := toMvPoly_one_new
  map_add' := toMvPoly_add_new
  map_mul' := toMvPoly_mul_new

/-- `AzMvPolynomialNew n R ord` is an `R`-algebra via the constant polynomial
    embedding `C`. -/
instance : Algebra R (AzMvPolynomialNew n R ord) where
  algebraMap := AzMvPolynomialNew.CHom
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := fun r p => toMvPoly_injective_new (by
    rw [toMvPoly_smul_new, toMvPoly_mul_new]
    show _ = (AzMvPolynomialNew.CHom r).toMvPoly * _
    rw [show (AzMvPolynomialNew.CHom r).toMvPoly = MvPolynomial.C r
        from toMvPoly_C_new r]
    exact MvPolynomial.C_mul'.symm)

end CommSemiringSection

/-! ### Algebraic instances chain (CommRing) -/

section CommRingSection

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

instance : AddGroup (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.addGroup AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)

instance : AddCommGroup (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.addCommGroup AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)

instance : NonUnitalNonAssocRing (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonUnitalNonAssocRing AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_mul_new toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)

instance : NonUnitalRing (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonUnitalRing AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_mul_new toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)

instance : NonAssocRing (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonAssocRing AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_one_new toMvPoly_add_new toMvPoly_mul_new
    toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)
    toMvPoly_natCast_new toMvPoly_intCast_new

instance : NonUnitalCommRing (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.nonUnitalCommRing AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_add_new toMvPoly_mul_new toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)

instance : AddGroupWithOne (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.addGroupWithOne AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_one_new toMvPoly_add_new toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _)
    toMvPoly_natCast_new toMvPoly_intCast_new

instance : Ring (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.ring AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_one_new toMvPoly_add_new toMvPoly_mul_new
    toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _) toMvPoly_pow_new
    toMvPoly_natCast_new toMvPoly_intCast_new

/-- `AzMvPolynomialNew n R ord` forms a commutative ring when `R` is a
    commutative ring with no zero divisors. -/
instance : CommRing (AzMvPolynomialNew n R ord) := fast_instance%
  Function.Injective.commRing AzMvPolynomialNew.toMvPoly toMvPoly_injective_new
    toMvPoly_zero_new toMvPoly_one_new toMvPoly_add_new toMvPoly_mul_new
    toMvPoly_neg_new toMvPoly_sub_new
    (fun _ _ => toMvPoly_nsmul_new _ _) (fun _ _ => toMvPoly_zsmul_new _ _) toMvPoly_pow_new
    toMvPoly_natCast_new toMvPoly_intCast_new

/-! ### Ring isomorphism -/

/-- The ring isomorphism between `AzMvPolynomialNew n R ord` and
    Mathlib's `MvPolynomial (Fin n) R`. -/
noncomputable def ringEquivMvPolynomialNew :
    AzMvPolynomialNew n R ord ≃+* MvPolynomial (Fin n) R where
  toFun := AzMvPolynomialNew.toMvPoly
  invFun := AzMvPolynomialNew.ofMvPoly
  left_inv := ofMvPoly_toMvPoly_new
  right_inv := toMvPoly_ofMvPoly_new
  map_mul' := toMvPoly_mul_new
  map_add' := toMvPoly_add_new

/-! ### Integral domain -/

/-- `AzMvPolynomialNew n R ord` is an integral domain when `R` is. -/
noncomputable instance [IsDomain R] :
    IsDomain (AzMvPolynomialNew n R ord) :=
  Function.Injective.isDomain AzMvPolynomialNew.toMvPolyHom
    (fun _ _ h => toMvPoly_injective_new h)

end CommRingSection

end Azurite
