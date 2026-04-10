/-
  Algebraic typeclass instances for AzMvPolynomial.

  Uses `Function.Injective.commSemiring` and `.commRing` to transfer the
  algebraic structure from `MvPolynomial σ R` to `AzMvPolynomial σ R ord`
  via the injective `toMvPoly` map.

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
import Mathlib.Tactic.FastInstance

namespace Azurite
open AzMvPolynomial

/-! ### Computable nat-related data instances

    These delegate to the efficient `R`-scalar multiplication and constant
    constructors rather than building things up with repeated addition. -/

section NatData

variable {R : Type _} [CommSemiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Computable `ℕ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def AzMvPolynomial.natCastAz (k : ℕ) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.C ((k : R))

instance : NatCast (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.natCastAz⟩

/-- Computable `ℕ`-action on `AzMvPolynomial`: scales every coefficient by
    `(k : R)` via the existing `AzMvPolynomial.smul`. O(numTerms) (plus the
    cost of one nat-cast in `R`), instead of the O(k · numTerms)
    repeated-addition version.

    Marked `@[irreducible]` so that `whnf` does not chase the body through
    typeclass-driven `Nat.cast` and `smul` machinery during unification. -/
@[irreducible] def AzMvPolynomial.nsmulAz (k : ℕ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial σ R ord :=
  AzMvPolynomial.smul ((k : R)) p

instance : SMul ℕ (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.nsmulAz⟩

end NatData

/-! ### Computable Pow instance -/

section PowData

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

instance : Pow (AzMvPolynomial σ R ord) ℕ := ⟨fun p n => p.pow n⟩

end PowData

/-! ### Computable int-related data instances -/

section IntData

variable {R : Type _} [CommRing R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Computable `ℤ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def AzMvPolynomial.intCastAz (k : ℤ) : AzMvPolynomial σ R ord :=
  AzMvPolynomial.C ((k : R))

instance : IntCast (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.intCastAz⟩

/-- Computable `ℤ`-action on `AzMvPolynomial`: scales every coefficient by
    `(k : R)` via the existing `AzMvPolynomial.smul`.

    Marked `@[irreducible]` (see `nsmulAz` for rationale). -/
@[irreducible] def AzMvPolynomial.zsmulAz (k : ℤ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial σ R ord :=
  AzMvPolynomial.smul ((k : R)) p

instance : SMul ℤ (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.zsmulAz⟩

end IntData

/-! ### Compatibility lemmas for the data instances -/

section EquivLemmasSemiring

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

omit [NoZeroDivisors R] in
theorem toMvPoly_nsmul (k : ℕ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.toMvPoly (k • p) = k • AzMvPolynomial.toMvPoly p := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.nsmulAz k p) = _
  unfold AzMvPolynomial.nsmulAz
  show AzMvPolynomial.toMvPoly (((k : R)) • p) = _
  rw [toMvPoly_smul]
  exact Nat.cast_smul_eq_nsmul (R := R) _ _

omit [NoZeroDivisors R] in
theorem toMvPoly_natCast (k : ℕ) :
    AzMvPolynomial.toMvPoly ((k : AzMvPolynomial σ R ord)) =
    (k : MvPolynomial σ R) := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.natCastAz k) = _
  unfold AzMvPolynomial.natCastAz
  rw [toMvPoly_C]
  simp

end EquivLemmasSemiring

section EquivLemmasRing

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

omit [NoZeroDivisors R] in
theorem toMvPoly_zsmul (k : ℤ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.toMvPoly (k • p) = k • AzMvPolynomial.toMvPoly p := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.zsmulAz k p) = _
  unfold AzMvPolynomial.zsmulAz
  show AzMvPolynomial.toMvPoly (((k : R)) • p) = _
  rw [toMvPoly_smul]
  exact Int.cast_smul_eq_zsmul (R := R) _ _

omit [NoZeroDivisors R] in
theorem toMvPoly_intCast (k : ℤ) :
    AzMvPolynomial.toMvPoly ((k : AzMvPolynomial σ R ord)) =
    (k : MvPolynomial σ R) := by
  show AzMvPolynomial.toMvPoly (AzMvPolynomial.intCastAz k) = _
  unfold AzMvPolynomial.intCastAz
  rw [toMvPoly_C]
  simp

end EquivLemmasRing

/-! ### Algebraic instances chain (CommSemiring) -/

section CommSemiringSection

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

instance : AddMonoid (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.addMonoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add (fun _ _ => toMvPoly_nsmul _ _)

instance : AddCommMonoid (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.addCommMonoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add (fun _ _ => toMvPoly_nsmul _ _)

instance : Monoid (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.monoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_one toMvPoly_mul toMvPoly_pow

instance : CommMonoid (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.commMonoid AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_one toMvPoly_mul toMvPoly_pow

instance : NonUnitalNonAssocSemiring (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonUnitalNonAssocSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul (fun _ _ => toMvPoly_nsmul _ _)

instance : NonUnitalSemiring (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonUnitalSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul (fun _ _ => toMvPoly_nsmul _ _)

instance : NonAssocSemiring (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonAssocSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul
    (fun _ _ => toMvPoly_nsmul _ _) toMvPoly_natCast

instance : NonUnitalCommSemiring (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonUnitalCommSemiring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul (fun _ _ => toMvPoly_nsmul _ _)

/-- `AzMvPolynomial σ R ord` forms a semiring when `R` is a commutative semiring with no zero
    divisors.

    Constructed manually rather than via `Function.Injective.semiring` because that abbrev's
    `npow` field would otherwise pull in `Function.Injective.monoidWithZero` and force the
    instance to be noncomputable. -/
instance : Semiring (AzMvPolynomial σ R ord) where
  __ := (inferInstance : NonUnitalSemiring (AzMvPolynomial σ R ord))
  one_mul := one_mul
  mul_one := mul_one
  npow := fun n p => p ^ n
  npow_zero := fun _ => pow_zero _
  npow_succ := fun _ _ => pow_succ _ _
  natCast_zero := toMvPoly_injective (by
    rw [toMvPoly_natCast,
        show toMvPoly (0 : AzMvPolynomial σ R ord) = (0 : MvPolynomial σ R) from toMvPoly_zero]
    simp)
  natCast_succ := fun n => toMvPoly_injective (by
    rw [toMvPoly_natCast, toMvPoly_add, toMvPoly_natCast,
        show toMvPoly (1 : AzMvPolynomial σ R ord) = (1 : MvPolynomial σ R) from toMvPoly_one]
    push_cast; ring)

/-- `AzMvPolynomial σ R ord` forms a commutative semiring when `R` is a
    commutative semiring with no zero divisors. -/
instance : CommSemiring (AzMvPolynomial σ R ord) where
  __ := (inferInstance : Semiring (AzMvPolynomial σ R ord))
  mul_comm := mul_comm

end CommSemiringSection

/-! ### Algebraic instances chain (CommRing) -/

section CommRingSection

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

instance : AddGroup (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.addGroup AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : AddCommGroup (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.addCommGroup AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : NonUnitalNonAssocRing (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonUnitalNonAssocRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : NonUnitalRing (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonUnitalRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : NonAssocRing (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonAssocRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)
    toMvPoly_natCast toMvPoly_intCast

instance : NonUnitalCommRing (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.nonUnitalCommRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)

instance : AddGroupWithOne (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.addGroupWithOne AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _)
    toMvPoly_natCast toMvPoly_intCast

instance : Ring (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.ring AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _) toMvPoly_pow
    toMvPoly_natCast toMvPoly_intCast

/-- `AzMvPolynomial σ R ord` forms a commutative ring when `R` is a
    commutative ring with no zero divisors. -/
instance : CommRing (AzMvPolynomial σ R ord) := fast_instance%
  Function.Injective.commRing AzMvPolynomial.toMvPoly toMvPoly_injective
    toMvPoly_zero toMvPoly_one toMvPoly_add toMvPoly_mul toMvPoly_neg toMvPoly_sub
    (fun _ _ => toMvPoly_nsmul _ _) (fun _ _ => toMvPoly_zsmul _ _) toMvPoly_pow
    toMvPoly_natCast toMvPoly_intCast

/-! ### Ring isomorphism -/

/-- The ring isomorphism between `AzMvPolynomial σ R ord` and Mathlib's `MvPolynomial σ R`. -/
noncomputable def ringEquivMvPolynomial :
    AzMvPolynomial σ R ord ≃+* MvPolynomial σ R where
  toFun := AzMvPolynomial.toMvPoly
  invFun := AzMvPolynomial.ofMvPoly
  left_inv := ofMvPoly_toMvPoly
  right_inv := toMvPoly_ofMvPoly
  map_mul' := toMvPoly_mul
  map_add' := toMvPoly_add

/-! ### Ring homomorphism -/

/-- The canonical ring homomorphism from `AzMvPolynomial σ R ord` to `MvPolynomial σ R`. -/
noncomputable def toMvPolyHom :
    AzMvPolynomial σ R ord →+* MvPolynomial σ R where
  toFun := AzMvPolynomial.toMvPoly
  map_zero' := toMvPoly_zero
  map_one' := toMvPoly_one
  map_add' := toMvPoly_add
  map_mul' := toMvPoly_mul

/-! ### Integral domain -/

/-- `AzMvPolynomial σ R ord` is an integral domain when `R` is. -/
noncomputable instance [IsDomain R] :
    IsDomain (AzMvPolynomial σ R ord) :=
  Function.Injective.isDomain toMvPolyHom (fun _ _ h => toMvPoly_injective h)

end CommRingSection

end Azurite
