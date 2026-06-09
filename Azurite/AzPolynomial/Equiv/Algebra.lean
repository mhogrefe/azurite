import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Neg
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Equiv.SMul
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.Algorithm.SlidingWindowPow
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.FastInstance

/-!
# Algebraic typeclass instances for AzPolynomial

Uses `Function.Injective.semiring` etc. to transfer the algebraic structure
from `Polynomial R` to `AzPolynomial R` via the injective `toPoly` map.

All instances are computable. The data fields (`nsmul`, `npow`, `natCast`,
`zsmul`, `intCast`) are defined using the existing computable operations on
`AzPolynomial` (`smul`, `fastPow`, `C`) rather than via the noncomputable
round-trip through `ofPoly`/`toPoly`.

Each parent class instance is defined at top level using `fast_instance%`,
following the pattern used in `AzMvPolynomial.Equiv.Algebra` and Mathlib's
`MeasureTheory.Function.SimpleFunc`.
-/

open Polynomial

namespace Azurite.AzPolynomial

/-! ### Computable nat-related data instances -/

section NatData

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Computable `ℕ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def natCastAz (k : ℕ) : AzPolynomial R :=
  AzPolynomial.C ((k : R))

instance : NatCast (AzPolynomial R) := ⟨natCastAz⟩

/-- Computable `ℕ`-action on `AzPolynomial`: scales every coefficient by
    `(k : R)` via the existing `AzPolynomial.smul`. O(numCoeffs) (plus the
    cost of one nat-cast in `R`), instead of the O(k · numCoeffs)
    repeated-addition version.

    Marked `@[irreducible]` so that `whnf` does not chase the body through
    typeclass-driven `Nat.cast` and `smul` machinery during unification. -/
@[irreducible] def nsmulAz (k : ℕ) (p : AzPolynomial R) : AzPolynomial R :=
  ((k : R)) • p

instance : SMul ℕ (AzPolynomial R) := ⟨nsmulAz⟩

end NatData

/-! ### Computable Pow instance -/

section PowData

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Computable `npow` for `AzPolynomial` via sliding-window exponentiation.
    O(log n) polynomial multiplications. -/
@[irreducible] def npowAz (p : AzPolynomial R) (n : ℕ) : AzPolynomial R :=
  Azurite.slidingWindowPow p n

instance : Pow (AzPolynomial R) ℕ := ⟨npowAz⟩

end PowData

/-! ### Computable int-related data instances -/

section IntData

variable {R : Type _} [Ring R] [DecidableEq R]

/-- Computable `ℤ`-cast: returns the constant polynomial `(k : R)`. O(1). -/
@[irreducible] def intCastAz (k : ℤ) : AzPolynomial R :=
  AzPolynomial.C ((k : R))

instance : IntCast (AzPolynomial R) := ⟨intCastAz⟩

/-- Computable `ℤ`-action on `AzPolynomial`: scales every coefficient by
    `(k : R)` via the existing `AzPolynomial.smul`.

    Marked `@[irreducible]` (see `nsmulAz` for rationale). -/
@[irreducible] def zsmulAz (k : ℤ) (p : AzPolynomial R) : AzPolynomial R :=
  ((k : R)) • p

instance : SMul ℤ (AzPolynomial R) := ⟨zsmulAz⟩

end IntData

/-! ### Compatibility lemmas for the data instances -/

section EquivLemmasSemiring

variable {R : Type _} [Semiring R] [DecidableEq R]

theorem toPoly_nsmul (k : ℕ) (p : AzPolynomial R) :
    AzPolynomial.toPoly (k • p) = k • AzPolynomial.toPoly p := by
  show AzPolynomial.toPoly (nsmulAz k p) = _
  unfold nsmulAz
  show AzPolynomial.toPoly (((k : R)) • p) = _
  rw [toPoly_smul]
  exact Nat.cast_smul_eq_nsmul (R := R) _ _

theorem toPoly_natCast (k : ℕ) :
    AzPolynomial.toPoly ((k : AzPolynomial R)) = (k : Polynomial R) := by
  show AzPolynomial.toPoly (natCastAz k) = _
  unfold natCastAz
  rw [toPoly_C]
  simp

/-- `toPoly` preserves sliding-window exponentiation — the `f = toPoly` case of the generic
`map_slidingWindowPow`, no re-induction needed. -/
theorem toPoly_npow (p : AzPolynomial R) (n : ℕ) :
    AzPolynomial.toPoly (p ^ n) = AzPolynomial.toPoly p ^ n := by
  show AzPolynomial.toPoly (npowAz p n) = _
  unfold npowAz
  exact Azurite.map_slidingWindowPow AzPolynomial.toPoly toPoly_one toPoly_mul p n

end EquivLemmasSemiring

section EquivLemmasRing

variable {R : Type _} [Ring R] [DecidableEq R]

theorem toPoly_zsmul (k : ℤ) (p : AzPolynomial R) :
    AzPolynomial.toPoly (k • p) = k • AzPolynomial.toPoly p := by
  show AzPolynomial.toPoly (zsmulAz k p) = _
  unfold zsmulAz
  show AzPolynomial.toPoly (((k : R)) • p) = _
  rw [toPoly_smul]
  exact Int.cast_smul_eq_zsmul (R := R) _ _

theorem toPoly_intCast (k : ℤ) :
    AzPolynomial.toPoly ((k : AzPolynomial R)) = (k : Polynomial R) := by
  show AzPolynomial.toPoly (intCastAz k) = _
  unfold intCastAz
  rw [toPoly_C]
  simp

end EquivLemmasRing

/-! ### Algebraic instances chain (Semiring) -/

section SemiringSection

variable {R : Type _} [Semiring R] [DecidableEq R]

instance : AddMonoid (AzPolynomial R) := fast_instance%
  Function.Injective.addMonoid AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add (fun _ _ => toPoly_nsmul _ _)

instance : AddCommMonoid (AzPolynomial R) := fast_instance%
  Function.Injective.addCommMonoid AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add (fun _ _ => toPoly_nsmul _ _)

instance : Monoid (AzPolynomial R) := fast_instance%
  Function.Injective.monoid AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_one toPoly_mul toPoly_npow

instance : NonUnitalNonAssocSemiring (AzPolynomial R) := fast_instance%
  Function.Injective.nonUnitalNonAssocSemiring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_mul (fun _ _ => toPoly_nsmul _ _)

instance : NonUnitalSemiring (AzPolynomial R) := fast_instance%
  Function.Injective.nonUnitalSemiring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_mul (fun _ _ => toPoly_nsmul _ _)

instance : NonAssocSemiring (AzPolynomial R) := fast_instance%
  Function.Injective.nonAssocSemiring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul
    (fun _ _ => toPoly_nsmul _ _) toPoly_natCast

/-- `AzPolynomial R` forms a semiring when `R` is a semiring.

    Constructed manually rather than via `Function.Injective.semiring` because
    that abbrev's `npow` field would otherwise pull in
    `Function.Injective.monoidWithZero` and force the instance to be
    noncomputable. -/
instance : Semiring (AzPolynomial R) where
  __ := (inferInstance : NonUnitalSemiring (AzPolynomial R))
  one_mul := one_mul
  mul_one := mul_one
  npow := fun n p => p ^ n
  npow_zero := fun _ => pow_zero _
  npow_succ := fun _ _ => pow_succ _ _
  natCast_zero := toPoly_inj.mp (by
    rw [toPoly_natCast,
        show AzPolynomial.toPoly (0 : AzPolynomial R) = (0 : Polynomial R) from toPoly_zero]
    simp)
  natCast_succ := fun n => toPoly_inj.mp (by
    rw [toPoly_natCast, toPoly_add, toPoly_natCast,
        show AzPolynomial.toPoly (1 : AzPolynomial R) = (1 : Polynomial R) from toPoly_one]
    exact Nat.cast_succ n)

end SemiringSection

/-! ### Algebraic instances chain (CommSemiring) -/

section CommSemiringSection

variable {R : Type _} [CommSemiring R] [DecidableEq R]

instance : CommMonoid (AzPolynomial R) := fast_instance%
  Function.Injective.commMonoid AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_one toPoly_mul toPoly_npow

instance : NonUnitalCommSemiring (AzPolynomial R) := fast_instance%
  Function.Injective.nonUnitalCommSemiring AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_mul (fun _ _ => toPoly_nsmul _ _)

/-- `AzPolynomial R` forms a commutative semiring when `R` is a commutative
    semiring. -/
instance : CommSemiring (AzPolynomial R) where
  __ := (inferInstance : Semiring (AzPolynomial R))
  mul_comm := mul_comm

/-- The constant polynomial embedding `C : R →+* AzPolynomial R` as a bundled
    ring homomorphism. Computable: the underlying function is just `C`. -/
def CHom : R →+* AzPolynomial R where
  toFun := C
  map_zero' := toPoly_inj.mp (by
    rw [toPoly_C,
      show AzPolynomial.toPoly (0 : AzPolynomial R) = (0 : Polynomial R) from toPoly_zero]
    exact Polynomial.C_0)
  map_one' := toPoly_inj.mp (by
    rw [toPoly_C,
      show AzPolynomial.toPoly (1 : AzPolynomial R) = (1 : Polynomial R) from toPoly_one]
    exact Polynomial.C_1)
  map_add' := fun r s => toPoly_inj.mp (by
    rw [toPoly_add, toPoly_C, toPoly_C, toPoly_C]
    exact Polynomial.C_add)
  map_mul' := fun r s => toPoly_inj.mp (by
    rw [toPoly_mul, toPoly_C, toPoly_C, toPoly_C]
    exact Polynomial.C_mul)

/-- The canonical ring homomorphism from `AzPolynomial R` to `Polynomial R`. -/
noncomputable def toPolyHom :
    AzPolynomial R →+* Polynomial R where
  toFun := AzPolynomial.toPoly
  map_zero' := toPoly_zero
  map_one' := toPoly_one
  map_add' := toPoly_add
  map_mul' := toPoly_mul

/-- `AzPolynomial R` is an `R`-algebra via the constant polynomial embedding `C`.
    The algebra map is `CHom`, and the scalar action reuses the existing
    computable `SMul R (AzPolynomial R)` instance. -/
instance : Algebra R (AzPolynomial R) where
  algebraMap := CHom
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := fun r p => toPoly_inj.mp (by
    rw [toPoly_smul, toPoly_mul]
    show _ = AzPolynomial.toPoly (CHom r) * _
    rw [show AzPolynomial.toPoly (CHom r) = Polynomial.C r from toPoly_C r]
    exact Polynomial.smul_eq_C_mul _)

/-- `AzPolynomial R` has no zero divisors when `R` doesn't. Proved by transfer
    along the injective ring hom `toPoly : AzPolynomial R → Polynomial R`. -/
instance [NoZeroDivisors R] : NoZeroDivisors (AzPolynomial R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    have h' : AzPolynomial.toPoly a * AzPolynomial.toPoly b = 0 := by
      rw [← toPoly_mul, h,
          show AzPolynomial.toPoly (0 : AzPolynomial R) = (0 : Polynomial R)
            from toPoly_zero]
    rcases mul_eq_zero.mp h' with hl | hr
    · left
      exact toPoly_inj.mp (by
        rw [hl,
            show AzPolynomial.toPoly (0 : AzPolynomial R) = (0 : Polynomial R)
              from toPoly_zero])
    · right
      exact toPoly_inj.mp (by
        rw [hr,
            show AzPolynomial.toPoly (0 : AzPolynomial R) = (0 : Polynomial R)
              from toPoly_zero])

end CommSemiringSection

/-! ### Algebraic instances chain (Ring) -/

section RingSection

variable {R : Type _} [Ring R] [DecidableEq R]

instance : AddGroup (AzPolynomial R) := fast_instance%
  Function.Injective.addGroup AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _)

instance : AddCommGroup (AzPolynomial R) := fast_instance%
  Function.Injective.addCommGroup AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _)

instance : NonUnitalNonAssocRing (AzPolynomial R) := fast_instance%
  Function.Injective.nonUnitalNonAssocRing AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_mul toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _)

instance : NonUnitalRing (AzPolynomial R) := fast_instance%
  Function.Injective.nonUnitalRing AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_mul toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _)

instance : NonAssocRing (AzPolynomial R) := fast_instance%
  Function.Injective.nonAssocRing AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _)
    toPoly_natCast toPoly_intCast

instance : Ring (AzPolynomial R) := fast_instance%
  Function.Injective.ring AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _) toPoly_npow
    toPoly_natCast toPoly_intCast

end RingSection

/-! ### Algebraic instances chain (CommRing) -/

section CommRingSection

variable {R : Type _} [CommRing R] [DecidableEq R]

instance : NonUnitalCommRing (AzPolynomial R) := fast_instance%
  Function.Injective.nonUnitalCommRing AzPolynomial.toPoly
    (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_add toPoly_mul toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _)

/-- `AzPolynomial R` forms a commutative ring when `R` is a commutative ring. -/
instance : CommRing (AzPolynomial R) := fast_instance%
  Function.Injective.commRing AzPolynomial.toPoly (fun _ _ h => toPoly_inj.mp h)
    toPoly_zero toPoly_one toPoly_add toPoly_mul toPoly_neg toPoly_sub
    (fun _ _ => toPoly_nsmul _ _) (fun _ _ => toPoly_zsmul _ _) toPoly_npow
    toPoly_natCast toPoly_intCast

/-! ### Ring isomorphism -/

/-- The ring isomorphism between `AzPolynomial R` and Mathlib's `Polynomial R`. -/
noncomputable def ringEquivPolynomial :
    AzPolynomial R ≃+* Polynomial R :=
  { equivPolynomial with
    map_mul' := toPoly_mul
    map_add' := toPoly_add}

/-! ### Integral domain -/

/-- `AzPolynomial R` is an integral domain when `R` is. -/
instance [IsDomain R] : IsDomain (AzPolynomial R) :=
  Function.Injective.isDomain toPolyHom (fun _ _ h => toPoly_inj.mp h)

end CommRingSection

end Azurite.AzPolynomial
