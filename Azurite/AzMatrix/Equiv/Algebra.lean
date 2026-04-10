/-
  Algebraic typeclass instances for AzMatrix.

  Transfers `AddCommMonoid`, `AddCommGroup`, `Module`, `Semiring`, and `Ring`
  from Mathlib's `Matrix` to `AzMatrix` via `toFn`.
  Provides a `LinearEquiv` between `AzMatrix R m n` and `Matrix (Fin m) (Fin n) R`.

  All instances are computable. Each parent class instance is defined at top
  level using `fast_instance%`, following the pattern used in
  `AzMvPolynomial.Equiv.Algebra` and `AzPolynomial.Equiv.Algebra`. The data
  fields (`nsmul`, `zsmul`, `npow`, `natCast`, `intCast`) are defined using
  `AzMatrix.ofFn` over the corresponding Pi-level operation, marked
  `@[irreducible]` so that `whnf` does not chase the body through
  typeclass-driven machinery during unification.
-/
import Azurite.AzMatrix.Equiv.Add
import Azurite.AzMatrix.Equiv.Sub
import Azurite.AzMatrix.Equiv.Neg
import Azurite.AzMatrix.Equiv.SMul
import Azurite.AzMatrix.Equiv.Zero
import Azurite.AzMatrix.Equiv.Mul
import Azurite.AzMatrix.Equiv.Basis
import Azurite.Algorithm.FastPow
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Tactic.FastInstance

namespace Azurite

/-! ### Function-level toFn lemmas -/

section ToFnLemmas
variable {R : Type _} {m n : Nat}

theorem AzMatrix.toFn_zero' [Zero R] :
    (0 : AzMatrix R m n).toFn = 0 := by
  ext i j; exact AzMatrix.toFn_zero i j

theorem AzMatrix.toFn_add' [Add R] (M N : AzMatrix R m n) :
    (M + N).toFn = M.toFn + N.toFn := by
  ext i j; exact AzMatrix.toFn_add M N i j

theorem AzMatrix.toFn_neg' [Neg R] (M : AzMatrix R m n) :
    (-M).toFn = -M.toFn := by
  ext i j; exact AzMatrix.toFn_neg M i j

theorem AzMatrix.toFn_sub' [Sub R] (M N : AzMatrix R m n) :
    (M - N).toFn = M.toFn - N.toFn := by
  ext i j; exact AzMatrix.toFn_sub M N i j

theorem AzMatrix.toFn_smul' {α} [SMul α R] (c : α) (M : AzMatrix R m n) :
    (c • M).toFn = c • M.toFn := by
  ext i j; exact AzMatrix.toFn_smul c M i j

end ToFnLemmas

/-! ### Computable nsmul / zsmul (rectangular) -/

section RectangularData
variable {R : Type _} {m n : Nat}

/-- Computable `ℕ`-action on `AzMatrix`: maps each entry through the
    Pi-level `Nat` smul. Marked `@[irreducible]` to keep `whnf` from
    chasing it through typeclass machinery. -/
@[irreducible] def AzMatrix.nsmulAzM [AddMonoid R] (k : ℕ) (M : AzMatrix R m n) :
    AzMatrix R m n :=
  AzMatrix.ofFn (k • M.toFn)

instance [AddMonoid R] : SMul ℕ (AzMatrix R m n) := ⟨AzMatrix.nsmulAzM⟩

/-- Computable `ℤ`-action on `AzMatrix`: maps each entry through the
    Pi-level `Int` smul. -/
@[irreducible] def AzMatrix.zsmulAzM [SubNegMonoid R] (k : ℤ) (M : AzMatrix R m n) :
    AzMatrix R m n :=
  AzMatrix.ofFn (k • M.toFn)

instance [SubNegMonoid R] : SMul ℤ (AzMatrix R m n) := ⟨AzMatrix.zsmulAzM⟩

theorem AzMatrix.toFn_nsmulAzM [AddMonoid R] (k : ℕ) (M : AzMatrix R m n) :
    (k • M).toFn = k • M.toFn := by
  show (AzMatrix.nsmulAzM k M).toFn = _
  unfold AzMatrix.nsmulAzM
  ext i j; simp

theorem AzMatrix.toFn_zsmulAzM [SubNegMonoid R] (k : ℤ) (M : AzMatrix R m n) :
    (k • M).toFn = k • M.toFn := by
  show (AzMatrix.zsmulAzM k M).toFn = _
  unfold AzMatrix.zsmulAzM
  ext i j; simp

end RectangularData

/-! ### AddCommMonoid / AddCommGroup / Module (rectangular) -/

section Rectangular
variable {R : Type _} {m n : Nat}

instance [AddCommMonoid R] : AddCommMonoid (AzMatrix R m n) := fast_instance%
  Function.Injective.addCommMonoid AzMatrix.toFn AzMatrix.toFn_injective
    AzMatrix.toFn_zero' AzMatrix.toFn_add' (fun M k => AzMatrix.toFn_nsmulAzM k M)

instance [AddCommGroup R] : AddCommGroup (AzMatrix R m n) := fast_instance%
  Function.Injective.addCommGroup AzMatrix.toFn AzMatrix.toFn_injective
    AzMatrix.toFn_zero' AzMatrix.toFn_add' AzMatrix.toFn_neg' AzMatrix.toFn_sub'
    (fun M k => AzMatrix.toFn_nsmulAzM k M) (fun M k => AzMatrix.toFn_zsmulAzM k M)

/-- `AzMatrix R m n` forms an `R`-module when `R` is a commutative semiring. -/
instance [CommSemiring R] : Module R (AzMatrix R m n) :=
  Function.Injective.module R
    { toFun := AzMatrix.toFn,
      map_zero' := AzMatrix.toFn_zero',
      map_add' := AzMatrix.toFn_add' }
    AzMatrix.toFn_injective AzMatrix.toFn_smul'

/-! ### Linear map and equivalence -/

variable [CommSemiring R]

/-- The canonical `R`-linear map from `AzMatrix R m n` to `Matrix (Fin m) (Fin n) R`. -/
def AzMatrix.toMatrixLM :
    AzMatrix R m n →ₗ[R] Matrix (Fin m) (Fin n) R where
  toFun M := M.toFn
  map_add' M N := AzMatrix.toFn_add' M N
  map_smul' c M := AzMatrix.toFn_smul' c M

/-- `R`-linear equivalence between `AzMatrix R m n` and `Matrix (Fin m) (Fin n) R`. -/
def AzMatrix.linearEquivMatrix :
    AzMatrix R m n ≃ₗ[R] Matrix (Fin m) (Fin n) R :=
  { AzMatrix.toMatrixLM with
    invFun := fun f => AzMatrix.ofFn f
    left_inv := AzMatrix.ofFn_toFn
    right_inv := fun f => funext (fun i => funext (fun j => AzMatrix.toFn_ofFn f i j)) }

@[simp]
theorem AzMatrix.linearEquivMatrix_apply (M : AzMatrix R m n) :
    AzMatrix.linearEquivMatrix M = M.toFn := rfl

@[simp]
theorem AzMatrix.linearEquivMatrix_symm_apply (f : Matrix (Fin m) (Fin n) R) :
    AzMatrix.linearEquivMatrix.symm f = AzMatrix.ofFn f := rfl

end Rectangular

/-! ### Semiring for square matrices -/

section SquareData
variable {R : Type _} [CommSemiring R] {n : Nat}

/-- One (identity matrix) for square matrices. -/
instance : One (AzMatrix R n n) := ⟨AzMatrix.identity⟩

/-- Explicit homogeneous multiplication for square matrices. -/
instance instMulAzMatrixSq : Mul (AzMatrix R n n) := ⟨fun A B => A.mul B⟩

/-- Helper: view `AzMatrix R n n` as `Matrix (Fin n) (Fin n) R`. -/
def toMat (M : AzMatrix R n n) : Matrix (Fin n) (Fin n) R := M.toFn

omit [CommSemiring R] in
theorem toMat_injective :
    Function.Injective (toMat (R := R) (n := n)) := AzMatrix.toFn_injective

theorem toMat_zero : toMat (0 : AzMatrix R n n) = 0 := by
  unfold toMat; ext i j; exact AzMatrix.toFn_zero i j

theorem toMat_one : toMat (1 : AzMatrix R n n) = 1 := by
  unfold toMat; ext i j; show AzMatrix.identity.toFn i j = _
  simp [AzMatrix.identity, Matrix.one_apply]

theorem toMat_add (M N : AzMatrix R n n) :
    toMat (M + N) = toMat M + toMat N := by
  unfold toMat; ext i j; exact AzMatrix.toFn_add M N i j

theorem toMat_mul (A B : AzMatrix R n n) :
    toMat (A * B) = toMat A * toMat B := by
  unfold toMat; ext i k; show (A.mulBasecase B).toFn i k = _
  rw [AzMatrix.toFn_mulBasecase]; exact (Matrix.mul_apply ..).symm

theorem toMat_nsmul (k : ℕ) (M : AzMatrix R n n) :
    toMat (k • M) = k • toMat M := by
  show toMat (AzMatrix.nsmulAzM k M) = _
  unfold AzMatrix.nsmulAzM toMat
  ext i j; simp

/-- Computable `npow` for square matrices via binary exponentiation.
    O(log k) matrix multiplications. -/
@[irreducible] def npowSq (A : AzMatrix R n n) (k : ℕ) : AzMatrix R n n :=
  Azurite.fastPow A k

instance : Pow (AzMatrix R n n) ℕ := ⟨npowSq⟩

/-- `toMat` preserves the tail-recursive `fastPowAux` helper. -/
theorem toMat_fastPowAux (acc base : AzMatrix R n n) (k : ℕ) :
    toMat (Azurite.fastPowAux acc base k) = toMat acc * toMat base ^ k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | _ k ih =>
    unfold Azurite.fastPowAux
    split
    · rename_i h; subst h; simp [pow_zero, mul_one]
    · rename_i h
      split
      · rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        rw [toMat_mul, show toMat base * toMat base = toMat base ^ 2 from (sq _).symm,
            ← pow_mul]
        congr 2; omega
      · rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        rw [toMat_mul, toMat_mul, mul_assoc]; congr 1
        rw [show toMat base * toMat base = toMat base ^ 2 from (sq _).symm,
            ← pow_mul, ← pow_succ']
        congr 1; omega

theorem toMat_npow (A : AzMatrix R n n) (k : ℕ) :
    toMat (A ^ k) = toMat A ^ k := by
  show toMat (npowSq A k) = _
  unfold npowSq
  rw [Azurite.fastPow, toMat_fastPowAux, toMat_one, one_mul]

/-- Computable `ℕ`-cast: returns the constant matrix `(k : Matrix _ _ R)`. -/
@[irreducible] def natCastSq (k : ℕ) : AzMatrix R n n :=
  AzMatrix.ofFn ((k : Matrix (Fin n) (Fin n) R))

instance : NatCast (AzMatrix R n n) := ⟨natCastSq⟩

theorem toMat_natCast (k : ℕ) :
    toMat ((k : AzMatrix R n n)) = (k : Matrix (Fin n) (Fin n) R) := by
  show toMat (natCastSq k) = _
  unfold toMat natCastSq
  ext i j; simp

end SquareData

/-! ### Semiring instance chain -/

section SemiringSection
variable {R : Type _} [CommSemiring R] {n : Nat}

instance : AddMonoid (AzMatrix R n n) := fast_instance%
  Function.Injective.addMonoid toMat toMat_injective
    toMat_zero toMat_add (fun _ _ => toMat_nsmul _ _)

instance : Monoid (AzMatrix R n n) := fast_instance%
  Function.Injective.monoid toMat toMat_injective
    toMat_one toMat_mul toMat_npow

instance : NonUnitalNonAssocSemiring (AzMatrix R n n) := fast_instance%
  Function.Injective.nonUnitalNonAssocSemiring toMat toMat_injective
    toMat_zero toMat_add toMat_mul (fun _ _ => toMat_nsmul _ _)

instance : NonUnitalSemiring (AzMatrix R n n) := fast_instance%
  Function.Injective.nonUnitalSemiring toMat toMat_injective
    toMat_zero toMat_add toMat_mul (fun _ _ => toMat_nsmul _ _)

instance : NonAssocSemiring (AzMatrix R n n) := fast_instance%
  Function.Injective.nonAssocSemiring toMat toMat_injective
    toMat_zero toMat_one toMat_add toMat_mul (fun _ _ => toMat_nsmul _ _) toMat_natCast

/-- `AzMatrix R n n` forms a semiring when `R` is a commutative semiring.

    Constructed manually rather than via `Function.Injective.semiring` because
    that abbrev's `npow` field would otherwise pull in
    `Function.Injective.monoidWithZero` and force the instance to be
    noncomputable. -/
instance : Semiring (AzMatrix R n n) where
  __ := (inferInstance : NonUnitalSemiring (AzMatrix R n n))
  one_mul := one_mul
  mul_one := mul_one
  npow := fun n p => p ^ n
  npow_zero := fun _ => pow_zero _
  npow_succ := fun _ _ => pow_succ _ _
  natCast_zero := toMat_injective (by
    rw [toMat_natCast, toMat_zero]; simp)
  natCast_succ := fun k => toMat_injective (by
    rw [toMat_natCast, toMat_add, toMat_natCast, toMat_one]
    exact Nat.cast_succ k)

end SemiringSection

/-! ### Ring instance chain (square matrices over a CommRing) -/

section RingSection
variable {R : Type _} [CommRing R] {n : Nat}

theorem toMat_neg (M : AzMatrix R n n) :
    toMat (-M) = -toMat M := by
  unfold toMat; ext i j; exact AzMatrix.toFn_neg M i j

theorem toMat_sub (M N : AzMatrix R n n) :
    toMat (M - N) = toMat M - toMat N := by
  unfold toMat; ext i j; exact AzMatrix.toFn_sub M N i j

theorem toMat_zsmul (M : AzMatrix R n n) (k : ℤ) :
    toMat (k • M) = k • toMat M := by
  show toMat (AzMatrix.zsmulAzM k M) = _
  unfold AzMatrix.zsmulAzM toMat
  ext i j; simp

/-- Computable `ℤ`-cast: returns the constant matrix `(k : Matrix _ _ R)`. -/
@[irreducible] def intCastSq (k : ℤ) : AzMatrix R n n :=
  AzMatrix.ofFn ((k : Matrix (Fin n) (Fin n) R))

instance : IntCast (AzMatrix R n n) := ⟨intCastSq⟩

theorem toMat_intCast (k : ℤ) :
    toMat ((k : AzMatrix R n n)) = (k : Matrix (Fin n) (Fin n) R) := by
  show toMat (intCastSq k) = _
  unfold toMat intCastSq
  ext i j; simp

instance : AddGroup (AzMatrix R n n) := fast_instance%
  Function.Injective.addGroup toMat toMat_injective
    toMat_zero toMat_add toMat_neg toMat_sub
    (fun _ _ => toMat_nsmul _ _) (fun _ _ => toMat_zsmul _ _)

instance : NonUnitalNonAssocRing (AzMatrix R n n) := fast_instance%
  Function.Injective.nonUnitalNonAssocRing toMat toMat_injective
    toMat_zero toMat_add toMat_mul toMat_neg toMat_sub
    (fun _ _ => toMat_nsmul _ _) (fun _ _ => toMat_zsmul _ _)

instance : NonUnitalRing (AzMatrix R n n) := fast_instance%
  Function.Injective.nonUnitalRing toMat toMat_injective
    toMat_zero toMat_add toMat_mul toMat_neg toMat_sub
    (fun _ _ => toMat_nsmul _ _) (fun _ _ => toMat_zsmul _ _)

instance : NonAssocRing (AzMatrix R n n) := fast_instance%
  Function.Injective.nonAssocRing toMat toMat_injective
    toMat_zero toMat_one toMat_add toMat_mul toMat_neg toMat_sub
    (fun _ _ => toMat_nsmul _ _) (fun _ _ => toMat_zsmul _ _) toMat_natCast toMat_intCast

instance : AddGroupWithOne (AzMatrix R n n) := fast_instance%
  Function.Injective.addGroupWithOne toMat toMat_injective
    toMat_zero toMat_one toMat_add toMat_neg toMat_sub
    (fun _ _ => toMat_nsmul _ _) (fun _ _ => toMat_zsmul _ _) toMat_natCast toMat_intCast

/-- `AzMatrix R n n` forms a ring when `R` is a commutative ring. -/
instance : Ring (AzMatrix R n n) := fast_instance%
  Function.Injective.ring toMat toMat_injective
    toMat_zero toMat_one toMat_add toMat_mul toMat_neg toMat_sub
    (fun _ _ => toMat_nsmul _ _) (fun _ _ => toMat_zsmul _ _) toMat_npow
    toMat_natCast toMat_intCast

end RingSection

end Azurite
