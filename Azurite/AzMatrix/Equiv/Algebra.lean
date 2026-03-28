/-
  Algebraic typeclass instances for AzMatrix.

  Transfers `AddCommMonoid`, `AddCommGroup`, `Module`, `Semiring`, and `Ring`
  from Mathlib's `Matrix` to `AzMatrix` via `toFn`.
  Provides a `LinearEquiv` between `AzMatrix R m n` and `Matrix (Fin m) (Fin n) R`.
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

namespace Azurite

/-! ### Auxiliary nsmul/zsmul (rectangular) -/

section Rectangular
variable {R : Type _} {m n : Nat}

private def nsmulAzM [AddMonoid R] (k : Nat) (M : AzMatrix R m n) : AzMatrix R m n :=
  AzMatrix.ofFn (k • M.toFn)

private def zsmulAzM [SubNegMonoid R] (k : Int) (M : AzMatrix R m n) : AzMatrix R m n :=
  AzMatrix.ofFn (k • M.toFn)

private theorem toFn_nsmulAzM [AddMonoid R] (M : AzMatrix R m n) (k : Nat) :
    (nsmulAzM k M).toFn = k • M.toFn := by
  ext i j; simp [nsmulAzM]

private theorem toFn_zsmulAzM [SubNegMonoid R] (M : AzMatrix R m n) (k : Int) :
    (zsmulAzM k M).toFn = k • M.toFn := by
  ext i j; simp [zsmulAzM]

/-! ### Function-level toFn lemmas -/

private theorem toFn_zero' [Zero R] :
    (0 : AzMatrix R m n).toFn = 0 := by ext i j; exact AzMatrix.toFn_zero i j

private theorem toFn_add' [Add R] (M N : AzMatrix R m n) :
    (M + N).toFn = M.toFn + N.toFn := by ext i j; exact AzMatrix.toFn_add M N i j

private theorem toFn_neg' [Neg R] (M : AzMatrix R m n) :
    (-M).toFn = -M.toFn := by ext i j; exact AzMatrix.toFn_neg M i j

private theorem toFn_sub' [Sub R] (M N : AzMatrix R m n) :
    (M - N).toFn = M.toFn - N.toFn := by ext i j; exact AzMatrix.toFn_sub M N i j

private theorem toFn_smul' [SMul α R] (c : α) (M : AzMatrix R m n) :
    (c • M).toFn = c • M.toFn := by ext i j; exact AzMatrix.toFn_smul c M i j

/-! ### AddCommMonoid -/

/-- `AzMatrix R m n` forms an additive commutative monoid. -/
noncomputable instance [AddCommMonoid R] : AddCommMonoid (AzMatrix R m n) :=
  letI : SMul Nat (AzMatrix R m n) := ⟨fun k M => nsmulAzM k M⟩
  Function.Injective.addCommMonoid AzMatrix.toFn AzMatrix.toFn_injective
    toFn_zero' toFn_add' toFn_nsmulAzM

/-! ### AddCommGroup -/

/-- `AzMatrix R m n` forms an additive commutative group. -/
noncomputable instance [AddCommGroup R] : AddCommGroup (AzMatrix R m n) :=
  letI : SMul Nat (AzMatrix R m n) := ⟨fun k M => nsmulAzM k M⟩
  letI : SMul Int (AzMatrix R m n) := ⟨fun k M => zsmulAzM k M⟩
  Function.Injective.addCommGroup AzMatrix.toFn AzMatrix.toFn_injective
    toFn_zero' toFn_add' toFn_neg' toFn_sub'
    toFn_nsmulAzM toFn_zsmulAzM

/-! ### Module -/

/-- `AzMatrix R m n` forms an `R`-module when `R` is a commutative semiring. -/
noncomputable instance [CommSemiring R] : Module R (AzMatrix R m n) :=
  Function.Injective.module R
    { toFun := AzMatrix.toFn,
      map_zero' := toFn_zero',
      map_add' := toFn_add' }
    AzMatrix.toFn_injective toFn_smul'

/-! ### Linear map and equivalence -/

variable [CommSemiring R]

/-- The canonical `R`-linear map from `AzMatrix R m n` to `Matrix (Fin m) (Fin n) R`. -/
noncomputable def AzMatrix.toMatrixLM :
    AzMatrix R m n →ₗ[R] Matrix (Fin m) (Fin n) R where
  toFun M := M.toFn
  map_add' M N := toFn_add' M N
  map_smul' c M := toFn_smul' c M

/-- `R`-linear equivalence between `AzMatrix R m n` and `Matrix (Fin m) (Fin n) R`. -/
noncomputable def AzMatrix.linearEquivMatrix :
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

section Semiring
variable {R : Type _} [CommSemiring R] {n : Nat}

/-- One (identity matrix) for square matrices. -/
instance : One (AzMatrix R n n) := ⟨AzMatrix.identity⟩

/-- Explicit homogeneous multiplication for square matrices. -/
instance instMulAzMatrixSq : Mul (AzMatrix R n n) := ⟨fun A B => A.mul B⟩

/-- Helper: view `AzMatrix R n n` as `Matrix (Fin n) (Fin n) R`. -/
@[reducible] def toMat (M : AzMatrix R n n) : Matrix (Fin n) (Fin n) R := M.toFn

omit [CommSemiring R] in
private theorem toMat_injective :
    Function.Injective (toMat (R := R) (n := n)) := AzMatrix.toFn_injective

private theorem toMat_zero : toMat (0 : AzMatrix R n n) = 0 := by
  ext i j; exact AzMatrix.toFn_zero i j

theorem toMat_one : toMat (1 : AzMatrix R n n) = 1 := by
  unfold toMat; ext i j; show AzMatrix.identity.toFn i j = _
  simp [AzMatrix.identity, Matrix.one_apply]

private theorem toMat_add (M N : AzMatrix R n n) :
    toMat (M + N) = toMat M + toMat N := by ext i j; exact AzMatrix.toFn_add M N i j

theorem toMat_mul (A B : AzMatrix R n n) :
    toMat (instMulAzMatrixSq.mul A B) = toMat A * toMat B := by
  ext i k; show (A.mulBasecase B).toFn i k = _
  rw [AzMatrix.toFn_mulBasecase]; exact (Matrix.mul_apply ..).symm

omit [CommSemiring R] in
private theorem toMat_neg [Neg R] (M : AzMatrix R n n) :
    toMat (-M) = -toMat M := by ext i j; exact AzMatrix.toFn_neg M i j

omit [CommSemiring R] in
private theorem toMat_sub [Sub R] (M N : AzMatrix R n n) :
    toMat (M - N) = toMat M - toMat N := by ext i j; exact AzMatrix.toFn_sub M N i j

-- nsmul
private def nsmulSq (k : Nat) (M : AzMatrix R n n) : AzMatrix R n n :=
  AzMatrix.ofFn (k • toMat M)

private theorem toMat_nsmul (k : Nat) (M : AzMatrix R n n) :
    toMat (nsmulSq k M) = k • toMat M := by
  unfold toMat nsmulSq; ext i j; simp

-- npow (computable via exponentiation by squaring)
def npowSq (A : AzMatrix R n n) (k : Nat) : AzMatrix R n n :=
  Azurite.fastPow A k

-- Direct induction proof: toMat preserves fastPowAux
private theorem toMat_fastPowAux (acc base : AzMatrix R n n) (k : ℕ) :
    toMat (Azurite.fastPowAux acc base k) = toMat acc * toMat base ^ k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | _ k ih =>
    unfold Azurite.fastPowAux
    split
    · rename_i h; subst h; simp [pow_zero, mul_one]
    · rename_i h
      split
      · rename_i heven
        rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        show toMat acc * (toMat (instMulAzMatrixSq.mul base base)) ^ (k / 2) =
            toMat acc * toMat base ^ k
        rw [toMat_mul, show toMat base * toMat base = toMat base ^ 2 from (sq _).symm, ← pow_mul]
        congr 2; omega
      · rename_i hodd
        rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        show toMat (instMulAzMatrixSq.mul acc base) *
            (toMat (instMulAzMatrixSq.mul base base)) ^ (k / 2) =
            toMat acc * toMat base ^ k
        rw [toMat_mul, toMat_mul, mul_assoc]; congr 1
        rw [show toMat base * toMat base = toMat base ^ 2 from (sq _).symm, ← pow_mul, ← pow_succ']
        congr 1; omega

theorem toMat_npow (A : AzMatrix R n n) (k : Nat) :
    toMat (npowSq A k) = toMat A ^ k := by
  simp [npowSq, Azurite.fastPow, toMat_fastPowAux, toMat_one, one_mul]

-- natCast
private def natCastSq (k : Nat) : AzMatrix R n n :=
  AzMatrix.ofFn ((k : Matrix (Fin n) (Fin n) R))

private theorem toMat_natCast (k : Nat) :
    toMat (natCastSq k : AzMatrix R n n) = (k : Matrix (Fin n) (Fin n) R) := by
  unfold toMat natCastSq; ext i j; simp

/-- `AzMatrix R n n` forms a semiring when `R` is a commutative semiring. -/
noncomputable instance : Semiring (AzMatrix R n n) :=
  letI : SMul Nat (AzMatrix R n n) := ⟨nsmulSq⟩
  letI : Pow (AzMatrix R n n) Nat := ⟨npowSq⟩
  letI : NatCast (AzMatrix R n n) := ⟨natCastSq⟩
  Function.Injective.semiring toMat toMat_injective
    toMat_zero toMat_one toMat_add toMat_mul
    toMat_nsmul toMat_npow toMat_natCast

end Semiring

/-! ### Ring for square matrices -/

-- Separate section with ONLY [CommRing R] to avoid instance diamond with [CommSemiring R]
section Ring
variable {R : Type _} [CommRing R] {n : Nat}

-- Redefine toMat locally (private defs don't escape sections)
@[reducible] private def toMatR (M : AzMatrix R n n) : Matrix (Fin n) (Fin n) R := M.toFn

omit [CommRing R] in
private theorem toMatR_inj :
    Function.Injective (toMatR (R := R) (n := n)) := AzMatrix.toFn_injective

private theorem toMatR_zero : toMatR (0 : AzMatrix R n n) = 0 := by
  ext i j; exact AzMatrix.toFn_zero i j

private theorem toMatR_one : toMatR (1 : AzMatrix R n n) = 1 := by
  unfold toMatR; ext i j; show AzMatrix.identity.toFn i j = _
  simp [AzMatrix.identity, Matrix.one_apply]

private theorem toMatR_add (M N : AzMatrix R n n) :
    toMatR (M + N) = toMatR M + toMatR N := by ext i j; exact AzMatrix.toFn_add M N i j

private theorem toMatR_mul (A B : AzMatrix R n n) :
    toMatR (instMulAzMatrixSq.mul A B) = toMatR A * toMatR B := by
  ext i k; show (A.mulBasecase B).toFn i k = _
  rw [AzMatrix.toFn_mulBasecase]; exact (Matrix.mul_apply ..).symm

private theorem toMatR_neg (M : AzMatrix R n n) :
    toMatR (-M) = -toMatR M := by ext i j; exact AzMatrix.toFn_neg M i j

private theorem toMatR_sub (M N : AzMatrix R n n) :
    toMatR (M - N) = toMatR M - toMatR N := by ext i j; exact AzMatrix.toFn_sub M N i j

private def nsmulR (k : Nat) (M : AzMatrix R n n) : AzMatrix R n n :=
  AzMatrix.ofFn (k • toMatR M)
private theorem toMatR_nsmul (k : Nat) (M : AzMatrix R n n) :
    toMatR (nsmulR k M) = k • toMatR M := by unfold toMatR nsmulR; ext i j; simp

private def zsmulR (k : Int) (M : AzMatrix R n n) : AzMatrix R n n :=
  AzMatrix.ofFn (k • toMatR M)
private theorem toMatR_zsmul (k : Int) (M : AzMatrix R n n) :
    toMatR (zsmulR k M) = k • toMatR M := by unfold toMatR zsmulR; ext i j; simp

private def npowR (A : AzMatrix R n n) (k : Nat) : AzMatrix R n n :=
  Azurite.fastPow A k

private theorem toMatR_fastPowAux (acc base : AzMatrix R n n) (k : ℕ) :
    toMatR (Azurite.fastPowAux acc base k) = toMatR acc * toMatR base ^ k := by
  induction k using Nat.strongRecOn generalizing acc base with
  | _ k ih =>
    unfold Azurite.fastPowAux
    split
    · rename_i h; subst h; simp [pow_zero, mul_one]
    · rename_i h
      split
      · rename_i heven
        rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        show toMatR acc * (toMatR (instMulAzMatrixSq.mul base base)) ^ (k / 2) =
            toMatR acc * toMatR base ^ k
        rw [toMatR_mul, show toMatR base * toMatR base = toMatR base ^ 2 from (sq _).symm, ← pow_mul]
        congr 2; omega
      · rename_i hodd
        rw [ih (k / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        show toMatR (instMulAzMatrixSq.mul acc base) *
            (toMatR (instMulAzMatrixSq.mul base base)) ^ (k / 2) =
            toMatR acc * toMatR base ^ k
        rw [toMatR_mul, toMatR_mul, mul_assoc]; congr 1
        rw [show toMatR base * toMatR base = toMatR base ^ 2 from (sq _).symm, ← pow_mul, ← pow_succ']
        congr 1; omega

private theorem toMatR_npow (A : AzMatrix R n n) (k : Nat) :
    toMatR (npowR A k) = toMatR A ^ k := by
  simp [npowR, Azurite.fastPow, toMatR_fastPowAux, toMatR_one, one_mul]

private def natCastR (k : Nat) : AzMatrix R n n :=
  AzMatrix.ofFn ((k : Matrix (Fin n) (Fin n) R))
private theorem toMatR_natCast (k : Nat) :
    toMatR (natCastR k : AzMatrix R n n) = (k : Matrix (Fin n) (Fin n) R) := by
  unfold toMatR natCastR; ext i j; simp

private def intCastR (k : Int) : AzMatrix R n n :=
  AzMatrix.ofFn ((k : Matrix (Fin n) (Fin n) R))
private theorem toMatR_intCast (k : Int) :
    toMatR (intCastR k : AzMatrix R n n) = (k : Matrix (Fin n) (Fin n) R) := by
  unfold toMatR intCastR; ext i j; simp

/-- `AzMatrix R n n` forms a ring when `R` is a commutative ring. -/
noncomputable instance : Ring (AzMatrix R n n) :=
  letI : SMul Nat (AzMatrix R n n) := ⟨nsmulR⟩
  letI : SMul Int (AzMatrix R n n) := ⟨zsmulR⟩
  letI : Pow (AzMatrix R n n) Nat := ⟨npowR⟩
  letI : NatCast (AzMatrix R n n) := ⟨natCastR⟩
  letI : IntCast (AzMatrix R n n) := ⟨intCastR⟩
  Function.Injective.ring toMatR toMatR_inj
    toMatR_zero toMatR_one toMatR_add toMatR_mul toMatR_neg toMatR_sub
    toMatR_nsmul toMatR_zsmul toMatR_npow toMatR_natCast toMatR_intCast

end Ring

end Azurite
