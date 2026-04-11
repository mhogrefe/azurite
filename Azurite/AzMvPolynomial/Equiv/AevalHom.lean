import Azurite.AzMvPolynomial.Equiv.Eval2
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra

/-!
# Bundled `R`-algebra-hom form of `AzMvPolynomial.aeval`

Provides `AzMvPolynomial.aevalAlgHom`: given a substitution `f : Fin n → S`
where `S` is an `R`-algebra, the map `p ↦ p.aeval f` is an `R`-algebra
homomorphism `AzMvPolynomial n R ord →ₐ[R] S`.

Fin-only counterpart of Mathlib's `MvPolynomial.aeval`, which is already
bundled as `MvPolynomial σ R →ₐ[R] S`.
-/

namespace Azurite

open AzMvPolynomial

variable {R S : Type _}
    [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    {n : ℕ} {ord : MonomialOrder}

/-- Bundled `R`-algebra-hom form of `AzMvPolynomial.aeval`. -/
def AzMvPolynomial.aevalAlgHom (f : Fin n → S) :
    AzMvPolynomial n R ord →ₐ[R] S where
  toFun p := p.aeval f
  map_zero' := by
    rw [toMvPoly_aeval,
        show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero,
        map_zero]
  map_one' := by
    rw [toMvPoly_aeval,
        show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one,
        map_one]
  map_add' p q := by
    rw [toMvPoly_aeval, toMvPoly_add, map_add, toMvPoly_aeval, toMvPoly_aeval]
  map_mul' p q := by
    rw [toMvPoly_aeval, toMvPoly_mul, map_mul, toMvPoly_aeval, toMvPoly_aeval]
  commutes' r := by
    show ((AzMvPolynomial.C r : AzMvPolynomial n R ord).aeval f) = algebraMap R S r
    rw [toMvPoly_aeval, toMvPoly_C, MvPolynomial.aeval_C]

@[simp] theorem AzMvPolynomial.aevalAlgHom_C (f : Fin n → S) (r : R) :
    (AzMvPolynomial.aevalAlgHom (ord := ord) f)
        (AzMvPolynomial.C r : AzMvPolynomial n R ord) = algebraMap R S r :=
  (AzMvPolynomial.aevalAlgHom (ord := ord) f).commutes r

@[simp] theorem AzMvPolynomial.aevalAlgHom_X (f : Fin n → S) (i : Fin n) :
    (AzMvPolynomial.aevalAlgHom (R := R) (ord := ord) f)
        (AzMvPolynomial.X i : AzMvPolynomial n R ord) = f i := by
  show (AzMvPolynomial.X i : AzMvPolynomial n R ord).aeval f = f i
  rw [toMvPoly_aeval, toMvPoly_X, MvPolynomial.aeval_X]

end Azurite
