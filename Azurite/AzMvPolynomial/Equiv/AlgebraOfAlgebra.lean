import Azurite.AzMvPolynomial.Equiv.Algebra
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# `Algebra R (AzMvPolynomial n S ord)` when `S` is an `R`-algebra

Azurite analogue of Mathlib's `MvPolynomial.algebra`. Given an `R`-algebra `S`,
`AzMvPolynomial n S ord` becomes an `R`-algebra via `RingHom.toAlgebra` on the
composite map `R → S → AzMvPolynomial n S ord`.

Kept in its own file so the `S = R` specialization in `Equiv/Algebra.lean`
(which uses the native `SMul R (AzMvPolynomial n R ord)`) does not diamond
with this more general instance.
-/

namespace Azurite

open AzMvPolynomial

variable {R S : Type _} [CommSemiring R] [CommSemiring S] [NoZeroDivisors S]
         [DecidableEq S] [Algebra R S]
         {n : ℕ} {ord : MonomialOrder}

/-- When `S` is an `R`-algebra, `AzMvPolynomial n S ord` is also an `R`-algebra
    via the composite embedding `R → S → AzMvPolynomial n S ord`. -/
instance mvAlgebraOfAlgebra : Algebra R (AzMvPolynomial n S ord) :=
  (AzMvPolynomial.CHom.comp (algebraMap R S)).toAlgebra

end Azurite
