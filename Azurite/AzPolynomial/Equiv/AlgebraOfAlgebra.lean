import Azurite.AzPolynomial.Equiv.Algebra
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# `Algebra R (AzPolynomial S)` when `S` is an `R`-algebra

This is the Azurite analogue of Mathlib's `Polynomial.algebraOfAlgebra`.
Given an `R`-algebra `S`, `AzPolynomial S` becomes an `R`-algebra via the
composite map `R → S → AzPolynomial S` (algebraMap followed by `C`).

Kept in its own file (rather than `Equiv/Algebra.lean`) so that the `S = R`
specialization there — which defines `Algebra R (AzPolynomial R)` — doesn't
create a diamond with this more general instance.
-/

namespace Azurite

open _root_.Azurite.AzPolynomial

variable {R S : Type _} [CommSemiring R] [CommSemiring S] [DecidableEq S] [Algebra R S]

/-- When `S` is an `R`-algebra, `AzPolynomial S` is also an `R`-algebra via
    the composite embedding `R → S → AzPolynomial S`. -/
instance algebraOfAlgebra : Algebra R (AzPolynomial S) where
  algebraMap := CHom.comp (algebraMap R S)
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := fun r p => toPoly_inj.mp (by
    rw [toPoly_smul, toPoly_mul]
    show _ = AzPolynomial.toPoly (CHom (algebraMap R S r)) * _
    rw [show AzPolynomial.toPoly (CHom (algebraMap R S r)) =
        Polynomial.C (algebraMap R S r) from toPoly_C _]
    rw [← Polynomial.algebraMap_apply]
    exact Algebra.smul_def r (AzPolynomial.toPoly p))

end Azurite
