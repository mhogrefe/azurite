/-
  Equivalence proofs for `AzMvPolynomialNew.mul`.

  Delegates to `mulNaive` equivalence proofs and will remain valid when
  `mul` switches to a more sophisticated algorithm (as long as the new
  algorithm is also proven equivalent).
-/
import Azurite.AzMvPolynomial.New.Equiv.MulNaive

namespace Azurite
open AzMvPolynomialNew MvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Multiplication commutes with `toMvPoly`. -/
theorem toMvPoly_mul_new (p q : AzMvPolynomialNew n R ord) :
    (p * q).toMvPoly = p.toMvPoly * q.toMvPoly :=
  toMvPoly_mulNaive_new p q

/-- Multiplication commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_mul_new (p q : MvPolynomial (Fin n) R) :
    (AzMvPolynomialNew.ofMvPoly (p * q) : AzMvPolynomialNew n R ord) =
      AzMvPolynomialNew.ofMvPoly p * AzMvPolynomialNew.ofMvPoly q := by
  set a := AzMvPolynomialNew.ofMvPoly (ord := ord) p
  set b := AzMvPolynomialNew.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly_new p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly_new q
  rw [show p * q = a.toMvPoly * b.toMvPoly from by rw [hp, hq],
      ← toMvPoly_mul_new]
  exact ofMvPoly_toMvPoly_new (a * b)

end Azurite
