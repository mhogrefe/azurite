/-
  Equivalence proofs for `AzMvPolynomial.mul`.

  These delegate to `mulNaive` equivalence proofs and will remain valid
  when `mul` switches to a more sophisticated algorithm (as long as the
  new algorithm is also proven equivalent).
-/
import Azurite.AzMvPolynomial.Equiv.MulNaive

namespace Azurite
open AzMvPolynomial MvPolynomial

variable {R : Type _} [CommRing R] [NoZeroDivisors R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Multiplication commutes with `toMvPoly`. -/
theorem toMvPoly_mul (p q : AzMvPolynomial σ R ord) :
    (p * q).toMvPoly = p.toMvPoly * q.toMvPoly :=
  toMvPoly_mulNaive p q

/-- Multiplication commutes with `ofMvPoly`. -/
@[simp] theorem ofMvPoly_mul (p q : MvPolynomial σ R) :
    (AzMvPolynomial.ofMvPoly (p * q) : AzMvPolynomial σ R ord) =
      AzMvPolynomial.ofMvPoly p * AzMvPolynomial.ofMvPoly q := by
  set a := AzMvPolynomial.ofMvPoly (ord := ord) p
  set b := AzMvPolynomial.ofMvPoly (ord := ord) q
  have hp : a.toMvPoly = p := toMvPoly_ofMvPoly p
  have hq : b.toMvPoly = q := toMvPoly_ofMvPoly q
  rw [show p * q = a.toMvPoly * b.toMvPoly from by rw [hp, hq],
      ← toMvPoly_mul]
  exact ofMvPoly_toMvPoly (a * b)

end Azurite
