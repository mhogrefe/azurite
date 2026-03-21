import Azurite.AzPolynomialQ.ToString
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.ToString

/-!
# AzPolynomialQ ↔ AzPolynomial ℚ toString equivalence

This module proves that `AzPolynomialQ.toChars` agrees with
`AzPolynomial.toChars` applied to `p.toAzPolynomial`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- The coefficient array produced by `toAzPolynomial` is the numerator array
    mapped by `n ↦ n / denom`. -/
private lemma coeffs_eq (p : AzPolynomialQ) :
    p.toAzPolynomial.coeffs = p.numerators.map (fun n : ℤ => (↑n : ℚ) / ↑p.denom) := by
  simp [AzPolynomialQ.toAzPolynomial, AzPolynomialQ.toIntPoly, mapZeroInjective]

/-- `AzPolynomialQ.toChars` agrees with `AzPolynomial.toChars` applied to
    `p.toAzPolynomial`. -/
theorem toChars_eq (p : AzPolynomialQ) :
    p.toChars = AzPolynomial.toChars p.toAzPolynomial := by
  simp only [toChars, AzPolynomial.toChars]
  by_cases hp : p = 0
  · subst hp; simp [AzPolynomialQ.toAzPolynomial_zero]
  · have hp' : p.toAzPolynomial ≠ 0 := by
      intro h; apply hp
      rw [← AzPolynomialQ.ofAzPolynomial_toAzPolynomial p, h]
      apply AzPolynomialQ.coeff_ext; intro i
      rw [AzPolynomialQ.coeff_ofAzPolynomial]
      simp [AzPolynomial.coeff, AzPolynomialQ.coeff]
    simp only [hp, hp', ↓reduceIte]
    rfl

end AzPolynomialQ

end Azurite
