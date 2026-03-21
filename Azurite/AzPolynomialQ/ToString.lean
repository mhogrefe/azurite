import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomial.ToString

/-!
# AzPolynomialQ toString

This module provides a `toChars` function for `AzPolynomialQ` that formats
a polynomial as a human-readable string, working directly on the `AzPolynomialQ`
structure (numerators + shared denominator) rather than converting to
`AzPolynomial ℚ` first.

## Main definitions

- `AzPolynomialQ.toChars` — format a `AzPolynomialQ` as a `String`

For the proof that `toChars` agrees with `AzPolynomial.toChars ∘ toAzPolynomial`,
see `Azurite.AzPolynomialQ.Equiv.ToString`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- Shared formatting pipeline: takes a list of rational coefficients and produces
    a human-readable polynomial string by formatting nonzero monomials in
    descending degree order with appropriate sign separators. -/
private def pipeline (coeffs : List ℚ) : String :=
  let indexed := listEnum coeffs
  let nonZero := indexed.filter fun (_, c) => c ≠ 0
  let monomials := nonZero.map fun (d, c) => monomialToChars d c
  let reversed := monomials.reverse
  let withSigns := (listEnum reversed).map fun (i, m) =>
    if i = 0 then m
    else match m with
    | '-' :: _ => m
    | _ => '+' :: m
  String.ofList withSigns.flatten

/-- Format a `AzPolynomialQ` as a human-readable polynomial string.
    Operates directly on the numerator array and shared denominator,
    computing each coefficient as `numerators[i] / denom : ℚ` and
    formatting it using the standard monomial formatter. -/
def toChars (p : AzPolynomialQ) : String :=
  if p = 0 then "0"
  else pipeline ((p.numerators.map (fun n : ℤ => (↑n : ℚ) / ↑p.denom)).toList)

instance : ToString AzPolynomialQ where
  toString := toChars

end AzPolynomialQ

end Azurite
