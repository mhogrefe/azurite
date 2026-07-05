import Azurite.AzRationalFunction.Basic
import Azurite.AzPolynomial.ToString
import Azurite.AzPolynomial.SMul

/-!
# Printing an `AzRationalFunction`

The display form reconstitutes the integer fraction from the factored
representation: with `factor = ±a/b`, the displayed numerator is
`(±a) • num` and the displayed denominator is `b • den` (a reduced,
content-coprime integer fraction with positive-leading-coefficient
denominator). Format:

* denominator `1`: just the numerator string;
* otherwise `num/den`, with a component wrapped in parentheses exactly when
  it has more than one nonzero term.
-/

namespace Azurite.AzRationalFunction

open Azurite.AzPolynomial

/-- Number of nonzero terms (nonzero coefficients). -/
def numTerms (p : AzPolynomial AzInt) : ℕ :=
  p.coeffs.foldl (fun k c => if c == 0 then k else k + 1) 0

/-- The displayed numerator: `(±a) • num` for `factor = ±a/b`. -/
def displayNum (r : AzRationalFunction) : AzPolynomial AzInt :=
  (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt) • r.num

/-- The displayed denominator: `b • den` for `factor = ±a/b`. -/
def displayDen (r : AzRationalFunction) : AzPolynomial AzInt :=
  (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • r.den

/-- A component string, parenthesized when it has more than one term. -/
def wrapComponent (p : AzPolynomial AzInt) : String :=
  if numTerms p ≤ 1 then AzPolynomial.toChars p
  else "(" ++ AzPolynomial.toChars p ++ ")"

/-- **String form** of a rational function: the reduced integer fraction
`num/den` (parenthesizing multi-term components), or just the numerator
when the denominator is `1`. -/
def toString (r : AzRationalFunction) : String :=
  if displayDen r == 1 then AzPolynomial.toChars (displayNum r)
  else wrapComponent (displayNum r) ++ "/" ++ wrapComponent (displayDen r)

instance : ToString AzRationalFunction := ⟨toString⟩

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!

#guard toString (ofNumDen (pp "2*x^2-2") (pp "4*x+4")) == "(x-1)/2"
#guard toString (ofNumDen (pp "x") (pp "-2")) == "-x/2"
#guard toString (ofNumDen (pp "x^2+1") (pp "x-1")) == "(x^2+1)/(x-1)"
#guard toString (ofNumDen (pp "3*x^2") (pp "x+1")) == "3*x^2/(x+1)"
#guard toString (ofNumDen (pp "-6*x-9") (pp "1")) == "-6*x-9"
#guard toString (0 : AzRationalFunction) == "0"
#guard toString (1 : AzRationalFunction) == "1"
#guard toString (ofAzRat ((Azurite.AzRat.parse "-3/4").get!)) == "-3/4"

end Tests

end Azurite.AzRationalFunction
