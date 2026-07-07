import Azurite.AzMvRationalFunction.Basic
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.SMul

/-!
# Printing an `AzMvRationalFunction`

Var-parametrized display (a `ParsableVar F n` naming scheme; unlike the
univariate printer which fixes `"x"`). The display form reconstitutes the
integer fraction from the factored representation: with `factor = ±a/b`, the
displayed numerator is `(±a) • num` and the displayed denominator is `b • den`.

Format (mirroring the univariate `AzRationalFunction`):

* denominator `1`: just the numerator char-list;
* otherwise `num/den`, with the numerator parenthesized exactly when it has
  more than one term, and the denominator parenthesized unless it is safe to
  leave bare after a `/`.

## The `wrapDenominator` rule (multivariate adaptation)

A bare denominator is left unparenthesized only when nothing in it would
re-associate after the `/`: it must be **constant** (`totalDegree = 0`) **or a
single term with coefficient `1` whose monomial is a pure power of ONE
variable** (at most one nonzero exponent). This keeps `1/x`, `1/x^2` bare (as
univariate) but wraps `1/(x*y)`, `1/(x^2*y)` — a bare `x*y` after `/` would
misread as `(·/x)*y`.

This is the multivariate refinement of the univariate rule
(`natDegree = 0 ∨ (numTerms ≤ 1 ∧ leadingCoeff = 1)`): on univariate-shaped
inputs (single variable) every coefficient-`1` monomial IS a single-variable
power, so the two rules coincide — important for cross-compatibility.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The displayed numerator: `(±a) • num` for `factor = ±a/b`. -/
def displayNum (r : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt) • r.num

/-- The displayed denominator: `b • den` for `factor = ±a/b`. -/
def displayDen (r : AzMvRationalFunction n ord) : AzMvPolynomial n AzInt ord :=
  (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • r.den

/-- Whether a denominator may be printed without enclosing parentheses:
constant, or a single coefficient-`1` term that is a pure power of one
variable (at most one nonzero exponent). -/
def denBare (p : AzMvPolynomial n AzInt ord) : Prop :=
  p.totalDegree = 0 ∨
    (p.numTerms ≤ 1 ∧ ∀ m ∈ p.terms.toList,
      m.coeff.val = 1 ∧ (m.monic.exponents.toList.countP (· != 0)) ≤ 1)

instance (p : AzMvPolynomial n AzInt ord) : Decidable (denBare p) := by
  unfold denBare; infer_instance

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- A numerator component, parenthesized when it has more than one term. -/
def wrapComponent (p : AzMvPolynomial n AzInt ord) : List Char :=
  if p.numTerms ≤ 1 then AzMvPolynomial.toCharsWith F p
  else '(' :: AzMvPolynomial.toCharsWith F p ++ [')']

/-- The denominator string, parenthesized unless `denBare` holds. -/
def wrapDenominator (p : AzMvPolynomial n AzInt ord) : List Char :=
  if denBare p then AzMvPolynomial.toCharsWith F p
  else '(' :: AzMvPolynomial.toCharsWith F p ++ [')']

/-- **Char-list form** of a rational function: the reduced integer fraction
`num/den` (parenthesizing a multi-term numerator and any non-`denBare`
denominator), or just the numerator when the denominator is `1`. -/
def toCharsWith (r : AzMvRationalFunction n ord) : List Char :=
  if displayDen r == 1 then AzMvPolynomial.toCharsWith F (displayNum r)
  else wrapComponent F (displayNum r) ++ '/' :: wrapDenominator F (displayDen r)

/-- **String form** of a rational function. -/
def toStrWith (r : AzMvRationalFunction n ord) : String :=
  String.ofList (toCharsWith F r)

end Display

end Azurite.AzMvRationalFunction
