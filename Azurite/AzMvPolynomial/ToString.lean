/-
  ToString for multivariate polynomials.

  The joining logic is factored into `joinMonomialsAux` / `joinMonomials`
  so that a future `splitMonomials` (inverse) can mirror the same recursion,
  making the round-trip proof a straightforward structural induction.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open AzPolynomial Monomial

variable {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [ParsableVar σ n]
         {ord : MonomialOrder}

/-- Join the remaining monomial char-lists (after the first), prepending `+`
    unless the monomial starts with `-`. -/
def joinMonomialsAux : List (List Char) → List Char
  | [] => []
  | m :: ms =>
    let sep := match m with | '-' :: _ => [] | _ => ['+']
    sep ++ m ++ joinMonomialsAux ms

/-- Join a list of monomial char-lists into a single char list.
    The first monomial is emitted as-is; subsequent monomials get a `+`
    prefix unless they start with `-`. -/
def joinMonomials : List (List Char) → List Char
  | [] => []
  | m :: ms => m ++ joinMonomialsAux ms

/-- Convert a multivariate polynomial to a list of characters.
    Returns `['0']` for the zero polynomial; otherwise joins the
    monomial representations with sign-aware concatenation. -/
def AzMvPolynomial.toChars (p : AzMvPolynomial σ R ord) : List Char :=
  if p.terms.isEmpty then ParsableCoeff.toChars (0 : R)
  else joinMonomials (p.terms.toList.map Monomial.toChars)

/-- Convert a multivariate polynomial to a string. -/
def AzMvPolynomial.toStr (p : AzMvPolynomial σ R ord) : String :=
  String.ofList p.toChars

instance : ToString (AzMvPolynomial σ R ord) where
  toString := AzMvPolynomial.toStr

end Azurite
