/-
  ToString for `AzMvPolynomial` — display layer parameterized over a
  `ParsableVar F n` naming scheme.  The math core does not reference `Var`.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open AzMvPolynomial Monomial

variable {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
         {n : ℕ} {ord : MonomialOrder}

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

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Convert a multivariate polynomial to a list of characters using the
    display naming scheme `F`.  Returns `['0']` for the zero polynomial;
    otherwise joins monomial representations with sign-aware concatenation. -/
def AzMvPolynomial.toCharsWith (p : AzMvPolynomial n R ord) : List Char :=
  if p.terms.isEmpty then ParsableCoeff.toChars (0 : R)
  else joinMonomials (p.terms.toList.map (fun m => m.toCharsWith F))

/-- Convert a multivariate polynomial to a string using naming scheme `F`. -/
def AzMvPolynomial.toStrWith (p : AzMvPolynomial n R ord) : String :=
  String.ofList (p.toCharsWith F)

end Display

/-- Default `toChars`: uses `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def AzMvPolynomial.toChars (p : AzMvPolynomial n R ord) : List Char :=
  p.toCharsWith (IndexedVar n)

/-- Default `toStr`: uses `IndexedVar n` naming. -/
@[inline] def AzMvPolynomial.toStr (p : AzMvPolynomial n R ord) : String :=
  String.ofList p.toChars

instance instToStringAzMvPolynomial : ToString (AzMvPolynomial n R ord) where
  toString := AzMvPolynomial.toStr

end Azurite
