/-
  ToString for `AzMvPolynomialNew` — display layer parameterized over a
  `ParsableVar F n` naming scheme.  The math core does not reference `Var`.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite

open AzMvPolynomialNew MonomialNew

variable {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
         {n : ℕ} {ord : MonomialOrder}

/-- Join the remaining monomial char-lists (after the first), prepending `+`
    unless the monomial starts with `-`. -/
def joinMonomialsAuxNew : List (List Char) → List Char
  | [] => []
  | m :: ms =>
    let sep := match m with | '-' :: _ => [] | _ => ['+']
    sep ++ m ++ joinMonomialsAuxNew ms

/-- Join a list of monomial char-lists into a single char list.
    The first monomial is emitted as-is; subsequent monomials get a `+`
    prefix unless they start with `-`. -/
def joinMonomialsNew : List (List Char) → List Char
  | [] => []
  | m :: ms => m ++ joinMonomialsAuxNew ms

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Convert a multivariate polynomial to a list of characters using the
    display naming scheme `F`.  Returns `['0']` for the zero polynomial;
    otherwise joins monomial representations with sign-aware concatenation. -/
def AzMvPolynomialNew.toCharsWith (p : AzMvPolynomialNew n R ord) : List Char :=
  if p.terms.isEmpty then ParsableCoeff.toChars (0 : R)
  else joinMonomialsNew (p.terms.toList.map (fun m => m.toCharsWith F))

/-- Convert a multivariate polynomial to a string using naming scheme `F`. -/
def AzMvPolynomialNew.toStrWith (p : AzMvPolynomialNew n R ord) : String :=
  String.ofList (p.toCharsWith F)

end Display

/-- Default `toChars`: uses `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def AzMvPolynomialNew.toChars (p : AzMvPolynomialNew n R ord) : List Char :=
  p.toCharsWith (IndexedVar n)

/-- Default `toStr`: uses `IndexedVar n` naming. -/
@[inline] def AzMvPolynomialNew.toStr (p : AzMvPolynomialNew n R ord) : String :=
  String.ofList p.toChars

instance : ToString (AzMvPolynomialNew n R ord) where
  toString := AzMvPolynomialNew.toStr

end Azurite
