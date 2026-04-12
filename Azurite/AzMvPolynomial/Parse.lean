/-
  Parsing `AzMvPolynomial` from character lists.

  Splits at `+`/`-` boundaries, parses each piece as a `Monomial`, then
  sorts via `AzMvPolynomial.ofMonomials?`.  Display is parameterized over
  a `ParsableVar F n` naming scheme; math core stays Fin-only.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open AzMvPolynomial Monomial MonicMonomial

variable {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Splitting polynomial char-lists into monomial char-lists -/

/-- Predicate for characters that are NOT `+` or `-`. -/
def isNotSign (c : Char) : Bool := c != '+' && c != '-'

/-- Take characters for one monomial from the front of a char list.
    The first character is always included unconditionally (it could be `-`);
    subsequent characters are included while they are not `+` or `-`. -/
def takeMonomial : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest => (c :: rest.takeWhile isNotSign, rest.dropWhile isNotSign)

theorem takeMonomial_snd_length_le (cs : List Char) :
    (takeMonomial cs).2.length ≤ cs.length := by
  match cs with
  | [] => simp [takeMonomial]
  | c :: rest =>
    simp only [takeMonomial]
    exact Nat.le_succ_of_le (List.dropWhile_suffix isNotSign).length_le

/-- Split the chars after the first monomial into monomial char-lists. -/
def splitMonomialsAux : List Char → List (List Char)
  | [] => []
  | '+' :: rest =>
    let tr := takeMonomial rest
    tr.1 :: splitMonomialsAux tr.2
  | c :: rest =>
    (c :: rest.takeWhile isNotSign) :: splitMonomialsAux (rest.dropWhile isNotSign)
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  · have := takeMonomial_snd_length_le rest
    omega
  · have := (List.dropWhile_suffix isNotSign (l := rest)).length_le
    omega

/-- Split a polynomial char-list into monomial char-lists. -/
def splitMonomials : List Char → List (List Char)
  | [] => []
  | cs@(_ :: _) =>
    let tr := takeMonomial cs
    tr.1 :: splitMonomialsAux tr.2

/-! ### Parsing -/

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Parse a char list into a multivariate polynomial using naming scheme `F`.
    Splits at `+`/`-` boundaries, parses each piece as a `Monomial`,
    then sorts the result.  Accepts monomials in any order but rejects
    duplicate monic parts (e.g. `x*y+y*x`).  Returns `none` on parse failure.
    The zero polynomial (represented as `['0']` via `ParsableCoeff.toChars_zero`)
    is handled as a special case, since a `Monomial` requires nonzero coefficient. -/
def AzMvPolynomial.parseWith
    (cs : List Char) : Option (AzMvPolynomial n R ord) :=
  if cs = ['0'] then some 0
  else
    let parts := splitMonomials cs
    match parts.mapM (Monomial.parseWith (ord := ord) (n := n) (R := R) F) with
    | none => none
    | some monomials =>
      AzMvPolynomial.ofMonomials? monomials.toArray

/-- Parse a string into a multivariate polynomial using naming scheme `F`. -/
@[inline] def AzMvPolynomial.parseStrWith
    (s : String) : Option (AzMvPolynomial n R ord) :=
  AzMvPolynomial.parseWith F s.toList

end Display

/-- Default `parse`: accepts `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def AzMvPolynomial.parse
    (cs : List Char) : Option (AzMvPolynomial n R ord) :=
  AzMvPolynomial.parseWith (IndexedVar n) cs

/-- Default `parseStr`: accepts `IndexedVar n` naming. -/
@[inline] def AzMvPolynomial.parseStr
    (s : String) : Option (AzMvPolynomial n R ord) :=
  AzMvPolynomial.parse s.toList

end Azurite
