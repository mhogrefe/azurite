/-
  Parsing `AzMvPolynomialNew` from character lists.

  Splits at `+`/`-` boundaries, parses each piece as a `MonomialNew`, then
  sorts via `AzMvPolynomialNew.ofMonomials?`.  Display is parameterized over
  a `ParsableVar F n` naming scheme; math core stays Fin-only.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite

open AzMvPolynomialNew MonomialNew MonicMonomialNew

variable {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Splitting polynomial char-lists into monomial char-lists -/

/-- Predicate for characters that are NOT `+` or `-`. -/
def isNotSignNew (c : Char) : Bool := c != '+' && c != '-'

/-- Take characters for one monomial from the front of a char list.
    The first character is always included unconditionally (it could be `-`);
    subsequent characters are included while they are not `+` or `-`. -/
def takeMonomialNew : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest => (c :: rest.takeWhile isNotSignNew, rest.dropWhile isNotSignNew)

theorem takeMonomialNew_snd_length_le (cs : List Char) :
    (takeMonomialNew cs).2.length ≤ cs.length := by
  match cs with
  | [] => simp [takeMonomialNew]
  | c :: rest =>
    simp only [takeMonomialNew]
    exact Nat.le_succ_of_le (List.dropWhile_suffix isNotSignNew).length_le

/-- Split the chars after the first monomial into monomial char-lists. -/
def splitMonomialsAuxNew : List Char → List (List Char)
  | [] => []
  | '+' :: rest =>
    let tr := takeMonomialNew rest
    tr.1 :: splitMonomialsAuxNew tr.2
  | c :: rest =>
    (c :: rest.takeWhile isNotSignNew) :: splitMonomialsAuxNew (rest.dropWhile isNotSignNew)
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  · have := takeMonomialNew_snd_length_le rest
    omega
  · have := (List.dropWhile_suffix isNotSignNew (l := rest)).length_le
    omega

/-- Split a polynomial char-list into monomial char-lists. -/
def splitMonomialsNew : List Char → List (List Char)
  | [] => []
  | cs@(_ :: _) =>
    let tr := takeMonomialNew cs
    tr.1 :: splitMonomialsAuxNew tr.2

/-! ### Parsing -/

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Parse a char list into a multivariate polynomial using naming scheme `F`.
    Splits at `+`/`-` boundaries, parses each piece as a `MonomialNew`,
    then sorts the result.  Accepts monomials in any order but rejects
    duplicate monic parts (e.g. `x*y+y*x`).  Returns `none` on parse failure. -/
def AzMvPolynomialNew.parseWith
    (cs : List Char) : Option (AzMvPolynomialNew n R ord) :=
  if cs = ParsableCoeff.toChars (0 : R) then some 0
  else
    let parts := splitMonomialsNew cs
    match parts.mapM (MonomialNew.parseWith (ord := ord) (n := n) (R := R) F) with
    | none => none
    | some monomials =>
      AzMvPolynomialNew.ofMonomials? monomials.toArray

/-- Parse a string into a multivariate polynomial using naming scheme `F`. -/
def AzMvPolynomialNew.parseStrWith
    (s : String) : Option (AzMvPolynomialNew n R ord) :=
  AzMvPolynomialNew.parseWith F s.toList

end Display

/-- Default `parse`: accepts `IndexedVar n` naming (`x₀, x₁, …`). -/
@[inline] def AzMvPolynomialNew.parse
    (cs : List Char) : Option (AzMvPolynomialNew n R ord) :=
  AzMvPolynomialNew.parseWith (IndexedVar n) cs

/-- Default `parseStr`: accepts `IndexedVar n` naming. -/
@[inline] def AzMvPolynomialNew.parseStr
    (s : String) : Option (AzMvPolynomialNew n R ord) :=
  AzMvPolynomialNew.parse s.toList

end Azurite
