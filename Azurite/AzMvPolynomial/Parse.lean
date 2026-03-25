/-
  Parsing multivariate polynomials from character lists.

  The splitting logic (`splitMonomials` / `splitMonomialsAux`) is structured
  as the exact inverse of `joinMonomials` / `joinMonomialsAux` from ToString.lean,
  enabling a straightforward round-trip proof by structural induction.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite

open AzPolynomial Monomial MonicMonomial

variable {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [ParsableVar σ n]
         {ord : MonomialOrder}

/-! ### Splitting polynomial char-lists into monomial char-lists -/

/-- Predicate for characters that are NOT `+` or `-`. -/
def isNotSign (c : Char) : Bool := c != '+' && c != '-'

/-- Take characters for one monomial from the front of a char list.
    The first character is always included unconditionally (it could be `-`);
    subsequent characters are included while they are not `+` or `-`.
    Returns `(monomial_chars, remaining_chars)`. -/
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

theorem takeMonomial_snd_length_lt_of_cons (c : Char) (rest : List Char) :
    (takeMonomial (c :: rest)).2.length < (c :: rest).length := by
  simp only [takeMonomial, List.length_cons]
  exact Nat.lt_succ_of_le (List.dropWhile_suffix isNotSign).length_le

/-- Split the chars after the first monomial into monomial char-lists.
    - `+` is consumed as a separator.
    - `-` is kept as the start of the next monomial.
    Mirrors `joinMonomialsAux` for round-trip provability. -/
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
  · -- '+' :: rest case
    have := takeMonomial_snd_length_le rest
    omega
  · -- c :: rest case
    have := (List.dropWhile_suffix isNotSign (l := rest)).length_le
    omega

/-- Split a polynomial char-list into monomial char-lists.
    Mirrors `joinMonomials` for round-trip provability. -/
def splitMonomials : List Char → List (List Char)
  | [] => []
  | cs@(_ :: _) =>
    let tr := takeMonomial cs
    tr.1 :: splitMonomialsAux tr.2

/-! ### Parsing -/

/-- Parse a char list into a multivariate polynomial.
    Splits at `+` / `-` boundaries, parses each piece as a `Monomial`,
    then sorts the result. Accepts monomials in any order but rejects
    duplicate monic parts (e.g. `x*y+y*x`).
    Returns `none` on any parse failure. -/
def AzMvPolynomial.parse
    (cs : List Char) : Option (AzMvPolynomial σ R ord) :=
  if cs = ParsableCoeff.toChars (0 : R) then some 0
  else
    let parts := splitMonomials cs
    match parts.mapM (Monomial.parse (ord := ord) (σ := σ) (R := R)) with
    | none => none
    | some monomials =>
      AzMvPolynomial.ofMonomials? monomials.toArray

/-- Parse a string into a multivariate polynomial. -/
def AzMvPolynomial.parseStr
    (s : String) : Option (AzMvPolynomial σ R ord) :=
  AzMvPolynomial.parse s.toList

end Azurite
