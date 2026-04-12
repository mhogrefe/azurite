/-
  `toChars` / `parse` for an `AzPolynomial` whose coefficients are themselves
  `AzMvPolynomial` values.  These cannot go through the regular `ParsableCoeff`
  layer because `AzMvPolynomial n R ord` does not satisfy `ParsableCoeff` — the
  rendering of a multivariate polynomial already contains polynomial syntax
  characters (`+`, `*`, `^`, ...) that the outer layer cannot distinguish from
  its own.

  We work around this by unconditionally wrapping each coefficient in
  parentheses `(...)`, except that coefficients equal to `1` are omitted when
  they multiply a non-trivial power of the outer variable.  The outer variable
  is rendered as `x`; the inner variable naming scheme `F : Type _` with
  `[ParsableVar F n]` is passed in by the caller (exactly like
  `AzMvPolynomial.toStrWith`).

  Example: for `(3*a+b) * T^2 + (-c) * T + (a+d) : AzPolynomial (AzMvPolynomial 4 ℤ ord)`
  with `F = AbcVar 4`, the string representation is
  `"(3*a+b)*x^2+(-c)*x+(a+d)"`.
-/
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Monomial
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.Equiv.Algebra

namespace Azurite

open AzPolynomial AzMvPolynomial

variable {R : Type _} [DecidableEq R] [CommSemiring R] [NoZeroDivisors R]
         [NeZero (1 : R)] [ParsableCoeff R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Display helpers -/

/-- Character list for the `x^i` tail (no coefficient, no leading `*`):
    `[]` for `i = 0`, `['x']` for `i = 1`, `x^i` otherwise. -/
def AzPolynomial.xPowerChars (i : ℕ) : List Char :=
  if i = 0 then []
  else if i = 1 then ['x']
  else 'x' :: '^' :: natToChars i

section Display
variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Character list for a single nonzero term `c * X^i`.

    * If `c = 1` and `i ≠ 0`, the coefficient is omitted (just `x^i`).
    * Otherwise the coefficient is wrapped in parentheses `(c)`, and — if
      `i ≠ 0` — followed by `*x^i`.

    The pure-constant `1` case (`c = 1`, `i = 0`) is rendered as `(1)` so that
    the empty polynomial `AzPolynomial.C 1` has a non-empty representation. -/
def AzPolynomial.termCharsMvCoeffWith
    (c : AzMvPolynomial n R ord) (i : ℕ) : List Char :=
  if c = 1 ∧ i ≠ 0 then
    AzPolynomial.xPowerChars i
  else
    let wrapped := '(' :: c.toCharsWith F ++ [')']
    if i = 0 then wrapped
    else wrapped ++ '*' :: AzPolynomial.xPowerChars i

/-- Join a nonempty list of pre-rendered terms with `+` separators. -/
def AzPolynomial.joinWithPlus : List (List Char) → List Char
  | [] => []
  | [t] => t
  | t :: ts => t ++ '+' :: AzPolynomial.joinWithPlus ts

/-- Convert an `AzPolynomial` with `AzMvPolynomial` coefficients to a character
    list using the variable naming scheme `F` for the inner variables.  The
    outer variable is always printed as `x`.  Returns `['0']` for the zero
    polynomial. -/
def AzPolynomial.toCharsMvCoeffWith
    (p : AzPolynomial (AzMvPolynomial n R ord)) : List Char :=
  if p.coeffs.size = 0 then ['0']
  else
    let indices := (List.range p.coeffs.size).reverse
    let terms := indices.filterMap (fun i =>
      let c := p.coeff i
      if c = 0 then none else some (AzPolynomial.termCharsMvCoeffWith F c i))
    AzPolynomial.joinWithPlus terms

/-- String version of `toCharsMvCoeffWith`. -/
@[inline] def AzPolynomial.toStrMvCoeffWith
    (p : AzPolynomial (AzMvPolynomial n R ord)) : String :=
  String.ofList (p.toCharsMvCoeffWith F)

end Display

/-! ### Parsing -/

/-- Split a character list at top-level `+` signs (respecting paren depth).
    Tail-recursive with accumulators; the first accumulator holds the current
    term's chars in reverse, the second holds completed terms in reverse. -/
def AzPolynomial.splitTermsAux :
    List Char → ℕ → List Char → List (List Char) → List (List Char)
  | [], _, curRev, accRev => (curRev.reverse :: accRev).reverse
  | c :: cs, d, curRev, accRev =>
    if c = '+' ∧ d = 0 then
      AzPolynomial.splitTermsAux cs 0 [] (curRev.reverse :: accRev)
    else if c = '(' then
      AzPolynomial.splitTermsAux cs (d + 1) (c :: curRev) accRev
    else if c = ')' then
      AzPolynomial.splitTermsAux cs (d - 1) (c :: curRev) accRev
    else
      AzPolynomial.splitTermsAux cs d (c :: curRev) accRev

/-- Split `cs` into top-level terms. -/
@[inline] def AzPolynomial.splitTerms (cs : List Char) : List (List Char) :=
  AzPolynomial.splitTermsAux cs 0 [] []

/-- Parse the `x^i` tail of a bare-variable term (no leading coefficient):
    `['x'] → i = 1`, `'x' :: '^' :: digits → i = N ≥ 2`.
    Fails for anything else (in particular, `[]` is not a valid bare-x tail). -/
def AzPolynomial.parseBareX : List Char → Option ℕ
  | ['x'] => some 1
  | 'x' :: '^' :: rest => parseNatChars rest
  | _ => none

/-- Parse the suffix following a closed coefficient `(...)`:
    `[]` → `i = 0` (bare constant),
    `['*', 'x']` → `i = 1`,
    `'*' :: 'x' :: '^' :: digits` → `i = N ≥ 2`.
    Fails for anything else. -/
def AzPolynomial.parseCoeffSuffix : List Char → Option ℕ
  | [] => some 0
  | ['*', 'x'] => some 1
  | '*' :: 'x' :: '^' :: rest => parseNatChars rest
  | _ => none

section Display
variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- Parse a single term (one of `x`, `x^i`, `(c)`, `(c)*x`, or `(c)*x^i`) into
    a `(coefficient, exponent)` pair. -/
def AzPolynomial.parseOneTermMvCoeff
    (cs : List Char) : Option (AzMvPolynomial n R ord × ℕ) :=
  match cs with
  | '(' :: rest =>
    -- Coefficient chars end at the first `)`; coefficient representations are
    -- assumed paren-free (enforced by the round-trip hypothesis).
    let (coeffCs, after) := rest.span (· != ')')
    match after with
    | ')' :: tail =>
      (AzPolynomial.parseCoeffSuffix tail).bind (fun i =>
        (AzMvPolynomial.parseWith F coeffCs).map (fun c => (c, i)))
    | _ => none
  | _ => (AzPolynomial.parseBareX cs).map (fun i => (1, i))

/-- Parse a character list representing an `AzPolynomial` with `AzMvPolynomial`
    coefficients using the variable naming scheme `F` for the inner variables.
    The outer variable is assumed to be `x`.  `['0']` is accepted as the zero
    polynomial. -/
def AzPolynomial.parseMvCoeffWith
    (cs : List Char) : Option (AzPolynomial (AzMvPolynomial n R ord)) :=
  if cs = ['0'] then some 0
  else
    match (AzPolynomial.splitTerms cs).mapM (AzPolynomial.parseOneTermMvCoeff F) with
    | none => none
    | some pairs =>
      some (pairs.foldl
        (fun (acc : AzPolynomial (AzMvPolynomial n R ord)) (p : AzMvPolynomial n R ord × ℕ) =>
          acc + AzPolynomial.monomial p.2 p.1) 0)

/-- String version of `parseMvCoeffWith`. -/
@[inline] def AzPolynomial.parseStrMvCoeffWith
    (s : String) : Option (AzPolynomial (AzMvPolynomial n R ord)) :=
  AzPolynomial.parseMvCoeffWith F s.toList

end Display

/-! ### Sanity-check tests -/

section Tests

open AzPolynomial

private instance : Fact (4 ≤ 26) := ⟨by omega⟩

private abbrev MvInt4 := AzMvPolynomial 4 ℤ .Degrevlex

/-- Helper: parse a multivariate string into `MvInt4` using `AbcVar 4` (`a,b,c,d`). -/
private def mv (s : String) : MvInt4 :=
  (AzMvPolynomial.parseWith (n := 4) (R := ℤ) (ord := .Degrevlex)
    (AbcVar 4) s.toList).getD 0

-- Zero polynomial
#guard (0 : AzPolynomial MvInt4).toStrMvCoeffWith (AbcVar 4) == "0"

-- The example from the task description:
-- `(3*a+b) * x^2 + (-c) * x + (a+d)`
private def p_example : AzPolynomial MvInt4 :=
  monomial 2 (mv "3*a+b") + monomial 1 (mv "-c") + AzPolynomial.C (mv "a+d")

#guard p_example.toStrMvCoeffWith (AbcVar 4) == "(3*a+b)*x^2+(-c)*x+(a+d)"

-- Coefficient `1` with power is omitted: `x^2 + (a)*x + (b+c)`
private def p_one_coeff : AzPolynomial MvInt4 :=
  monomial 2 (mv "1") + monomial 1 (mv "a") + AzPolynomial.C (mv "b+c")

#guard p_one_coeff.toStrMvCoeffWith (AbcVar 4) == "x^2+(a)*x+(b+c)"

-- A single `x` term
private def p_x : AzPolynomial MvInt4 := monomial 1 (mv "1")
#guard p_x.toStrMvCoeffWith (AbcVar 4) == "x"

-- A pure constant 1 (edge case): rendered as `(1)` so the representation is nonempty
private def p_const_one : AzPolynomial MvInt4 := C (mv "1")
#guard p_const_one.toStrMvCoeffWith (AbcVar 4) == "(1)"

-- Parse round-trip on the flagship example
#guard (AzPolynomial.parseStrMvCoeffWith (AbcVar 4) (n := 4) (R := ℤ) (ord := .Degrevlex)
    "(3*a+b)*x^2+(-c)*x+(a+d)").map
      (·.toStrMvCoeffWith (AbcVar 4)) == some "(3*a+b)*x^2+(-c)*x+(a+d)"

-- Parse round-trip on the `coeff=1` omission example
#guard (AzPolynomial.parseStrMvCoeffWith (AbcVar 4) (n := 4) (R := ℤ) (ord := .Degrevlex)
    "x^2+(a)*x+(b+c)").map
      (·.toStrMvCoeffWith (AbcVar 4)) == some "x^2+(a)*x+(b+c)"

-- Zero polynomial round-trip
#guard (AzPolynomial.parseStrMvCoeffWith (AbcVar 4) (n := 4) (R := ℤ) (ord := .Degrevlex)
    "0").map (·.toStrMvCoeffWith (AbcVar 4)) == some "0"

end Tests

end Azurite
