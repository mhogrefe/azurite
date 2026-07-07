import Azurite.AzPolynomial.Basic

/-!
# Stringifying `AzPolynomial R` with a user-supplied coefficient printer

`AzPolynomial.toStrWithCoeff coeffStr p` renders a univariate polynomial in the
variable `x`, printing each coefficient `c` via `coeffStr c` and **wrapping a
coefficient in parentheses when its rendered string is non-atomic** — i.e. when
it contains `+`, `-`, or `/` (so it is not a bare monomial). This keeps terms
such as `((a+b)/c)*x^2` unambiguous when the coefficient ring is itself a
polynomial or rational-function ring.

Unlike `AzPolynomial.toChars`, this takes the coefficient→string map explicitly,
so it works over *any* coefficient type (e.g. `AzMvRationalFunction`, which has
no `ParsableCoeff` instance). Coefficient `1` is omitted on positive-degree
terms; the zero polynomial prints as `"0"`.
-/

namespace Azurite.AzPolynomial

/-- The `x^i` tail (no coefficient, no leading `*`): `""` for `i = 0`, `"x"`
    for `i = 1`, `"x^i"` otherwise. -/
def xPowerStr (i : ℕ) : String :=
  if i = 0 then "" else if i = 1 then "x" else "x^" ++ toString i

/-- Wrap `s` in parentheses when it is *non-atomic* — contains an operator
    (`+`, `-`, `/`) — so it does not merge ambiguously with a following
    `*x^i`. A bare monomial (only digits, letters, `*`, `^`) is left as is. -/
def wrapIfCompound (s : String) : String :=
  if s.any (fun ch => ch == '+' || ch == '-' || ch == '/') then "(" ++ s ++ ")" else s

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- A single nonzero term `c · x^i`, rendered. Coefficient `1` is dropped on
    positive-degree terms; otherwise the (possibly parenthesized) coefficient is
    followed by `*x^i` when `i ≠ 0`. -/
def termStrWithCoeff (coeffStr : R → String) (c : R) (i : ℕ) : String :=
  if c = 1 ∧ i ≠ 0 then
    xPowerStr i
  else
    let w := wrapIfCompound (coeffStr c)
    if i = 0 then w else w ++ "*" ++ xPowerStr i

/-- Render `p : AzPolynomial R` in the variable `x`, printing coefficients via
    `coeffStr` and parenthesizing non-atomic ones. Highest degree first, joined
    with `+`; the zero polynomial is `"0"`. -/
def toStrWithCoeff (coeffStr : R → String) (p : AzPolynomial R) : String :=
  let terms := ((List.range p.coeffs.size).reverse).filterMap (fun i =>
    let c := p.coeff i
    if c = 0 then none else some (termStrWithCoeff coeffStr c i))
  match terms with
  | [] => "0"
  | _ => String.intercalate "+" terms

end Azurite.AzPolynomial
