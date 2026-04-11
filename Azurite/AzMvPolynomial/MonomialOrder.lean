/-
  Monomial orderings for multivariate polynomials.

  Defines the `MonomialOrder` inductive (`Lex` / `Deglex` / `Degrevlex`)
  together with vector-level comparison helpers (`lexCompareAux`,
  `revlexCompareAux`, `totalDeg`, `compareExponents`).  This file is
  variable-type independent — the monic monomial wrappers that carry
  `Vector ℕ n` lift the helpers here.
-/
import Mathlib.Data.Vector.Defs

namespace Azurite

/-- Monomial orderings for multivariate polynomials.
    - `Lex`: pure lexicographic (compare exponents left-to-right)
    - `Deglex`: total degree first, then lex to break ties
    - `Degrevlex`: total degree first, then reverse lex with flipped comparison -/
inductive MonomialOrder
  | Lex
  | Deglex
  | Degrevlex
  deriving DecidableEq, Repr

namespace MonomialOrder

/-- Lexicographic comparison of exponent vectors, starting at index `i`. -/
def lexCompareAux (a b : Vector ℕ n) (i : ℕ) : Ordering :=
  if h : i < n then
    match compare a[i] b[i] with
    | .eq => lexCompareAux a b (i + 1)
    | ord => ord
  else .eq
termination_by n - i

/-- Lexicographic comparison of exponent vectors. -/
def lexCompare (a b : Vector ℕ n) : Ordering := lexCompareAux a b 0

/-- Reverse lexicographic comparison with flipped result, starting at
    offset `i` from the end.
    The monomial with the *smaller* exponent at the rightmost differing
    position is considered *greater*. -/
def revlexCompareAux (a b : Vector ℕ n) (i : ℕ) : Ordering :=
  if h : i < n then
    let j := n - 1 - i
    match compare a[j] b[j] with
    | .eq => revlexCompareAux a b (i + 1)
    | .lt => .gt
    | .gt => .lt
  else .eq
termination_by n - i

/-- Reverse lexicographic comparison (right-to-left, flipped). -/
def revlexCompare (a b : Vector ℕ n) : Ordering := revlexCompareAux a b 0

/-- Total degree of an exponent vector. -/
def totalDeg (v : Vector ℕ n) : ℕ := v.toArray.foldl (· + ·) 0

/-- Compare exponent vectors according to the given monomial ordering. -/
def compareExponents (ord : MonomialOrder) (a b : Vector ℕ n) : Ordering :=
  match ord with
  | .Lex => lexCompare a b
  | .Deglex =>
    match compare (totalDeg a) (totalDeg b) with
    | .eq => lexCompare a b
    | r => r
  | .Degrevlex =>
    match compare (totalDeg a) (totalDeg b) with
    | .eq => revlexCompare a b
    | r => r

end MonomialOrder

end Azurite
