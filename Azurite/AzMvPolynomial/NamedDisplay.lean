/-
  Round-trip sanity checks for the default `AzMvPolynomial` display
  (`IndexedVar n` naming, `x₀, x₁, …`).

  The math core `AzMvPolynomial n R ord` is indexed by `n : ℕ` / `Fin n`,
  matching Mathlib.  Human-readable `toChars` / `parse` happen through a
  user-chosen display type `F` carrying a `[ParsableVar F n]` instance — see
  `AzMvPolynomial.toCharsWith` / `parseWith` in `ToString.lean` / `Parse.lean`.
  The default `IndexedVar n` layer specialises those to `x₀, x₁, …`.
-/
import Azurite.AzMvPolynomial.ToString
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ParsableCoeff.AzInt
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat

open Azurite

section NamedDisplayExamples

-- Parse `x₀+x₁` into a `Fin 2` polynomial, then pretty-print it back using
-- the default `IndexedVar`-based display.
#guard
  ((AzMvPolynomial.parseStr (R := AzInt) (ord := .Degrevlex) (n := 2) "x₀+x₁").map
      AzMvPolynomial.toStr) == some "x₀+x₁"

-- Parse a polynomial with a constant and a nonlinear term, round-trip.
#guard
  ((AzMvPolynomial.parseStr (R := AzInt) (ord := .Degrevlex) (n := 3)
      "3*x₀^2*x₁-2*x₀*x₂+5").map AzMvPolynomial.toStr)
    == some "3*x₀^2*x₁-2*x₀*x₂+5"

end NamedDisplayExamples
