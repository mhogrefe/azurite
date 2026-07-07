import Azurite.AzMvRationalFunction.Instances

/-!
# Composition of multivariate rational functions

Substitute a **tuple** `s : Fin n → AzMvRationalFunction m ord'` of rational
functions into an `n`-variable rational function `r : AzMvRationalFunction n ord`,
producing an `AzMvRationalFunction m ord'`. This is the multivariate
generalization of the univariate `comp`.

It is built directly from the field arithmetic: a composition kernel `evalMv`
evaluates an integer polynomial at the tuple `s`, valued in the *field*
`AzMvRationalFunction m ord'` (each monomial `∏ᵢ (s i)^{eᵢ}` via
`MonicMonomial.eval`, each integer coefficient via `ofAzInt`); then
`comp r s = factor · (evalMv num s / evalMv den s)`.

No pole guard is needed: field division by `0` is `0`, so `comp` collapses to
`0` exactly when the denominator vanishes at `s` — the same junk convention as
the univariate `comp`. (This file necessarily sits after `Instances`: the
`MonicMonomial.eval` product needs the `CommMonoid` from the `Field` instance,
and `Arithmetic`/`Equiv.Arithmetic` precede `Instances` in the import graph.)
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n m : ℕ} {ord ord' : MonomialOrder}

/-- **Composition kernel**: evaluate an integer polynomial `p` at the tuple `s`,
valued in the field `AzMvRationalFunction m ord'`. Each term contributes
`(coeff : AzMvRationalFunction) · ∏ᵢ (s i)^{exponentᵢ}`. -/
def evalMv (p : AzMvPolynomial n AzInt ord) (s : Fin n → AzMvRationalFunction m ord') :
    AzMvRationalFunction m ord' :=
  p.terms.foldl (fun acc t => acc + ofAzInt t.coeff.val * t.monic.eval s) 0

/-- **Composition** `r ∘ s`: substitute the tuple `s` for the variables of `r`.
Evaluate the numerator and denominator parts at `s` and divide, scaling by the
rational factor. `0` (junk) when the denominator part vanishes at `s`. -/
def comp (r : AzMvRationalFunction n ord) (s : Fin n → AzMvRationalFunction m ord') :
    AzMvRationalFunction m ord' :=
  ofAzRat r.factor * (evalMv r.num s / evalMv r.den s)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def r2 (s : String) : AzMvRationalFunction 2 .Degrevlex :=
  (parseStrWith (XyzVar 2) s).getD 0

private def render (r : AzMvRationalFunction 2 .Degrevlex) : String :=
  toStrWith (XyzVar 2) r

-- constant tuple: composition = evaluation at (3, -1) → (3-1)/(3+1) = 1/2
#guard render (comp (r2 "(x+y)/(x-y)") ![r2 "3", r2 "-1"]) == "1/2"
#guard comp (r2 "(x+y)/(x-y)") ![r2 "3", r2 "-1"] == r2 "1/2"
-- variables-for-variables: identity
#guard comp (r2 "(x+y)/(x-y)") ![r2 "x", r2 "y"] == r2 "(x+y)/(x-y)"
-- rename/swap x ↔ y: (y+x)/(y-x) = -(x+y)/(x-y)
#guard render (comp (r2 "(x+y)/(x-y)") ![r2 "y", r2 "x"]) == "(-x-y)/(x-y)"
-- a genuine composition
#guard comp (r2 "(x+y)/(x-y)") ![r2 "x^2", r2 "y^2"] == r2 "(x^2+y^2)/(x^2-y^2)"
-- a common-factor-creating example: (x/y) ∘ [x*y, y] = (x*y)/y = x
#guard render (comp (r2 "x/y") ![r2 "x*y", r2 "y"]) == "x"
-- the tuple hits a pole (denominator x - x = 0) → 0
#guard comp (r2 "1/(x-y)") ![r2 "x", r2 "x"] == 0

end Tests

end Azurite.AzMvRationalFunction
