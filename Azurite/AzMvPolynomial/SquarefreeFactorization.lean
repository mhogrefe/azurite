/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.SquarefreeFactorization
import Azurite.AzMvPolynomial.FinSuccEquiv
import Azurite.AzMvPolynomial.Gcd
import Azurite.AzMvPolynomial.Rename
import Azurite.AzMvPolynomial.Equiv.Compare
import Azurite.AzMvPolynomial.ExactDiv
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ParseToString

/-!
# Multivariate square-free factorization (recursive Yun)

`mvSquarefreeFactorization P` computes the square-free factorization of a
multivariate integer polynomial `P : AzMvPolynomial n AzInt ord` — a list of
pairs `(gᵢ, eᵢ)` with each `gᵢ` (conjecturally) square-free and pairwise
coprime, `∏ gᵢ^{eᵢ} = P` up to a unit, and the `gᵢ` in the canonical
`AzMvPolynomial` order.

Naive univariate Yun with a single partial derivative is *wrong*
multivariately (it misses factors not involving that variable). The correct
recursion splits off the first variable `x₀`:

1. `c := content P` (the `AzMvPolynomial n`-content, i.e. the gcd of the
   `x₀`-coefficients) and `pp := primitivePart P` (primitive in `x₀`).
2. **Yun w.r.t. `x₀` on `pp`**: view `pp` in the tower
   `AzPolynomial (AzMvPolynomial n AzInt ord)` via `finSuccEquiv` (peel `x₀`),
   run the univariate `AzPolynomial.squarefreeFactorization` over the
   coefficient ring `AzMvPolynomial n`, and map each factor back with
   `finSuccEquivSymm`. This is correct on `pp` because every non-unit factor
   of an `x₀`-primitive polynomial involves `x₀`.
3. **Recurse** on `c` (one fewer variable) and embed each `n`-variable factor
   into `n+1` variables as a constant in `x₀` (`renameInjective … Fin.succ`).
4. **Merge** by multiplicity: a `pp`-factor involves `x₀`, a `c`-factor does
   not, so factors sharing a multiplicity are coprime and are combined by
   *multiplying* their square-free parts (`∏ (g·h)^m = pp · c = P`). Finally
   sort by the `AzMvPolynomial` `LinearOrder`, matching the univariate Yun's
   canonical-order convention.

Base case: a `0`-variable polynomial is a constant (a unit if nonzero), so it
factors to `[]`. The recursion is structural on the variable count `n`.

This is **Phase 1**: the computable implementation, the two instances the
tower Yun needs, and evaluation guards. Correctness (product, square-freeness,
pairwise coprimality, canonical order) is deferred to Phase 2.
-/

namespace Azurite.AzMvPolynomial

open Azurite Azurite.AzPolynomial

/-- **`GcdImpl` for the tower** `AzPolynomial (AzMvPolynomial n AzInt ord)`:
the univariate Yun runs its gcds in this tower ring. A tower gcd is computed
by lifting both arguments to `AzMvPolynomial (n+1)` (`finSuccEquivSymm`),
taking the normalized multivariate `AzMvPolynomial.gcd` there, and projecting
back (`finSuccEquiv`); the gcd-free part is the exact quotient. `GcdImpl`
carries no proof fields, so this is a pure operation instance. -/
instance instGcdImplAzMvPolynomial {n : ℕ} {ord : MonomialOrder} :
    GcdImpl (AzMvPolynomial n AzInt ord) where
  gcd P Q :=
    (AzMvPolynomial.gcd (finSuccEquivSymm P) (finSuccEquivSymm Q)).finSuccEquiv
  gcdGcdFreePart P Q :=
    let g := (AzMvPolynomial.gcd (finSuccEquivSymm P) (finSuccEquivSymm Q)).finSuccEquiv
    (g, if g = 0 then 0 else (exactDivQuoRem P g).1)

variable {n : ℕ} {ord : MonomialOrder}

/-- Insert `(g, e)` into a multiplicity-keyed list, **multiplying** the
square-free parts when the multiplicity `e` is already present. -/
def insertMult (acc : List (AzMvPolynomial n AzInt ord × ℕ))
    (g : AzMvPolynomial n AzInt ord) (e : ℕ) : List (AzMvPolynomial n AzInt ord × ℕ) :=
  match acc with
  | [] => [(g, e)]
  | (g', e') :: rest =>
    if e' = e then (g * g', e') :: rest else (g', e') :: insertMult rest g e

/-- Merge a list of `(square-free part, multiplicity)` pairs, combining pairs
of equal multiplicity by multiplying their square-free parts. -/
def mergeByMult (l : List (AzMvPolynomial n AzInt ord × ℕ)) :
    List (AzMvPolynomial n AzInt ord × ℕ) :=
  l.foldl (fun acc ge => insertMult acc ge.1 ge.2) []

/-- **Multivariate square-free factorization** (recursive Yun, splitting off
`x₀`). Structural recursion on the variable count `n`; the base case `n = 0`
(a constant) is `[]`. -/
def mvSquarefreeFactorization {ord : MonomialOrder} :
    {n : ℕ} → AzMvPolynomial n AzInt ord → List (AzMvPolynomial n AzInt ord × ℕ)
  | 0, _ => []
  | (m + 1), P =>
    let c := AzMvPolynomial.content P
    let pp := AzMvPolynomial.primitivePart P
    -- Yun w.r.t. `x₀` on the `x₀`-primitive part, in the tower ring
    let ppFactors := (AzPolynomial.squarefreeFactorization (finSuccEquiv pp)).map
      (fun ge => (finSuccEquivSymm ge.1, ge.2))
    -- factor the content (one fewer variable), embed as constants in `x₀`
    let cFactors := (mvSquarefreeFactorization c).map
      (fun ge => (renameInjective ge.1 Fin.succ (Fin.succ_injective m), ge.2))
    (mergeByMult (ppFactors ++ cFactors)).mergeSort (fun a b => a.1 ≤ b.1)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩
private instance : Fact (3 ≤ 26) := ⟨by omega⟩

private def p2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (parseStrWith (XyzVar 2) s).getD 0
private def p3 (s : String) : AzMvPolynomial 3 AzInt .Degrevlex :=
  (parseStrWith (XyzVar 3) s).getD 0
private def s2 (l : List (AzMvPolynomial 2 AzInt .Degrevlex × ℕ)) : List (String × ℕ) :=
  l.map (fun ge => (ge.1.toStrWith (XyzVar 2), ge.2))
private def s3 (l : List (AzMvPolynomial 3 AzInt .Degrevlex × ℕ)) : List (String × ℕ) :=
  l.map (fun ge => (ge.1.toStrWith (XyzVar 3), ge.2))

-- `(x+y)²·(x−y)`: two square-free classes, sorted `x−y < x+y`
#guard s2 (mvSquarefreeFactorization (p2 "x^3+x^2*y-x*y^2-y^3")) == [("x-y", 1), ("x+y", 2)]
-- pure monomial `x²·y³`: distinct multiplicities on two variables
#guard s2 (mvSquarefreeFactorization (p2 "x^2*y^3")) == [("y", 3), ("x", 2)]
-- `(x²−y²)²`: a single square-free polynomial at multiplicity 2 (NOT split)
#guard s2 (mvSquarefreeFactorization (p2 "x^4-2*x^2*y^2+y^4")) == [("x^2-y^2", 2)]
-- pure content: `y²·(x+1)` — the `y²` factor lives entirely in the content,
-- exercising the recursion + embedding
#guard s2 (mvSquarefreeFactorization (p2 "x*y^2+y^2")) == [("y", 2), ("x+1", 1)]
-- a square-free input: a single class at multiplicity 1
#guard s2 (mvSquarefreeFactorization (p2 "x^2+y^2+1")) == [("x^2+y^2+1", 1)]
-- three variables: `x²·y·z³`
#guard s3 (mvSquarefreeFactorization (p3 "x^2*y*z^3")) == [("z", 3), ("y", 1), ("x", 2)]
-- three variables, square-free
#guard s3 (mvSquarefreeFactorization (p3 "x^2+y^2+z^2")) == [("x^2+y^2+z^2", 1)]

end Tests

end Azurite.AzMvPolynomial
