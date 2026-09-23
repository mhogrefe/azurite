/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Parse
import Azurite.AzMvPolynomial.Derivative

/-!
# Partial derivatives of multivariate rational functions

The partial derivative `∂/∂xⱼ` of an `AzMvRationalFunction`, via the quotient
rule through a single normalization: the integer-polynomial combination
`(∂ⱼN)·D − N·(∂ⱼD)` over `D²`, with the constant rational factor multiplying
through unchanged (it is constant in every variable, so its derivative
contributes nothing). Junk-free: the denominator is always nonzero.

This is the multivariate, per-variable generalization of the univariate
`derivative`; `AzMvPolynomial.pderivGeneral j` supplies the polynomial partial
derivative. It needs only `ofNumDen` and polynomial arithmetic (no field), so
it precedes `Instances`.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- **Partial derivative** `∂r/∂xⱼ` — the quotient rule through one
normalization. -/
def pderiv (r : AzMvRationalFunction n ord) (j : Fin n) : AzMvRationalFunction n ord :=
  let T := AzMvPolynomial.pderivGeneral j r.num * r.den
    - r.num * AzMvPolynomial.pderivGeneral j r.den
  ofNumDen
    ((⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt) • T)
    ((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • (r.den * r.den))

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def r2 (s : String) : AzMvRationalFunction 2 .Degrevlex :=
  (parseStrWith (XyzVar 2) s).getD 0

private def render (r : AzMvRationalFunction 2 .Degrevlex) : String :=
  toStrWith (XyzVar 2) r

-- polynomial case (denominator 1): partials of `x²y`
#guard render (pderiv (r2 "x^2*y") 0) == "2*x*y"
#guard render (pderiv (r2 "x^2*y") 1) == "x^2"
-- a simple reciprocal
#guard render (pderiv (r2 "1/x") 0) == "-1/x^2"
-- a genuine fraction: `∂/∂x ((x+y)/(x-y)) = -2y/(x-y)²`
#guard render (pderiv (r2 "(x+y)/(x-y)") 0) == "-2*y/(x^2-2*x*y+y^2)"
#guard render (pderiv (r2 "(x+y)/(x-y)") 1) == "2*x/(x^2-2*x*y+y^2)"
-- differentiating w.r.t. a variable that does not appear → 0
#guard render (pderiv (r2 "x^2") 1) == "0"
#guard pderiv (r2 "x^2") 1 == 0

end Tests

end Azurite.AzMvRationalFunction
