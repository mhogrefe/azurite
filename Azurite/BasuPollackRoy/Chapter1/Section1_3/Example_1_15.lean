/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Instances
import Azurite.AzPolynomial.SRemS
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.CoeffStr

/-!
# BPR Example 1.15

The signed remainder sequence of `P` and `P'` for the general quartic
`P = x⁴ + a·x² + b·x + c ∈ ℚ(a,b,c)[x]`.

The coefficient field `ℚ(a,b,c)` is realized as the computable field
`AzMvRationalFunction 3 .Degrevlex` (variables `0,1,2 = a,b,c`, displayed via
`AbcVar 3`), which is `≃+*`-equivalent to `FractionRing (MvPolynomial (Fin 3) ℚ)`.
The signed remainder sequence is `Azurite.AzPolynomial.sRemSList P P' 5`,
computed *entirely* over that field — a stress test of the `AzMvRationalFunction`
arithmetic. The sequence terminates after five nonzero entries; the last is a
(nonzero) constant, a greatest common divisor of `P` and `P'` up to a unit, so
the general quartic is squarefree over `ℚ(a,b,c)`.

The entries are stringified with `AzPolynomial.toStrWithCoeff`, printing each
`ℚ(a,b,c)`-coefficient via `AzMvRationalFunction.toStrWith (AbcVar 3)` and
parenthesizing the non-atomic ones. All values below are checked at build time.
-/

namespace Azurite.BPR.Example_1_15

open Azurite Azurite.AzPolynomial

/-- The coefficient field `ℚ(a,b,c)`, computably. -/
abbrev Q3 := AzMvRationalFunction 3 .Degrevlex

instance : Fact (3 ≤ 26) := ⟨by omega⟩

/-- The rational function `a` (variable `0`). -/
def a : Q3 := AzMvRationalFunction.ofMvPolynomial (AzMvPolynomial.X 0)
/-- The rational function `b` (variable `1`). -/
def b : Q3 := AzMvRationalFunction.ofMvPolynomial (AzMvPolynomial.X 1)
/-- The rational function `c` (variable `2`). -/
def c : Q3 := AzMvRationalFunction.ofMvPolynomial (AzMvPolynomial.X 2)

/-- `P = x⁴ + a·x² + b·x + c ∈ ℚ(a,b,c)[x]`. -/
def P : AzPolynomial Q3 :=
  monomial 4 1 + monomial 2 a + monomial 1 b + monomial 0 c

/-- `P' = 4x³ + 2a·x + b`, the formal derivative of `P`. -/
def P' : AzPolynomial Q3 := derivative P

/-- Render an `AzPolynomial ℚ(a,b,c)` in `x`, coefficients via `AbcVar 3`. -/
def render (p : AzPolynomial Q3) : String :=
  toStrWithCoeff (fun q => AzMvRationalFunction.toStrWith (AbcVar 3) q) p

-- Sanity: `P` and `P'` render as stated.
#guard render P == "x^4+a*x^2+b*x+c"
#guard render P' == "4*x^3+2*a*x+b"

-- The full signed remainder sequence of `P` and `P'` over `ℚ(a,b,c)`
-- (five nonzero entries; the last is the unit-normalized gcd — a constant).
#guard (sRemSList P P' 5).map render ==
  [ "x^4+a*x^2+b*x+c",
    "4*x^3+2*a*x+b",
    "(-a/2)*x^2+(-3*b/4)*x+(-c)",
    "((-2*a^3-9*b^2+8*a*c)/a^2)*x+((-a^2*b-12*b*c)/a^2)",
    "((-4*a^5*b^2+16*a^6*c-27*a^2*b^4+144*a^3*b^2*c-128*a^4*c^2+256*a^2*c^3)/(16*a^6+144*a^3*b^2-128*a^4*c+324*b^4-576*a*b^2*c+256*a^2*c^2))" ]

-- The last nonzero entry is a constant (degree 0): a gcd of `P`, `P'` up to a
-- unit, so the general quartic is squarefree over `ℚ(a,b,c)`.
#guard ((sRemSList P P' 5).getLast!).natDegree == 0
-- The next term is `0` — the sequence has terminated.
#guard sRemS P P' 5 == 0

end Azurite.BPR.Example_1_15
