/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Parse
import Azurite.AzMvPolynomial.Eval
import Azurite.AzMvPolynomial.Cast

/-!
# Evaluation at a point

`AzMvPolynomial.evalAzRat`: evaluate an integer multivariate polynomial at a
rational point `x : Fin n → AzRat` — cast the `AzInt` coefficients to `AzRat`
(`mapAzIntToAzRat`) and run the direct sum-of-monomials `AzMvPolynomial.eval`.

`AzMvRationalFunction.evalAzRat` / `evalAzInt`: evaluate a rational function at
a rational / integer tuple, returning `none` at a pole (where the denominator
part vanishes) and the exact rational value `factor · num(x)/den(x)` otherwise.
The integer-point evaluator uses the all-integer `AzMvPolynomial.eval` on the
two parts with a single rational normalization.
-/

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Evaluate an integer multivariate polynomial at a rational point: cast the
`AzInt` coefficients to `AzRat` and evaluate. -/
def evalAzRat (p : AzMvPolynomial n AzInt ord) (x : Fin n → AzRat) : AzRat :=
  (p.mapAzIntToAzRat).eval x

end Azurite.AzMvPolynomial

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Evaluate at a rational tuple; `none` at a pole. -/
def evalAzRat (r : AzMvRationalFunction n ord) (x : Fin n → AzRat) : Option AzRat :=
  let d := AzMvPolynomial.evalAzRat r.den x
  if d = 0 then none
  else some (r.factor * (AzMvPolynomial.evalAzRat r.num x / d))

/-- Evaluate at an integer tuple; `none` at a pole. All-integer evaluation on
the two parts, one rational normalization. -/
def evalAzInt (r : AzMvRationalFunction n ord) (z : Fin n → AzInt) : Option AzRat :=
  let d := AzMvPolynomial.eval r.den z
  if d = 0 then none
  else some (r.factor * AzRat.ofAzInts (AzMvPolynomial.eval r.num z) d)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (1 ≤ 26) := ⟨by omega⟩
private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def p1 (s : String) : AzMvPolynomial 1 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 1) s).getD 0
private def p2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 2) s).getD 0
private def r1 (s : String) : AzMvRationalFunction 1 .Degrevlex :=
  (parseStrWith (XyzVar 1) s).getD 0
private def r2 (s : String) : AzMvRationalFunction 2 .Degrevlex :=
  (parseStrWith (XyzVar 2) s).getD 0
private def qq (s : String) : AzRat := (Azurite.AzRat.parse s).get!
private def zz (s : String) : AzInt := (AzInt.parse s).get!

-- polynomial at a rational point (single variable): `(x^2+1)(1/2) = 5/4`
#guard Azurite.AzRat.toString (AzMvPolynomial.evalAzRat (p1 "x^2+1") ![qq "1/2"]) == "5/4"
-- polynomial at a rational point (two variables): `x^2+y` at `(1/2, 3) = 13/4`
#guard Azurite.AzRat.toString
    (AzMvPolynomial.evalAzRat (p2 "x^2+y") ![qq "1/2", qq "3"]) == "13/4"
-- constant polynomial ignores the point
#guard Azurite.AzRat.toString (AzMvPolynomial.evalAzRat (p2 "7") ![qq "100/3", qq "-1"]) == "7"
-- zero polynomial
#guard Azurite.AzRat.toString
    (AzMvPolynomial.evalAzRat (0 : AzMvPolynomial 2 AzInt .Degrevlex) ![qq "5/3", qq "2"]) == "0"

-- rational function at rational points
#guard ((r1 "(x^2+1)/(x-1)").evalAzRat ![qq "3"]).map ToString.toString == some "5"
#guard ((r1 "(x^2+1)/(x-1)").evalAzRat ![qq "1/2"]).map ToString.toString == some "-5/2"
-- two-variable example: `(x+y)/(x-y)` at `(3, 1) = 2`
#guard ((r2 "(x+y)/(x-y)").evalAzRat ![qq "3", qq "1"]).map ToString.toString == some "2"
#guard ((r2 "-3/4").evalAzRat ![qq "17/5", qq "2"]).map ToString.toString == some "-3/4"

-- poles (denominator vanishes → none)
#guard (r1 "(x^2+1)/(x-1)").evalAzRat ![qq "1"] == none
#guard (r2 "1/(x*y)").evalAzRat ![qq "0", qq "5"] == none

-- integer points
#guard ((r1 "(x^2+1)/(x-1)").evalAzInt ![zz "3"]).map ToString.toString == some "5"
#guard (r1 "(x^2+1)/(x-1)").evalAzInt ![zz "1"] == none
#guard ((r2 "(x+y)/(x-y)").evalAzInt ![zz "3", zz "1"]).map ToString.toString == some "2"

-- the two evaluators agree on integer points
#guard ((r2 "(x+y)/(x-y)").evalAzInt ![zz "5", zz "2"]).map ToString.toString
    == ((r2 "(x+y)/(x-y)").evalAzRat ![(zz "5").toAzRat, (zz "2").toAzRat]).map ToString.toString

end Tests

end Azurite.AzMvRationalFunction
