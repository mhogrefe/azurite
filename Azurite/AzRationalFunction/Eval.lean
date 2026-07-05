import Azurite.AzRationalFunction.Parse
import Azurite.AzPolynomial.Eval
import Azurite.AzInt.Pow

/-!
# Evaluation at a point

`AzPolynomial.evalAzRat`: evaluate an integer polynomial at a rational
point `a/b` through the house `evalSpecial` (homogenized Horner,
`evalSpecial p a b = bⁿ · p(a/b)`) — all-integer arithmetic with a single
rational normalization at the end (no per-step gcd reductions).

`AzRationalFunction.evalAzRat` / `evalAzInt`: evaluate a rational function,
returning `none` at a pole (where the denominator part vanishes) and the
exact rational value otherwise.
-/

namespace Azurite.AzPolynomial

/-- Evaluate an integer polynomial at a rational point `x = ±a/b`:
`p(a/b) = evalSpecial p a b / b^n` — the house homogenized Horner
(`evalSpecial p a b = bⁿ · p(a/b)`, all-integer), with a single rational
normalization at the end. -/
def evalAzRat (p : AzPolynomial AzInt) (x : AzRat) : AzRat :=
  let a : AzInt := ⟨x.sign, x.num, x.zero_sign⟩
  let b : AzInt := ⟨true, x.den, fun _ => rfl⟩
  AzRat.ofAzInts (p.evalSpecial a b) (b.pow (p.coeffs.size - 1))

end Azurite.AzPolynomial

namespace Azurite.AzRationalFunction

open Azurite.AzPolynomial

/-- Evaluate at a rational point; `none` at a pole. -/
def evalAzRat (r : AzRationalFunction) (x : AzRat) : Option AzRat :=
  let d := AzPolynomial.evalAzRat r.den x
  if d = 0 then none
  else some (r.factor * (AzPolynomial.evalAzRat r.num x / d))

/-- Evaluate at an integer point; `none` at a pole. All-integer Horner on
the two parts, one rational normalization. -/
def evalAzInt (r : AzRationalFunction) (z : AzInt) : Option AzRat :=
  let d := AzPolynomial.eval r.den z
  if d = 0 then none
  else some (r.factor * AzRat.ofAzInts (AzPolynomial.eval r.num z) d)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def rr (s : String) : AzRationalFunction := (parse s).get!
private def qq (s : String) : AzRat := (Azurite.AzRat.parse s).get!
private def zz (s : String) : AzInt := (AzInt.parse s).get!

-- polynomial at a rational: `(x^2+1)(1/2) = 5/4`
#guard Azurite.AzRat.toString (AzPolynomial.evalAzRat ((parseAzPolynomial "x^2+1").get!) (qq "1/2")) == "5/4"
#guard Azurite.AzRat.toString (AzPolynomial.evalAzRat ((parseAzPolynomial "2*x^3-x").get!) (qq "-3/2")) == "-21/4"
#guard Azurite.AzRat.toString (AzPolynomial.evalAzRat ((parseAzPolynomial "7").get!) (qq "100/3")) == "7"
#guard Azurite.AzRat.toString (AzPolynomial.evalAzRat (0 : AzPolynomial AzInt) (qq "5/3")) == "0"
-- rational function at rational points
#guard ((rr "(x-1)/2").evalAzRat (qq "1/2")).map ToString.toString == some "-1/4"
#guard ((rr "(x^2+1)/(x-1)").evalAzRat (qq "3")).map ToString.toString == some "5"
#guard ((rr "(x^2+1)/(x-1)").evalAzRat (qq "1/2")).map ToString.toString == some "-5/2"
#guard ((rr "-3/4").evalAzRat (qq "17/5")).map ToString.toString == some "-3/4"
-- poles
#guard (rr "(x^2+1)/(x-1)").evalAzRat (qq "1") == none
#guard (rr "1/x").evalAzRat (qq "0") == none
-- integer points
#guard ((rr "(x^2+1)/(x-1)").evalAzInt (zz "3")).map ToString.toString == some "5"
#guard (rr "(x^2+1)/(x-1)").evalAzInt (zz "1") == none
#guard ((rr "x/2").evalAzInt (zz "-7")).map ToString.toString == some "-7/2"
-- the two evaluators agree on integer points
#guard ((rr "(2*x^2-2)/(4*x+4)").evalAzInt (zz "5")).map ToString.toString
    == ((rr "(2*x^2-2)/(4*x+4)").evalAzRat ((zz "5").toAzRat)).map ToString.toString

end Tests

end Azurite.AzRationalFunction
