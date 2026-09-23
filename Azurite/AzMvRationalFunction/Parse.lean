/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.ToString
import Azurite.AzMvPolynomial.Parse

/-!
# Parsing an `AzMvRationalFunction`

Liberal, Var-parametrized parser: `num/den` or just `num`, where each component
may be unnormalized (any integer-polynomial fraction — the normalizing
constructor reduces it) and may carry one level of unnecessary parentheses. A
zero denominator does not parse. Mirrors the univariate `AzRationalFunction`.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Split at the first `/`. (Valid components never contain a `/`, so the first
slash is the separator; on invalid input the component parse fails anyway.) -/
private def splitSlashAux : List Char → List Char →
    Option (List Char × List Char)
  | [], _ => none
  | '/' :: t, acc => some (acc.reverse, t)
  | c :: t, acc => splitSlashAux t (c :: acc)

/-- Split a candidate `num/den` at the first `/`, if any. -/
def splitSlash (cs : List Char) : Option (List Char × List Char) :=
  splitSlashAux cs []

/-- Strip one level of enclosing parentheses, if present. -/
def stripParens (cs : List Char) : List Char :=
  match cs with
  | '(' :: t =>
    match t.getLast? with
    | some ')' => t.dropLast
    | _ => cs
  | _ => cs

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

/-- **Parse** a rational function: `num/den` or `num`, components possibly
unnormalized and possibly wrapped in one level of parentheses. -/
def parseWith (cs : List Char) : Option (AzMvRationalFunction n ord) :=
  match splitSlash cs with
  | none =>
    (AzMvPolynomial.parseWith (R := AzInt) (ord := ord) F (stripParens cs)).map ofMvPolynomial
  | some (l, rr) => do
    let nm ← AzMvPolynomial.parseWith (R := AzInt) (ord := ord) F (stripParens l)
    let dm ← AzMvPolynomial.parseWith (R := AzInt) (ord := ord) F (stripParens rr)
    if dm = 0 then none else some (ofNumDen nm dm)

/-- **Parse** a rational function from a string. -/
@[inline] def parseStrWith (s : String) : Option (AzMvRationalFunction n ord) :=
  parseWith F s.toList

end Display

-- ═══════════════════════════════════════════════════════════════════
-- Tests (string in via `parseStrWith`, string out via `toStrWith`)
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def rt (s : String) : Option String :=
  (parseStrWith (XyzVar 2) (ord := .Degrevlex) s).map (toStrWith (XyzVar 2))

-- construction and normalization
#guard rt "(2*x^2-2)/(4*x+4)" == some "(x-1)/2"
#guard rt "x/-2" == some "-x/2"
#guard rt "(x^2+1)/(x-1)" == some "(x^2+1)/(x-1)"
#guard rt "3*x^2/(x+1)" == some "3*x^2/(x+1)"
#guard rt "0/(7*x+7)" == some "0"
#guard rt "-6*x-9" == some "-6*x-9"
-- multivariate reduction
#guard rt "(x^2-y^2)/(x-y)" == some "x+y"
-- the multivariate `wrapDenominator` rule
#guard rt "1/(x*y)" == some "1/(x*y)"
#guard rt "1/x^2" == some "1/x^2"
#guard rt "1/(x^2*y)" == some "1/(x^2*y)"
#guard rt "x/(x*y)" == some "1/y"
-- liberal: one level of unnecessary parens
#guard rt "(x+y)" == some "x+y"
#guard rt "(x)/(2)" == some "x/2"
-- constants
#guard rt "-3/4" == some "-3/4"
#guard toStrWith (XyzVar 2) (0 : AzMvRationalFunction 2 .Degrevlex) == "0"
#guard toStrWith (XyzVar 2) (1 : AzMvRationalFunction 2 .Degrevlex) == "1"
-- canonical: the same function parses to the same value
#guard parseStrWith (XyzVar 2) (ord := .Degrevlex) "2*x/(-4*x^2-4*x*y)"
  == parseStrWith (XyzVar 2) (ord := .Degrevlex) "-x/(2*x^2+2*x*y)"
-- rejections: zero denominator, malformed
#guard parseStrWith (XyzVar 2) (ord := .Degrevlex) "x/0" == none
#guard parseStrWith (XyzVar 2) (ord := .Degrevlex) "x//2" == none

end Tests

end Azurite.AzMvRationalFunction
