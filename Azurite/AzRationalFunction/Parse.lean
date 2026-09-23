/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRationalFunction.ToString

/-!
# Parsing an `AzRationalFunction`

Liberal parser: `num/den` or just `num`, where each component may be
unnormalized (any integer-polynomial fraction — the normalizing constructor
reduces it) and may carry one level of unnecessary parentheses. A zero
denominator does not parse.
-/

namespace Azurite.AzRationalFunction

open Azurite.AzPolynomial

/-- Split at the first `/`. (No parenthesis-depth tracking needed: valid
components never contain a `/`, so the first slash is the separator, and on
invalid input the component parse fails regardless.) -/
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

/-- **Parse** a rational function: `num/den` or `num`, components possibly
unnormalized and possibly wrapped in one level of parentheses. -/
def parse (s : String) : Option AzRationalFunction :=
  let cs := s.toList
  match splitSlash cs with
  | none =>
    (parseAzPolynomial (String.ofList (stripParens cs))).map ofPolynomial
  | some (l, rr) => do
    let n ← parseAzPolynomial (String.ofList (stripParens l))
    let d ← parseAzPolynomial (String.ofList (stripParens rr))
    if d = 0 then none else some (ofNumDen n d)

-- ═══════════════════════════════════════════════════════════════════
-- Tests (string in via `parse`, string out via `toString`)
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- construction and normalization
#guard (parse "(2*x^2-2)/(4*x+4)").map toString == some "(x-1)/2"
#guard (parse "x/-2").map toString == some "-x/2"
#guard (parse "(x^2+1)/(x-1)").map toString == some "(x^2+1)/(x-1)"
#guard (parse "3*x^2/(x+1)").map toString == some "3*x^2/(x+1)"
#guard (parse "6*x/-4").map toString == some "-3*x/2"
#guard (parse "0/(7*x+7)").map toString == some "0"
#guard (parse "-6*x-9").map toString == some "-6*x-9"
-- liberal: one level of unnecessary parens
#guard (parse "(x+1)").map toString == some "x+1"
#guard (parse "(x)/(2)").map toString == some "x/2"
-- constants
#guard (parse "-3/4").map toString == some "-3/4"
#guard toString (0 : AzRationalFunction) == "0"
#guard toString (1 : AzRationalFunction) == "1"
-- canonical: the same function parses to the same value
#guard parse "2*x/(-4*x^2-4*x)" == parse "-x/(2*x^2+2*x)"
-- conversions agree with parsing
#guard (parse "x+1") == (parseAzPolynomial "x+1").map ofPolynomial
#guard toString (ofAzInt ((AzInt.parse "-5").get!)) == "-5"
#guard toString (ofAzRat ((Azurite.AzRat.parse "-3/4").get!)) == "-3/4"
-- rejections: zero denominator, malformed
#guard parse "x/0" == none
#guard parse "x//2" == none
-- the house polynomial parser reads the empty string as `0`
#guard parse "" == some 0

end Tests

end Azurite.AzRationalFunction
