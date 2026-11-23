/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ParseBase
import Azurite.AzInt.Parse
import Azurite.Rounding.Mode

/-!
# Parsing Malachite's demo output

Malachite's demos print one line per case in a stable `input = output` format, using Rust's
`Display` and `Debug` renderings: decimal naturals, `(a, b)` tuples, `[a, b, c]` vectors,
`Some(x)`/`None` options, `Less`/`Equal`/`Greater` orderings, and `Floor`/`Ceiling`/`Down`/`Up`/
`Nearest`/`Exact` rounding modes; a borrowed operand prints as `&x` and a borrowed receiver as
`(&x)`. The helpers here take those apart. Every parser returns `Option`, and the oracle treats a
parse failure as an error: an unrecognized line is never skipped, so a change in a demo's output
format cannot make a run pass vacuously.
-/

namespace Azurite.Oracle

open Azurite

/-- Why a check failed: the line could not be read as a record of the mode's shape, or it could
and Malachite's value disagrees with Azurite's. The runner treats the two differently: a
multiline mode joins an unreadable record with the lines that follow it, but a disagreement is
final, so that a wrong result can never be hidden by the joining. -/
inductive Failure where
  | unreadable (msg : String)
  | disagreement (msg : String)

def Failure.message : Failure → String
  | .unreadable msg => msg
  | .disagreement msg => msg

/-- A check's verdict: `.ok ()` when the line agrees with Azurite. -/
abbrev Verdict := Except Failure Unit

/-- A line that does not have the shape the check reads. -/
def fail {α : Type} (msg : String) : Except Failure α := .error (.unreadable msg)

/-- A readable line whose values are inconsistent with Azurite's. -/
def disagree {α : Type} (msg : String) : Except Failure α := .error (.disagreement msg)

/-- `Option` to `Except`, naming what failed to parse. -/
def expect {α : Type} (what : String) : Option α → Except Failure α
  | some a => .ok a
  | none => fail s!"could not parse {what}"

/-- The verdict for a computed value against the printed one. -/
def expectEq {α : Type} [BEq α] [ToString α] (what : String) (computed printed : α) : Verdict :=
  if computed == printed then .ok ()
  else disagree s!"{what}: Azurite computed {computed}, Malachite printed {printed}"

/-- Removes leading and trailing ASCII whitespace. -/
def trim (s : String) : String := s.trimAscii.toString

/-- The string without its first `n` characters. -/
def dropChars (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- The string without its last `n` characters. -/
def dropRightChars (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))

/-- Whether the group opened by the first character closes at the last one, so that the whole
string is a single `openC`…`closeC` group. -/
def isWrapped (s : String) (openC closeC : Char) : Bool := Id.run do
  let cs := s.toList
  if cs.head? != some openC || cs.getLast? != some closeC then return false
  let mut depth := 0
  let mut i := 0
  for c in cs do
    if c == openC then depth := depth + 1
    else if c == closeC then depth := depth - 1
    i := i + 1
    if depth == 0 && i < cs.length then return false
  return true

/-- Strips one layer of `(`…`)` if it wraps the whole string. -/
def unwrapParens (s : String) : String :=
  if isWrapped s '(' ')' then dropRightChars (dropChars s 1) 1 else s

/-- A borrowed operand prints as `&x` and a borrowed receiver as `(&x)`; both mean `x`. -/
def stripRef (s : String) : String :=
  let s := unwrapParens (trim s)
  let s := if s.startsWith "&" then dropChars s 1 else s
  unwrapParens (trim s)

/-- Splits at the top-level occurrences of `sep`, ignoring those nested in parentheses or
brackets. -/
def splitTopLevel (s : String) (sep : Char) : List String := Id.run do
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for c in s.toList do
    if c == '(' || c == '[' then
      depth := depth + 1
      cur := cur.push c
    else if c == ')' || c == ']' then
      depth := depth - 1
      cur := cur.push c
    else if c == sep && depth == 0 then
      parts := parts.push cur
      cur := ""
    else
      cur := cur.push c
  parts := parts.push cur
  return parts.toList

/-- Splits `lhs = rhs` at the last ` = `, the one the demo printed between input and output. -/
def splitEquals (s : String) : Option (String × String) :=
  match (s.splitOn " = ").reverse with
  | rhs :: p :: ps => some (" = ".intercalate (p :: ps).reverse, trim rhs)
  | _ => none

/-- The comma-separated arguments of a call, each with its borrow marker removed. -/
def splitArgs (args : String) : List String :=
  if (trim args).isEmpty then [] else (splitTopLevel args ',').map stripRef

/-- Takes apart `recv.method(arg, …) = result`, returning the receiver (with `&` and wrapping
parentheses removed), the arguments, and the result. -/
def methodCall (line method : String) : Option (String × List String × String) := do
  let (lhs, rhs) ← splitEquals line
  match lhs.splitOn s!".{method}(" with
  | [recv, rest] =>
    guard (rest.endsWith ")")
    pure (stripRef recv, splitArgs (dropRightChars rest 1), rhs)
  | _ => none

/-- Takes apart `name(arg, …) = result`, returning the arguments and the result. -/
def functionCall (line name : String) : Option (List String × String) := do
  let (lhs, rhs) ← splitEquals line
  guard (lhs.startsWith s!"{name}(" && lhs.endsWith ")")
  pure (splitArgs (dropRightChars (dropChars lhs (name.length + 1)) 1), rhs)

/-- Takes apart `x op y = z` for an infix operator printed with spaces around it. -/
def binaryOp (line op : String) : Option (String × String × String) := do
  let (lhs, rhs) ← splitEquals line
  match lhs.splitOn s!" {op} " with
  | [x, y] => pure (stripRef x, stripRef y, rhs)
  | _ => none

/-- A decimal natural. Anything but digits is rejected, so that a stray `&` or a sign cannot be
read as a number. -/
def parseAzNat (s : String) : Option AzNat :=
  let s := trim s
  if s.isEmpty || !(s.toList.all Char.isDigit) then none else AzNat.parse s

/-- A decimal integer: an optional `-` and then digits, so that `-0` and a stray sign are
rejected. -/
def parseAzInt (s : String) : Option AzInt :=
  let s := trim s
  let digits := if s.startsWith "-" then dropChars s 1 else s
  if digits.isEmpty || !(digits.toList.all Char.isDigit) || s == "-0" then none
  else AzInt.parse s

def parseNat (s : String) : Option Nat := (trim s).toNat?

def parseBool (s : String) : Option Bool :=
  match trim s with
  | "true" => some true
  | "false" => some false
  | _ => none

def parseInt (s : String) : Option Int := (trim s).toInt?

def parseOrdering (s : String) : Option Ordering :=
  match trim s with
  | "Less" => some .lt
  | "Equal" => some .eq
  | "Greater" => some .gt
  | _ => none

/-- Malachite's name for an ordering. -/
def orderingName : Ordering → String
  | .lt => "Less"
  | .eq => "Equal"
  | .gt => "Greater"

/-- Malachite's `RoundingMode` has one mode Azurite's lacks: `Exact`, which panics when any
rounding would be needed. A demo line printed with `Exact` therefore records an exact result. -/
inductive Rounding where
  | mode (m : RoundingMode)
  | exact

def parseRounding (s : String) : Option Rounding :=
  match trim s with
  | "Floor" => some (.mode .Floor)
  | "Ceiling" => some (.mode .Ceiling)
  | "Down" => some (.mode .Down)
  | "Up" => some (.mode .Up)
  | "Nearest" => some (.mode .Nearest)
  | "Exact" => some .exact
  | _ => none

/-- A `(a, b)` tuple, as two strings. -/
def parseTuple2 (s : String) : Option (String × String) :=
  let s := trim s
  if isWrapped s '(' ')' then
    match splitTopLevel (dropRightChars (dropChars s 1) 1) ',' with
    | [a, b] => some (trim a, trim b)
    | _ => none
  else none

/-- A `(a, b, c)` triple, as three strings. -/
def parseTuple3 (s : String) : Option (String × String × String) :=
  let s := trim s
  if isWrapped s '(' ')' then
    match splitTopLevel (dropRightChars (dropChars s 1) 1) ',' with
    | [a, b, c] => some (trim a, trim b, trim c)
    | _ => none
  else none

/-- A `[a, b, …]` vector, as strings. -/
def parseList (s : String) : Option (List String) :=
  let s := trim s
  if isWrapped s '[' ']' then
    let inner := trim (dropRightChars (dropChars s 1) 1)
    some (if inner.isEmpty then [] else (splitTopLevel inner ',').map trim)
  else none

/-- A `Some(x)` or `None`, the payload as a string. -/
def parseOption (s : String) : Option (Option String) :=
  let s := trim s
  if s == "None" then some none
  else if s.startsWith "Some(" && s.endsWith ")" then
    some (some (trim (dropRightChars (dropChars s 5) 1)))
  else none

/-- An `Ok(x)` or `Err(())`, the payload as a string: how `FromStr` reports its result. -/
def parseResult (s : String) : Option (Option String) :=
  let s := trim s
  if s == "Err(())" then some none
  else if s.startsWith "Ok(" && s.endsWith ")" then
    some (some (trim (dropRightChars (dropChars s 3) 1)))
  else none

/-- Renders a `FromStr` result the way Rust's `Debug` does. -/
def resultString {α : Type} [ToString α] : Option α → String
  | some a => s!"Ok({a})"
  | none => "Err(())"

/-- Renders an option the way Rust's `Debug` does. -/
def optionString {α : Type} [ToString α] : Option α → String
  | some a => s!"Some({a})"
  | none => "None"

def parseAzNats (ss : List String) : Option (List AzNat) := ss.mapM parseAzNat

/-- A vector of 64-bit limbs or digits. -/
def parseLimbs (ss : List String) : Option (Array UInt64) := do
  let ns ← ss.mapM parseNat
  guard (ns.all (· < 2 ^ 64))
  pure (ns.map UInt64.ofNat).toArray

/-- A pair rendered as Malachite renders `(value, ordering)`. -/
def pairString {α : Type} [ToString α] (a : α) (o : Ordering) : String :=
  s!"({a}, {orderingName o})"

/-- Whether `c` can be part of a Rust identifier. -/
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- A method name without the suffixes that name its ownership variant (`_val_ref`, `_ref_ref`,
`_ref`, `_assign`, `_assign_ref`, …), which is the name of the operation itself. -/
partial def stripOwnershipSuffixes (name : String) : String :=
  match ["_val", "_ref", "_assign"].find? (name.endsWith ·) with
  | some s => stripOwnershipSuffixes (dropRightChars name s.length)
  | none => name

/-- The line with every called method or associated function (`.name(` or `::name(`) renamed
by `stripOwnershipSuffixes`. -/
def stripCalledOwnershipSuffixes (line : String) : String := Id.run do
  let cs := line.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if isIdentChar c && (i == 0 || !isIdentChar cs[i - 1]!) then
      let mut j := i
      while j < cs.size && isIdentChar cs[j]! do
        j := j + 1
      let word := String.ofList (cs.extract i j).toList
      let called :=
        j < cs.size && cs[j]! == '(' && i > 0 && (cs[i - 1]! == '.' || cs[i - 1]! == ':')
      out := out ++ (if called then stripOwnershipSuffixes word else word)
      i := j
    else
      out := out.push c
      i := i + 1
  return out

/-- An in-place demo line, `x := X; x.op(args) = o; x = Z`, `x := X; x.op(args); x = Z`, or
`x := X; x op= Y; x = Z`, as the out-of-place line it stands for: `(X).op(args) = (Z, o)`,
`(X).op(args) = Z` (`-(X) = Z` for `neg` and `|X| = Z` for `abs`, as their demos print them), or
`(X) op Y = Z`. -/
def assignmentAsCall (line : String) : Option String := do
  let [a, b, c] := (line.splitOn "; ").map trim | none
  let [v, x] := a.splitOn " := " | none
  guard (c.startsWith s!"{v} = ")
  let z := dropChars c (v.length + 3)
  if b.startsWith s!"{v}." then
    let call := dropChars b (v.length + 1)
    match splitEquals call with
    | some (lhs, o) => pure s!"({x}).{lhs} = ({z}, {o})"
    | none =>
      match stripOwnershipSuffixes ((call.splitOn "(").headD "") with
      | "neg" => pure s!"-({x}) = {z}"
      | "abs" => pure s!"|{x}| = {z}"
      | _ => pure s!"({x}).{call} = {z}"
  else
    match b.splitOn " " with
    | v' :: op :: rest =>
      guard (v' == v && op.length ≥ 2 && op.endsWith "=")
      pure s!"({x}) {dropRightChars op 1} {" ".intercalate rest} = {z}"
    | _ => none

/-- A line of a demo of an in-place or borrowing variant of an operation, rewritten as the lines
the operation's own demos may print: in-place forms become out-of-place ones
(`assignmentAsCall`), ownership suffixes are dropped from called names, and a borrowed `|&x|`
becomes `|x|`. Since `Float` prints its absolute value and negation as `|x|` and `-(x)` and
`BigExponentFloat` as `(x).abs()` and `(x).neg()`, a line of either kind comes in both forms. -/
def normalizedOwnershipForms (line : String) : List String :=
  let line := stripCalledOwnershipSuffixes (((assignmentAsCall line).getD line).replace "|&" "|")
  match splitEquals line with
  | some (lhs, z) =>
    if lhs.startsWith "|" && lhs.endsWith "|" then
      [line, s!"({dropRightChars (dropChars lhs 1) 1}).abs() = {z}"]
    else if lhs.startsWith "-(" && lhs.endsWith ")" then
      [line, s!"{dropChars lhs 1}.neg() = {z}"]
    else [line]
  | none => [line]

/-- Lets a check read the lines of the demos of an operation's in-place and borrowing variants:
a line the check cannot read is checked again in each form `normalizedOwnershipForms` gives,
taking the first form the check can read. A line the check reads as printed is never
rewritten. -/
def withOwnershipForms (check : String → Verdict) (line : String) : Verdict :=
  match check line with
  | .error (.unreadable msg) =>
    let forms := (normalizedOwnershipForms line).filter (· != line)
    match forms.map check |>.find? (fun v => !(v matches .error (.unreadable _))) with
    | some verdict => verdict
    | none => .error (.unreadable msg)
  | verdict => verdict

end Azurite.Oracle
