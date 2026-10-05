/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzInt
import Azurite.AzRat.Add
import Azurite.AzRat.Sub
import Azurite.AzRat.Mul
import Azurite.AzRat.Div
import Azurite.AzRat.Unary
import Azurite.AzRat.Pow
import Azurite.AzRat.Shift
import Azurite.AzRat.Round
import Azurite.AzRat.Compare
import Azurite.AzRat.Construct
import Azurite.AzRat.Conversion
import Azurite.AzRat.ToString
import Azurite.AzRat.Parse
import Azurite.AzRat.FromSci
import Azurite.AzRat.ToSci
import Azurite.AzRat.LengthAfterPoint
import Azurite.AzRat.LogBase
import Azurite.AzRat.LogBase2

/-!
# Checks for Malachite's `Rational` against `AzRat`

One check per line shape that a `Rational` demo prints, as the `AzNat` and `AzInt` files have for
the `Natural` and `Integer` demos. Both libraries print a rational as `-1/3`, in lowest terms, so
the values are read with `parseAzRat` and compared structurally. The correspondence, and the
conventions encoded here (Malachite's `Exact` rounding mode in scientific notation as Azurite's
`toSciExact` predicate, its `from_str` grammar, its `ToSciOptions` fields), are documented on
Malachite's "Malachite for Azurite Users: Rationals" page.
-/

namespace Azurite.Oracle

open Azurite

/-- A rational as Malachite prints it: an optional `-`, digits, and optionally `/` and digits,
already in lowest terms. Anything else is rejected, so that `AzRat.parse`'s leniency (unreduced
fractions, base prefixes, a zero denominator) never makes a malformed line readable. -/
def parseAzRat (s : String) : Option AzRat := do
  let s := trim s
  let (n, d) ← match s.splitOn "/" with
    | [n] => some (n, "1")
    | [n, d] => some (n, d)
    | _ => none
  let n ← parseAzInt n
  let d ← parseAzNat d
  guard (d != (0 : AzNat))
  let q := AzRat.ofSignAzNats n.sign n.abs d
  guard (q.num == n.abs && q.den == d)
  pure q

/-! ### Field operations -/

/-- `x op y = z` for an infix operator on two rationals. -/
def checkRatBinaryOp (op : String) (f : AzRat → AzRat → AzRat) (line : String) : Verdict := do
  let (x, y, z) ← expect s!"an `x {op} y = z` line" (binaryOp line op)
  let x ← expect "x" (parseAzRat x)
  let y ← expect "y" (parseAzRat y)
  let z ← expect "z" (parseAzRat z)
  expectEq s!"x {op} y" (f x y) z

def checkRatAdd : String → Verdict := checkRatBinaryOp "+" AzRat.add

def checkRatSub : String → Verdict := checkRatBinaryOp "-" AzRat.sub

def checkRatMul : String → Verdict := checkRatBinaryOp "*" AzRat.mul

/-- Malachite panics on a zero divisor, so every printed line has a nonzero one. -/
def checkRatDiv : String → Verdict := checkRatBinaryOp "/" AzRat.div

/-- `name(x) = z` with a rational argument, or `|x| = z` (also `|&x| = z`) for `abs`. -/
def unaryRatLine (line name : String) : Except Failure (String × String) := do
  if name == "abs" then
    let (lhs, rhs) ← expect "an `|x| = z` line" (splitEquals line)
    if !(lhs.startsWith "|" && lhs.endsWith "|") then fail "not an `|x|` left-hand side"
    pure (stripRef (dropRightChars (dropChars lhs 1) 1), rhs)
  else
    let (args, res) ← expect s!"a `{name}(x) = z` line" (functionCall line name)
    match args with
    | [x] => pure (x, res)
    | _ => fail s!"{name} takes one argument"

/-- `name(x) = z` for a unary operation with a rational result. -/
def checkRatUnary (name : String) (f : AzRat → AzRat) (line : String) : Verdict := do
  let (x, res) ← unaryRatLine line name
  let x ← expect "x" (parseAzRat x)
  let z ← expect "z" (parseAzRat res)
  expectEq name (f x) z

/-- `-(x) = z`. -/
def checkRatNeg (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `-(x) = z` line" (splitEquals line)
  if !lhs.startsWith "-" then fail "not a negation"
  let x ← expect "x" (parseAzRat (stripRef (dropChars lhs 1)))
  let z ← expect "z" (parseAzRat rhs)
  expectEq "neg" (AzRat.neg x) z

def checkRatAbs : String → Verdict := checkRatUnary "abs" AzRat.abs

/-- Malachite panics on the reciprocal of zero, so every printed line has a nonzero input. -/
def checkRatReciprocal : String → Verdict := checkRatUnary "reciprocal" AzRat.inv

/-- `(x).pow(e) = z` with a `u64` or `i64` exponent: `zpow`, which covers both. -/
def checkRatPow (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.pow(e) = z` line" (methodCall line "pow")
  let e ← match args with
    | [e] => pure e
    | _ => fail "pow takes one argument"
  let x ← expect "x" (parseAzRat x)
  let e ← expect "exponent" (parseInt e)
  let z ← expect "z" (parseAzRat res)
  expectEq "pow" (AzRat.zpow x e) z

/-- `x << s = z` or `x >> s = z`; a negative count (from the signed demos) reverses the
direction. -/
def checkRatShift (op : String) (left : Bool) (line : String) : Verdict := do
  let (x, s, z) ← expect s!"an `x {op} s = z` line" (binaryOp line op)
  let x ← expect "x" (parseAzRat x)
  let s ← expect "shift" (parseInt s)
  let z ← expect "z" (parseAzRat z)
  let shifted :=
    if (s < 0) != left then AzRat.shiftLeft x s.natAbs else AzRat.shiftRight x s.natAbs
  expectEq op shifted z

def checkRatShl : String → Verdict := checkRatShift "<<" true

def checkRatShr : String → Verdict := checkRatShift ">>" false

/-! ### Rounding and logarithms -/

/-- `floor(x) = n` or `ceiling(x) = n`: `round` in the corresponding mode, ordering dropped. -/
def checkRatFloorCeiling (name : String) (mode : RoundingMode) (line : String) : Verdict := do
  let (x, res) ← unaryRatLine line name
  let x ← expect "x" (parseAzRat x)
  let n ← expect "n" (parseAzInt res)
  expectEq name (AzRat.round x mode).1 n

def checkRatFloor : String → Verdict := checkRatFloorCeiling "floor" .Floor

def checkRatCeiling : String → Verdict := checkRatFloorCeiling "ceiling" .Ceiling

/-- `Integer::rounding_from(x, rm) = (n, o)`. Under `Exact`, Malachite only prints a line when
`x` is an integer. -/
def checkRatRoundingFrom (line : String) : Verdict := do
  let (args, res) ← expect "an `Integer::rounding_from(x, rm) = (n, o)` line"
    (functionCall line "Integer::rounding_from")
  let (x, rm) ← match args with
    | [x, rm] => pure (x, rm)
    | _ => fail "rounding_from takes two arguments"
  let x ← expect "x" (parseAzRat x)
  let rm ← expect "rounding mode" (parseRounding rm)
  let (n, o) ← expect "(integer, ordering)" (parseTuple2 res)
  let n ← expect "integer" (parseAzInt n)
  let o ← expect "ordering" (parseOrdering o)
  let (an, ao) ← match rm with
    | .mode m => pure (AzRat.round x m)
    | .exact =>
      if x.den == (1 : AzNat) then pure ((AzRat.round x .Floor).1, .eq)
      else disagree "Malachite printed an Exact rounding of a non-integer"
  expectEq "rounding_from" (pairString an ao) (pairString n o)

/-- `name(x) = e` for a logarithm with an integer result; the `_abs` demos and the positive-only
ones print the same shape, and Azurite's functions take the absolute value. -/
def checkRatLog2 (names : List String) (f : AzRat → Int) (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `name(x) = e` line" (splitEquals line)
  let name ← match names.find? fun n => lhs.startsWith s!"{n}(" with
    | some n => pure n
    | none => fail s!"not a {names} line"
  let (args, res) ← expect s!"a `{name}(x) = e` line" (functionCall line name)
  let x ← match args with
    | [x] => pure x
    | _ => fail s!"{name} takes one argument"
  let x ← expect "x" (parseAzRat x)
  let e ← expect "e" (parseInt rhs)
  let _ := res
  expectEq name (f x) e

def checkRatFloorLogBase2 : String → Verdict :=
  checkRatLog2 ["floor_log_base_2_abs", "floor_log_base_2"] AzRat.floorLogBase2Abs

def checkRatCeilingLogBase2 : String → Verdict :=
  checkRatLog2 ["ceiling_log_base_2_abs", "ceiling_log_base_2"] AzRat.ceilingLogBase2Abs

/-- `x`, the base `b` (a `u64`), and the result of a `name(x, b) = r` line. -/
def logBaseLine (line name : String) : Except Failure (AzRat × UInt64 × String) := do
  let (args, res) ← expect s!"a `{name}(x, b) = r` line" (functionCall line name)
  let (x, b) ← match args with
    | [x, b] => pure (x, b)
    | _ => fail s!"{name} takes two arguments"
  let x ← expect "x" (parseAzRat x)
  let b ← parseUInt64 b
  if b < 2 then fail "the base is below 2"
  pure (x, b, res)

/-- `floor_log_base(x, b) = e` for a `u64` base and positive `x`. -/
def checkRatFloorLogBase (line : String) : Verdict := do
  let (x, b, res) ← logBaseLine line "floor_log_base"
  let e ← expect "e" (parseInt res)
  expectEq "floor_log_base" (AzRat.floorLogBaseAbs b x) e

/-- `ceiling_log_base(x, b) = e`: the floor, plus one unless `b^e = |x|`. -/
def checkRatCeilingLogBase (line : String) : Verdict := do
  let (x, b, res) ← logBaseLine line "ceiling_log_base"
  let e ← expect "e" (parseInt res)
  let f := AzRat.floorLogBaseAbs b x
  let computed := if AzRat.cmpPowAbs b f x == .eq then f else f + 1
  expectEq "ceiling_log_base" computed e

/-- `checked_log_base(x, b) = Some(e)` or `None`: the floor when `b^e = |x|` exactly. -/
def checkRatCheckedLogBase (line : String) : Verdict := do
  let (x, b, res) ← logBaseLine line "checked_log_base"
  let res ← expect "result" (parseOption res)
  let res ← match res with
    | some e => expect "e" ((parseInt e).map some)
    | none => pure none
  let f := AzRat.floorLogBaseAbs b x
  let computed : Option Int := if AzRat.cmpPowAbs b f x == .eq then some f else none
  expectEq "checked_log_base" (optionString computed) (optionString res)

/-! ### Comparison -/

def checkRatCmp (line : String) : Verdict := do
  let (x, y, o) ← comparisonLine line
  let x ← expect "x" (parseAzRat x)
  let y ← expect "y" (parseAzRat y)
  expectEq "cmp" (orderingName (AzRat.cmp x y)) (orderingName o)

/-- A rational compared with a natural or an integer, which both read as integers. -/
def checkRatCmpInteger (line : String) : Verdict := do
  let (x, y, o) ← comparisonLine line
  let x ← expect "x" (parseAzRat x)
  let y ← expect "y" (parseAzInt y)
  expectEq "partial_cmp" (orderingName (AzRat.cmp x y.toAzRat)) (orderingName o)

/-- A rational compared with an unsigned machine integer. -/
def checkRatCmpUnsigned (line : String) : Verdict := do
  let (x, u, o) ← comparisonLine line
  let x ← expect "x" (parseAzRat x)
  let u ← parseUInt64 u
  expectEq "partial_cmp" (orderingName (AzRat.cmp x u.toAzRat)) (orderingName o)

/-- A rational compared with a signed machine integer. -/
def checkRatCmpSigned (line : String) : Verdict := do
  let (x, i, o) ← comparisonLine line
  let x ← expect "x" (parseAzRat x)
  let i ← parseInt64 i
  expectEq "partial_cmp" (orderingName (AzRat.cmp x i.toAzRat)) (orderingName o)

def checkRatEq (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseAzRat x)
  let y ← expect "y" (parseAzRat y)
  expectEq "eq" (x == y) e

/-- A rational against a natural or an integer. -/
def checkRatEqInteger (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseAzRat x)
  let y ← expect "y" (parseAzInt y)
  expectEq "partial_eq" (x == y.toAzRat) e

/-- `x is negative`, `x is zero`, or `x is positive`. -/
def checkRatSign (line : String) : Verdict := do
  let (x, expected) ←
    if line.endsWith " is negative" then pure (dropRightChars line 12, Ordering.lt)
    else if line.endsWith " is zero" then pure (dropRightChars line 8, Ordering.eq)
    else if line.endsWith " is positive" then pure (dropRightChars line 12, Ordering.gt)
    else fail "not a sign line"
  let x ← expect "x" (parseAzRat x)
  expectEq "sign" (orderingName (AzRat.signOrd x)) (orderingName expected)

/-! ### Construction and conversion -/

/-- `Rational::from_naturals(n, d) = q`; Malachite panics on a zero denominator. -/
def checkRatFromNaturals (line : String) : Verdict := do
  let (args, res) ← expect "a `Rational::from_naturals(n, d) = q` line"
    (functionCall line "Rational::from_naturals"
      <|> functionCall line "Rational::from_naturals_ref")
  let (n, d) ← match args with
    | [n, d] => pure (n, d)
    | _ => fail "from_naturals takes two arguments"
  let n ← expect "n" (parseAzNat n)
  let d ← expect "d" (parseAzNat d)
  let q ← expect "q" (parseAzRat res)
  expectEq "from_naturals" (AzRat.ofAzNats n d) q

/-- `Rational::from_integers(n, d) = q`. -/
def checkRatFromIntegers (line : String) : Verdict := do
  let (args, res) ← expect "a `Rational::from_integers(n, d) = q` line"
    (functionCall line "Rational::from_integers"
      <|> functionCall line "Rational::from_integers_ref")
  let (n, d) ← match args with
    | [n, d] => pure (n, d)
    | _ => fail "from_integers takes two arguments"
  let n ← expect "n" (parseAzInt n)
  let d ← expect "d" (parseAzInt d)
  let q ← expect "q" (parseAzRat res)
  expectEq "from_integers" (AzRat.ofAzInts n d) q

/-- `Rational::from_sign_and_naturals(s, n, d) = q`. -/
def checkRatFromSignAndNaturals (line : String) : Verdict := do
  let (args, res) ← expect "a `Rational::from_sign_and_naturals(s, n, d) = q` line"
    (functionCall line "Rational::from_sign_and_naturals"
      <|> functionCall line "Rational::from_sign_and_naturals_ref")
  let (s, n, d) ← match args with
    | [s, n, d] => pure (s, n, d)
    | _ => fail "from_sign_and_naturals takes three arguments"
  let s ← expect "sign" (parseBool s)
  let n ← expect "n" (parseAzNat n)
  let d ← expect "d" (parseAzNat d)
  let q ← expect "q" (parseAzRat res)
  expectEq "from_sign_and_naturals" (AzRat.ofSignAzNats s n d) q

/-- `Rational::from(z) = q` for a natural, an integer, or a machine integer, all of which print
as integers; also `Rational::from(&z)`. -/
def checkRatFromInteger (line : String) : Verdict := do
  let (args, res) ← expect "a `Rational::from(z) = q` line" (functionCall line "Rational::from")
  let z ← match args with
    | [z] => pure z
    | _ => fail "Rational::from takes one argument"
  let z ← expect "z" (parseAzInt z)
  let q ← expect "q" (parseAzRat res)
  expectEq "from" z.toAzRat q

/-! ### Strings -/

/-- A bare `q`, as the `to_string` demo prints it: the canonical rendering, which `parseAzRat`
accepts and `toString` reproduces. -/
def checkRatToString (line : String) : Verdict := do
  let q ← expect "a rational" (parseAzRat line)
  expectEq "to_string" (toString q) (trim line)

/-- Malachite's `Rational::from_str`: an optional single `+` or `-`, digits, and optionally `/`,
an optional single `+`, and a nonzero denominator; the fraction need not be reduced. -/
def malachiteParseRational (s : String) : Option AzRat := do
  let (n, d) ← match s.splitOn "/" with
    | [n] => some (n, "1")
    | [n, d] => some (n, d)
    | _ => none
  let n ← malachiteParseInteger 10 n
  let d ← malachiteParseBase 10 d
  guard (d != (0 : AzNat))
  pure (AzRat.ofSignAzNats n.sign n.abs d)

/-- The result of a parsing demo: `Some(q)`/`None`, `Ok(q)`/`Err(())`, or a bare `q` from the
`_targeted` demos. -/
def parsedRational (rhs : String) : Except Failure (Option AzRat) := do
  let res ← match parseOption rhs, parseResult rhs with
    | some r, _ => pure r
    | _, some r => pure r
    | none, none => pure (some rhs)
  match res with
  | some q => expect "q" ((parseAzRat q).map some)
  | none => pure none

/-- `Rational::from_str(s) = Ok(q)` or `Err(())`. The string is printed bare. -/
def checkRatFromStr (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `Rational::from_str(s) = r` line" (splitEquals line)
  let prefix_ := "Rational::from_str("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a from_str call"
  let s := dropRightChars (dropChars lhs prefix_.length) 1
  let res ← parsedRational rhs
  expectEq "from_str" (resultString (malachiteParseRational s)) (resultString res)

/-- `Rational::from_sci_string(s) = r` or `Rational::from_sci_string(s, b) = r`, the string
printed bare (so the base, when present, is everything after the last comma). -/
def checkRatFromSciString (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `Rational::from_sci_string(s[, b]) = r` line" (splitEquals line)
  let prefix_ := "Rational::from_sci_string("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a from_sci_string call"
  let inner := dropRightChars (dropChars lhs prefix_.length) 1
  let (s, b) ← match (inner.splitOn ", ").reverse with
    | [s] => pure (s, (10 : UInt64))
    | b :: rest@(_ :: _) =>
      match parseNat b with
      | some b => if b < 2 || b > 36 then fail "the base is outside [2, 36]"
                  else pure (", ".intercalate rest.reverse, UInt64.ofNat b)
      | none => pure (inner, 10)
    | [] => fail "from_sci_string takes one or two arguments"
  let res ← parsedRational rhs
  expectEq "from_sci_string" (optionString (AzRat.fromSci s b)) (optionString res)

/-- Malachite's `ToSciOptions`, as `Debug` prints it:
`ToSciOptions { base: 10, rounding_mode: Nearest, size_options: Precision(16),
neg_exp_threshold: -6, lowercase: true, e_lowercase: true, force_exponent_plus_sign: false,
include_trailing_zeros: false }`. The rounding mode is returned separately, since `Exact` has
no `RoundingMode` counterpart in Azurite. -/
def parseToSciOptions (s : String) : Except Failure (SciOptions × Rounding) := do
  let s := trim s
  let prefix_ := "ToSciOptions { "
  if !(s.startsWith prefix_ && s.endsWith " }") then fail "not a ToSciOptions value"
  let fields := (splitTopLevel (dropRightChars (dropChars s prefix_.length) 2) ',').map fun f =>
    match (trim f).splitOn ": " with
    | [k, v] => (k, trim v)
    | _ => (trim f, "")
  let field (k : String) : Except Failure String :=
    match fields.lookup k with
    | some v => pure v
    | none => fail s!"ToSciOptions has no field {k}"
  let base ← field "base" >>= fun v => expect "base" (parseNat v)
  let rm ← field "rounding_mode" >>= fun v => expect "rounding mode" (parseRounding v)
  let size ← field "size_options" >>= fun v =>
    if v == "Complete" then pure SciSizeOptions.complete
    else if v.startsWith "Precision(" && v.endsWith ")" then
      (expect "precision" (parseNat (dropRightChars (dropChars v 10) 1))).map .precision
    else if v.startsWith "Scale(" && v.endsWith ")" then
      (expect "scale" (parseNat (dropRightChars (dropChars v 6) 1))).map .scale
    else fail s!"unknown size option {v}"
  let threshold ← field "neg_exp_threshold" >>= fun v => expect "threshold" (parseInt v)
  let flag (k : String) : Except Failure Bool := field k >>= fun v => expect k (parseBool v)
  let lowercase ← flag "lowercase"
  let eLowercase ← flag "e_lowercase"
  let plus ← flag "force_exponent_plus_sign"
  let zeros ← flag "include_trailing_zeros"
  let mode := match rm with
    | .mode m => m
    | .exact => .Nearest
  pure ({ base := UInt64.ofNat base, mode, size,
          format := { negExpThreshold := threshold, lowercase, eLowercase,
                      forceExponentPlusSign := plus, includeTrailingZeros := zeros } }, rm)

/-- `q.to_sci() = s`: the default options. -/
def checkRatToSci (line : String) : Verdict := do
  let (q, args, res) ← expect "a `q.to_sci() = s` line" (methodCall line "to_sci")
  if !args.isEmpty then fail "to_sci takes no arguments"
  let q ← expect "q" (parseAzRat q)
  expectEq "to_sci" (AzRat.toSciString q) res

/-- `to_sci_with_options(q, ToSciOptions { … }) = s`. Under `Exact`, Malachite only prints a line
when no rounding is needed, which is `toSciExact`; the digits are then those of any mode. -/
def checkRatToSciWithOptions (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `to_sci_with_options(q, options) = s` line" (splitEquals line)
  let prefix_ := "to_sci_with_options("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a to_sci_with_options call"
  let inner := dropRightChars (dropChars lhs prefix_.length) 1
  let (q, options) ← match inner.splitOn ", ToSciOptions { " with
    | [q, rest] => pure (q, "ToSciOptions { " ++ rest)
    | _ => fail "to_sci_with_options takes a rational and options"
  let q ← expect "q" (parseAzRat q)
  let (o, rm) ← parseToSciOptions options
  if rm matches .exact then
    if !AzRat.toSciExact q o then disagree "Malachite printed an Exact conversion that rounds"
  match AzRat.toSci q o with
  | some s => expectEq "to_sci_with_options" s rhs
  | none => disagree "Azurite cannot meet the request these options make"

/-- `q can be converted to sci using ToSciOptions { … }`, or `cannot be`: whether `toSci` has a
result, and under `Exact` whether that result is exact. -/
def checkRatFmtSciValid (line : String) : Verdict := do
  let (q, options, expected) ←
    match line.splitOn " cannot be converted to sci using ",
        line.splitOn " can be converted to sci using " with
    | [q, o], _ => pure (q, o, false)
    | _, [q, o] => pure (q, o, true)
    | _, _ => fail "not a fmt_sci_valid line"
  let q ← expect "q" (parseAzRat q)
  let (o, rm) ← parseToSciOptions options
  let valid := match rm with
    | .exact => AzRat.toSciExact q o
    | .mode _ => (AzRat.toSciNumber q o).isSome
  expectEq "fmt_sci_valid" valid expected

/-- `length_after_point_in_small_base(q, b) = Some(n)` or `None`. -/
def checkRatLengthAfterPoint (line : String) : Verdict := do
  let (args, res) ← expect "a `length_after_point_in_small_base(q, b) = r` line"
    (functionCall line "length_after_point_in_small_base")
  let (q, b) ← match args with
    | [q, b] => pure (q, b)
    | _ => fail "length_after_point_in_small_base takes two arguments"
  let q ← expect "q" (parseAzRat q)
  let b ← parseUInt64 b
  let res ← expect "result" (parseOption res)
  let res ← match res with
    | some n => expect "n" ((parseNat n).map some)
    | none => pure none
  expectEq "length_after_point_in_small_base" (optionString (AzRat.lengthAfterPoint b q))
    (optionString res)

end Azurite.Oracle
