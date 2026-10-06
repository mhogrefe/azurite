/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzRat
import Azurite.Oracle.MalachiteFloat
import Azurite.AzFloat.Add
import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Div
import Azurite.AzFloat.DivRat
import Azurite.AzFloat.Mul
import Azurite.AzFloat.MulRat
import Azurite.AzFloat.Rsqrt
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Compare
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Shift

/-!
# Checks for Malachite's `Float` against `AzFloat`

One check per line shape that a `Float` demo prints in its `_debug` form, where every value is
written in Malachite's exact hexadecimal format with its precision (`0x1.8#2`), which Azurite
reads with `AzFloat.ofHexString`. Each check recomputes the operation with `AzFloat`, whose
exponent is unbounded, and passes the result through `clamp` (`Azurite.Oracle.MalachiteFloat`),
which applies Malachite's exponent range; the result is then compared structurally, so the
precision must agree as well as the value. Malachite's `-0.0` has no Azurite counterpart: the
sign of a zero is read from the line where a check needs it and ignored when comparing results.
Malachite's `Exact` rounding mode is checked as "the rounding in any mode is exact". The
correspondence is documented on Malachite's "Malachite for Azurite Users: Floats" page.
-/

namespace Azurite.Oracle

open Azurite

/-! ### Reading and comparing floats -/

/-- A float as Malachite prints it, with whether it was a negative zero (which reads as `zero`). -/
def parseFloat (s : String) : Option (AzFloat × Bool) :=
  let s := trim s
  if s == "-0x0.0" then some (.zero, true) else (AzFloat.ofHexString s).map (·, false)

/-- The hexadecimal rendering, with the sign of a zero restored. -/
def floatString (x : AzFloat) (negativeZero : Bool) : String :=
  if negativeZero && x matches .zero then "-0x0.0" else AzFloat.toHexString x

/-- The verdict for a computed float against a printed one; zeros agree regardless of sign. -/
def expectFloat (what : String) (computed : AzFloat) (printed : AzFloat × Bool) : Verdict :=
  if computed == printed.1 then .ok ()
  else disagree s!"{what}: Azurite computed {AzFloat.toHexString computed}, Malachite printed \
    {floatString printed.1 printed.2}"

/-- The verdict for a computed `(float, ordering)` pair against a printed one. -/
def expectFloatPair (what : String) (computed : AzFloat × Ordering)
    (printed : (AzFloat × Bool) × Ordering) : Verdict :=
  if computed.1 == printed.1.1 && computed.2 == printed.2 then .ok ()
  else disagree s!"{what}: Azurite computed ({AzFloat.toHexString computed.1}, \
    {orderingName computed.2}), Malachite printed ({floatString printed.1.1 printed.1.2}, \
    {orderingName printed.2})"

/-- A printed `(float, ordering)` pair. -/
def parseFloatPair (s : String) : Except Failure ((AzFloat × Bool) × Ordering) := do
  let (z, o) ← expect "(float, ordering)" (parseTuple2 s)
  let z ← expect "float" (parseFloat z)
  let o ← expect "ordering" (parseOrdering o)
  pure (z, o)

/-- A hexadecimal natural as Malachite's `{:#x}` prints it, `0x7b`. -/
def parseHexNatural (s : String) : Option AzNat :=
  let s := trim s
  if s.startsWith "0x" then malachiteParseBase 16 (dropChars s 2) else none

/-- A hexadecimal integer as Malachite's `{:#x}` prints it, `-0x7b`. -/
def parseHexInteger (s : String) : Option AzInt :=
  let s := trim s
  if s.startsWith "-" then (parseHexNatural (dropChars s 1)).map fun n => AzInt.neg n.toAzInt
  else (parseHexNatural s).map AzNat.toAzInt

/-- The precision Malachite's `+`, `-`, `*`, `/`, and `_round` methods use: the larger of the
operands' precisions. -/
def combined (x y : AzFloat) : Nat := AzFloat.combinedPrecision x y

/-- Rounds with Azurite in the given `Rounding`, then applies Malachite's exponent range. Under
`Exact`, Malachite only prints a line when no rounding is needed, so the result of any mode must
be exact. -/
def roundedResult (what : String) (f : RoundingMode → AzFloat × Ordering) (rm : Rounding) :
    Except Failure (AzFloat × Ordering) :=
  match rm with
  | .mode m => let (r, o) := f m; pure (clamp r o m)
  | .exact =>
    let (r, o) := f .Nearest
    if o != .eq then disagree s!"{what}: Malachite printed an Exact result that rounds"
    else pure (clamp r o .Nearest)

/-! ### Arithmetic -/

/-- A binary operation's line in one of its four shapes: `x op y = z`, `(x).name_prec(y, p) =
(z, o)`, `(x).name_round(y, rm) = (z, o)`, or `(x).name_prec_round(y, p, rm) = (z, o)`. -/
def checkFloatBinary (op name : String)
    (f : AzFloat × Bool → AzFloat × Bool → Nat → RoundingMode → AzFloat × Ordering)
    (line : String) : Verdict := do
  match methodCall line s!"{name}_prec_round", methodCall line s!"{name}_round",
      methodCall line s!"{name}_prec" with
  | some (x, [y, p, rm], res), _, _ =>
    let x ← expect "x" (parseFloat x)
    let y ← expect "y" (parseFloat y)
    let p ← expect "precision" (parseNat p)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f x y p) rm
    expectFloatPair s!"{name}_prec_round" computed printed
  | _, some (x, [y, rm], res), _ =>
    let x ← expect "x" (parseFloat x)
    let y ← expect "y" (parseFloat y)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f x y (combined x.1 y.1)) rm
    expectFloatPair s!"{name}_round" computed printed
  | _, _, some (x, [y, p], res) =>
    let x ← expect "x" (parseFloat x)
    let y ← expect "y" (parseFloat y)
    let p ← expect "precision" (parseNat p)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f x y p) (.mode .Nearest)
    expectFloatPair s!"{name}_prec" computed printed
  | _, _, _ =>
    let (x, y, z) ← expect s!"an `x {op} y = z` line" (binaryOp line op)
    let x ← expect "x" (parseFloat x)
    let y ← expect "y" (parseFloat y)
    let z ← expect "z" (parseFloat z)
    let computed ← roundedResult name (f x y (combined x.1 y.1)) (.mode .Nearest)
    expectFloat s!"x {op} y" computed.1 z

/-- An operation on the values alone, the signs of zero operands not mattering to a nonzero
result. -/
def onValues (f : AzFloat → AzFloat → Nat → RoundingMode → AzFloat × Ordering)
    (x y : AzFloat × Bool) : Nat → RoundingMode → AzFloat × Ordering := f x.1 y.1

def checkFloatAdd : String → Verdict := checkFloatBinary "+" "add" (onValues AzFloat.addPrecRound)

def checkFloatSub : String → Verdict := checkFloatBinary "-" "sub" (onValues AzFloat.subPrecRound)

def checkFloatMul : String → Verdict := checkFloatBinary "*" "mul" (onValues AzFloat.mulPrecRound)

/-- Division by a zero gives `±∞` with the sign of the dividend times the sign of the zero, so a
`-0.0` divisor, which Azurite reads as `zero`, negates Azurite's result. -/
def checkFloatDiv : String → Verdict := checkFloatBinary "/" "div" fun x y p m =>
  let (r, o) := AzFloat.divPrecRound x.1 y.1 p m
  (if y.2 then AzFloat.neg r else r, o)

/-- One mixed operation's line already taken apart: the float `x`, the rational `q`, the
precision (`x`'s, `AzFloat.ratOpPrecision`, when absent), the rounding mode (`Nearest` when
absent), and the printed `(z, o)`. -/
def checkFloatRationalShape (what name : String)
    (f : AzFloat × Bool → AzRat → Nat → RoundingMode → AzFloat × Ordering)
    (x q : String) (p rm : Option String) (res : String) : Verdict := do
  let x ← expect "x" (parseFloat x)
  let q ← expect "q" (parseAzRat q)
  let p ← match p with
    | some p => expect "precision" (parseNat p)
    | none => pure (AzFloat.ratOpPrecision x.1)
  let rm ← match rm with
    | some rm => expect "rounding mode" (parseRounding rm)
    | none => pure (.mode .Nearest)
  let printed ← parseFloatPair res
  let computed ← roundedResult name (f x q p) rm
  expectFloatPair what computed printed

/-- A mixed operation's line, with a float `x` and a rational `q`, in one of its shapes:
`x op q = z`, `q op x = z`, `(x).name_prec(q, p) = (z, o)`, `(x).name_round(q, rm) = (z, o)`,
or `(x).name_prec_round(q, p, rm) = (z, o)`; and, when `flipped` names the functions computing
`q op x`, `flipped_prec(q, x, p) = (z, o)` and its `_round` and `_prec_round` siblings. The plain
and `_round` shapes use the precision of `x` (`AzFloat.ratOpPrecision`). `f` computes `x op q`
and `g` computes `q op x`; each receives `x` with its negative-zero flag. -/
def checkFloatRationalBinary (op name : String)
    (f : AzFloat × Bool → AzRat → Nat → RoundingMode → AzFloat × Ordering)
    (g : AzRat → AzFloat × Bool → Nat → RoundingMode → AzFloat × Ordering)
    (flipped : Option String) (line : String) : Verdict := do
  let g' := fun x q => g q x
  let call (suffix : String) : Option (List String × String) := do
    let n ← flipped
    functionCall line s!"{n}_{suffix}"
  match methodCall line s!"{name}_prec_round", methodCall line s!"{name}_round",
      methodCall line s!"{name}_prec" with
  | some (x, [q, p, rm], res), _, _ =>
    checkFloatRationalShape s!"{name}_prec_round" name f x q (some p) (some rm) res
  | _, some (x, [q, rm], res), _ =>
    checkFloatRationalShape s!"{name}_round" name f x q none (some rm) res
  | _, _, some (x, [q, p], res) =>
    checkFloatRationalShape s!"{name}_prec" name f x q (some p) none res
  | _, _, _ =>
  match call "prec_round", call "round", call "prec" with
  | some ([q, x, p, rm], res), _, _ =>
    checkFloatRationalShape s!"q {op} x prec_round" name g' x q (some p) (some rm) res
  | _, some ([q, x, rm], res), _ =>
    checkFloatRationalShape s!"q {op} x round" name g' x q none (some rm) res
  | _, _, some ([q, x, p], res) =>
    checkFloatRationalShape s!"q {op} x prec" name g' x q (some p) none res
  | _, _, _ =>
    let (a, b, z) ← expect s!"an `x {op} q` or `q {op} x` line" (binaryOp line op)
    let z ← expect "z" (parseFloat z)
    match parseFloat a, parseAzRat b, parseAzRat a, parseFloat b with
    | some x, some q, _, _ =>
      let computed ← roundedResult name (f x q (AzFloat.ratOpPrecision x.1)) (.mode .Nearest)
      expectFloat s!"x {op} q" computed.1 z
    | _, _, some q, some x =>
      let computed ← roundedResult name (g q x (AzFloat.ratOpPrecision x.1)) (.mode .Nearest)
      expectFloat s!"q {op} x" computed.1 z
    | _, _, _, _ => fail s!"could not parse a float and a rational around `{op}`"

def checkFloatAddRational : String → Verdict :=
  checkFloatRationalBinary "+" "add_rational" (fun x => AzFloat.addRatPrecRound x.1)
    (fun q x => AzFloat.addRatPrecRound x.1 q) none

def checkFloatSubRational : String → Verdict :=
  checkFloatRationalBinary "-" "sub_rational" (fun x => AzFloat.subRatPrecRound x.1)
    (fun q x => AzFloat.ratSubPrecRound q x.1) none

def checkFloatMulRational : String → Verdict :=
  checkFloatRationalBinary "*" "mul_rational" (fun x => AzFloat.mulRatPrecRound x.1)
    (fun q x => AzFloat.mulRatPrecRound x.1 q) none

/-- `x / q` and `q / x`. Malachite's `q / -0.0` is `∓∞`, with the sign of the zero, which
Azurite, reading the zero as unsigned, gives as `±∞`; so the result is negated when `x` is
`-0.0`, as for `checkFloatDiv`. -/
def checkFloatDivRational : String → Verdict :=
  checkFloatRationalBinary "/" "div_rational" (fun x => AzFloat.divRatPrecRound x.1)
    (fun q x p m =>
      let (r, o) := AzFloat.ratDivPrecRound q x.1 p m
      (if x.2 then AzFloat.neg r else r, o))
    (some "rational_div_float")

/-- A unary operation's line in one of its four shapes: the plain one (`(x) ^ 2 = z` or
`(x).sqrt() = z`), `(x).name_prec(p) = (z, o)`, `(x).name_round(rm) = (z, o)`, or
`(x).name_prec_round(p, rm) = (z, o)`. The plain shape rounds to nearest at `x`'s precision. -/
def checkFloatUnary (name : String) (plain : String → Option (String × String))
    (f : AzFloat → Nat → RoundingMode → AzFloat × Ordering) (line : String) : Verdict := do
  match methodCall line s!"{name}_prec_round", methodCall line s!"{name}_round",
      methodCall line s!"{name}_prec" with
  | some (x, [p, rm], res), _, _ =>
    let x ← expect "x" (parseFloat x)
    let p ← expect "precision" (parseNat p)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f x.1 p) rm
    expectFloatPair s!"{name}_prec_round" computed printed
  | _, some (x, [rm], res), _ =>
    let x ← expect "x" (parseFloat x)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f x.1 (x.1.precision?.getD 1)) rm
    expectFloatPair s!"{name}_round" computed printed
  | _, _, some (x, [p], res) =>
    let x ← expect "x" (parseFloat x)
    let p ← expect "precision" (parseNat p)
    let printed ← parseFloatPair res
    let computed ← roundedResult name (f x.1 p) (.mode .Nearest)
    expectFloatPair s!"{name}_prec" computed printed
  | _, _, _ =>
    let (x, z) ← expect s!"a `{name}` line" (plain line)
    let x ← expect "x" (parseFloat x)
    let z ← expect "z" (parseFloat z)
    let computed ← roundedResult name (f x.1 (x.1.precision?.getD 1)) (.mode .Nearest)
    expectFloat name computed.1 z

/-- `(x) ^ 2 = z`. -/
def squareLine (line : String) : Option (String × String) := do
  let (x, two, z) ← binaryOp line "^"
  guard (two == "2")
  pure (x, z)

/-- `(x).sqrt() = z`. -/
def sqrtLine (line : String) : Option (String × String) := do
  let (x, args, z) ← methodCall line "sqrt"
  guard args.isEmpty
  pure (x, z)

def checkFloatSquare : String → Verdict :=
  checkFloatUnary "square" squareLine AzFloat.sqrPrecRound

def checkFloatSqrt : String → Verdict := checkFloatUnary "sqrt" sqrtLine AzFloat.sqrtPrecRound

/-- `(x).reciprocal_sqrt() = z`. -/
def reciprocalSqrtLine (line : String) : Option (String × String) := do
  let (x, args, z) ← methodCall line "reciprocal_sqrt"
  guard args.isEmpty
  pure (x, z)

/-- `1/√x`. A `-0.0` input, which Azurite reads as `zero`, gives `+∞` in both libraries, so no
sign adjustment is needed. -/
def checkFloatReciprocalSqrt : String → Verdict :=
  checkFloatUnary "reciprocal_sqrt" reciprocalSqrtLine AzFloat.rsqrtPrecRound

/-- `-(x) = z`. -/
def checkFloatNeg (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `-(x) = z` line" (splitEquals line)
  if !lhs.startsWith "-" then fail "not a negation"
  let x ← expect "x" (parseFloat (stripRef (dropChars lhs 1)))
  let z ← expect "z" (parseFloat rhs)
  expectFloat "neg" (AzFloat.neg x.1) z

/-- `|x| = z`. -/
def checkFloatAbs (line : String) : Verdict := do
  let (lhs, rhs) ← expect "an `|x| = z` line" (splitEquals line)
  if !(lhs.startsWith "|" && lhs.endsWith "|") then fail "not an `|x|` left-hand side"
  let x ← expect "x" (parseFloat (dropRightChars (dropChars lhs 1) 1))
  let z ← expect "z" (parseFloat rhs)
  expectFloat "abs" (AzFloat.abs x.1) z

/-- `x << s = z` or `x >> s = z`: an exact shift of the exponent, then Malachite's range, whose
rule for shifts is the `Nearest` one. -/
def checkFloatShift (op : String) (left : Bool) (line : String) : Verdict := do
  let (x, s, z) ← expect s!"an `x {op} s = z` line" (binaryOp line op)
  let x ← expect "x" (parseFloat x)
  let s ← expect "shift" (parseInt s)
  let z ← expect "z" (parseFloat z)
  let k := AzInt.ofInt (if left then s else -s)
  expectFloat op (clampExact (AzFloat.shiftLeft x.1 k) .Nearest) z

def checkFloatShl : String → Verdict := checkFloatShift "<<" true

def checkFloatShr : String → Verdict := checkFloatShift ">>" false

/-- `Float::power_of_2_prec_round(e, p, rm) = (z, o)`, `Float::power_of_2_prec(e, p) = (z, o)`,
or `Float::power_of_2(e) = z` (precision 1, `Nearest`): `2^e`, exact, then Malachite's range. -/
def checkFloatPowerOf2 (line : String) : Verdict := do
  match functionCall line "Float::power_of_2_prec_round",
      functionCall line "Float::power_of_2_prec", functionCall line "Float::power_of_2" with
  | some ([e, p, rm], res), _, _ =>
    let e ← expect "exponent" (parseInt e)
    let p ← expect "precision" (parseNat p)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult "power_of_2_prec_round"
      (fun m => AzFloat.setPrecRound (AzFloat.powerOf2 (AzInt.ofInt e)) p m) rm
    expectFloatPair "power_of_2_prec_round" computed printed
  | _, some ([e, p], res), _ =>
    let e ← expect "exponent" (parseInt e)
    let p ← expect "precision" (parseNat p)
    let printed ← parseFloatPair res
    let computed := clamp (AzFloat.setPrec (AzFloat.powerOf2 (AzInt.ofInt e)) p) .eq .Nearest
    expectFloatPair "power_of_2_prec" computed printed
  | _, _, some ([e], res) =>
    let e ← expect "exponent" (parseInt e)
    let z ← expect "z" (parseFloat res)
    expectFloat "power_of_2" (clampExact (AzFloat.powerOf2 (AzInt.ofInt e)) .Nearest) z
  | _, _, _ => fail "not a power_of_2 line"

/-- `x := X; x.set_prec_round(p, rm) = o; x = Z` or `x := X; x.set_prec(p) = o; x = Z`. The
precision change can overflow (a carry at the maximum exponent) but never underflows. -/
def checkFloatSetPrec (line : String) : Verdict := do
  let (x, call, z) ← match line.splitOn "; " with
    | [x, call, z] => pure (x, call, z)
    | _ => fail "not an `x := X; x.set_prec…; x = Z` line"
  if !x.startsWith "x := " then fail "not an `x := X` prefix"
  let x ← expect "x" (parseFloat (dropChars x 5))
  if !z.startsWith "x = " then fail "not an `x = Z` suffix"
  let z ← expect "z" (parseFloat (dropChars z 4))
  let (p, rm, o) ← match methodCall call "set_prec_round", methodCall call "set_prec" with
    | some (_, [p, rm], o), _ => pure (p, rm, o)
    | _, some (_, [p], o) => pure (p, "Nearest", o)
    | _, _ => fail "not a set_prec call"
  let p ← expect "precision" (parseNat p)
  let rm ← expect "rounding mode" (parseRounding rm)
  let o ← expect "ordering" (parseOrdering o)
  let computed ← roundedResult "set_prec_round" (AzFloat.setPrecRound x.1 p) rm
  expectFloatPair "set_prec_round" computed (z, o)

/-! ### Classification, sign, and accessors -/

/-- A predicate printed as `x<pos>` or `x<neg>`, on the float and its zero sign. -/
def checkFloatPredicate (pos neg : String) (f : AzFloat → Bool → Bool) (line : String) :
    Verdict := do
  let (x, expected) ←
    if line.endsWith neg then pure (dropRightChars line neg.length, false)
    else if line.endsWith pos then pure (dropRightChars line pos.length, true)
    else fail s!"not an `x{pos}` or `x{neg}` line"
  let x ← expect "x" (parseFloat x)
  expectEq (trim pos) (f x.1 x.2) expected

def checkFloatIsNaN : String → Verdict :=
  checkFloatPredicate " is NaN" " is not NaN" fun x _ => x.isNaN

def checkFloatIsFinite : String → Verdict :=
  checkFloatPredicate " is finite" " is not finite" fun x _ => x.isFinite

def checkFloatIsInfinite : String → Verdict :=
  checkFloatPredicate " is infinite" " is not infinite" fun x _ => x.isInfinite

def checkFloatIsZero : String → Verdict :=
  checkFloatPredicate " is zero" " is not zero" fun x _ => x.isZero

def checkFloatIsNormal : String → Verdict :=
  checkFloatPredicate " is normal" " is not normal" fun x _ => x.isNormal

/-- Malachite's `is_power_of_2`: a positive finite power of two. -/
def checkFloatIsPowerOf2 : String → Verdict :=
  checkFloatPredicate " is a power of 2" " is not a power of 2" fun x _ =>
    match x with
    | .finite s _ p m _ => s && (AzFloat.coreSignificand p m).isPowerOfTwo
    | _ => false

/-- `x is negative`, `x is zero`, or `x is positive`: Malachite's `sign` is the sign bit, so a
zero is positive or negative by its sign and never "zero". -/
def checkFloatSign (line : String) : Verdict := do
  let (x, expected) ←
    if line.endsWith " is negative" then pure (dropRightChars line 12, Ordering.lt)
    else if line.endsWith " is zero" then pure (dropRightChars line 8, Ordering.eq)
    else if line.endsWith " is positive" then pure (dropRightChars line 12, Ordering.gt)
    else fail "not a sign line"
  let (x, negativeZero) ← expect "x" (parseFloat x)
  let computed ← match x with
    | .zero => pure (if negativeZero then Ordering.lt else .gt)
    | .nan => fail "NaN has no sign"
    | x => pure (if x.isPositive then Ordering.gt else .lt)
  expectEq "sign" (orderingName computed) (orderingName expected)

/-- `name(x) = r` with a float argument. -/
def unaryFloatLine (line name : String) : Except Failure (AzFloat × Bool × String) := do
  let (args, res) ← expect s!"a `{name}(x) = r` line" (functionCall line name)
  let x ← match args with
    | [x] => pure x
    | _ => fail s!"{name} takes one argument"
  let (x, negativeZero) ← expect "x" (parseFloat x)
  pure (x, negativeZero, res)

/-- `get_exponent(x) = Some(e)` or `None`. -/
def checkFloatGetExponent (line : String) : Verdict := do
  let (x, _, res) ← unaryFloatLine line "get_exponent"
  let printed ← expect "exponent" (parseOption res)
  let printed ← match printed with
    | some e => expect "exponent" ((parseInt e).map some)
    | none => pure none
  expectEq "get_exponent" (optionString (x.exponent?.map AzInt.toString))
    (optionString (printed.map toString))

/-- `get_prec(x) = Some(p)` or `None`. -/
def checkFloatGetPrec (line : String) : Verdict := do
  let (x, _, res) ← unaryFloatLine line "get_prec"
  let printed ← expect "precision" (parseOption res)
  let printed ← match printed with
    | some p => expect "precision" ((parseNat p).map some)
    | none => pure none
  expectEq "get_prec" (optionString x.precision?) (optionString printed)

/-- `to_significand(x) = Some(n)` or `None`: both libraries left-align the significand at a
64-bit limb boundary, so the naturals agree. -/
def checkFloatToSignificand (line : String) : Verdict := do
  let (x, _, res) ← unaryFloatLine line "to_significand"
  let printed ← expect "significand" (parseOption res)
  let printed ← match printed with
    | some n => expect "significand" ((parseAzNat n).map some)
    | none => pure none
  expectEq "to_significand" (optionString x.significand?) (optionString printed)

/-- `ulp(x) = Z` or `None`: `2^(exponent - precision)` at precision 1, `None` for the special
values and when that power of two is below Malachite's range. -/
def checkFloatUlp (line : String) : Verdict := do
  let (x, _, res) ← unaryFloatLine line "ulp"
  let computed : Option AzFloat := x.ulp?.bind fun u =>
    if u.exponent?.any (· < minExponent) then none else some u
  if trim res == "None" then
    if let some u := computed then
      disagree s!"ulp: Azurite computed {AzFloat.toHexString u}, Malachite printed None"
    else pure ()
  else
    let z ← expect "ulp" (parseFloat res)
    match computed with
    | some u => expectFloat "ulp" u z
    | none => disagree s!"ulp: Azurite has none, Malachite printed {floatString z.1 z.2}"

/-- `min_positive_value_prec(p) = Z`, `max_finite_value_with_prec(p) = Z`, `one_prec(p) = Z`, or
`two_prec(p) = Z`: Malachite's constants of a given precision. -/
def checkFloatConstant (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `name(p) = Z` line" (splitEquals line)
  let names := [("min_positive_value_prec", minPositive true),
    ("max_finite_value_with_prec", maxFinite true),
    ("one_prec", fun p => AzFloat.setPrec AzFloat.one p),
    ("two_prec", fun p => AzFloat.setPrec AzFloat.two p)]
  let (name, f) ← match names.find? fun (n, _) => lhs.startsWith s!"{n}(" with
    | some nf => pure nf
    | none => fail "not a constant line"
  let (args, _) ← expect s!"a `{name}(p) = Z` line" (functionCall line name)
  let p ← match args with
    | [p] => expect "precision" (parseNat p)
    | _ => fail s!"{name} takes one argument"
  if p == 0 then fail "the precision is zero"
  let z ← expect "Z" (parseFloat rhs)
  expectFloat name (f p) z

/-! ### Comparison -/

/-- The `x < y`, `x = y`, `x > y`, and `x and y are incomparable` lines, as strings. -/
def floatComparisonLine (line : String) : Except Failure (String × String × Option Ordering) :=
  match line.splitOn " and ", line.splitOn " < ", line.splitOn " > ", line.splitOn " = " with
  | [x, rest], _, _, _ =>
    if rest.endsWith " are incomparable" then pure (x, dropRightChars rest 17, none)
    else fail "not a comparison line"
  | _, [x, y], _, _ => pure (x, y, some .lt)
  | _, _, [x, y], _ => pure (x, y, some .gt)
  | _, _, _, [x, y] => pure (x, y, some .eq)
  | _, _, _, _ => fail "not a comparison line"

/-- Malachite's rendering of an optional ordering in these lines. -/
def partialOrderingName : Option Ordering → String
  | some o => orderingName o
  | none => "incomparable"

/-- `Float`'s `PartialOrd`: by value, `NaN` incomparable, the zeros equal. -/
def checkFloatPartialCmp (line : String) : Verdict := do
  let (x, y, o) ← floatComparisonLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseFloat y)
  expectEq "partial_cmp" (partialOrderingName (AzFloat.partialCompare x.1 y.1))
    (partialOrderingName o)

/-- Malachite's `ComparableFloat` order, a total order: by value; equal nonzero values by
precision, the lower precision first for positive values and last for negative ones; `-0.0`
below `NaN` below `0.0`. -/
def comparableCmp (x : AzFloat × Bool) (y : AzFloat × Bool) : Ordering :=
  -- the position of the zeros and `NaN` in Malachite's order: `-0.0`, then `NaN`, then `0.0`
  let rank : AzFloat × Bool → Option Nat
    | (.zero, true) => some 0
    | (.nan, _) => some 1
    | (.zero, false) => some 2
    | _ => none
  match rank x, rank y with
  | some a, some b => compare a b
  | some _, none => if y.1.isPositive then .lt else .gt
  | none, some _ => if x.1.isPositive then .gt else .lt
  | none, none =>
    match AzFloat.partialCompare x.1 y.1 with
    | some .eq =>
      match x.1.precision?, y.1.precision? with
      | some p, some q => if x.1.isPositive then compare p q else compare q p
      | _, _ => .eq
    | some o => o
    | none => .eq

def checkComparableFloatPartialCmp (line : String) : Verdict := do
  let (x, y, o) ← floatComparisonLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseFloat y)
  expectEq "ComparableFloat::partial_cmp" (partialOrderingName (some (comparableCmp x y)))
    (partialOrderingName o)

/-- `Float`'s `PartialEq`: equal values, `NaN` unequal to everything, the zeros equal. -/
def checkFloatEq (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseFloat y)
  expectEq "eq" (AzFloat.eqIEEE x.1 y.1) e

/-- `ComparableFloat`'s `Eq`: structural, so the precisions and the zero signs must agree and
`NaN` equals itself. -/
def checkComparableFloatEq (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseFloat y)
  expectEq "ComparableFloat::eq" (x.1 == y.1 && x.2 == y.2) e

/-- A float compared with a natural or an integer, printed in hexadecimal. -/
def checkFloatPartialCmpInteger (line : String) : Verdict := do
  let (x, y, o) ← floatComparisonLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseHexInteger y)
  expectEq "partial_cmp" (partialOrderingName (AzFloat.partialCompare x.1 (AzFloat.ofAzInt y)))
    (partialOrderingName o)

def checkFloatPartialEqInteger (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseFloat x)
  let y ← expect "y" (parseHexInteger y)
  expectEq "partial_eq" (AzFloat.eqIEEE x.1 (AzFloat.ofAzInt y)) e

/-! ### Conversion -/

/-- Malachite's exact conversion of an integer: the precision is the number of significant bits
without the trailing zero bits (`1000` has precision 7, not 10), where `ofAzInt` keeps them. -/
def exactFromInteger (z : AzInt) : AzFloat :=
  match z.abs.trailingZeros with
  | none => .zero
  | some t => (AzFloat.setPrecRound (AzFloat.ofAzInt z) (z.abs.size - t) .Floor).1

/-- `Float::try_from(z) = Ok("Z")` or `Err(Overflow)`, `Float::from_T_prec(z, p) = (Z, o)`, or
`Float::from_T_prec_round(z, p, rm) = (Z, o)`, for a natural or an integer `z` (printed in
decimal) and `T` its type name: exact conversion, or rounding to `p` bits, then Malachite's
range. -/
def checkFloatFromInteger (typeName : String) (line : String) : Verdict := do
  match functionCall line s!"Float::from_{typeName}_prec_round",
      functionCall line s!"Float::from_{typeName}_prec", functionCall line "Float::try_from" with
  | some ([z, p, rm], res), _, _ =>
    let z ← expect "z" (parseAzInt z)
    let p ← expect "precision" (parseNat p)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult s!"from_{typeName}_prec_round"
      (AzFloat.setPrecRound (AzFloat.ofAzInt z) p) rm
    expectFloatPair s!"from_{typeName}_prec_round" computed printed
  | _, some ([z, p], res), _ =>
    let z ← expect "z" (parseAzInt z)
    let p ← expect "precision" (parseNat p)
    let printed ← parseFloatPair res
    let computed ← roundedResult s!"from_{typeName}_prec"
      (AzFloat.setPrecRound (AzFloat.ofAzInt z) p) (.mode .Nearest)
    expectFloatPair s!"from_{typeName}_prec" computed printed
  | _, _, some ([z], res) =>
    let z ← expect "z" (parseAzInt z)
    let exact := exactFromInteger z
    let printed ← expect "result" (parseResult res)
    match printed with
    | none =>
      if exact.exponent?.any (maxExponent < ·) then pure ()
      else disagree s!"try_from: Azurite computed {AzFloat.toHexString exact}, Malachite \
        printed an error"
    | some s =>
      -- the float is printed as a quoted string
      let s := trim s
      if !(s.startsWith "\"" && s.endsWith "\"") then fail "the result is not a quoted string"
      let z ← expect "Z" (parseFloat (dropRightChars (dropChars s 1) 1))
      if exact.exponent?.any (maxExponent < ·) then
        disagree "try_from: the value is beyond Malachite's range, but Malachite printed one"
      else expectFloat "try_from" exact z
  | _, _, _ => fail s!"not a from_{typeName} line"

def checkFloatFromNatural : String → Verdict := checkFloatFromInteger "natural"

def checkFloatFromIntegerValue : String → Verdict := checkFloatFromInteger "integer"

/-- `Float::from(0x7b) = Z` for an unsigned machine integer, printed in hexadecimal: exact. -/
def checkFloatFromUnsigned (line : String) : Verdict := do
  let (args, res) ← expect "a `Float::from(u) = Z` line" (functionCall line "Float::from")
  let u ← match args with
    | [u] => expect "u" (parseHexNatural u)
    | _ => fail "Float::from takes one argument"
  let z ← expect "Z" (parseFloat res)
  expectFloat "from" (exactFromInteger u.toAzInt) z

/-- `Float::from_rational_prec(q, p) = (Z, o)` or `Float::from_rational_prec_round(q, p, rm) =
(Z, o)`: `ofAzRatRound`, then Malachite's range. -/
def checkFloatFromRational (line : String) : Verdict := do
  match functionCall line "Float::from_rational_prec_round",
      functionCall line "Float::from_rational_prec" with
  | some ([q, p, rm], res), _ =>
    let q ← expect "q" (parseAzRat q)
    let p ← expect "precision" (parseNat p)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← parseFloatPair res
    let computed ← roundedResult "from_rational_prec_round" (AzFloat.ofAzRatRound q p) rm
    expectFloatPair "from_rational_prec_round" computed printed
  | _, some ([q, p], res) =>
    let q ← expect "q" (parseAzRat q)
    let p ← expect "precision" (parseNat p)
    let printed ← parseFloatPair res
    let computed ← roundedResult "from_rational_prec" (AzFloat.ofAzRatRound q p) (.mode .Nearest)
    expectFloatPair "from_rational_prec" computed printed
  | _, _ => fail "not a from_rational line"

end Azurite.Oracle
