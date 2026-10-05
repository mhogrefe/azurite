/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzRat
import Azurite.Oracle.AzZModPow2
import Azurite.AzNat.ToStringBase
import Azurite.AzNat.SqrtRem
import Azurite.ExhaustiveGenerator.Basic
import Azurite.ExhaustiveGenerator.PositiveNaturals
import Azurite.ExhaustiveGenerator.AzRanges

/-!
# More checks for Malachite's `Natural`

The `Natural` functions that `AzNat` (or `AzRat`, for scientific notation) already computes but
`Azurite.Oracle.AzNat` did not yet check: equality and the comparisons with primitive integers,
formatting in the power-of-2 bases with widths and prefixes, the limb functions in both orders, the
Euclidean division functions, remainders modulo a power of 2, two-modulus Chinese remaindering,
logarithms, the ceiling and checked square roots, negation, scientific notation, and the
exhaustive generators. Each is the existing Azurite function applied to the printed inputs; the
correspondence is documented on Malachite's "Malachite for Azurite Users: Naturals" page and the
check-by-check record is Malachite's "How Malachite Is Tested: Naturals".
-/

namespace Azurite.Oracle

open Azurite

/-! ### Equality and comparison with primitive integers -/

/-- `x = y` or `x ≠ y` for two naturals: structural equality. -/
def checkNatEq (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  expectEq "eq" (x == y) e

/-- The comparison of a natural with a primitive integer printed in decimal: `compareUInt64` for a
nonnegative primitive; every natural is greater than a negative one. -/
def compareWithPrimitive (n : AzNat) (p : String) : Except Failure Ordering := do
  let i ← expect "primitive" (parseInt p)
  if i < 0 then
    if i < -(2 ^ 63) then fail "the primitive is below the i64 range"
    pure .gt
  else
    let u ← parseUInt64 p
    pure (n.compareUInt64 u)

/-- `n < p`, `n = p`, or `n > p` with the natural first (`first := true`), or `p < n` and so on
with the primitive first. -/
def checkNatCmpPrimitive (first : Bool) (line : String) : Verdict := do
  let (x, y, o) ← comparisonLine line
  let (n, p) := if first then (x, y) else (y, x)
  let n ← expect "n" (parseAzNat n)
  let c ← compareWithPrimitive n p
  let c := if first then c else c.swap
  expectEq "partial_cmp" (orderingName c) (orderingName o)

def checkNatCmpPrimitiveFirst : String → Verdict := checkNatCmpPrimitive true

def checkNatCmpPrimitiveSecond : String → Verdict := checkNatCmpPrimitive false

/-- `n = p` or `n ≠ p`, natural first or primitive first: `beqUInt64` for a nonnegative primitive;
no natural equals a negative one. -/
def checkNatEqPrimitive (first : Bool) (line : String) : Verdict := do
  let (x, y, e) ← equalityLine line
  let (n, p) := if first then (x, y) else (y, x)
  let n ← expect "n" (parseAzNat n)
  let i ← expect "primitive" (parseInt p)
  let computed ← if i < 0 then pure false else do
    let u ← parseUInt64 p
    pure (n.beqUInt64 u)
  expectEq "partial_eq" computed e

def checkNatEqPrimitiveFirst : String → Verdict := checkNatEqPrimitive true

def checkNatEqPrimitiveSecond : String → Verdict := checkNatEqPrimitive false

/-! ### Formatting -/

/-- Rust's zero padding of a formatted number to width `w`: zeros go after the base prefix. -/
def padToWidth (pre body : String) (w : Nat) : String :=
  let len := pre.length + body.length
  if len ≥ w then pre ++ body else pre ++ String.ofList (List.replicate (w - len) '0') ++ body

/-- The rendering of `n` for a Rust format specifier ending in `b`, `o`, `x`, `X`, or nothing
(decimal), with the `#` flag adding the prefix. -/
def formatNatural (n : AzNat) (alt : Bool) (kind : Char) (w : Nat) : Option String :=
  let spec : Option (UInt64 × Bool) := match kind with
    | 'b' => some (2, false)
    | 'o' => some (8, false)
    | 'x' => some (16, false)
    | 'X' => some (16, true)
    | 'd' => some (10, false)
    | _ => none
  match spec with
  | none => none
  | some (b, upper) =>
    let body := AzNat.toStringBaseWith b upper false n
    let pre := if alt && b != 10 then (if b == 2 then "0b" else if b == 8 then "0o" else "0x")
      else ""
    some (padToWidth pre body w)

/-- `format!("{:0W}", n) = s`, `format!("{:#0Wx}", n) = s`, and the other zero-padded forms that
the `_with_width` demos print: the specifier is between the quotes, the number after them. -/
def checkNatFormat (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `format!(spec, n) = s` line" (splitEquals line)
  if !(lhs.startsWith "format!(\"{:" && lhs.endsWith ")") then fail "not a format! call"
  -- drop `format!("{:` (11 characters) and the closing `)`
  let inner := dropRightChars (dropChars lhs 11) 1
  let (spec, n) ← match inner.splitOn "}\", " with
    | [spec, n] => pure (spec, n)
    | _ => fail "not a `{:spec}\", n` argument list"
  let n ← expect "n" (parseAzNat n)
  let alt := spec.startsWith "#"
  let spec := if alt then dropChars spec 1 else spec
  if !spec.startsWith "0" then fail "not a zero-padded specifier"
  let spec := dropChars spec 1
  let (digits, kind) :=
    match spec.toList.getLast? with
    | some c => if c.isDigit then (spec, 'd') else (dropRightChars spec 1, c)
    | none => (spec, 'd')
  let w ← expect "width" (parseNat digits)
  let s ← expect "format" (formatNatural n alt kind w)
  expectEq "format" s rhs

/-- `n.to_string_base_upper(b) = s`: digit letters in upper case, for a base up to 36. -/
def checkNatToStringBaseUpper (line : String) : Verdict := do
  let (n, args, res) ← expect "an `n.to_string_base_upper(b) = s` line"
    (methodCall line "to_string_base_upper")
  let b ← match args with
    | [b] => expect "base" (parseNat b)
    | _ => fail "to_string_base_upper takes one argument"
  if b < 2 || b > 36 then fail "the base is outside [2, 36]"
  let n ← expect "n" (parseAzNat n)
  expectEq "to_string_base_upper" (AzNat.toStringBaseWith (UInt64.ofNat b) true false n) res

/-! ### Limbs -/

/-- `from_limbs_asc([l, …]) = n`, `from_limbs_desc`, and the `from_owned_limbs_*` forms. -/
def checkNatFromLimbs (line : String) : Verdict := do
  let names := [("from_limbs_asc", false), ("from_limbs_desc", true),
    ("from_owned_limbs_asc", false), ("from_owned_limbs_desc", true)]
  let (name, desc) ← match names.find? fun (n, _) => line.startsWith s!"{n}(" with
    | some nd => pure nd
    | none => fail "not a from_limbs line"
  let (args, res) ← expect s!"a `{name}(ls) = n` line" (functionCall line name)
  let ls ← match args with
    | [ls] => expect "limbs" (parseList ls >>= parseLimbs)
    | _ => fail s!"{name} takes one argument"
  let n ← expect "n" (parseAzNat res)
  expectEq name (AzNat.ofLimbs (if desc then ls.reverse else ls)) n

/-- `to_limbs_asc(n) = [l, …]`, `to_limbs_desc`, `into_limbs_*`, `as_limbs_asc`,
`limbs(n).rev()`, and `limb_count(n) = k`. -/
def checkNatToLimbs (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a limbs line" (splitEquals line)
  if lhs.startsWith "limb_count(" then
    let (n, res) ← unaryFunction line "limb_count"
    let k ← expect "count" (parseNat res)
    expectEq "limb_count" n.limbs.size k
  else
    let (lhs, desc) :=
      if lhs.endsWith ".rev()" then (dropRightChars lhs 6, true) else (lhs, false)
    let names := [("to_limbs_asc", false), ("to_limbs_desc", true), ("into_limbs_asc", false),
      ("into_limbs_desc", true), ("as_limbs_asc", false), ("limbs", false)]
    let (name, d) ← match names.find? fun (n, _) => lhs.startsWith s!"{n}(" with
      | some nd => pure nd
      | none => fail "not a to_limbs line"
    let (args, _) ← expect s!"a `{name}(n)` call" (functionCall (lhs ++ " = x") name)
    let n ← match args with
      | [n] => expect "n" (parseAzNat n)
      | _ => fail s!"{name} takes one argument"
    let ls ← expect "limbs" (parseList rhs >>= parseLimbs)
    let computed := if d != desc then n.limbs.reverse else n.limbs
    expectEq name computed ls

/-! ### Division -/

/-- `x.div_euclidean(y) = q`, `x.mod_euclidean(y) = r`, or `x.div_mod_euclidean(y) = (q, r)`,
which on naturals are the truncating `divMod`. -/
def checkNatEuclidean (line : String) : Verdict := do
  match methodCall line "div_mod_euclidean", methodCall line "div_euclidean",
      methodCall line "mod_euclidean" with
  | some (x, [y], res), _, _ =>
    let x ← expect "x" (parseAzNat x)
    let y ← expect "y" (parseAzNat y)
    let (q, r) ← expect "(q, r)" (parseTuple2 res)
    let q ← expect "q" (parseAzNat q)
    let r ← expect "r" (parseAzNat r)
    let (aq, ar) := AzNat.divMod x y
    expectEq "div_mod_euclidean" s!"({aq}, {ar})" s!"({q}, {r})"
  | _, some (x, [y], res), _ =>
    let x ← expect "x" (parseAzNat x)
    let y ← expect "y" (parseAzNat y)
    let q ← expect "q" (parseAzNat res)
    expectEq "div_euclidean" (AzNat.divMod x y).1 q
  | _, _, some (x, [y], res) =>
    let x ← expect "x" (parseAzNat x)
    let y ← expect "y" (parseAzNat y)
    let r ← expect "r" (parseAzNat res)
    expectEq "mod_euclidean" (AzNat.divMod x y).2 r
  | _, _, _ => fail "not a Euclidean division line"

/-- `x is divisible by y` or `x is not divisible by y`: the remainder is zero (with `0` divisible
only by itself, which `mod x 0 = x` gives). -/
def checkNatDivisibleBy (line : String) : Verdict := do
  let (x, y, expected) ←
    match line.splitOn " is not divisible by ", line.splitOn " is divisible by " with
    | [x, y], _ => pure (x, y, false)
    | _, [x, y] => pure (x, y, true)
    | _, _ => fail "not a divisibility line"
  let x ← expect "x" (parseAzNat x)
  let y ← expect "y" (parseAzNat y)
  expectEq "divisible_by" (AzNat.mod x y == (0 : AzNat)) expected

/-- `n.rem_power_of_2(k) = r` (`modPow2`) or `n.neg_mod_power_of_2(k) = r` (the negation of `n`'s
residue in `AzZModPow2 k`). -/
def checkNatRemPowerOf2 (line : String) : Verdict := do
  match methodCall line "rem_power_of_2", methodCall line "neg_mod_power_of_2" with
  | some (n, [k], res), _ =>
    let n ← expect "n" (parseAzNat n)
    let k ← expect "k" (parseNat k)
    let r ← expect "r" (parseAzNat res)
    expectEq "rem_power_of_2" (AzNat.modPow2 n k) r
  | _, some (n, [k], res) =>
    let n ← expect "n" (parseAzNat n)
    let k ← expect "k" (parseNat k)
    let r ← expect "r" (parseAzNat res)
    expectEq "neg_mod_power_of_2" (AzZModPow2.neg (AzZModPow2.ofAzNat k n)).val r
  | _, _ => fail "not a remainder-modulo-a-power-of-2 line"

/-- `r1.crt(m1, r2, m2) = Some(x)` or `None`: Azurite's Garner algorithm on the two moduli, which
must be coprime for a solution to be printed. -/
def checkNatCrt (line : String) : Verdict := do
  let (r1, args, res) ← expect "an `r1.crt(m1, r2, m2) = r` line" (methodCall line "crt")
  let (m1, r2, m2) ← match args with
    | [m1, r2, m2] => pure (m1, r2, m2)
    | _ => fail "crt takes three arguments"
  let r1 ← expect "r1" (parseAzNat r1)
  let m1 ← expect "m1" (parseAzNat m1)
  let r2 ← expect "r2" (parseAzNat r2)
  let m2 ← expect "m2" (parseAzNat m2)
  let res ← expect "result" (parseOption res)
  let coprime := AzNat.gcd m1 m2 == (1 : AzNat)
  match res with
  | some x =>
    let x ← expect "x" (parseAzNat x)
    if !coprime then disagree "Malachite combined moduli that are not coprime"
    expectEq "crt" (AzNat.garner [m1, m2] [r1, r2]) x
  | none =>
    if coprime then disagree s!"crt: Malachite printed None for coprime moduli {m1} and {m2}"
    else pure ()

/-! ### Logarithms and square roots -/

/-- `name(n) = e` or `name(n) = Some(e)`/`None` for the base-2 logarithms: from `AzNat.size` and
`isPowerOfTwo`. -/
def checkNatLogBase2 (line : String) : Verdict := do
  let names := ["floor_log_base_2", "ceiling_log_base_2", "checked_log_base_2"]
  let name ← match names.find? fun n => line.startsWith s!"{n}(" with
    | some n => pure n
    | none => fail "not a base-2 logarithm line"
  let (n, res) ← unaryFunction line name
  if n == (0 : AzNat) then fail "the logarithm of zero is undefined"
  let floor := n.size - 1
  let exact := n.isPowerOfTwo
  match name with
  | "floor_log_base_2" => expectEq name floor (← expect "e" (parseNat res))
  | "ceiling_log_base_2" =>
    expectEq name (if exact then floor else floor + 1) (← expect "e" (parseNat res))
  | _ =>
    let printed ← expect "result" (parseOption res)
    let printed ← match printed with
      | some e => expect "e" ((parseNat e).map some)
      | none => pure none
    expectEq name (optionString (if exact then some floor else none)) (optionString printed)

/-- `name(n, k) = e` (or `Some(e)`/`None`) for the logarithms in base `2^k`. -/
def checkNatLogBasePowerOf2 (line : String) : Verdict := do
  let names := ["floor_log_base_power_of_2", "ceiling_log_base_power_of_2",
    "checked_log_base_power_of_2"]
  let name ← match names.find? fun n => line.startsWith s!"{n}(" with
    | some n => pure n
    | none => fail "not a base-2^k logarithm line"
  let (args, res) ← expect s!"a `{name}(n, k) = e` line" (functionCall line name)
  let (n, k) ← match args with
    | [n, k] => pure (n, k)
    | _ => fail s!"{name} takes two arguments"
  let n ← expect "n" (parseAzNat n)
  let k ← expect "k" (parseNat k)
  if n == (0 : AzNat) || k == 0 then fail "the logarithm is undefined"
  let bits := n.size - 1
  let floor := bits / k
  let exact := n.isPowerOfTwo && bits % k == 0
  match name with
  | "floor_log_base_power_of_2" => expectEq name floor (← expect "e" (parseNat res))
  | "ceiling_log_base_power_of_2" =>
    expectEq name (if exact then floor else floor + 1) (← expect "e" (parseNat res))
  | _ =>
    let printed ← expect "result" (parseOption res)
    let printed ← match printed with
      | some e => expect "e" ((parseNat e).map some)
      | none => pure none
    expectEq name (optionString (if exact then some floor else none)) (optionString printed)

/-- `⌊log_b n⌋` and whether `n` is a power of `b`: `AzRat.floorLogBaseAbs` and `cmpPowAbs` for a
base that fits in a limb, repeated multiplication otherwise. -/
def natLogBase (n b : AzNat) : Nat × Bool :=
  if b.limbs.size ≤ 1 then
    let bb := b.limbs.getD 0 0
    let f := AzRat.floorLogBaseAbs bb n.toAzRat
    (f.toNat, AzRat.cmpPowAbs bb f n.toAzRat == .eq)
  else Id.run do
    -- a base of two or more limbs: at most `n.size / 64` multiplications
    let mut e := 0
    let mut p : AzNat := 1
    for _ in [0:n.size + 1] do
      let q := AzNat.mul p b
      if AzNat.compare q n == .gt then break
      p := q
      e := e + 1
    return (e, p == n)

/-- `floor_log_base(n, b) = e`, `ceiling_log_base(n, b) = e`, or `checked_log_base(n, b) = …`. -/
def checkNatLogBase (line : String) : Verdict := do
  let names := ["floor_log_base", "ceiling_log_base", "checked_log_base"]
  let name ← match names.find? fun n => line.startsWith s!"{n}(" with
    | some n => pure n
    | none => fail "not a logarithm line"
  let (args, res) ← expect s!"a `{name}(n, b) = e` line" (functionCall line name)
  let (n, b) ← match args with
    | [n, b] => pure (n, b)
    | _ => fail s!"{name} takes two arguments"
  let n ← expect "n" (parseAzNat n)
  let b ← expect "base" (parseAzNat b)
  if n == (0 : AzNat) || AzNat.compare b 2 == .lt then fail "the logarithm is undefined"
  let (floor, exact) := natLogBase n b
  match name with
  | "floor_log_base" => expectEq name floor (← expect "e" (parseNat res))
  | "ceiling_log_base" =>
    expectEq name (if exact then floor else floor + 1) (← expect "e" (parseNat res))
  | _ =>
    let printed ← expect "result" (parseOption res)
    let printed ← match printed with
      | some e => expect "e" ((parseNat e).map some)
      | none => pure none
    expectEq name (optionString (if exact then some floor else none)) (optionString printed)

/-- `x.ceiling_sqrt() = r` or `x.checked_sqrt() = Some(r)`/`None`, from `AzNat.sqrtRem`. -/
def checkNatSqrtVariants (line : String) : Verdict := do
  match methodCall line "ceiling_sqrt", methodCall line "checked_sqrt" with
  | some (x, [], res), _ =>
    let x ← expect "x" (parseAzNat x)
    let r ← expect "r" (parseAzNat res)
    let (s, rem) := AzNat.sqrtRem x
    expectEq "ceiling_sqrt" (if rem == (0 : AzNat) then s else AzNat.add s 1) r
  | _, some (x, [], res) =>
    let x ← expect "x" (parseAzNat x)
    let printed ← expect "result" (parseOption res)
    let printed ← match printed with
      | some r => expect "r" ((parseAzNat r).map some)
      | none => pure none
    let (s, rem) := AzNat.sqrtRem x
    expectEq "checked_sqrt" (optionString (if rem == (0 : AzNat) then some s else none))
      (optionString printed)
  | _, _ => fail "not a square-root line"

/-! ### Negation -/

/-- `-n = z` or `-(&n) = z`: the integer `-n`. -/
def checkNatNeg (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `-n = z` line" (splitEquals line)
  if !lhs.startsWith "-" then fail "not a negation"
  let n ← expect "n" (parseAzNat (stripRef (dropChars lhs 1)))
  let z ← expect "z" (parseAzInt rhs)
  expectEq "neg" (AzInt.neg n.toAzInt) z

/-! ### Scientific notation -/

/-- Malachite's `FromSciStringOptions`, as `Debug` prints it:
`FromSciStringOptions { base: 10, rounding_mode: Nearest }`. -/
def parseFromSciStringOptions (s : String) : Except Failure (UInt64 × Rounding) := do
  let s := trim s
  let prefix_ := "FromSciStringOptions { "
  if !(s.startsWith prefix_ && s.endsWith " }") then fail "not a FromSciStringOptions value"
  let fields := (splitTopLevel (dropRightChars (dropChars s prefix_.length) 2) ',').map fun f =>
    match (trim f).splitOn ": " with
    | [k, v] => (k, trim v)
    | _ => (trim f, "")
  let base ← match fields.lookup "base" with
    | some v => expect "base" (parseNat v)
    | none => fail "FromSciStringOptions has no base"
  let rm ← match fields.lookup "rounding_mode" with
    | some v => expect "rounding mode" (parseRounding v)
    | none => fail "FromSciStringOptions has no rounding_mode"
  if base < 2 || base > 36 then fail "the base is outside [2, 36]"
  pure (UInt64.ofNat base, rm)

/-- Malachite's `Natural::from_sci_string_with_options`: the exact rational the string denotes,
rounded to an integer in the given mode (`None` under `Exact` when it is not an integer), and
`None` when that integer is negative. -/
def naturalFromSci (s : String) (b : UInt64) (rm : Rounding) : Option AzNat := do
  let q ← AzRat.fromSci s b
  let z ← match rm with
    | .mode m => some (AzRat.round q m).1
    | .exact => if q.den == (1 : AzNat) then some (AzRat.round q .Floor).1 else none
  if z.sign then some z.abs else none

/-- `Natural::from_sci_string(s) = r` or `Natural::from_sci_string_with_options(s, options) = r`,
the string printed bare. -/
def checkNatFromSciString (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `Natural::from_sci_string…(s) = r` line" (splitEquals line)
  let (s, b, rm) ←
    if lhs.startsWith "Natural::from_sci_string_with_options(" && lhs.endsWith " })" then
      let inner := dropRightChars (dropChars lhs 38) 1
      match inner.splitOn ", FromSciStringOptions { " with
      | [s, rest] =>
        let (b, rm) ← parseFromSciStringOptions ("FromSciStringOptions { " ++ rest)
        pure (s, b, rm)
      | _ => fail "from_sci_string_with_options takes a string and options"
    else if lhs.startsWith "Natural::from_sci_string(" && lhs.endsWith ")" then
      pure (dropRightChars (dropChars lhs 25) 1, (10 : UInt64), Rounding.mode .Nearest)
    else fail "not a from_sci_string call"
  let res ← parsedNatural rhs
  expectEq "from_sci_string" (optionString (naturalFromSci s b rm)) (optionString res)

/-- `x.to_sci() = s`: `AzRat.toSci` with the default options. -/
def checkNatToSci (line : String) : Verdict := do
  let (x, args, res) ← expect "an `x.to_sci() = s` line" (methodCall line "to_sci")
  if !args.isEmpty then fail "to_sci takes no arguments"
  let x ← expect "x" (parseAzNat x)
  expectEq "to_sci" (AzRat.toSciString x.toAzRat) res

/-- `to_sci_with_options(x, ToSciOptions { … }) = s`: `AzRat.toSci` on the integer `x`, `Exact`
being `toSciExact`. -/
def checkNatToSciWithOptions (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `to_sci_with_options(x, options) = s` line" (splitEquals line)
  let prefix_ := "to_sci_with_options("
  if !(lhs.startsWith prefix_ && lhs.endsWith ")") then fail "not a to_sci_with_options call"
  let inner := dropRightChars (dropChars lhs prefix_.length) 1
  let (x, options) ← match inner.splitOn ", ToSciOptions { " with
    | [x, rest] => pure (x, "ToSciOptions { " ++ rest)
    | _ => fail "to_sci_with_options takes a natural and options"
  let x ← expect "x" (parseAzNat x)
  let (o, rm) ← parseToSciOptions options
  if rm matches .exact then
    if !AzRat.toSciExact x.toAzRat o then
      disagree "Malachite printed an Exact conversion that rounds"
  match AzRat.toSci x.toAzRat o with
  | some s => expectEq "to_sci_with_options" s rhs
  | none => disagree "Azurite cannot meet the request these options make"

/-- `x can be converted to sci using ToSciOptions { … }`, or `cannot be`. -/
def checkNatFmtSciValid (line : String) : Verdict := do
  let (x, options, expected) ←
    match line.splitOn " cannot be converted to sci using ",
        line.splitOn " can be converted to sci using " with
    | [x, o], _ => pure (x, o, false)
    | _, [x, o] => pure (x, o, true)
    | _, _ => fail "not a fmt_sci_valid line"
  let x ← expect "x" (parseAzNat x)
  let (o, rm) ← parseToSciOptions options
  let valid := match rm with
    | .exact => AzRat.toSciExact x.toAzRat o
    | .mode _ => (AzRat.toSciNumber x.toAzRat o).isSome
  expectEq "fmt_sci_valid" valid expected

/-! ### Exhaustive generation -/

/-- The first `k` values of an exhaustive generator, as naturals. -/
def generatorPrefix {T : Type} [g : ExhaustiveGenerator T] (val : T → AzNat) (k : Nat) :
    List AzNat :=
  (List.range k).filterMap fun i => (g.gen i).map val

/-- `exhaustive_naturals()[i] = n` or `exhaustive_positive_naturals()[i] = n`: the `i`-th value of
Azurite's generator. -/
def checkExhaustiveIndexed (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `generator()[i] = n` line" (splitEquals line)
  let (name, idx) ← match lhs.splitOn "()[" with
    | [name, idx] =>
      if idx.endsWith "]" then pure (name, dropRightChars idx 1)
      else fail "not an indexed generator line"
    | _ => fail "not an indexed generator line"
  let i ← expect "index" (parseNat idx)
  let n ← expect "n" (parseAzNat rhs)
  let computed : Option AzNat ← match name with
    | "exhaustive_naturals" => pure (naturalsGen.gen i)
    | "exhaustive_positive_naturals" => pure ((positiveNaturalsGen.gen i).map (·.val))
    | _ => fail s!"unknown generator {name}"
  expectEq name (optionString computed) (optionString (some n))

/-- `exhaustive_natural_range(a, b) = [x, …]`, the inclusive and to-infinity forms likewise: the
printed prefix (up to twenty values) must be the same prefix of Azurite's generator. -/
def checkExhaustiveRange (line : String) : Verdict := do
  let (lhs, rhs) ← expect "a `generator(args) = [x, …]` line" (splitEquals line)
  let printed ← expect "values" (parseList rhs >>= parseAzNats)
  let k := printed.length
  let computed ←
    match functionCall line "exhaustive_natural_range",
        functionCall line "exhaustive_natural_inclusive_range",
        functionCall line "exhaustive_natural_range_to_infinity" with
    | some ([a, b], _), _, _ => do
      let a ← expect "a" (parseAzNat a)
      let b ← expect "b" (parseAzNat b)
      pure (@generatorPrefix _ (azNatRangeGen a b) (·.val) (k + 1))
    | _, some ([a, b], _), _ => do
      let a ← expect "a" (parseAzNat a)
      let b ← expect "b" (parseAzNat b)
      pure (@generatorPrefix _ (azNatRangeInclusiveGen a b) (·.val) (k + 1))
    | _, _, some ([a], _) => do
      let a ← expect "a" (parseAzNat a)
      pure (@generatorPrefix _ (azNatRangeToInfinityGen a) (·.val) k)
    | _, _, _ => fail "not a range-generator line"
  -- Malachite prints the whole range when it has fewer than twenty values, so a shorter prefix
  -- must be the whole of Azurite's range too; `computed` holds one value more than was printed
  if k < 20 && computed.length > k then
    disagree s!"{lhs}: Azurite's generator has more than the {k} values Malachite printed"
  expectEq lhs (toString (computed.take k)) (toString printed)

end Azurite.Oracle
