/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Oracle.AzFloat
import Azurite.AzFloat.Float64
import Azurite.AzRat.LogBase
import Azurite.AzRat.Shift

/-!
# Checks for the conversions between Malachite's `Natural` and the primitive floats

Malachite prints an `f32` or `f64` as the shortest decimal that reads back to it (Rust's `Display`,
through `NiceFloat`). The oracle reads such a decimal back exactly: the decimal is an exact rational
(`AzRat.fromSci`), and the float it denotes is the IEEE 754 binary format's nearest value to that
rational, ties to even, subnormals included (`ieeeNearest`). Values are then compared as values,
so the precision an `AzFloat` happens to carry does not matter.

The conversions themselves are computed with Azurite: a natural becomes an exact `AzFloat`
(`ofAzNat`) and is rounded to the format with `AzFloat.toFloat64` (for `f64`, with its proven IEEE
rounding) or `setPrecRound` (for `f32`, where a natural can never be subnormal), and a float
becomes a natural through its exact rational value and `AzRat.round`. Overflow follows IEEE 754:
the natural is rounded to the format's precision first, and only a rounded value above the largest
finite float overflows, to `∞` under `Nearest`, `Ceiling`, and `Up` and to the largest finite float
under `Floor` and `Down`.

A negative float, `-∞` included, converts to the natural 0, above the input, under `Down`,
`Ceiling`, and `Nearest`, as Malachite documents; under the other modes it panics.

The demos for the two float types print the same lines, so each type has its own modes, the
format being part of the mode.
-/

namespace Azurite.Oracle

open Azurite

/-- An IEEE 754 binary format: precision `p`, the largest `AzFloat` exponent of a finite value
`emax` (`1024` for `f64`, so that values are below `2^1024`), and the exponent of the smallest
subnormal, `2^qmin`. -/
structure BinaryFormat where
  p : Nat
  emax : Int
  qmin : Int
  name : String

def binary64 : BinaryFormat := { p := 53, emax := 1024, qmin := -1074, name := "f64" }

def binary32 : BinaryFormat := { p := 24, emax := 128, qmin := -149, name := "f32" }

/-- The largest finite value of the format, `(1 - 2^-p) · 2^emax`. -/
def BinaryFormat.maxFinite (fmt : BinaryFormat) : AzFloat :=
  AzFloat.mkFinite true (AzInt.ofInt fmt.emax) fmt.p (AzNat.lowMask fmt.p)

/-- The value of the format nearest to `q`, ties to even, with subnormals: `q` is rounded to `p`
bits in the normal range and to a multiple of `2^qmin` below it. Overflow does not arise for the
decimals the demos print, which all denote finite floats. -/
def ieeeNearest (fmt : BinaryFormat) (q : AzRat) : AzFloat :=
  if q.num == (0 : AzNat) then .zero
  else
    let e2 := AzRat.floorLogBaseAbs 2 q
    -- bits from the leading one down to the `2^qmin` place
    let bitsAboveQuantum := e2 - fmt.qmin + 1
    if bitsAboveQuantum ≥ fmt.p then (AzFloat.ofAzRatRound q fmt.p .Nearest).1
    else if bitsAboveQuantum ≥ 1 then (AzFloat.ofAzRatRound q bitsAboveQuantum.toNat .Nearest).1
    else
      -- below the smallest subnormal: it, or zero (a tie at half of it goes to zero, the even
      -- one); the comparison with the halfway point `2^(qmin - 1)` is exact
      let half : AzRat := (1 : AzRat) >>> (1 - fmt.qmin).toNat
      if AzRat.cmp (AzRat.abs q) half == .gt then
        AzFloat.mkFinite q.sign (AzInt.ofInt (fmt.qmin + 1)) 1 1
      else .zero

/-- A float as Malachite prints it, read as the value of the format it denotes. -/
def parsePrimitiveFloat (fmt : BinaryFormat) (s : String) : Option AzFloat :=
  match trim s with
  | "NaN" => some .nan
  | "Infinity" => some (.infinity true)
  | "-Infinity" => some (.infinity false)
  | s => (AzRat.fromSci s 10).map (ieeeNearest fmt)

/-- Equality of values (not of representations): `NaN` equals itself here, since both sides print
it the same way. -/
def sameValue (a b : AzFloat) : Bool :=
  (a.isNaN && b.isNaN) || AzFloat.partialCompare a b == some .eq

def expectSameFloat (what : String) (computed printed : AzFloat) : Verdict :=
  if sameValue computed printed then .ok ()
  else disagree s!"{what}: Azurite computed {AzFloat.toHexString computed}, Malachite printed \
    {AzFloat.toHexString printed}"

/-! ### Natural to float -/

/-- A natural rounded to the format in a rounding mode, with the `Ordering` of the result against
the natural. The natural is rounded to `p` bits first; a rounded value above the largest finite
value becomes the maximum under `Floor` and `Down` and `∞` otherwise, as in IEEE 754. -/
def naturalToFloat (fmt : BinaryFormat) (n : AzNat) (m : RoundingMode) : AzFloat × Ordering :=
  let x := AzFloat.ofAzNat n
  if n == (0 : AzNat) then (.zero, .eq)
  else if fmt.p == 53 then
    let r := AzFloat.ofFloat64 (AzFloat.toFloat64 x m)
    (r, (AzFloat.partialCompare r x).getD .eq)
  else
    -- round to `p` bits with an unbounded exponent; overflow only if the rounded value is too big
    let (r, o) := AzFloat.setPrecRound x fmt.p m
    if AzFloat.partialCompare r fmt.maxFinite == some .gt then
      match m with
      | .Floor | .Down => (fmt.maxFinite, .lt)
      | _ => (.infinity true, .gt)
    else (r, o)

/-- Whether the natural is exactly a value of the format. -/
def naturalFitsFloat (fmt : BinaryFormat) (n : AzNat) : Bool :=
  (naturalToFloat fmt n .Nearest).2 == .eq &&
    !(AzFloat.partialCompare (AzFloat.ofAzNat n) fmt.maxFinite == some .gt)

/-- The format named at the start of a line (`f32::…`) or at its end (`… an f32`). -/
def formatOfName : String → Option BinaryFormat
  | "f32" => some binary32
  | "f64" => some binary64
  | _ => none

/-- `T::rounding_from(&n, rm) = (f, o)`, `T::try_from(&n) = Ok(f)`/`Err(…)`,
`T::exact_from(&n) = f`, or `n is convertible to an T`/`is not convertible`, for `T` either float
type. -/
def checkNatToFloat (line : String) : Verdict := do
  if line.endsWith " f32" || line.endsWith " f64" then
    let (n, t, expected) ←
      match line.splitOn " is not convertible to an ", line.splitOn " is convertible to an " with
      | [n, t], _ => pure (n, t, false)
      | _, [n, t] => pure (n, t, true)
      | _, _ => fail "not a convertibility line"
    let fmt ← expect "float type" (formatOfName t)
    let n ← expect "n" (parseAzNat n)
    expectEq "convertible_from" (naturalFitsFloat fmt n) expected
  else
    let (lhs, rhs) ← expect "a `T::…(&n) = r` line" (splitEquals line)
    let (t, rest) ← match lhs.splitOn "::" with
      | [t, rest] => pure (t, rest)
      | _ => fail "not a `T::…` call"
    let fmt ← expect "float type" (formatOfName t)
    let call := s!"{rest} = {rhs}"
    match functionCall call "rounding_from", functionCall call "try_from",
        functionCall call "exact_from" with
    | some ([n, rm], res), _, _ =>
      let n ← expect "n" (parseAzNat n)
      let rm ← expect "rounding mode" (parseRounding rm)
      let (f, o) ← expect "(float, ordering)" (parseTuple2 res)
      let f ← expect "float" (parsePrimitiveFloat fmt f)
      let o ← expect "ordering" (parseOrdering o)
      let (r, ro) ← match rm with
        | .mode m => pure (naturalToFloat fmt n m)
        | .exact =>
          let (r, ro) := naturalToFloat fmt n .Nearest
          if ro != .eq then disagree "Malachite printed an Exact conversion that rounds"
          pure (r, ro)
      expectSameFloat s!"{t}::rounding_from" r f
      expectEq s!"{t}::rounding_from ordering" (orderingName ro) (orderingName o)
    | _, some ([n], res), _ =>
      let n ← expect "n" (parseAzNat n)
      if trim res == "Err(PrimitiveFloatFromNaturalError)" then
        expectEq s!"{t}::try_from" (naturalFitsFloat fmt n) false
      else
        let res ← expect "Ok(f)" (if res.startsWith "Ok(" && res.endsWith ")" then
          some (dropRightChars (dropChars res 3) 1) else none)
        let f ← expect "float" (parsePrimitiveFloat fmt res)
        if !naturalFitsFloat fmt n then disagree s!"{t}::try_from: {n} is not exactly a float"
        expectSameFloat s!"{t}::try_from" (naturalToFloat fmt n .Nearest).1 f
    | _, _, some ([n], res) =>
      let n ← expect "n" (parseAzNat n)
      let f ← expect "float" (parsePrimitiveFloat fmt res)
      if !naturalFitsFloat fmt n then disagree s!"{t}::exact_from: {n} is not exactly a float"
      expectSameFloat s!"{t}::exact_from" (naturalToFloat fmt n .Nearest).1 f
    | _, _, _ => fail "not a natural-to-float line"

/-! ### Float to natural -/

/-- `Natural::rounding_from(f, rm) = (n, o)`, `Natural::try_from(f) = Ok(n)`/`Err(…)`,
`Natural::exact_from(f) = n`, or `f is convertible to a Natural`/`is not`, for floats of the
format `fmt` (the lines do not name the type, so the mode does). -/
def checkNatFromFloat (fmt : BinaryFormat) (line : String) : Verdict := do
  if line.endsWith " convertible to a Natural" then
    let (f, expected) ←
      match line.splitOn " is not convertible to a Natural",
          line.splitOn " is convertible to a Natural" with
      | [f, ""], _ => pure (f, false)
      | _, [f, ""] => pure (f, true)
      | _, _ => fail "not a convertibility line"
    let f ← expect "float" (parsePrimitiveFloat fmt f)
    let ok := match f.toAzRat? with
      | some q => q.den == (1 : AzNat) && q.sign
      | none => false
    expectEq "convertible_from" ok expected
  else
    match functionCall line "Natural::rounding_from", functionCall line "Natural::try_from",
        functionCall line "Natural::exact_from" with
    | some ([f, rm], res), _, _ =>
      let f ← expect "float" (parsePrimitiveFloat fmt f)
      let rm ← expect "rounding mode" (parseRounding rm)
      let (n, o) ← expect "(natural, ordering)" (parseTuple2 res)
      let n ← expect "n" (parseAzNat n)
      let o ← expect "ordering" (parseOrdering o)
      -- a negative value, `-∞` included, is 0 (above it) under `Down`, `Ceiling`, and `Nearest`;
      -- Malachite documents a panic under the other modes, so such a line is a disagreement
      let negative := match f with
        | .infinity s => !s
        | _ => match f.toAzRat? with
          | some q => !q.sign && q != 0
          | none => false
      if negative then
        match rm with
        | .mode .Down | .mode .Ceiling | .mode .Nearest =>
          expectEq "rounding_from" (pairString (0 : AzNat) Ordering.gt) (pairString n o)
        | _ => disagree "rounding_from: Malachite printed a negative input that should panic"
      else
      let q ← expect "a finite float" f.toAzRat?
      let (z, zo) ← match rm with
        | .mode m => pure (AzRat.round q m)
        | .exact =>
          if q.den != (1 : AzNat) then disagree "Malachite printed an Exact conversion that rounds"
          pure ((AzRat.round q .Floor).1, .eq)
      if !z.sign then disagree s!"rounding_from: the result {z} is negative"
      expectEq "rounding_from" (pairString z.abs zo) (pairString n o)
    | _, some ([f], res), _ =>
      let f ← expect "float" (parsePrimitiveFloat fmt f)
      let computed : String := match f.toAzRat? with
        | none => "Err(FloatInfiniteOrNan)"
        | some q =>
          if !q.sign then "Err(FloatNegative)"
          else if q.den != (1 : AzNat) then "Err(FloatNonIntegerOrOutOfRange)"
          else s!"Ok({q.num})"
      expectEq "try_from" computed (trim res)
    | _, _, some ([f], res) =>
      let f ← expect "float" (parsePrimitiveFloat fmt f)
      let q ← expect "a finite float" f.toAzRat?
      let n ← expect "n" (parseAzNat res)
      if !(q.den == (1 : AzNat) && q.sign) then disagree "exact_from of a non-natural float"
      expectEq "exact_from" q.num n
    | _, _, _ => fail "not a float-to-natural line"

def checkNatFromF32 : String → Verdict := checkNatFromFloat binary32

def checkNatFromF64 : String → Verdict := checkNatFromFloat binary64

/-! ### Scientific mantissa and exponent -/

/-- `n` rounded to the format's precision in mode `m` and split as `mantissa · 2^exponent` with
the mantissa in `[1, 2)`, with the `Ordering` of the rounded value against `n`; a carry to the next
power of 2 moves to the exponent. -/
def sciMantissaAndExponent (fmt : BinaryFormat) (n : AzNat) (m : RoundingMode) :
    Option (AzFloat × Int × Ordering) :=
  match AzFloat.setPrecRound (AzFloat.ofAzNat n) fmt.p m with
  | (r@(.finite _ e _ _ _), o) =>
    let ex := e - 1
    some (AzFloat.shiftLeft r (-ex), ex.toInt, o)
  | _ => none

/-- The rational `m · 2^e` for a float mantissa and a natural exponent, if the mantissa is in
`[1, 2)`. -/
def sciValue (m : AzFloat) (e : Nat) : Option AzRat := do
  let q ← m.toAzRat?
  guard (AzRat.cmp q 1 != .lt && AzRat.cmp q 2 == .lt)
  pure (q <<< e)

/-- The lines of the `sci_mantissa_and_exponent` family for floats of the format `fmt`. -/
def checkNatSci (fmt : BinaryFormat) (line : String) : Verdict := do
  match functionCall line "sci_mantissa_and_exponent_round",
      functionCall line "sci_mantissa_and_exponent", functionCall line "sci_mantissa",
      functionCall line "sci_exponent" with
  | some ([n, rm], res), _, _, _ =>
    let n ← expect "n" (parseAzNat n)
    let rm ← expect "rounding mode" (parseRounding rm)
    let printed ← expect "result" (parseOption res)
    let computed := match rm with
      | .mode m => sciMantissaAndExponent fmt n m
      | .exact => (sciMantissaAndExponent fmt n .Nearest).filter (·.2.2 == .eq)
    match computed, printed with
    | none, none => pure ()
    | some (cm, ce, co), some t =>
      let (pm, pe, po) ← expect "(m, e, o)" (parseTuple3 t)
      let pm ← expect "mantissa" (parsePrimitiveFloat fmt pm)
      let pe ← expect "exponent" (parseInt pe)
      let po ← expect "ordering" (parseOrdering po)
      expectSameFloat "sci_mantissa_and_exponent_round" cm pm
      expectEq "sci exponent" ce pe
      expectEq "sci ordering" (orderingName co) (orderingName po)
    | c, _ => disagree s!"sci_mantissa_and_exponent_round: Azurite has \
        {if c.isSome then "a result" else "none"}, Malachite printed {res}"
  | _, some ([n], res), _, _ =>
    let n ← expect "n" (parseAzNat n)
    let (pm, pe) ← expect "(m, e)" (parseTuple2 res)
    let pm ← expect "mantissa" (parsePrimitiveFloat fmt pm)
    let pe ← expect "exponent" (parseInt pe)
    let (cm, ce, _) ← expect "a positive n" (sciMantissaAndExponent fmt n .Nearest)
    expectSameFloat "sci_mantissa_and_exponent" cm pm
    expectEq "sci exponent" ce pe
  | _, _, some ([n], res), _ =>
    let n ← expect "n" (parseAzNat n)
    let pm ← expect "mantissa" (parsePrimitiveFloat fmt res)
    let (cm, _, _) ← expect "a positive n" (sciMantissaAndExponent fmt n .Nearest)
    expectSameFloat "sci_mantissa" cm pm
  | _, _, _, some ([n], res) =>
    let n ← expect "n" (parseAzNat n)
    let pe ← expect "exponent" (parseInt res)
    let (_, ce, _) ← expect "a positive n" (sciMantissaAndExponent fmt n .Nearest)
    expectEq "sci_exponent" ce pe
  | _, _, _, _ =>
    match functionCall line "Natural::from_sci_mantissa_and_exponent_round",
        functionCall line "Natural::from_sci_mantissa_and_exponent" with
    | some ([m, e, rm], res), _ =>
      let m ← expect "mantissa" (parsePrimitiveFloat fmt m)
      let e ← expect "exponent" (parseNat e)
      let rm ← expect "rounding mode" (parseRounding rm)
      let printed ← expect "result" (parseOption res)
      let computed : Option (AzNat × Ordering) := do
        let q ← sciValue m e
        let (z, o) ← match rm with
          | .mode md => some (AzRat.round q md)
          | .exact => if q.den == (1 : AzNat) then some ((AzRat.round q .Floor).1, .eq) else none
        pure (z.abs, o)
      let computedStr := match computed with
        | some (n, o) => s!"Some({pairString n o})"
        | none => "None"
      let printedStr ← match printed with
        | some t => do
          let (n, o) ← expect "(n, o)" (parseTuple2 t)
          let n ← expect "n" (parseAzNat n)
          let o ← expect "o" (parseOrdering o)
          pure s!"Some({pairString n o})"
        | none => pure "None"
      expectEq "from_sci_mantissa_and_exponent_round" computedStr printedStr
    | _, some ([m, e], res) =>
      let m ← expect "mantissa" (parsePrimitiveFloat fmt m)
      let e ← expect "exponent" (parseNat e)
      let printed ← expect "result" (parseOption res)
      let printed ← match printed with
        | some n => expect "n" ((parseAzNat n).map some)
        | none => pure none
      let computed := (sciValue m e).map fun q => (AzRat.round q .Nearest).1.abs
      expectEq "from_sci_mantissa_and_exponent" (optionString computed) (optionString printed)
    | _, _ => fail "not a sci-mantissa line"

def checkNatSciF32 : String → Verdict := checkNatSci binary32

def checkNatSciF64 : String → Verdict := checkNatSci binary64

end Azurite.Oracle
