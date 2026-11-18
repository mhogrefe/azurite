/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan`

The special values (`NaN`, `arctan (±∞) = ±π/2` in the three modes, `arctan 0 = 0` at every
precision, `p = 0`), the correctly rounded 53-bit values of `arctan (1/2)`, `arctan (±1)`,
`arctan 3`, `arctan (1/1024)`, `arctan 100`, `arctan (−1000)`, `arctan 10¹²`, `arctan 2⁶⁰`,
`arctan` of the 53-bit floats nearest `−7/5`, `22/7` and `1/3`, the neighbours of `1`, the
directed modes, 1-, 2- and 20-bit results, 200- and 400-bit values.  Extreme arguments: `2⁻⁴⁰`
(the ordinary path next to the argument), `±2^(−2^30)`, `(3/2)·2^(−2^30)` at 100 bits (the tiny
path, independent of the exponent), `2^1000` (next to `π/2`) and `2^(2^30)`.  References: a
1400-bit fixed-point evaluation (forty halvings `t ↦ t/(1 + √(1 + t²))`, Taylor series, Machin
`π`) at the exact float arguments, rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atanPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("1.5707963267948966", .lt)
#guard D (A (infinity true) 53 .Floor) == ("1.5707963267948966", .lt)
#guard D (A (infinity true) 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (infinity false) 53) == ("-1.5707963267948966", .gt)
#guard D (A (infinity false) 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (A (infinity false) 53 .Ceiling) == ("-1.5707963267948966", .gt)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "1" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "0.5" 53) 53) == ("0.4636476090008061", .lt)
#guard D (A (X "1" 53) 53) == ("0.7853981633974483", .lt)
#guard D (A (X "-1" 53) 53) == ("-0.7853981633974483", .gt)
#guard D (A (X "3" 53) 53) == ("1.2490457723982544", .gt)
#guard D (A (X "0.0009765625" 53) 53) == ("0.0009765621895593195", .gt)
#guard D (A (X "100" 53) 53) == ("1.5607966601082315", .gt)
#guard D (A (X "-1000" 53) 53) == ("-1.5697963271282298", .lt)
#guard D (A (X "1000000000000" 53) 53) == ("1.5707963267938967", .gt)
#guard D (A (X "1152921504606846976" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A (X "-1.4" 53) 53) == ("-0.9505468408120751", .gt)
#guard D (A (X "3.142857142857143" 53) 53) == ("1.2627435457711202", .gt)
#guard D (A (X "0.3333333333333333" 53) 53) == ("0.3217505543966422", .gt)
-- the neighbours of `1`: `1 + 2^(−52)` and `1 − 2^(−53)`
#guard D (A (X "1.0000000000000002" 53) 53) == ("0.7853981633974484", .lt)
#guard D (A (X "0.9999999999999999" 53) 53) == ("0.7853981633974483", .gt)

-- directed modes and other precisions
#guard D (A (X "1" 53) 53 .Floor) == ("0.7853981633974483", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.7853981633974484", .gt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.7853981633974484", .lt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-0.7853981633974483", .gt)
#guard D (A (X "3" 53) 53 .Floor) == ("1.2490457723982542", .lt)
#guard D (A (X "3" 53) 53 .Ceiling) == ("1.2490457723982544", .gt)
#guard D (A (X "-3" 53) 53 .Floor) == ("-1.2490457723982544", .lt)
#guard D (A (X "-3" 53) 53 .Ceiling) == ("-1.2490457723982542", .gt)
#guard D (A (X "3" 53) 20) == ("1.249046", .gt)
#guard D (A (X "0.5" 53) 1) == ("0.5", .gt)
#guard D (A (X "0.5" 53) 2) == ("0.5", .gt)
#guard toString (atan (X "1" 53)) == "0.7853981633974483"
#guard toString (atan (X "1" 200)) == "0.7853981633974483096156608458198757210492923498437764552437\
  36"
#guard toString (atan (X "100" 200)) == "1.56079666010823138102498157543047189353721534714317627085\
  9533"
#guard toString (atan (X "-0.333333333333333333333333333333333333333333333333333333333333\
  4" 200)) == "-0.321750554396642193401404614358661319020755295557656191\
  4328033"
#guard D (A (X "0.75" 53) 400) ==
    ("0.64350110879328438680280922871732263804151059111531238286560611\
  87135124748116210887128168447012827488780143387542594782965", .lt)

-- small arguments on the ordinary path
#guard D (A (X "9.094947017729282e-13" 53) 53) == ("9.094947017729282e-13", .gt)
#guard D (A (X "9.094947017729282e-13" 53) 53 .Floor) == ("9.094947017729281e-13", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 200) == ("7.88860905221011805411728565282786\
  229673206435109023004770279e-31", .gt)

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
#guard A tinyX 53 == (tinyX, .gt)
#guard A tinyX 53 .Ceiling == (tinyX, .gt)
#guard (A tinyX 53 .Floor).2 == .lt
#guard (A tinyX 53 .Floor).1 != tinyX
#guard A (-tinyX) 53 == (-tinyX, .lt)
#guard A (-tinyX) 53 .Floor == (-tinyX, .lt)
#guard (A (-tinyX) 53 .Ceiling).2 == .gt
#guard A ((X "1.5" 100) <<< tinyE) 53 == ((X "1.5" 53) <<< tinyE, .gt)
#guard (A tinyX 200).1 == (X "1" 200) <<< tinyE
#guard atan tinyX == tinyX
-- the tiny path and the loop agree where both apply (`2^(−200)` at 53 and at 150 bits)
#guard A ((X "1" 53) <<< AzInt.ofInt (-200)) 53 .Floor
  == ((A ((X "1" 53) <<< AzInt.ofInt (-200)) 150 .Floor).1 |> fun y => (setPrecRound y 53 .Floor))

-- huge arguments: next to `π/2`, at a cost independent of the exponent
#guard D (A ((X "1" 53) <<< AzInt.ofInt 1000) 53) == ("1.5707963267948966", .lt)
#guard D (A ((X "1" 53) <<< AzInt.ofInt 1000) 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (-((X "1" 53) <<< AzInt.ofInt 1000)) 53 .Floor) == ("-1.5707963267948968", .lt)
#guard A ((X "1" 53) <<< AzInt.ofInt (2 ^ 30 : Int)) 53
  == (X "1.5707963267948966" 53, .lt)
