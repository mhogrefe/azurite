/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzFloat.WrightOmega

/-!
# Tests for the Wright `ω` function

The special values (`NaN`, `±∞`, `p = 0`, the exact value `ω(1) = 1` at several precisions of
the argument), `ω` at moderate arguments in the five modes (`ω(0)` is the omega constant
`0.56714…`), next to `1` and next to `0`, very negative arguments (`ω(x) ≈ eˣ`), large
arguments (`ω(x) ≈ x − ln x`; `10³⁰` through the loop and `10³⁰⁰`, `3·2^(2^40)` through the
large-argument path), other precisions, 200- and 1000-bit values, and agreement with
`W₀(eˣ)` and with `eˣ`.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  wrightOmegaPrecRound (X x 53) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (wrightOmegaPrecRound nan 53 .Nearest) == ("NaN", .eq)
#guard D (wrightOmegaPrecRound (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (wrightOmegaPrecRound (infinity false) 53 .Nearest) == ("0.0", .eq)
#guard D (wrightOmegaPrecRound (infinity true) 0 .Nearest) == ("Infinity", .eq)
#guard D (wrightOmegaPrecRound (infinity false) 0 .Nearest) == ("0.0", .eq)
#guard D (W "0" 0) == ("NaN", .eq)
#guard D (W "1" 0) == ("NaN", .eq)
#guard D (W "2" 0) == ("NaN", .eq)

-- `ω(1) = 1`, the only exact value
#guard D (W "1" 53) == ("1.0", .eq)
#guard D (W "1" 53 .Floor) == ("1.0", .eq)
#guard D (W "1" 1 .Ceiling) == ("1.0", .eq)
#guard D (wrightOmegaPrecRound (X "1" 1) 200 .Up) == ("1.0", .eq)
#guard D (wrightOmegaPrecRound (X "1" 1000) 10 .Down) == ("1.0", .eq)

-- moderate arguments
#guard D (W "0" 53) == ("0.5671432904097838", .lt)
#guard D (W "0" 53 .Floor) == ("0.5671432904097838", .lt)
#guard D (W "0" 53 .Ceiling) == ("0.567143290409784", .gt)
#guard D (W "0.5" 53) == ("0.7662486081617502", .lt)
#guard D (W "2" 53) == ("1.5571455989976115", .gt)
#guard D (W "2" 53 .Floor) == ("1.5571455989976113", .lt)
#guard D (W "2" 53 .Ceiling) == ("1.5571455989976115", .gt)
#guard D (W "2" 53 .Up) == ("1.5571455989976115", .gt)
#guard D (W "2" 53 .Down) == ("1.5571455989976113", .lt)
#guard D (W "-1" 53) == ("0.2784645427610738", .gt)
#guard D (W "-1" 53 .Floor) == ("0.27846454276107374", .lt)
#guard D (W "-10" 53) == ("0.00004539786874921543", .lt)
#guard D (W "-10" 53 .Ceiling) == ("0.000045397868749215435", .gt)
#guard D (W "3.141592653589793" 53) == ("2.3060545683741136", .lt)
#guard D (W "100" 53) == ("95.44148664557584", .gt)
#guard D (W "100" 53 .Floor) == ("95.44148664557582", .lt)

-- next to `1` and next to `0`
#guard D (W "1.0000000000000002" 53) == ("1.0000000000000002", .gt)
#guard D (W "0.9999999999999999" 53) == ("1.0", .gt)
#guard D (W "1e-30" 53) == ("0.5671432904097838", .lt)
#guard D (W "-1e-30" 53) == ("0.5671432904097838", .lt)

-- very negative arguments: `ω(x) ≈ eˣ`
#guard D (W "-800" 53) == ("3.6678745841776874e-348", .gt)
#guard D (W "-800" 53 .Floor) == ("3.667874584177687e-348", .lt)
#guard D (W "-100000" 53) == ("3.5629495653093734e-43430", .gt)
#guard (W "-100000" 53).1 == (expPrecRound (X "-100000" 53) 53 .Nearest).1
private def negHuge : AzFloat := -((X "1" 53) <<< AzInt.ofInt 40)
#guard wrightOmegaPrecRound negHuge 53 .Nearest == expPrecRound negHuge 53 .Nearest
#guard wrightOmegaPrecRound negHuge 53 .Floor == expPrecRound negHuge 53 .Floor

-- large arguments: `ω(x) ≈ x − ln x`
#guard D (W "1e30" 53) == ("1.0e30", .gt)
#guard D (W "1e30" 53 .Floor) == ("9.999999999999999e29", .lt)
#guard D (W "1e30" 53 .Ceiling) == ("1.0e30", .gt)
#guard D (W "1e300" 53) == ("1.0e300", .gt)
#guard D (W "1e300" 53 .Floor) == ("9.999999999999999e299", .lt)
#guard D (W "1e300" 53 .Ceiling) == ("1.0e300", .gt)
#guard D (W "123456789" 53) == ("123456770.36859839", .gt)
#guard D (W "123456789" 53 .Floor) == ("123456770.36859837", .lt)
private def hugeX : AzFloat := (X "3" 53) <<< AzInt.ofInt (2 ^ 40)
private def belowHugeX : AzFloat := (X "2.9999999999999996" 53) <<< AzInt.ofInt (2 ^ 40)
#guard wrightOmegaPrecRound hugeX 53 .Nearest == (hugeX, .gt)
#guard wrightOmegaPrecRound hugeX 53 .Ceiling == (hugeX, .gt)
#guard wrightOmegaPrecRound hugeX 53 .Floor == (belowHugeX, .lt)

-- other precisions
#guard D (W "2" 1) == ("2.0", .gt)
#guard D (W "2" 2) == ("1.5", .lt)
#guard D (W "2" 20) == ("1.557146", .gt)
#guard D (W "-3.5" 24) == ("0.029324712", .gt)
#guard D (wrightOmegaPrecRound (X "0" 53) 200 .Nearest)
  == ("0.567143290409783872999968662210355549753815787186512508135131", .gt)
#guard D (wrightOmegaPrecRound (X "2" 53) 200 .Nearest)
  == ("1.557145598997611416858672000000663180283737870626520315282267", .gt)
#guard D (wrightOmegaPrecRound (X "-10" 53) 200 .Floor)
  == ("0.0000453978687492154295701480425671995323557485808290619841007793", .lt)
#guard D (wrightOmegaPrecRound (X "1e30" 53) 200 .Nearest)
  == ("1000000000000000019884624838586.922447210178629459575631520882", .gt)
#guard D (wrightOmegaPrecRound (X "0.1" 200) 53 .Nearest) == ("0.6040681900258921", .lt)
#guard D (wrightOmegaPrecRound (X "1.5" 53) 1000 .Nearest) == ("1.26495972012550054196836718671532\
  391096576593841007107693007910326824557790882044602256479655813950800839935114908572078634551983\
    9405937292723863936367991788592109829828719702255660751823675619801906154273575177438697828917\
    4536867728861440224422355155039703890553960300370873300223570367183135710985002", .lt)

-- agreement with `W₀(eˣ)`
private def viaW0 (x : String) (p : Nat) (m : RoundingMode) :=
  lambertW0PrecRound (expPrecRound (X x 53) (p + 200) .Nearest).1 p m
#guard W "2" 53 == viaW0 "2" 53 .Nearest
#guard W "-10" 53 .Floor == viaW0 "-10" 53 .Floor
#guard W "100" 100 .Ceiling == viaW0 "100" 100 .Ceiling
#guard W "0.3" 300 == viaW0 "0.3" 300 .Nearest

-- `wrightOmegaFloat`
#guard toString (wrightOmegaFloat (X "2" 53)) == "1.5571455989976115"
#guard toString (wrightOmegaFloat (X "1" 53)) == "1.0"
#guard toString (wrightOmegaFloat (X "0" 53)) == "0.5"
