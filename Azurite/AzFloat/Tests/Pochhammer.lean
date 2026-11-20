/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pochhammer
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for Pochhammer's symbol

The special values (`NaN`, `(x)₀ = 1`, the infinities, the exact zeros where a factor
vanishes, `p = 0`), small `n` through the exact path (`(1)ₙ = n!`, `(1/2)₃ = 15/8`,
`(−5/2)₄ = −15/16`, `(−5)₃ = −60`), `n = 128` and `129` on either side of its bound, larger `n`
through the loop — positive, negative and sign-straddling arguments — checked against exact
factorials (`(1)ₙ = n!`, `(1/2)ₙ = (2n)!/(4ⁿ n!)`, `(−250)₂₀₀ = 250!/50!`,
`(−1001/2)₁₀₀₀ = −(1001!!)(997!!)/2¹⁰⁰⁰`), `n = 20000`, other
precisions, and 200- and 1000-bit values.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (x : String) (n p : Nat) (m : RoundingMode := .Nearest) :=
  pochhammerPrecRound (X x 53) n p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (pochhammerPrecRound nan 3 53 .Nearest) == ("NaN", .eq)
#guard D (pochhammerPrecRound nan 0 53 .Nearest) == ("NaN", .eq)
#guard D (P "2.5" 0 53) == ("1.0", .eq)
#guard D (P "0" 0 53) == ("1.0", .eq)
#guard D (P "-3" 0 53) == ("1.0", .eq)
#guard D (P "2.5" 0 0) == ("NaN", .eq)
#guard D (pochhammerPrecRound (infinity true) 0 53 .Nearest) == ("1.0", .eq)
#guard D (pochhammerPrecRound (infinity false) 0 53 .Nearest) == ("1.0", .eq)
#guard D (pochhammerPrecRound (infinity true) 3 53 .Nearest) == ("Infinity", .eq)
#guard D (pochhammerPrecRound (infinity false) 3 53 .Nearest) == ("-Infinity", .eq)
#guard D (pochhammerPrecRound (infinity false) 4 53 .Nearest) == ("Infinity", .eq)
#guard D (pochhammerPrecRound (infinity false) 4 0 .Nearest) == ("Infinity", .eq)
#guard D (P "0" 1 53) == ("0.0", .eq)
#guard D (P "0" 5 0) == ("0.0", .eq)
#guard D (P "-2" 3 53) == ("0.0", .eq)
#guard D (P "-2" 1000000 53) == ("0.0", .eq)
#guard D (P "-5" 6 53) == ("0.0", .eq)
#guard D (P "1" 5 0) == ("NaN", .eq)

-- small `n`: the exact path
#guard D (P "1" 5 53) == ("1.2e2", .eq)
#guard D (P "1" 20 53) == ("2.43290200817664e18", .eq)
#guard D (P "1" 30 53) == ("2.6525285981219107e32", .gt)
#guard D (P "1" 30 53 .Floor) == ("2.6525285981219103e32", .lt)
#guard D (P "0.5" 3 53) == ("1.875", .eq)
#guard D (P "0.1" 4 53) == ("0.7161000000000001", .gt)
#guard D (P "0.1" 4 53 .Ceiling) == ("0.7161000000000001", .gt)
#guard D (P "3.141592653589793" 10 53) == ("299606572.3661012", .lt)
#guard D (P "-2.5" 2 53) == ("3.75", .eq)
#guard D (P "-2.5" 4 53) == ("-0.9375", .eq)
#guard D (P "-5" 3 53) == ("-6.0e1", .eq)
#guard D (P "-5" 5 53) == ("-1.2e2", .eq)
#guard D (P "-0.3" 7 53 .Floor) == ("-95.54465970000001", .lt)
#guard D (P "1e-30" 3 53) == ("2.0e-30", .lt)
#guard D (P "1e30" 3 53) == ("1.0000000000000001e90", .gt)
#guard D (P "-1e30" 3 53) == ("-1.0000000000000001e90", .lt)

-- `n = 128` and `129`, either side of the bound for long arguments
#guard D (P "1" 128 53) == ("3.856204823625804e215", .lt)
#guard D (P "1" 129 53) == ("4.974504222477287e217", .gt)
#guard D (P "0.5" 128 53) == ("1.921126920444879e214", .gt)
#guard D (P "0.5" 129 53) == ("2.4686480927716693e216", .gt)
#guard D (P "0.5" 129 53 .Floor) == ("2.468648092771669e216", .lt)
#guard D (P "0.5" 129 53 .Ceiling) == ("2.4686480927716693e216", .gt)

-- larger `n`: positive, negative and sign-straddling arguments
#guard D (P "0.5" 200 53) == ("3.1443238660087782e373", .lt)
#guard D (P "-0.5" 200 53) == ("-7.88051094237789e370", .gt)
#guard D (P "-100.5" 200 53) == ("-2.793281378035082e313", .gt)
#guard D (P "-100.5" 200 53 .Up) == ("-2.7932813780350825e313", .lt)
#guard D (P "-300.5" 200 53) == ("5.666032824771262e456", .gt)
#guard D (P "-250" 200 53) == ("1.0629467857114953e428", .lt)
#guard D (P "1" 171 53) == ("1.2410180702176678e309", .lt)

-- against exact factorials: `(1)ₙ = n!`, `(1/2)ₙ = (2n)!/(4ⁿ n!)`, `(−250)₂₀₀ = 250!/50!`
private def fact (n : Nat) : AzFloat := ofAzNat (AzNat.factorial n)
#guard P "1" 200 53 == setPrecRound (fact 200) 53 .Nearest
#guard P "1" 200 53 .Floor == setPrecRound (fact 200) 53 .Floor
#guard P "1" 1000 100 .Ceiling == setPrecRound (fact 1000) 100 .Ceiling
#guard P "1" 20000 53 == setPrecRound (fact 20000) 53 .Nearest
#guard P "0.5" 200 53 == divPrecRound (fact 400) (fact 200 <<< AzInt.ofInt 400) 53 .Nearest
#guard P "0.5" 200 53 .Up == divPrecRound (fact 400) (fact 200 <<< AzInt.ofInt 400) 53 .Up
#guard P "0.5" 3000 80 .Floor
  == divPrecRound (fact 6000) (fact 3000 <<< AzInt.ofInt 6000) 80 .Floor
#guard P "-250" 200 53 == divPrecRound (fact 250) (fact 50) 53 .Nearest
#guard P "-250" 200 53 .Down == divPrecRound (fact 250) (fact 50) 53 .Down
#guard P "-250" 201 53 .Floor == (-(divPrecRound (fact 250) (fact 49) 53 .Ceiling).1, .lt)
-- the loop where the exact product is refused: `(−1001/2)₁₀₀₀ = −(1001!!)(997!!)/2¹⁰⁰⁰`
private def dfact (n : Nat) : AzNat :=
  (List.range n).foldl (fun acc j => acc * AzNat.ofNat (2 * j + 1)) 1
private def ref (m : RoundingMode) : AzFloat :=
  (divPrecRound (ofAzNat (dfact 501 * dfact 499)) (powerOf2 (AzInt.ofInt 1000)) 53 m).1
#guard (P "-500.5" 1000 53).1 == -ref .Nearest
#guard (P "-500.5" 1000 53 .Floor).1 == -ref .Ceiling
#guard (P "-500.5" 1000 53 .Down).1 == -ref .Floor

-- other precisions
#guard D (P "0.5" 300 1) == ("8.0e612", .lt)
#guard D (P "0.5" 300 20) == ("9.96521e612", .lt)
#guard D (P "0.5" 300 200)
  == ("9.96521158232201117390153204506059285653971266748397774673537e612", .lt)
#guard D (P "-100.5" 200 200 .Floor)
  == ("-2.79328137803508203496951318586662228357006059416887910085368e313", .lt)
#guard D (P "0.25" 1000 1000) == ("6.2405436980660171504467857400702233670145851454649099926211245\
  738319994041470195220951316686598146233448463453943236694801340854880510454042709847318661214469\
    1709264854836947930412429912802068860154132489096966708102232037055648592469710428042452668458\
    8156763358896401674107303635356370017897790452149e2564", .lt)

-- `pochhammer`
#guard toString (pochhammer (X "0.5" 53) 3) == "1.875"
#guard toString (pochhammer (X "1" 53) 30) == "2.6525285981219107e32"

-- the fuel as an argument
#guard D (pochhammerPrecRoundFuel 3 (X "0.3" 53) 200 53 .Nearest)
  == ("6.457145019614471e372", .lt)
#guard D (pochhammerPrecRoundFuel 0 (X "-2" 53) 5 53 .Nearest) == ("0.0", .eq)
#guard pochhammerPrecRoundFuel (gammaFuel 53) (X "0.3" 53) 200 53 .Nearest == P "0.3" 200 53
