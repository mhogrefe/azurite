/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzFloat.WrightOmega
import Azurite.AzRat.Parse

/-!
# Tests for the Wright `ω` function of a rational

The special values (`p = 0`, the exact value `ω(1) = 1`), `ω` at exact rationals (`0`, `1/3`,
`22/7`, `−7/3`, `±1/10`, `10¹²`, `1 ± 10⁻³⁰`, `−2500/3` where `ω ≈ e^q`, and `(10⁴² + 1)/3`,
`(10⁴⁰⁰ + 1)/3` where `ω ≈ q − ln q`), other precisions, 200- and 1000-bit values, and
agreement with the float version on exactly representable arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  wrightOmegaRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W "0" 0) == ("NaN", .eq)
#guard D (W "1" 0) == ("NaN", .eq)
#guard D (W "1" 53) == ("1.0", .eq)
#guard D (W "1" 53 .Floor) == ("1.0", .eq)
#guard D (W "1" 1 .Up) == ("1.0", .eq)
#guard D (W "-1" 53) == ("0.2784645427610738", .gt)

-- exact rationals
#guard D (W "0" 53) == ("0.5671432904097838", .lt)
#guard D (W "1/3" 53) == ("0.695892876664791", .gt)
#guard D (W "1/3" 53 .Floor) == ("0.6958928766647909", .lt)
#guard D (W "1/3" 53 .Ceiling) == ("0.695892876664791", .gt)
#guard D (W "22/7" 53) == ("2.306936631825424", .gt)
#guard D (W "22/7" 53 .Floor) == ("2.3069366318254234", .lt)
#guard D (W "-7/3" 53) == ("0.08873765260048497", .gt)
#guard D (W "-7/3" 53 .Ceiling) == ("0.08873765260048497", .gt)
#guard D (W "-1/10" 53) == ("0.5316916197790177", .gt)
#guard D (W "1/10" 53) == ("0.6040681900258921", .lt)
#guard D (W "1000000000000" 53) == ("999999999972.369", .gt)
#guard D (W "1000000000000" 53 .Floor) == ("999999999972.3689", .lt)
#guard D (W "1000000000000000000000000000001/1000000000000000000000000000000" 53) == ("1.0", .lt)
#guard D (W "999999999999999999999999999999/1000000000000000000000000000000" 53) == ("1.0", .gt)
#guard D (W "-2500/3" 53) == ("1.2244237565560661e-362", .lt)
#guard D (W "-2500/3" 53 .Floor) == ("1.2244237565560661e-362", .lt)

-- large arguments: `ω(q) ≈ q − ln q`
#guard D (W "1000000000000000000000000000000000000000001/3" 53) == ("3.3333333333333332e41", .lt)
#guard D (W "1000000000000000000000000000000000000000001/3" 53 .Ceiling)
  == ("3.3333333333333336e41", .gt)
private def big : AzRat := Q ("1" ++ "".pushn '0' 399 ++ "1/3")
#guard wrightOmegaRatPrecRound big 53 .Nearest == ofAzRatRound big 53 .Nearest
#guard (wrightOmegaRatPrecRound big 53 .Floor).2 == .lt
#guard (wrightOmegaRatPrecRound big 53 .Ceiling).1 == (ofAzRatRound big 53 .Ceiling).1

-- very negative arguments: the bracket from `e^q` (the candidate path ended in the fallback
-- for the first of these)
private def veryNeg : AzRat := Q "-316990021309512686572654174207/15"
#guard wrightOmegaRatPrecRound veryNeg 1 .Nearest == expRatPrecRound veryNeg 1 .Nearest
#guard wrightOmegaRatPrecRound veryNeg 1 .Floor == expRatPrecRound veryNeg 1 .Floor
#guard wrightOmegaRatPrecRound veryNeg 53 .Ceiling == expRatPrecRound veryNeg 53 .Ceiling
#guard W "-100" 53 == expRatPrecRound (Q "-100") 53 .Nearest
#guard W "-5000" 53 .Floor == expRatPrecRound (Q "-5000") 53 .Floor
#guard W "-300" 200 == expRatPrecRound (Q "-300") 200 .Nearest
#guard W "-1500" 1000 .Ceiling == expRatPrecRound (Q "-1500") 1000 .Ceiling

-- other precisions
#guard D (W "1/3" 1) == ("0.5", .lt)
#guard D (W "1/3" 20) == ("0.695893", .gt)
#guard D (W "1/3" 200) == ("0.695892876664791017126023677472673775824745994066263452766847", .lt)
#guard D (W "-7/3" 200 .Floor)
  == ("0.0887376526004849616507085123204429543042984982604024500053304", .lt)
#guard D (W "22/7" 1000) == ("2.306936631825423829251066261612711741402385224440329942091577921187\
  530602094957017340312809361864931239120199188582019142960557661590225388736678804669103312393099\
    8705418871534755308422589559016935917633246830645185118169364133592417674693933638624221889380\
    08203650917281110485672969778319797973813259", .lt)

-- agreement with the float version
#guard W "0" 53 == wrightOmegaPrecRound zero 53 .Nearest
#guard W "1/2" 53 .Floor == wrightOmegaPrecRound (X "0.5" 53) 53 .Floor
#guard W "-7/4" 100 .Ceiling == wrightOmegaPrecRound (X "-1.75" 53) 100 .Ceiling
#guard W "1099511627776" 64 == wrightOmegaPrecRound (X "1099511627776" 53) 64 .Nearest

-- `wrightOmegaRat`
#guard toString (wrightOmegaRat (Q "1/3") 53) == "0.695892876664791"
