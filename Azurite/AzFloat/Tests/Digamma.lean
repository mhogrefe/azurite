/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Digamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for the digamma function

The special values (`NaN`, `±∞`, `ψ(0) = −∞`, the poles `−1, −2, …`, `p = 0`), `ψ` at positive
arguments (`ψ(1) = −γ` in the five modes, `ψ(1/2) = −γ − 2 ln 2`,
`ψ(1/4) = −γ − π/2 − 3 ln 2`), on either side of the zero `1.4616…`, large arguments
(`ψ(x) ≈ ln x`), negative arguments through the reflection formula (next to the poles `−1`,
at a half-integer, next to the zero `−0.504…`), tiny arguments (`ψ(x) ≈ −1/x − γ`, down to
`2^(−2^30)`), other precisions, and 200- and 1000-bit values.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  digammaPrecRound (X x 53) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (digammaPrecRound nan 53 .Nearest) == ("NaN", .eq)
#guard D (digammaPrecRound (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (digammaPrecRound (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard D (digammaPrecRound zero 53 .Nearest) == ("-Infinity", .eq)
#guard D (digammaPrecRound zero 0 .Nearest) == ("-Infinity", .eq)
#guard D (W "-1" 53) == ("NaN", .eq)
#guard D (W "-2" 53) == ("NaN", .eq)
#guard D (W "-1000000" 53) == ("NaN", .eq)
#guard D (W "1" 0) == ("NaN", .eq)
#guard D (W "-0.5" 0) == ("NaN", .eq)

-- positive arguments
#guard D (W "1" 53) == ("-0.5772156649015329", .lt)
#guard D (W "1" 53 .Floor) == ("-0.5772156649015329", .lt)
#guard D (W "1" 53 .Ceiling) == ("-0.5772156649015328", .gt)
#guard D (W "1" 53 .Up) == ("-0.5772156649015329", .lt)
#guard D (W "1" 53 .Down) == ("-0.5772156649015328", .gt)
#guard D (W "2" 53) == ("0.42278433509846713", .lt)
#guard D (W "0.5" 53) == ("-1.9635100260214235", .lt)
#guard D (W "0.25" 53) == ("-4.2274535333762655", .lt)
#guard D (W "1.5" 53) == ("0.03648997397857652", .lt)
#guard D (W "3.141592653589793" 53) == ("0.9772133079420067", .lt)
#guard D (W "10" 53) == ("2.251752589066721", .lt)
#guard D (W "10" 53 .Floor) == ("2.251752589066721", .lt)
#guard D (W "100" 53) == ("4.600161852738087", .lt)
#guard D (W "100" 53 .Ceiling) == ("4.600161852738088", .gt)

-- on either side of the zero `1.4616321449683623…`
#guard D (W "1.4616321449683623" 53) == ("-9.241265521729427e-17", .gt)
#guard D (W "1.4616321449683625" 53) == ("1.2245374622004068e-16", .lt)
#guard D (W "1.4616321449683623" 53 .Floor) == ("-9.241265521729428e-17", .lt)

-- large arguments: `ψ(x) ≈ ln x − 1/(2x)`
#guard D (W "1e30" 53) == ("69.07755278982137", .lt)
#guard D (W "1e30" 53 .Floor) == ("69.07755278982137", .lt)
#guard D (W "1e300" 53) == ("690.7755278982137", .lt)
#guard D (W "123456789" 53) == ("18.631401762118017", .lt)
private def hugeX : AzFloat := (X "3" 53) <<< AzInt.ofInt (2 ^ 20)
#guard (digammaPrecRound hugeX 53 .Nearest).1 == (lnPrecRound hugeX 53 .Nearest).1
#guard (digammaPrecRound hugeX 53 .Nearest).2 == (lnPrecRound hugeX 53 .Nearest).2

-- negative arguments
#guard D (W "-0.5" 53) == ("0.03648997397857652", .lt)
#guard D (W "-0.5" 53 .Floor) == ("0.03648997397857652", .lt)
#guard D (W "-0.5" 53 .Ceiling) == ("0.03648997397857653", .gt)
#guard D (W "-1.5" 53) == ("0.7031566406452432", .gt)
#guard D (W "-2.25" 53) == ("4.158583564657972", .lt)
#guard D (W "-2.25" 53 .Down) == ("4.158583564657972", .lt)
#guard D (W "-0.999999" 53) == ("-999999.5771842643", .lt)
#guard D (W "-1.000001" 53) == ("1000000.4228639568", .lt)
#guard D (W "-100.3" 53) == ("6.895643124860435", .lt)
#guard D (W "-100.3" 53 .Up) == ("6.8956431248604355", .gt)
#guard D (W "-1000000.5" 53) == ("13.815511557963816", .gt)
#guard D (W "-0.504083008264455" 53) == ("4.042965717222496e-15", .lt)
#guard D (W "-123456789.25" 53) == ("21.77299442583281", .lt)

-- tiny arguments: `ψ(x) ≈ −1/x − γ`
#guard D (W "1e-10" 53) == ("-10000000000.577215", .gt)
#guard D (W "-1e-10" 53) == ("9999999999.422785", .gt)
#guard D (W "1e-40" 53) == ("-1.0e40", .gt)
#guard D (W "1e-40" 53 .Floor) == ("-1.0000000000000002e40", .lt)
#guard D (W "-1e-40" 53) == ("1.0e40", .lt)
#guard D (W "-1e-40" 53 .Ceiling) == ("1.0000000000000002e40", .gt)
#guard D (W "1e-300" 53) == ("-9.999999999999999e299", .gt)
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt (-(2 ^ 30))
private def invTinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt (2 ^ 30)
#guard digammaPrecRound tinyX 53 .Nearest == (-invTinyX, .gt)
#guard digammaPrecRound tinyX 53 .Ceiling == (-invTinyX, .gt)
#guard (digammaPrecRound tinyX 53 .Floor).2 == .lt
#guard digammaPrecRound (-tinyX) 53 .Nearest == (invTinyX, .gt)
#guard (digammaPrecRound (-tinyX) 53 .Floor).2 == .lt

-- other precisions
#guard D (W "2" 1) == ("0.5", .gt)
#guard D (W "2" 2) == ("0.4", .lt)
#guard D (W "2" 20) == ("0.4227843", .lt)
#guard D (W "-3.5" 24) == ("1.388871", .gt)
#guard D (digammaPrecRound (X "1" 53) 200 .Nearest)
  == ("-0.577215664901532860606512090082402431042159335939923598805767", .gt)
#guard D (digammaPrecRound (X "0.5" 53) 200 .Floor)
  == ("-1.963510026021423479440976332998755567193159604660434107047128", .lt)
#guard D (digammaPrecRound (X "-2.25" 53) 200 .Nearest)
  == ("4.15858356465797227481755768162726375127436940511130799376411", .lt)
#guard D (digammaPrecRound (X "100" 53) 200 .Nearest)
  == ("4.60016185273808740019860558557585072686681279076852805437077", .gt)
#guard D (digammaPrecRound (X "0.1" 200) 53 .Nearest) == ("-10.423754940411078", .lt)
#guard D (digammaPrecRound (X "0.25" 53) 1000 .Nearest) == ("-4.2274535333762654080895301460966835\
  773672444387082422716552795595189567958298533170685544569520613461317099335681602930055639870265\
    3622562318486595661439198077082509757902090386137488097574475612565594856923418564684975534298\
    90206183011156704093048811352668799064572003142484460725661083066793061233775", .lt)
#guard D (digammaPrecRound (X "-0.75" 53) 1000 .Nearest) == ("-2.894120200042932074756196812763350\
  244033911105374908938321946226185623462496519983735221123618728012798376600234826959672230653693\
    2028922898515326232810586474374917642456875705280415476424114227923226152359008523135164220096\
    55687284967782337075971547801933546573123866980915112739232774973345972790044", .lt)

-- `digamma`
#guard toString (digamma (X "1" 53)) == "-0.5772156649015329"
#guard toString (digamma (X "-0.5" 53)) == "0.03648997397857652"

-- the fuel as an argument
#guard D (digammaPrecRoundFuel 3 (X "1" 53) 53 .Nearest) == ("-0.5772156649015329", .lt)
#guard D (digammaPrecRoundFuel 3 (X "-2.5" 53) 53 .Nearest) == ("1.103156640645243", .lt)
#guard D (digammaPrecRoundFuel 0 (X "0" 53) 53 .Nearest) == ("-Infinity", .eq)
#guard digammaPrecRoundFuel (lnGammaFuel 53) (X "0.3" 53) 53 .Nearest == W "0.3" 53
