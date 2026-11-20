/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DigammaRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the digamma function of a rational

The special values (`ψ(0) = −∞`, the poles, `p = 0`), `ψ` at positive rationals (`ψ(1) = −γ`,
`ψ(1/3) = −γ − π/(2√3) − (3/2) ln 3`, `2/3`, `22/7`, `1/10`, `10¹²`), negative rationals
through the reflection formula, tiny rationals (`±10⁻³⁰`, `2⁻¹⁰⁰` where `−1/q` is a float, and
`1/(2¹⁰⁰ + 1)`), other precisions, and agreement with the float version on exactly
representable arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  digammaRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W "0" 53) == ("-Infinity", .eq)
#guard D (W "0" 0) == ("-Infinity", .eq)
#guard D (W "-1" 53) == ("NaN", .eq)
#guard D (W "-1000000" 53) == ("NaN", .eq)
#guard D (W "1" 0) == ("NaN", .eq)

-- positive rationals
#guard D (W "1" 53) == ("-0.5772156649015329", .lt)
#guard D (W "1/2" 53) == ("-1.9635100260214235", .lt)
#guard D (W "1/3" 53) == ("-3.1320337800208065", .lt)
#guard D (W "1/3" 53 .Floor) == ("-3.1320337800208065", .lt)
#guard D (W "1/3" 53 .Ceiling) == ("-3.132033780020806", .gt)
#guard D (W "2/3" 53) == ("-1.3182344157865884", .gt)
#guard D (W "22/7" 53) == ("0.9776864244423235", .lt)
#guard D (W "22/7" 53 .Floor) == ("0.9776864244423235", .lt)
#guard D (W "1/10" 53) == ("-10.423754940411078", .lt)
#guard D (W "1000000000000" 53) == ("27.63102111592805", .gt)

-- negative rationals
#guard D (W "-1/2" 53) == ("0.03648997397857652", .lt)
#guard D (W "-7/3" 53) == ("2.86033701278484", .gt)
#guard D (W "-7/3" 53 .Ceiling) == ("2.86033701278484", .gt)
#guard D (W "-1/3" 53) == ("1.6817655842134116", .gt)
#guard D (W "-1001/10" 53) == ("14.279984365171568", .lt)
#guard D (W "-999999/1000000" 53) == ("-999999.57721302", .gt)
#guard D (W "-3000001/3" 53) == ("15.62931075553152", .gt)

-- tiny rationals: `ψ(q) ≈ −1/q − γ`
#guard D (W "1/1000000000000000000000000000000" 53) == ("-1.0e30", .lt)
#guard D (W "1/1000000000000000000000000000000" 53 .Floor) == ("-1.0e30", .lt)
#guard D (W "-1/1000000000000000000000000000000" 53) == ("1.0e30", .gt)
#guard D (W "1/1267650600228229401496703205376" 53) == ("-1.2676506002282294e30", .gt)
#guard D (W "1/1267650600228229401496703205376" 53 .Floor) == ("-1.2676506002282297e30", .lt)
#guard D (W "1/1267650600228229401496703205377" 53) == ("-1.2676506002282294e30", .gt)

-- large rationals, other precisions
#guard D (W "1000000000000000000000000000001/3" 53) == ("67.97894050115326", .lt)
#guard D (W "1/3" 1) == ("-4.0", .lt)
#guard D (W "1/3" 20) == ("-3.132034", .lt)
#guard D (W "1/3" 200) == ("-3.132033780020806322996419074287268854155428296720418064192752", .lt)
#guard D (W "-7/3" 200 .Floor)
  == ("2.860337012784840099026230611926315449557209379943751082805705", .lt)
#guard D (W "22/7" 1000) == ("0.977686424442323468117151363649785618846750431076342514482628427408\
  987909203289700413858472426241267038138000476158881097460753802714922502799543232756811978110771\
    3763851718834992409238419436250501725626411883927553749796881732584965760257043918247478963059\
    74624207010227076604531187125660704890545767", .gt)

-- agreement with the float version
#guard W "1/4" 53 == digammaPrecRound (X "0.25" 53) 53 .Nearest
#guard W "-9/4" 53 .Floor == digammaPrecRound (X "-2.25" 53) 53 .Floor
#guard W "-1/2" 100 .Ceiling == digammaPrecRound (X "-0.5" 53) 100 .Ceiling
#guard W "1099511627776" 64 == digammaPrecRound (X "1099511627776" 53) 64 .Nearest

-- `digammaRat`
#guard toString (digammaRat (Q "1/3") 53) == "-3.1320337800208065"

-- the fuel as an argument
#guard D (digammaRatPrecRoundFuel 3 (Q "1/3") 53 .Nearest) == ("-3.1320337800208065", .lt)
#guard D (digammaRatPrecRoundFuel 3 (Q "-7/2") 53 .Nearest) == ("1.388870926359529", .gt)
#guard digammaRatPrecRoundFuel (lnGammaFuel 53) (Q "22/7") 53 .Nearest == W "22/7" 53
