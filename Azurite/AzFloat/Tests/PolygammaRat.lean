/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzRat.Instances

/-!
# Tests for the polygamma functions of a rational

The special values (`0`, the negative integers for odd and even `n`, `p = 0`), positive
arguments (`ψ′(1) = π²/6`, `ψ′(1/4) = π² + 8 G`, `ψ′(1/3)`), negative arguments on both
paths (the recurrence, and three positive arguments for `q ≈ −10¹⁸/3`), large `n`, tiny and
huge arguments, the tiny-argument path, other precisions, `n = 0` (the digamma function),
`trigammaRat`, and agreement with the float function on dyadic arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (n : Nat) (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  polygammaRatPrecRound n (Q x) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P 1 "0" 53) == ("Infinity", .eq)
#guard D (P 2 "0" 53) == ("-Infinity", .eq)
#guard D (P 3 "0" 0) == ("Infinity", .eq)
#guard D (P 1 "-1" 53) == ("Infinity", .eq)
#guard D (P 2 "-7" 53) == ("NaN", .eq)
#guard D (P 1 "1/3" 0) == ("NaN", .eq)

-- positive arguments
#guard D (P 1 "1" 53) == ("1.6449340668482264", .lt)
#guard D (P 1 "1/3" 53) == ("10.095597125427094", .gt)
#guard D (P 1 "1/3" 53 .Floor) == ("10.095597125427092", .lt)
#guard D (P 1 "1/3" 53 .Ceiling) == ("10.095597125427094", .gt)
#guard D (P 1 "1/4" 53) == ("17.19732915450711", .lt)
#guard D (P 2 "1/3" 53) == ("-55.122122399401604", .gt)
#guard D (P 2 "1" 53) == ("-2.4041138063191885", .gt)
#guard D (P 3 "2/3" 53) == ("31.33133563753209", .lt)
#guard D (P 5 "22/7" 53) == ("0.15877665094811477", .lt)
#guard D (P 1 "1000/3" 53) == ("0.0030045044999919", .gt)

-- negative arguments: the recurrence, and three positive arguments
#guard D (P 1 "-1/2" 53) == ("8.934802200544679", .lt)
#guard D (P 2 "-1/2" 53) == ("-0.82879664423432", .gt)
#guard D (P 1 "-1/3" 53) == ("12.063875409358717", .lt)
#guard D (P 2 "-7/3" 53) == ("47.616347837435065", .lt)
#guard D (P 2 "-7/3" 53 .Up) == ("47.61634783743507", .gt)
#guard D (P 3 "-301/3" 53) == ("519.5151502306204", .gt)
#guard D (P 4 "-3/2" 53) == ("-0.3137559995067314", .lt)
#guard D (P 1 "-1000000000000000001/3" 53) == ("13.159472534785811", .lt)
#guard D (P 2 "-1000000000000000001/3" 53) == ("-47.73728583450431", .lt)

-- large `n`
#guard D (P 10 "1/3" 53) == ("-642831187194.7932", .gt)
#guard D (P 100 "1/3" 53) == ("-1.4429470060440445e206", .lt)
#guard D (P 100 "-201/2" 53) == ("-3.3121910883047074e-45", .gt)

-- tiny and huge arguments
#guard D (P 1 "1/10000000000" 53) == ("1.0e20", .lt)
#guard D (P 2 "-1/10000000000" 53) == ("2.0e30", .gt)
#guard D (P 1 "1/1267650600228229401496703205376" 53) == ("1.6069380442589903e60", .lt)
#guard D (P 2 "-1/1267650600228229401496703205376" 53 .Floor) == ("4.0740719526689717e90", .lt)
#guard D (P 3 "1/3000000000000000000000000000000" 53) == ("4.86e122", .gt)
#guard D (P 1 "1000000000000000000000000000001/3" 53) == ("3.0e-30", .lt)
private def tiny (n : Nat) (s : String) : Bool :=
  (polygammaRatTiny? n (Q s) (gammaRatExp (Q s)) 53 .Nearest).isSome
#guard tiny 3 "1/3000000000000000000000000000000"
#guard !tiny 1 "1/10000000000"

-- other precisions
#guard D (P 1 "1/3" 200) == ("10.09559712542709408179200409989251636051890411928097814194168", .gt)
#guard D (P 2 "1/3" 200) == ("-55.12212239940160755245575595481501856908419062602976216572894", .lt)
#guard D (P 1 "1/3" 1) == ("8.0", .lt)

-- `n = 0`: the digamma function
#guard D (P 0 "1/3" 53) == ("-3.1320337800208065", .lt)
#guard polygammaRatPrecRound 0 (Q "13/4") 80 .Floor == digammaRatPrecRound (Q "13/4") 80 .Floor

-- `trigammaRat`, `polygammaRat`
#guard trigammaRatPrecRound (Q "1/3") 53 .Up == polygammaRatPrecRound 1 (Q "1/3") 53 .Up
#guard toString (trigammaRat (Q "1/3") 53) == "10.095597125427094"
#guard toString (polygammaRat 2 (Q "1/3") 53) == "-55.122122399401604"

-- agreement with the float function on dyadic arguments
#guard polygammaRatPrecRound 2 (Q "-9/4") 53 .Up == polygammaPrecRound 2 (X "-2.25" 53) 53 .Up
#guard polygammaRatPrecRound 5 (Q "1/4") 100 .Floor
  == polygammaPrecRound 5 (X "0.25" 53) 100 .Floor
#guard polygammaRatPrecRound 1 (Q "-201/2") 53 .Nearest
  == polygammaPrecRound 1 (X "-100.5" 53) 53 .Nearest

-- the fuel as an argument; for an odd `n` no fuel is needed at the positive integers and at
-- the denominator `2`
#guard D (polygammaRatPrecRoundFuel 0 1 (Q "1/2") 53 .Nearest) == ("4.934802200544679", .lt)
#guard D (polygammaRatPrecRoundFuel 0 3 (Q "5") 53 .Nearest) == ("0.021427828192755075", .gt)
#guard D (polygammaRatPrecRoundFuel 0 1 (Q "-7/2") 53 .Nearest) == ("9.620879298050347", .lt)
#guard D (polygammaRatPrecRoundFuel 3 1 (Q "1/3") 53 .Nearest) == ("10.095597125427094", .gt)
#guard polygammaRatPrecRoundFuel (lnGammaFuel 53) 2 (Q "1/3") 53 .Nearest == P 2 "1/3" 53
