/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `exp` of a rational

`exp 0 = 1`, agreement with the float `exp` on exactly representable rationals, and the correctly
rounded values of
`e^(1/3) = 1.3956124250860895286281253196025868375979065151994069826175167060317390156…`,
`e^(22/7) = 23.169972298262480230817513795768629809461838588463548510844569453534415337…`,
`e^(−7/3) = 0.096971967864405062809906659298370731480720858924804393653047104108325424…`,
`e^(−1/5) = 0.818730753077981858669935508619039424358591256269015672478028761616508777…`,
`e^(123456.789) = 4.0014389392630817570982471707409674646437583709055439455533924484257…·10^53616`
(references from a 90-digit decimal evaluation), and the directed modes.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := expRatPrecRound (Q q) p m

-- special values
#guard E "0" 53 == (F "1" 53, .eq)
#guard E "0" 1 == (one, .eq)
#guard E "0" 0 == (nan, .eq)
#guard E "1" 0 == (nan, .eq)
#guard expRat (Q "0") 53 == F "1" 53

-- agreement with the float `exp` on exactly representable rationals
#guard E "1" 150 == expPrecRound (F "1" 53) 150 .Nearest
#guard E "-1" 150 == expPrecRound (F "-1" 53) 150 .Nearest
#guard E "1/2" 100 .Floor == expPrecRound (F "1/2" 53) 100 .Floor
#guard E "3" 100 .Ceiling == expPrecRound (F "3" 53) 100 .Ceiling
#guard E "100" 150 == expPrecRound (F "100" 53) 150 .Nearest
#guard E "-100" 150 == expPrecRound (F "-100" 53) 150 .Nearest
#guard E "1/1152921504606846976" 70 == expPrecRound (F "1/1152921504606846976" 53) 70 .Nearest
#guard expRat (Q "7/4") 53 == exp (F "7/4" 53)

-- non-dyadic rationals
private def refE13 : AzRat :=
  R "139561242508608952862812531960258683759790651519940698261751670603173901564595184696978882" 89
private def refE227 : AzRat :=
  R "231699722982624802308175137957686298094618385884635485108445694535344153377701137626998091" 88
private def refEm73 : AzRat :=
  R "969719678644050628099066592983707314807208589248043936530471041083254240877796035344699129" 91
private def refEm15 : AzRat :=
  R "818730753077981858669935508619039424358591256269015672478028761616508777402491098623457204" 90
#guard (E "1/3" 150).1 == ofAzRat refE13 150
#guard E "1/3" 150 .Floor == ofAzRatRound refE13 150 .Floor
#guard E "1/3" 150 .Ceiling == ofAzRatRound refE13 150 .Ceiling
#guard E "1/3" 53 == ofAzRatRound refE13 53 .Nearest
#guard (E "22/7" 150).1 == ofAzRat refE227 150
#guard E "22/7" 150 .Down == ofAzRatRound refE227 150 .Down
#guard (E "-7/3" 150).1 == ofAzRat refEm73 150
#guard E "-7/3" 150 .Up == ofAzRatRound refEm73 150 .Up
#guard (E "-1/5" 150).1 == ofAzRat refEm15 150
#guard E "-1/5" 100 .Floor == ofAzRatRound refEm15 100 .Floor
#guard expRat (Q "1/3") 53 == ofAzRat refE13 53
#guard expRat (Q "22/7") 200 == ofAzRat refE227 200

-- a large argument: `e^(123456.789)`
private def refBig : AzRat :=
  Q ("400143893926308175709824717074096746464375837090554394555339244842573455040744161200357957"
    ++ "".pushn '0' 53527 ++ "/1")
#guard (E "123456789/1000" 100).1 == ofAzRat refBig 100
#guard E "123456789/1000" 100 .Floor == ofAzRatRound refBig 100 .Floor

-- directed modes are ordered
#guard (E "5/7" 60 .Floor).2 == .lt
#guard (E "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E "5/7" 60 .Floor).1 (E "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E "-5/7" 60 .Floor).1 (E "-5/7" 60 .Ceiling).1 == some .lt

-- `exp (ln q)` returns to `q` at a lower precision
#guard (expPrecRound (lnRat (Q "1/3") 200) 100 .Nearest).1 == F "1/3" 100
#guard (expPrecRound (lnRat (Q "22/7") 200) 100 .Nearest).1 == F "22/7" 100
