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
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := expRatPrecRound (Q q) p m

-- special values
#guard D (E "0" 53) == ("1.0", .eq)
#guard D (E "0" 1) == ("1.0", .eq)
#guard D (E "0" 0) == ("NaN", .eq)
#guard D (E "1" 0) == ("NaN", .eq)
#guard toString (expRat (Q "0") 53) == "1.0"

-- agreement with the float `exp` on exactly representable rationals
#guard E "1" 150 == expPrecRound (X "1" 53) 150 .Nearest
#guard E "-1" 150 == expPrecRound (X "-1" 53) 150 .Nearest
#guard E "1/2" 100 .Floor == expPrecRound (X "0.5" 53) 100 .Floor
#guard E "3" 100 .Ceiling == expPrecRound (X "3" 53) 100 .Ceiling
#guard E "100" 150 == expPrecRound (X "100" 53) 150 .Nearest
#guard E "-100" 150 == expPrecRound (X "-100" 53) 150 .Nearest
#guard E "1/1152921504606846976" 70 == expPrecRound (X "8.673617379884035e-19" 53) 70 .Nearest
#guard expRat (Q "7/4") 53 == exp (X "1.75" 53)

-- non-dyadic rationals
private def refE13 : AzRat :=
  R "139561242508608952862812531960258683759790651519940698261751670603173901564595184696978882" 89
private def refE227 : AzRat :=
  R "231699722982624802308175137957686298094618385884635485108445694535344153377701137626998091" 88
private def refEm73 : AzRat :=
  R "969719678644050628099066592983707314807208589248043936530471041083254240877796035344699129" 91
private def refEm15 : AzRat :=
  R "818730753077981858669935508619039424358591256269015672478028761616508777402491098623457204" 90
#guard toString ((E "1/3" 150).1) == "1.395612425086089528628125319602586837597906515"
#guard D (E "1/3" 150 .Floor) == ("1.395612425086089528628125319602586837597906515", .lt)
#guard D (E "1/3" 150 .Ceiling) == ("1.395612425086089528628125319602586837597906516", .gt)
#guard D (E "1/3" 53) == ("1.3956124250860895", .lt)
#guard toString ((E "22/7" 150).1) == "23.1699722982624802308175137957686298094618386"
#guard D (E "22/7" 150 .Down) == ("23.16997229826248023081751379576862980946183857", .lt)
#guard toString ((E "-7/3" 150).1) == "0.0969719678644050628099066592983707314807208589"
#guard D (E "-7/3" 150 .Up) == ("0.096971967864405062809906659298370731480720859", .gt)
#guard toString ((E "-1/5" 150).1) == "0.818730753077981858669935508619039424358591256"
#guard D (E "-1/5" 100 .Floor) == ("0.818730753077981858669935508619", .lt)
#guard toString (expRat (Q "1/3") 53) == "1.3956124250860895"
#guard toString (expRat (Q "22/7") 200)
  == "23.16997229826248023081751379576862980946183858846354851084456"

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
#guard toString ((expPrecRound (lnRat (Q "1/3") 200) 100 .Nearest).1)
  == "0.3333333333333333333333333333335"
#guard toString ((expPrecRound (lnRat (Q "22/7") 200) 100 .Nearest).1)
  == "3.14285714285714285714285714286"

-- a tiny rational argument (`±1/(3·2^1000)`): the value is `1 ± tiny`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (expRatPrecRound tinyQ 53 .Nearest) == ("1.0", .lt)
#guard D (expRatPrecRound tinyQ 53 .Floor) == ("1.0", .lt)
#guard D (expRatPrecRound tinyQ 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (expRatPrecRound (-tinyQ) 53 .Nearest) == ("1.0", .gt)
#guard D (expRatPrecRound (-tinyQ) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (expRatPrecRound (-tinyQ) 53 .Ceiling) == ("1.0", .gt)
