/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpM1
import Azurite.AzFloat.ExpM1Rat
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `exp q − 1` of a rational

`exp 0 − 1 = 0`, agreement with the float `expM1` on exactly representable rationals and with
`expRat q − 1` at a higher precision, the correctly rounded values of `exp (±1/3) − 1`,
`exp (22/7) − 1`, `exp (−7/3) − 1` and `exp (±1/(3·10^30)) − 1` (references from a 200-digit
decimal evaluation; the small arguments exercise the compensation), the directed modes, and
`expM1Rat (ln q) ≈ q − 1`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (q : String) (p : Nat) (m : RoundingMode := .Nearest) := expM1RatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E "0" 53) == ("0.0", .eq)
#guard D (E "0" 0) == ("NaN", .eq)
#guard D (E "1" 0) == ("NaN", .eq)
#guard toString (expM1Rat (Q "0") 53) == "0.0"

-- agreement with the float `expM1` on exactly representable rationals
#guard E "1" 150 == expM1PrecRound (X "1" 53) 150 .Nearest
#guard E "-1" 150 == expM1PrecRound (X "-1" 53) 150 .Nearest
#guard E "1/2" 100 .Floor == expM1PrecRound (X "0.5" 53) 100 .Floor
#guard E "3" 100 .Ceiling == expM1PrecRound (X "3" 53) 100 .Ceiling
#guard E "100" 150 == expM1PrecRound (X "100" 53) 150 .Nearest
#guard E "-100" 150 == expM1PrecRound (X "-100" 53) 150 .Nearest
#guard E "1/1073741824" 150 == expM1PrecRound (X "0.000000000931322574615478515625" 53) 150 .Nearest
#guard E "-1/1073741824" 150 .Floor
  == expM1PrecRound (X "-0.000000000931322574615478515625" 53) 150 .Floor
#guard E "1/1606938044258990275541962092341162602522202993782792835301376" 53
  == expM1PrecRound (powerOf2 (AzInt.ofInt (-200))) 53 .Nearest
#guard expM1Rat (Q "7/4") 53 == expM1 (X "1.75" 53)

private def refE13 : AzRat :=
  R ("3956124250860895286281253196025868375979065151994069826175167060317390156459518469697888" ++
    "1729583022413521118441041886209612212329277789293930634939417174789249374621227268560348" ++
    "09217995869622609693158") 199
private def refEm13 : AzRat :=
  R ("-283468689426210749574395903074620332546887940178520842859129792872695922765097620891208" ++
    "9110848250538409219003798121701201437060120603129064742262774640120765980067535524534412" ++
    "0092630913949335818698944") 200
private def refE227 : AzRat :=
  R ("2216997229826248023081751379576862980946183858846354851084456945353441533777011376269980" ++
    "8986269432728590324615817461454844900023289397298061149071132939763087521988364969748117" ++
    "463869283809255881914806") 198
private def refEm73 : AzRat :=
  R ("-903028032135594937190093340701629268519279141075195606346952895891674575912220396465530" ++
    "0874312590119468603986767810508342190355320544127340343550832369246506005092193155077183" ++
    "4561267407466767375241232") 200
private def refSmall : AzRat :=
  R ("3333333333333333333333333333333888888888888888888888888888888950617283950617283950617283" ++
    "950622427983539094650205761316872428326474622770919067215363511659827008078036885") 199
private def refSmallNeg : AzRat :=
  R ("-333333333333333333333333333333277777777777777777777777777777783950617283950617283950617" ++
    "28395010288065843621399176954732510291495198902606310013717421124828341716201798506") 200

-- non-dyadic rationals
#guard toString (E "1/3" 150).1 == "0.3956124250860895286281253196025868375979065153"
#guard D (E "1/3" 150 .Floor) == ("0.395612425086089528628125319602586837597906515", .lt)
#guard D (E "1/3" 150 .Ceiling) == ("0.3956124250860895286281253196025868375979065153", .gt)
#guard toString (E "-1/3" 150).1 == "-0.28346868942621074957439590307462033254688794"
#guard D (E "-1/3" 150 .Down) == ("-0.28346868942621074957439590307462033254688794", .gt)
#guard toString (E "22/7" 150).1 == "22.1699722982624802308175137957686298094618386"
#guard D (E "22/7" 100 .Up) == ("22.16997229826248023081751379577", .gt)
#guard toString (E "-7/3" 150).1 == "-0.903028032135594937190093340701629268519279141"
#guard toString (expM1Rat (Q "1/3") 53) == "0.3956124250860895"
#guard toString (expM1Rat (Q "-7/3") 200) == "-0.90302803213559493719009334070162926851927914107519\
  5606346953"

-- small arguments: `±1/(3·10^30)`, the compensation keeps the full precision
#guard toString (E "1/3000000000000000000000000000000" 150).1 == "3.3333333333333333333333333333338\
  88888888888888e-31"
#guard D (E "1/3000000000000000000000000000000" 150 .Floor) ==
  ("3.333333333333333333333333333333888888888888888e-31", .lt)
#guard toString (E "-1/3000000000000000000000000000000" 150).1 == "-3.33333333333333333333333333333\
  2777777777777777e-31"
#guard D (E "-1/3000000000000000000000000000000" 150 .Ceiling) ==
  ("-3.333333333333333333333333333332777777777777777e-31", .gt)
#guard toString (expM1Rat (Q "1/3000000000000000000000000000000") 53) == "3.3333333333333333e-31"

-- agreement with `expRat q − 1` at a higher precision
#guard (E "5/7" 100).1 == (subPrecRound (expRat (Q "5/7") 300) one 100 .Nearest).1
#guard (E "-5/7" 100).1 == (subPrecRound (expRat (Q "-5/7") 300) one 100 .Nearest).1

-- directed modes are ordered
#guard (E "5/7" 60 .Floor).2 == .lt
#guard (E "5/7" 60 .Ceiling).2 == .gt
#guard partialCompare (E "5/7" 60 .Floor).1 (E "5/7" 60 .Ceiling).1 == some .lt
#guard partialCompare (E "-5/7" 60 .Floor).1 (E "-5/7" 60 .Ceiling).1 == some .lt

-- `expM1 (ln q) ≈ q − 1`
#guard toString (expM1PrecRound (lnRat (Q "4/3") 200) 100 .Nearest).1 == "0.33333333333333333333333\
  33333335"
#guard toString (expM1PrecRound (lnRat (Q "2/3") 200) 100 .Nearest).1 == "-0.3333333333333333333333\
  333333335"

-- a hugely negative exponent: the value is within `2^(−|x|/2)` above `−1`, and one test
-- (`expM1NearNegOne?`) rounds it at a cost independent of `|x|`
private def m1Above : AzFloat := X "-0.9999999999999999" 53
private def hugeNegX : AzRat :=
  -((AzNat.ofNat 1) <<< (100000 : Nat)).toAzRat * Q "1/3"
private def negX : AzRat := Q "-2001/2"
#guard D (expM1RatPrecRound hugeNegX 53 .Nearest) == ("-1.0", .lt)
#guard D (expM1RatPrecRound hugeNegX 53 .Floor) == ("-1.0", .lt)
#guard D (expM1RatPrecRound hugeNegX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard D (expM1RatPrecRound negX 53 .Nearest) == ("-1.0", .lt)
#guard D (expM1RatPrecRound negX 53 .Floor) == ("-1.0", .lt)
#guard D (expM1RatPrecRound negX 53 .Ceiling) == ("-0.9999999999999999", .gt)
#guard expM1NearNegOne? true 126 53 .Nearest == none
#guard expM1NearNegOne? true 127 53 .Nearest == some (X "-1" 53, .lt)
#guard expM1NearNegOne? false 1000 53 .Nearest == none
