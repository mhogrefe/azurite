/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PsiZero
import Azurite.AzFloat.ToString

/-!
# Tests for the real zeros of the digamma function

`x₀, …, x₁₀` at 53 bits (the fifteen digits of DLMF Table 5.4.1 are the leading digits of
`x₀, …, x₁₀`), directed modes, large indices (`100`, `1000`, `10⁶`, `10²⁹` where the zero is
`−n + 0.0149…`), other precisions, 200- and 1000-bit values, `p = 0`, and an independent
check: `ψ` is negative at the zero rounded down and positive at the zero rounded up.
-/

open Azurite Azurite.AzFloat

private def Z (n p : Nat) (m : RoundingMode := .Nearest) := psiZeroPrecRound n p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (Z 0 0) == ("NaN", .eq)
#guard D (Z 5 0) == ("NaN", .eq)

-- `x₀, …, x₁₀`
#guard D (Z 0 53) == ("1.4616321449683622", .lt)
#guard D (Z 1 53) == ("-0.5040830082644554", .gt)
#guard D (Z 2 53) == ("-1.5734984731623904", .gt)
#guard D (Z 3 53) == ("-2.6107208684441447", .lt)
#guard D (Z 4 53) == ("-3.635293366436901", .lt)
#guard D (Z 5 53) == ("-4.653237761743142", .gt)
#guard D (Z 6 53) == ("-5.6671624415568855", .gt)
#guard D (Z 7 53) == ("-6.678418213073427", .lt)
#guard D (Z 8 53) == ("-7.687788325031626", .gt)
#guard D (Z 9 53) == ("-8.695764163816401", .gt)
#guard D (Z 10 53) == ("-9.702672540001863", .gt)

-- DLMF Table 5.4.1
#guard (toString (psiZero 0 53)).startsWith "1.46163214496836"
#guard (toString (psiZero 1 53)).startsWith "-0.50408300826445"
#guard (toString (psiZero 2 53)).startsWith "-1.57349847316239"
#guard (toString (psiZero 3 53)).startsWith "-2.61072086844414"
#guard (toString (psiZero 4 53)).startsWith "-3.63529336643690"
#guard (toString (psiZero 5 53)).startsWith "-4.65323776174314"
#guard (toString (psiZero 6 53)).startsWith "-5.66716244155688"
#guard (toString (psiZero 7 53)).startsWith "-6.67841821307342"
#guard (toString (psiZero 8 53)).startsWith "-7.68778832503162"
#guard (toString (psiZero 9 53)).startsWith "-8.69576416381640"
#guard (toString (psiZero 10 53)).startsWith "-9.70267254000186"

-- directed modes
#guard D (Z 0 53 .Floor) == ("1.4616321449683622", .lt)
#guard D (Z 0 53 .Ceiling) == ("1.4616321449683625", .gt)
#guard D (Z 0 53 .Up) == ("1.4616321449683625", .gt)
#guard D (Z 0 53 .Down) == ("1.4616321449683622", .lt)
#guard D (Z 1 53 .Floor) == ("-0.5040830082644555", .lt)
#guard D (Z 1 53 .Ceiling) == ("-0.5040830082644554", .gt)
#guard D (Z 7 53 .Floor) == ("-6.678418213073427", .lt)
#guard D (Z 7 53 .Ceiling) == ("-6.678418213073426", .gt)

-- large indices
#guard D (Z 100 53) == ("-99.80953650218777", .lt)
#guard D (Z 1000 53) == ("-999.8641415089436", .lt)
#guard D (Z 1000000 53) == ("-999999.9288278621", .lt)
#guard D (Z 1000000 53 .Floor) == ("-999999.9288278621", .lt)
#guard D (Z 100000000000000000000000000000 53) == ("-1.0e29", .gt)
#guard D (Z 100000000000000000000000000000 53 .Floor) == ("-1.0000000000000001e29", .lt)
#guard D (Z 100000000000000000000000000000 120) == ("-99999999999999999999999999999.9850354", .lt)

-- other precisions
#guard D (Z 0 1) == ("1.0", .lt)
#guard D (Z 0 2) == ("1.5", .gt)
#guard D (Z 0 20) == ("1.461632", .lt)
#guard D (Z 1 1) == ("-0.5", .gt)
#guard D (Z 1 24) == ("-0.50408304", .lt)
#guard D (Z 3 10 .Ceiling) == ("-2.61", .gt)
#guard D (Z 0 200) == ("1.461632144968362341262659542325721328468196204006446351295989", .gt)
#guard D (Z 1 200) == ("-0.504083008264455409258269304533302498955385182368579845177269", .gt)
#guard D (Z 2 200 .Floor)
  == ("-1.573498473162390458778286043690434612655040859116846149930144", .lt)
#guard D (Z 12 200) == ("-11.71413306122895384213497680067738659242131370390661088772281", .gt)
#guard D (Z 0 1000) == ("1.46163214496836234126265954232572132846819620400644635129598840859878644\
  035380181024307499273372559275055679336553305334161736577846698582917716838164502465254261879204\
    4384381978333559773961976074719431934937175414059451930109963724166527772172791673250880463960\
    076932978144901475185803414306536810631", .lt)
#guard D (Z 1 1000) == ("-0.5040830082644554092582693045333024989553851823685798451772695845095938\
  337134788646256447938151365254680192096227490330003661686647595405533729442852932788045823297420\
    2185210876277214353029729973487516711058773831596239648631526331699399417089845297625302164356\
    96366515645477797723716812792351038208114", .lt)

-- `ψ` changes sign between the zero rounded down and the zero rounded up
private def signs (n p : Nat) : Bool :=
  lt (digammaPrecRound (Z n p .Floor).1 p .Nearest).1 zero
    && lt zero (digammaPrecRound (Z n p .Ceiling).1 p .Nearest).1
#guard signs 0 53
#guard signs 1 53
#guard signs 2 53
#guard signs 9 53
#guard signs 1000 53
#guard signs 0 300
#guard signs 3 300

-- the verified fallback: bisection on the sign of `ψ`
/-- An enclosure as its two decimal outputs. -/
private def E (o : Option Encl) : Option (String × String) :=
  o.map fun b => (toString b.1, toString b.2)

#guard E (psiZeroFallback 0 64) == some ("1.461632144968362341262367344002727687644",
  "1.46163214496836234126283175831189344806")
#guard E (psiZeroFallback 3 64) == some ("-2.61072086844414465000174174698089901266",
  "-2.61072086844414465000129224999362704155")
-- three steps for `x₁`: the middles `−1/2`, `−3/4`, `−5/8`, `−9/16`
#guard (psiZeroBisect 1 88 (AzInt.ofInt 1) 3 0 (AzInt.ofInt (-1))).map (fun r =>
  r.1 == psiZeroMid 3 (AzInt.ofInt (-5))) == some true
-- the fast enclosure is narrow, so it is the one in use
#guard (psiZeroFast 3 64).map (psiZeroNarrow · 64) == some true
#guard psiZeroEncl 0 64 == psiZeroFast 0 64
#guard psiZeroEncl 3 64 == psiZeroFast 3 64
#guard !psiZeroNarrow (one, powerOf2 (AzInt.ofInt 1)) 64
-- the fuel as an argument
#guard D (psiZeroPrecRoundFuel 2 3 53 .Nearest) == ("-2.6107208684441447", .lt)
#guard psiZeroPrecRoundFuel (lnGammaFuel 53) 7 53 .Nearest == Z 7 53
