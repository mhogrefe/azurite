/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.GdInv
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the inverse Gudermannian `gd⁻¹ x`

The special values (`NaN`, `±∞ ↦ NaN`, `0`, `p = 0`); the domain: the two doubles around `π/2`
(the one below gives `38.025…`, the one above `NaN`), `2`, huge arguments; the correctly rounded
53-bit values from `1/1024` to `201/128` and next to `π/2`; 200- and 300-bit results; directed
rounding and oddness; tiny arguments (the value is just outside `x`); and the round trip with
`gd`.  References: a 500-digit evaluation of `ln ((1 + sin x)/cos x)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := gdInvPrecRound x p m

-- special values
#guard A nan 53 == (nan, .eq)
#guard A (infinity true) 53 == (nan, .eq)
#guard A (infinity false) 53 == (nan, .eq)
#guard A zero 53 == (zero, .eq)
#guard A zero 0 == (zero, .eq)
#guard A (F "1" 53) 0 == (nan, .eq)

-- the domain `|x| < π/2`: the doubles just below and just above `π/2`
private def below : AzFloat := F "7074237752028440/4503599627370496" 53
private def above : AzFloat := F "7074237752028441/4503599627370496" 53
#guard gdInvInDomain below (AzInt.ofInt 1) 53 && !gdInvInDomain above (AzInt.ofInt 1) 53
#guard A below 53 == (F "1337885867383887/35184372088832" 53, .lt)
#guard A (-below) 53 == (F "-1337885867383887/35184372088832" 53, .gt)
#guard A above 53 == (nan, .eq)
#guard A (-above) 53 == (nan, .eq)
#guard A (F "2" 53) 53 == (nan, .eq)
#guard A (F "-100" 53) 53 == (nan, .eq)
#guard A (h (F "1" 53) (2 ^ 40)) 53 == (nan, .eq)
#guard gdInvInDomain (F "3/2" 2) (AzInt.ofInt 1) 2 && !gdInvInDomain (F "2" 2) (AzInt.ofInt 2) 2
#guard gdInvInDomain (F "1/2" 53) (AzInt.ofInt 0) 53

-- correctly rounded 53-bit values
#guard A (F "1/1024" 53) 53 == (F "4503600343198549/4611686018427387904" 53, .lt)
#guard A (F "3/8" 53) 53 == (F "6919533342580767/18014398509481984" 53, .gt)
#guard A (F "1" 53) 53 == (F "172571065633625/140737488355328" 53, .gt)
#guard A (F "-1" 53) 53 == (F "-172571065633625/140737488355328" 53, .lt)
#guard A (F "5/4" 53) 53 == (F "8203164045865069/4503599627370496" 53, .gt)
#guard A (F "3/2" 53) 53 == (F "7522537068455729/2251799813685248" 53, .gt)
#guard A (F "25/16" 53) 53 == (F "6175655408969807/1125899906842624" 53, .lt)
#guard A (F "201/128" 53) 53 == (F "4687645271173831/562949953421312" 53, .lt)

-- other precisions, directed rounding, oddness
#guard A (F "1" 53) 200 == (F ("985206621013600131413596446220706783397168592983187416994149"
  ++ "/803469022129495137770981046170581301261101496891396417650688") 200, .gt)
#guard A (F "3/2" 53) 300 == (F ("8506350425016061728220807367535134260504296626149152767778795"
  ++ "45503577508835053560688302941/25462949704181076078355571105117227013143354920824203132"
  ++ "9517556169297662470417088272924672") 300, .lt)
#guard A (F "1/64" 53) 300 == (F ("101855943429997337842497179394053330624193982620814177487244"
  ++ "0707481009479012906498835274861/6518515124270355476059026202910010115364698859730996002"
  ++ "0356494379340201592426774597868716032") 300, .lt)
#guard A (F "1" 53) 53 .Floor == (F "5522274100275999/4503599627370496" 53, .lt)
#guard A (F "1" 53) 53 .Ceiling == (F "172571065633625/140737488355328" 53, .gt)
#guard (A (F "-5/4" 53) 53 .Floor).1 == -(A (F "5/4" 53) 53 .Ceiling).1
#guard toString (gdInv (F "1" 200))
  == "1.226191170883517070813060967471906752724248350220740279138617"

-- tiny arguments: the value is just outside `x`
#guard A (h (F "1" 53) (-1000)) 53 == (h (F "1" 53) (-1000), .lt)
#guard A (h (F "-1" 53) (-1000)) 53 == (h (F "-1" 53) (-1000), .gt)
#guard A (h (F "1" 53) (-(2 ^ 30))) 53 .Ceiling
  == (h (F "4503599627370497/4503599627370496" 53) (-(2 ^ 30)), .gt)

-- round trip with `gd` at a higher intermediate precision
#guard (gdPrecRound (A (F "5/4" 53) 200).1 53 .Nearest).1 == F "5/4" 53
#guard (A (gdPrecRound (F "3" 53) 200 .Nearest).1 53).1 == F "3" 53

-- the dummy bracket next to `π/2` at a level too low to separate `x` from `π/2`
private def near : AzFloat := (piDiv2PrecRound 200 .Floor).1
#guard gdInvBracket near (AzInt.ofInt 1) 64 == (-one, one)
#guard gdInvBracket near (AzInt.ofInt 1) 400 != (-one, one)
#guard lt (F "138" 53) (A near 53).1 && lt (A near 53).1 (F "200" 53)
#guard A (piDiv2PrecRound 200 .Ceiling).1 53 == (nan, .eq)
#guard lnOfEncl (-one, one) 64 == (-one, one) && lnOfEncl (zero, one) 64 == (-one, one)
