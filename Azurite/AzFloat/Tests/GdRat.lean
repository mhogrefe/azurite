/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.GdRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Gudermannian of a rational

`gd 0 = 0`, `p = 0`; the correctly rounded 53-bit values on every path — the series of
`tanh (|q|/2)` (`1/1000`, `−1/7000000`, `1/3`), the general path (`2/3`, `−7/5`), the series of
`e^(−|q|)` (`22/7`, `100/3`) and the huge path (`1000/3`, `10^40/7`); 200- and 300-bit results;
directed rounding and oddness; a tiny argument; agreement with the float function on dyadic
arguments.  References: a 400-digit evaluation of `2 arctan ((e^q − 1)/(e^q + 1))` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def A (q : String) (p : Nat) (m : RoundingMode := .Nearest) := gdRatPrecRound (Q q) p m

-- special values
#guard A "0" 53 == (zero, .eq)
#guard A "0" 0 == (zero, .eq)
#guard A "1/3" 0 == (nan, .eq)

-- correctly rounded 53-bit values on every path
#guard A "1/1000" 53 == (F "1152921312453311/1152921504606846976" 53, .gt)
#guard A "-1/7000000" 53 == (F "-5396990266136719/37778931862957161709568" 53, .gt)
#guard A "1/3" 53 == (F "5896592075852365/18014398509481984" 53, .gt)
#guard A "2/3" 53 == (F "5603821151032449/9007199254740992" 53, .gt)
#guard A "-7/5" 53 == (F "-4896537914728799/4503599627370496" 53, .lt)
#guard A "22/7" 53 == (F "6685734359227809/4503599627370496" 53, .lt)
#guard A "100/3" 53 == (F "3537118876014205/2251799813685248" 53, .lt)
#guard A "1000/3" 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard A "10000000000000000000000000000000000000000/7" 53
  == (F "884279719003555/562949953421312" 53, .lt)
#guard A "-10000000000000000000000000000000000000000/7" 53 .Floor
  == (-(piDiv2PrecRound 53 .Ceiling).1, .lt)

-- other precisions, directed rounding, oddness
#guard A "1/3" 200 == (F ("65749198711629171117603498858474506161320689615773415828105"
  ++ "/200867255532373784442745261542645325315275374222849104412672") 200, .gt)
#guard A "22/7" 300 == (F ("15120217764466748005175062453830778745684515493990813257670246"
  ++ "73731502380834827558104038419/1018517988167243043134222844204689080525734196832968125"
  ++ "318070224677190649881668353091698688") 300, .gt)
#guard A "1/3" 53 .Floor == (F "2948296037926182/9007199254740992" 53, .lt)
#guard (A "-1/3" 53 .Ceiling).1 == -(A "1/3" 53 .Floor).1
#guard (A "-22/7" 53).1 == -(A "22/7" 53).1

-- a tiny argument: the value is just inside `q`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard (gdRatPrecRound tinyQ 53 .Nearest) == (ofAzRat tinyQ 53, (ofAzRatRound tinyQ 53 .Nearest).2)
#guard (gdRatPrecRound tinyQ 53 .Ceiling).2 == .gt

-- agreement with the float function on dyadic arguments
#guard A "3/8" 53 == gdPrecRound (F "3/8" 53) 53 .Nearest
#guard A "3/4" 53 == gdPrecRound (F "3/4" 53) 53 .Nearest
#guard A "-2" 53 .Floor == gdPrecRound (F "-2" 53) 53 .Floor
#guard A "20" 100 == gdPrecRound (F "20" 53) 100 .Nearest
#guard A "200" 53 .Ceiling == gdPrecRound (F "200" 53) 53 .Ceiling
