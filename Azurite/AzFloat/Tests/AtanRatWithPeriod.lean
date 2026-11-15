/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arctan (q) u / (2π)` of a rational

The special values (`0` at `q = 0` and for `u = 0`; an eighth of a turn `±u/8` at `q = ±1`,
exact or rounded; `p = 0`), the correctly rounded 53-bit values in degrees (`u = 360`) at the
exact rationals `1/3`, `1/10`, `±22/7`, `−7/5`, `355/113`, `−1/1000`, `10³⁰`, `1 + 10⁻⁶`, other
periods (`1`, `7`, `400`, `2^64 − 1`), agreement with the float function at representable
arguments, the directed modes, 1-, 20- and 113-bit results, a 200-bit string, and the tiny
argument `±1/(3·2^1000)`.  References: an independent 1400-bit fixed-point evaluation rounded
with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanRatWithPeriodPrecRound (Q q) u p m

-- special values
#guard R "0" 360 53 == (zero, .eq)
#guard R "0" 360 0 == (zero, .eq)
#guard R "1/3" 0 53 == (zero, .eq)
#guard R "-1" 0 53 == (zero, .eq)
#guard R "1/3" 360 0 == (nan, .eq)
#guard R "1" 360 53 == (F "45" 53, .eq)
#guard R "-1" 360 53 == (F "-45" 53, .eq)
#guard R "1" 1 53 == (F "1/8" 53, .eq)
#guard R "1" 360 2 == (F "48" 2, .gt)
#guard R "-1" 360 2 .Floor == (F "-48" 2, .lt)

-- correctly rounded values at exact rationals
#guard R "1/3" 360 53 == (F "1297244197648527/70368744177664" 53, .lt)
#guard R "1/10" 360 53 == (F "6429556281526975/1125899906842624" 53, .lt)
#guard R "22/7" 360 53 == (F "2545584950026753/35184372088832" 53, .gt)
#guard R "-22/7" 360 53 == (F "-2545584950026753/35184372088832" 53, .lt)
#guard R "-7/5" 360 53 == (F "-7664890437556127/140737488355328" 53, .lt)
#guard R "355/113" 360 53 == (F "5090701136882613/70368744177664" 53, .lt)
#guard R "-1/1000" 360 53 == (F "-8257189288084933/144115188075855872" 53, .gt)
#guard R "1000000000000000000000000000000" 360 53 == (F "90" 53, .gt)
#guard R "1000001/1000000" 360 53 == (F "6333191007819795/140737488355328" 53, .lt)
#guard R "1/3" 1 53 == (F "7379878102178287/144115188075855872" 53, .lt)
#guard R "1/3" 400 53 == (F "5765529767326787/281474976710656" 53, .gt)
#guard R "-1/3" 7 53 == (F "-6457393339406001/18014398509481984" 53, .gt)
#guard R "3/4" 18446744073709551615 53 == (F "1889248794157641472" 53, .lt)
#guard R "1/3" 360 53 .Floor == (F "1297244197648527/70368744177664" 53, .lt)
#guard R "-22/7" 360 53 .Floor == (F "-2545584950026753/35184372088832" 53, .lt)
#guard R "1/3" 360 53 .Ceiling == (F "5188976790594109/281474976710656" 53, .gt)
#guard R "-22/7" 360 53 .Ceiling == (F "-5091169900053505/70368744177664" 53, .gt)
#guard R "1/3" 360 20 == (F "151019/8192" 20, .lt)
#guard R "1/3" 360 1 == (F "16" 1, .lt)
#guard R "1/3" 360 113
  == (F "1495620732195441784842479450767701/81129638414606681695789005144064" 113, .lt)

-- agreement with the float function at representable arguments
#guard R "1/2" 360 53 == atanWithPeriodPrecRound (F "1/2" 53) 360 53 .Nearest
#guard R "-3" 360 53 == atanWithPeriodPrecRound (F "-3" 53) 360 53 .Nearest
#guard R "1/1024" 7 53 .Floor == atanWithPeriodPrecRound (F "1/1024" 53) 7 53 .Floor
#guard R "1000000000000" 360 53 == atanWithPeriodPrecRound (F "1000000000000" 53) 360 53 .Nearest
#guard atanRatWithPeriod (Q "1/3") 360 53 == (R "1/3" 360 53).1
#guard (toString (atanRatWithPeriod (Q "1/3") 360 200)).startsWith
  "18.43494882292201064842780627954670532879578570035477897"

-- tiny arguments (`±1/(3·2^1000)`)
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard atanRatWithPeriodPrecRound tinyQ 360 53 .Nearest
  == ((F "2687888034010621" 53) <<< AzInt.ofInt (-1047), .lt)
#guard atanRatWithPeriodPrecRound tinyQ 360 53 .Floor
  == ((F "2687888034010621" 53) <<< AzInt.ofInt (-1047), .lt)
#guard atanRatWithPeriodPrecRound (-tinyQ) 360 53 .Ceiling
  == (-((F "2687888034010621" 53) <<< AzInt.ofInt (-1047)), .gt)
