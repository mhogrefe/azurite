/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Div
import Azurite.AzRat.Parse

/-!
# Tests for `Γ` and `1/Γ` of a rational

* Special values: `0`, the poles, `p = 0`, positive integers (exact factorials).
* Dyadic arguments: the results must be those of the float functions at the same argument, in
  every mode.
* Non-dyadic arguments: `Γ(1/3)`, `Γ(1/4)`, `Γ(2/3)`, `Γ(−1/3)` against decimal brackets; the
  recurrence `Γ(q + 1) = q Γ(q)` on both sides of `0` and `Γ(q) · (1/Γ(q)) = 1` at 200 bits.
* Tiny arguments, with `1/q` at or next to a rounding boundary, and arguments next to a pole.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def G (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  gammaRatPrecRound (Q s) p m
private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  reciprocalGammaRatPrecRound (Q s) p m
private def pinf : AzFloat := infinity true

-- special values
#guard G "0" 53 == (pinf, .eq)
#guard G "0" 0 == (pinf, .eq)
#guard G "-1" 53 == (nan, .eq)
#guard G "-3" 53 == (nan, .eq)
#guard G "3" 0 == (nan, .eq)
#guard G "1/3" 0 == (nan, .eq)
#guard R "0" 53 == (zero, .eq)
#guard R "-1" 53 == (zero, .eq)
#guard R "-1000" 0 == (zero, .eq)
#guard R "1/3" 0 == (nan, .eq)

-- positive integers
#guard G "1" 53 == (F "1" 53, .eq)
#guard G "2" 53 == (F "1" 53, .eq)
#guard G "5" 53 == (F "24" 53, .eq)
#guard G "21" 100 == (F "2432902008176640000" 100, .eq)
#guard (G "30" 53).2 != .eq
#guard R "1" 53 == (F "1" 53, .eq)
#guard R "3" 53 == (F "1/2" 53, .eq)
#guard R "4" 53 .Floor == ofAzRatRound (Q "1/6") 53 .Floor

-- dyadic arguments: the float functions
private def dyadicOk (s : String) (p : Nat) (m : RoundingMode) : Bool :=
  G s p m == gammaPrecRound (F s 64) p m && R s p m == reciprocalGammaPrecRound (F s 64) p m
#guard [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
  ["1/2", "3/2", "5/4", "7/2", "33/32", "1/1024", "3", "171", "200", "1000", "-1/2", "-7/2",
    "-33/32", "-1/1024", "-201/2"].all fun s => dyadicOk s 53 m
#guard ["1/2", "7/2", "33/32", "100", "-5/4", "-201/2"].all fun s =>
  dyadicOk s 24 .Nearest && dyadicOk s 200 .Nearest && dyadicOk s 200 .Floor

-- non-dyadic arguments against decimal brackets
private def between (s lo hi : String) (p : Nat) : Bool :=
  [RoundingMode.Nearest, .Floor, .Ceiling].all fun m =>
    lt (F lo 200) (G s p m).1 && lt (G s p m).1 (F hi 200)
#guard between "1/3" "2678938534707747/1000000000000000" "2678938534707748/1000000000000000" 53
#guard between "1/4" "3625609908221908/1000000000000000" "3625609908221909/1000000000000000" 53
#guard between "2/3" "1354117939426400/1000000000000000" "1354117939426401/1000000000000000" 53
#guard between "-1/3" "-406235381827921/100000000000000" "-406235381827919/100000000000000" 53
#guard between "-1/3" "-4062353818279202/1000000000000000" "-4062353818279201/1000000000000000"
  100
#guard between "1/3" "2678938534707747/1000000000000000" "2678938534707748/1000000000000000" 300
#guard between "-10000001/10000000" "999999957/100" "999999958/100" 53

-- within `2^(−180)` of `1`
private def nearOne (x : AzFloat) : Bool :=
  lt (subPrecRound x (F "1" 200) 200 .Nearest).1.abs (powerOf2 (AzInt.ofInt (-180)))

-- the recurrence `Γ(q + 1) = q Γ(q)` at 200 bits
private def recOk (s s1 : String) : Bool :=
  nearOne (divPrecRound (divPrecRound (G s1 200).1 (G s 200).1 200 .Nearest).1 (F s 200) 200
    .Nearest).1
#guard recOk "1/3" "4/3"
#guard recOk "22/7" "29/7"
#guard recOk "1/1000" "1001/1000"
#guard recOk "1000/7" "1007/7"
#guard recOk "-1/3" "2/3"
#guard recOk "-4/3" "-1/3"
#guard recOk "-7/3" "-4/3"
#guard recOk "-1000/7" "-993/7"
#guard recOk "-1/1000" "999/1000"

-- `Γ(q) · (1/Γ(q)) = 1` at 200 bits, and the signs between the poles
#guard ["1/3", "22/7", "1000/7", "-1/3", "-4/3", "-1000/7", "1/1000000", "-999999/1000000"].all
  fun s => nearOne (mulPrecRound (G s 200).1 (R s 200).1 200 .Nearest).1
#guard lt (G "-1/3" 53).1 zero && lt zero (G "-4/3" 53).1 && lt (G "-7/3" 53).1 zero
#guard lt (R "-1/3" 53).1 zero && lt zero (R "-4/3" 53).1 && lt (R "-7/3" 53).1 zero

-- directed modes are consistent
#guard ["1/3", "-4/3", "100/7"].all fun s =>
  (G s 53 .Floor).2 == .lt && (G s 53 .Ceiling).2 == .gt && lt (G s 53 .Floor).1 (G s 53 .Ceiling).1
    && (R s 53 .Floor).2 == .lt && (R s 53 .Ceiling).2 == .gt

-- tiny arguments: `2^(−200)` (`1/q` a float) and `1/(2^200 + 1)` (`1/q` next to one)
private def t200 : String := "1606938044258990275541962092341162602522202993782792835301376"
private def t200' : String := "1606938044258990275541962092341162602522202993782792835301377"
#guard G ("1/" ++ t200) 53 == (F t200 53, .gt)
#guard G ("1/" ++ t200') 53 == (F t200 53, .lt)
#guard G ("-1/" ++ t200) 53 .Ceiling == ((-(F t200 53)), .gt)
#guard R ("1/" ++ t200) 53 == (F ("1/" ++ t200) 53, .lt)
#guard R ("1/" ++ t200') 53 == (F ("1/" ++ t200) 53, .gt)
#guard R ("-1/" ++ t200) 53 == (F ("-1/" ++ t200) 53, .lt)
#guard (G ("3/" ++ t200) 53 .Floor).2 == .lt && (R ("3/" ++ t200) 53 .Floor).2 == .lt
