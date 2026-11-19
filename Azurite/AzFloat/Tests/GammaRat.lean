/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Div
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def G (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  gammaRatPrecRound (Q s) p m
private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  reciprocalGammaRatPrecRound (Q s) p m
private def pinf : AzFloat := infinity true
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (G "0" 53) == ("Infinity", .eq)
#guard D (G "0" 0) == ("Infinity", .eq)
#guard D (G "-1" 53) == ("NaN", .eq)
#guard D (G "-3" 53) == ("NaN", .eq)
#guard D (G "3" 0) == ("NaN", .eq)
#guard D (G "1/3" 0) == ("NaN", .eq)
#guard D (R "0" 53) == ("0.0", .eq)
#guard D (R "-1" 53) == ("0.0", .eq)
#guard D (R "-1000" 0) == ("0.0", .eq)
#guard D (R "1/3" 0) == ("NaN", .eq)

-- positive integers
#guard D (G "1" 53) == ("1.0", .eq)
#guard D (G "2" 53) == ("1.0", .eq)
#guard D (G "5" 53) == ("24.0", .eq)
#guard D (G "21" 100) == ("2.43290200817664e18", .eq)
#guard (G "30" 53).2 != .eq
#guard D (R "1" 53) == ("1.0", .eq)
#guard D (R "3" 53) == ("0.5", .eq)
#guard D (R "4" 53 .Floor) == ("0.16666666666666666", .lt)

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
  lt (subPrecRound x (X "1" 200) 200 .Nearest).1.abs (powerOf2 (AzInt.ofInt (-180)))

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
#guard D (G ("1/" ++ t200) 53) == ("1.6069380442589903e60", .gt)
#guard D (G ("1/" ++ t200') 53) == ("1.6069380442589903e60", .lt)
#guard D (G ("-1/" ++ t200) 53 .Ceiling) == ("-1.6069380442589903e60", .gt)
#guard D (R ("1/" ++ t200) 53) == ("6.223015277861142e-61", .lt)
#guard D (R ("1/" ++ t200') 53) == ("6.223015277861142e-61", .gt)
#guard D (R ("-1/" ++ t200) 53) == ("-6.223015277861142e-61", .lt)
#guard (G ("3/" ++ t200) 53 .Floor).2 == .lt && (R ("3/" ++ t200) 53 .Floor).2 == .lt

-- denominators 2, 3, 4, 6: the certified loops (no fuel; `Γ(q)` is irrational)
#guard ["1/2", "-1/2", "3/4", "2/3", "1/6", "5/6", "-1/3", "1/4", "1/3", "22/6"].all fun s =>
  gammaRatSpecial (Q s)
#guard ["1/5", "7", "7/12", "0", "-3"].all fun s => !gammaRatSpecial (Q s)
#guard D (G "2/3" 53) == ("1.3541179394264005", .gt)
#guard D (G "1/6" 53) == ("5.566316001780235", .lt)
#guard D (G "5/6" 53 .Down) == ("1.128787029908126", .lt)
#guard D (G "-1/3" 53) == ("-4.062353818279202", .lt)
#guard D (G "1/3" 53) == ("2.6789385347077475", .lt)
#guard D (G "1/4" 53) == ("3.625609908221908", .lt)
#guard D (G "-17/6" 53) == ("-1.2859082955984287", .lt)
#guard D (G "100/3" 53) == ("8.411595456441839e35", .gt)
#guard D (G "1/2" 200)
  == ("1.772453850905516027298167483341145182797549456122387128213808", .lt)
#guard D (R "1/6" 53) == ("0.17965203550789735", .gt)
#guard D (R "-5/2" 53) == ("-1.057855469152043", .gt)

-- the same denominators through the constants (`gammaSpecialFast?`), with integer shifts
#guard D (G "301/2" 53) == ("4.661072627097378e261", .gt)
#guard D (G "-301/6" 53) == ("-1.0742431898422673e-64", .lt)
#guard [(1, 2), (1, 3), (2, 3), (1, 4), (3, 4), (1, 6), (5, 6)].all fun (r, d) =>
  (gammaBaseEncl r d 64).1.isFinite && (gammaBaseEncl r d 64).2.isFinite
#guard (gammaSpecialFast? false true (AzNat.ofNat 1000001) 3 53 .Nearest).isNone
#guard (gammaAP 1 3 4).toNat == 1 * 4 * 7 * 10

-- no fuel at the integers: a certified loop beyond the factorial bound
#guard D (gammaRatPrecRoundFuel 0 (Q "3000") 53 .Nearest) == ("1.383119867812618e9127", .lt)
#guard D (reciprocalGammaRatPrecRoundFuel 0 (Q "3000") 53 .Nearest)
  == ("7.230031346317684e-9128", .lt)
#guard G "7/5" 53 == gammaRatPrecRoundFuel (gammaFuel 53) (Q "7/5") 53 .Nearest
