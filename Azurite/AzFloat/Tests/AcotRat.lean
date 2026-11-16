/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotRat
import Azurite.AzFloat.Acot
import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot q` of a rational, plain and with a period

`acotRat`: the special values (`π/2` at `0`, `±π/4` at `±1`, `p = 0`), the correctly rounded
53-bit values at exact rationals on both sides of `1`, the directed modes, 20- and 113-bit
results, agreement with the float `acot`, oddness, a 200-bit string, tiny and huge rationals.

`acotRatWithPeriod`: the special values (`u/4` at `0`; `±u/8` at `±1`; `u = 0`; `p = 0`), the
correctly rounded 53-bit values in degrees, other periods, the directed modes, a 20-bit result,
a 200-bit string, and tiny and huge rationals.

References: an independent 1400-bit fixed-point evaluation of `arctan (1/q)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotRatPrecRound (Q q) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotRatWithPeriodPrecRound (Q q) u p m
private def piN : AzFloat := F "884279719003555/281474976710656" 53
private def piC : AzFloat := F "7074237752028441/2251799813685248" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard T "0" 53 == (h piN (-1), .lt)
#guard T "0" 53 .Ceiling == (h piC (-1), .gt)
#guard T "1" 53 == (h piN (-2), .lt)
#guard T "1" 53 .Ceiling == (h piC (-2), .gt)
#guard T "-1" 53 == (-(h piN (-2)), .gt)
#guard T "-1" 53 .Floor == (-(h piC (-2)), .lt)
#guard T "3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "3" 53 == (F "5796142707547873/18014398509481984" 53, .lt)
#guard T "-3" 53 == (F "-5796142707547873/18014398509481984" 53, .gt)
#guard T "3/2" 53 == (F "5296256612459413/9007199254740992" 53, .lt)
#guard T "-7/5" 53 == (F "-5586710707897953/9007199254740992" 53, .lt)
#guard T "22/7" 53 == (F "2774692779658249/9007199254740992" 53, .gt)
#guard T "1/3" 53 == (F "175787564848171/140737488355328" 53, .gt)
#guard T "-2/7" 53 == (F "-5820887511435685/4503599627370496" 53, .lt)
#guard T "1/1000000" 53 == (F "7074233248428813/4503599627370496" 53, .gt)
#guard T "1000000007/3" 53 == (F "7253554866912891/2417851639229258349412352" 53, .gt)
#guard T "355/113" 53 == (F "5551480013267005/18014398509481984" 53, .gt)
#guard T "2" 53 == (F "8352332796509007/18014398509481984" 53, .lt)
#guard T "-1/2" 53 == (F "-1246538638225297/1125899906842624" 53, .gt)
#guard T "3" 53 .Floor == (F "5796142707547873/18014398509481984" 53, .lt)
#guard T "-3/2" 53 .Floor == (F "-2648128306229707/4503599627370496" 53, .lt)
#guard T "3" 53 .Ceiling == (F "2898071353773937/9007199254740992" 53, .gt)
#guard T "-3/2" 53 .Ceiling == (F "-5296256612459413/9007199254740992" 53, .gt)
#guard T "3" 20 == (F "84345/262144" 20, .gt)
#guard T "3/2" 113
  == (F "6106168142420669375800887123151837/10384593717069655257060992658440192" 113, .gt)

-- agreement with the float `acot` at representable arguments, oddness
#guard T "2" 53 == acotPrecRound (F "2" 53) 53 .Nearest
#guard T "-3/2" 53 .Floor == acotPrecRound (F "-3/2" 53) 53 .Floor
#guard T "1/4" 53 .Ceiling == acotPrecRound (F "1/4" 53) 53 .Ceiling
#guard acotRat (Q "3") 53 == (T "3" 53).1
#guard (T "-22/7" 53 .Floor).1 == -(T "22/7" 53 .Ceiling).1
#guard (toString (acotRat (Q "3") 200)).startsWith
  "0.321750554396642193401404614358661319020755295557656191"

-- tiny and huge rationals
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard acotRatPrecRound (pw 5000) 53 .Nearest == (h piN (-1), .lt)
#guard acotRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h piN (-1)), .gt)
#guard acotRatPrecRound (-(pw 5000)) 53 .Floor == (-(h piC (-1)), .lt)
#guard acotRatPrecRound (-(pw 5000)) 53 .Ceiling == (-(h piN (-1)), .gt)
#guard acotRatPrecRound (pw 5000)⁻¹ 53 .Nearest == (h (F "1" 53) (-5000), .gt)
#guard acotRatPrecRound (pw 5000)⁻¹ 53 .Floor
  == (h (F "9007199254740991/9007199254740992" 53) (-5000), .lt)
#guard acotRatPrecRound (-(pw 5000)⁻¹) 53 .Floor == (-(h (F "1" 53) (-5000)), .lt)
#guard acotRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)

-- with a period: special values
#guard R "0" 360 53 == (F "90" 53, .eq)
#guard R "0" 0 53 == (zero, .eq)
#guard R "0" 7 1 == (F "2" 1, .gt)
#guard R "3" 0 53 == (zero, .eq)
#guard R "-1/3" 0 53 == (zero, .eq)
#guard R "3" 360 0 == (nan, .eq)
#guard R "1" 360 53 == (F "45" 53, .eq)
#guard R "-1" 360 53 == (F "-45" 53, .eq)
#guard R "3/3" 7 53 == (F "7/8" 53, .eq)
#guard R "-1" 7 1 .Ceiling == (F "-1/2" 1, .gt)

-- with a period: correctly rounded values
#guard R "3" 360 53 == (F "1297244197648527/70368744177664" 53, .lt)
#guard R "-3" 360 53 == (F "-1297244197648527/70368744177664" 53, .gt)
#guard R "3/2" 360 53 == (F "2370727743063897/70368744177664" 53, .lt)
#guard R "-7/5" 360 53 == (F "-5001483514423393/140737488355328" 53, .gt)
#guard R "22/7" 360 53 == (F "4968068303745017/281474976710656" 53, .gt)
#guard R "1000000007/3" 360 53 == (F "3246860002661611/18889465931478580854784" 53, .gt)
#guard R "1/3" 360 53 == (F "5035942778341233/70368744177664" 53, .gt)
#guard R "-2/7" 360 53 == (F "-5211129491026147/70368744177664" 53, .gt)
#guard R "2" 360 53 == (F "1869349290346353/70368744177664" 53, .gt)
#guard R "3" 1 53 == (F "7379878102178287/144115188075855872" 53, .lt)
#guard R "3" 7 53 == (F "6457393339406001/18014398509481984" 53, .lt)
#guard R "3" 400 53 == (F "5765529767326787/281474976710656" 53, .gt)
#guard R "-3" 360 53 .Floor == (F "-5188976790594109/281474976710656" 53, .lt)
#guard R "-3" 360 53 .Ceiling == (F "-1297244197648527/70368744177664" 53, .gt)
#guard R "3" 360 20 == (F "151019/8192" 20, .lt)
#guard R "3/2" 360 53 == acotWithPeriodPrecRound (F "3/2" 53) 360 53 .Nearest
#guard acotRatWithPeriod (Q "3") 360 53 == (R "3" 360 53).1
#guard (toString (acotRatWithPeriod (Q "3") 360 200)).startsWith
  "18.43494882292201064842780627954670532879578570035477897"
#guard acotRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest
  == (h (F "1007958012753983/17592186044416" 53) (-5000), .gt)
#guard acotRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Floor
  == (h (F "8063664102031863/140737488355328" 53) (-5000), .lt)
#guard acotRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Nearest
  == (-(h (F "1007958012753983/17592186044416" 53) (-5000)), .lt)
#guard acotRatWithPeriodPrecRound (pw 5000) 360 53 .Nearest == (F "90" 53, .gt)
#guard acotRatWithPeriodPrecRound (pw 5000) 360 53 .Floor
  == (F "6333186975989759/70368744177664" 53, .lt)
#guard acotRatWithPeriodPrecRound (-(pw 5000)) 360 53 .Floor == (F "-90" 53, .lt)
