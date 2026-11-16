/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsecWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsec (x) u / (2π)`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and for `u = 0`; `u/4` at `±∞`;
`u = 0`; `0` at `1`; `u/2` at `−1`; `u/6` at `2` and `u/3` at `−2` — exact for `u = 360`, the
correctly rounded rationals for `u = 7`, `1` in several modes; `p = 0`), the correctly rounded
53-bit values in degrees, other periods (`1`, `7`, `400`, `2^64 − 1`), the directed modes, 1-,
20- and 113-bit results, a 200-bit string, the neighbours `±(1 + 2^(−52))` of `±1`, and huge
arguments `±2^1000`, `±2^(2^30)`: values next to the float `u/4`, at no extra cost.
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  asecWithPeriodPrecRound x u p m

-- special values
#guard W nan 360 53 == (nan, .eq)
#guard W zero 360 53 == (nan, .eq)
#guard W zero 0 53 == (nan, .eq)
#guard W (F "1/2" 53) 360 53 == (nan, .eq)
#guard W (F "-3/4" 53) 0 53 == (nan, .eq)
#guard W (infinity true) 360 53 == (F "90" 53, .eq)
#guard W (infinity false) 360 53 == (F "90" 53, .eq)
#guard W (infinity true) 7 1 == (F "2" 1, .gt)
#guard W (infinity false) 0 53 == (zero, .eq)
#guard W (F "3" 53) 0 53 == (zero, .eq)
#guard W (F "-1" 53) 0 53 == (zero, .eq)
#guard W (F "3" 53) 360 0 == (nan, .eq)
#guard W (F "1" 53) 360 53 == (zero, .eq)
#guard W (F "1" 200) 360 0 == (zero, .eq)
#guard W (F "-1" 53) 360 53 == (F "180" 53, .eq)
#guard W (F "-1" 53) 7 1 == (F "4" 1, .gt)
-- a sixth and a third of a turn
#guard W (F "2" 53) 360 53 == (F "60" 53, .eq)
#guard W (F "-2" 200) 360 53 == (F "120" 53, .eq)
#guard W (F "2" 53) 3 53 == (F "1/2" 53, .eq)
#guard W (F "2" 53) 7 53 == (F "5254199565265579/4503599627370496" 53, .gt)
#guard W (F "2" 53) 7 53 .Floor == (F "2627099782632789/2251799813685248" 53, .lt)
#guard W (F "-2" 53) 7 53 == (F "5254199565265579/2251799813685248" 53, .gt)
#guard W (F "2" 53) 1 53 == (F "6004799503160661/36028797018963968" 53, .lt)
#guard W (F "-2" 53) 1 53 .Ceiling == (F "3002399751580331/9007199254740992" 53, .gt)

-- correctly rounded values
#guard W (F "3" 53) 360 53 == (F "155094426010451/2199023255552" 53, .lt)
#guard W (F "-3" 53) 360 53 == (F "240729759988909/2199023255552" 53, .gt)
#guard W (F "3/2" 53) 360 53 == (F "6782095246202283/140737488355328" 53, .gt)
#guard W (F "-7/5" 53) 360 53 == (F "149076944745807/1099511627776" 53, .gt)
#guard W (F "5/4" 53) 360 53 == (F "1297244197648527/35184372088832" 53, .lt)
#guard W (F "100" 53) 360 53 == (F "786608497934669/8796093022208" 53, .gt)
#guard W (F "-1000" 53) 360 53 == (F "1584304702178187/17592186044416" 53, .lt)
#guard W (F "1000001/1000000" 53) 360 53 == (F "2919357026173153/36028797018963968" 53, .gt)
#guard W (F "-1000001/1000000" 53) 360 53 == (F "197823001293559/1099511627776" 53, .gt)
#guard W (F "22/7" 53) 360 53 == (F "5027635346137851/70368744177664" 53, .lt)
#guard W (F "3/2" 53) 1 53 == (F "2411411643094145/18014398509481984" 53, .gt)
#guard W (F "-4" 53) 1 53 == (F "5228054277212783/18014398509481984" 53, .gt)
#guard W (F "3/2" 53) 7 53 == (F "8439940750829507/9007199254740992" 53, .lt)
#guard W (F "-4" 53) 7 53 == (F "4574547492561185/2251799813685248" 53, .lt)
#guard W (F "3/2" 53) 400 53 == (F "7535661384669203/140737488355328" 53, .lt)
#guard W (F "-4" 53) 400 53 == (F "8168834808144973/70368744177664" 53, .lt)
#guard W (F "3/2" 53) 18446744073709551615 53 == (F "2469285522528404480" 53, .gt)
#guard W (F "-4" 53) 18446744073709551615 53 == (F "5353527579865889792" 53, .gt)
#guard W (F "3/2" 53) 360 53 .Floor == (F "3391047623101141/70368744177664" 53, .lt)
#guard W (F "-4" 53) 360 53 .Floor == (F "7351951327330475/70368744177664" 53, .lt)
#guard W (F "3/2" 53) 360 53 .Ceiling == (F "6782095246202283/140737488355328" 53, .gt)
#guard W (F "-4" 53) 360 53 .Ceiling == (F "1837987831832619/17592186044416" 53, .gt)
#guard W (F "3/2" 53) 360 20 == (F "197385/4096" 20, .gt)
#guard W (F "-4" 53) 360 1 == (F "128" 1, .gt)
#guard W (F "3/2" 53) 360 113
  == (F "7819223455638480087591349316335203/162259276829213363391578010288128" 113, .gt)
#guard asecWithPeriod (F "3/2" 53) 360 == (W (F "3/2" 53) 360 53).1
#guard (toString (asecWithPeriodPrecRound (F "3/2" 200) 360 200 .Nearest).1).startsWith
  "48.18968510422140193414208326942174046898588046409865224"

-- next to `±1`
#guard W (F "4503599627370497/4503599627370496" 53) 360 53
  == (F "5701871567757263/4722366482869645213696" 53, .gt)
#guard W (F "-4503599627370497/4503599627370496" 53) 360 53
  == (F "3166593466753753/17592186044416" 53, .lt)
#guard W (F "-4503599627370497/4503599627370496" 53) 360 53 .Ceiling
  == (F "6333186933507507/35184372088832" 53, .gt)

-- huge arguments: next to the float `u/4`
private def T : AzFloat := powerOf2 (AzInt.ofInt 1000)
#guard W T 360 53 == (F "90" 53, .gt)
#guard W T 360 53 .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard W (-T) 360 53 == (F "90" 53, .lt)
#guard W (-T) 360 53 .Ceiling == (F "6333186975989761/70368744177664" 53, .gt)
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard W huge 360 53 == (F "90" 53, .gt)
#guard W huge 360 53 .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard W (-huge) 360 53 == (F "90" 53, .lt)
#guard W (-huge) 360 53 .Ceiling == (F "6333186975989761/70368744177664" 53, .gt)
#guard W (-huge) 360 53 .Floor == (F "90" 53, .lt)
