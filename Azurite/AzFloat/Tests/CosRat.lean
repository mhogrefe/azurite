/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.CosRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cos q` of a rational

The special values (`cos 0 = 1`, `p = 0`), the correctly rounded 53-bit values of `cos q` at the
exact rationals `1/3`, `1/10`, `22/7`, `−7/5` (which differs in the last place from `cos` of the
53-bit float nearest `−7/5`), `355/113` (`cos ≈ −1 + 3.6·10⁻¹⁴`), `−1/1000`, `10³⁰`, `2⁻¹⁰⁰`,
agreement with the float `cos` at exactly representable arguments (`1/2`, `3`, `10¹²`,
`1/1024`), the directed modes, a 20-bit result, and 200-bit values of `cos (1/3)` and
`cos (355/113)`.  References: a 240-digit evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def C (q : String) (p : Nat) (m : RoundingMode := .Nearest) := cosRatPrecRound (Q q) p m

-- special values
#guard C "0" 53 == (F "1" 53, .eq)
#guard C "0" 0 == (nan, .eq)
#guard C "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard C "1/3" 53 == (F "8511415502608429/9007199254740992" 53, .gt)
#guard C "1/10" 53 == (F "8962200775956417/9007199254740992" 53, .gt)
#guard C "22/7" 53 == (F "-4503596026893703/4503599627370496" 53, .lt)
#guard C "-7/5" 53 == (F "6123711691446023/36028797018963968" 53, .lt)
#guard cosPrecRound (F "-7/5" 53) 53 .Nearest == (F "6123711691446027/36028797018963968" 53, .gt)
#guard C "355/113" 53 == (F "-140737488355323/140737488355328" 53, .lt)
#guard C "-1/1000" 53 == (F "2251798687785435/2251799813685248" 53, .gt)
#guard C "1000000000000000000000000000000" 53 == (F "-4485275356010793/4503599627370496" 53, .gt)
#guard C "1/1267650600228229401496703205376" 53 == (F "1" 53, .gt)

-- agreement with the float `cos` at representable arguments
#guard C "1/2" 53 == cosPrecRound (F "1/2" 53) 53 .Nearest
#guard C "3" 53 == cosPrecRound (F "3" 53) 53 .Nearest
#guard C "1000000000000" 53 == cosPrecRound (F "1000000000000" 53) 53 .Nearest
#guard C "1/1024" 53 == cosPrecRound (F "1/1024" 53) 53 .Nearest

-- directed modes and other precisions
#guard C "1/3" 53 .Floor == (F "2127853875652107/2251799813685248" 53, .lt)
#guard C "1/3" 53 .Ceiling == (F "8511415502608429/9007199254740992" 53, .gt)
#guard C "22/7" 53 .Floor == (F "-4503596026893703/4503599627370496" 53, .lt)
#guard C "22/7" 53 .Ceiling == (F "-9007192053787405/9007199254740992" 53, .gt)
#guard C "1/3" 20 == (F "990859/1048576" 20, .lt)
#guard cosRat (Q "1/3") 53 == F "8511415502608429/9007199254740992" 53
#guard toString (cosRat (Q "1/3") 200)
  == "0.944956946314737664388284007675880607845852699565140737677646"
#guard toString (cosRat (Q "355/113") 200)
  == "-0.9999999999999644184337169343129714252032324580791768112016077"
