/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.HexString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the constants

`√2 = 1.4142135623730950488…`; its binary64 significand is `0x6a09e667f3bcd`, and that value
lies above `√2` (`1.41421356237309514…`).  The low-precision cases are rounded by hand from
`√3 = 1.7320508…`, `√5 = 2.2360679…`, `√2/2 = 0.7071067…`, `√3/3 = 0.5773502…`,
`√5/5 = 0.4472135…`, `φ = 1.6180339…`; the 53-bit decimals are the familiar binary64 values.
`√2/2` must agree with `√2` shifted, since the shift is exact.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard sqrt2PrecRound 1 .Nearest == (one, .lt)
#guard sqrt2PrecRound 1 .Ceiling == (two, .gt)
#guard sqrt2PrecRound 2 .Nearest == (F "3/2" 2, .gt)
#guard sqrt2PrecRound 2 .Floor == (F "1" 2, .lt)
#guard sqrt2PrecRound 53 .Nearest == (F "6369051672525773/4503599627370496" 53, .gt)
#guard sqrt2PrecRound 53 .Ceiling == (F "6369051672525773/4503599627370496" 53, .gt)
#guard sqrt2PrecRound 53 .Floor == (F "6369051672525772/4503599627370496" 53, .lt)
#guard toHexString (sqrt2 53) == "0x1.6a09e667f3bcd#53"
#guard toHexString (sqrt2PrecRound 53 .Floor).1 == "0x1.6a09e667f3bcc#53"
#guard toString (sqrt2 53) == "1.4142135623730951"
#guard toString (sqrt2 100) == "1.414213562373095048801688724209"

/-! ## `√3`, `√5` -/

#guard sqrt3PrecRound 2 .Nearest == (F "3/2" 2, .lt)
#guard sqrt3PrecRound 3 .Nearest == (F "7/4" 3, .gt)
#guard sqrt3PrecRound 3 .Floor == (F "3/2" 3, .lt)
#guard toString (sqrt3 53) == "1.7320508075688772"
#guard sqrt5PrecRound 2 .Nearest == (F "2" 2, .lt)
#guard sqrt5PrecRound 3 .Nearest == (F "2" 3, .lt)
#guard sqrt5PrecRound 4 .Nearest == (F "9/4" 4, .gt)
#guard sqrt5PrecRound 4 .Down == (F "2" 4, .lt)
#guard toString (sqrt5 53) == "2.23606797749979"

/-! ## `√2/2`, `√3/3`, `√5/5` -/

#guard sqrt2Over2PrecRound 1 .Nearest == (oneHalf, .lt)
#guard sqrt2Over2PrecRound 2 .Nearest == (F "3/4" 2, .gt)
#guard sqrt2Over2PrecRound 53 .Nearest ==
  ((sqrt2PrecRound 53 .Nearest).1 >>> (1 : Nat), (sqrt2PrecRound 53 .Nearest).2)
#guard sqrt2Over2PrecRound 100 .Floor ==
  ((sqrt2PrecRound 100 .Floor).1 >>> (1 : Nat), (sqrt2PrecRound 100 .Floor).2)
#guard toString (sqrt2Over2 53) == "0.7071067811865476"
#guard sqrt3Over3PrecRound 1 .Nearest == (oneHalf, .lt)
#guard sqrt3Over3PrecRound 2 .Nearest == (F "1/2" 2, .lt)
#guard sqrt3Over3PrecRound 3 .Nearest == (F "5/8" 3, .gt)
#guard sqrt3Over3PrecRound 3 .Floor == (F "1/2" 3, .lt)
#guard sqrt5Over5PrecRound 1 .Nearest == (oneHalf, .gt)
#guard sqrt5Over5PrecRound 2 .Nearest == (F "1/2" 2, .gt)
#guard sqrt5Over5PrecRound 3 .Nearest == (F "7/16" 3, .lt)
#guard sqrt5Over5PrecRound 3 .Ceiling == (F "1/2" 3, .gt)

/-! ## The golden ratio -/

#guard phiPrecRound 1 .Nearest == (two, .gt)
#guard phiPrecRound 1 .Floor == (one, .lt)
#guard phiPrecRound 2 .Nearest == (F "3/2" 2, .lt)
#guard phiPrecRound 3 .Nearest == (F "3/2" 3, .lt)
#guard phiPrecRound 3 .Ceiling == (F "7/4" 3, .gt)
#guard phiPrecRound 4 .Nearest == (F "13/8" 4, .gt)
#guard phiPrecRound 4 .Down == (F "3/2" 4, .lt)
#guard toString (phi 53) == "1.618033988749895"
#guard toString (phi 100) == "1.618033988749894848204586834366"
