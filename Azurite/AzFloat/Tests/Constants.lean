/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Phi
import Azurite.AzFloat.HexString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for the constants

`√2 = 1.4142135623730950488…`; its binary64 significand is `0x6a09e667f3bcd`, and that value
lies above `√2` (`1.41421356237309514…`).  The low-precision cases are rounded by hand from
`√3 = 1.7320508…`, `√5 = 2.2360679…`, `√2/2 = 0.7071067…`, `√3/3 = 0.5773502…`,
`√5/5 = 0.4472135…`, `φ = 1.6180339…`; the 53-bit decimals are the familiar binary64 values.
`√2/2` must agree with `√2` shifted, since the shift is exact.
-/

open Azurite Azurite.AzFloat


/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (sqrt2PrecRound 1 .Nearest) == ("1.0", .lt)
#guard D (sqrt2PrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (sqrt2PrecRound 2 .Nearest) == ("1.5", .gt)
#guard D (sqrt2PrecRound 2 .Floor) == ("1.0", .lt)
#guard D (sqrt2PrecRound 53 .Nearest) == ("1.4142135623730951", .gt)
#guard D (sqrt2PrecRound 53 .Ceiling) == ("1.4142135623730951", .gt)
#guard D (sqrt2PrecRound 53 .Floor) == ("1.414213562373095", .lt)
#guard toHexString (sqrt2 53) == "0x1.6a09e667f3bcd#53"
#guard toHexString (sqrt2PrecRound 53 .Floor).1 == "0x1.6a09e667f3bcc#53"
#guard toString (sqrt2 53) == "1.4142135623730951"
#guard toString (sqrt2 100) == "1.414213562373095048801688724209"

/-! ## `√3`, `√5` -/

#guard D (cbrt2PrecRound 1 .Nearest) == ("1.0", .lt)
#guard D (cbrt2PrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (cbrt2PrecRound 2 .Nearest) == ("1.5", .gt)
#guard D (cbrt2PrecRound 2 .Floor) == ("1.0", .lt)
#guard D (cbrt2PrecRound 3 .Nearest) == ("1.2", .lt)
#guard D (cbrt2PrecRound 53 .Nearest) == ("1.2599210498948732", .gt)
#guard D (cbrt2PrecRound 53 .Ceiling) == ("1.2599210498948732", .gt)
#guard D (cbrt2PrecRound 53 .Floor) == ("1.259921049894873", .lt)
#guard D (cbrt2PrecRound 0 .Nearest) == ("NaN", .eq)
#guard toHexString (cbrt2 53) == "0x1.428a2f98d728b#53"
#guard toString (cbrt2 53) == "1.2599210498948732"
#guard cbrt2 100 == cbrt (X "2" 100)
#guard D (sqrt3PrecRound 2 .Nearest) == ("1.5", .lt)
#guard D (sqrt3PrecRound 3 .Nearest) == ("1.8", .gt)
#guard D (sqrt3PrecRound 3 .Floor) == ("1.5", .lt)
#guard toString (sqrt3 53) == "1.7320508075688772"
#guard D (sqrt5PrecRound 2 .Nearest) == ("2.0", .lt)
#guard D (sqrt5PrecRound 3 .Nearest) == ("2.0", .lt)
#guard D (sqrt5PrecRound 4 .Nearest) == ("2.2", .gt)
#guard D (sqrt5PrecRound 4 .Down) == ("2.0", .lt)
#guard toString (sqrt5 53) == "2.23606797749979"

/-! ## `√2/2`, `√3/3`, `√5/5` -/

#guard D (sqrt2Over2PrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (sqrt2Over2PrecRound 2 .Nearest) == ("0.8", .gt)
#guard sqrt2Over2PrecRound 53 .Nearest ==
  ((sqrt2PrecRound 53 .Nearest).1 >>> (1 : Nat), (sqrt2PrecRound 53 .Nearest).2)
#guard sqrt2Over2PrecRound 100 .Floor ==
  ((sqrt2PrecRound 100 .Floor).1 >>> (1 : Nat), (sqrt2PrecRound 100 .Floor).2)
#guard toString (sqrt2Over2 53) == "0.7071067811865476"
#guard D (sqrt3Over3PrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (sqrt3Over3PrecRound 2 .Nearest) == ("0.5", .lt)
#guard D (sqrt3Over3PrecRound 3 .Nearest) == ("0.6", .gt)
#guard D (sqrt3Over3PrecRound 3 .Floor) == ("0.5", .lt)
#guard D (sqrt5Over5PrecRound 1 .Nearest) == ("0.5", .gt)
#guard D (sqrt5Over5PrecRound 2 .Nearest) == ("0.5", .gt)
#guard D (sqrt5Over5PrecRound 3 .Nearest) == ("0.44", .lt)
#guard D (sqrt5Over5PrecRound 3 .Ceiling) == ("0.5", .gt)

/-! ## The golden ratio -/

#guard D (phiPrecRound 0 .Nearest) == ("NaN", .eq)

#guard D (phiPrecRound 1 .Nearest) == ("2.0", .gt)
#guard D (phiPrecRound 1 .Floor) == ("1.0", .lt)
#guard D (phiPrecRound 2 .Nearest) == ("1.5", .lt)
#guard D (phiPrecRound 3 .Nearest) == ("1.5", .lt)
#guard D (phiPrecRound 3 .Ceiling) == ("1.8", .gt)
#guard D (phiPrecRound 4 .Nearest) == ("1.6", .gt)
#guard D (phiPrecRound 4 .Down) == ("1.5", .lt)
#guard toString (phi 53) == "1.618033988749895"
#guard toString (phi 100) == "1.618033988749894848204586834366"
