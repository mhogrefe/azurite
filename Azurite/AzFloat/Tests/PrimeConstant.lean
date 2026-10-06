/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.HexString
import Azurite.AzFloat.PrimeConstant
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the prime constant

`ρ = 0.0110 1010 0010 1000 1010 0010 0000 1010…₂ = 0.41468250985111166024810962215…`: bit `n`
is `1` exactly when `n` is prime (`2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, …`).  The low
precisions are rounded by hand from the expansion (the significant bits start at the second
place); the hexadecimal digits read `6a28a20a08a208…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

/-! ## The words -/

#guard wordOfBits (fun l => l = 0 || l = 63) == 0x8000000000000001
#guard wordOfBits (fun _ => true) == 0xFFFFFFFFFFFFFFFF
#guard wordOfBits (fun _ => false) == 0
#guard (primeConstantLimbs 1).limbs == #[0x6a28a20a08a20828]                 -- primes below 64

/-! ## Rounding -/

#guard primeConstantPrecRound 0 .Nearest == (nan, .eq)
#guard primeConstantPrecRound 1 .Nearest == (oneHalf, .gt)                      -- 0.01|1…
#guard primeConstantPrecRound 1 .Floor == (F "1/4" 1, .lt)
#guard primeConstantPrecRound 2 .Nearest == (F "3/8" 2, .lt)                     -- 0.011|0…
#guard primeConstantPrecRound 3 .Nearest == (F "7/16" 3, .gt)                    -- 0.0110|1…
#guard primeConstantPrecRound 3 .Down == (F "3/8" 3, .lt)
#guard primeConstantPrecRound 4 .Nearest == (F "13/32" 4, .lt)                   -- 0.01101|0…
#guard primeConstantPrecRound 5 .Nearest == (F "27/64" 5, .gt)                   -- 0.011010|1…
#guard toHexString (primeConstant 53) == "0x0.6a28a20a08a208#53"
#guard toString (primeConstant 53) == "0.41468250985111166"
#guard (toHexString (primeConstantPrecRound 64 .Floor).1, (primeConstantPrecRound 64 .Floor).2)
  == ("0x0.6a28a20a08a208280#64", .lt)
#guard (toHexString (primeConstantPrecRound 130 .Ceiling).1,
    (primeConstantPrecRound 130 .Ceiling).2)
  == ("0x0.6a28a20a08a20828228220808a2880024#130", .gt)
#guard toString (primeConstant 100) == "0.4146825098511116602481096221542"
