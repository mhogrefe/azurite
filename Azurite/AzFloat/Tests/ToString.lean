/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the shortest round-tripping decimal output

Expected strings computed by hand from the rule (the nearest `p`-digit decimal must convert
back to the float at its precision); the 53-bit cases agree with the shortest round-trip
renderings of the corresponding `f64` values.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard toString nan == "NaN"
#guard toString posInfinity == "Infinity"
#guard toString negInfinity == "-Infinity"
#guard toString zero == "0.0"
#guard toString one == "1.0"
#guard toString two == "2.0"
#guard toString negOne == "-1.0"
#guard toString oneHalf == "0.5"
#guard toString (F "3/2" 2) == "1.5"
#guard toString (F "-3/2" 2) == "-1.5"
#guard toString (F "255" 8) == "255.0"
#guard toString (F "1000000" 20) == "1.0e6"                  -- one digit suffices
#guard toString (F "1/10" 53) == "0.1"
#guard toString (F "1/3" 53) == "0.3333333333333333"
#guard toString (F "22/7" 53) == "3.142857142857143"
#guard toString (F "1/3" 10) == "0.3335"                     -- 683/2048 at 10 bits
#guard toString (F "1/3" 1) == "0.2"                         -- 1/4 at 1 bit: 0.2 rounds to 1/4
#guard toString (F "22/7" 1) == "4.0"
#guard toString (one <<< (100 : Nat)) == "1.0e30"            -- 2^100 at precision 1
#guard toString (F "1267650600228229401496703205376" 53) == "1.2676506002282294e30"
#guard toString (one >>> (20 : Nat)) == "1.0e-6"             -- 2^-20 at precision 1
#guard toString (one >>> (17 : Nat)) == "8.0e-6"             -- 2^-17 ≈ 7.6e-6 at precision 1
#guard toString (F "617/500000" 53) == "0.001234"
#guard toString (F "18446744073709551616" 65) == "18446744073709551616.0"
#guard shortestDecimalPrecision (F "1/3" 53) == 16
#guard shortestDecimalPrecision (F "1/10" 53) == 1
#guard shortestDecimalPrecision one == 1
#guard shortestDecimalPrecision (F "1/3" 10) == 4
#guard toDecimalAt (F "1/3" 53) 3 == some "0.333"
#guard toDecimalAt (F "1/3" 53) 20 == some "0.33333333333333331483"
#guard toDecimalAt one 3 == some "1.0"
#guard toDecimalAt nan 3 == none
