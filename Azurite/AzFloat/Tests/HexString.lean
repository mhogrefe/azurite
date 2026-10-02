/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse

/-!
# Tests for the hexadecimal debug format

Expected strings computed by hand from the format's rules.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def H (x : AzFloat) : String := toHexString x
private def RT (x : AzFloat) : Bool := ofHexString (toHexString x) == some x

/-! ## Writing -/

#guard H nan == "NaN"
#guard H posInfinity == "Infinity"
#guard H negInfinity == "-Infinity"
#guard H zero == "0x0.0"
#guard H one == "0x1.0#1"
#guard H (F "1" 10) == "0x1.000#10"
#guard H (F "3/2" 2) == "0x1.8#2"
#guard H (F "-3/2" 2) == "-0x1.8#2"
#guard H (F "1/2" 1) == "0x0.8#1"
#guard H (F "1/2" 5) == "0x0.80#5"
#guard H (F "255" 8) == "0xff.0#8"
#guard toHexString (F "255" 8) true == "0xFF.0#8"
#guard H (F "1000000" 20) == "0xf4240.0#20"
#guard H (F "2469/2" 12) == "0x4d2.8#12"
#guard H (one >>> (17 : Nat)) == "0x0.00008#1"
#guard H (one >>> (10 : Nat)) == "0x0.004#1"
#guard H (one >>> (20 : Nat)) == "0x0.00001#1"
#guard H (one >>> (21 : Nat)) == "0x8.0E-6#1"
#guard H (one <<< (100 : Nat)) == "0x1.0E+25#1"
#guard H (F "617/500000" 53) == "0x0.0050df15a4acf314#53"
#guard H (F "-1126559017/32" 33) == "-0x2192f69.48#33"
#guard H ((F "3/2" 2) <<< (1000000000 : Nat)) == "0x1.8E+250000000#2"
#guard H ((F "3/2" 2) >>> (1000000000 : Nat)) == "0x1.8E-250000000#2"
#guard H (F "65535" 16) == "0xffff.0#16"
#guard H (F "65536" 1) == "0x1.0E+4#1"
#guard H (F "65536" 17) == "0x10000.0#17"
#guard H (F "16" 1) == "0x1.0E+1#1"
#guard H (F "8" 1) == "0x8.0#1"
#guard H (F "1/16" 1) == "0x0.1#1"
#guard H (F "1/16" 4) == "0x0.10#4"
#guard H (F "1/16" 5) == "0x0.10#5"

/-! ## Reading -/

#guard ofHexString "NaN" == some nan
#guard ofHexString "Infinity" == some posInfinity
#guard ofHexString "-Infinity" == some negInfinity
#guard ofHexString "0x0.0" == some zero
#guard ofHexString "0x1.0#1" == some one
#guard ofHexString "0x0.8#5" == some (F "1/2" 5)
#guard ofHexString "0x0.80#5" == some (F "1/2" 5)
#guard ofHexString "0xFF.0#8" == some (F "255" 8)
#guard ofHexString "0x1.8E+250000000#2" == some ((F "3/2" 2) <<< (1000000000 : Nat))
#guard ofHexString "-0x0.0" == none                  -- no negative zero
#guard ofHexString "0x0.0#5" == none                 -- zero carries no precision
#guard ofHexString "0x1.8#1" == none                 -- not representable at precision 1
#guard ofHexString "0x1.0" == none                   -- precision required
#guard ofHexString "0x1.0#0" == none
#guard ofHexString "1.0#1" == none                   -- prefix required
#guard ofHexString "0x1#1" == none                   -- point required
#guard ofHexString "0xg.0#1" == none
#guard ofHexString "" == none

/-! ## Round trips -/

#guard RT nan && RT posInfinity && RT negInfinity && RT zero
#guard RT one && RT (F "1/3" 53) && RT (F "-1/3" 10) && RT (F "22/7" 1)
#guard RT (F "1000000" 20) && RT (F "617/500000" 53) && RT (F "-1126559017/32" 33)
#guard RT (one >>> (17 : Nat)) && RT (one >>> (21 : Nat)) && RT (one <<< (100 : Nat))
#guard RT ((F "3/2" 2) <<< (1000000000 : Nat)) && RT ((F "3/2" 2) >>> (1000000000 : Nat))
#guard RT (F "65536" 1) && RT (F "65536" 17) && RT (F "1/16" 5) && RT (F "8" 1)
