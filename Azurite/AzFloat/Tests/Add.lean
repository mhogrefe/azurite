/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for addition and subtraction

Expected values computed by hand (the exact sum or difference, then rounding to the destination
precision), shown as decimal output.  `H` is the exact hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def H (x : AzFloat) : String := toHexString x

private def A (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  addPrecRound x y p m

private def S (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  subPrecRound x y p m

/-! ## Exact cases -/

#guard D (A one one 1) == ("2.0", .eq)
#guard D (A one one 5) == ("2.0", .eq)
#guard D (A one oneHalf 2) == ("1.5", .eq)
#guard D (A (X "10" 4) (X "5" 3) 4) == ("15.0", .eq)
#guard D (A (X "0.3333333333333333" 53) (X "0.3333333333333333" 53) 53)
  == ("0.6666666666666666", .eq)  -- doubling
#guard D (S (X "1.5" 2) one 2) == ("0.5", .eq)  -- Sterbenz
#guard D (S one one 5) == ("0.0", .eq)
#guard D (A one negOne 5) == ("0.0", .eq)
#guard D (S (X "0.3333333333333333" 53) (X "0.3333333333333333" 53) 53) == ("0.0", .eq)
#guard D (S (X "6" 3) (X "5" 3) 3) == ("1.0", .eq)
#guard D (A (X "-10" 4) (X "-5" 3) 4) == ("-15.0", .eq)
#guard D (A (X "10" 4) (X "-5" 3) 4) == ("5.0", .eq)
#guard D (A (X "-10" 4) (X "5" 3) 4) == ("-5.0", .eq)
#guard D (A (X "5" 3) (X "-10" 4) 4) == ("-5.0", .eq)

/-! ## Rounded cases -/

#guard D (A one oneHalf 1) == ("2.0", .gt)  -- 1.5 to 1 bit, ties to even
#guard D (A one oneHalf 1 .Floor) == ("1.0", .lt)
#guard D (A one oneHalf 1 .Down) == ("1.0", .lt)
#guard D (A one oneHalf 1 .Up) == ("2.0", .gt)
#guard D (A (X "10" 4) (X "5" 3) 3) == ("16.0", .gt)  -- 15 to 3 bits
#guard D (A (X "10" 4) (X "5" 3) 3 .Floor) == ("14.0", .lt)
#guard D (A (X "-10" 4) (X "-5" 3) 3) == ("-16.0", .lt)
#guard D (A (X "-10" 4) (X "-5" 3) 3 .Floor) == ("-16.0", .lt)
#guard D (A (X "-10" 4) (X "-5" 3) 3 .Ceiling) == ("-14.0", .gt)
#guard D (A (X "-10" 4) (X "-5" 3) 3 .Down) == ("-14.0", .gt)
#guard D (S (X "16" 1) one 3) == ("16.0", .gt)  -- 15 to 3 bits again
#guard D (S (X "16" 1) one 3 .Floor) == ("14.0", .lt)
#guard D (S (X "16" 1) one 4) == ("15.0", .eq)

/-! ## Far operands (sticky-only contribution) -/

#guard D (A one (one >>> (100 : Nat)) 53) == ("1.0", .lt)
#guard D (A one (one >>> (100 : Nat)) 53 .Up) == ("1.0000000000000002", .gt)
#guard H (A one (one >>> (100 : Nat)) 53 .Up).1 == "0x1.0000000000001#53"
#guard D (S one (one >>> (100 : Nat)) 53) == ("1.0", .gt)
#guard H (S one (one >>> (100 : Nat)) 53 .Floor).1 == "0x0.fffffffffffff8#53"   -- 1 − 2^-53
#guard (S one (one >>> (100 : Nat)) 53 .Floor).2 == .lt
#guard D (A (one <<< (1000 : Nat)) one 5) == ("1.1e301", .lt)
#guard toString ((A (one <<< (1000 : Nat)) one 5 .Up).1) == "1.14e301"
#guard D (S (one <<< (1000 : Nat)) one 5) == ("1.1e301", .gt)
#guard toString ((S (one <<< (1000 : Nat)) one 5 .Floor).1) == "1.04e301"
#guard (S (one <<< (1000 : Nat)) one 5 .Floor).2 == .lt
#guard D (A (one >>> (1000 : Nat)) one 5) == ("1.0", .lt)  -- order swapped

/-! ## Special values -/

#guard (A nan one 5).1.isNaN
#guard (A one nan 5).1.isNaN
#guard (A posInfinity negInfinity 5).1.isNaN
#guard D (A posInfinity posInfinity 5) == ("Infinity", .eq)
#guard D (A negInfinity one 5) == ("-Infinity", .eq)
#guard D (A one posInfinity 5) == ("Infinity", .eq)
#guard (S posInfinity posInfinity 5).1.isNaN
#guard D (S posInfinity negInfinity 5) == ("Infinity", .eq)
#guard D (A zero zero 5) == ("0.0", .eq)
#guard D (A zero (X "0.3333333333333333" 53) 10) == ("0.3335", .gt)  -- re-rounding
#guard D (A (X "0.3333333333333333" 53) zero 53) == ("0.3333333333333333", .eq)
#guard (A one one 0).1.isNaN

/-! ## Instances -/

#guard toString (one + oneHalf) == "2.0"                    -- at precision max 1 1 = 1
#guard toString (X "1" 2 + oneHalf) == "1.5"
#guard toString (X "0.1" 53 + X "0.2" 53) == "0.30000000000000004"
#guard toString (X "0.3" 53 - X "0.1" 53) == "0.19999999999999998"
#guard (X "1" 53 + (one >>> (52 : Nat))).precision? == some 53
#guard toString (X "1" 53 + (one >>> (52 : Nat))) == "1.0000000000000002"
#guard toString (one - one) == "0.0"
#guard toString ((X "3.145" 10) + (X "-3.145" 10)) == "0.0"
