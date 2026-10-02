/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for addition and subtraction

Expected values computed by hand (the exact sum or difference, then rounding to the destination
precision).  `H` is the exact hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def H (x : AzFloat) : String := toHexString x
private def A (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  addPrecRound x y p m
private def S (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  subPrecRound x y p m
private def M (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  mulPrecRound x y p m
private def Sq (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrPrecRound x p m
private def D (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  divPrecRound x y p m
private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrtPrecRound x p m

/-! ## Exact cases -/

#guard (A one one 1) == (two, .eq)
#guard (A one one 5) == (F "2" 5, .eq)
#guard (A one oneHalf 2) == (F "3/2" 2, .eq)
#guard (A (F "10" 4) (F "5" 3) 4) == (F "15" 4, .eq)
#guard (A (F "1/3" 53) (F "1/3" 53) 53) == ((F "1/3" 53) <<< (1 : Nat), .eq)      -- doubling
#guard (S (F "3/2" 2) one 2) == (setPrec oneHalf 2, .eq)                           -- Sterbenz
#guard (S one one 5) == (zero, .eq)
#guard (A one negOne 5) == (zero, .eq)
#guard (S (F "1/3" 53) (F "1/3" 53) 53) == (zero, .eq)
#guard (S (F "6" 3) (F "5" 3) 3) == (setPrec one 3, .eq)
#guard (A (F "-10" 4) (F "-5" 3) 4) == (F "-15" 4, .eq)
#guard (A (F "10" 4) (F "-5" 3) 4) == (F "5" 4, .eq)
#guard (A (F "-10" 4) (F "5" 3) 4) == (F "-5" 4, .eq)
#guard (A (F "5" 3) (F "-10" 4) 4) == (F "-5" 4, .eq)

/-! ## Rounded cases -/

#guard (A one oneHalf 1) == (two, .gt)                      -- 1.5 to 1 bit, ties to even
#guard (A one oneHalf 1 .Floor) == (one, .lt)
#guard (A one oneHalf 1 .Down) == (one, .lt)
#guard (A one oneHalf 1 .Up) == (two, .gt)
#guard (A (F "10" 4) (F "5" 3) 3) == (F "16" 3, .gt)        -- 15 to 3 bits
#guard (A (F "10" 4) (F "5" 3) 3 .Floor) == (F "14" 3, .lt)
#guard (A (F "-10" 4) (F "-5" 3) 3) == (F "-16" 3, .lt)
#guard (A (F "-10" 4) (F "-5" 3) 3 .Floor) == (F "-16" 3, .lt)
#guard (A (F "-10" 4) (F "-5" 3) 3 .Ceiling) == (F "-14" 3, .gt)
#guard (A (F "-10" 4) (F "-5" 3) 3 .Down) == (F "-14" 3, .gt)
#guard (S (F "16" 1) one 3) == (F "16" 3, .gt)              -- 15 to 3 bits again
#guard (S (F "16" 1) one 3 .Floor) == (F "14" 3, .lt)
#guard (S (F "16" 1) one 4) == (F "15" 4, .eq)

/-! ## Far operands (sticky-only contribution) -/

#guard (A one (one >>> (100 : Nat)) 53) == (F "1" 53, .lt)
#guard (A one (one >>> (100 : Nat)) 53 .Up) == (F "1" 53 + (one >>> (52 : Nat)), .gt)
#guard H (A one (one >>> (100 : Nat)) 53 .Up).1 == "0x1.0000000000001#53"
#guard (S one (one >>> (100 : Nat)) 53) == (F "1" 53, .gt)
#guard H (S one (one >>> (100 : Nat)) 53 .Floor).1 == "0x0.fffffffffffff8#53"   -- 1 − 2^-53
#guard (S one (one >>> (100 : Nat)) 53 .Floor).2 == .lt
#guard (A (one <<< (1000 : Nat)) one 5) == (setPrec (one <<< (1000 : Nat)) 5, .lt)
#guard (A (one <<< (1000 : Nat)) one 5 .Up).1 == ((F "17" 5) <<< (996 : Nat))
#guard (S (one <<< (1000 : Nat)) one 5) == (setPrec (one <<< (1000 : Nat)) 5, .gt)
#guard (S (one <<< (1000 : Nat)) one 5 .Floor).1 == ((F "31" 5) <<< (995 : Nat))
#guard (S (one <<< (1000 : Nat)) one 5 .Floor).2 == .lt
#guard (A (one >>> (1000 : Nat)) one 5) == (F "1" 5, .lt)                       -- order swapped

/-! ## Special values -/

#guard (A nan one 5).1.isNaN
#guard (A one nan 5).1.isNaN
#guard (A posInfinity negInfinity 5).1.isNaN
#guard (A posInfinity posInfinity 5) == (posInfinity, .eq)
#guard (A negInfinity one 5) == (negInfinity, .eq)
#guard (A one posInfinity 5) == (posInfinity, .eq)
#guard (S posInfinity posInfinity 5).1.isNaN
#guard (S posInfinity negInfinity 5) == (posInfinity, .eq)
#guard (A zero zero 5) == (zero, .eq)
#guard (A zero (F "1/3" 53) 10) == (F "1/3" 10, .gt)                            -- re-rounding
#guard (A (F "1/3" 53) zero 53) == (F "1/3" 53, .eq)
#guard (A one one 0).1.isNaN

/-! ## Instances -/

#guard toString (one + oneHalf) == "2.0"                    -- at precision max 1 1 = 1
#guard toString (F "1" 2 + oneHalf) == "1.5"
#guard toString (F "1/10" 53 + F "1/5" 53) == "0.30000000000000004"
#guard toString (F "3/10" 53 - F "1/10" 53) == "0.19999999999999998"
#guard (F "1" 53 + (one >>> (52 : Nat))).precision? == some 53
#guard toString (F "1" 53 + (one >>> (52 : Nat))) == "1.0000000000000002"
#guard (one - one) == zero
#guard ((F "22/7" 10) + (F "-22/7" 10)) == zero

/-! ## Multiplication -/

#guard (M one one 1) == (one, .eq)
#guard (M two two 5) == (F "4" 5, .eq)
#guard (M (F "3" 2) (F "3" 2) 4) == (F "9" 4, .eq)
#guard (M (F "3" 2) (F "3" 2) 2) == (F "8" 2, .lt)                                 -- 9 → 8
#guard (M (F "3" 2) (F "5" 3) 3) == (F "16" 3, .gt)                                -- 15 tie → 16
#guard (M (F "3" 2) (F "5" 3) 3 .Floor) == (F "14" 3, .lt)
#guard (M (F "1/3" 53) (F "3" 2) 53) == (F "1" 53, .gt)  -- (2^54−1)/2^54 tie
#guard (M (F "1/3" 53) (F "3" 2) 53 .Floor) == (F "9007199254740991/9007199254740992" 53, .lt)
#guard (M negOne (F "3" 2) 2) == (F "-3" 2, .eq)
#guard (M negOne negOne 1) == (one, .eq)
#guard (M (one <<< 1000) (one >>> 999) 1) == (two, .eq)
#guard (M nan one 5) == (nan, .eq)
#guard (M one nan 5) == (nan, .eq)
#guard (M (infinity true) (infinity false) 5) == (infinity false, .eq)
#guard (M (infinity false) (infinity false) 5) == (infinity true, .eq)
#guard (M (infinity true) zero 5) == (nan, .eq)
#guard (M zero (infinity false) 5) == (nan, .eq)
#guard (M (infinity false) negOne 5) == (infinity true, .eq)
#guard (M (F "1/3" 53) (infinity false) 5) == (infinity false, .eq)
#guard (M zero (F "1/3" 53) 5) == (zero, .eq)
#guard (M (F "1/3" 53) zero 5) == (zero, .eq)
#guard (M zero zero 5) == (zero, .eq)

/-! ## Squaring -/

#guard (Sq (F "3" 2) 4) == (F "9" 4, .eq)
#guard (Sq (F "3" 2) 2) == (F "8" 2, .lt)
#guard (Sq (F "3" 2) 2 .Ceiling) == (F "12" 2, .gt)
#guard (Sq negOne 1) == (one, .eq)
#guard (Sq (F "-1/3" 53) 53) == (M (F "-1/3" 53) (F "-1/3" 53) 53)
#guard (Sq (one >>> 500) 1) == (one >>> 1000, .eq)
#guard (Sq (infinity false) 3) == (infinity true, .eq)
#guard (Sq zero 3) == (zero, .eq)
#guard (Sq nan 3) == (nan, .eq)

/-! ## Instances -/

#guard toString (two * two) == "4.0"
#guard toString ((F "3" 2) * (F "5" 3)) == "16.0"
#guard toString (F "1/10" 53 * F "1/10" 53) == "0.010000000000000002"
#guard toString (sqr (F "1/10" 53)) == "0.010000000000000002"
#guard sqr (F "-1/3" 53) == F "-1/3" 53 * F "-1/3" 53

/-! ## Division -/

#guard (D one one 1) == (one, .eq)
#guard (D (F "6" 3) (F "3" 2) 2) == (F "2" 2, .eq)
#guard (D one (F "3" 2) 2) == (F "3/8" 2, .gt)                                      -- 1/3 → 0.375
#guard (D one (F "3" 2) 2 .Floor) == (F "1/4" 2, .lt)
#guard (D one (F "3" 2) 53) == (F "1/3" 53, .lt)
#guard (D (F "1/3" 53) (F "1/3" 53) 53) == (F "1" 53, .eq)
#guard (D two (F "3" 2) 1) == (oneHalf, .lt)                                        -- 2/3 → 1/2
#guard (D (F "7" 3) (F "5" 3) 3) == (F "3/2" 3, .gt)                                -- 1.4 → 1.5
#guard (D (F "5" 3) (F "7" 3) 3) == (F "3/4" 3, .gt)                                -- 0.714 → 0.75
#guard (D (F "1" 100) (F "3" 2) 10) == (F "1/3" 10, .gt)                            -- 683/2048
#guard (D negOne (F "3" 2) 2) == (F "-3/8" 2, .lt)
#guard (D negOne negOne 1) == (one, .eq)
#guard (D (one <<< 1000) (one <<< 999) 1) == (two, .eq)
#guard (D one (one <<< 1000) 1) == (one >>> 1000, .eq)
#guard (D nan one 5) == (nan, .eq)
#guard (D one nan 5) == (nan, .eq)
#guard (D (infinity true) (infinity false) 5) == (nan, .eq)
#guard (D (infinity false) one 5) == (infinity false, .eq)
#guard (D (infinity false) negOne 5) == (infinity true, .eq)
#guard (D (infinity true) zero 5) == (infinity true, .eq)
#guard (D one zero 5) == (infinity true, .eq)
#guard (D negOne zero 5) == (infinity false, .eq)
#guard (D zero zero 5) == (nan, .eq)
#guard (D zero one 5) == (zero, .eq)
#guard (D zero (infinity true) 5) == (zero, .eq)
#guard (D one (infinity false) 5) == (zero, .eq)
#guard toString (one / F "3" 2) == "0.4"
#guard toString (F "1" 53 / F "3" 53) == "0.3333333333333333"
#guard toString (F "22" 53 / F "7" 53) == "3.142857142857143"

/-! ## Square root -/

#guard (R one 1) == (one, .eq)
#guard (R (F "4" 3) 2) == (F "2" 2, .eq)
#guard (R (F "9/4" 4) 2) == (F "3/2" 2, .eq)
#guard (R (F "2" 2) 2) == (F "3/2" 2, .gt)                                          -- √2 → 1.5
#guard (R (F "2" 2) 2 .Floor) == (F "1" 2, .lt)
#guard (R (F "2" 2) 53) == (F "6369051672525773/4503599627370496" 53, .gt)
#guard (R (F "1/4" 2) 1) == (oneHalf, .eq)
#guard (R (one <<< 100) 1) == (one <<< 50, .eq)
#guard (R (one <<< 101) 1) == (one <<< 50, .lt)                                     -- √2·2^50
#guard (R (one <<< 101) 1 .Ceiling) == (one <<< 51, .gt)
#guard (R (F "9/4" 4) 1) == (two, .gt)                                              -- tie 1.5 → 2
#guard (R (F "25/4" 5) 2) == (F "2" 2, .lt)                                         -- tie 2.5 → 2
#guard (R nan 3) == (nan, .eq)
#guard (R (infinity true) 3) == (infinity true, .eq)
#guard (R (infinity false) 3) == (nan, .eq)
#guard (R zero 3) == (zero, .eq)
#guard (R negOne 3) == (nan, .eq)
#guard toString (sqrt (F "2" 53)) == "1.4142135623730951"
#guard toString (sqrt (F "1/10" 53)) == "0.31622776601683794"

/-! ## Rounding an unreduced fraction -/

#guard (ofFractionRound true (AzNat.ofNat 2) (AzNat.ofNat 6) 53 .Nearest).1 == F "1/3" 53
#guard (ofFractionRound false (AzNat.ofNat 10) (AzNat.ofNat 30) 2 .Nearest).1 == F "-1/3" 2
#guard (ofFractionRound true (AzNat.ofNat 12) (AzNat.ofNat 4) 5 .Nearest) == (F "3" 5, .eq)
#guard (ofFractionRound true (AzNat.ofNat 0) (AzNat.ofNat 4) 5 .Nearest) == (zero, .eq)
#guard (ofFractionRound true (AzNat.ofNat 1) (AzNat.ofNat 10) 53 .Nearest).1 == F "1/10" 53
#guard (ofFractionRound true (AzNat.ofNat 7) (AzNat.ofNat 5) 3 .Floor) == (F "5/4" 3, .lt)
