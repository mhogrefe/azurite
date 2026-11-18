/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulAddMulRat
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString

/-!
# Tests for a product plus or minus a product with a rational factor

Expected values computed by hand (the exact `x·y ± z·w`, then one rounding).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (e : Int) : AzFloat := powerOf2 (AzInt.ofInt e)
private def A (x y z : AzFloat) (w : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulAddMulRatPrecRound x y z (Q w) p m
private def S (x y z : AzFloat) (w : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  mulSubMulRatPrecRound x y z (Q w) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Special values -/

#guard D (A nan one one "1/3" 10) == ("NaN", .eq)
#guard D (A one one nan "1/3" 10) == ("NaN", .eq)
#guard D (A zero (infinity true) one "1/3" 10) == ("NaN", .eq) -- 0 · ∞
#guard D (A one one (infinity true) "0" 10) == ("NaN", .eq) -- ∞ · 0
#guard D (A (infinity true) one (infinity true) "-1" 10) == ("NaN", .eq) -- ∞ − ∞
#guard D (S (infinity true) one (infinity true) "1" 10) == ("NaN", .eq) -- ∞ − ∞
#guard D (A (infinity true) one (infinity true) "1" 10) == ("Infinity", .eq)
#guard D (S (infinity true) one (infinity false) "1" 10) == ("Infinity", .eq)
#guard D (A (infinity true) negOne one "1/3" 10) == ("-Infinity", .eq)
#guard D (A one one (infinity false) "-2/3" 10) == ("Infinity", .eq)
#guard D (A zero zero zero "1/3" 10) == ("0.0", .eq)
#guard D (A (X "3" 2) (X "2" 2) (X "-18" 5) "1/3" 10) == ("0.0", .eq)
#guard D (S (X "3" 2) (X "2" 2) (X "18" 5) "1/3" 10) == ("0.0", .eq)
#guard D (A (X "7" 3) one zero "5/3" 10) == ("7.0", .eq)

/-! ## Agreement with the simpler operations -/

#guard A one one (X "3" 2) "1/3" 5 == addRatPrecRound one (Q "1") 5 .Nearest
#guard A (X "3" 2) (X "5" 3) one "7/9" 20 == addRatPrecRound (X "15" 4) (Q "7/9") 20 .Nearest
#guard S (X "3" 2) (X "5" 3) one "7/9" 20 .Floor
  == subRatPrecRound (X "15" 4) (Q "7/9") 20 .Floor

/-! ## Exact results -/

#guard D (A (X "2" 5) (X "3" 5) (X "4" 5) "5/4" 5) == ("11.0", .eq)
#guard D (S (X "2" 5) (X "3" 5) (X "4" 5) "5/4" 5) == ("1.0", .eq)
#guard D (A (X "0.5" 3) (X "0.75" 3) (X "0.75" 3) "5/3" 10) == ("1.625", .eq)
#guard D (S (X "0.5" 3) (X "0.75" 3) (X "0.75" 3) "5/3" 10) == ("-0.875", .eq)

/-! ## One rounding, not two or three -/

-- `x = y = 1 + 2^-52`, `z = −1`, `w = 1 + 2^-51`: `x·y + z·w = 2^-104` exactly; rounding the
-- product first would give `0`.
private def y53 : AzFloat := X "1.0000000000000002" 53   -- 1 + 2^-52
#guard D (A y53 y53 negOne "2251799813685249/2251799813685248" 53) == ("4.930380657631324e-32", .eq)
#guard D (S y53 y53 one "2251799813685249/2251799813685248" 53) == ("4.930380657631324e-32", .eq)
-- rounding tags at 3 bits
#guard D (A (X "0.5" 3) (X "1" 3) (X "0.5" 3) "5/4" 3) == ("1.0", .lt) -- 9/8
#guard D (A (X "0.5" 3) (X "1" 3) (X "0.75" 3) "1" 3) == ("1.2", .eq)
#guard D (A (X "1" 3) (X "1" 3) (X "0.75" 3) "1/4" 3) == ("1.2", .gt) -- 19/16
#guard D (A (X "0.5" 3) (X "1" 3) (X "0.5" 3) "5/4" 3 .Up) == ("1.2", .gt)
#guard D (S (X "1" 3) (X "1" 3) (X "0.5" 3) "1/4" 3) == ("0.9", .eq)
#guard D (S (X "1" 3) (X "1" 3) (X "0.25" 3) "1/4" 3) == ("1.0", .gt) -- 15/16
-- default precisions
#guard toString (mulAddMulRat (X "1" 3) (X "2" 10) (X "3" 5) (Q "4/3")) == "6.0"
#guard toString (mulSubMulRat (X "1" 3) (X "2" 10) (X "3" 5) (Q "4/3")) == "-2.0"

/-! ## `Float` versions -/

private def inf : Float := 1.0 / 0.0
private def eps : Float := 2.0 ^ (-52.0)
#guard toString (mulAddMulRatFloat64 2.0 3.0 4.0 (Q "5/4")) == "11.000000"
#guard toString (mulSubMulRatFloat64 2.0 3.0 4.0 (Q "5/4")) == "1.000000"
#guard toString (mulAddMulRatFloat64 1.0 0.0 1.0 (Q "1/10")) == "0.100000"
#guard mulAddMulRatFloat64 (1.0 + eps) (1.0 + eps) (-1.0) (Q "2251799813685249/2251799813685248")
  == 2.0 ^ (-104.0)
#guard mulSubMulRatFloat64 (1.0 + eps) (1.0 + eps) 1.0 (Q "2251799813685249/2251799813685248")
  == 2.0 ^ (-104.0)
#guard (mulAddMulRatFloat64 0.0 inf 1.0 (Q "1")).isNaN
#guard (mulAddMulRatFloat64 1.0 1.0 inf (Q "0")).isNaN
#guard (mulSubMulRatFloat64 inf 1.0 inf (Q "1")).isNaN
#guard mulAddMulRatFloat64 inf 1.0 inf (Q "1") == inf
#guard mulAddMulRatFloat64 1.0e200 1.0e200 1.0 (Q "1") == inf
#guard toString ((mulSubMulRatFloat64 3.0 2.0 4.0 (Q "3/2")).toBits) == "0" -- exact zero is +0.0
