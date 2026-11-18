/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for the real branches of the Lambert `W` function

The special values (`NaN`, `±∞`, `0`, below the branch point — including the 53-bit float nearest
`−e⁻¹`, which lies below it —, `p = 0`), `W₀` on positive floats (`1/2`, `1` (the omega
constant), `3`, `10¹⁰`, `2^±100`, `1/3`, `5/2`) and on `(−e⁻¹, 0)`, `W₋₁` on `(−e⁻¹, 0)`
(`−1/10`, `−9/25`, `−1/4`, `−2^(−100)`, `−1/8`, `−1/1000`, `−0.3678`), the float one ulp above
the 53-bit float nearest `−e⁻¹` (`q = 1 + e x ≈ 1.17·10⁻¹⁶`, both branches), all in the three
modes with 120-digit references at the exact float arguments, and 200-bit values.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W0 (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := lambertW0PrecRound x p m
private def Wm (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  lambertWm1PrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- The 53-bit float nearest `−e⁻¹` (below it). -/
private def nearBranch : AzFloat := X "-0.36787944117144233" 53
/-- One ulp above `nearBranch`: in the domain, `q ≈ 1.17·10⁻¹⁶`. -/
private def aboveBranch (p : Nat) : AzFloat :=
  X "-0.367879441171442278513126211691997013986110687255859375" p
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W0 nan 53) == ("NaN", .eq)
#guard D (W0 pinf 53) == ("Infinity", .eq)
#guard D (W0 ninf 53) == ("NaN", .eq)
#guard D (W0 zero 53) == ("0.0", .eq)
#guard D (W0 (X "-1" 53) 53) == ("NaN", .eq)
#guard D (W0 (X "-0.5" 53) 53) == ("NaN", .eq)
#guard D (W0 nearBranch 53) == ("NaN", .eq)
#guard D (W0 (X "1" 53) 0) == ("NaN", .eq)
#guard D (W0 zero 0) == ("0.0", .eq)
#guard D (Wm nan 53) == ("NaN", .eq)
#guard D (Wm pinf 53) == ("NaN", .eq)
#guard D (Wm ninf 53) == ("NaN", .eq)
#guard D (Wm zero 53) == ("-Infinity", .eq)
#guard D (Wm (X "1" 53) 53) == ("NaN", .eq)
#guard D (Wm (X "-1" 53) 53) == ("NaN", .eq)
#guard D (Wm nearBranch 53) == ("NaN", .eq)
#guard D (Wm (X "-0.25" 53) 0) == ("NaN", .eq)
#guard D (Wm zero 0) == ("-Infinity", .eq)

-- `W₀`, `x > 0`
#guard D (W0 (X "0.5" 53) 53) == ("0.35173371124919584", .gt)
#guard D (W0 (X "0.5" 53) 53 .Floor) == ("0.3517337112491958", .lt)
#guard D (W0 (X "1" 53) 53) == ("0.5671432904097838", .lt)
#guard D (W0 (X "1" 53) 53 .Ceiling) == ("0.567143290409784", .gt)
#guard D (W0 (X "3" 53) 53) == ("1.04990889496404", .gt)
#guard D (W0 (X "3" 53) 53 .Floor) == ("1.0499088949640398", .lt)
#guard D (W0 (X "10000000000" 53) 53) == ("20.028685413304952", .gt)
#guard D (W0 (X "1267650600228229401496703205376" 53) 53) == ("65.13820678515364", .lt)
#guard D (W0 (X "1267650600228229401496703205376" 53) 53 .Ceiling) == ("65.13820678515366", .gt)
#guard D (W0 (X "7.888609052210118e-31" 53) 53) == ("7.888609052210118e-31", .gt)
#guard D (W0 (X "7.888609052210118e-31" 53) 53 .Floor) == ("7.888609052210117e-31", .lt)
#guard D (W0 (X "0.3333333333333333" 53) 53) == ("0.25762765304973667", .lt)
#guard D (W0 (X "2.5" 53) 53) == ("0.958586356728703", .gt)

-- `W₀`, `−e⁻¹ < x < 0`
#guard D (W0 (X "-0.1" 53) 53) == ("-0.11183255915896297", .gt)
#guard D (W0 (X "-0.1" 53) 53 .Floor) == ("-0.11183255915896298", .lt)
#guard D (W0 (X "-0.36" 53) 53) == ("-0.8060843159708176", .lt)
#guard D (W0 (X "-0.36" 53) 53 .Ceiling) == ("-0.8060843159708175", .gt)
#guard D (W0 (X "-0.25" 53) 53) == ("-0.3574029561813889", .gt)
#guard D (W0 (X "-7.888609052210118e-31" 53) 53) == ("-7.888609052210118e-31", .gt)
#guard D (W0 (X "-0.125" 53) 53) == ("-0.14442135313750973", .gt)
#guard D (W0 (X "-0.001" 53) 53) == ("-0.001001001502671886", .lt)
#guard D (W0 (X "-0.3678" 53) 53) == ("-0.9793607149578305", .gt)
#guard D (W0 (aboveBranch 53) 53) == ("-0.9999999846957459", .lt)
#guard D (W0 (aboveBranch 53) 53 .Ceiling) == ("-0.9999999846957458", .gt)

-- `W₋₁`
#guard D (Wm (X "-0.1" 53) 53) == ("-3.577152063957297", .gt)
#guard D (Wm (X "-0.1" 53) 53 .Floor) == ("-3.5771520639572976", .lt)
#guard D (Wm (X "-0.36" 53) 53) == ("-1.2227701339785062", .lt)
#guard D (Wm (X "-0.36" 53) 53 .Ceiling) == ("-1.222770133978506", .gt)
#guard D (Wm (X "-0.25" 53) 53) == ("-2.15329236411035", .lt)
#guard D (Wm (X "-7.888609052210118e-31" 53) 53) == ("-73.61354712904495", .lt)
#guard D (Wm (X "-7.888609052210118e-31" 53) 53 .Ceiling) == ("-73.61354712904493", .gt)
#guard D (Wm (X "-0.125" 53) 53) == ("-3.2616856845764888", .gt)
#guard D (Wm (X "-0.001" 53) 53) == ("-9.11800647040274", .lt)
#guard D (Wm (X "-0.3678" 53) 53) == ("-1.0209272394094255", .lt)
#guard D (Wm (aboveBranch 53) 53) == ("-1.0000000153042543", .lt)
#guard D (Wm (aboveBranch 53) 53 .Ceiling) == ("-1.000000015304254", .gt)

-- 200 bits
#guard D (W0 (X "1" 200) 200)
  == ("0.567143290409783872999968662210355549753815787186512508135131", .gt)
#guard D (Wm (X "-0.25" 200) 200)
  == ("-2.153292364110349649169099150092981375536206485319477695884512", .lt)
#guard D (W0 (aboveBranch 200) 200)
  == ("-0.999999984695745871504828693939342150717749770893783964214804", .gt)
#guard D (Wm (aboveBranch 200) 200)
  == ("-1.000000015304254284641969185575173803269239102042638319966135", .gt)

-- the nearest wrappers and the omega constant
#guard lambertW0Float (X "1" 53) == (W0 (X "1" 53) 53).1
#guard lambertWm1Float (X "-0.25" 53) == (Wm (X "-0.25" 53) 53).1
#guard toString (lambertW0Float (X "1" 200))
  == "0.567143290409783872999968662210355549753815787186512508135131"

-- tiny arguments of `W₀` (`W₀ x = x − x² + ⋯`): rounded by one test, at a cost independent of
-- the exponent (the Ziv loop would need about `|e|` bits to see the side of `x`)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def third200 : AzFloat := (X "0.3333333333333333" 53) <<< AzInt.ofInt (-200)
#guard W0 tinyX 53 == (tinyX, .gt)
#guard W0 tinyX 53 .Ceiling == (tinyX, .gt)
#guard (W0 tinyX 53 .Floor).2 == .lt
#guard (W0 tinyX 53 .Floor).1 != tinyX
#guard W0 (-tinyX) 53 .Ceiling == (-tinyX, .gt)
#guard (W0 (-tinyX) 53).2 == .gt
#guard W0 ((X "1.5" 100) <<< tinyE) 53 == ((X "1.5" 53) <<< tinyE, .gt)
#guard lambertW0Float tinyX == tinyX
#guard D (W0 third200 53) == ("2.0743384259537138e-61", .gt)
#guard D (W0 third200 53 .Floor) == ("2.0743384259537134e-61", .lt)
#guard D (W0 (-third200) 53) == ("-2.0743384259537138e-61", .gt)
#guard D (W0 (-third200) 53 .Floor) == ("-2.074338425953714e-61", .lt)

-- huge arguments of `W₀` and arguments of `W₋₁` near `0⁻`, far outside the `Float` range
-- (references: the root of `w + ln |w| = ln |x|` at 80 digits)
#guard D (W0 ((X "1" 53) <<< AzInt.ofInt (2 ^ 30)) 53) == ("744261097.5269905", .lt)
#guard D (W0 ((X "1" 53) <<< AzInt.ofInt (2 ^ 62)) 53) == ("3.196577161300664e18", .lt)
#guard D (Wm ((X "-1" 53) <<< tinyE) 53) == ("-744261138.3827956", .lt)
#guard D (Wm ((X "-1" 53) <<< AzInt.ofInt (-(2 ^ 62 : Int))) 53) == ("-3.196577161300664e18", .gt)

-- precisions at which the Halley refinement used to take its last step too early (the working
-- precision `p + 74` divisible by `2^⌊lg ((p + 74)/64)⌋`), sending the bracket to the
-- bisection fallback (about a thousand times slower; the values were right)
private def consistent (x : AzFloat) (p : Nat) : Bool :=
  let f := W0 x p .Floor
  let c := W0 x p .Ceiling
  let n := W0 x p
  f.2 == .lt && c.2 == .gt && le f.1 n.1 && le n.1 c.1 && lt f.1 c.1
#guard [86, 100, 120, 150, 182, 310, 438].all fun p => consistent (X "0.3333333333333333" 53) p
#guard [100, 120, 310].all fun p => consistent (X "-0.3333333333333333" 53) p
#guard [100, 120].all fun p =>
  (Wm (X "-0.3333333333333333\
    " 53) p .Floor).2 == .lt && (Wm (X "-0.3333333333333333" 53) p .Ceiling).2 == .gt

-- arguments in the subnormal range of `Float` (the `Float` seed is not used there) and
-- arguments with huge exponents (`|W| ≈ 2^78`: more integer bits than the working precision
-- of a 3-bit request); both used to end in the bisection fallback
private def nat (n : Nat) : AzFloat := ofAzNat (AzNat.ofNat n)
private def sub268 : AzFloat := -((nat 0x62dc507e392e14) <<< AzInt.ofInt (-1124))
private def dirOk (f : RoundingMode → AzFloat × Ordering) : Bool :=
  (f .Floor).2 == .lt && (f .Ceiling).2 == .gt && le (f .Floor).1 (f .Nearest).1
    && le (f .Nearest).1 (f .Ceiling).1 && lt (f .Floor).1 (f .Ceiling).1
#guard dirOk fun m => Wm sub268 93 m
#guard dirOk fun m => Wm sub268 53 m
#guard toString (Wm sub268 53).1 == "-747.849857705648"
#guard dirOk fun m => Wm (-((nat 3) <<< AzInt.ofInt (-1074))) 53 m
#guard dirOk fun m => W0 (one <<< AzInt.ofInt (2 ^ 78)) 3 m
#guard dirOk fun m => W0 (one <<< AzInt.ofInt (2 ^ 78)) 53 m
#guard dirOk fun m => W0 (one <<< AzInt.ofInt (2 ^ 200)) 3 m
#guard dirOk fun m => Wm (-(one <<< AzInt.ofInt (-(2 ^ 78)))) 3 m
#guard dirOk fun m => Wm (-(one <<< AzInt.ofInt (-(2 ^ 200)))) 53 m
-- `W₀ (2^(2^78)) ≈ 2^78 ln 2 − ln (2^78 ln 2)`: between `2^77` and `2^78`
#guard (W0 (one <<< AzInt.ofInt (2 ^ 78)) 53).1.exponent? == some (AzInt.ofInt 78)
#guard toString (expSize (one <<< AzInt.ofInt (2 ^ 78))) == "79"
#guard toString (lambertIntBits (nat 1000, nat 1001)) == "10"
#guard toString (lambertIntBits (X "0.25" 53, X "0.5" 53)) == "0"

-- the top of the `Float` range (the `Float` seed is not used above `2^1000`): the 53-bit
-- result is the rounding of the 200-bit one; `W₀ (3·2^1022) ≈ 703.0`
#guard [990, 1010, 1021, 1022, 1023].all fun k =>
  let x := (nat 3) <<< AzInt.ofInt k
  dirOk (fun m => W0 x 53 m) && (W0 x 53).1 == (setPrecRound (W0 x 200).1 53 .Nearest).1
#guard toString (W0 ((nat 3) <<< AzInt.ofInt 1022) 53).1 == "702.9397596232295"
#guard (seedFloat true ((nat 3) <<< AzInt.ofInt 1022)).isNone
#guard (seedFloat true ((nat 3) <<< AzInt.ofInt 990)).isSome
