/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TreeT
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for the tree function: `T₀(x) = −W₀(−x)` and `T₋₁(x) = −W₋₁(−x)`

The special values (`NaN`, `±∞`, `0`, above the branch point `e⁻¹` — including the 53-bit float
nearest `e⁻¹`, which lies above it —, `p = 0`); `T` at `1/4`, `1/8`, `23/64`, `2^(−10)`, `−1`
(minus the omega constant) and `−3` in the three modes at 53 bits and to nearest at 200 bits,
against references from an independent 120-digit Newton iteration on `T e^(−T) = x`; the
relation with `W₀` in every mode; the rational version on the same arguments and on
non-dyadic ones; tiny and huge arguments.  The same for `T₋₁` on `(0, e⁻¹)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := treeT0PrecRound x p m
private def TR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  treeT0RatPrecRound (Q q) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- The 53-bit float nearest `e⁻¹` (above it). -/
private def nearBranch : AzFloat := X "0.36787944117144233" 53
/-- One ulp below `nearBranch`: in the domain. -/
private def belowBranch : AzFloat := X "0.3678794411714423" 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T nan 53) == ("NaN", .eq)
#guard D (T pinf 53) == ("NaN", .eq)
#guard D (T ninf 53) == ("-Infinity", .eq)
#guard D (T zero 53) == ("0.0", .eq)
#guard D (T zero 0) == ("0.0", .eq)
#guard D (T (X "0.25" 53) 0) == ("NaN", .eq)
#guard D (T (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (T (X "1" 53) 53) == ("NaN", .eq)
#guard D (T (X "0.375" 53) 53) == ("NaN", .eq)
#guard D (T nearBranch 53) == ("NaN", .eq)
#guard (T belowBranch 53).1.isFinite
#guard lt (T belowBranch 53).1 one
#guard lt (X "0.99609375" 53) (T belowBranch 53).1

-- 53 bits, three modes
#guard D (T (X "0.25" 53) 53) == ("0.3574029561813889", .lt)
#guard D (T (X "0.25" 53) 53 .Floor) == ("0.3574029561813889", .lt)
#guard D (T (X "0.25" 53) 53 .Ceiling) == ("0.35740295618138895", .gt)
#guard D (T (X "0.125" 53) 53) == ("0.14442135313750973", .lt)
#guard D (T (X "0.125" 53) 53 .Floor) == ("0.14442135313750973", .lt)
#guard D (T (X "0.125" 53) 53 .Ceiling) == ("0.14442135313750976", .gt)
#guard D (T (X "0.359375" 53) 53) == ("0.7990217286464407", .lt)
#guard D (T (X "0.359375" 53) 53 .Floor) == ("0.7990217286464407", .lt)
#guard D (T (X "0.359375" 53) 53 .Ceiling) == ("0.7990217286464408", .gt)
#guard D (T (X "0.0009765625" 53) 53) == ("0.0009775175737302226", .lt)
#guard D (T (X "0.0009765625" 53) 53 .Ceiling) == ("0.0009775175737302228", .gt)
#guard D (T (X "-1" 53) 53) == ("-0.5671432904097838", .gt)
#guard D (T (X "-1" 53) 53 .Floor) == ("-0.567143290409784", .lt)
#guard D (T (X "-1" 53) 53 .Ceiling) == ("-0.5671432904097838", .gt)
#guard D (T (X "-3" 53) 53) == ("-1.04990889496404", .lt)
#guard D (T (X "-3" 53) 53 .Floor) == ("-1.04990889496404", .lt)
#guard D (T (X "-3" 53) 53 .Ceiling) == ("-1.0499088949640398", .gt)

-- 200 bits
#guard toString (T (X "0.25" 53) 200).1 == "0.35740295618138890306881110405590475331659055507601204\
  36276204"
#guard toString (T (X "-1" 53) 200).1 == "-0.567143290409783872999968662210355549753815787186512508\
  135131"
#guard toString (T (X "0.359375" 53) 200).1 == "0.7990217286464407600909312445163833978062321210921\
  44379993086"

-- the relation with `W₀`, every mode
private def viaW (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := lambertW0PrecRound (-x) p (-m)
  T x p m == (-r.1, r.2.swap)
#guard [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
  viaW (X "0.3333333333333333" 53) 80 m && viaW (X "-3.5" 53) 80 m && viaW (X "-0.001" 53) 80 m
-- directed modes bracket the nearest value
#guard le (T (X "0.3333333333333333" 53) 100 .Floor).1 (T (X "0.3333333333333333" 53) 100).1
#guard le (T (X "0.3333333333333333" 53) 100).1 (T (X "0.3333333333333333" 53) 100 .Ceiling).1
#guard T (X "0.3333333333333333" 53) 100 .Down == T (X "0.3333333333333333" 53) 100 .Floor
#guard T (X "-5" 53) 100 .Down == T (X "-5" 53) 100 .Ceiling
#guard T (X "-5" 53) 100 .Up == T (X "-5" 53) 100 .Floor

-- tiny and huge arguments: `T(x) ≈ x + x²` near `0`, `T(x) ≈ −ln(−x)` far out
#guard D (T ((X "1" 53) <<< AzInt.ofInt (-200)) 53) == ("6.223015277861142e-61", .lt)
#guard D (T ((X "-1" 53) <<< AzInt.ofInt (-200)) 53) == ("-6.223015277861142e-61", .lt)
#guard (T ((X "1" 53) <<< AzInt.ofInt (-200)) 53 .Ceiling).2 == .gt
#guard (T ((X "1" 53) <<< AzInt.ofInt (-(2 ^ 40))) 53 .Floor).1
  == (X "1" 53) <<< AzInt.ofInt (-(2 ^ 40))
#guard lt (T ((X "-1" 53) <<< AzInt.ofInt 200) 53).1 (X "-133" 53)
#guard lt (X "-134" 53) (T ((X "-1" 53) <<< AzInt.ofInt 200) 53).1

-- the rational version
#guard D (TR "0" 53) == ("0.0", .eq)
#guard D (TR "0" 0) == ("0.0", .eq)
#guard D (TR "1/4" 0) == ("NaN", .eq)
#guard D (TR "1/2" 53) == ("NaN", .eq)
#guard D (TR "3679/10000" 53) == ("NaN", .eq)
#guard (TR "3678/10000" 53).1.isFinite
#guard TR "1/4" 53 == T (X "0.25" 53) 53
#guard TR "1/4" 53 .Ceiling == T (X "0.25" 53) 53 .Ceiling
#guard TR "-3" 53 .Floor == T (X "-3" 53) 53 .Floor
#guard TR "23/64" 200 == T (X "0.359375" 53) 200
#guard (TR "1/3" 53 .Floor).2 == .lt
#guard (TR "1/3" 53 .Ceiling).2 == .gt
#guard le (TR "1/3" 100 .Floor).1 (TR "1/3" 100).1
#guard lt (T (X "0.3333333333333333" 53) 100).1 (TR "1/3" 100 .Ceiling).1
#guard treeT0Rat (Q "1/4") 53 == (T (X "0.25" 53) 53).1
#guard treeT0Float (X "0.25" 53) == (T (X "0.25" 53) 53).1
#guard toString (treeT0Float nan) == "NaN"

/-! ### The branch `T₋₁` -/

private def Tm (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := treeTm1PrecRound x p m
private def TmR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  treeTm1RatPrecRound (Q q) p m

-- special values
#guard D (Tm nan 53) == ("NaN", .eq)
#guard D (Tm pinf 53) == ("NaN", .eq)
#guard D (Tm ninf 53) == ("NaN", .eq)
#guard D (Tm zero 53) == ("Infinity", .eq)
#guard D (Tm zero 0) == ("Infinity", .eq)
#guard D (Tm (X "0.25" 53) 0) == ("NaN", .eq)
#guard D (Tm (X "-0.25" 53) 53) == ("NaN", .eq)
#guard D (Tm (X "-3" 53) 53) == ("NaN", .eq)
#guard D (Tm (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (Tm nearBranch 53) == ("NaN", .eq)
#guard lt one (Tm belowBranch 53).1
#guard lt (Tm belowBranch 53).1 (X "1.00390625" 53)

-- 53 bits, three modes
#guard D (Tm (X "0.25" 53) 53) == ("2.15329236411035", .gt)
#guard D (Tm (X "0.25" 53) 53 .Floor) == ("2.1532923641103494", .lt)
#guard D (Tm (X "0.25" 53) 53 .Ceiling) == ("2.15329236411035", .gt)
#guard D (Tm (X "0.125" 53) 53) == ("3.2616856845764888", .lt)
#guard D (Tm (X "0.125" 53) 53 .Floor) == ("3.2616856845764888", .lt)
#guard D (Tm (X "0.125" 53) 53 .Ceiling) == ("3.261685684576489", .gt)
#guard D (Tm (X "0.359375" 53) 53) == ("1.2321472314428312", .lt)
#guard D (Tm (X "0.359375" 53) 53 .Ceiling) == ("1.2321472314428314", .gt)
#guard D (Tm (X "0.0009765625" 53) 53) == ("9.144639686625084", .gt)
#guard D (Tm (X "0.0009765625" 53) 53 .Floor) == ("9.144639686625082", .lt)

-- 200 bits
#guard toString (Tm (X "0.25" 53) 200).1 == "2.1532923641103496491690991500929813755362064853194776\
  95884512"
#guard toString (Tm (X "0.0009765625" 53) 200).1 == "9.14463968662508319248836861113583194930933690\
  4039638212432"

-- the relation with `W₋₁`, every mode; the two branches on either side of `1`
private def viaWm (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := lambertWm1PrecRound (-x) p (-m)
  Tm x p m == (-r.1, r.2.swap)
#guard [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
  viaWm (X "0.3333333333333333" 53) 80 m && viaWm (X "0.001" 53) 80 m
#guard lt (T (X "0.3333333333333333" 53) 80).1 one && lt one (Tm (X "0.3333333333333333" 53) 80).1
#guard Tm (X "0.2" 53) 100 .Down == Tm (X "0.2" 53) 100 .Floor
#guard Tm (X "0.2" 53) 100 .Up == Tm (X "0.2" 53) 100 .Ceiling
-- a tiny argument: `T₋₁(x) ≈ ln (1/x) + ln ln (1/x)`
#guard lt (X "143" 53) (Tm ((X "1" 53) <<< AzInt.ofInt (-200)) 53).1
#guard lt (Tm ((X "1" 53) <<< AzInt.ofInt (-200)) 53).1 (X "144" 53)

-- the rational version
#guard D (TmR "0" 53) == ("Infinity", .eq)
#guard D (TmR "0" 0) == ("Infinity", .eq)
#guard D (TmR "1/4" 0) == ("NaN", .eq)
#guard D (TmR "-1/4" 53) == ("NaN", .eq)
#guard D (TmR "1/2" 53) == ("NaN", .eq)
#guard D (TmR "3679/10000" 53) == ("NaN", .eq)
#guard lt one (TmR "3678/10000" 53).1
#guard TmR "1/4" 53 == Tm (X "0.25" 53) 53
#guard TmR "1/4" 53 .Floor == Tm (X "0.25" 53) 53 .Floor
#guard TmR "1/1024" 200 == Tm (X "0.0009765625" 53) 200
#guard (TmR "1/3" 53 .Floor).2 == .lt
#guard (TmR "1/3" 53 .Ceiling).2 == .gt
#guard treeTm1Rat (Q "1/4") 53 == (Tm (X "0.25" 53) 53).1
#guard treeTm1Float (X "0.25" 53) == (Tm (X "0.25" 53) 53).1
#guard toString (treeTm1Float nan) == "NaN"
