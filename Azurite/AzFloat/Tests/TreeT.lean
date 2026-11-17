/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TreeT
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse

/-!
# Tests for the tree function `T(x) = −W₀(−x)`

The special values (`NaN`, `±∞`, `0`, above the branch point `e⁻¹` — including the 53-bit float
nearest `e⁻¹`, which lies above it —, `p = 0`); `T` at `1/4`, `1/8`, `23/64`, `2^(−10)`, `−1`
(minus the omega constant) and `−3` in the three modes at 53 bits and to nearest at 200 bits,
against references from an independent 120-digit Newton iteration on `T e^(−T) = x`; the
relation with `W₀` in every mode; the rational version on the same arguments and on
non-dyadic ones; tiny and huge arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := treeTPrecRound x p m
private def TR (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  treeTRatPrecRound (Q q) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- The 53-bit float nearest `e⁻¹` (above it). -/
private def nearBranch : AzFloat := F "828390857088487/2251799813685248" 53
/-- One ulp below `nearBranch`: in the domain. -/
private def belowBranch : AzFloat := F "6627126856707895/18014398509481984" 53

-- special values
#guard T nan 53 == (nan, .eq)
#guard T pinf 53 == (nan, .eq)
#guard T ninf 53 == (ninf, .eq)
#guard T zero 53 == (zero, .eq)
#guard T zero 0 == (zero, .eq)
#guard T (F "1/4" 53) 0 == (nan, .eq)
#guard T (F "1/2" 53) 53 == (nan, .eq)
#guard T (F "1" 53) 53 == (nan, .eq)
#guard T (F "3/8" 53) 53 == (nan, .eq)
#guard T nearBranch 53 == (nan, .eq)
#guard (T belowBranch 53).1.isFinite
#guard lt (T belowBranch 53).1 one
#guard lt (F "255/256" 53) (T belowBranch 53).1

-- 53 bits, three modes
#guard T (F "1/4" 53) 53 == (F "6438399281118467/18014398509481984" 53, .lt)
#guard T (F "1/4" 53) 53 .Floor == (F "6438399281118467/18014398509481984" 53, .lt)
#guard T (F "1/4" 53) 53 .Ceiling == (F "1609599820279617/4503599627370496" 53, .gt)
#guard T (F "1/8" 53) 53 == (F "5203327617395453/36028797018963968" 53, .lt)
#guard T (F "1/8" 53) 53 .Floor == (F "5203327617395453/36028797018963968" 53, .lt)
#guard T (F "1/8" 53) 53 .Ceiling == (F "2601663808697727/18014398509481984" 53, .gt)
#guard T (F "23/64" 53) 53 == (F "224904622462065/281474976710656" 53, .lt)
#guard T (F "23/64" 53) 53 .Floor == (F "224904622462065/281474976710656" 53, .lt)
#guard T (F "23/64" 53) 53 .Ceiling == (F "7196947918786081/9007199254740992" 53, .gt)
#guard T (F "1/1024" 53) 53 == (F "4508004127538731/4611686018427387904" 53, .lt)
#guard T (F "1/1024" 53) 53 .Ceiling == (F "1127001031884683/1152921504606846976" 53, .gt)
#guard T (F "-1" 53) 53 == (F "-5108372622710359/9007199254740992" 53, .gt)
#guard T (F "-1" 53) 53 .Floor == (F "-638546577838795/1125899906842624" 53, .lt)
#guard T (F "-1" 53) 53 .Ceiling == (F "-5108372622710359/9007199254740992" 53, .gt)
#guard T (F "-3" 53) 53 == (F "-1182092327033255/1125899906842624" 53, .lt)
#guard T (F "-3" 53) 53 .Floor == (F "-1182092327033255/1125899906842624" 53, .lt)
#guard T (F "-3" 53) 53 .Ceiling == (F "-4728369308133019/4503599627370496" 53, .gt)

-- 200 bits
#guard (T (F "1/4" 53) 200).1 == F ("1148648814837005366403261257571596333520173057029165660978403"
  ++ "/3213876088517980551083924184682325205044405987565585670602752") 200
#guard (T (F "-1" 53) 200).1 == F ("-227841032476426663099079751600042627130329070727104284459813"
  ++ "/401734511064747568885490523085290650630550748445698208825344") 200
#guard (T (F "23/64" 53) 200).1
  == F ("1283978413951549140248550874312079866357971327935468310189845"
    ++ "/1606938044258990275541962092341162602522202993782792835301376") 200

-- the relation with `W₀`, every mode
private def viaW (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := lambertW0PrecRound (-x) p (-m)
  T x p m == (-r.1, r.2.swap)
#guard [RoundingMode.Nearest, .Floor, .Ceiling, .Down, .Up].all fun m =>
  viaW (F "1/3" 53) 80 m && viaW (F "-7/2" 53) 80 m && viaW (F "-1/1000" 53) 80 m
-- directed modes bracket the nearest value
#guard le (T (F "1/3" 53) 100 .Floor).1 (T (F "1/3" 53) 100).1
#guard le (T (F "1/3" 53) 100).1 (T (F "1/3" 53) 100 .Ceiling).1
#guard T (F "1/3" 53) 100 .Down == T (F "1/3" 53) 100 .Floor
#guard T (F "-5" 53) 100 .Down == T (F "-5" 53) 100 .Ceiling
#guard T (F "-5" 53) 100 .Up == T (F "-5" 53) 100 .Floor

-- tiny and huge arguments: `T(x) ≈ x + x²` near `0`, `T(x) ≈ −ln(−x)` far out
#guard T ((F "1" 53) <<< AzInt.ofInt (-200)) 53 == ((F "1" 53) <<< AzInt.ofInt (-200), .lt)
#guard T ((F "-1" 53) <<< AzInt.ofInt (-200)) 53 == ((F "-1" 53) <<< AzInt.ofInt (-200), .lt)
#guard (T ((F "1" 53) <<< AzInt.ofInt (-200)) 53 .Ceiling).2 == .gt
#guard (T ((F "1" 53) <<< AzInt.ofInt (-(2 ^ 40))) 53 .Floor).1
  == (F "1" 53) <<< AzInt.ofInt (-(2 ^ 40))
#guard lt (T ((F "-1" 53) <<< AzInt.ofInt 200) 53).1 (F "-133" 53)
#guard lt (F "-134" 53) (T ((F "-1" 53) <<< AzInt.ofInt 200) 53).1

-- the rational version
#guard TR "0" 53 == (zero, .eq)
#guard TR "0" 0 == (zero, .eq)
#guard TR "1/4" 0 == (nan, .eq)
#guard TR "1/2" 53 == (nan, .eq)
#guard TR "3679/10000" 53 == (nan, .eq)
#guard (TR "3678/10000" 53).1.isFinite
#guard TR "1/4" 53 == T (F "1/4" 53) 53
#guard TR "1/4" 53 .Ceiling == T (F "1/4" 53) 53 .Ceiling
#guard TR "-3" 53 .Floor == T (F "-3" 53) 53 .Floor
#guard TR "23/64" 200 == T (F "23/64" 53) 200
#guard (TR "1/3" 53 .Floor).2 == .lt
#guard (TR "1/3" 53 .Ceiling).2 == .gt
#guard le (TR "1/3" 100 .Floor).1 (TR "1/3" 100).1
#guard lt (T (F "1/3" 53) 100).1 (TR "1/3" 100 .Ceiling).1
#guard treeTRat (Q "1/4") 53 == (T (F "1/4" 53) 53).1
#guard treeTFloat (F "1/4" 53) == (T (F "1/4" 53) 53).1
#guard treeTFloat nan == nan
