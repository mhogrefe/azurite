/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Bernoulli
import Azurite.AzRat.ToString
import Azurite.AzNat.ToStringBase

/-!
# Tests for the Bernoulli and tangent numbers

`B_0, …, B_20`, `B_30`, `B_50`, `B_100`, `B_120` against values from the defining recurrence
`∑_{k≤n} C(n+1, k) B_k = 0` in exact rational arithmetic (an independent computation); the odd
ones; the table `bernoulliEvens` against the single values; the first tangent numbers.
-/

open Azurite

private def B (n : Nat) : String := toString (AzRat.bernoulli n)
private def T (m : Nat) : List String := (AzNat.tangentNumbers m).toList.map toString

-- tangent numbers
#guard T 0 == []
#guard T 1 == ["1"]
#guard T 2 == ["1", "2"]
#guard T 7 == ["1", "2", "16", "272", "7936", "353792", "22368256"]
#guard (AzNat.tangentNumbers 30).size == 30
-- a longer table agrees with a shorter one
#guard (T 40).take 7 == T 7
#guard (T 40).take 25 == T 25

-- Bernoulli numbers
#guard B 0 == "1"
#guard B 1 == "-1/2"
#guard B 2 == "1/6"
#guard B 3 == "0"
#guard B 4 == "-1/30"
#guard B 5 == "0"
#guard B 6 == "1/42"
#guard B 8 == "-1/30"
#guard B 10 == "5/66"
#guard B 12 == "-691/2730"
#guard B 14 == "7/6"
#guard B 16 == "-3617/510"
#guard B 18 == "43867/798"
#guard B 20 == "-174611/330"
#guard B 30 == "8615841276005/14322"
#guard B 50 == "495057205241079648212477525/66"
#guard B 100 == "-945980378191221252952274330694937218727028415330669361333856962043113954151"
  ++ "97247711/33330"
#guard B 120 == "-515074865350791090618439968578499832740951703532626752130928691671992974749"
  ++ "22985358811329367077682677803282070131/2328255930"
#guard [7, 9, 11, 99, 1001].all fun n => B n == "0"

-- the table of even ones
#guard (AzRat.bernoulliEvens 0).size == 0
#guard (AzRat.bernoulliEvens 10).toList.map toString
  == ["1/6", "-1/30", "1/42", "-1/30", "5/66", "-691/2730", "7/6", "-3617/510", "43867/798",
    "-174611/330"]
#guard (List.range 60).all fun i =>
  toString ((AzRat.bernoulliEvens 60).getD i 0) == B (2 * (i + 1))
-- the pieces
#guard toString (AzRat.bernoulliOfTangent 1 (AzNat.ofNat 1)) == "1/6"
#guard toString (AzRat.bernoulliOfTangent 2 (AzNat.ofNat 2)) == "-1/30"
