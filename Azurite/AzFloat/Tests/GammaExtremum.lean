/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaExtremum
import Azurite.AzFloat.ToString

/-!
# Tests for the local extrema of the Gamma function

`Γ(x₀), …, Γ(x₁₀)` at 53 bits (the fifteen digits of DLMF Table 5.4.1 are their leading
digits; the signs alternate from `n = 1` on), directed modes, other precisions, 200-bit
values, large indices, `p = 0`, the fuel as an argument, and the tight enclosure of a zero.
-/

open Azurite Azurite.AzFloat

private def G (n p : Nat) (m : RoundingMode := .Nearest) := gammaExtremumPrecRound n p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (G 0 0) == ("NaN", .eq)
#guard D (G 5 0) == ("NaN", .eq)

-- `Γ(x₀), …, Γ(x₁₀)`
#guard D (G 0 53) == ("0.8856031944108887", .gt)
#guard D (G 1 53) == ("-3.544643611155005", .gt)
#guard D (G 2 53) == ("2.30240725833968", .lt)
#guard D (G 3 53) == ("-0.8881363584012419", .lt)
#guard D (G 4 53) == ("0.24512753983436625", .lt)
#guard D (G 5 53) == ("-0.0527796395873194", .gt)
#guard D (G 6 53) == ("0.009324594482614851", .gt)
#guard D (G 7 53) == ("-0.0013973966089497673", .lt)
#guard D (G 8 53) == ("0.0001818784449094042", .gt)
#guard D (G 9 53) == ("-0.00002092529044652667", .lt)
#guard D (G 10 53) == ("2.1574161045228504e-6", .lt)

-- directed modes
#guard D (G 0 53 .Floor) == ("0.8856031944108886", .lt)
#guard D (G 0 53 .Ceiling) == ("0.8856031944108887", .gt)
#guard D (G 1 53 .Down) == ("-3.544643611155005", .gt)
#guard D (G 1 53 .Up) == ("-3.5446436111550055", .lt)

-- other precisions
#guard D (G 0 1) == ("1.0", .gt)
#guard D (G 0 200)
  == ("0.8856031944108887002788159005825887332079515336699034488712", .gt)
#guard D (G 3 200)
  == ("-0.8881363584012419200955280293943273785550799259462940202570745", .gt)
#guard toString (gammaExtremum 5 100) == "-0.0527796395873194007604835707629"

-- large indices: between the poles `−n` and `−n + 1` the extremum is of the order of `1/n!`
#guard D (G 1000 53) == ("4.820995856313732e-2567", .lt)
#guard D (G 1001 53) == ("-4.8168333888606693e-2570", .lt)

-- the fuel as an argument
#guard D (gammaExtremumPrecRoundFuel 0 2 53 .Nearest) == ("2.30240725833968", .lt)
#guard gammaExtremumPrecRoundFuel (gammaFuel 53) 4 53 .Nearest == G 4 53

-- the tight enclosure of `x₀`: narrower than `2^(−80)`
#guard (toString (psiZeroEnclAt 0 80).1, toString (psiZeroEnclAt 0 80).2)
  == ("1.4616321449683623412626595420619696240897607",
    "1.46163214496836234126265954248117143384190325")
#guard psiZeroNarrow (psiZeroEnclAt 0 80) 160
#guard (psiZeroTightAt 7 80 80).isSome
