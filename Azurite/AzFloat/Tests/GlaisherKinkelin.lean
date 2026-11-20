/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GlaisherKinkelin
import Azurite.AzFloat.ToString

/-!
# Tests for the Glaisher–Kinkelin constant

`A = 1.28242 71291 00622 63687 53425 68869 79172 77676 88927 32500 11920 63740 02174 04063 …`
at several precisions and in the directed modes, `p = 0`, the fuel as an argument, the
enclosure of `ln A = 0.24875 44770 33784 26254 …`, the parameters, and the first term
`|t₁| = |B₄|/(2·3·4 n²) = 1/(720 n²)` of the expansion.
-/

open Azurite Azurite.AzFloat

private def A (p : Nat) (m : RoundingMode := .Nearest) := glaisherKinkelinPrecRound p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A 0) == ("NaN", .eq)

-- the constant
#guard D (A 1) == ("1.0", .lt)
#guard D (A 10) == ("1.283", .gt)
#guard D (A 24) == ("1.2824271", .lt)
#guard D (A 53) == ("1.2824271291006226", .lt)
#guard toString (glaisherKinkelin 64) == "1.2824271291006226369"
#guard D (A 113) == ("1.2824271291006226368753425688697916", .lt)
#guard D (A 200)
  == ("1.28242712910062263687534256886979172776768892732500119206374", .gt)
#guard D (A 300) == ("1.28242712910062263687534256886979172776768892732500119206374002174"
  ++ "0406308858826461129736492", .gt)

-- directed modes
#guard D (A 53 .Floor) == ("1.2824271291006226", .lt)
#guard D (A 53 .Ceiling) == ("1.2824271291006228", .gt)
#guard D (A 53 .Down) == ("1.2824271291006226", .lt)
#guard D (A 53 .Up) == ("1.2824271291006228", .gt)

-- the fuel as an argument
#guard D (glaisherKinkelinPrecRoundFuel 0 53 .Nearest) == ("1.2824271291006226", .lt)
#guard glaisherKinkelinPrecRoundFuel (gammaFuel 53) 53 .Nearest == A 53

-- the enclosure of `ln A` at level 64
#guard (toString (glaisherKinkelinLnEncl 64).1, toString (glaisherKinkelinLnEncl 64).2)
  == ("0.248754477033784262547252880566380014758072",
    "0.248754477033784262547252993685096284171692")

-- the parameters: at most `j = ⌊w/12⌋ + 3` terms at `n = 8j`
#guard (glaisherTerms 64, glaisherArg 64, glaisherTerms 1000, glaisherArg 1000)
  == (8, 64, 86, 688)

-- `|t₁| = 1/720` at `n = 1`, from the tangent number `T₂ = 2`
#guard toString (glaisherTermEncl 64 (AzNat.tangentNumbers 2) (Encl.nat 1) 1
  (Encl.exact one)).1 == "0.0013888888888888888887"
