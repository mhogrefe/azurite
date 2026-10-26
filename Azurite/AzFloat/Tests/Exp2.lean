/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp2
import Azurite.AzFloat.Exp
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `2^x`

Special values, the exact powers of two (`2^10 = 1024`, `2^(−3) = 1/8`, `2^0 = 1`, at any
precision), agreement of `2^(1/2)` with `√2`, the correctly rounded values of `2^(1/2)`,
`2^(3/4)`, `2^(1/1024)`, `2^(201/2)`, `2^(−1/2)`, `2^(−7/4)` and `2^(12345/4096)` (references
from a 120-digit evaluation of `exp (x ln 2)`), the directed modes, and agreement with
`exp (x ln 2)` at a higher precision.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := exp2PrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values
#guard E nan 53 == (nan, .eq)
#guard E pinf 53 == (infinity true, .eq)
#guard E ninf 53 == (zero, .eq)
#guard E zero 53 == (F "1" 53, .eq)
#guard E zero 0 == (nan, .eq)
#guard E (F "1" 53) 0 == (nan, .eq)
#guard exp2 nan == nan
#guard exp2 pinf == infinity true
#guard exp2 ninf == zero
#guard exp2 zero == one

-- exact powers of two
#guard E (F "10" 53) 53 == (F "1024" 53, .eq)
#guard E (F "10" 53) 1 == (F "1024" 1, .eq)
#guard E (F "-3" 53) 53 == (F "1/8" 53, .eq)
#guard E (F "-3" 53) 1 == (F "1/8" 1, .eq)
#guard E (F "1" 53) 10 == (F "2" 10, .eq)
#guard E (F "100" 53) 5 == (F "1267650600228229401496703205376" 5, .eq)
#guard E (F "-100" 53) 5 == (F "1/1267650600228229401496703205376" 5, .eq)
#guard exp2 (F "64" 53) == F "18446744073709551616" 53

private def refHalf : AzRat :=
  R ("1414213562373095048801688724209698078569671875376948073176679737990732478462107038850387" ++
    "53432764157273501384623091229703") 119
private def refThird2 : AzRat :=
  R ("1681792830507429086062250952466429790080068524713569021626452171949849509907804479628648" ++
    "00839858507234560314748703817016") 119
private def refTiny : AzRat :=
  R ("1000677130693066356678172784874647194837821984248737693869604067954757995800310399720395" ++
    "43255696752726563760483930754223") 119
private def refBig : AzRat :=
  R ("1792728671193156477399422023278661496394239222564273688025833797661299920739602714806557" ++
    "82263190056099174776747126665601") 89
private def refNegHalf : AzRat :=
  R ("7071067811865475244008443621048490392848359376884740365883398689953662392310535194251937" ++
    "67163820786367506923115456148512") 120
private def refNeg74 : AzRat :=
  R ("2973017787506802666793749926401189788232430231159543532547505561798666670567292899676953" ++
    "36134534418429009348693692303298") 120
private def refMix : AzRat :=
  R ("8077540144938868974412652508337452940401211922693780486105932056212090027550120554883279" ++
    "30609453188721931465845984318593") 119

-- `2^(1/2) = √2`
#guard E (F "1/2" 53) 150 == sqrt2PrecRound 150 .Nearest
#guard E (F "1/2" 53) 150 .Floor == sqrt2PrecRound 150 .Floor
#guard E (F "1/2" 53) 150 .Ceiling == sqrt2PrecRound 150 .Ceiling
#guard (E (F "1/2" 53) 150).1 == ofAzRat refHalf 150
#guard exp2 (F "1/2" 53) == ofAzRat refHalf 53

-- other dyadic arguments
#guard (E (F "3/4" 53) 150).1 == ofAzRat refThird2 150
#guard E (F "3/4" 53) 150 .Floor == ofAzRatRound refThird2 150 .Floor
#guard E (F "3/4" 53) 150 .Ceiling == ofAzRatRound refThird2 150 .Ceiling
#guard (E (F "1/1024" 53) 150).1 == ofAzRat refTiny 150
#guard (E (F "201/2" 53) 150).1 == ofAzRat refBig 150
#guard E (F "201/2" 53) 150 .Down == ofAzRatRound refBig 150 .Down
#guard (E (F "-1/2" 53) 150).1 == ofAzRat refNegHalf 150
#guard E (F "-1/2" 53) 150 .Up == ofAzRatRound refNegHalf 150 .Up
#guard (E (F "-7/4" 53) 150).1 == ofAzRat refNeg74 150
#guard (E (F "12345/4096" 53) 150).1 == ofAzRat refMix 150
#guard E (F "12345/4096" 53) 100 .Floor == ofAzRatRound refMix 100 .Floor
#guard exp2 (F "-7/4" 53) == ofAzRat refNeg74 53

-- directed modes are ordered
#guard (E (F "5/8" 53) 60 .Floor).2 == .lt
#guard (E (F "5/8" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (F "5/8" 53) 60 .Floor).1 (E (F "5/8" 53) 60 .Ceiling).1 == some .lt

-- agreement with `exp (x ln 2)` at a higher precision
#guard (E (F "7/16" 53) 100).1
  == (expPrecRound (mulPrecRound (F "7/16" 53) (ln2 300) 300 .Nearest).1 100 .Nearest).1
