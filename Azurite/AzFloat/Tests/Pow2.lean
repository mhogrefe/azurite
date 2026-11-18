/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Constants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Exp
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.Pow2
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- The rational `digits / 10^zeros`. -/
private def R (digits : String) (zeros : Nat) : AzRat := Q (digits ++ "/1" ++ "".pushn '0' zeros)
private def E (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := pow2PrecRound x p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E nan 53) == ("NaN", .eq)
#guard D (E pinf 53) == ("Infinity", .eq)
#guard D (E ninf 53) == ("0.0", .eq)
#guard D (E zero 53) == ("1.0", .eq)
#guard D (E zero 0) == ("NaN", .eq)
#guard D (E (X "1" 53) 0) == ("NaN", .eq)
#guard toString (pow2 nan) == "NaN"
#guard toString (pow2 pinf) == "Infinity"
#guard toString (pow2 ninf) == "0.0"
#guard toString (pow2 zero) == "1.0"

-- exact powers of two
#guard D (E (X "10" 53) 53) == ("1024.0", .eq)
#guard D (E (X "10" 53) 1) == ("1.0e3", .eq)
#guard D (E (X "-3" 53) 53) == ("0.125", .eq)
#guard D (E (X "-3" 53) 1) == ("0.1", .eq)
#guard D (E (X "1" 53) 10) == ("2.0", .eq)
#guard D (E (X "100" 53) 5) == ("1.3e30", .eq)
#guard D (E (X "-100" 53) 5) == ("8.0e-31", .eq)
#guard toString (pow2 (X "64" 53)) == "1.8446744073709552e19"

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
#guard E (X "0.5" 53) 150 == sqrt2PrecRound 150 .Nearest
#guard E (X "0.5" 53) 150 .Floor == sqrt2PrecRound 150 .Floor
#guard E (X "0.5" 53) 150 .Ceiling == sqrt2PrecRound 150 .Ceiling
#guard toString (E (X "0.5" 53) 150).1 == "1.414213562373095048801688724209698078569671875"
#guard toString (pow2 (X "0.5" 53)) == "1.4142135623730951"

-- other dyadic arguments
#guard toString (E (X "0.75" 53) 150).1 == "1.681792830507429086062250952466429790080068525"
#guard D (E (X "0.75" 53) 150 .Floor) == ("1.681792830507429086062250952466429790080068524", .lt)
#guard D (E (X "0.75" 53) 150 .Ceiling) == ("1.681792830507429086062250952466429790080068525", .gt)
#guard toString (E (X "0.0009765625" 53) 150).1 == "1.000677130693066356678172784874647194837821984"
#guard toString (E (X "100.5" 53) 150).1 == "1792728671193156477399422023278.661496394239222"
#guard D (E (X "100.5" 53) 150 .Down) == ("1792728671193156477399422023278.661496394239222", .lt)
#guard toString (E (X "-0.5" 53) 150).1 == "0.7071067811865475244008443621048490392848359376"
#guard D (E (X "-0.5" 53) 150 .Up) == ("0.707106781186547524400844362104849039284835938", .gt)
#guard toString (E (X "-1.75" 53) 150).1 == "0.2973017787506802666793749926401189788232430233"
#guard toString (E (X "3.013916015625\
  " 53) 150).1 == "8.07754014493886897441265250833745294040121193"
#guard D (E (X "3.013916015625" 53) 100 .Floor) == ("8.07754014493886897441265250834", .lt)
#guard toString (pow2 (X "-1.75" 53)) == "0.29730177875068026"

-- directed modes are ordered
#guard (E (X "0.625" 53) 60 .Floor).2 == .lt
#guard (E (X "0.625" 53) 60 .Ceiling).2 == .gt
#guard partialCompare (E (X "0.625" 53) 60 .Floor).1 (E (X "0.625" 53) 60 .Ceiling).1 == some .lt

-- agreement with `exp (x ln 2)` at a higher precision
#guard (E (X "0.4375" 53) 100).1
  == (expPrecRound (mulPrecRound (X "0.4375" 53) (ln2 300) 300 .Nearest).1 100 .Nearest).1

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (pow2PrecRound tinyX 53 .Nearest) == ("1.0", .lt)
#guard D (pow2PrecRound tinyX 53 .Floor) == ("1.0", .lt)
#guard D (pow2PrecRound tinyX 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (pow2PrecRound (-tinyX) 53 .Nearest) == ("1.0", .gt)
#guard D (pow2PrecRound (-tinyX) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (pow2PrecRound (-tinyX) 53 .Ceiling) == ("1.0", .gt)
