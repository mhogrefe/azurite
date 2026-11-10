/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.Dottie
import Azurite.AzFloat.HexString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Dottie number

`d = 0.73908513321516064165531208767387340401341175890075746496568063577328465488354759…`
(the solution of `cos x = x`; reference by Newton's iteration at 160 digits).  `p = 0`, the
low precisions by hand (`0.1011110100110…₂`), the 10-, 53- and 64-bit values in the three
modes, the decimal expansion at 300 bits, the contracting fallback (`dottieIter`) against the
Newton candidate, and `cos d = d` to the last bit at 200 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard dottiePrecRound 0 .Nearest == (nan, .eq)
#guard dottiePrecRound 1 .Nearest == (F "1/2" 1, .lt)
#guard dottiePrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard dottiePrecRound 2 .Nearest == (F "3/4" 2, .gt)
#guard dottiePrecRound 2 .Floor == (F "1/2" 2, .lt)
#guard dottiePrecRound 3 .Nearest == (F "3/4" 3, .gt)
#guard dottiePrecRound 3 .Floor == (F "5/8" 3, .lt)
#guard dottiePrecRound 10 .Nearest == (F "757/1024" 10, .gt)
#guard dottiePrecRound 10 .Floor == (F "189/256" 10, .lt)
#guard dottiePrecRound 53 .Nearest == (F "3328543530542871/4503599627370496" 53, .gt)
#guard dottiePrecRound 53 .Ceiling == (F "3328543530542871/4503599627370496" 53, .gt)
#guard dottiePrecRound 53 .Floor == (F "6657087061085741/9007199254740992" 53, .lt)
#guard dottiePrecRound 64 .Nearest
  == (F "13633714301103599051/18446744073709551616" 64, .gt)
#guard dottiePrecRound 64 .Floor == (F "6816857150551799525/9223372036854775808" 64, .lt)
#guard toString (dottie 53) == "0.7390851332151607"
#guard (toString (dottie 300)).startsWith
  "0.739085133215160641655312087673873404013411758900757464965680635773284654883547594599376"

-- the verified bracket around the proven-convergent fallback iterate contains the candidate's
#guard
  let W := 80
  let I := dottieMvt (dottieIter W (8 * W) oneHalf) W
  let J := dottieMvt (dottieCandidate W) W
  le I.1 J.1 && le J.2 I.2

-- `cos d = d`: at 200 bits the two agree to within one unit in the last place
#guard
  let d := dottie 200
  let c := (cosPrecRound d 200 .Nearest).1
  let diff := (subPrecRound c d 200 .Nearest).1
  le diff.abs (one <<< AzInt.ofInt (-199))
