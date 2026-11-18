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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (dottiePrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (dottiePrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (dottiePrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (dottiePrecRound 2 .Nearest) == ("0.8", .gt)
#guard D (dottiePrecRound 2 .Floor) == ("0.5", .lt)
#guard D (dottiePrecRound 3 .Nearest) == ("0.8", .gt)
#guard D (dottiePrecRound 3 .Floor) == ("0.6", .lt)
#guard D (dottiePrecRound 10 .Nearest) == ("0.739", .gt)
#guard D (dottiePrecRound 10 .Floor) == ("0.738", .lt)
#guard D (dottiePrecRound 53 .Nearest) == ("0.7390851332151607", .gt)
#guard D (dottiePrecRound 53 .Ceiling) == ("0.7390851332151607", .gt)
#guard D (dottiePrecRound 53 .Floor) == ("0.7390851332151606", .lt)
#guard D (dottiePrecRound 64 .Nearest) == ("0.73908513321516064166", .gt)
#guard D (dottiePrecRound 64 .Floor) == ("0.7390851332151606416", .lt)
#guard toString (dottie 53) == "0.7390851332151607"
#guard toString (dottie 300)
  == "0.739085133215160641655312087673873404013411758900757464965680635773284654883547594599376107"

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
