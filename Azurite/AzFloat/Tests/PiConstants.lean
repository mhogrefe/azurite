/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PiConstants
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the multiples, reciprocals and square roots of `π`

The correctly rounded values at 1, 2, 3, 53 and 100 bits in the nearest, floor and ceiling
modes (exact rationals from a 100-digit `π`), precision `0`, the shift relations with `pi` and
`piDiv3`, and the decimal strings at 53 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard D (tauPrecRound 1 .Nearest) == ("8.0", .gt)
#guard D (tauPrecRound 1 .Floor) == ("4.0", .lt)
#guard D (tauPrecRound 1 .Ceiling) == ("8.0", .gt)
#guard D (tauPrecRound 2 .Nearest) == ("6.0", .lt)
#guard D (tauPrecRound 2 .Floor) == ("6.0", .lt)
#guard D (tauPrecRound 2 .Ceiling) == ("8.0", .gt)
#guard D (tauPrecRound 3 .Nearest) == ("6.0", .lt)
#guard D (tauPrecRound 3 .Floor) == ("6.0", .lt)
#guard D (tauPrecRound 3 .Ceiling) == ("7.0", .gt)
#guard D (tauPrecRound 53 .Nearest) == ("6.283185307179586", .lt)
#guard D (tauPrecRound 53 .Floor) == ("6.283185307179586", .lt)
#guard D (tauPrecRound 53 .Ceiling) == ("6.283185307179587", .gt)
#guard D (tauPrecRound 100 .Nearest) == ("6.28318530717958647692528676656", .lt)
#guard D (tauPrecRound 100 .Floor) == ("6.28318530717958647692528676656", .lt)
#guard D (tauPrecRound 100 .Ceiling) == ("6.283185307179586476925286766565", .gt)
#guard D (piDiv2PrecRound 1 .Nearest) == ("2.0", .gt)
#guard D (piDiv2PrecRound 1 .Floor) == ("1.0", .lt)
#guard D (piDiv2PrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (piDiv2PrecRound 2 .Nearest) == ("1.5", .lt)
#guard D (piDiv2PrecRound 2 .Floor) == ("1.5", .lt)
#guard D (piDiv2PrecRound 2 .Ceiling) == ("2.0", .gt)
#guard D (piDiv2PrecRound 3 .Nearest) == ("1.5", .lt)
#guard D (piDiv2PrecRound 3 .Floor) == ("1.5", .lt)
#guard D (piDiv2PrecRound 3 .Ceiling) == ("1.8", .gt)
#guard D (piDiv2PrecRound 53 .Nearest) == ("1.5707963267948966", .lt)
#guard D (piDiv2PrecRound 53 .Floor) == ("1.5707963267948966", .lt)
#guard D (piDiv2PrecRound 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (piDiv2PrecRound 100 .Nearest) == ("1.57079632679489661923132169164", .lt)
#guard D (piDiv2PrecRound 100 .Floor) == ("1.57079632679489661923132169164", .lt)
#guard D (piDiv2PrecRound 100 .Ceiling) == ("1.570796326794896619231321691641", .gt)
#guard D (piDiv3PrecRound 1 .Nearest) == ("1.0", .lt)
#guard D (piDiv3PrecRound 1 .Floor) == ("1.0", .lt)
#guard D (piDiv3PrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (piDiv3PrecRound 2 .Nearest) == ("1.0", .lt)
#guard D (piDiv3PrecRound 2 .Floor) == ("1.0", .lt)
#guard D (piDiv3PrecRound 2 .Ceiling) == ("1.5", .gt)
#guard D (piDiv3PrecRound 3 .Nearest) == ("1.0", .lt)
#guard D (piDiv3PrecRound 3 .Floor) == ("1.0", .lt)
#guard D (piDiv3PrecRound 3 .Ceiling) == ("1.2", .gt)
#guard D (piDiv3PrecRound 53 .Nearest) == ("1.0471975511965979", .gt)
#guard D (piDiv3PrecRound 53 .Floor) == ("1.0471975511965976", .lt)
#guard D (piDiv3PrecRound 53 .Ceiling) == ("1.0471975511965979", .gt)
#guard D (piDiv3PrecRound 100 .Nearest) == ("1.047197551196597746154214461094", .gt)
#guard D (piDiv3PrecRound 100 .Floor) == ("1.047197551196597746154214461092", .lt)
#guard D (piDiv3PrecRound 100 .Ceiling) == ("1.047197551196597746154214461094", .gt)
#guard D (piDiv4PrecRound 1 .Nearest) == ("1.0", .gt)
#guard D (piDiv4PrecRound 1 .Floor) == ("0.5", .lt)
#guard D (piDiv4PrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (piDiv4PrecRound 2 .Nearest) == ("0.8", .lt)
#guard D (piDiv4PrecRound 2 .Floor) == ("0.8", .lt)
#guard D (piDiv4PrecRound 2 .Ceiling) == ("1.0", .gt)
#guard D (piDiv4PrecRound 3 .Nearest) == ("0.8", .lt)
#guard D (piDiv4PrecRound 3 .Floor) == ("0.8", .lt)
#guard D (piDiv4PrecRound 3 .Ceiling) == ("0.9", .gt)
#guard D (piDiv4PrecRound 53 .Nearest) == ("0.7853981633974483", .lt)
#guard D (piDiv4PrecRound 53 .Floor) == ("0.7853981633974483", .lt)
#guard D (piDiv4PrecRound 53 .Ceiling) == ("0.7853981633974484", .gt)
#guard D (piDiv4PrecRound 100 .Nearest) == ("0.78539816339744830961566084582", .lt)
#guard D (piDiv4PrecRound 100 .Floor) == ("0.78539816339744830961566084582", .lt)
#guard D (piDiv4PrecRound 100 .Ceiling) == ("0.785398163397448309615660845821", .gt)
#guard D (piDiv6PrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (piDiv6PrecRound 1 .Floor) == ("0.5", .lt)
#guard D (piDiv6PrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (piDiv6PrecRound 2 .Nearest) == ("0.5", .lt)
#guard D (piDiv6PrecRound 2 .Floor) == ("0.5", .lt)
#guard D (piDiv6PrecRound 2 .Ceiling) == ("0.8", .gt)
#guard D (piDiv6PrecRound 3 .Nearest) == ("0.5", .lt)
#guard D (piDiv6PrecRound 3 .Floor) == ("0.5", .lt)
#guard D (piDiv6PrecRound 3 .Ceiling) == ("0.6", .gt)
#guard D (piDiv6PrecRound 53 .Nearest) == ("0.5235987755982989", .gt)
#guard D (piDiv6PrecRound 53 .Floor) == ("0.5235987755982988", .lt)
#guard D (piDiv6PrecRound 53 .Ceiling) == ("0.5235987755982989", .gt)
#guard D (piDiv6PrecRound 100 .Nearest) == ("0.523598775598298873077107230547", .gt)
#guard D (piDiv6PrecRound 100 .Floor) == ("0.523598775598298873077107230546", .lt)
#guard D (piDiv6PrecRound 100 .Ceiling) == ("0.523598775598298873077107230547", .gt)
#guard D (piDiv8PrecRound 1 .Nearest) == ("0.5", .gt)
#guard D (piDiv8PrecRound 1 .Floor) == ("0.2", .lt)
#guard D (piDiv8PrecRound 1 .Ceiling) == ("0.5", .gt)
#guard D (piDiv8PrecRound 2 .Nearest) == ("0.4", .lt)
#guard D (piDiv8PrecRound 2 .Floor) == ("0.4", .lt)
#guard D (piDiv8PrecRound 2 .Ceiling) == ("0.5", .gt)
#guard D (piDiv8PrecRound 3 .Nearest) == ("0.4", .lt)
#guard D (piDiv8PrecRound 3 .Floor) == ("0.4", .lt)
#guard D (piDiv8PrecRound 3 .Ceiling) == ("0.44", .gt)
#guard D (piDiv8PrecRound 53 .Nearest) == ("0.39269908169872414", .lt)
#guard D (piDiv8PrecRound 53 .Floor) == ("0.39269908169872414", .lt)
#guard D (piDiv8PrecRound 53 .Ceiling) == ("0.3926990816987242", .gt)
#guard D (piDiv8PrecRound 100 .Nearest) == ("0.39269908169872415480783042291", .lt)
#guard D (piDiv8PrecRound 100 .Floor) == ("0.39269908169872415480783042291", .lt)
#guard D (piDiv8PrecRound 100 .Ceiling) == ("0.3926990816987241548078304229103", .gt)

#guard D (oneDivPiPrecRound 1 .Nearest) == ("0.2", .lt)
#guard D (oneDivPiPrecRound 1 .Floor) == ("0.2", .lt)
#guard D (oneDivPiPrecRound 1 .Ceiling) == ("0.5", .gt)
#guard D (oneDivPiPrecRound 2 .Nearest) == ("0.4", .gt)
#guard D (oneDivPiPrecRound 2 .Floor) == ("0.25", .lt)
#guard D (oneDivPiPrecRound 2 .Ceiling) == ("0.4", .gt)
#guard D (oneDivPiPrecRound 3 .Nearest) == ("0.3", .lt)
#guard D (oneDivPiPrecRound 3 .Floor) == ("0.3", .lt)
#guard D (oneDivPiPrecRound 3 .Ceiling) == ("0.4", .gt)
#guard D (oneDivPiPrecRound 53 .Nearest) == ("0.3183098861837907", .gt)
#guard D (oneDivPiPrecRound 53 .Floor) == ("0.31830988618379064", .lt)
#guard D (oneDivPiPrecRound 53 .Ceiling) == ("0.3183098861837907", .gt)
#guard D (oneDivPiPrecRound 100 .Nearest) == ("0.318309886183790671537767526745", .lt)
#guard D (oneDivPiPrecRound 100 .Floor) == ("0.318309886183790671537767526745", .lt)
#guard D (oneDivPiPrecRound 100 .Ceiling) == ("0.3183098861837906715377675267453", .gt)
#guard D (twoDivPiPrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (twoDivPiPrecRound 1 .Floor) == ("0.5", .lt)
#guard D (twoDivPiPrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (twoDivPiPrecRound 2 .Nearest) == ("0.8", .gt)
#guard D (twoDivPiPrecRound 2 .Floor) == ("0.5", .lt)
#guard D (twoDivPiPrecRound 2 .Ceiling) == ("0.8", .gt)
#guard D (twoDivPiPrecRound 3 .Nearest) == ("0.6", .lt)
#guard D (twoDivPiPrecRound 3 .Floor) == ("0.6", .lt)
#guard D (twoDivPiPrecRound 3 .Ceiling) == ("0.8", .gt)
#guard D (twoDivPiPrecRound 53 .Nearest) == ("0.6366197723675814", .gt)
#guard D (twoDivPiPrecRound 53 .Floor) == ("0.6366197723675813", .lt)
#guard D (twoDivPiPrecRound 53 .Ceiling) == ("0.6366197723675814", .gt)
#guard D (twoDivPiPrecRound 100 .Nearest) == ("0.63661977236758134307553505349", .lt)
#guard D (twoDivPiPrecRound 100 .Floor) == ("0.63661977236758134307553505349", .lt)
#guard D (twoDivPiPrecRound 100 .Ceiling) == ("0.6366197723675813430755350534906", .gt)

#guard D (sqrtPiPrecRound 1 .Nearest) == ("2.0", .gt)
#guard D (sqrtPiPrecRound 1 .Floor) == ("1.0", .lt)
#guard D (sqrtPiPrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (sqrtPiPrecRound 2 .Nearest) == ("2.0", .gt)
#guard D (sqrtPiPrecRound 2 .Floor) == ("1.5", .lt)
#guard D (sqrtPiPrecRound 2 .Ceiling) == ("2.0", .gt)
#guard D (sqrtPiPrecRound 3 .Nearest) == ("1.8", .lt)
#guard D (sqrtPiPrecRound 3 .Floor) == ("1.8", .lt)
#guard D (sqrtPiPrecRound 3 .Ceiling) == ("2.0", .gt)
#guard D (sqrtPiPrecRound 53 .Nearest) == ("1.772453850905516", .gt)
#guard D (sqrtPiPrecRound 53 .Floor) == ("1.7724538509055159", .lt)
#guard D (sqrtPiPrecRound 53 .Ceiling) == ("1.772453850905516", .gt)
#guard D (sqrtPiPrecRound 100 .Nearest) == ("1.772453850905516027298167483341", .gt)
#guard D (sqrtPiPrecRound 100 .Floor) == ("1.77245385090551602729816748334", .lt)
#guard D (sqrtPiPrecRound 100 .Ceiling) == ("1.772453850905516027298167483341", .gt)
#guard D (oneDivSqrtPiPrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (oneDivSqrtPiPrecRound 1 .Floor) == ("0.5", .lt)
#guard D (oneDivSqrtPiPrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (oneDivSqrtPiPrecRound 2 .Nearest) == ("0.5", .lt)
#guard D (oneDivSqrtPiPrecRound 2 .Floor) == ("0.5", .lt)
#guard D (oneDivSqrtPiPrecRound 2 .Ceiling) == ("0.8", .gt)
#guard D (oneDivSqrtPiPrecRound 3 .Nearest) == ("0.6", .gt)
#guard D (oneDivSqrtPiPrecRound 3 .Floor) == ("0.5", .lt)
#guard D (oneDivSqrtPiPrecRound 3 .Ceiling) == ("0.6", .gt)
#guard D (oneDivSqrtPiPrecRound 53 .Nearest) == ("0.5641895835477563", .lt)
#guard D (oneDivSqrtPiPrecRound 53 .Floor) == ("0.5641895835477563", .lt)
#guard D (oneDivSqrtPiPrecRound 53 .Ceiling) == ("0.5641895835477564", .gt)
#guard D (oneDivSqrtPiPrecRound 100 .Nearest) == ("0.564189583547756286948079451561", .gt)
#guard D (oneDivSqrtPiPrecRound 100 .Floor) == ("0.56418958354775628694807945156", .lt)
#guard D (oneDivSqrtPiPrecRound 100 .Ceiling) == ("0.564189583547756286948079451561", .gt)
#guard D (twoDivSqrtPiPrecRound 1 .Nearest) == ("1.0", .lt)
#guard D (twoDivSqrtPiPrecRound 1 .Floor) == ("1.0", .lt)
#guard D (twoDivSqrtPiPrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (twoDivSqrtPiPrecRound 2 .Nearest) == ("1.0", .lt)
#guard D (twoDivSqrtPiPrecRound 2 .Floor) == ("1.0", .lt)
#guard D (twoDivSqrtPiPrecRound 2 .Ceiling) == ("1.5", .gt)
#guard D (twoDivSqrtPiPrecRound 3 .Nearest) == ("1.2", .gt)
#guard D (twoDivSqrtPiPrecRound 3 .Floor) == ("1.0", .lt)
#guard D (twoDivSqrtPiPrecRound 3 .Ceiling) == ("1.2", .gt)
#guard D (twoDivSqrtPiPrecRound 53 .Nearest) == ("1.1283791670955126", .lt)
#guard D (twoDivSqrtPiPrecRound 53 .Floor) == ("1.1283791670955126", .lt)
#guard D (twoDivSqrtPiPrecRound 53 .Ceiling) == ("1.1283791670955128", .gt)
#guard D (twoDivSqrtPiPrecRound 100 .Nearest) == ("1.128379167095512573896158903122", .gt)
#guard D (twoDivSqrtPiPrecRound 100 .Floor) == ("1.12837916709551257389615890312", .lt)
#guard D (twoDivSqrtPiPrecRound 100 .Ceiling) == ("1.128379167095512573896158903122", .gt)
#guard D (oneDivSqrtTauPrecRound 1 .Nearest) == ("0.5", .gt)
#guard D (oneDivSqrtTauPrecRound 1 .Floor) == ("0.2", .lt)
#guard D (oneDivSqrtTauPrecRound 1 .Ceiling) == ("0.5", .gt)
#guard D (oneDivSqrtTauPrecRound 2 .Nearest) == ("0.4", .lt)
#guard D (oneDivSqrtTauPrecRound 2 .Floor) == ("0.4", .lt)
#guard D (oneDivSqrtTauPrecRound 2 .Ceiling) == ("0.5", .gt)
#guard D (oneDivSqrtTauPrecRound 3 .Nearest) == ("0.4", .lt)
#guard D (oneDivSqrtTauPrecRound 3 .Floor) == ("0.4", .lt)
#guard D (oneDivSqrtTauPrecRound 3 .Ceiling) == ("0.44", .gt)
#guard D (oneDivSqrtTauPrecRound 53 .Nearest) == ("0.3989422804014327", .gt)
#guard D (oneDivSqrtTauPrecRound 53 .Floor) == ("0.39894228040143265", .lt)
#guard D (oneDivSqrtTauPrecRound 53 .Ceiling) == ("0.3989422804014327", .gt)
#guard D (oneDivSqrtTauPrecRound 100 .Nearest) == ("0.3989422804014326779399460599344", .gt)
#guard D (oneDivSqrtTauPrecRound 100 .Floor) == ("0.398942280401432677939946059934", .lt)
#guard D (oneDivSqrtTauPrecRound 100 .Ceiling) == ("0.3989422804014326779399460599344", .gt)

-- precision `0`
#guard D (tauPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (piDiv2PrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (piDiv3PrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (piDiv4PrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (piDiv6PrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (piDiv8PrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (oneDivPiPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (twoDivPiPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (sqrtPiPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (oneDivSqrtPiPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (twoDivSqrtPiPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (oneDivSqrtTauPrecRound 0 .Nearest) == ("NaN", .eq)

-- shift relations
#guard tau 200 == pi 200 <<< AzInt.ofInt 1
#guard piDiv2 200 == pi 200 <<< AzInt.ofInt (-1)
#guard piDiv4 200 == pi 200 <<< AzInt.ofInt (-2)
#guard piDiv8 200 == pi 200 <<< AzInt.ofInt (-3)
#guard piDiv6 200 == piDiv3 200 <<< AzInt.ofInt (-1)
#guard (piDiv3PrecRound 200 .Floor).2 == .lt
#guard (piDiv3PrecRound 200 .Ceiling).2 == .gt
#guard twoDivPi 200 == oneDivPi 200 <<< AzInt.ofInt 1
#guard (oneDivPiPrecRound 200 .Floor).2 == .lt
#guard (oneDivPiPrecRound 200 .Ceiling).2 == .gt
#guard twoDivSqrtPi 200 == oneDivSqrtPi 200 <<< AzInt.ofInt 1
#guard (sqrtPiPrecRound 200 .Floor).2 == .lt
#guard (sqrtPiPrecRound 200 .Ceiling).2 == .gt
#guard (oneDivSqrtTauPrecRound 200 .Floor).2 == .lt

-- decimal strings at 53 bits
#guard toString (tau 53) == "6.283185307179586"
#guard toString (piDiv2 53) == "1.5707963267948966"
#guard toString (piDiv3 53) == "1.0471975511965979"
#guard toString (piDiv4 53) == "0.7853981633974483"
#guard toString (piDiv6 53) == "0.5235987755982989"
#guard toString (piDiv8 53) == "0.39269908169872414"
#guard toString (oneDivPi 53) == "0.3183098861837907"
#guard toString (sqrtPi 53) == "1.772453850905516"
#guard toString (oneDivSqrtPi 53) == "0.5641895835477563"
#guard toString (twoDivSqrtPi 53) == "1.1283791670955126"
#guard toString (oneDivSqrtTau 53) == "0.3989422804014327"
#guard toString (twoDivPi 53) == "0.6366197723675814"
