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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard tauPrecRound 1 .Nearest == (F "8" 1, .gt)
#guard tauPrecRound 1 .Floor == (F "4" 1, .lt)
#guard tauPrecRound 1 .Ceiling == (F "8" 1, .gt)
#guard tauPrecRound 2 .Nearest == (F "6" 2, .lt)
#guard tauPrecRound 2 .Floor == (F "6" 2, .lt)
#guard tauPrecRound 2 .Ceiling == (F "8" 2, .gt)
#guard tauPrecRound 3 .Nearest == (F "6" 3, .lt)
#guard tauPrecRound 3 .Floor == (F "6" 3, .lt)
#guard tauPrecRound 3 .Ceiling == (F "7" 3, .gt)
#guard tauPrecRound 53 .Nearest == (F "884279719003555/140737488355328" 53, .lt)
#guard tauPrecRound 53 .Floor == (F "884279719003555/140737488355328" 53, .lt)
#guard tauPrecRound 53 .Ceiling == (F "7074237752028441/1125899906842624" 53, .gt)
#guard tauPrecRound 100 .Nearest
  == (F "124451306656115542615260972311/19807040628566084398385987584" 100, .lt)
#guard tauPrecRound 100 .Floor
  == (F "124451306656115542615260972311/19807040628566084398385987584" 100, .lt)
#guard tauPrecRound 100 .Ceiling
  == (F "995610453248924340922087778489/158456325028528675187087900672" 100, .gt)
#guard piDiv2PrecRound 1 .Nearest == (F "2" 1, .gt)
#guard piDiv2PrecRound 1 .Floor == (F "1" 1, .lt)
#guard piDiv2PrecRound 1 .Ceiling == (F "2" 1, .gt)
#guard piDiv2PrecRound 2 .Nearest == (F "3/2" 2, .lt)
#guard piDiv2PrecRound 2 .Floor == (F "3/2" 2, .lt)
#guard piDiv2PrecRound 2 .Ceiling == (F "2" 2, .gt)
#guard piDiv2PrecRound 3 .Nearest == (F "3/2" 3, .lt)
#guard piDiv2PrecRound 3 .Floor == (F "3/2" 3, .lt)
#guard piDiv2PrecRound 3 .Ceiling == (F "7/4" 3, .gt)
#guard piDiv2PrecRound 53 .Nearest == (F "884279719003555/562949953421312" 53, .lt)
#guard piDiv2PrecRound 53 .Floor == (F "884279719003555/562949953421312" 53, .lt)
#guard piDiv2PrecRound 53 .Ceiling == (F "7074237752028441/4503599627370496" 53, .gt)
#guard piDiv2PrecRound 100 .Nearest
  == (F "124451306656115542615260972311/79228162514264337593543950336" 100, .lt)
#guard piDiv2PrecRound 100 .Floor
  == (F "124451306656115542615260972311/79228162514264337593543950336" 100, .lt)
#guard piDiv2PrecRound 100 .Ceiling
  == (F "995610453248924340922087778489/633825300114114700748351602688" 100, .gt)
#guard piDiv3PrecRound 1 .Nearest == (F "1" 1, .lt)
#guard piDiv3PrecRound 1 .Floor == (F "1" 1, .lt)
#guard piDiv3PrecRound 1 .Ceiling == (F "2" 1, .gt)
#guard piDiv3PrecRound 2 .Nearest == (F "1" 2, .lt)
#guard piDiv3PrecRound 2 .Floor == (F "1" 2, .lt)
#guard piDiv3PrecRound 2 .Ceiling == (F "3/2" 2, .gt)
#guard piDiv3PrecRound 3 .Nearest == (F "1" 3, .lt)
#guard piDiv3PrecRound 3 .Floor == (F "1" 3, .lt)
#guard piDiv3PrecRound 3 .Ceiling == (F "5/4" 3, .gt)
#guard piDiv3PrecRound 53 .Nearest == (F "2358079250676147/2251799813685248" 53, .gt)
#guard piDiv3PrecRound 53 .Floor == (F "4716158501352293/4503599627370496" 53, .lt)
#guard piDiv3PrecRound 53 .Ceiling == (F "2358079250676147/2251799813685248" 53, .gt)
#guard piDiv3PrecRound 100 .Nearest
  == (F "663740302165949560614725185659/633825300114114700748351602688" 100, .gt)
#guard piDiv3PrecRound 100 .Floor
  == (F "331870151082974780307362592829/316912650057057350374175801344" 100, .lt)
#guard piDiv3PrecRound 100 .Ceiling
  == (F "663740302165949560614725185659/633825300114114700748351602688" 100, .gt)
#guard piDiv4PrecRound 1 .Nearest == (F "1" 1, .gt)
#guard piDiv4PrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard piDiv4PrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard piDiv4PrecRound 2 .Nearest == (F "3/4" 2, .lt)
#guard piDiv4PrecRound 2 .Floor == (F "3/4" 2, .lt)
#guard piDiv4PrecRound 2 .Ceiling == (F "1" 2, .gt)
#guard piDiv4PrecRound 3 .Nearest == (F "3/4" 3, .lt)
#guard piDiv4PrecRound 3 .Floor == (F "3/4" 3, .lt)
#guard piDiv4PrecRound 3 .Ceiling == (F "7/8" 3, .gt)
#guard piDiv4PrecRound 53 .Nearest == (F "884279719003555/1125899906842624" 53, .lt)
#guard piDiv4PrecRound 53 .Floor == (F "884279719003555/1125899906842624" 53, .lt)
#guard piDiv4PrecRound 53 .Ceiling == (F "7074237752028441/9007199254740992" 53, .gt)
#guard piDiv4PrecRound 100 .Nearest
  == (F "124451306656115542615260972311/158456325028528675187087900672" 100, .lt)
#guard piDiv4PrecRound 100 .Floor
  == (F "124451306656115542615260972311/158456325028528675187087900672" 100, .lt)
#guard piDiv4PrecRound 100 .Ceiling
  == (F "995610453248924340922087778489/1267650600228229401496703205376" 100, .gt)
#guard piDiv6PrecRound 1 .Nearest == (F "1/2" 1, .lt)
#guard piDiv6PrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard piDiv6PrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard piDiv6PrecRound 2 .Nearest == (F "1/2" 2, .lt)
#guard piDiv6PrecRound 2 .Floor == (F "1/2" 2, .lt)
#guard piDiv6PrecRound 2 .Ceiling == (F "3/4" 2, .gt)
#guard piDiv6PrecRound 3 .Nearest == (F "1/2" 3, .lt)
#guard piDiv6PrecRound 3 .Floor == (F "1/2" 3, .lt)
#guard piDiv6PrecRound 3 .Ceiling == (F "5/8" 3, .gt)
#guard piDiv6PrecRound 53 .Nearest == (F "2358079250676147/4503599627370496" 53, .gt)
#guard piDiv6PrecRound 53 .Floor == (F "4716158501352293/9007199254740992" 53, .lt)
#guard piDiv6PrecRound 53 .Ceiling == (F "2358079250676147/4503599627370496" 53, .gt)
#guard piDiv6PrecRound 100 .Nearest
  == (F "663740302165949560614725185659/1267650600228229401496703205376" 100, .gt)
#guard piDiv6PrecRound 100 .Floor
  == (F "331870151082974780307362592829/633825300114114700748351602688" 100, .lt)
#guard piDiv6PrecRound 100 .Ceiling
  == (F "663740302165949560614725185659/1267650600228229401496703205376" 100, .gt)
#guard piDiv8PrecRound 1 .Nearest == (F "1/2" 1, .gt)
#guard piDiv8PrecRound 1 .Floor == (F "1/4" 1, .lt)
#guard piDiv8PrecRound 1 .Ceiling == (F "1/2" 1, .gt)
#guard piDiv8PrecRound 2 .Nearest == (F "3/8" 2, .lt)
#guard piDiv8PrecRound 2 .Floor == (F "3/8" 2, .lt)
#guard piDiv8PrecRound 2 .Ceiling == (F "1/2" 2, .gt)
#guard piDiv8PrecRound 3 .Nearest == (F "3/8" 3, .lt)
#guard piDiv8PrecRound 3 .Floor == (F "3/8" 3, .lt)
#guard piDiv8PrecRound 3 .Ceiling == (F "7/16" 3, .gt)
#guard piDiv8PrecRound 53 .Nearest == (F "884279719003555/2251799813685248" 53, .lt)
#guard piDiv8PrecRound 53 .Floor == (F "884279719003555/2251799813685248" 53, .lt)
#guard piDiv8PrecRound 53 .Ceiling == (F "7074237752028441/18014398509481984" 53, .gt)
#guard piDiv8PrecRound 100 .Nearest
  == (F "124451306656115542615260972311/316912650057057350374175801344" 100, .lt)
#guard piDiv8PrecRound 100 .Floor
  == (F "124451306656115542615260972311/316912650057057350374175801344" 100, .lt)
#guard piDiv8PrecRound 100 .Ceiling
  == (F "995610453248924340922087778489/2535301200456458802993406410752" 100, .gt)

#guard oneDivPiPrecRound 1 .Nearest == (F "1/4" 1, .lt)
#guard oneDivPiPrecRound 1 .Floor == (F "1/4" 1, .lt)
#guard oneDivPiPrecRound 1 .Ceiling == (F "1/2" 1, .gt)
#guard oneDivPiPrecRound 2 .Nearest == (F "3/8" 2, .gt)
#guard oneDivPiPrecRound 2 .Floor == (F "1/4" 2, .lt)
#guard oneDivPiPrecRound 2 .Ceiling == (F "3/8" 2, .gt)
#guard oneDivPiPrecRound 3 .Nearest == (F "5/16" 3, .lt)
#guard oneDivPiPrecRound 3 .Floor == (F "5/16" 3, .lt)
#guard oneDivPiPrecRound 3 .Ceiling == (F "3/8" 3, .gt)
#guard oneDivPiPrecRound 53 .Nearest == (F "5734161139222659/18014398509481984" 53, .gt)
#guard oneDivPiPrecRound 53 .Floor == (F "2867080569611329/9007199254740992" 53, .lt)
#guard oneDivPiPrecRound 53 .Ceiling == (F "5734161139222659/18014398509481984" 53, .gt)
#guard oneDivPiPrecRound 100 .Nearest
  == (F "807011436558923259726928379167/2535301200456458802993406410752" 100, .lt)
#guard oneDivPiPrecRound 100 .Floor
  == (F "807011436558923259726928379167/2535301200456458802993406410752" 100, .lt)
#guard oneDivPiPrecRound 100 .Ceiling
  == (F "25219107392466351866466511849/79228162514264337593543950336" 100, .gt)
#guard twoDivPiPrecRound 1 .Nearest == (F "1/2" 1, .lt)
#guard twoDivPiPrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard twoDivPiPrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard twoDivPiPrecRound 2 .Nearest == (F "3/4" 2, .gt)
#guard twoDivPiPrecRound 2 .Floor == (F "1/2" 2, .lt)
#guard twoDivPiPrecRound 2 .Ceiling == (F "3/4" 2, .gt)
#guard twoDivPiPrecRound 3 .Nearest == (F "5/8" 3, .lt)
#guard twoDivPiPrecRound 3 .Floor == (F "5/8" 3, .lt)
#guard twoDivPiPrecRound 3 .Ceiling == (F "3/4" 3, .gt)
#guard twoDivPiPrecRound 53 .Nearest == (F "5734161139222659/9007199254740992" 53, .gt)
#guard twoDivPiPrecRound 53 .Floor == (F "2867080569611329/4503599627370496" 53, .lt)
#guard twoDivPiPrecRound 53 .Ceiling == (F "5734161139222659/9007199254740992" 53, .gt)
#guard twoDivPiPrecRound 100 .Nearest
  == (F "807011436558923259726928379167/1267650600228229401496703205376" 100, .lt)
#guard twoDivPiPrecRound 100 .Floor
  == (F "807011436558923259726928379167/1267650600228229401496703205376" 100, .lt)
#guard twoDivPiPrecRound 100 .Ceiling
  == (F "25219107392466351866466511849/39614081257132168796771975168" 100, .gt)

#guard sqrtPiPrecRound 1 .Nearest == (F "2" 1, .gt)
#guard sqrtPiPrecRound 1 .Floor == (F "1" 1, .lt)
#guard sqrtPiPrecRound 1 .Ceiling == (F "2" 1, .gt)
#guard sqrtPiPrecRound 2 .Nearest == (F "2" 2, .gt)
#guard sqrtPiPrecRound 2 .Floor == (F "3/2" 2, .lt)
#guard sqrtPiPrecRound 2 .Ceiling == (F "2" 2, .gt)
#guard sqrtPiPrecRound 3 .Nearest == (F "7/4" 3, .lt)
#guard sqrtPiPrecRound 3 .Floor == (F "7/4" 3, .lt)
#guard sqrtPiPrecRound 3 .Ceiling == (F "2" 3, .gt)
#guard sqrtPiPrecRound 53 .Nearest == (F "7982422502469483/4503599627370496" 53, .gt)
#guard sqrtPiPrecRound 53 .Floor == (F "3991211251234741/2251799813685248" 53, .lt)
#guard sqrtPiPrecRound 53 .Ceiling == (F "7982422502469483/4503599627370496" 53, .gt)
#guard sqrtPiPrecRound 100 .Nearest
  == (F "1123426093988607008443415564395/633825300114114700748351602688" 100, .gt)
#guard sqrtPiPrecRound 100 .Floor
  == (F "561713046994303504221707782197/316912650057057350374175801344" 100, .lt)
#guard sqrtPiPrecRound 100 .Ceiling
  == (F "1123426093988607008443415564395/633825300114114700748351602688" 100, .gt)
#guard oneDivSqrtPiPrecRound 1 .Nearest == (F "1/2" 1, .lt)
#guard oneDivSqrtPiPrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard oneDivSqrtPiPrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard oneDivSqrtPiPrecRound 2 .Nearest == (F "1/2" 2, .lt)
#guard oneDivSqrtPiPrecRound 2 .Floor == (F "1/2" 2, .lt)
#guard oneDivSqrtPiPrecRound 2 .Ceiling == (F "3/4" 2, .gt)
#guard oneDivSqrtPiPrecRound 3 .Nearest == (F "5/8" 3, .gt)
#guard oneDivSqrtPiPrecRound 3 .Floor == (F "1/2" 3, .lt)
#guard oneDivSqrtPiPrecRound 3 .Ceiling == (F "5/8" 3, .gt)
#guard oneDivSqrtPiPrecRound 53 .Nearest == (F "5081767996463981/9007199254740992" 53, .lt)
#guard oneDivSqrtPiPrecRound 53 .Floor == (F "5081767996463981/9007199254740992" 53, .lt)
#guard oneDivSqrtPiPrecRound 53 .Ceiling == (F "2540883998231991/4503599627370496" 53, .gt)
#guard oneDivSqrtPiPrecRound 100 .Nearest
  == (F "715195264226828036787283732471/1267650600228229401496703205376" 100, .gt)
#guard oneDivSqrtPiPrecRound 100 .Floor
  == (F "357597632113414018393641866235/633825300114114700748351602688" 100, .lt)
#guard oneDivSqrtPiPrecRound 100 .Ceiling
  == (F "715195264226828036787283732471/1267650600228229401496703205376" 100, .gt)
#guard twoDivSqrtPiPrecRound 1 .Nearest == (F "1" 1, .lt)
#guard twoDivSqrtPiPrecRound 1 .Floor == (F "1" 1, .lt)
#guard twoDivSqrtPiPrecRound 1 .Ceiling == (F "2" 1, .gt)
#guard twoDivSqrtPiPrecRound 2 .Nearest == (F "1" 2, .lt)
#guard twoDivSqrtPiPrecRound 2 .Floor == (F "1" 2, .lt)
#guard twoDivSqrtPiPrecRound 2 .Ceiling == (F "3/2" 2, .gt)
#guard twoDivSqrtPiPrecRound 3 .Nearest == (F "5/4" 3, .gt)
#guard twoDivSqrtPiPrecRound 3 .Floor == (F "1" 3, .lt)
#guard twoDivSqrtPiPrecRound 3 .Ceiling == (F "5/4" 3, .gt)
#guard twoDivSqrtPiPrecRound 53 .Nearest == (F "5081767996463981/4503599627370496" 53, .lt)
#guard twoDivSqrtPiPrecRound 53 .Floor == (F "5081767996463981/4503599627370496" 53, .lt)
#guard twoDivSqrtPiPrecRound 53 .Ceiling == (F "2540883998231991/2251799813685248" 53, .gt)
#guard twoDivSqrtPiPrecRound 100 .Nearest
  == (F "715195264226828036787283732471/633825300114114700748351602688" 100, .gt)
#guard twoDivSqrtPiPrecRound 100 .Floor
  == (F "357597632113414018393641866235/316912650057057350374175801344" 100, .lt)
#guard twoDivSqrtPiPrecRound 100 .Ceiling
  == (F "715195264226828036787283732471/633825300114114700748351602688" 100, .gt)
#guard oneDivSqrtTauPrecRound 1 .Nearest == (F "1/2" 1, .gt)
#guard oneDivSqrtTauPrecRound 1 .Floor == (F "1/4" 1, .lt)
#guard oneDivSqrtTauPrecRound 1 .Ceiling == (F "1/2" 1, .gt)
#guard oneDivSqrtTauPrecRound 2 .Nearest == (F "3/8" 2, .lt)
#guard oneDivSqrtTauPrecRound 2 .Floor == (F "3/8" 2, .lt)
#guard oneDivSqrtTauPrecRound 2 .Ceiling == (F "1/2" 2, .gt)
#guard oneDivSqrtTauPrecRound 3 .Nearest == (F "3/8" 3, .lt)
#guard oneDivSqrtTauPrecRound 3 .Floor == (F "3/8" 3, .lt)
#guard oneDivSqrtTauPrecRound 3 .Ceiling == (F "7/16" 3, .gt)
#guard oneDivSqrtTauPrecRound 53 .Nearest == (F "7186705221432913/18014398509481984" 53, .gt)
#guard oneDivSqrtTauPrecRound 53 .Floor == (F "449169076339557/1125899906842624" 53, .lt)
#guard oneDivSqrtTauPrecRound 53 .Ceiling == (F "7186705221432913/18014398509481984" 53, .gt)
#guard oneDivSqrtTauPrecRound 100 .Nearest
  == (F "505719421207294732937928315907/1267650600228229401496703205376" 100, .gt)
#guard oneDivSqrtTauPrecRound 100 .Floor
  == (F "1011438842414589465875856631813/2535301200456458802993406410752" 100, .lt)
#guard oneDivSqrtTauPrecRound 100 .Ceiling
  == (F "505719421207294732937928315907/1267650600228229401496703205376" 100, .gt)

-- precision `0`
#guard tauPrecRound 0 .Nearest == (nan, .eq)
#guard piDiv2PrecRound 0 .Nearest == (nan, .eq)
#guard piDiv3PrecRound 0 .Nearest == (nan, .eq)
#guard piDiv4PrecRound 0 .Nearest == (nan, .eq)
#guard piDiv6PrecRound 0 .Nearest == (nan, .eq)
#guard piDiv8PrecRound 0 .Nearest == (nan, .eq)
#guard oneDivPiPrecRound 0 .Nearest == (nan, .eq)
#guard twoDivPiPrecRound 0 .Nearest == (nan, .eq)
#guard sqrtPiPrecRound 0 .Nearest == (nan, .eq)
#guard oneDivSqrtPiPrecRound 0 .Nearest == (nan, .eq)
#guard twoDivSqrtPiPrecRound 0 .Nearest == (nan, .eq)
#guard oneDivSqrtTauPrecRound 0 .Nearest == (nan, .eq)

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
