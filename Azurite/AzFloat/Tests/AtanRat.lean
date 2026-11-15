/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan
import Azurite.AzFloat.AtanRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arctan q` of a rational

The special values (`arctan 0 = 0` at every precision, `p = 0`), the correctly rounded 53-bit
values of `arctan q` at the exact rationals `1/3` (same significand as `arctan` of the 53-bit
float nearest `1/3`, but on the other side of the exact value), `1/10`, `±22/7`, `−7/5`,
`355/113`, `−1/1000`, `10³⁰`, the neighbours `1 ± 10⁻⁶` of `1`, `1/(10⁹ + 7)`, `123456.789`,
agreement with the float `atan` at exactly representable arguments (`1/2`, `−3`, `10¹²`,
`1/1024`, `1`), the directed modes, 1-, 20-, 113- and 400-bit results, 200-bit strings, and the
tiny path at `±1/(3·2^1000)` (`arctan q` rounds like a value just inside `q`).  References: an
independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1/3" 53 == (F "5796142707547873/18014398509481984" 53, .lt)
#guard T "1/10" 53 == (F "1795470824878867/18014398509481984" 53, .lt)
#guard T "22/7" 53 == (F "1421722840549829/1125899906842624" 53, .gt)
#guard T "-22/7" 53 == (F "-1421722840549829/1125899906842624" 53, .lt)
#guard T "-7/5" 53 == (F "-535110299759933/562949953421312" 53, .lt)
#guard T "355/113" 53 == (F "5686367748711689/4503599627370496" 53, .lt)
#guard T "-1/1000" 53 == (F "-4611684481199637/4611686018427387904" 53, .gt)
#guard T "1000000000000000000000000000000" 53 == (F "884279719003555/562949953421312" 53, .lt)
#guard T "1000001/1000000" 53 == (F "884280281953227/1125899906842624" 53, .gt)
#guard T "999999/1000000" 53 == (F "7074233248426561/9007199254740992" 53, .lt)
#guard T "1/1000000007" 53 == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "123456789/1000" 53 == (F "7074201272871127/4503599627370496" 53, .lt)
#guard atanPrecRound (F "1/3" 53) 53 .Nearest == (F "5796142707547873/18014398509481984" 53, .gt)

-- agreement with the float `atan` at representable arguments
#guard T "1/2" 53 == atanPrecRound (F "1/2" 53) 53 .Nearest
#guard T "-3" 53 == atanPrecRound (F "-3" 53) 53 .Nearest
#guard T "1000000000000" 53 == atanPrecRound (F "1000000000000" 53) 53 .Nearest
#guard T "1/1024" 53 == atanPrecRound (F "1/1024" 53) 53 .Nearest
#guard T "1" 53 == atanPrecRound (F "1" 53) 53 .Nearest
#guard T "-1" 200 .Floor == atanPrecRound (F "-1" 53) 200 .Floor

-- directed modes and other precisions
#guard T "1/3" 53 .Floor == (F "5796142707547873/18014398509481984" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "2898071353773937/9007199254740992" 53, .gt)
#guard T "22/7" 53 .Floor == (F "5686891362199315/4503599627370496" 53, .lt)
#guard T "22/7" 53 .Ceiling == (F "1421722840549829/1125899906842624" 53, .gt)
#guard T "-22/7" 53 .Floor == (F "-1421722840549829/1125899906842624" 53, .lt)
#guard T "-22/7" 53 .Ceiling == (F "-5686891362199315/4503599627370496" 53, .gt)
#guard T "1/3" 20 == (F "84345/262144" 20, .gt)
#guard T "1/3" 1 == (F "1/4" 1, .lt)
#guard T "1/3" 113
  == (F "6682497571302097730138680461658875/20769187434139310514121985316880384" 113, .lt)
#guard T "-7/5" 113
  == (F "-9871042750877485343105352595100417/10384593717069655257060992658440192" 113, .gt)
#guard T "1/3" 400
  == (F ("415420164932562277212025873527013502124066934406946286877252913667945603875091507966"
    ++ "647483758809945330481323919515903069/129112493904345429482795958600150593716485289641"
    ++ "4611756415329678270323811008420597314822676640068915717951585986373746688") 400, .lt)
#guard atanRat (Q "1/3") 53 == F "5796142707547873/18014398509481984" 53
#guard (toString (atanRat (Q "1/3") 200)).startsWith
  "0.32175055439664219340140461435866131902075529555765619143280"
#guard (toString (atanRat (Q "355/113") 200)).startsWith
  "1.2626272802211267126987321884110788752799549704226693178019"

-- tiny arguments (`±1/(3·2^1000)`): `q − q³/3 < arctan q < q`, rounded without the iteration
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyLo : AzFloat := (ofAzRatRound tinyQ 53 .Floor).1
private def tinyHi : AzFloat := (ofAzRatRound tinyQ 53 .Ceiling).1
#guard atanRatPrecRound tinyQ 53 .Nearest == (tinyLo, .lt)
#guard atanRatPrecRound tinyQ 53 .Floor == (tinyLo, .lt)
#guard atanRatPrecRound tinyQ 53 .Ceiling == (tinyHi, .gt)
#guard atanRatPrecRound (-tinyQ) 53 .Nearest == (-tinyLo, .gt)
#guard atanRatPrecRound (-tinyQ) 53 .Floor == (-tinyHi, .lt)
#guard atanRatPrecRound (-tinyQ) 53 .Ceiling == (-tinyLo, .gt)
#guard (atanTinyRat? tinyQ 53 .Nearest).isSome
#guard (atanTinyRat? (Q "1/1000") 53 .Nearest).isNone
