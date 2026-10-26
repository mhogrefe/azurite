/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpConstants
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.LogBase
import Azurite.AzFloat.Log2
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `e`, `ln 10`, `log₁₀ e`, `log₂ 10` and `log₁₀ 2`

`e = 2.71828182845904523536028747135266249775724709369995957496696762772407663…`,
`ln 10 = 2.30258509299404568401799145468436420760110148862877297603332790096757260…`,
`log₁₀ e = 0.434294481903251827651128918916605082294397005803666566114453783165864649…`,
`log₂ 10 = 3.32192809488736234787031942948939017586483139302458061205475639581593477…`,
`log₁₀ 2 = 0.301029995663981195213738894724493026768189881462108541310427461127108189…`.
The correctly rounded values at 1, 2, 53 and 100 bits in the nearest, floor and ceiling modes
(from 80-digit decimal values), precision `0`, agreement with the general functions, and the
decimal strings at 53 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard ePrecRound 1 .Nearest == (F "2" 1, .lt)
#guard ePrecRound 1 .Floor == (F "2" 1, .lt)
#guard ePrecRound 1 .Ceiling == (F "4" 1, .gt)
#guard ePrecRound 2 .Nearest == (F "3" 2, .gt)
#guard ePrecRound 2 .Floor == (F "2" 2, .lt)
#guard ePrecRound 2 .Ceiling == (F "3" 2, .gt)
#guard ePrecRound 53 .Nearest == (F "6121026514868073/2251799813685248" 53, .lt)
#guard ePrecRound 53 .Floor == (F "6121026514868073/2251799813685248" 53, .lt)
#guard ePrecRound 53 .Ceiling == (F "3060513257434037/1125899906842624" 53, .gt)
#guard ePrecRound 100 .Nearest
  == (F "430728948929449700355022696705/158456325028528675187087900672" 100, .lt)
#guard ePrecRound 100 .Floor
  == (F "430728948929449700355022696705/158456325028528675187087900672" 100, .lt)
#guard ePrecRound 100 .Ceiling
  == (F "861457897858899400710045393411/316912650057057350374175801344" 100, .gt)
#guard ln10PrecRound 1 .Nearest == (F "2" 1, .lt)
#guard ln10PrecRound 1 .Floor == (F "2" 1, .lt)
#guard ln10PrecRound 1 .Ceiling == (F "4" 1, .gt)
#guard ln10PrecRound 2 .Nearest == (F "2" 2, .lt)
#guard ln10PrecRound 2 .Floor == (F "2" 2, .lt)
#guard ln10PrecRound 2 .Ceiling == (F "3" 2, .gt)
#guard ln10PrecRound 53 .Nearest == (F "2592480341699211/1125899906842624" 53, .gt)
#guard ln10PrecRound 53 .Floor == (F "5184960683398421/2251799813685248" 53, .lt)
#guard ln10PrecRound 53 .Ceiling == (F "2592480341699211/1125899906842624" 53, .gt)
#guard ln10PrecRound 100 .Nearest
  == (F "91214792975327357045064969303/39614081257132168796771975168" 100, .lt)
#guard ln10PrecRound 100 .Floor
  == (F "91214792975327357045064969303/39614081257132168796771975168" 100, .lt)
#guard ln10PrecRound 100 .Ceiling
  == (F "729718343802618856360519754425/316912650057057350374175801344" 100, .gt)
#guard log10EPrecRound 1 .Nearest == (F "1/2" 1, .gt)
#guard log10EPrecRound 1 .Floor == (F "1/4" 1, .lt)
#guard log10EPrecRound 1 .Ceiling == (F "1/2" 1, .gt)
#guard log10EPrecRound 2 .Nearest == (F "3/8" 2, .lt)
#guard log10EPrecRound 2 .Floor == (F "3/8" 2, .lt)
#guard log10EPrecRound 2 .Ceiling == (F "1/2" 2, .gt)
#guard log10EPrecRound 53 .Nearest == (F "3911776933737095/9007199254740992" 53, .lt)
#guard log10EPrecRound 53 .Floor == (F "3911776933737095/9007199254740992" 53, .lt)
#guard log10EPrecRound 53 .Ceiling == (F "7823553867474191/18014398509481984" 53, .gt)
#guard log10EPrecRound 100 .Nearest
  == (F "1101067321320930181902300261115/2535301200456458802993406410752" 100, .gt)
#guard log10EPrecRound 100 .Floor
  == (F "550533660660465090951150130557/1267650600228229401496703205376" 100, .lt)
#guard log10EPrecRound 100 .Ceiling
  == (F "1101067321320930181902300261115/2535301200456458802993406410752" 100, .gt)
#guard log2TenPrecRound 1 .Nearest == (F "4" 1, .gt)
#guard log2TenPrecRound 1 .Floor == (F "2" 1, .lt)
#guard log2TenPrecRound 1 .Ceiling == (F "4" 1, .gt)
#guard log2TenPrecRound 2 .Nearest == (F "3" 2, .lt)
#guard log2TenPrecRound 2 .Floor == (F "3" 2, .lt)
#guard log2TenPrecRound 2 .Ceiling == (F "4" 2, .gt)
#guard log2TenPrecRound 53 .Nearest == (F "7480317065143153/2251799813685248" 53, .lt)
#guard log2TenPrecRound 53 .Floor == (F "7480317065143153/2251799813685248" 53, .lt)
#guard log2TenPrecRound 53 .Ceiling == (F "3740158532571577/1125899906842624" 53, .gt)
#guard log2TenPrecRound 100 .Nearest
  == (F "1052761035849745868401611337717/316912650057057350374175801344" 100, .gt)
#guard log2TenPrecRound 100 .Floor
  == (F "263190258962436467100402834429/79228162514264337593543950336" 100, .lt)
#guard log2TenPrecRound 100 .Ceiling
  == (F "1052761035849745868401611337717/316912650057057350374175801344" 100, .gt)
#guard log10TwoPrecRound 1 .Nearest == (F "1/4" 1, .lt)
#guard log10TwoPrecRound 1 .Floor == (F "1/4" 1, .lt)
#guard log10TwoPrecRound 1 .Ceiling == (F "1/2" 1, .gt)
#guard log10TwoPrecRound 2 .Nearest == (F "1/4" 2, .lt)
#guard log10TwoPrecRound 2 .Floor == (F "1/4" 2, .lt)
#guard log10TwoPrecRound 2 .Ceiling == (F "3/8" 2, .gt)
#guard log10TwoPrecRound 53 .Nearest == (F "5422874305198591/18014398509481984" 53, .gt)
#guard log10TwoPrecRound 53 .Floor == (F "2711437152599295/9007199254740992" 53, .lt)
#guard log10TwoPrecRound 53 .Ceiling == (F "5422874305198591/18014398509481984" 53, .gt)
#guard log10TwoPrecRound 100 .Nearest
  == (F "763201709380294112488717654721/2535301200456458802993406410752" 100, .gt)
#guard log10TwoPrecRound 100 .Floor
  == (F "11925026709067095507636213355/39614081257132168796771975168" 100, .lt)
#guard log10TwoPrecRound 100 .Ceiling
  == (F "763201709380294112488717654721/2535301200456458802993406410752" 100, .gt)

-- precision `0`
#guard ePrecRound 0 .Nearest == (zero, .lt)
#guard ln10PrecRound 0 .Nearest == (zero, .lt)
#guard log10EPrecRound 0 .Nearest == (zero, .lt)
#guard log2TenPrecRound 0 .Nearest == (zero, .lt)
#guard log10TwoPrecRound 0 .Nearest == (zero, .lt)

-- agreement with the general functions
#guard e 200 == exp (F "1" 200)
#guard ln10 200 == lnRat (Q "10") 200
#guard ln10 150 == ln (F "10" 150)
#guard log10Two 150 == logBase (F "2" 150) 10
#guard log2Ten 150 == log2 (F "10" 150)

-- decimal strings at 53 bits
#guard toString (e 53) == "2.718281828459045"
#guard toString (ln10 53) == "2.302585092994046"
#guard toString (log10E 53) == "0.4342944819032518"
#guard toString (log2Ten 53) == "3.321928094887362"
#guard toString (log10Two 53) == "0.3010299956639812"
