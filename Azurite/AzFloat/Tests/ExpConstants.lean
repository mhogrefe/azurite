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
import Azurite.AzFloat.OfString
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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

#guard D (ePrecRound 1 .Nearest) == ("2.0", .lt)
#guard D (ePrecRound 1 .Floor) == ("2.0", .lt)
#guard D (ePrecRound 1 .Ceiling) == ("4.0", .gt)
#guard D (ePrecRound 2 .Nearest) == ("3.0", .gt)
#guard D (ePrecRound 2 .Floor) == ("2.0", .lt)
#guard D (ePrecRound 2 .Ceiling) == ("3.0", .gt)
#guard D (ePrecRound 53 .Nearest) == ("2.718281828459045", .lt)
#guard D (ePrecRound 53 .Floor) == ("2.718281828459045", .lt)
#guard D (ePrecRound 53 .Ceiling) == ("2.7182818284590455", .gt)
#guard D (ePrecRound 100 .Nearest) == ("2.71828182845904523536028747135", .lt)
#guard D (ePrecRound 100 .Floor) == ("2.71828182845904523536028747135", .lt)
#guard D (ePrecRound 100 .Ceiling) == ("2.718281828459045235360287471354", .gt)
#guard D (ln10PrecRound 1 .Nearest) == ("2.0", .lt)
#guard D (ln10PrecRound 1 .Floor) == ("2.0", .lt)
#guard D (ln10PrecRound 1 .Ceiling) == ("4.0", .gt)
#guard D (ln10PrecRound 2 .Nearest) == ("2.0", .lt)
#guard D (ln10PrecRound 2 .Floor) == ("2.0", .lt)
#guard D (ln10PrecRound 2 .Ceiling) == ("3.0", .gt)
#guard D (ln10PrecRound 53 .Nearest) == ("2.302585092994046", .gt)
#guard D (ln10PrecRound 53 .Floor) == ("2.3025850929940455", .lt)
#guard D (ln10PrecRound 53 .Ceiling) == ("2.302585092994046", .gt)
#guard D (ln10PrecRound 100 .Nearest) == ("2.302585092994045684017991454684", .lt)
#guard D (ln10PrecRound 100 .Floor) == ("2.302585092994045684017991454684", .lt)
#guard D (ln10PrecRound 100 .Ceiling) == ("2.302585092994045684017991454687", .gt)
#guard D (log10EPrecRound 1 .Nearest) == ("0.5", .gt)
#guard D (log10EPrecRound 1 .Floor) == ("0.2", .lt)
#guard D (log10EPrecRound 1 .Ceiling) == ("0.5", .gt)
#guard D (log10EPrecRound 2 .Nearest) == ("0.4", .lt)
#guard D (log10EPrecRound 2 .Floor) == ("0.4", .lt)
#guard D (log10EPrecRound 2 .Ceiling) == ("0.5", .gt)
#guard D (log10EPrecRound 53 .Nearest) == ("0.4342944819032518", .lt)
#guard D (log10EPrecRound 53 .Floor) == ("0.4342944819032518", .lt)
#guard D (log10EPrecRound 53 .Ceiling) == ("0.43429448190325187", .gt)
#guard D (log10EPrecRound 100 .Nearest) == ("0.4342944819032518276511289189167", .gt)
#guard D (log10EPrecRound 100 .Floor) == ("0.4342944819032518276511289189163", .lt)
#guard D (log10EPrecRound 100 .Ceiling) == ("0.4342944819032518276511289189167", .gt)
#guard D (log2TenPrecRound 1 .Nearest) == ("4.0", .gt)
#guard D (log2TenPrecRound 1 .Floor) == ("2.0", .lt)
#guard D (log2TenPrecRound 1 .Ceiling) == ("4.0", .gt)
#guard D (log2TenPrecRound 2 .Nearest) == ("3.0", .lt)
#guard D (log2TenPrecRound 2 .Floor) == ("3.0", .lt)
#guard D (log2TenPrecRound 2 .Ceiling) == ("4.0", .gt)
#guard D (log2TenPrecRound 53 .Nearest) == ("3.321928094887362", .lt)
#guard D (log2TenPrecRound 53 .Floor) == ("3.321928094887362", .lt)
#guard D (log2TenPrecRound 53 .Ceiling) == ("3.3219280948873626", .gt)
#guard D (log2TenPrecRound 100 .Nearest) == ("3.32192809488736234787031942949", .gt)
#guard D (log2TenPrecRound 100 .Floor) == ("3.321928094887362347870319429487", .lt)
#guard D (log2TenPrecRound 100 .Ceiling) == ("3.32192809488736234787031942949", .gt)
#guard D (log10TwoPrecRound 1 .Nearest) == ("0.2", .lt)
#guard D (log10TwoPrecRound 1 .Floor) == ("0.2", .lt)
#guard D (log10TwoPrecRound 1 .Ceiling) == ("0.5", .gt)
#guard D (log10TwoPrecRound 2 .Nearest) == ("0.25", .lt)
#guard D (log10TwoPrecRound 2 .Floor) == ("0.25", .lt)
#guard D (log10TwoPrecRound 2 .Ceiling) == ("0.4", .gt)
#guard D (log10TwoPrecRound 53 .Nearest) == ("0.3010299956639812", .gt)
#guard D (log10TwoPrecRound 53 .Floor) == ("0.30102999566398114", .lt)
#guard D (log10TwoPrecRound 53 .Ceiling) == ("0.3010299956639812", .gt)
#guard D (log10TwoPrecRound 100 .Nearest) == ("0.3010299956639811952137388947246", .gt)
#guard D (log10TwoPrecRound 100 .Floor) == ("0.3010299956639811952137388947242", .lt)
#guard D (log10TwoPrecRound 100 .Ceiling) == ("0.3010299956639811952137388947246", .gt)

-- precision `0`
#guard D (ePrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (ln10PrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (log10EPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (log2TenPrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (log10TwoPrecRound 0 .Nearest) == ("NaN", .eq)

-- agreement with the general functions
#guard e 200 == exp (X "1" 200)
#guard ln10 200 == lnRat (Q "10") 200
#guard ln10 150 == ln (X "10" 150)
#guard log10Two 150 == logBase (X "2" 150) 10
#guard log2Ten 150 == log2 (X "10" 150)

-- decimal strings at 53 bits
#guard toString (e 53) == "2.718281828459045"
#guard toString (ln10 53) == "2.302585092994046"
#guard toString (log10E 53) == "0.4342944819032518"
#guard toString (log2Ten 53) == "3.321928094887362"
#guard toString (log10Two 53) == "0.3010299956639812"
