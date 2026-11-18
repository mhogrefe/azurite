/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2
import Azurite.AzFloat.HexString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln 2`

`ln 2 = 0.6931471805599453094172321214581765680755…`.  At `p` bits the candidates in `[1/2, 1)`
are `m/2^p`; `ln 2 · 2^53 = 6243314768165359.2088…` and
`ln 2 · 2^100 = 878668439483319573618263538048.2468…` (60-digit arithmetic), so rounding to
nearest goes down at both precisions.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (ln2PrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (ln2PrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (ln2PrecRound 2 .Nearest) == ("0.8", .gt)
#guard D (ln2PrecRound 2 .Floor) == ("0.5", .lt)
#guard D (ln2PrecRound 3 .Nearest) == ("0.8", .gt)
#guard D (ln2PrecRound 3 .Floor) == ("0.6", .lt)
#guard D (ln2PrecRound 53 .Nearest) == ("0.6931471805599453", .lt)
#guard D (ln2PrecRound 53 .Floor) == ("0.6931471805599453", .lt)
#guard D (ln2PrecRound 53 .Ceiling) == ("0.6931471805599454", .gt)
#guard D (ln2PrecRound 100 .Nearest) == ("0.693147180559945309417232121458", .lt)
#guard D (ln2PrecRound 100 .Up) == ("0.693147180559945309417232121459", .gt)
#guard toString (ln2 53) == "0.6931471805599453"

/-! ## `log₂ e = 1/ln 2 = 1.4426950408889634073992468100189213742664595415298…`

`log₂ e · 2^52 = 6497320848556798.0916…`, `log₂ e · 2^99 = 914416617264592211221101407494.5696…`. -/

#guard D (log2EPrecRound 1 .Nearest) == ("1.0", .lt)
#guard D (log2EPrecRound 1 .Ceiling) == ("2.0", .gt)
#guard D (log2EPrecRound 2 .Nearest) == ("1.5", .gt)
#guard D (log2EPrecRound 3 .Nearest) == ("1.5", .gt)
#guard D (log2EPrecRound 3 .Floor) == ("1.2", .lt)
#guard D (log2EPrecRound 53 .Nearest) == ("1.4426950408889634", .lt)
#guard D (log2EPrecRound 53 .Ceiling) == ("1.4426950408889636", .gt)
#guard D (log2EPrecRound 100 .Nearest) == ("1.442695040888963407359924681003", .gt)
#guard D (log2EPrecRound 100 .Floor) == ("1.442695040888963407359924681001", .lt)
#guard toString (log2E 53) == "1.4426950408889634"
