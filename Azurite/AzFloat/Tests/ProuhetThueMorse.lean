/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.HexString
import Azurite.AzFloat.ProuhetThueMorse
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Prouhet–Thue–Morse constant

`τ = 0.0110 1001 1001 0110 1001 0110 0110 1001…₂ = 0.41245403364010759778…`.  The low
precisions are rounded by hand from the expansion (the significant bits start at the second
place); the hexadecimal digits are the Thue–Morse word `0x6996966996696996` and its complement
`0x9669699669969669`, each nibble carrying four terms.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

/-! ## The sequence and the words -/

#guard (List.range 16).map (fun n => if prouhetThueMorseSeq n then 1 else 0)
  == [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0]
#guard prouhetThueMorseSeq 64 == true
#guard prouhetThueMorseSeq 65 == false
#guard prouhetThueMorseLimb 0 == prouhetThueMorseWord
#guard prouhetThueMorseLimb 1 == prouhetThueMorseWordNot
#guard prouhetThueMorseLimb 3 == prouhetThueMorseWord
#guard prouhetThueMorseWord + prouhetThueMorseWordNot == 0xFFFFFFFFFFFFFFFF

/-! ## Rounding -/

#guard D (prouhetThueMorsePrecRound 0 .Nearest) == ("NaN", .eq)
#guard D (prouhetThueMorsePrecRound 1 .Nearest) == ("0.5", .gt)  -- 0.01|1…
#guard D (prouhetThueMorsePrecRound 1 .Floor) == ("0.2", .lt)
#guard D (prouhetThueMorsePrecRound 2 .Nearest) == ("0.4", .lt)  -- 0.011|0…
#guard D (prouhetThueMorsePrecRound 3 .Nearest) == ("0.44", .gt)  -- 0.0110|1…
#guard D (prouhetThueMorsePrecRound 3 .Down) == ("0.4", .lt)
#guard D (prouhetThueMorsePrecRound 4 .Nearest) == ("0.4", .lt)  -- 0.01101|0…
#guard D (prouhetThueMorsePrecRound 4 .Ceiling) == ("0.44", .gt)
#guard toHexString (prouhetThueMorse 53) == "0x0.69969669966968#53"
#guard toString (prouhetThueMorse 53) == "0.4124540336401076"
#guard (toHexString (prouhetThueMorsePrecRound 64 .Floor).1,
    (prouhetThueMorsePrecRound 64 .Floor).2) == ("0x0.69969669966969968#64", .lt)
#guard (toHexString (prouhetThueMorsePrecRound 130 .Ceiling).1,
    (prouhetThueMorsePrecRound 130 .Ceiling).2)
  == ("0x0.69969669966969969669699669969669a#130", .gt)
#guard toString (prouhetThueMorse 100) == "0.4124540336401075977833613682584"
