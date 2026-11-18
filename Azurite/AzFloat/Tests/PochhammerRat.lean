/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PochhammerRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzRat.Instances

/-!
# Tests for Pochhammer's symbol of a rational

The special values (`(q)₀ = 1`, the exact zeros where a factor vanishes, `p = 0`), small `n`
through the exact path (`(1/2)₃ = 15/8`, `(−5/2)₄ = −15/16`, `(1/3)₃ = 28/27`), `n = 128` and
`129` on either side of its bound, larger `n` through the loop — positive, negative and
sign-straddling arguments — checked against the product taken in exact rational arithmetic,
other precisions, and agreement with the float function on dyadic arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def P (q : String) (n p : Nat) (m : RoundingMode := .Nearest) :=
  pochhammerRatPrecRound (Q q) n p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P "1/3" 0 53) == ("1.0", .eq)
#guard D (P "0" 0 53) == ("1.0", .eq)
#guard D (P "-3" 0 53) == ("1.0", .eq)
#guard D (P "1/3" 0 0) == ("NaN", .eq)
#guard D (P "0" 1 53) == ("0.0", .eq)
#guard D (P "0" 5 0) == ("0.0", .eq)
#guard D (P "-2" 3 53) == ("0.0", .eq)
#guard D (P "-2" 1000000 53) == ("0.0", .eq)
#guard D (P "-5" 6 53) == ("0.0", .eq)
#guard D (P "1/3" 5 0) == ("NaN", .eq)

-- small `n`: the exact path
#guard D (P "1" 5 53) == ("1.2e2", .eq)
#guard D (P "1/3" 1 53) == ("0.3333333333333333", .lt)
#guard D (P "1/3" 3 53) == ("1.037037037037037", .lt)
#guard D (P "1/3" 3 53 .Floor) == ("1.037037037037037", .lt)
#guard D (P "1/2" 3 53) == ("1.875", .eq)
#guard D (P "-5/2" 4 53) == ("-0.9375", .eq)
#guard D (P "-7/3" 3 53) == ("-1.037037037037037", .gt)
#guard D (P "-7/3" 5 53 .Ceiling) == ("-1.1522633744855966", .gt)
#guard D (P "-5" 3 53) == ("-6.0e1", .eq)
#guard D (P "22/7" 10 53) == ("300198104.72969264", .gt)
#guard D (P "1/1000000007" 4 53) == ("5.999999969e-9", .gt)
#guard D (P "-123456789/1000" 7 53 .Down) == ("-4.3704983981433445e35", .gt)

-- `n = 128` and `129`
#guard D (P "1/3" 128 53) == ("5.662569472428049e213", .lt)
#guard D (P "1/3" 129 53) == ("7.266964156282663e215", .gt)
#guard D (P "1/3" 129 53 .Floor) == ("7.266964156282662e215", .lt)
#guard D (P "1/3" 129 53 .Ceiling) == ("7.266964156282663e215", .gt)
#guard D (P "-7/3" 129 53) == ("-3.6205775770541235e210", .gt)

-- larger `n`: positive, negative and sign-straddling arguments
#guard D (P "1/3" 200 53) == ("8.603289796878314e372", .lt)
#guard D (P "-1/3" 200 53) == ("-1.6617057396153727e371", .lt)
#guard D (P "-301/3" 200 53) == ("-2.411672218035846e313", .lt)
#guard D (P "-301/3" 200 53 .Up) == ("-2.411672218035846e313", .lt)
#guard D (P "-901/3" 200 53) == ("4.722791621985214e456", .gt)
#guard D (P "-250" 200 53) == ("1.0629467857114953e428", .lt)
#guard D (P "5/7" 1000 53) == ("4.381359313535593e2566", .gt)

-- both paths against the product in exact rational arithmetic (the loop from `n = 1000`,
-- or `300` for the long argument)
private def exact (q : String) (n p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  ofAzRatRound ((List.range n).foldl (fun acc j => acc * (Q q + Q (toString j))) (Q "1")) p m
#guard P "1/3" 129 53 == exact "1/3" 129 53 .Nearest
#guard P "1/3" 200 53 .Floor == exact "1/3" 200 53 .Floor
#guard P "-1/3" 200 53 .Up == exact "-1/3" 200 53 .Up
#guard P "-301/3" 200 53 == exact "-301/3" 200 53 .Nearest
#guard P "-301/3" 201 100 .Ceiling == exact "-301/3" 201 100 .Ceiling
#guard P "-901/3" 200 53 .Down == exact "-901/3" 200 53 .Down
#guard P "-250" 200 53 == exact "-250" 200 53 .Nearest
#guard P "5/7" 400 80 == exact "5/7" 400 80 .Nearest
#guard P "1/3" 1000 53 == exact "1/3" 1000 53 .Nearest
#guard P "-1001/3" 1000 53 .Floor == exact "-1001/3" 1000 53 .Floor
#guard P "-4001/3" 1000 53 .Up == exact "-4001/3" 1000 53 .Up
#guard P "123456789123456789/1000000000000000007" 300 53
  == exact "123456789123456789/1000000000000000007" 300 53 .Nearest

-- other precisions
#guard D (P "1/3" 300 1) == ("2.0e612", .lt)
#guard D (P "1/3" 300 20) == ("2.548387e612", .gt)
#guard D (P "1/3" 300 200)
  == ("2.548386202868079508904134953411587588914218543774401601412141e612", .gt)
#guard D (P "-301/3" 200 200 .Floor)
  == ("-2.411672218035845831651616336271099098575642100075240737023424e313", .lt)
#guard D (P "1/3" 10 1000) == ("288591.23778556791816965570966485461227116462598858575081711798675\
  676133380751579196938136124235804162644583312164473572795474944537587427390811021355145726430591\
    5426171484699148165083235956578434859184744872902165997730698233670341580721096038882961608155\
    93828854002608003522498264153499635895612118747", .lt)

-- agreement with the float function on dyadic arguments
#guard P "1/2" 200 53 == pochhammerPrecRound (X "0.5" 53) 200 53 .Nearest
#guard P "-201/2" 200 53 .Floor == pochhammerPrecRound (X "-100.5" 53) 200 53 .Floor
#guard P "-5/2" 4 53 == pochhammerPrecRound (X "-2.5" 53) 4 53 .Nearest

-- `pochhammerRat`
#guard toString (pochhammerRat (Q "1/2") 3 53) == "1.875"
#guard toString (pochhammerRat (Q "1/3") 3 53) == "1.037037037037037"
