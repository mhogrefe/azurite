/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CothRat
import Azurite.AzFloat.Coth
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `coth q` of a rational

The special values (`coth 0 = +∞`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, the transition to `±1`, 1-, 2-, 20-,
113- and 200-bit results, agreement with the float `coth` at representable arguments, oddness,
200-bit strings, tiny rationals `±2^(−5000)`, `±1/(3·2^5000)` (just outside `1/q`, at no
cost), and large rationals `±10^6/3`, `±2^5000/3` (just outside `±1`, at no cost).  References:
an independent 6000-bit fixed-point evaluation of `(e^(2q) + 1)/(e^(2q) − 1)` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  cothRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("Infinity", .eq)
#guard D (T "0" 0) == ("Infinity", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("1.3130352854993312", .lt)
#guard D (T "-1" 53) == ("-1.3130352854993312", .gt)
#guard D (T "1/3" 53) == ("3.110296679619444", .gt)
#guard D (T "-2/7" 53) == ("-3.5947237896167397", .gt)
#guard D (T "22/7" 53) == ("1.0037324043984772", .gt)
#guard D (T "355/113" 53) == ("1.003741871197191", .lt)
#guard D (T "-7/5" 53) == ("-1.1294947064598964", .gt)
#guard D (T "10" 53) == ("1.0000000041223072", .lt)
#guard D (T "-100/3" 53) == ("-1.0", .gt)
#guard D (T "1/1000" 53) == ("1000.0003333333111", .gt)
#guard D (T "-1/1000000007" 53) == ("-1000000007.0", .gt)
#guard D (T "3/1125899906842624" 53) == ("375299968947541.3", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("3.0e30", .lt)
#guard D (T "700/3" 53) == ("1.0", .lt)
#guard D (T "1/3" 53 .Floor) == ("3.1102966796194433", .lt)
#guard D (T "-2/7" 53 .Floor) == ("-3.59472378961674", .lt)
#guard D (T "22/7" 53 .Floor) == ("1.003732404398477", .lt)
#guard D (T "-100/3" 53 .Floor) == ("-1.0000000000000002", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("1000000007.0", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("3.110296679619444", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("-3.5947237896167397", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("1.0037324043984772", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("-1.0", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("1000000007.0000001", .gt)
#guard D (T "1/3" 20) == ("3.1103", .gt)
#guard D (T "1/3" 1) == ("4.0", .gt)
#guard D (T "-22/7" 2) == ("-1.0", .gt)
#guard D (T "1/3" 113) == ("3.1102966796194437013783752314176247", .lt)
#guard D (T "-7/5" 200) == ("-1.129494706459896450510955731954660602184848739933190114699503", .lt)

-- the transition to `±1`
#guard D (T "55/3" 53) == ("1.0000000000000002", .lt)
#guard D (T "55/3" 53 .Floor) == ("1.0000000000000002", .lt)
#guard D (T "55/3" 53 .Ceiling) == ("1.0000000000000004", .gt)
#guard D (T "-58/3" 53) == ("-1.0", .gt)
#guard D (T "-58/3" 53 .Floor) == ("-1.0000000000000002", .lt)
#guard D (T "-58/3" 53 .Ceiling) == ("-1.0", .gt)
#guard D (T "61/3" 53) == ("1.0", .lt)
#guard D (T "61/3" 53 .Floor) == ("1.0", .lt)
#guard D (T "61/3" 53 .Ceiling) == ("1.0000000000000002", .gt)

-- agreement with the float `coth` at representable arguments, oddness
#guard T "3/2" 53 == cothPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == cothPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == cothPrecRound (X "100" 53) 20 .Ceiling
#guard cothRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := cothRatPrecRound q p (-m)
  cothRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard toString (cothRat (Q "1/3") 200)
  == "3.110296679619443701378375231417624794566543581787011086057344"
#guard toString (cothRat (Q "-22/7") 200)
  == "-1.003732404398477118693835025095884540928947620006350198124255"

-- tiny rationals: just outside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (cothRatPrecRound (pw 5000) 53 .Nearest) == ("1.412467032139426e1505", .lt)
#guard D (cothRatPrecRound (pw 5000) 53 .Floor) == ("1.412467032139426e1505", .lt)
#guard D (cothRatPrecRound (pw 5000) 53 .Ceiling) == ("1.4124670321394264e1505", .gt)
#guard D (cothRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-1.412467032139426e1505", .gt)
#guard D (cothRatPrecRound (-(pw 5000)) 53 .Floor) == ("-1.4124670321394264e1505", .lt)
#guard D (cothRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest) == ("4.237401096418278e1505", .lt)
#guard D (cothRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling) == ("4.237401096418279e1505", .gt)
#guard D (cothRatPrecRound (Q "3" * pw 5000) 53 .Nearest) == ("4.708223440464753e1504", .lt)

-- large rationals: just outside `±1`
private def bigOk (q : AzRat) : Bool :=
  cothRatPrecRound q 53 .Nearest == (X "1" 53, .lt)
    && cothRatPrecRound q 53 .Floor == (X "1" 53, .lt)
    && cothRatPrecRound q 53 .Ceiling == (up, .gt)
    && cothRatPrecRound (-q) 53 .Nearest == (X "-1" 53, .gt)
    && cothRatPrecRound (-q) 53 .Floor == (-up, .lt)
    && cothRatPrecRound q 200 .Nearest == (X "1" 200, .lt)
#guard bigOk (Q "1000000/3")
#guard bigOk (Q "1/3" * (pw 5000)⁻¹)
#guard bigOk (Q "700/3")
