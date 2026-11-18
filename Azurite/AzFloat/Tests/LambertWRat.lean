/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LambertW
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for the Lambert `W` function of a rational

The special values (`0`, below the branch point — `−3678794412/10¹⁰ < −e⁻¹` —, `W₋₁` of a
positive rational, `p = 0`), `W₀` and `W₋₁` at exact rationals (`1/10`, `1/3`, `22/7`, `10¹²`,
`−1/10`, `−1/3`, `−9/25`, `−10⁻³⁰`, and `−3678794411/10¹⁰` just above `−e⁻¹`, `q ≈ 1.9·10⁻¹⁰`) in
the three modes with 120-digit references, agreement with the float versions on exactly
representable arguments, and 200-bit values.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W0 (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lambertW0RatPrecRound (Q q) p m
private def Wm (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lambertWm1RatPrecRound (Q q) p m
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W0 "0" 53) == ("0.0", .eq)
#guard D (W0 "0" 0) == ("0.0", .eq)
#guard D (W0 "1" 0) == ("NaN", .eq)
#guard D (W0 "-1" 53) == ("NaN", .eq)
#guard D (W0 "-3678794412/10000000000" 53) == ("NaN", .eq)
#guard D (Wm "0" 53) == ("-Infinity", .eq)
#guard D (Wm "0" 0) == ("-Infinity", .eq)
#guard D (Wm "-1/4" 0) == ("NaN", .eq)
#guard D (Wm "1/2" 53) == ("NaN", .eq)
#guard D (Wm "-1" 53) == ("NaN", .eq)
#guard D (Wm "-3678794412/10000000000" 53) == ("NaN", .eq)

-- `W₀`
#guard D (W0 "1/10" 53) == ("0.09127652716086226", .lt)
#guard D (W0 "1/10" 53 .Ceiling) == ("0.09127652716086228", .gt)
#guard D (W0 "1/3" 53) == ("0.2576276530497367", .gt)
#guard D (W0 "1/3" 53 .Ceiling) == ("0.2576276530497367", .gt)
#guard D (W0 "22/7" 53) == ("1.0738665609038538", .lt)
#guard D (W0 "22/7" 53 .Ceiling) == ("1.073866560903854", .gt)
#guard D (W0 "1000000000000" 53) == ("24.43500440493491", .lt)
#guard D (W0 "-1/10" 53) == ("-0.11183255915896297", .lt)
#guard D (W0 "-1/10" 53 .Floor) == ("-0.11183255915896297", .lt)
#guard D (W0 "-1/3" 53) == ("-0.6190612867359451", .gt)
#guard D (W0 "-1/3" 53 .Ceiling) == ("-0.6190612867359451", .gt)
#guard D (W0 "-9/25" 53) == ("-0.8060843159708178", .gt)
#guard D (W0 "-9/25" 53 .Ceiling) == ("-0.8060843159708178", .gt)
#guard D (W0 "-3678794411/10000000000" 53) == ("-0.999980292244517", .gt)
#guard D (W0 "-3678794411/10000000000" 53 .Ceiling) == ("-0.999980292244517", .gt)
#guard D (W0 "-1/1000000000000000000000000000000" 53) == ("-1.0e-30", .lt)
#guard D (W0 "-1/1000000000000000000000000000000" 53 .Floor) == ("-1.0e-30", .lt)

-- `W₋₁`
#guard D (Wm "-1/10" 53) == ("-3.577152063957297", .gt)
#guard D (Wm "-1/10" 53 .Floor) == ("-3.5771520639572976", .lt)
#guard D (Wm "-1/3" 53) == ("-1.5121345516578424", .gt)
#guard D (Wm "-1/3" 53 .Floor) == ("-1.5121345516578426", .lt)
#guard D (Wm "-9/25" 53) == ("-1.222770133978506", .lt)
#guard D (Wm "-9/25" 53 .Ceiling) == ("-1.2227701339785058", .gt)
#guard D (Wm "-3678794411/10000000000" 53) == ("-1.0000197080144169", .lt)
#guard D (Wm "-3678794411/10000000000" 53 .Floor) == ("-1.0000197080144169", .lt)
#guard D (Wm "-1/1000000000000000000000000000000" 53) == ("-73.37311031382298", .lt)
#guard D (Wm "-1/1000000000000000000000000000000" 53 .Ceiling) == ("-73.37311031382296", .gt)

-- agreement with the float versions on exactly representable arguments
#guard W0 "1/2" 53 == lambertW0PrecRound (X "0.5" 53) 53 .Nearest
#guard W0 "-1/4" 53 .Floor == lambertW0PrecRound (X "-0.25" 53) 53 .Floor
#guard Wm "-1/4" 53 == lambertWm1PrecRound (X "-0.25" 53) 53 .Nearest
#guard Wm "-1/8" 200 .Ceiling == lambertWm1PrecRound (X "-0.125" 200) 200 .Ceiling

-- 200 bits and the nearest wrappers
#guard D (W0 "1/10" 200) == ("0.0912765271608622642998957214231795686531192240514720326483084", .lt)
#guard D (Wm "-1/3" 200) == ("-1.512134551657842473896739678072038704603650385135359454259286", .lt)
#guard lambertW0Rat (Q "1/10") 53 == (W0 "1/10" 53).1
#guard lambertWm1Rat (Q "-1/3") 53 == (Wm "-1/3" 53).1

-- a tiny rational argument (`±1/(3·2^1000)`): the tiny path of `W₀`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard toString (lambertW0RatPrecRound tinyQ 53 .Ceiling).1 == "3.1108787283440633e-302"
#guard (lambertW0RatPrecRound tinyQ 53 .Ceiling).2 == .gt
#guard toString (lambertW0RatPrecRound tinyQ 53 .Floor).1 == "3.110878728344063e-302"
#guard (lambertW0RatPrecRound (-tinyQ) 53 .Floor).2 == .lt
#guard toString (lambertW0RatPrecRound (-tinyQ) 53 .Ceiling).1 == "-3.110878728344063e-302"
