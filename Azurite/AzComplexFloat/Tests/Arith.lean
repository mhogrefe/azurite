/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzComplexFloat.Arith
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for the arithmetic on `AzComplexFloat`

Inputs are decimal spellings rounded to nearest at 53 bits; results are shown as the decimal
outputs of the two components with the two comparison tags.
-/

open Azurite Azurite.AzComplexFloat

private def X (s : String) (p : Nat := 53) : AzFloat := (AzFloat.ofDecimalString s p).get!
private def C (a b : String) (p : Nat := 53) : AzComplexFloat := ⟨X a p, X b p⟩
private def D (r : Rounded) : String × String × Ordering × Ordering :=
  (toString r.1.re, toString r.1.im, r.2.1, r.2.2)
private def DR (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def inf : AzFloat := .infinity true

/-! ## Exact operations and predicates -/

#guard toString (-(C "1" "2")).re == "-1.0"
#guard toString (-(C "1" "2")).im == "-2.0"
#guard toString (C "1" "2").conj.re == "1.0"
#guard toString (C "1" "2").conj.im == "-2.0"
#guard (C "0" "0").isZero
#guard !(C "0" "1").isZero
#guard nan.isNaN
#guard (C "1" "2").isFinite
#guard !(⟨inf, .zero⟩ : AzComplexFloat).isFinite

/-! ## Addition and subtraction -/

#guard D (addPrecRound (C "1.5" "2") (C "0.25" "-3") 10 10 .Nearest .Nearest)
  == ("1.75", "-1.0", .eq, .eq)
#guard D (addPrecRound (C "1" "1") (C "0.0009765625" "3") 10 10 .Nearest .Nearest)
  == ("1.0", "4.0", .lt, .eq)
#guard D (addPrecRound (C "1" "1") (C "0.0009765625" "3") 10 10 .Ceiling .Ceiling)
  == ("1.002", "4.0", .gt, .eq)
#guard D (subPrecRound (C "1.5" "2") (C "0.25" "-3") 10 10 .Nearest .Nearest)
  == ("1.25", "5.0", .eq, .eq)
#guard D (addPrecRound ⟨inf, X "1"⟩ ⟨.infinity false, X "1"⟩ 10 10 .Nearest .Nearest)
  == ("NaN", "2.0", .eq, .eq)

/-! ## Multiplication and squaring -/

#guard D (mulPrecRound (C "1" "2") (C "3" "4") 10 10 .Nearest .Nearest)
  == ("-5.0", "1.0e1", .eq, .eq)
#guard D (mulPrecRound i i 10 10 .Nearest .Nearest) == ("-1.0", "0.0", .eq, .eq)
-- (1.1 + 2.3i)(3.7 − 4.9i) = 15.34 + 3.12i for the decimal inputs
#guard D (mulPrecRound (C "1.1" "2.3") (C "3.7" "-4.9") 20 20 .Nearest .Nearest)
  == ("15.34", "3.12", .lt, .lt)
#guard D (mulPrecRound (C "1.1" "2.3") (C "3.7" "-4.9") 100 100 .Nearest .Nearest)
  == ("15.34000000000000047073456244106", "3.11999999999999892530411216285", .lt, .gt)
#guard D (sqrPrecRound (C "3" "4") 10 10 .Nearest .Nearest) == ("-7.0", "24.0", .eq, .eq)
#guard D (sqrPrecRound (C "1.1" "2.3") 20 20 .Nearest .Nearest) == ("-4.08", "5.06", .lt, .lt)
#guard sqrPrecRound (C "1.1" "2.3") 20 20 .Nearest .Nearest
  == mulPrecRound (C "1.1" "2.3") (C "1.1" "2.3") 20 20 .Nearest .Nearest
#guard D (mulPrecRound ⟨inf, .zero⟩ (C "1" "1") 10 10 .Nearest .Nearest)
  == ("Infinity", "Infinity", .eq, .eq)
#guard D (mulFloatPrecRound (C "1.1" "2.3") (X "3") 20 20 .Nearest .Nearest)
  == ("3.3", "6.9", .lt, .gt)
#guard DR (normSqrPrecRound (C "3" "4") 10 .Nearest) == ("25.0", .eq)
#guard DR (normSqrPrecRound (C "1.1" "2.3") 20 .Up) == ("6.5", .gt)

/-! ## Division -/

-- (1 + 2i)/(3 + 4i) = 0.44 + 0.08i
#guard D (divPrecRound (C "1" "2") (C "3" "4") 10 10 .Nearest .Nearest)
  == ("0.44", "0.08", .lt, .lt)
#guard D (divPrecRound (C "1" "2") (C "3" "4") 53 53 .Nearest .Nearest)
  == ("0.44", "0.08", .gt, .gt)
#guard D (divPrecRound (C "1" "2") (C "3" "4") 53 53 .Floor .Floor)
  == ("0.43999999999999995", "0.07999999999999999", .lt, .lt)
#guard D (divPrecRound (C "-7" "24") (C "3" "4") 10 10 .Nearest .Nearest)
  == ("3.0", "4.0", .eq, .eq)
#guard D (divPrecRound one i 10 10 .Nearest .Nearest) == ("0.0", "-1.0", .eq, .eq)
-- far-apart exponents
#guard D (divPrecRound (C "1e30" "1") (C "1" "1e-30") 53 53 .Nearest .Nearest)
  == ("1.0e30", "-1.0322104544624199e-16", .gt, .lt)
-- a zero divisor and non-finite operands give `NaN`
#guard D (divPrecRound (C "1" "2") zero 10 10 .Nearest .Nearest) == ("NaN", "NaN", .eq, .eq)
#guard D (divPrecRound (C "1" "2") ⟨inf, .zero⟩ 10 10 .Nearest .Nearest) == ("NaN", "NaN", .eq, .eq)
#guard D (divPrecRound ⟨.nan, .zero⟩ one 10 10 .Nearest .Nearest) == ("NaN", "NaN", .eq, .eq)
#guard D (divFloatPrecRound (C "1" "2") (X "3") 20 20 .Nearest .Nearest)
  == ("0.3333335", "0.666667", .gt, .gt)
#guard D (divFloatPrecRound (C "1" "2") (X "0") 20 20 .Nearest .Nearest)
  == ("Infinity", "Infinity", .eq, .eq)

/-! ## Different precisions and modes for the two components -/

#guard D (divPrecRound (C "1" "2") (C "3" "4") 10 53 .Nearest .Nearest)
  == ("0.44", "0.08", .lt, .gt)

#guard D (divPrecRound (C "1" "2") (C "3" "4") 53 53 .Floor .Ceiling)
  == ("0.43999999999999995", "0.08", .lt, .gt)
#guard D (mulPrecRound (C "1.1" "2.3") (C "3.7" "-4.9") 20 20 .Ceiling .Floor)
  == ("15.34001", "3.12", .gt, .lt)
#guard D (cisPrecRound (X "1") 53 53 .Floor .Ceiling)
  == ("0.5403023058681397", "0.8414709848078966", .lt, .gt)

/-! ## `e^(ix)` -/

#guard D (cisPrecRound (X "0") 20 20 .Nearest .Nearest) == ("1.0", "0.0", .eq, .eq)
#guard D (cisPrecRound (X "1") 53 53 .Nearest .Nearest)
  == ("0.5403023058681398", "0.8414709848078965", .gt, .lt)
#guard D (cisPrecRound (X "1") 53 53 .Floor .Floor)
  == ("0.5403023058681397", "0.8414709848078965", .lt, .lt)
#guard D (cisPrecRound inf 53 53 .Nearest .Nearest) == ("NaN", "NaN", .eq, .eq)
