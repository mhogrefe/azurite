/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnQGamma
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln |Γ_q|` and `ln Γ_q`

The eight functions (the base and the argument each a float or a rational): the bases that
are not positive and finite, the base `1` (`ln |Γ|`, `ln Γ`), arguments that are not finite,
`0` and the poles (`+∞`), `p = 0`, the logarithms of the exact `q`-factorials (`0` at
`n = 1, 2`, `ln (3/2)`, `ln (315/64)`, `ln 2080`), bases below and above `1`, the signs at
negative arguments and `NaN` of `ln Γ_q` there, 200 bits of
`ln Γ_{1/2}(1/2) = 0.45236951172055617770789383382251485649434927133830278347195764…` and of
`ln Γ_{1/3}(1/3) = 0.71406901125832672814847168606304614863816267106863904312398749…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at 53 bits. -/
private def F (s : String) : AzFloat := ofAzRat (Q s) 53
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def DL (r : (AzFloat × Ordering) × Bool) : String × Ordering × Bool :=
  (toString r.1.1, r.1.2, r.2)
private def LA (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsQGammaPrecRound (F q) (F x) p m)
private def L (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnQGammaPrecRound (F q) (F x) p m)
private def LAR (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsQGammaRatPrecRound (Q q) (Q x) p m)
private def LR (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnQGammaRatPrecRound (Q q) (Q x) p m)
private def LAFR (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsQGammaFloatRatPrecRound (F q) (Q x) p m)
private def LFR (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnQGammaFloatRatPrecRound (F q) (Q x) p m)
private def LARF (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsQGammaRatFloatPrecRound (Q q) (F x) p m)
private def LRF (q x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnQGammaRatFloatPrecRound (Q q) (F x) p m)

/-! ### Floats -/

-- bases and arguments that are not finite, bases `≤ 0`, `p = 0`
#guard DL (lnAbsQGammaPrecRound nan (F "1/2") 53 .Nearest) == ("NaN", .eq, true)
#guard DL (lnAbsQGammaPrecRound (F "1/2") nan 53 .Nearest) == ("NaN", .eq, true)
#guard DL (lnAbsQGammaPrecRound (infinity true) (F "1/2") 53 .Nearest) == ("NaN", .eq, true)
#guard DL (lnAbsQGammaPrecRound (F "1/2") (infinity true) 53 .Nearest)
  == ("Infinity", .eq, true)
#guard DL (lnAbsQGammaPrecRound (F "1/2") (infinity false) 53 .Nearest)
  == ("Infinity", .eq, true)
#guard D (lnQGammaPrecRound (F "1/2") (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (lnQGammaPrecRound (F "1/2") (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard D (lnQGammaPrecRound (F "1/2") nan 53 .Nearest) == ("NaN", .eq)
#guard LA "0" "1/2" 53 == ("NaN", .eq, true)
#guard LA "-2" "1/2" 53 == ("NaN", .eq, true)
#guard LA "1/2" "1/2" 0 == ("NaN", .eq, true)

-- `0` and the poles
#guard LA "1/2" "0" 53 == ("Infinity", .eq, true)
#guard LA "1/2" "-3" 53 == ("Infinity", .eq, true)
#guard L "1/2" "0" 53 == ("Infinity", .eq)
#guard L "1/2" "-3" 53 == ("NaN", .eq)

-- the base `1`: `ln |Γ|`, `ln Γ`
#guard LA "1" "5" 53 == ("3.1780538303479458", .gt, true)
#guard LA "1" "-5/2" 53 == ("-0.056243716497674054", .lt, false)
#guard L "1" "5" 53 == ("3.1780538303479458", .gt)
#guard L "1" "-5/2" 53 == ("NaN", .eq)

-- the logarithms of the exact values
#guard LA "1/2" "1" 53 == ("0.0", .eq, true)
#guard LA "1/2" "2" 53 == ("0.0", .eq, true)
#guard LA "1/2" "3" 53 == ("0.4054651081081644", .gt, true)
#guard LA "1/2" "5" 53 == ("1.5936895554659611", .lt, true)
#guard LA "3" "5" 53 == ("7.640123172695364", .gt, true)
#guard LA "2" "20" 53 == ("130.45590411892644", .gt, true)

-- bases below and above `1`
#guard LA "1/2" "1/2" 53 == ("0.45236951172055617", .lt, true)
#guard LA "1/2" "1/2" 53 .Ceiling == ("0.4523695117205562", .gt, true)
#guard LA "1/2" "1/2" 200
  == ("0.4523695117205561777078938338225148564943492713383027834719576", .lt, true)
#guard LA "3/4" "1/4" 53 == ("1.1962652362519794", .gt, true)
#guard LA "2" "1/2" 53 == ("0.7122997044305357", .gt, true)
#guard LA "1/2" "301/3" 53 == ("67.61055784080881", .lt, true)
#guard L "1/2" "1/2" 53 == ("0.45236951172055617", .lt)
#guard L "2" "7/2" 53 == ("1.972722386441955", .lt)

-- negative arguments: the sign, and `NaN` of `ln Γ_q`
#guard LA "1/2" "-1/2" 53 == ("0.6405959181801539", .gt, false)
#guard LA "1/2" "-3/2" 53 == ("-0.6560073649815787", .gt, true)
#guard LA "1/2" "-5/2" 53 == ("-2.887494711970699", .gt, false)
#guard LA "2" "-5/2" 53 == ("2.5710393349388703", .gt, false)
#guard L "1/2" "-5/2" 53 == ("NaN", .eq)
#guard L "1/2" "-3/2" 53 == ("NaN", .eq)

-- to nearest at the precision of the arguments
#guard toString (lnAbsQGamma (F "1/2") (F "1/2")).1 == "0.45236951172055617"
#guard (lnAbsQGamma (F "1/2") (F "-1/2")).2 == false
#guard toString (lnQGamma (F "1/2") (F "1/2")) == "0.45236951172055617"

/-! ### Rationals -/

#guard LAR "1/3" "1/3" 53 == ("0.7140690112583268", .gt, true)
#guard LAR "1/3" "1/3" 200
  == ("0.7140690112583267281484716860630461486381626710686390431239875", .lt, true)
#guard LAR "1/3" "4" 53 == ("0.6554068525770983", .gt, true)
#guard LAR "3" "5" 53 == ("7.640123172695364", .gt, true)
#guard LAR "1/3" "-7/3" 53 == ("-3.8887120013451457", .lt, false)
#guard LAR "1" "1/2" 53 == ("0.5723649429247001", .lt, true)
#guard LAR "1/3" "0" 53 == ("Infinity", .eq, true)
#guard LAR "1/3" "-2" 53 == ("Infinity", .eq, true)
#guard LAR "-1/3" "1/2" 53 == ("NaN", .eq, true)
#guard LR "1/3" "1/3" 53 == ("0.7140690112583268", .gt)
#guard LR "1/3" "-7/3" 53 == ("NaN", .eq)
#guard LR "1/3" "0" 53 == ("Infinity", .eq)
#guard LR "1" "1/2" 53 == ("0.5723649429247001", .lt)
#guard LR "1" "-1/2" 53 == ("NaN", .eq)
#guard toString (lnQGammaRat (Q "1/3") (Q "1/3") 53) == "0.7140690112583268"
#guard (lnAbsQGammaRat (Q "1/3") (Q "-7/3") 53).2 == false

/-! ### A float and a rational -/

#guard LAFR "1/2" "1/3" 53 == ("0.8064201287407794", .gt, true)
#guard LAFR "1/2" "-4/3" 53 == ("-0.2249905737835603", .gt, true)
#guard LFR "1/2" "1/3" 53 == ("0.8064201287407794", .gt)
#guard LFR "1/2" "-4/3" 53 == ("NaN", .eq)
#guard LARF "1/3" "1/2" 53 == ("0.39127174310402474", .lt, true)
#guard LARF "1/3" "-1/2" 53 == ("0.29771199317829605", .lt, false)
#guard LRF "1/3" "1/2" 53 == ("0.39127174310402474", .lt)
#guard LRF "1/3" "-1/2" 53 == ("NaN", .eq)
