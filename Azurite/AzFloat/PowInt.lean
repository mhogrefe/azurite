/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Div
import Azurite.AzFloat.Mul
import Azurite.AzNat.Parity
import Azurite.AzNat.Pow

/-!
## `x^n` for an integer `n`

`powIntExactPrecRound x n p mode` is `x^n` for a float `x` and an `AzInt` `n`, correctly rounded
to precision `p` in `mode`, with the comparison against the exact value, through the exact power.
It costs about `|n| · bits(m)` bits; the public `powIntPrecRound` (`Pow.lean`) uses it only when
that is cheap and Ziv's loop otherwise.  A finite `x = ±m · 2^E` with odd `m` (the left-aligned
significand with its trailing zeros moved into the exponent, so `2^k` costs nothing) has the
exact dyadic power `x^n = ±m^n · 2^(E n)` for `n ≥ 0`, built as the exact floats `±m^n`
(`AzNat.pow`) and `powerOf2 (E n)` and multiplied with one rounding; for `n < 0` it is
`±2^(−E n) / m^|n|`, one correctly rounded division of exact floats.  Special values: `NaN`
propagates; `x^0 = 1` (also for `0`, `±∞`); `0^n = 0` for `n > 0` and `+∞` for `n < 0`;
`(±∞)^n = 0` for `n < 0`, `+∞^n = +∞` and `(−∞)^n = ±∞` by the parity of `n > 0`.  The
specification
`powIntExactPrecRound_eq_liftVal` is in `Equiv/PowInt.lean`.
-/

namespace Azurite.AzFloat

/-- `o^k` for the odd part `o` of a significand: `o` itself when `o = 1`, so that a huge `k`
(an exponent of `2^30` bits, say) is never converted to a `Nat` and powered over all its bits. -/
def powOdd (o k : AzNat) : AzNat := if o = AzNat.ofNat 1 then o else o.pow k.toNat

/-- `x^n` rounded to precision `p` with `mode` through the exact power, and the comparison with
the exact value (`(nan, .eq)` for `p = 0` unless the value is `0` or an infinity). -/
def powIntExactPrecRound (x : AzFloat) (n : AzInt) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s =>
    if n = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else if n.sign then (infinity (s || n.abs.isEven), .eq) else (zero, .eq)
  | zero =>
    if n = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
    else if n.sign then (zero, .eq) else (infinity true, .eq)
  | finite s e _ m _ =>
    if p = 0 then (nan, .eq)
    else if n = 0 then setPrecRound one p mode
    else
      -- the significand is left-aligned: power only its odd part `m / 2^c`
      let c := m.trailingZeros.getD 0
      let t := (e - (AzNat.ofNat m.size).toAzInt + (AzNat.ofNat c).toAzInt) * n.abs.toAzInt
      let neg := !s && n.abs.isOdd
      let mk := ofAzNat (powOdd (m.shiftRight c) n.abs)
      if n.sign then mulPrecRound (if neg then -mk else mk) (powerOf2 t) p mode
      else divPrecRound (if neg then -(powerOf2 (-t)) else powerOf2 (-t)) mk p mode

end Azurite.AzFloat
