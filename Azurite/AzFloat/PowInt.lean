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

`powIntPrecRound x n p mode` is `x^n` for a float `x` and an `AzInt` `n`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `powInt x n` rounds to
nearest at the precision of `x`.  A finite `x = ±m · 2^E` has the exact dyadic power
`x^n = ±m^n · 2^(E n)` for `n ≥ 0`, built as the exact floats `±m^n` (`AzNat.pow`) and
`powerOf2 (E n)` and multiplied with one rounding; for `n < 0` it is `±2^(−E n) / m^|n|`, one
correctly rounded division of exact floats.  Special values: `NaN` propagates; `x^0 = 1` (also
for `0`, `±∞`);
`0^n = 0` for `n > 0` and `+∞` for `n < 0`; `(±∞)^n = 0` for `n < 0`, `+∞^n = +∞` and
`(−∞)^n = ±∞` by the parity of `n > 0`.  The specification
`powIntPrecRound_eq_liftVal` is in `Equiv/PowInt.lean`.
-/

namespace Azurite.AzFloat

/-- `x^n` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or an infinity). -/
def powIntPrecRound (x : AzFloat) (n : AzInt) (p : Nat) (mode : RoundingMode) :
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
      let k := n.abs.toNat
      let t := (e - (AzNat.ofNat m.size).toAzInt) * n.abs.toAzInt
      let neg := !s && n.abs.isOdd
      let mk := ofAzNat (m.pow k)
      if n.sign then mulPrecRound (if neg then -mk else mk) (powerOf2 t) p mode
      else divPrecRound (if neg then -(powerOf2 (-t)) else powerOf2 (-t)) mk p mode

/-- `x^n` rounded to nearest at the precision of `x`. -/
def powInt (x : AzFloat) (n : AzInt) : AzFloat :=
  (powIntPrecRound x n (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
