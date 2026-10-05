/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Div
import Azurite.AzFloat.Shift
import Azurite.AzNat.Mul

/-!
# Multiplication of an `AzFloat` by an `AzRat`

`x · q` for a float `x = ± m · 2^(e − |m|)` and a rational `q = ± num / den`, correctly rounded
to a destination precision `p`.  Unlike a sum, the exponent of `x` factors out of a product as
a pure shift: `x · q = ± (m · num / den) · 2^(e − |m|)`.  The fraction `m · num / den` is small
(its parts have the sizes of the inputs) and is rounded in one division by `ofFractionRound`,
which needs no reduction, and the shift is exact — so no approximation loop is needed; this is
also how Malachite proceeds.  `Equiv/MulRat.lean` proves `mulRatPrecRound x q p mode = liftVal
(fun a => Spec.mul a q) x p mode`.

The `*` instances between an `AzFloat` and an `AzRat` round to nearest at the float's precision
(`ratOpPrecision`).
-/

namespace Azurite.AzFloat

/-- `x · q` rounded to precision `p` with `mode`, and the comparison with the exact product. -/
def mulRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if q.num = 0 then (nan, .eq) else (infinity (s == q.sign), .eq)
  | zero => (zero, .eq)
  | finite s e _ m _ =>
    let r := ofFractionRound (s == q.sign) (m * q.num) q.den p mode
    (r.1 <<< (e - (AzNat.ofNat m.size).toAzInt), r.2)

instance : HMul AzFloat AzRat AzFloat :=
  ⟨fun x q => (mulRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

instance : HMul AzRat AzFloat AzFloat :=
  ⟨fun q x => (mulRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

end Azurite.AzFloat
