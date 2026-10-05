/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.MulRat

/-!
# Division between an `AzFloat` and an `AzRat`

`x / q` and `q / x` for a float `x = ± m · 2^(e − |m|)` and a rational `q = ± num / den`,
correctly rounded to a destination precision `p`.  As for the product, the exponent of `x`
factors out as a pure shift:

* `x / q = ± (m · den / num) · 2^(e − |m|)`,
* `q / x = ± (num / (den · m)) · 2^(|m| − e)`,

so each is one `ofFractionRound` (a single division, no reduction) followed by an exact shift.
The special values follow `Spec.div` (`Equiv/Div.lean`): a nonzero value over `0` is `±∞` by
its sign, `0 / 0` and `∞ / ∞` are `NaN`, a finite value over `±∞` is `0`.  `Equiv/DivRat.lean`
proves `divRatPrecRound x q p mode = liftVal (fun a => Spec.div a q) x p mode` and
`ratDivPrecRound q x p mode = liftVal (fun a => Spec.div q a) x p mode`.

The `/` instances round to nearest at the float's precision (`ratOpPrecision`).
-/

namespace Azurite.AzFloat

/-- `x / q` rounded to precision `p` with `mode`, and the comparison with the exact quotient. -/
def divRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity s => if q.num = 0 then (infinity s, .eq) else (infinity (s == q.sign), .eq)
  | zero => if q.num = 0 then (nan, .eq) else (zero, .eq)
  | finite s e _ m _ =>
    if q.num = 0 then (infinity s, .eq)
    else
      let r := ofFractionRound (s == q.sign) (m * q.den) q.num p mode
      (r.1 <<< (e - (AzNat.ofNat m.size).toAzInt), r.2)

/-- `q / x` rounded to precision `p` with `mode`, and the comparison with the exact quotient. -/
def ratDivPrecRound (q : AzRat) (x : AzFloat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (zero, .eq)
  | zero => if q.num = 0 then (nan, .eq) else (infinity q.sign, .eq)
  | finite s e _ m _ =>
    let r := ofFractionRound (q.sign == s) q.num (q.den * m) p mode
    (r.1 <<< ((AzNat.ofNat m.size).toAzInt - e), r.2)

instance : HDiv AzFloat AzRat AzFloat :=
  ⟨fun x q => (divRatPrecRound x q (ratOpPrecision x) .Nearest).1⟩

instance : HDiv AzRat AzFloat AzFloat :=
  ⟨fun q x => (ratDivPrecRound q x (ratOpPrecision x) .Nearest).1⟩

end Azurite.AzFloat
