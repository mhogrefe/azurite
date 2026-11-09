/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PowRatBracket
import Azurite.AzFloat.Pow

/-!
## `x^q` for a float `x` and a rational `q`

`powRatPrecRound x q p mode` is `x^q` for a float `x` and an `AzRat` `q`, correctly rounded to
precision `p` in `mode`, with the comparison against the exact value; `powRat x q p` rounds to
nearest.  The structure of `powPrecRound` (`AzFloat/Pow.lean`) with the exponent `q = ±num/den`
in lowest terms:

* **Integer exponents** (`den = 1`): `powIntOrZiv` with `n = ±num` — the exact power when
  `powIntCheap` allows, Ziv's loop on `exp (n ln |x|)` otherwise.
* **Non-integer exponents** (`den ≥ 2`), `x > 0`: `powRatExact?` decides whether `x^q` is
  rational — exactly when `x = m 2^t` has `den ∣ t` and `m` a `den`-th power — and gives
  `x^q = z^(±num)` for the float `z = u 2^(t/den)`, handled as an integer power; otherwise `x^q`
  is irrational and Ziv's loop on `powRatApprox` (the bracket of `exp (q ln x)` from the float
  below `q`) is certified.  `x < 0` gives `NaN`.
* **Special values** as for `powPrecRound`: `x^0 = 1` even for `NaN`; `NaN^q = NaN` otherwise;
  `(±∞)^q` by the sign of `q` (and the parity of an integer `q` for `−∞`); `0^q = 0` for `q > 0`,
  `+∞` for `q < 0`; `1^q = 1`.  The specification `powRatPrecRound_eq` is in `Equiv/PowRat.lean`:
  `roundVal p mode (Spec.pow x.toVal (some q))`.
-/

namespace Azurite.AzFloat

/-- `x^q` rounded to precision `p` with `mode`, and the comparison with the exact value
(`(nan, .eq)` for `p = 0` unless the value is `0` or an infinity). -/
def powRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if hq0 : q.num = 0 then (if p = 0 then (nan, .eq) else setPrecRound one p mode)
  else
    match x with
    | nan => (nan, .eq)
    | zero => if q.sign then (zero, .eq) else (infinity true, .eq)
    | infinity sx =>
      if sx then (if q.sign then (infinity true, .eq) else (zero, .eq))
      else if q.sign then
        (if q.den = 1 ∧ q.num.isOdd then (infinity false, .eq) else (infinity true, .eq))
      else (zero, .eq)
    | finite sx ex qx mx hvx =>
      if hp : p = 0 then (nan, .eq)
      else if eqIEEE (finite sx ex qx mx hvx) one then setPrecRound one p mode
      else
        haveI : NeZero p := ⟨hp⟩
        if hd : q.den = 1 then
          powIntOrZiv sx ex qx mx hvx (AzInt.mkNorm q.sign q.num) (mkNorm_ne_zero hq0) p mode
        else if hsx : sx = false then (nan, .eq)
        else
          match hex : powRatExact? ex mx q with
          | some (z, N) =>
            match z with
            | finite true ez qz mz hvz =>
              if hN : N = 0 then (nan, .eq)
              else powIntOrZiv true ez qz mz hvz N hN p mode
            | _ => (nan, .eq)
          | none =>
            zivLoopCertified (powRatApprox false (finite true ex qx mx hvx) ex q) p mode
              (powRatStart q ex p)
              (powRatApprox_isSome_exists p mode false ex hvx q
                (by
                  simp only [powSign, Bool.false_eq_true, ↓reduceIte, one_mul]
                  exact not_mem_floatSet_of_irrational p
                    (irrational_of_powRatExact?_none ex hvx q hq0 hd hex))
                (powRatStart q ex p) (by unfold powRatStart zivGuardBits; omega))

/-- `x^q` rounded to nearest at precision `p`. -/
def powRat (x : AzFloat) (q : AzRat) (p : Nat) : AzFloat := (powRatPrecRound x q p .Nearest).1

end Azurite.AzFloat
