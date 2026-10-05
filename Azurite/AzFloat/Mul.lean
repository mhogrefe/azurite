/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.Mul
import Azurite.AzNat.Square

/-!
# Multiplication and squaring

MCA §3.3, Algorithm FPmultiply: the exact product of `±n₁ · 2^(e₁ − p₁)` and `±n₂ · 2^(e₂ − p₂)`
is `±(n₁ n₂) · 2^((e₁ − p₁) + (e₂ − p₂))`, so the significands are multiplied in full (the
`p₁`- and `p₂`-bit cores, no truncation to `n + g` digits) and the product rounded once with
`roundScaled`.  A short product (MCA Algorithm 3.4) only approximates the high part and would need
a fallback to decide the rounding and the comparison; it is left for a later performance pass.

Correctness: `Equiv/Mul.lean` (`mulPrecRound_eq_liftVal₂`, `sqrPrecRound_eq_liftE`).
-/

namespace Azurite.AzFloat

/-- `x · y` rounded to precision `p` with `mode`, and the comparison with the exact product.
`0 · (±∞)` is `NaN`; the sign of an infinite product is the product of the signs. -/
def mulPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x, y with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity s, infinity t => (infinity (s == t), .eq)
  | infinity _, zero => (nan, .eq)
  | zero, infinity _ => (nan, .eq)
  | infinity s, finite t _ _ _ _ => (infinity (s == t), .eq)
  | finite s _ _ _ _, infinity t => (infinity (s == t), .eq)
  | zero, _ => (zero, .eq)
  | _, zero => (zero, .eq)
  | finite s e₁ p₁ m₁ _, finite t e₂ p₂ m₂ _ =>
    roundScaled (s == t) (coreSignificand p₁ m₁ * coreSignificand p₂ m₂)
      (e₁ - (AzNat.ofNat p₁).toAzInt + (e₂ - (AzNat.ofNat p₂).toAzInt)) p mode

/-- `x²` rounded to precision `p` with `mode`, and the comparison with the exact square; the
significand is squared with `AzNat.square`. -/
def sqrPrecRound (x : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x with
  | nan => (nan, .eq)
  | infinity _ => (infinity true, .eq)
  | zero => (zero, .eq)
  | finite _ e q m _ =>
    let w := e - (AzNat.ofNat q).toAzInt
    roundScaled true (AzNat.square (coreSignificand q m)) (w + w) p mode

instance : Mul AzFloat := ⟨fun x y => (mulPrecRound x y (combinedPrecision x y) .Nearest).1⟩

/-- `x²` rounded to nearest at the precision of `x`. -/
def sqr (x : AzFloat) : AzFloat := (sqrPrecRound x (x.precision?.getD 1) .Nearest).1

end Azurite.AzFloat
