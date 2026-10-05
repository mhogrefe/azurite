/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Compare
import Azurite.AzFloat.RoundScaled
import Azurite.AzInt.DivRound
import Azurite.AzNat.Div
import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.ShiftLeft

/-!
# Division

MCA §3.4.2: `x / y = ±(n₁ / n₂) · 2^((e₁ − p₁) − (e₂ − p₂))` for cores `n₁`, `n₂`.  With
`g = p + p₂ − p₁`, or one less when `n₁ / 2^p₁ ≥ n₂ / 2^p₂`, the quotient `n₁ · 2^g / n₂` lies in
`[2^(p−1), 2^p)`, so one rounded integer division (`AzInt.divRound`, which decides the rounding
and the comparison from the remainder) gives the `p`-bit significand, and only a carry to `2^p`
remains to be normalized.  Approximate schemes (Newton reciprocal, short division, Barrett) all
need a correction step before they round correctly and are not used.

`ofFractionRound` rounds an unreduced fraction with the same quotient machinery (no gcd).
Correctness: `Equiv/Div.lean` (`divPrecRound_eq_liftVal₂`, `ofFractionRound_eq`).
-/

namespace Azurite.AzFloat

/-- The rounded quotient of two cores (`n₁` of `p₁` bits at exponent `e₁`, `n₂` of `p₂` bits at
`e₂`), with sign `s`; `hge` says whether `n₁ / 2^p₁ ≥ n₂ / 2^p₂`. -/
def divCores (s : Bool) (e₁ : AzInt) (n₁ : AzNat) (p₁ : Nat) (e₂ : AzInt) (n₂ : AzNat)
    (p₂ : Nat) (hge : Bool) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  let g : AzInt :=
    (AzNat.ofNat (p + p₂)).toAzInt - (AzNat.ofNat (p₁ + (if hge then 1 else 0))).toAzInt
  let A := if g.sign then n₁.shiftLeft g.abs.toNat else n₁
  let B := if g.sign then n₂ else n₂.shiftLeft g.abs.toNat
  let qo := AzInt.divRound (AzInt.mkNorm s A) B.toAzInt mode
  let w := e₁ - (AzNat.ofNat p₁).toAzInt - (e₂ - (AzNat.ofNat p₂).toAzInt) - g
  (normalizeCarry qo.1 (w + (AzNat.ofNat p).toAzInt) p, qo.2)

/-- `x / y` rounded to precision `p` with `mode`, and the comparison with the exact quotient.
`∞ / ∞` and `0 / 0` are `NaN`; `x / 0 = ±∞` with the sign of `x`; `x / ∞ = 0`. -/
def divPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  match x, y with
  | nan, _ => (nan, .eq)
  | _, nan => (nan, .eq)
  | infinity _, infinity _ => (nan, .eq)
  | infinity s, zero => (infinity s, .eq)
  | infinity s, finite t _ _ _ _ => (infinity (s == t), .eq)
  | zero, zero => (nan, .eq)
  | zero, _ => (zero, .eq)
  | finite _ _ _ _ _, infinity _ => (zero, .eq)
  | finite s _ _ _ _, zero => (infinity s, .eq)
  | finite s e₁ p₁ m₁ _, finite t e₂ p₂ m₂ _ =>
    divCores (s == t) e₁ (coreSignificand p₁ m₁) p₁ e₂ (coreSignificand p₂ m₂) p₂
      (compareMagnitude 0 m₁ 0 m₂ != .lt) p mode

instance : Div AzFloat := ⟨fun x y => (divPrecRound x y (combinedPrecision x y) .Nearest).1⟩

/-- The rounding of the fraction `±num / den` to precision `p`, for any numerator and denominator
(no reduction to lowest terms, hence no gcd): the quotient machinery of division applied to the
raw integers.  `den = 0` is unspecified. -/
def ofFractionRound (s : Bool) (num den : AzNat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else if num = 0 then (zero, .eq)
  else
    divCores s (AzNat.ofNat num.size).toAzInt num num.size (AzNat.ofNat den.size).toAzInt den
      den.size (compare (num.shiftLeft den.size) (den.shiftLeft num.size) != .lt) p mode

end Azurite.AzFloat
