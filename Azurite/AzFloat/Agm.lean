/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Add
import Azurite.AzFloat.AddSubRat
import Azurite.AzFloat.Compare
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Precision
import Azurite.AzFloat.Shift
import Azurite.AzFloat.Sqrt
import Azurite.AzFloat.Ziv
import Azurite.AzRat.Compare

/-!
## The arithmetic–geometric mean

`agmPrecRound x y p mode` is `AGM(x, y)` correctly rounded to precision `p` in `mode`, with the
comparison against the exact value (MCA §4.8).  The iteration
`(a, b) ↦ ((a + b)/2, √(ab))` is run at a working precision `w` as an **interval iteration**:
lower bounds are rounded down and upper bounds up at every operation, so `aLo ≤ a_n ≤ aHi` and
`bLo ≤ b_n ≤ bHi` hold exactly (the step is monotone in both arguments).  Since
`b_n ≤ AGM(x, y) ≤ a_n` for `n ≥ 1`, `[bLo, aHi]` brackets the AGM, and Ziv's loop
(`zivLoop`) raises `w` until the rounding is determined.  The iteration stops once the bracket is
relatively narrow (`agmConverged`, a cheap test that only affects speed, not correctness): the
bracket then has relative width about `2^(8−w)`, so with `w = p + 64` an attempt fails only when
`AGM(x, y)` lies within about `2^(−p−55)` of a `(p+1)`-bit boundary — probability `≈ 2^(−55)` for
a "random" value — and the fuel is exhausted only within `≈ 2^(−15p−1000)` of a boundary.

Two more variants share the engine: `agmRatPrecRound` (two `AzRat`s) and `agmFloatRatPrecRound`
(an `AzFloat` and an `AzRat`), seeding the interval iteration with the floor and ceiling of the
rational at the working precision (`ratBounds`).

Special values: `NaN` or a negative argument gives `NaN`; a zero argument gives `0` unless the
other is `+∞` (`NaN`); `+∞` with a positive argument gives `+∞`; `AGM(x, x) = x` is returned
exactly (rounded to `p`) — this case cannot be left to the loop, since `x` may be a rounding
boundary.

Termination: for distinct positive algebraic `x, y` the value `AGM(x, y)` is transcendental
(Wüstholz's analytic subgroup theorem for non-CM curves, Chudnovsky for the CM case, via
`AGM(1, k') = π/(2K(k))`), so the loop always terminates in principle, but no formal proof is
available; `agmFuel p` caps the doublings of the working precision at four (brackets of width
`2^(−16(p + 64))`), after which `NaN` is returned.  The specification
(`Azurite/AzFloat/Equiv/Agm.lean`) is "correctly rounded or `NaN`".
-/

namespace Azurite.AzFloat

/-- Lower and upper bounds for the current AGM pair `(a_n, b_n)`. -/
structure AgmBounds where
  aLo : AzFloat
  aHi : AzFloat
  bLo : AzFloat
  bHi : AzFloat

/-- One AGM step on the bounds at working precision `w`: lower bounds rounded down, upper bounds
rounded up (the halving is exact). -/
def agmStep (w : Nat) (s : AgmBounds) : AgmBounds :=
  { aLo := (addPrecRound s.aLo s.bLo w .Floor).1 >>> (1 : Nat)
    aHi := (addPrecRound s.aHi s.bHi w .Ceiling).1 >>> (1 : Nat)
    bLo := (sqrtPrecRound (mulPrecRound s.aLo s.bLo w .Floor).1 w .Floor).1
    bHi := (sqrtPrecRound (mulPrecRound s.aHi s.bHi w .Ceiling).1 w .Ceiling).1 }

/-- Stop once `aHi − bLo ≤ aHi · 2^(8−w)` (speed only; any number of steps is correct).  The
rounding noise alone keeps the bracket about `8` ulps wide at precision `w`, so the threshold
must be well above one ulp; `256` ulps is reached as soon as the exact gap `a_n − b_n` has
become negligible. -/
def agmConverged (w : Nat) (s : AgmBounds) : Bool :=
  le (addPrecRound s.aHi (-s.bLo) w .Ceiling).1 (s.aHi >>> (w - 8))

/-- Iterate until converged, at most `fuel` steps. -/
def agmIter (w : Nat) : Nat → AgmBounds → AgmBounds
  | 0, s => s
  | fuel + 1, s => if agmConverged w s then s else agmIter w fuel (agmStep w s)

/-- The exponent magnitude in bits (`0` for non-finite values). -/
def expBits : AzFloat → Nat
  | finite _ e _ _ _ => e.abs.size
  | _ => 0

/-- Steps allowed at working precision `w`: `lg` of the exponent gap to reach the quadratic
regime, then `lg w` more; `w + |e_x| + |e_y| + 2` is far more than enough. -/
def agmIterFuel (x y : AzFloat) (w : Nat) : Nat := w + expBits x + expBits y + 2

/-- The bracket of the AGM from initial bounds `s₀` at working precision `w`: at least one step,
then iterate (at most `fuel` more steps); the ends `bLo ≤ AGM ≤ aHi`, given by their rounding
procedures. -/
def agmApproxFrom (s₀ : AgmBounds) (fuel w : Nat) : Roundable × Roundable :=
  let s := agmIter w fuel (agmStep w s₀)
  (fun p mode => setPrecRound s.bLo p mode, fun p mode => setPrecRound s.aHi p mode)

/-- The bracket of `AGM(x, y)` for exact floats `x, y`. -/
def agmApprox (x y : AzFloat) (w : Nat) : Roundable × Roundable :=
  agmApproxFrom ⟨x, x, y, y⟩ (agmIterFuel x y w) w

/-- The floats below and above a rational at working precision `w`. -/
def ratBounds (q : AzRat) (w : Nat) : AzFloat × AzFloat :=
  ((ofAzRatRound q w .Floor).1, (ofAzRatRound q w .Ceiling).1)

/-- A bit-length proxy for the magnitude of a rational, for the step fuel. -/
def ratExpBits (q : AzRat) : Nat := q.num.size + q.den.size

/-- The bracket of `AGM(q₁, q₂)` for rationals: both seeded by their floor/ceiling at `w`. -/
def agmRatApprox (q₁ q₂ : AzRat) (w : Nat) : Roundable × Roundable :=
  let b₁ := ratBounds q₁ w
  let b₂ := ratBounds q₂ w
  agmApproxFrom ⟨b₁.1, b₁.2, b₂.1, b₂.2⟩ (w + ratExpBits q₁ + ratExpBits q₂ + 2) w

/-- The bracket of `AGM(x, q)` for a float `x` and a rational `q`. -/
def agmFloatRatApprox (x : AzFloat) (q : AzRat) (w : Nat) : Roundable × Roundable :=
  let b := ratBounds q w
  agmApproxFrom ⟨x, x, b.1, b.2⟩ (w + expBits x + ratExpBits q + 2) w

/-- Four doublings of the working precision from `p + 64`. -/
def agmFuel (p : Nat) : Nat := zivFuel (16 * (p + zivGuardBits))

/-- `AGM(x, y)` rounded to precision `p` with `mode`, and the comparison with the exact value
(`NaN` if the fuel runs out, which the transcendence of the AGM rules out in principle). -/
def agmPrecRound (x y : AzFloat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if x.isNaN || y.isNaN then (nan, .eq)
  else if x.isNegative || y.isNegative then (nan, .eq)
  else if x.isZero || y.isZero then
    (if x.isInfinite || y.isInfinite then (nan, .eq) else (zero, .eq))
  else if x.isInfinite || y.isInfinite then (infinity true, .eq)
  else if eqIEEE x y then setPrecRound x p mode
  else zivLoop (agmApprox x y) p mode (agmFuel p) (p + zivGuardBits)

/-- `AGM(x, y)` rounded to nearest at precision `p`. -/
def agm (x y : AzFloat) (p : Nat) : AzFloat := (agmPrecRound x y p .Nearest).1

/-- `AGM(q₁, q₂)` of two rationals, rounded to precision `p` with `mode` (`NaN` for a negative
argument; `0` for a zero one; `q` itself for `q₁ = q₂`). -/
def agmRatPrecRound (q₁ q₂ : AzRat) (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if q₁ < 0 ∨ q₂ < 0 then (nan, .eq)
  else if q₁ = 0 ∨ q₂ = 0 then (zero, .eq)
  else if q₁ = q₂ then ofAzRatRound q₁ p mode
  else zivLoop (agmRatApprox q₁ q₂) p mode (agmFuel p) (p + zivGuardBits)

/-- `AGM(q₁, q₂)` rounded to nearest. -/
def agmRat (q₁ q₂ : AzRat) (p : Nat) : AzFloat := (agmRatPrecRound q₁ q₂ p .Nearest).1

/-- `AGM(x, q)` of a float and a rational, rounded to precision `p` with `mode`.  The exact-equality
case `x = q` (where the loop could not terminate) is detected by the correctly rounded `x − q` at
one bit, which is zero iff `x = q`, without materializing `x` as a rational. -/
def agmFloatRatPrecRound (x : AzFloat) (q : AzRat) (p : Nat) (mode : RoundingMode) :
    AzFloat × Ordering :=
  if x.isNaN then (nan, .eq)
  else if x.isNegative ∨ q < 0 then (nan, .eq)
  else if q = 0 then (if x.isInfinite then (nan, .eq) else (zero, .eq))
  else if x.isZero then (zero, .eq)
  else if x.isInfinite then (infinity true, .eq)
  else if (subRatPrecRound x q 1 .Floor).1.isZero then setPrecRound x p mode
  else zivLoop (agmFloatRatApprox x q) p mode (agmFuel p) (p + zivGuardBits)

/-- `AGM(x, q)` rounded to nearest. -/
def agmFloatRat (x : AzFloat) (q : AzRat) (p : Nat) : AzFloat :=
  (agmFloatRatPrecRound x q p .Nearest).1

end Azurite.AzFloat
