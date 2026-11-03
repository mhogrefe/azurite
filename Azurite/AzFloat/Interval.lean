/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpApprox
import Azurite.AzFloat.PiBracket
import Azurite.AzFloat.ToString

/-!
# Interval evaluation with directed rounding

An `Encl` is a pair `(lo, hi)` of floats, meant to enclose a real number `x` as
`lo ≤ x ≤ hi`. The operations round the lower end down and the upper end up at a working
precision `w`, so that enclosures propagate through `+`, `−`, `×`, `/` and powers
(`Equiv/Interval.lean`). The base cases are exact floats, `π` (the Brent–Salamin bracket
`piBracket`) and `exp x` (`expBracketAt`).

Everything here is structural, so the kernel can evaluate an enclosure (`decide +kernel` on
`valData`, the sign, numerator and denominator of an endpoint), and the soundness lemmas turn
the computed endpoints into real bounds: this is how numerical claims (e.g. DLMF §2.11(i)) are
checked by Azurite's own arithmetic, without `native_decide`.
-/

namespace Azurite.AzFloat

/-- An enclosure `[lo, hi]` of a real number by two floats. -/
abbrev Encl := AzFloat × AzFloat

namespace Encl

/-- The point enclosure of an exact float. -/
def exact (x : AzFloat) : Encl := (x, x)

/-- The point enclosure of a natural number. -/
def nat (n : Nat) : Encl := exact (ofAzNat (AzNat.ofNat n))

/-- `[a] + [b]`. -/
def add (w : Nat) (a b : Encl) : Encl :=
  ((addPrecRound a.1 b.1 w .Floor).1, (addPrecRound a.2 b.2 w .Ceiling).1)

/-- `[a] − [b]`. -/
def sub (w : Nat) (a b : Encl) : Encl :=
  ((subPrecRound a.1 b.2 w .Floor).1, (subPrecRound a.2 b.1 w .Ceiling).1)

/-- `[a] − [b]` for a difference known to be nonnegative: the lower end is clamped at `0`. -/
def subNonneg (w : Nat) (a b : Encl) : Encl :=
  (clampNonneg (subPrecRound a.1 b.2 w .Floor).1, (subPrecRound a.2 b.1 w .Ceiling).1)

/-- `[a] · [b]` for nonnegative enclosures. -/
def mul (w : Nat) (a b : Encl) : Encl :=
  ((mulPrecRound a.1 b.1 w .Floor).1, (mulPrecRound a.2 b.2 w .Ceiling).1)

/-- `[a] / [b]` for a nonnegative `[a]` and a positive `[b]`. -/
def div (w : Nat) (a b : Encl) : Encl :=
  ((divPrecRound a.1 b.2 w .Floor).1, (divPrecRound a.2 b.1 w .Ceiling).1)

/-- `[a]ⁿ` for a nonnegative enclosure. -/
def pow (w : Nat) (a : Encl) : Nat → Encl
  | 0 => exact one
  | n + 1 => mul w (pow w a n) a

/-- `[a] ± [e]`: widen by a nonnegative error enclosure. -/
def widen (w : Nat) (a e : Encl) : Encl :=
  ((subPrecRound a.1 e.2 w .Floor).1, (addPrecRound a.2 e.2 w .Ceiling).1)

/-- `−[a]`. -/
def neg (a : Encl) : Encl := (-a.2, -a.1)

/-- `π`, by the Brent–Salamin bracket at working precision `w ≥ 64`. -/
def pi (w : Nat) : Encl := piBracket w

/-- `exp x` for a finite float `x`, with the lower end clamped at `0`. -/
def exp (w : Nat) (x : AzFloat) : Encl :=
  (clampNonneg (expBracketAt x w).1, (expBracketAt x w).2)

end Encl

/-- The sign (`true` = nonnegative), numerator and denominator of the value of a finite float. -/
def valData (x : AzFloat) : Option (Bool × Nat × Nat) :=
  x.toAzRat?.map fun q => (q.sign, q.num.toNat, q.den.toNat)

/-- The fixed-point decimal rendering of `x` rounded to nearest at `k` digits after the point,
trailing zeros kept and no exponent notation (`none` for `NaN` and `±∞`). -/
def toDecimalPlaces (x : AzFloat) (k : Nat) : Option String :=
  let o : SciOptions :=
    SciOptions.mk 10 .Nearest (.scale k) (SciFormat.mk (-64) true true false true)
  x.toAzRat?.bind fun q => q.toSci o

end Azurite.AzFloat
