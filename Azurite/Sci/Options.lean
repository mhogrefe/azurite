/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Mode

/-!
# Options for scientific-notation output

The configuration of `toSci` (`docs/to_sci_plan.md`), ported from the author's own
`ToSciOptions` / `SciSizeOptions` in Malachite.  The numeric part (`base`, `mode`, `size`)
drives the first stage, `AzRat.toSciNumber`, and defines the rounding target the correctness
proofs refer to; the textual part (`SciFormat`) drives only the rendering of a `SciNumber`.

Malachite's `RoundingMode::Exact` has no counterpart in `Azurite.RoundingMode`: exactness is a
validity predicate (`toSciValid`) instead of a mode.
-/

namespace Azurite

/-- How many digits to produce.
* `complete`: every digit (only for values whose base-`b` expansion terminates).
* `precision p`: `p ≥ 1` significant digits.
* `scale s`: `s` digits after the point. -/
inductive SciSizeOptions where
  | complete
  | precision (p : Nat)
  | scale (s : Nat)
  deriving DecidableEq, Repr

instance : Inhabited SciSizeOptions := ⟨.precision 16⟩

/-- `precision 0` is meaningless; everything else is valid. -/
def SciSizeOptions.valid : SciSizeOptions → Bool
  | .precision p => p != 0
  | _ => true

/-- The purely textual options: how a `SciNumber` is rendered. -/
structure SciFormat where
  /-- Exponent notation is used when the base-`b` exponent is `≤` this (must be negative). -/
  negExpThreshold : Int := -6
  /-- Digit letters `a`–`z` (`true`) or `A`–`Z`. -/
  lowercase : Bool := true
  /-- Exponent marker `e` (`true`) or `E`. -/
  eLowercase : Bool := true
  /-- Write `e+8` rather than `e8` (always done for bases `≥ 15`, where `e` is a digit). -/
  forceExponentPlusSign : Bool := false
  /-- Keep zeros after the point. -/
  includeTrailingZeros : Bool := false
  deriving DecidableEq, Repr

instance : Inhabited SciFormat := ⟨{}⟩

/-- All `toSci` options.  Defaults: base 10, round to nearest, 16 significant digits,
exponent notation below `10^-6`, lowercase, no forced `+`, trailing zeros trimmed. -/
structure SciOptions where
  /-- The digit base, `2 ≤ base ≤ 36`. -/
  base : UInt64 := 10
  /-- How the value is rounded to the requested size. -/
  mode : RoundingMode := .Nearest
  /-- How many digits. -/
  size : SciSizeOptions := .precision 16
  /-- The rendering options. -/
  format : SciFormat := {}
  deriving DecidableEq, Repr

instance : Inhabited SciOptions := ⟨{}⟩

/-- Malachite's setter preconditions: base in `[2, 36]`, a negative exponent threshold, and a
positive precision. -/
def SciOptions.valid (o : SciOptions) : Bool :=
  2 ≤ o.base && o.base ≤ 36 && o.format.negExpThreshold < 0 && o.size.valid

end Azurite
