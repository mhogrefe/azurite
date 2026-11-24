/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzFloat.Constants

/-!
# `AzComplexFloat`: arbitrary-precision complex floating-point numbers

A complex number in rectangular form: a pair of `AzFloat`s.  The two components are
independent floats (each with its own precision, each possibly `NaN` or `±∞`); there is no
separate "complex infinity".

This file holds the type, the constants and the exact operations (negation, conjugation).
The rounded arithmetic is in `AzComplexFloat/Arith.lean`, with the convention of the real
floats: every function takes a pair of precisions and a pair of rounding modes (for the real and
the imaginary part, as in MPC and rug), and returns the result with two `Ordering`s comparing the real
and the imaginary part with the exact ones.  Each component is correctly rounded
(`AzComplexFloat/Equiv/Arith.lean`).
-/

namespace Azurite

/-- An arbitrary-precision complex floating-point number `re + im·i`. -/
structure AzComplexFloat where
  /-- The real part. -/
  re : AzFloat
  /-- The imaginary part. -/
  im : AzFloat
  deriving DecidableEq

namespace AzComplexFloat

/-- A real float as a complex one (imaginary part `0`). -/
def ofFloat (x : AzFloat) : AzComplexFloat := ⟨x, AzFloat.zero⟩

/-- `0`. -/
def zero : AzComplexFloat := ⟨AzFloat.zero, AzFloat.zero⟩

/-- `1`. -/
def one : AzComplexFloat := ⟨AzFloat.one, AzFloat.zero⟩

/-- The imaginary unit `i`. -/
def i : AzComplexFloat := ⟨AzFloat.zero, AzFloat.one⟩

/-- `NaN` in both components. -/
def nan : AzComplexFloat := ⟨AzFloat.nan, AzFloat.nan⟩

instance : Inhabited AzComplexFloat := ⟨zero⟩

/-- Are both components finite? -/
def isFinite (z : AzComplexFloat) : Bool := z.re.isFinite && z.im.isFinite

/-- Is a component `NaN`? -/
def isNaN (z : AzComplexFloat) : Bool := z.re.isNaN || z.im.isNaN

/-- Is the number `0`? -/
def isZero (z : AzComplexFloat) : Bool := decide (z.re = AzFloat.zero ∧ z.im = AzFloat.zero)

/-- Negation (exact). -/
def neg (z : AzComplexFloat) : AzComplexFloat := ⟨-z.re, -z.im⟩

instance : Neg AzComplexFloat := ⟨neg⟩

/-- Complex conjugation (exact). -/
def conj (z : AzComplexFloat) : AzComplexFloat := ⟨z.re, -z.im⟩

end AzComplexFloat

end Azurite
