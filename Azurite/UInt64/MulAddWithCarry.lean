/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.MulWithCarry

namespace UInt64

/-- Computes `a * b + acc + c` as a 128-bit result, returned as `(hi, lo)`.
    Fits without overflow since `(2^64-1)^2 + 2 * (2^64-1) = 2^128 - 1`.

The carry is added as a conditional *scalar* (`if _ then 1 else 0`) rather
than by branching on the result pair, so codegen keeps `(hi', lo')` in
registers instead of boxing it at a control-flow join point. -/
@[inline]
def mulAddWithCarry (a b acc c : UInt64) : UInt64 × UInt64 :=
  let (hi, lo) := mulWithCarry a b c
  let lo' := lo + acc
  (hi + (if lo' < lo then 1 else 0), lo')

end UInt64
