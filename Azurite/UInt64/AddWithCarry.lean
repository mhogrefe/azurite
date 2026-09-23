/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Adds two 64-bit unsigned integers along with a boolean carry, returning the sum and the new carry out. -/
@[inline]
def addWithCarry (a b : UInt64) (c : Bool) : UInt64 × Bool :=
  let sum1 := a + b
  let c1 := sum1 < a
  let c_val : UInt64 := if c then 1 else 0
  let sum2 := sum1 + c_val
  let c2 := sum2 < sum1
  (sum2, c1 || c2)

end UInt64
