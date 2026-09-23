/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Test whether `u` is a multiple of `2 ^ k`, i.e. whether its `k` least-significant
bits are all zero. For `k ≥ 64`, only `0` qualifies. -/
@[inline]
def isMultipleOfPow2 (u : UInt64) (k : Nat) : Bool :=
  if k < 64 then u &&& ((1 <<< UInt64.ofNat k) - 1) == 0
  else u == 0

end UInt64
