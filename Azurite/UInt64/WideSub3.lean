/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.SubWithBorrow

namespace UInt64

/-- 192-bit subtraction of two triples `(hi, mid, lo)`, each interpreted as
`hi · 2^128 + mid · 2^64 + lo`. Returns the triple mod `2^192`; no borrow-out. -/
@[inline]
def wideSub3 (x y : UInt64 × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 :=
  let z0 := subWithBorrow x.2.2 y.2.2 false
  let z1 := subWithBorrow x.2.1 y.2.1 z0.2
  let z2 := subWithBorrow x.1 y.1 z1.2
  (z2.1, z1.1, z0.1)

end UInt64
