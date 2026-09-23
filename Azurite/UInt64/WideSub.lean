/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- 128-bit subtraction of two pairs `(hi₁, lo₁)` and `(hi₂, lo₂)`, each interpreted
as `hi · 2^64 + lo`. Returns `(hi, lo)` mod `2^128`; no borrow-out. -/
@[inline]
def wideSub (x y : UInt64 × UInt64) : UInt64 × UInt64 :=
  let lo := x.2 - y.2
  let borrow : UInt64 := if x.2 < y.2 then 1 else 0
  let hi := x.1 - y.1 - borrow
  (hi, lo)

end UInt64
