/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Combined quotient/remainder of `x / y` and `x % y`, returned as `(q, r)`.
Compilers (GCC/Clang/MSVC) recognize this idiom and emit a single hardware
`DIV` instruction, which produces both quotient and remainder simultaneously. -/
@[inline]
def divMod (x y : UInt64) : UInt64 × UInt64 :=
  (x / y, x % y)

end UInt64
