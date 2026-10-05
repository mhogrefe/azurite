/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Number of trailing zero bits of a nonzero `UInt64` (returns `0` for `0`).

`d &&& -d` isolates the lowest set bit of `d`, and `UInt64.log2` has a hardware implementation,
so this takes a few machine instructions.  `BitVec.ctz`, by contrast, is defined by a 64-step
bit reversal followed by a 64-step leading-zero scan on `Nat`-backed bit vectors. -/
@[inline]
def trailingZeros (d : UInt64) : Nat := (d &&& -d).log2.toNat

#guard trailingZeros 1 = 0
#guard trailingZeros 2 = 1
#guard trailingZeros 96 = 5
#guard trailingZeros 0xFFFFFFFFFFFFFFFF = 0
#guard trailingZeros 0xFFFFFFFFFFFFFFFE = 1
#guard trailingZeros 0x8000000000000000 = 63
#guard trailingZeros 0x0123456780000000 = 31

end UInt64
