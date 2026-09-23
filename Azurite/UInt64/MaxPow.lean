/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace UInt64

/-- Tail-recursive helper for `maxPow`. `cap = (2^64 - 1) / b` is the
    largest accumulator value for which `acc * b` still fits in a
    `UInt64`. Fuel of `64` is sufficient: in the worst case `b = 2`,
    the loop emits `e = 63` digits before saturating. -/
def maxPow.go (b cap : UInt64) : Nat → UInt64 → Nat → UInt64 × Nat
  | 0, acc, e => (acc, e)
  | f + 1, acc, e =>
      if acc ≤ cap then maxPow.go b cap f (acc * b) (e + 1)
      else (acc, e)

/-- `maxPow b` returns `(b^e, e)` where `e` is the largest natural
    number such that `b^e` still fits in a `UInt64`. For degenerate
    bases `b ∈ {0, 1}` (which have no meaningful largest power), returns
    `(1, 0)`.

    Used to plan base-`b` digit batching for `AzNat` pretty-printing:
    e.g.\ `maxPow 10 = (10^19, 19)` says we can pack `19` decimal
    digits into one limb without overflow. -/
def maxPow (b : UInt64) : UInt64 × Nat :=
  if b < 2 then (1, 0)
  else maxPow.go b ((0 - 1 : UInt64) / b) 64 1 0

-- Sanity checks.
-- 10^19 = 10_000_000_000_000_000_000 fits in UInt64 (MAX = 2^64 - 1 ≈ 1.84e19).
#guard maxPow 10 == (10000000000000000000, 19)
-- 2^63 is the largest 2-power below 2^64.
#guard maxPow 2 == (9223372036854775808, 63)
-- 16^15 = 2^60.
#guard maxPow 16 == (1152921504606846976, 15)
-- 3^40 ≈ 1.22e19 fits; 3^41 doesn't.
#guard maxPow 3 == (12157665459056928801, 40)
-- Degenerate bases.
#guard maxPow 0 == (1, 0)
#guard maxPow 1 == (1, 0)
-- Single-power bases: base itself already saturates one digit.
#guard maxPow 0xFFFF_FFFF_FFFF_FFFF == (0xFFFF_FFFF_FFFF_FFFF, 1)
#guard maxPow 0x8000_0000_0000_0000 == (0x8000_0000_0000_0000, 1)

/-! ### Precomputed base-10 batching constants

Base-10 string conversion of an `AzNat` packs the largest possible
number of decimal digits into each limb. These constants are the
`maxPow 10` output, named for convenient use without re-running the
loop on every conversion. -/

/-- `10^19 = 10_000_000_000_000_000_000`, the largest power of `10` that
    fits in a `UInt64` (the next power, `10^20`, exceeds `2^64`). -/
def maxPow10 : UInt64 := 10000000000000000000

/-- The exponent in `maxPow10`: `19`. Equivalently, the number of base-`10`
    digits packed into one limb during `AzNat` string conversion. -/
def maxPow10Exp : Nat := 19

/-- The constants `maxPow10` and `maxPow10Exp` match `maxPow 10`. -/
theorem maxPow_ten : maxPow 10 = (maxPow10, maxPow10Exp) := by decide

end UInt64
