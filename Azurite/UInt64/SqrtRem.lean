/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

namespace Azurite.UInt64

/-!
Integer square root with remainder for `UInt64`.  Uses a hardware
`Float.sqrt` as an initial guess, then deterministically corrects with
integer increments/decrements until the result satisfies
`s * s ≤ n < (s + 1) * (s + 1)`.

The correction step is sound for any starting `s ∈ [0, 2^32 − 1]`, so
the proof of correctness does not touch `Float` semantics — the
hardware sqrt is treated as an untrusted hint.

Overflow notes:
  - For `n : UInt64`, the true `⌊√n⌋` is at most `2^32 − 1` (since
    `(2^32)^2 = 2^64` overflows).  We clamp the float guess to that
    range so `s * s` always fits in `UInt64`.
  - For the up-correction we want `(s + 1)^2 ≤ n`.  Naively
    `(s + 1) * (s + 1)` overflows when `s = 2^32 − 1`.  We rewrite as
    `2 * s + 1 ≤ n − s * s`; the right side is well-defined because
    the loop preserves `s * s ≤ n` after down-correction, and the
    left side fits since `2 * (2^32 − 1) + 1 < 2^33`.
-/

/-- The maximum possible value of `⌊√n⌋` for `n : UInt64`, namely
    `2^32 − 1 = 0xFFFFFFFF`. -/
def sqrtRem.cap : UInt64 := 0xFFFFFFFF

/-- Float-based initial guess for `⌊√n⌋`, clamped to
    `[0, sqrtRem.cap]` so squaring never overflows.  The result is
    only used as a hint; the correction loops below produce the
    correct answer regardless of where the guess lands. -/
def sqrtRem.floatGuess (n : UInt64) : UInt64 :=
  let s := n.toFloat.sqrt.toUInt64
  if s > sqrtRem.cap then sqrtRem.cap else s

/-- Down-correction loop.  Decrement `s` until `s * s ≤ n`.  `fuel`
    bounds the worst-case iteration count; `s.toNat + 1` is always
    sufficient (worst case is `s` down to `0`). -/
def sqrtRem.correctDown (s n : UInt64) (fuel : Nat) : UInt64 :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s = 0 then s
    else if s * s > n then sqrtRem.correctDown (s - 1) n fuel'
    else s

/-- Up-correction loop.  Increment `s` until `(s + 1) * (s + 1) > n`.
    Precondition: `s * s ≤ n` (established by `correctDown`).  The
    overflow-safe condition `2 * s + 1 ≤ n − s * s` is equivalent to
    `(s + 1) * (s + 1) ≤ n` whenever `s * s ≤ n`.  `fuel` bounds the
    iteration count; `(cap − s).toNat + 1` is always sufficient. -/
def sqrtRem.correctUp (s n : UInt64) (fuel : Nat) : UInt64 :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    if s ≥ sqrtRem.cap then s
    else if 2 * s + 1 ≤ n - s * s then sqrtRem.correctUp (s + 1) n fuel'
    else s

/-- Integer square root for `UInt64`: the unique `s` with
    `s * s ≤ n < (s + 1) * (s + 1)`.  The Float-based initial guess
    is refined by the correction loops; the proof of correctness
    lives entirely on the integer side and does not reason about
    Float. -/
def sqrt (n : UInt64) : UInt64 :=
  let s0 := sqrtRem.floatGuess n
  let s1 := sqrtRem.correctDown s0 n (s0.toNat + 1)
  sqrtRem.correctUp s1 n (sqrtRem.cap.toNat - s1.toNat + 1)

/-- Integer square root with remainder.  Returns `(s, r)` with
    `s * s + r = n` and `r ≤ 2 * s`, i.e. `s := sqrt n` and
    `r := n - s * s`. -/
def sqrtRem (n : UInt64) : UInt64 × UInt64 :=
  let s := sqrt n
  (s, n - s * s)

end Azurite.UInt64

section Examples

open Azurite.UInt64

-- Perfect squares and basic values.
#guard sqrtRem 0 = (0, 0)
#guard sqrtRem 1 = (1, 0)
#guard sqrtRem 2 = (1, 1)
#guard sqrtRem 3 = (1, 2)
#guard sqrtRem 4 = (2, 0)
#guard sqrtRem 100 = (10, 0)
#guard sqrtRem 101 = (10, 1)
#guard sqrtRem 9999 = (99, 198)
#guard sqrtRem 10000 = (100, 0)

-- Just below and above 2^53 (Float precision boundary).
#guard sqrtRem (((1 : UInt64) <<< 53) - 1) = (94906265, 118490766)
#guard sqrtRem ((1 : UInt64) <<< 53) = (94906265, 118490767)

-- Powers of two above the Float-exact range.
#guard sqrtRem ((1 : UInt64) <<< 60) = ((1 : UInt64) <<< 30, 0)
#guard sqrtRem (((1 : UInt64) <<< 60) + 1) = ((1 : UInt64) <<< 30, 1)
#guard sqrtRem ((1 : UInt64) <<< 62) = ((1 : UInt64) <<< 31, 0)

-- Near UInt64.maxValue (the Float guess overflows to 2^32 here; the
-- clamp + down-correction must recover).
#guard sqrtRem ((0 : UInt64) - 1) = (4294967295, 8589934590)
#guard sqrtRem ((4294967295 : UInt64) * 4294967295) = (4294967295, 0)

end Examples
