/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.Digits

namespace UInt64

/-- Horner reconstruction over a digit array: fold right with
    `acc → acc * b + d`. All arithmetic wraps modulo `2^64`. -/
def ofDigitsGeneric (b : UInt64) (ds : Array UInt64) : UInt64 :=
  ds.foldr (fun d acc => acc * b + d) 0

/-- Power-of-2 specialization of `ofDigitsGeneric`: replaces multiplication
    by `b = 2^k` with a left shift by `k`. Intended for `k ∈ [0, 63]`;
    outside that range the shift wraps modulo `64` and the function
    diverges from base-`2^k` decoding. -/
def ofDigitsPow2 (k : Nat) (ds : Array UInt64) : UInt64 :=
  ds.foldr (fun d acc => (acc <<< UInt64.ofNat k) + d) 0

/-- `ofDigits b ds` reconstructs a `UInt64` from its base-`b` digit array
    (LSB-first), the left inverse of `digits b` modulo wraparound.
    Dispatches to `ofDigitsPow2` (shift+add) when `b` is a power of two,
    otherwise uses generic Horner.

    All arithmetic wraps modulo `2^64`. The round-trip
    `ofDigits b (digits b u) = u` holds unconditionally for `b ≥ 2`
    because `Nat.ofDigits b.toNat (Nat.digits b.toNat u.toNat) = u.toNat`
    and `u.toNat < 2^64`. -/
def ofDigits (b : UInt64) (ds : Array UInt64) : UInt64 :=
  if b.isPowerOfTwo then
    ofDigitsPow2 b.toBitVec.ctz.toNat ds
  else
    ofDigitsGeneric b ds

-- Sanity checks.
-- Direct construction in various bases.
#guard ofDigits 10 #[5, 4, 3, 2, 1] = 12345
#guard ofDigits 10 #[] = 0
#guard ofDigits 16 #[0xF, 0xE, 0xE, 0xB, 0xD, 0xA, 0xE, 0xD] = 0xDEADBEEF
#guard ofDigits 2 #[0, 1, 1, 0, 1] = 0b10110
#guard ofDigits 8 #[5, 5, 7] = 0o755

-- Round-trip with `digits`.
#guard ofDigits 10 (digits 10 12345) = 12345
#guard ofDigits 16 (digits 16 0xDEADBEEF) = 0xDEADBEEF
#guard ofDigits 2 (digits 2 1234567890) = 1234567890
#guard ofDigits 10 (digits 10 0xFFFF_FFFF_FFFF_FFFF) = 0xFFFF_FFFF_FFFF_FFFF

-- Top-bit-set values still round-trip.
#guard ofDigits 16 (digits 16 0x8000_0000_0000_0000) = 0x8000_0000_0000_0000

end UInt64
