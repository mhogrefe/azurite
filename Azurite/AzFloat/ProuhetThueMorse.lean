/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundScaled
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Parity
import Azurite.AzNat.ShiftRight

/-!
# The Prouhet–Thue–Morse constant

`τ = 0.0110100110010110… = Σ tₙ / 2^(n+1) ≈ 0.4124540336`, where `tₙ` is the Thue–Morse
sequence, the parity of the number of ones in the binary expansion of `n`
(`prouhetThueMorseSeq`).  Its binary expansion *is* the sequence, so the constant is produced
bit for bit with no arithmetic: since `t (64j + l) = t j xor t l` for `l < 64`, the `j`-th word
of 64 bits is either the Thue–Morse word `T₆ = 0x6996966996696996` or its complement, according
to `t j` (`prouhetThueMorseLimb`).  The first `64 N` bits are therefore an `AzNat` whose limbs
take only these two values (`prouhetThueMorseLimbs`).

Rounding to `p` bits needs the first `p` significant bits (the expansion starts `0.01`, so
these are bits `2` to `p + 1`), the next bit, and the knowledge that the tail is neither `0` nor
a half: the sequence is not eventually constant (`t (2^k) = 1`, `t (3 · 2^k) = 0`), so the
truncation is never exact and the value is never a midpoint.  `roundFromFloor` then rounds
with the floor and the next bit alone.  `Equiv/ProuhetThueMorse.lean` defines the real number
`prouhetThueMorseConstant` and proves
`prouhetThueMorsePrecRound p mode = liftVal₀ (some prouhetThueMorseConstant) p mode`.
-/

namespace Azurite.AzFloat

/-- The Thue–Morse sequence: `t 0 = 0`, `t (2n) = t n`, `t (2n + 1) = 1 − t n`; the parity of the
number of ones in the binary expansion. -/
def prouhetThueMorseSeq (n : ℕ) : Bool :=
  if h : n = 0 then false else xor (prouhetThueMorseSeq (n / 2)) (decide (n % 2 = 1))
decreasing_by omega

/-- The first 64 bits of the Thue–Morse sequence, most significant first. -/
def prouhetThueMorseWord : UInt64 := 0x6996966996696996

/-- The complement of `prouhetThueMorseWord`: bits `64j` to `64j + 63` of the sequence when
`t j = 1`. -/
def prouhetThueMorseWordNot : UInt64 := 0x9669699669969669

/-- Bits `64j` to `64j + 63` of the Thue–Morse sequence, most significant first. -/
def prouhetThueMorseLimb (j : ℕ) : UInt64 :=
  if prouhetThueMorseSeq j then prouhetThueMorseWordNot else prouhetThueMorseWord

/-- The first `64 N` bits of the constant as an integer: limb `i` (least significant first)
holds bits `64 (N − 1 − i)` to `64 (N − 1 − i) + 63`. -/
def prouhetThueMorseLimbs (N : ℕ) : AzNat :=
  AzNat.ofLimbs (Array.ofFn fun i : Fin N => prouhetThueMorseLimb (N - 1 - i))

/-- The Prouhet–Thue–Morse constant rounded to precision `p` with `mode`, and the comparison
with the exact value. -/
def prouhetThueMorsePrecRound (p : Nat) (mode : RoundingMode) : AzFloat × Ordering :=
  if p = 0 then (nan, .eq)
  else
    let N := (p + 2) / 64 + 1
    -- the first `p + 1` significant bits: the floor at `p` bits and the round bit
    let Y := (prouhetThueMorseLimbs N).shiftRight (64 * N - (p + 2))
    let r := roundFromFloor (Y.shiftRight 1) false (if Y.isOdd then .gt else .lt) mode
    (normalizeCarry (AzInt.mkNorm true r.1) (AzInt.ofInt (-1)) p, r.2)

/-- The Prouhet–Thue–Morse constant rounded to nearest at precision `p`. -/
def prouhetThueMorse (p : Nat) : AzFloat := (prouhetThueMorsePrecRound p .Nearest).1

end Azurite.AzFloat
