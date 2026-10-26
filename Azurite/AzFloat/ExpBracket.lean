/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2Bracket
import Azurite.AzFloat.Shift
import Azurite.AzNat.ExpSplit

/-!
## Brackets of `exp` at dyadic rationals by binary splitting

`expChunkBracket p s e w` encloses `exp (p / 2^s)` for `p / 2^s ≤ 2^(−e)` (`e ≥ 1`): the Taylor
series is summed exactly by `AzNat.expNumDen` with `expTermCount e w` terms (enough for a tail
below `2^(−w−1)`, using `n! ≥ (n/2)^(n/2)`), the fraction is bracketed at precision `w + 8`
(`natQuotBracket`), shifted exactly, and widened by the tail.  `expChunks M K` is the bit-burst
decomposition (MCA §4.9) of `M / 2^(2^K)` into chunks `p / 2^s` of `2^i` bits at scale
`2^(−2^(i+1))`, each below `2^(−2^i)`, and `expDyadicBracket M K w` multiplies the chunk brackets
with directed rounding: `exp (M / 2^(2^K)) = ∏ exp (p_i / 2^(s_i))`.
-/

namespace Azurite.AzFloat

/-- The search for the number of terms. -/
def expTermCount.go (e w : Nat) : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n =>
    if w + 2 ≤ n * e + (n / 2) * Nat.log 2 (n / 2) then n else expTermCount.go e w fuel (n + 1)

/-- The number of series terms `n ≥ 2` with `n e + (n/2) ⌊log₂ (n/2)⌋ ≥ w + 2`, so that the tail
of `exp x` for `|x| ≤ 2^(−e)` is at most `2^(−w−1)`. -/
def expTermCount (e w : Nat) : Nat := expTermCount.go e w (w + 3) 2

/-- A float bracket of the quotient `n / d` of two naturals at precision `k`. -/
def natQuotBracket (n d : AzNat) (k : Nat) : AzFloat × AzFloat := seriesBracket (n, d) k

/-- The bracket of `exp (p / 2^s)` for `p / 2^s ≤ 2^(−e)`, `e ≥ 1`, at working precision `w`. -/
def expChunkBracket (p : AzNat) (s e w : Nat) : AzFloat × AzFloat :=
  let n := expTermCount e w
  let nd := AzNat.expNumDen p s (n - 1)
  let q := natQuotBracket nd.1 nd.2 (w + 8)
  let sh : AzInt := -(AzNat.ofNat (s * (n - 1))).toAzInt
  let tail := powerOf2 (-(AzNat.ofNat (w + 1)).toAzInt)
  ((subPrecRound (q.1 <<< sh) tail (w + 8) .Floor).1,
    (addPrecRound (q.2 <<< sh) tail (w + 8) .Ceiling).1)

/-- The chunks `(p, s, e)` of `M / 2^(2^K)` for `M < 2^(2^K)`, coarse to fine: the value of a
chunk is `p / 2^s ≤ 2^(−e)`. -/
def expChunks (M : AzNat) : Nat → List (AzNat × Nat × Nat)
  | 0 => [(M, 1, 1)]
  | K + 1 =>
    let h := 2 ^ K
    let hi := M >>> h
    let lo := M - (hi <<< h)
    expChunks hi K ++ [(lo, 2 ^ (K + 1), 2 ^ K)]

/-- The product of the chunk brackets, rounded at precision `w + 8`. -/
def expChunksBracket (w : Nat) : List (AzNat × Nat × Nat) → AzFloat × AzFloat
  | [] => (one, one)
  | (p, s, e) :: rest =>
    let b := expChunkBracket p s e w
    let r := expChunksBracket w rest
    ((mulPrecRound b.1 r.1 (w + 8) .Floor).1, (mulPrecRound b.2 r.2 (w + 8) .Ceiling).1)

/-- The bracket of `exp (M / 2^(2^K))` for `M < 2^(2^K)`. -/
def expDyadicBracket (M : AzNat) (K w : Nat) : AzFloat × AzFloat :=
  expChunksBracket w (expChunks M K)

end Azurite.AzFloat
