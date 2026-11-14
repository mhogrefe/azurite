/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzInt.Sub
import Azurite.AzInt.Mul
import Azurite.AzInt.ShiftLeft
import Azurite.AzNat.Mul

/-!
## Binary splitting for the sine and cosine series at a dyadic rational

For `y² = d₂ / 2^s` (`d₂ : AzNat`, `s : ℕ`) the partial sums of

  `cos y = ∑_k (−1)^k y^(2k)/(2k)!`  and  `sin y / y = ∑_k (−1)^k y^(2k)/(2k+1)!`

are computed **exactly** as fractions of big integers by binary splitting (MCA §4.9.1, step 5 of
Algorithm 4.4 SinCos).  Both series have the term ratio `−y²/((2k+1+o)(2k+2+o))` from index `k`
to `k + 1`, with the offset `o = 0` for the cosine and `o = 1` for the sine.  Over an index
range `[l, l+n)` the state `(P, B, T)` represents

  `∑_{k<n} ∏_{i≤k} (−y²)/((2(l+i)+1+o)(2(l+i)+2+o)) = T / (B · 2^(s n))`,
  `P = (−d₂)^n`,  `B = ∏_{i<n} (2(l+i)+1+o)(2(l+i)+2+o)`:

a single term is `(−d₂, q, −d₂)` (`altLeaf`), and two adjacent ranges merge by
`(P₁ P₂, B₁ B₂, (T₁ B₂) · 2^(s n₂) + P₁ T₂)` (`altMerge`).  As in `AzNat/ExpSplit.lean` the
power-of-two part of the denominator is the shift `s · n`, never materialized; the sign of the
alternating series is carried by `P` and `T` (`AzInt`s).  With `st = altSplit d₂ s o 0 N`:

  `∑_{k≤N} (−1)^k y^(2k)/(2k+o)! = 1 + T / (B · 2^(sN))`,  and the last term is `P / (B · 2^(sN))`.

The proofs are in `Azurite/AzInt/Equiv/SinCosSplit.lean`.
-/

namespace Azurite.AzInt

/-- An alternating binary-splitting state `(P, B, T)`. -/
abbrev AltSplitState := AzInt × AzNat × AzInt

/-- Merge the states of two adjacent ranges, the second of length `n₂`:
`(P₁ P₂, B₁ B₂, (T₁ B₂) · 2^(s n₂) + P₁ T₂)`. -/
def altMerge (s n₂ : Nat) (x y : AltSplitState) : AltSplitState :=
  (x.1 * y.1, x.2.1 * y.2.1, ((x.2.2 * y.2.1.toAzInt) <<< (s * n₂)) + x.1 * y.2.2)

/-- The ratio denominator `(2l+1+o)(2l+2+o)` from the term of index `l` to the next. -/
def altDen (o l : Nat) : Nat := (2 * l + 1 + o) * (2 * l + 2 + o)

/-- The single ratio of index `l`: `−d₂/(2^s q)`, as `(−d₂, q, −d₂)`. -/
def altLeaf (d2 : AzNat) (o l : Nat) : AltSplitState :=
  (-d2.toAzInt, AzNat.ofNat (altDen o l), -d2.toAzInt)

/-- The empty range: `(1, 1, 0)`. -/
def altEmpty : AltSplitState := (1, AzNat.ofNat 1, 0)

/-- The sequential evaluation of the range `[l, l+n)`, the fallback when the fuel runs out. -/
def altSeq (d2 : AzNat) (s o : Nat) : Nat → Nat → AltSplitState
  | _, 0 => altEmpty
  | l, n + 1 => altMerge s n (altLeaf d2 o l) (altSeq d2 s o (l + 1) n)

/-- Binary splitting of the range `[l, l+n)` with `fuel` halvings. -/
def altSplitFuel (d2 : AzNat) (s o : Nat) : Nat → Nat → Nat → AltSplitState
  | 0, l, n => altSeq d2 s o l n
  | _ + 1, _, 0 => altEmpty
  | _ + 1, l, 1 => altLeaf d2 o l
  | fuel + 1, l, n + 2 =>
    let m := (n + 2) / 2
    altMerge s (n + 2 - m) (altSplitFuel d2 s o fuel l m)
      (altSplitFuel d2 s o fuel (l + m) (n + 2 - m))

/-- Binary splitting of the range `[l, l+n)` (fuel `n`, enough for every depth). -/
def altSplit (d2 : AzNat) (s o l n : Nat) : AltSplitState := altSplitFuel d2 s o n l n

end Azurite.AzInt
