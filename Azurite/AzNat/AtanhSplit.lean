/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Conversion
import Azurite.AzNat.Instances
import Azurite.AzNat.Mul

/-!
## Binary splitting for `atanh(1/q) = ∑_k 1/((2k+1) q^(2k+1))`

The partial sum `∑_{k<N} 1/((2k+1) q^(2k+1))` is computed **exactly** as a fraction of big
integers by binary splitting (MCA §4.9.1).  Over an index range `[l, l+n)` the state
`(T, B, Q)` represents

  `∑_{k<n} 1/((2(l+k)+1) q^(2(k+1))) = T / (B · Q)`,  `B = ∏_{k<n} (2(l+k)+1)`, `Q = (q²)^n`:

a single term is `(1, 2l+1, q²)` (`atanhLeaf`), and two adjacent ranges merge by
`(T₁ B₂ Q₂ + B₁ T₂, B₁ B₂, Q₁ Q₂)` (`splitMerge`), because the second range's terms carry the
extra factor `1/Q₁`.  `atanhSplitFuel` halves the range `fuel` times (`atanhSplit` uses
`fuel = n`, far more than the `⌈log₂ n⌉` levels needed) and finishes sequentially (`atanhSeq`)
if the fuel runs out, so the result is the same fraction for every fuel.  Finally
`∑_{k<N} 1/((2k+1) q^(2k+1)) = q · T(0, N) / (B(0, N) · Q(0, N))` (`atanhNumDen`).

The proofs are in `Azurite/AzNat/Equiv/AtanhSplit.lean`; the theory (tail bounds, the Machin-like
formula for `ln 2`) in `Azurite/BrentZimmermann/Chapter4/Ln2BinarySplitting.lean`.
-/

namespace Azurite.AzNat

/-- A binary-splitting state `(T, B, Q)` representing the fraction `T/(B·Q)`. -/
abbrev SplitState := AzNat × AzNat × AzNat

/-- Merge the states of two adjacent ranges: `(T₁ B₂ Q₂ + B₁ T₂, B₁ B₂, Q₁ Q₂)`. -/
def splitMerge (x y : SplitState) : SplitState :=
  (x.1 * y.2.1 * y.2.2 + x.2.1 * y.1, x.2.1 * y.2.1, x.2.2 * y.2.2)

/-- The single term of index `l`: `1/((2l+1) q²)`, as `(1, 2l+1, q²)`. -/
def atanhLeaf (q2 : AzNat) (l : Nat) : SplitState := (ofNat 1, ofNat (2 * l + 1), q2)

/-- The empty range. -/
def splitEmpty : SplitState := (ofNat 0, ofNat 1, ofNat 1)

/-- The sequential evaluation of the range `[l, l+n)`, the fallback when the fuel runs out. -/
def atanhSeq (q2 : AzNat) : Nat → Nat → SplitState
  | _, 0 => splitEmpty
  | l, n + 1 => splitMerge (atanhLeaf q2 l) (atanhSeq q2 (l + 1) n)

/-- Binary splitting of the range `[l, l+n)` with `fuel` halvings. -/
def atanhSplitFuel (q2 : AzNat) : Nat → Nat → Nat → SplitState
  | 0, l, n => atanhSeq q2 l n
  | _ + 1, _, 0 => splitEmpty
  | _ + 1, l, 1 => atanhLeaf q2 l
  | fuel + 1, l, n + 2 =>
    let m := (n + 2) / 2
    splitMerge (atanhSplitFuel q2 fuel l m) (atanhSplitFuel q2 fuel (l + m) (n + 2 - m))

/-- Binary splitting of the range `[l, l+n)` (fuel `n`, enough for every depth). -/
def atanhSplit (q2 : AzNat) (l n : Nat) : SplitState := atanhSplitFuel q2 n l n

/-- The exact fraction `∑_{k<N} 1/((2k+1) q^(2k+1)) = num/den` with
`num = q · T(0, N)`, `den = B(0, N) · Q(0, N)`. -/
def atanhNumDen (q N : Nat) : AzNat × AzNat :=
  let s := atanhSplit (ofNat (q * q)) 0 N
  (ofNat q * s.1, s.2.1 * s.2.2)

end Azurite.AzNat
