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
## Binary splitting for `atanh(1/q) = ∑_k 1/((2k+1) q^(2k+1))` and `arctan(1/q)`

The partial sum `∑_{k<N} 1/((2k+1) q^(2k+1))` is computed **exactly** as a fraction of big
integers by binary splitting (MCA §4.9.1).  Over an index range `[l, l+n)` the state
`(T, B, Q)` represents

  `∑_{k<n} 1/((2(l+k)+1) q^(2(k+1))) = T / (B · Q)`,  `B = ∏_{k<n} (2(l+k)+1)`, `Q = (q²)^n`:

a single term is `(1, 2l+1, q²)` (`atanhLeaf`), and two adjacent ranges merge by
`(T₁ B₂ Q₂ + B₁ T₂, B₁ B₂, Q₁ Q₂)` (`splitMerge`), because the second range's terms carry the
extra factor `1/Q₁`.  The engine is generic in the leaf (`seqOf`, `splitFuelOf`, `splitOf`):
`splitFuelOf leaf` halves the range `fuel` times (`splitOf` uses `fuel = n`, far more than the
`⌈log₂ n⌉` levels needed) and finishes sequentially (`seqOf`) if the fuel runs out, so the result
is the same fraction for every fuel.  Finally
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

/-- The sequential evaluation of the range `[l, l+n)` for the series with the given `leaf`
(the term of index `l` as a state), the fallback when the fuel runs out. -/
def seqOf (leaf : Nat → SplitState) : Nat → Nat → SplitState
  | _, 0 => splitEmpty
  | l, n + 1 => splitMerge (leaf l) (seqOf leaf (l + 1) n)

/-- Binary splitting of the range `[l, l+n)` with `fuel` halvings, for the series with the given
`leaf`. -/
def splitFuelOf (leaf : Nat → SplitState) : Nat → Nat → Nat → SplitState
  | 0, l, n => seqOf leaf l n
  | _ + 1, _, 0 => splitEmpty
  | _ + 1, l, 1 => leaf l
  | fuel + 1, l, n + 2 =>
    let m := (n + 2) / 2
    splitMerge (splitFuelOf leaf fuel l m) (splitFuelOf leaf fuel (l + m) (n + 2 - m))

/-- Binary splitting of the range `[l, l+n)` (fuel `n`, enough for every depth). -/
def splitOf (leaf : Nat → SplitState) (l n : Nat) : SplitState := splitFuelOf leaf n l n

/-- The sequential evaluation for `atanh(1/q)`. -/
def atanhSeq (q2 : AzNat) : Nat → Nat → SplitState := seqOf (atanhLeaf q2)

/-- Binary splitting with `fuel` halvings for `atanh(1/q)`. -/
def atanhSplitFuel (q2 : AzNat) : Nat → Nat → Nat → SplitState := splitFuelOf (atanhLeaf q2)

/-- Binary splitting of the range `[l, l+n)` for `atanh(1/q)`. -/
def atanhSplit (q2 : AzNat) (l n : Nat) : SplitState := splitOf (atanhLeaf q2) l n

/-- The exact fraction `∑_{k<N} 1/((2k+1) q^(2k+1)) = num/den` with
`num = q · T(0, N)`, `den = B(0, N) · Q(0, N)`. -/
def atanhNumDen (q N : Nat) : AzNat × AzNat :=
  let s := atanhSplit (ofNat (q * q)) 0 N
  (ofNat q * s.1, s.2.1 * s.2.2)

/-! ### `arctan(1/q)` by pairs of terms

`arctan(1/q) = ∑_k (−1)^k/((2k+1) q^(2k+1))` alternates; two consecutive terms make the
**positive** term `((4j+3) q² − (4j+1)) / ((4j+1)(4j+3) q^(4j+3))`, so the same engine applies
with the leaf `((4j+3) q² − (4j+1), (4j+1)(4j+3), q⁴)` representing
`((4j+3) q² − (4j+1)) / ((4j+1)(4j+3) q⁴)`, and
`∑_{j<N} [1/((4j+1) q^(4j+1)) − 1/((4j+3) q^(4j+3))] = q · T(0, N) / (B(0, N) · Q(0, N))`
(`atanNumDen`; the theory is in `Azurite/BrentZimmermann/Chapter4/PiBinarySplitting.lean`). -/

/-- The pair of terms of index `l` of `arctan(1/q)`:
`((4l+3) q² − (4l+1), (4l+1)(4l+3), q⁴)` (the small factors as `Nat`, `q4 = q⁴`). -/
def atanLeaf (q : Nat) (q4 : AzNat) (l : Nat) : SplitState :=
  (ofNat ((4 * l + 3) * (q * q) - (4 * l + 1)), ofNat ((4 * l + 1) * (4 * l + 3)), q4)

/-- The exact fraction `∑_{j<N} [1/((4j+1) q^(4j+1)) − 1/((4j+3) q^(4j+3))] = num/den`, the first
`2N` terms of the series of `arctan(1/q)`. -/
def atanNumDen (q N : Nat) : AzNat × AzNat :=
  let s := splitOf (atanLeaf q (ofNat (q * q * (q * q)))) 0 N
  (ofNat q * s.1, s.2.1 * s.2.2)

end Azurite.AzNat
