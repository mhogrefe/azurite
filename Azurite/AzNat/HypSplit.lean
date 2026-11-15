/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.AtanhSplit

/-!
## Binary splitting for hypergeometric series `∑_k ∏_{j≤k} p(j)/q(j)`

The partial sum of a series whose term ratio is a rational function of the index,
`t_k = ∏_{j≤k} p(j)/q(j)`, is computed **exactly** as a fraction of big integers by binary
splitting (MCA §4.9.1).  Over an index range `[l, l+n)` the state `(P, Q, T)` represents

  `∑_{k<n} ∏_{j≤k} p(l+j)/q(l+j) = T / Q`,  `P = ∏_{k<n} p(l+k)`,  `Q = ∏_{k<n} q(l+k)`:

a single term is `(p(l), q(l), p(l))`, and two adjacent ranges merge by
`(P₁ P₂, Q₁ Q₂, T₁ Q₂ + P₁ T₂)` (`hypMerge`), because the second range's terms carry the extra
factor `P₁/Q₁`.  As in `AtanhSplit.lean` the engine is generic in the leaf and halves the range
`fuel` times before finishing sequentially, so the fraction is the same for every fuel.

Instances, for Catalan's constant `G = (√3 π/4) A + (3/8) S`
(`Azurite/Transcendental/Catalan.lean`):

* `S = ∑_{k≥0} 1/((2k+1)² C(2k,k))`: `p(0) = q(0) = 1`, `p(k) = k(2k−1)`, `q(k) = 2(2k+1)²`
  (`catalanLeaf`); `catalanNumDen N` is the fraction `3 T / (8 Q)` of `(3/8) ∑_{k<N}`.
* `A = ∑_{k≥0} 1/((2k+1) 3^{k+1})`, with the `(T, B, Q)` engine of `AtanhSplit.lean` and the leaf
  `(1, 2l+1, 3)`; `atanhSqrtThreeNumDen N` is the fraction `T / (4 B Q)` of `(1/4) ∑_{k<N}`.

The proofs are in `Azurite/AzNat/Equiv/HypSplit.lean`.
-/

namespace Azurite.AzNat

/-- A binary-splitting state `(P, Q, T)` representing the fraction `T/Q` (and the product
`P/Q` of the term ratios of its range). -/
abbrev HypState := AzNat × AzNat × AzNat

/-- Merge the states of two adjacent ranges: `(P₁ P₂, Q₁ Q₂, T₁ Q₂ + P₁ T₂)`. -/
def hypMerge (x y : HypState) : HypState :=
  (x.1 * y.1, x.2.1 * y.2.1, x.2.2 * y.2.1 + x.1 * y.2.2)

/-- The empty range. -/
def hypEmpty : HypState := (ofNat 1, ofNat 1, ofNat 0)

/-- The sequential evaluation of the range `[l, l+n)`, the fallback when the fuel runs out. -/
def hypSeq (leaf : Nat → HypState) : Nat → Nat → HypState
  | _, 0 => hypEmpty
  | l, n + 1 => hypMerge (leaf l) (hypSeq leaf (l + 1) n)

/-- Binary splitting of the range `[l, l+n)` with `fuel` halvings. -/
def hypSplitFuel (leaf : Nat → HypState) : Nat → Nat → Nat → HypState
  | 0, l, n => hypSeq leaf l n
  | _ + 1, _, 0 => hypEmpty
  | _ + 1, l, 1 => leaf l
  | fuel + 1, l, n + 2 =>
    let m := (n + 2) / 2
    hypMerge (hypSplitFuel leaf fuel l m) (hypSplitFuel leaf fuel (l + m) (n + 2 - m))

/-- Binary splitting of the range `[l, l+n)` (fuel `n`, enough for every depth). -/
def hypSplit (leaf : Nat → HypState) (l n : Nat) : HypState := hypSplitFuel leaf n l n

/-- The leaf of `∑ 1/((2k+1)² C(2k,k))`: the ratio of the term of index `l` to the previous one
is `l (2l − 1) / (2 (2l + 1)²)` (and `1` for `l = 0`). -/
def catalanLeaf (l : Nat) : HypState :=
  if l = 0 then (ofNat 1, ofNat 1, ofNat 1)
  else
    let p := ofNat (l * (2 * l - 1))
    (p, ofNat (2 * (2 * l + 1) * (2 * l + 1)), p)

/-- The exact fraction `(3/8) ∑_{k<N} 1/((2k+1)² C(2k,k)) = num/den` with `num = 3 T(0, N)`,
`den = 8 Q(0, N)`. -/
def catalanNumDen (N : Nat) : AzNat × AzNat :=
  let s := hypSplit catalanLeaf 0 N
  (ofNat 3 * s.2.2, ofNat 8 * s.2.1)

/-- The leaf of `∑ 1/((2k+1) 3^{k+1})`: `(1, 2l+1, 3)`. -/
def atanhSqrtThreeLeaf (l : Nat) : SplitState := (ofNat 1, ofNat (2 * l + 1), ofNat 3)

/-- The exact fraction `(1/4) ∑_{k<N} 1/((2k+1) 3^{k+1}) = num/den` with `num = T(0, N)`,
`den = 4 B(0, N) Q(0, N)`. -/
def atanhSqrtThreeNumDen (N : Nat) : AzNat × AzNat :=
  let s := splitOf atanhSqrtThreeLeaf 0 N
  (s.1, ofNat 4 * (s.2.1 * s.2.2))

end Azurite.AzNat
