/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.AtanhSplit
import Azurite.AzNat.ShiftLeft

/-!
## Binary splitting for the exponential series at a dyadic rational

For `x = p / 2^s` (`p : AzNat`, `s : ℕ`), the partial sum `∑_{m≤N} x^m/m!` is computed
**exactly** as a fraction of big integers by binary splitting (MCA §4.9).  Over an index range
`[l, l+n)` the state `(P, B, T)` represents

  `∑_{k<n} ∏_{i≤k} p/(2^s (l+i+1)) = T / (B · 2^(s n))`,  `P = p^n`,  `B = ∏_{i<n} (l+i+1)`:

a single term is `(p, l+1, p)` (`expLeaf`), and two adjacent ranges merge by
`(P₁ P₂, B₁ B₂, (T₁ B₂) · 2^(s n₂) + P₁ T₂)` (`expMerge`), because the second range's terms carry
the factor `P₁/(B₁ 2^(s n₁))`.  The power-of-two part of the denominator is never materialized:
it is the shift `s · n`.  `expSplitFuel` halves the range `fuel` times (`expSplit` uses
`fuel = n`) and finishes sequentially (`expSeq`) if the fuel runs out.  Finally
`∑_{m≤N} x^m/m! = (B · 2^(sN) + T) / (B · 2^(sN))` (`expNumDen`, returning the numerator and `B`;
the shift `sN` is applied by the caller).

The proofs are in `Azurite/AzNat/Equiv/ExpSplit.lean`.
-/

namespace Azurite.AzNat

/-- Merge the states of two adjacent ranges, the second of length `n₂`:
`(P₁ P₂, B₁ B₂, (T₁ B₂) · 2^(s n₂) + P₁ T₂)`. -/
def expMerge (s n₂ : Nat) (x y : SplitState) : SplitState :=
  (x.1 * y.1, x.2.1 * y.2.1, ((x.2.2 * y.2.1) <<< (s * n₂)) + x.1 * y.2.2)

/-- The single term of index `l`: `p/(2^s (l+1))`, as `(p, l+1, p)`. -/
def expLeaf (p : AzNat) (l : Nat) : SplitState := (p, ofNat (l + 1), p)

/-- The empty range: `(1, 1, 0)`. -/
def expEmpty : SplitState := (ofNat 1, ofNat 1, ofNat 0)

/-- The sequential evaluation of the range `[l, l+n)`, the fallback when the fuel runs out. -/
def expSeq (p : AzNat) (s : Nat) : Nat → Nat → SplitState
  | _, 0 => expEmpty
  | l, n + 1 => expMerge s n (expLeaf p l) (expSeq p s (l + 1) n)

/-- Binary splitting of the range `[l, l+n)` with `fuel` halvings. -/
def expSplitFuel (p : AzNat) (s : Nat) : Nat → Nat → Nat → SplitState
  | 0, l, n => expSeq p s l n
  | _ + 1, _, 0 => expEmpty
  | _ + 1, l, 1 => expLeaf p l
  | fuel + 1, l, n + 2 =>
    let m := (n + 2) / 2
    expMerge s (n + 2 - m) (expSplitFuel p s fuel l m) (expSplitFuel p s fuel (l + m) (n + 2 - m))

/-- Binary splitting of the range `[l, l+n)` (fuel `n`, enough for every depth). -/
def expSplit (p : AzNat) (s l n : Nat) : SplitState := expSplitFuel p s n l n

/-- The exact fraction `∑_{m≤N} (p/2^s)^m/m! = num / (den · 2^(sN))`. -/
def expNumDen (p : AzNat) (s N : Nat) : AzNat × AzNat :=
  let st := expSplit p s 0 N
  (st.2.1 <<< (s * N) + st.2.2, st.2.1)

end Azurite.AzNat
