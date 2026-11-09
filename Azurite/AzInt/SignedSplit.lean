/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzInt.Mul
import Azurite.AzInt.Conversion
import Azurite.AzNat.Mul
import Azurite.AzNat.Square

/-!
## Signed binary splitting (`P, Q, T`) and Sweeney's series for Euler's constant

The partial sums of a hypergeometric-like series `∑_k (a k / q k) ∏_{j≤k} p j / q j` with signed
numerators `a k` are computed **exactly** by binary splitting.  This is the general `P, Q, B, T`
form of MCA §4.9.1 in the case `b = q` (the small denominator factor of the term equal to the
denominator of the ratio), where `B = Q` and the state shrinks to `(P, Q, T)`: over an index
range `[l, l+n)` it represents

  `P = ∏_{k<n} p (l+k)`, `Q = ∏_{k<n} q (l+k)`,
  `T / Q² = ∑_{k<n} (a (l+k) / q (l+k)) ∏_{j≤k} p (l+j) / q (l+j)`:

a single term is `(p, q, a p)` and two adjacent ranges merge by
`(P₁ P₂, Q₁ Q₂, Q₂² T₁ + Q₁ P₁ T₂)` (`signedMerge`), because the second range's terms carry the
extra factor `P₁/Q₁` — two products and one squaring of `AzNat`s and two `AzNat × AzInt`
products per merge, against the five products of the general form.  `T` is an `AzInt`,
everything else an `AzNat`.  As in `AzNat/AtanhSplit.lean`, the engine is generic in the leaf
(`signedSeqOf`, `signedSplitFuelOf`, `signedSplitOf`) and the result does not depend on the fuel.

**Sweeney's series** for Euler's constant: `γ = ∑_{k≥0} (−1)^k n^(k+1) / ((k+1) (k+1)!) − ln n
− E₁(n)` (`Azurite/Transcendental/EulerGamma.lean`), with the term of index `k` equal to
`((−1)^k / (k+1)) ∏_{j≤k} n / (j+1)`: the leaf is `(n, k+1, ±n)` (`sweeneyLeaf`) and
`sweeneyNumDen n N = (T, Q²)` is the exact fraction `∑_{k<N} (−1)^k n^(k+1) / ((k+1) (k+1)!)`.

The proofs are in `Azurite/AzInt/Equiv/SignedSplit.lean`.
-/

namespace Azurite.AzInt

/-- A signed binary-splitting state `(P, Q, T)` representing the fraction `T/Q²`. -/
abbrev SignedSplitState := AzNat × AzNat × AzInt

/-- Merge the states of two adjacent ranges: `(P₁ P₂, Q₁ Q₂, Q₂² T₁ + Q₁ P₁ T₂)`. -/
def signedMerge (x y : SignedSplitState) : SignedSplitState :=
  (x.1 * y.1, x.2.1 * y.2.1,
    (AzNat.square y.2.1).toAzInt * x.2.2 + (x.2.1 * x.1).toAzInt * y.2.2)

/-- The empty range. -/
def signedEmpty : SignedSplitState := (AzNat.ofNat 1, AzNat.ofNat 1, 0)

/-- The sequential evaluation of the range `[l, l+n)` for the series with the given `leaf` (the
term of index `l` as a state), the fallback when the fuel runs out. -/
def signedSeqOf (leaf : Nat → SignedSplitState) : Nat → Nat → SignedSplitState
  | _, 0 => signedEmpty
  | l, n + 1 => signedMerge (leaf l) (signedSeqOf leaf (l + 1) n)

/-- Binary splitting of the range `[l, l+n)` with `fuel` halvings. -/
def signedSplitFuelOf (leaf : Nat → SignedSplitState) : Nat → Nat → Nat → SignedSplitState
  | 0, l, n => signedSeqOf leaf l n
  | _ + 1, _, 0 => signedEmpty
  | _ + 1, l, 1 => leaf l
  | fuel + 1, l, n + 2 =>
    let m := (n + 2) / 2
    signedMerge (signedSplitFuelOf leaf fuel l m) (signedSplitFuelOf leaf fuel (l + m) (n + 2 - m))

/-- Binary splitting of the range `[l, l+n)` (fuel `n`, enough for every depth). -/
def signedSplitOf (leaf : Nat → SignedSplitState) (l n : Nat) : SignedSplitState :=
  signedSplitFuelOf leaf n l n

/-! ### Sweeney's series -/

/-- The term of index `k` of Sweeney's series, `((−1)^k / (k+1)) · n/(k+1) · (∏_{j<k} n/(j+1))`,
as the leaf `(n, k+1, (−1)^k n)`. -/
def sweeneyLeaf (n : AzNat) (k : Nat) : SignedSplitState :=
  (n, AzNat.ofNat (k + 1), if k % 2 = 0 then n.toAzInt else -n.toAzInt)

/-- The exact fraction `∑_{k<N} (−1)^k n^(k+1) / ((k+1) (k+1)!) = T / Q²`, as `(T, Q²)`. -/
def sweeneyNumDen (n N : Nat) : AzInt × AzNat :=
  let s := signedSplitOf (sweeneyLeaf (AzNat.ofNat n)) 0 N
  (s.2.2, AzNat.square s.2.1)

end Azurite.AzInt
