/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzInt.Sub
import Azurite.AzInt.MulSmall
import Azurite.AzInt.Mul
import Azurite.AzInt.ShiftRight
import Azurite.AzInt.Conversion
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.MulNat

/-!
## Sweeney's series by a truncated backward recurrence

The partial sum `S = ∑_{k<N} (−1)^k n^(k+1) / ((k+1) (k+1)!)` of Sweeney's series for Euler's
constant satisfies `S = Z₀` for the backward recurrence

  `Z_N = 0`,   `Z_k = (n / (k+1)) · ((−1)^k / (k+1) + Z_{k+1})`.

Writing `Z_k = ν_k / δ_k`, one step is the integer map
`(ν, δ) ↦ (n (k+1) ν + (−1)^k n δ, (k+1)² δ)`, the upper triangular matrix
`[[n (k+1), (−1)^k n], [0, (k+1)²]]` — no division.  Two economies make this fast at every
precision:

* **Word-sized blocks.**  The matrices of consecutive steps are multiplied in machine
  arithmetic, `[[A, B], [0, C]]`, as long as the entries stay below `2^63`
  (`sweeneyFits`); only then is the block applied to the long numbers (`sweeneyFlush`):
  three single-limb multiplications and one addition for several terms of the series.
* **Truncation.**  `ν / δ` is unchanged when both are divided by a power of two, so after each
  block the pair is cut back to about `V` bits (whole limbs).  The exact fraction of the
  partial sum has about `N log N` bits; here nothing longer than `V + 128` bits is ever
  multiplied.

The truncation error is carried along exactly, as a radius: the state `(nm, dn, rn)` stands
for every `Z` with `|Z · dn − nm| ≤ rn`.  A block multiplies the radius by `A`; a truncation
adds `2 + |Z|` to it.  So nothing has to be proven about the size of the error — the final
enclosure `sweeneyHornerEncl` of `S` is valid whatever `V` is, and its width is whatever the
radius says.  (The radius grows to about `1.45 n` bits, the cancellation of the series, which
is why `V ≈ w + 1.45 n` is needed for `w` good bits.)

The proofs are in `Azurite/AzInt/Equiv/SweeneyHorner.lean`.
-/

namespace Azurite.AzInt

/-- `z · a` for a natural `a`: a single-limb multiplication when `a < 2^63`. -/
def mulNat (z : AzInt) (a : Nat) : AzInt :=
  if a ≤ 9223372036854775807 then mulUInt64 z a.toUInt64 else z * (AzNat.ofNat a).toAzInt

/-- The state of the truncated recurrence: `|Z · dn − nm| ≤ rn` for the value `Z` it stands
for. -/
structure SweeneyState where
  /-- The numerator. -/
  nm : AzInt
  /-- The denominator. -/
  dn : AzNat
  /-- The radius of the numerator. -/
  rn : AzNat

/-- Cut the state back to about `V` bits: when the denominator has at least `V + 256` bits,
everything is shifted right by the whole limbs above `V` bits.
The radius grows by `2 + 2^j ≥ 2 + |Z|`, with `j` read off the bit lengths. -/
def sweeneyTrim (V : Nat) (s : SweeneyState) : SweeneyState :=
  if V + 256 ≤ s.dn.size then
    let sh := (s.dn.size - V) / 64 * 64
    ⟨s.nm >>> sh, s.dn >>> sh,
      (s.rn >>> sh) + (AzNat.ofNat 2 + (1 : AzNat) <<< (max s.nm.abs.size s.rn.size + 2
        - s.dn.size))⟩
  else s

/-- Apply the word block `[[A, Bp − Bn], [0, C]]` to the state, `Z ↦ (A Z + B) / C`, and
trim. -/
def sweeneyFlush (V A Bp Bn C : Nat) (s : SweeneyState) : SweeneyState :=
  sweeneyTrim V
    ⟨if Bn ≤ Bp then s.nm.mulNat A + (s.dn.mulNat (Bp - Bn)).toAzInt
      else s.nm.mulNat A - (s.dn.mulNat (Bn - Bp)).toAzInt,
      s.dn.mulNat C, s.rn.mulNat A⟩

/-- A long block `[[A, B], [0, C]]`. -/
structure SweeneyBlock where
  /-- The upper left entry. -/
  A : AzNat
  /-- The upper right entry. -/
  B : AzInt
  /-- The lower right entry. -/
  C : AzNat

/-- The identity block. -/
def SweeneyBlock.one : SweeneyBlock := ⟨AzNat.ofNat 1, 0, AzNat.ofNat 1⟩

/-- The word block `[[a, bp − bn], [0, c]]` times the long block `M`. -/
def sweeneyPush (a bp bn c : Nat) (M : SweeneyBlock) : SweeneyBlock :=
  ⟨M.A.mulNat a,
    if bn ≤ bp then M.B.mulNat a + (M.C.mulNat (bp - bn)).toAzInt
    else M.B.mulNat a - (M.C.mulNat (bn - bp)).toAzInt,
    M.C.mulNat c⟩

/-- Apply the long block `M` to the state and trim. -/
def sweeneyApply (V : Nat) (M : SweeneyBlock) (s : SweeneyState) : SweeneyState :=
  sweeneyTrim V ⟨M.A.toAzInt * s.nm + M.B * s.dn.toAzInt, M.C * s.dn, M.A * s.rn⟩

/-- A cheap sufficient test, on bit lengths, that the word block `[[A, Bp − Bn], [0, C]]` times
the matrix `[[a, ±n], [0, c]]` of one more index has entries below `2^63`. -/
def sweeneyFits (a n c A Bp Bn C : Nat) : Bool :=
  decide (a.log2 + A.log2 < 62) && decide (n.log2 + C.log2 < 61)
    && decide (a.log2 + Bp.log2 < 61) && decide (a.log2 + Bn.log2 < 61)
    && decide (c.log2 + C.log2 < 62)

/-- The backward recurrence from index `k` down to `0`, word blocks applied directly:
`[[A, Bp − Bn], [0, C]]` is the pending word block (the product of the matrices of the indices
from `k` up to where `s` stands; the signed entry is kept as a difference of naturals, so that
the loop runs on machine words).  The matrix `[[n k, ±n], [0, k²]]` of index `k − 1` is
multiplied into the block if the result fits a word; otherwise the block is flushed first. -/
def sweeneyHornerLoop (n V : Nat) : Nat → Nat → Nat → Nat → Nat → SweeneyState → SweeneyState
  | 0, A, Bp, Bn, C, s => sweeneyFlush V A Bp Bn C s
  | k + 1, A, Bp, Bn, C, s =>
    let a := n * (k + 1)
    let c := (k + 1) * (k + 1)
    if sweeneyFits a n c A Bp Bn C then
      if k % 2 = 0 then sweeneyHornerLoop n V k (a * A) (a * Bp + n * C) (a * Bn) (c * C) s
      else sweeneyHornerLoop n V k (a * A) (a * Bp) (a * Bn + n * C) (c * C) s
    else if k % 2 = 0 then sweeneyHornerLoop n V k a n 0 c (sweeneyFlush V A Bp Bn C s)
    else sweeneyHornerLoop n V k a 0 n c (sweeneyFlush V A Bp Bn C s)

/-- The same recurrence with two levels of blocks: a word block that is full is multiplied
into the long block `M`, and `M` is applied to the state once its entries have `Lb` bits. -/
def sweeneyHornerLoop₂ (n V Lb : Nat) :
    Nat → Nat → Nat → Nat → Nat → SweeneyBlock → SweeneyState → SweeneyState
  | 0, A, Bp, Bn, C, M, s => sweeneyApply V (sweeneyPush A Bp Bn C M) s
  | k + 1, A, Bp, Bn, C, M, s =>
    let a := n * (k + 1)
    let c := (k + 1) * (k + 1)
    if sweeneyFits a n c A Bp Bn C then
      if k % 2 = 0 then
        sweeneyHornerLoop₂ n V Lb k (a * A) (a * Bp + n * C) (a * Bn) (c * C) M s
      else sweeneyHornerLoop₂ n V Lb k (a * A) (a * Bp) (a * Bn + n * C) (c * C) M s
    else if Lb ≤ (sweeneyPush A Bp Bn C M).C.size then
      if k % 2 = 0 then
        sweeneyHornerLoop₂ n V Lb k a n 0 c SweeneyBlock.one
          (sweeneyApply V (sweeneyPush A Bp Bn C M) s)
      else
        sweeneyHornerLoop₂ n V Lb k a 0 n c SweeneyBlock.one
          (sweeneyApply V (sweeneyPush A Bp Bn C M) s)
    else if k % 2 = 0 then sweeneyHornerLoop₂ n V Lb k a n 0 c (sweeneyPush A Bp Bn C M) s
    else sweeneyHornerLoop₂ n V Lb k a 0 n c (sweeneyPush A Bp Bn C M) s

/-- The state for the sum of the first `N` terms of Sweeney's series with argument `n`, at `V`
bits; long blocks of `Lb` bits, or word blocks only for `Lb = 0`. -/
def sweeneyHorner (n N V Lb : Nat) : SweeneyState :=
  if Lb = 0 then sweeneyHornerLoop n V N 1 0 0 1 ⟨0, (1 : AzNat) <<< V, 0⟩
  else sweeneyHornerLoop₂ n V Lb N 1 0 0 1 SweeneyBlock.one ⟨0, (1 : AzNat) <<< V, 0⟩

/-- Numerators `a`, `c` and the denominator `d` with `a / d ≤ S ≤ c / d` for the partial sum
`S ≥ 0` of the first `N` terms: `nm − rn` (or `0` when `nm < rn`), `nm + rn`, and `dn`. -/
def sweeneyHornerEncl (n N V Lb : Nat) : AzNat × AzNat × AzNat :=
  let s := sweeneyHorner n N V Lb
  let lo := s.nm - s.rn.toAzInt
  (if lo.sign then lo.abs else 0, (s.nm + s.rn.toAzInt).abs, s.dn)

end Azurite.AzInt
