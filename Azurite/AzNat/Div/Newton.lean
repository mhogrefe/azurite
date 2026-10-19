/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Classic
import Azurite.AzNat.Mul
import Azurite.AzNat.Add
import Azurite.AzNat.Sub
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Pow2
import Azurite.AzNat.Compare
import Azurite.AzNat.Size
import Azurite.AzNat.Mul.SSCached
import Azurite.AzNat.Mul.ShortProduct

/-!
## Newton–Barrett division

Division in `O(M(n))` (MCA §3.4, §2.4.1), with `β = 2^64` the limb base.

* `approxReciprocal base A n`: for `β^n/2 ≤ A < β^n`, an integer `X` with
  `A X < β^(2n) < A (X + 2)` (MCA Algorithm 3.5 and Lemma 3.8).  Newton's iteration on the
  reciprocal: the recursive call gives the top `h = n − ⌊(n−1)/2⌋` limbs, one product
  `T = A X_h` (corrected by at most four decrements so that `T < β^(n+h)`), and one more
  product `T_m X_h` with the top of `β^(n+h) − T` supplies the low `ℓ = n − h` limbs.  Below
  `base` limbs the reciprocal is `⌊(β^(2n) − 1)/A⌋` by the classical division
  (`reciprocalBase`).  Full products are used; the wrap-around trick (MCA §3.4.1) is a later
  optimization.
* `barrettStep sp V X n A`: for `A < V β^n`, the quotient and remainder of `A` by `V` from the
  trial quotient `⌊⌊A/β^n⌋ X / β^n⌋` (MCA Algorithm 2.5, Theorem 2.4 adapted to the approximate
  reciprocal: `A < V (Q + 5)`), computed with Mulders' short products (`Mul/ShortProduct`,
  MCA §3.3 and the remark of §2.4.1): the high short product with one guard limb for the trial
  quotient, the exact low product for the remainder.
* `divModNewton base fftFrom sp U V` (`sp` the short products' base-case size): normalizes `V` to `β^n/2 ≤ V' < β^n` by a shift, computes the
  reciprocal once, and divides the shifted dividend block by block of `n` limbs
  (`newtonDivBlocks`; the divisor is "implicitly invariant"), then shifts the remainder back.

From `fftFrom` limbs on, the FFT-range tricks of MCA §3.4.1 and §2.4.1 are used:

* the product `A X_h` of the reciprocal step is computed modulo `2^m + 1` only, `m ≥ 64 (n+1)`
  bits, and recovered exactly from the window `(β^(n+h) − 2β^n, β^(n+h) + 2β^n)` it is known to
  lie in (`wrapProduct`; about half the cost of the full product);
* Barrett's steps use cached forward transforms of the reciprocal and the divisor
  (`BarrettCache`, `barrettStepFFT`): the trial quotient's product `A₁ X` costs one forward and one
  backward transform, and the remainder is `A − Q V` computed modulo `2^m + 1` (`m ≥ 64 (n+1)`),
  exact because `0 ≤ A − Q V < 5V`.

Correctness: `Equiv/Div/Newton.lean`.  All recursions are structural (fuel), so the definitions
reduce in the kernel.
-/

namespace Azurite.AzNat

/-- `⌊(β^(2n) − 1)/A⌋`, the exact base case of the reciprocal. -/
def reciprocalBase (A : AzNat) (n : Nat) : AzNat :=
  (divModClassic divDispatchThreshold (pow2 (128 * n) - 1) A).1

/-- Steps 6–7 of MCA Algorithm 3.5: while `T ≥ B`, `(x, T) ← (x − 1, T − A)`, at most `fuel`
times. -/
def reciprocalCorrect (A B : AzNat) : Nat → AzNat → AzNat → AzNat × AzNat
  | 0, x, T => (x, T)
  | fuel + 1, x, T => if B ≤ T then reciprocalCorrect A B fuel (x - 1) (T - A) else (x, T)

/-- The wrap-around trick (MCA §3.4.1): `A X_h` from its residue modulo `2^m + 1`,
`m = (SSPlan.ofLimbs (n+1)).bits ≥ 64 (n+1)`, given that `β^(n+h) − 2β^n < A X_h < β^(n+h) + 2β^n`:
the unique number in that window congruent to the residue is `lo + ((T − lo) mod (2^m + 1))` with
`lo = β^(n+h) − 2β^n + 1`. -/
def wrapProduct (n h : Nat) (A Xh : AzNat) : AzNat :=
  let p := SSPlan.ofLimbs (n + 1)
  let Tf := p.mulModF' (· * ·) A Xh
  let lo := pow2 (64 * (n + h)) - (pow2 (64 * n) <<< (1 : Nat)) + 1
  lo + (AzFermat.sub Tf (AzFermat.ofAzNat p.bits lo)).val

/-- Steps 6–11 of MCA Algorithm 3.5 from `X_h` and `T₀ = A X_h`: the correction loop, then the
low limbs from `T_m X_h`. -/
def newtonStepAssemble (n l h : Nat) (A Xh T0 : AzNat) : AzNat :=
  let B := pow2 (64 * (n + h))
  let xt := reciprocalCorrect A B 4 Xh T0
  let D := B - xt.2
  let Tm := D >>> (64 * l)
  let U := Tm * xt.1
  (xt.1 <<< (64 * l)) + (U >>> (64 * (2 * h - l)))

/-- MCA Algorithm 3.5 with explicit fuel (`n` suffices: the recursive call has fewer limbs); the
product `A X_h` by the wrap-around trick from `fftFrom` limbs on. -/
def approxReciprocalFuel (base fftFrom : Nat) : Nat → AzNat → Nat → AzNat
  | 0, A, n => reciprocalBase A n
  | fuel + 1, A, n =>
    if n ≤ base then reciprocalBase A n
    else
      let l := (n - 1) / 2
      let h := n - l
      let Ah := A >>> (64 * l)
      let Xh := approxReciprocalFuel base fftFrom fuel Ah h
      let T0 := if fftFrom ≤ n then wrapProduct n h A Xh else A * Xh
      newtonStepAssemble n l h A Xh T0

/-- **Approximate reciprocal** (MCA Algorithm 3.5): for `β^n/2 ≤ A < β^n`, an `X` with
`A X < β^(2n) < A (X + 2)`. -/
def approxReciprocal (base fftFrom : Nat) (A : AzNat) (n : Nat) : AzNat :=
  approxReciprocalFuel base fftFrom n A n

/-- Steps 4–5 of MCA Algorithm 2.5: while `R ≥ V`, `(Q, R) ← (Q + 1, R − V)`, at most `fuel`
times. -/
def barrettCorrect (V : AzNat) : Nat → AzNat → AzNat → AzNat × AzNat
  | 0, Q, R => (Q, R)
  | fuel + 1, Q, R => if V ≤ R then barrettCorrect V fuel (Q + 1) (R - V) else (Q, R)

/-- **Barrett's step** (MCA Algorithm 2.5 in base `β^n`) with short products (MCA §2.4.1):
`(Q, R)` with `A = Q V + R`, `R < V`, for `A < V β^n` and `X` an approximate reciprocal of `V`.
The trial quotient is the high short product `mulHigh` with one guard limb — within `3(n+1)` of
`⌊⌊A/β^n⌋ X/β^(n−1)⌋`, so after `/β` within `3(n+1)` of the exact trial quotient, one unit in
practice — and the remainder `A − Q V` is the exact low product `mulLow` modulo `β^w`, with
`β^w > (3n+9) V`; `3n + 9` corrections suffice (at most five in practice). -/
def barrettStep (sp : Nat) (V X : AzNat) (n : Nat) (A : AzNat) : AzNat × AzNat :=
  let A1 := A >>> (64 * n)
  let Q := mulHigh sp (A1 <<< 128) (X <<< 64) (n + 2) >>> 64
  let w := n + 2 + Nat.size (3 * n + 9) / 64
  let R := ((A.modPow2 (64 * w) + pow2 (64 * w)) - mulLow sp Q V w).modPow2 (64 * w)
  barrettCorrect V (3 * n + 9) Q R

/-- Divide the top `j` blocks of `n` limbs of `U` (blocks `j − 1, …, 0`), continuing from the
quotient `Q` and remainder `R` of the blocks above. -/
def newtonDivBlocks (sp : Nat) (V X : AzNat) (n : Nat) (U : AzNat) :
    Nat → AzNat → AzNat → AzNat × AzNat
  | 0, Q, R => (Q, R)
  | j + 1, Q, R =>
    let blk := (U >>> (64 * (n * j))).modPow2 (64 * n)
    let qr := barrettStep sp V X n ((R <<< (64 * n)) + blk)
    newtonDivBlocks sp V X n U j ((Q <<< (64 * n)) + qr.1) qr.2

/-- The cached forward transforms for Barrett's steps: of the reciprocal `X` for the full
product `A₁ X` (residues of `2n + 1` limbs) and of the divisor `V` for the remainder
`A − Q V mod (2^m + 1)` (residues of `n + 1` limbs). -/
structure BarrettCache where
  /-- The plan of the full product `A₁ X`. -/
  full : SSPlan
  /-- The transform of `X`. -/
  fX : Array (AzFermat full.N)
  hfX : fX.size = 2 ^ (full.k + 1)
  /-- The plan of the modular product `Q V`. -/
  modp : SSPlan
  /-- The transform of `V`. -/
  fV : Array (AzFermat modp.N)
  hfV : fV.size = 2 ^ (modp.k + 1)

/-- The cache for an `n`-limb divisor `V` with reciprocal `X`. -/
def mkBarrettCache (n : Nat) (V X : AzNat) : BarrettCache :=
  let full := SSPlan.ofLimbs (2 * n + 1)
  let modp := SSPlan.ofLimbs (n + 1)
  ⟨full, full.transform X, full.transform_size X, modp, modp.transform V, modp.transform_size V⟩

/-- The trial quotient `⌊⌊A/β^n⌋ X / β^n⌋` with the cached transform of `X` (the product
`⌊A/β^n⌋ X` is below `2^full.bits`, so its residue is exact). -/
def barrettQuotientFFT (c : BarrettCache) (n : Nat) (A : AzNat) : AzNat :=
  (c.full.mulModF (· * ·) c.fX c.hfX (A >>> (64 * n))).val >>> (64 * n)

/-- `(A − Q V) mod (2^modp.bits + 1)` with the cached transform of `V`; equal to `A − Q V` when
`0 ≤ A − Q V < 2^modp.bits`. -/
def barrettRemainderFFT (c : BarrettCache) (A Q : AzNat) : AzNat :=
  (AzFermat.sub (AzFermat.ofAzNat c.modp.bits A) (c.modp.mulModF (· * ·) c.fV c.hfV Q)).val

/-- Barrett's step with the cached transforms. -/
def barrettStepFFT (c : BarrettCache) (V : AzNat) (n : Nat) (A : AzNat) : AzNat × AzNat :=
  let Q := barrettQuotientFFT c n A
  barrettCorrect V 5 Q (barrettRemainderFFT c A Q)

/-- `newtonDivBlocks` with `barrettStepFFT`. -/
def newtonDivBlocksFFT (c : BarrettCache) (V : AzNat) (n : Nat) (U : AzNat) :
    Nat → AzNat → AzNat → AzNat × AzNat
  | 0, Q, R => (Q, R)
  | j + 1, Q, R =>
    let blk := (U >>> (64 * (n * j))).modPow2 (64 * n)
    let qr := barrettStepFFT c V n ((R <<< (64 * n)) + blk)
    newtonDivBlocksFFT c V n U j ((Q <<< (64 * n)) + qr.1) qr.2

/-- The `j` blocks of `U` by `V` (reciprocal `X`), with the FFT-range Barrett step from
`fftFrom` limbs on. -/
def newtonDivBlocksDispatch (sp fftFrom : Nat) (V X : AzNat) (n : Nat) (U : AzNat) (j : Nat) :
    AzNat × AzNat :=
  if fftFrom ≤ n then newtonDivBlocksFFT (mkBarrettCache n V X) V n U j 0 0
  else newtonDivBlocks sp V X n U j 0 0

/-- **Newton–Barrett division**: `(U / V, U % V)`, with `(0, U)` for `V = 0`; the FFT-range
tricks from `fftFrom` divisor limbs on. -/
def divModNewton (base fftFrom sp : Nat) (U V : AzNat) : AzNat × AzNat :=
  if V.limbs.size = 0 then (0, U)
  else
    let n := V.limbs.size
    let k := 64 * n - V.size
    let V' := V <<< k
    let U' := U <<< k
    let X := approxReciprocal base fftFrom V' n
    let j := (U'.limbs.size + n - 1) / n
    let qr := newtonDivBlocksDispatch sp fftFrom V' X n U' j
    (qr.1, qr.2 >>> k)

end Azurite.AzNat
