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
* `barrettStep V X n A`: for `A < V β^n`, the quotient and remainder of `A` by `V` from the trial
  quotient `⌊⌊A/β^n⌋ X / β^n⌋` and at most four corrections (MCA Algorithm 2.5, Theorem 2.4
  adapted to the approximate reciprocal: `A < V (Q + 5)`).
* `divModNewton base U V`: normalizes `V` to `β^n/2 ≤ V' < β^n` by a shift, computes the
  reciprocal once, and divides the shifted dividend block by block of `n` limbs
  (`newtonDivBlocks`; the divisor is "implicitly invariant"), then shifts the remainder back.

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

/-- MCA Algorithm 3.5 with explicit fuel (`n` suffices: the recursive call has fewer limbs). -/
def approxReciprocalFuel (base : Nat) : Nat → AzNat → Nat → AzNat
  | 0, A, n => reciprocalBase A n
  | fuel + 1, A, n =>
    if n ≤ base then reciprocalBase A n
    else
      let l := (n - 1) / 2
      let h := n - l
      let Ah := A >>> (64 * l)
      let Xh := approxReciprocalFuel base fuel Ah h
      let B := pow2 (64 * (n + h))
      let xt := reciprocalCorrect A B 4 Xh (A * Xh)
      let D := B - xt.2
      let Tm := D >>> (64 * l)
      let U := Tm * xt.1
      (xt.1 <<< (64 * l)) + (U >>> (64 * (2 * h - l)))

/-- **Approximate reciprocal** (MCA Algorithm 3.5): for `β^n/2 ≤ A < β^n`, an `X` with
`A X < β^(2n) < A (X + 2)`. -/
def approxReciprocal (base : Nat) (A : AzNat) (n : Nat) : AzNat :=
  approxReciprocalFuel base n A n

/-- Steps 4–5 of MCA Algorithm 2.5: while `R ≥ V`, `(Q, R) ← (Q + 1, R − V)`, at most `fuel`
times. -/
def barrettCorrect (V : AzNat) : Nat → AzNat → AzNat → AzNat × AzNat
  | 0, Q, R => (Q, R)
  | fuel + 1, Q, R => if V ≤ R then barrettCorrect V fuel (Q + 1) (R - V) else (Q, R)

/-- **Barrett's step** (MCA Algorithm 2.5 in base `β^n`): `(Q, R)` with `A = Q V + R`,
`R < V`, for `A < V β^n` and `X` an approximate reciprocal of `V`. -/
def barrettStep (V X : AzNat) (n : Nat) (A : AzNat) : AzNat × AzNat :=
  let A1 := A >>> (64 * n)
  let Q := (A1 * X) >>> (64 * n)
  let R := A - Q * V
  barrettCorrect V 5 Q R

/-- Divide the top `j` blocks of `n` limbs of `U` (blocks `j − 1, …, 0`), continuing from the
quotient `Q` and remainder `R` of the blocks above. -/
def newtonDivBlocks (V X : AzNat) (n : Nat) (U : AzNat) : Nat → AzNat → AzNat → AzNat × AzNat
  | 0, Q, R => (Q, R)
  | j + 1, Q, R =>
    let blk := (U >>> (64 * (n * j))).modPow2 (64 * n)
    let qr := barrettStep V X n ((R <<< (64 * n)) + blk)
    newtonDivBlocks V X n U j ((Q <<< (64 * n)) + qr.1) qr.2

/-- **Newton–Barrett division**: `(U / V, U % V)`, with `(0, U)` for `V = 0`. -/
def divModNewton (base : Nat) (U V : AzNat) : AzNat × AzNat :=
  if V.limbs.size = 0 then (0, U)
  else
    let n := V.limbs.size
    let k := 64 * n - V.size
    let V' := V <<< k
    let U' := U <<< k
    let X := approxReciprocal base V' n
    let j := (U'.limbs.size + n - 1) / n
    let qr := newtonDivBlocks V' X n U' j 0 0
    (qr.1, qr.2 >>> k)

end Azurite.AzNat
