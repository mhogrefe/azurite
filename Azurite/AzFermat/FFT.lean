/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFermat.Basic
import Azurite.BrentZimmermann.Chapter2.FFT

/-!
# The FFT over `AzFermat N`

Algorithms 2.2 (ForwardFFT) and 2.3 (BackwardFFT) of Brent–Zimmermann on arrays of `2^k`
residues modulo `2^N + 1`.  The root of unity is a power of two, `ω = 2^e`, so every twiddle
multiplication is `mulPow2`.  `forwardFFT` takes the natural order to the bit-reversed order and
`backwardFFT` the bit-reversed order back to the natural order, exactly as the functional
`BZ.forwardFFT` / `BZ.backwardFFT` of `BrentZimmermann/Chapter2/FFT.lean`; the correspondence,
position by position through `toZMod`, is in `Equiv/FFT.lean`.

The arrays carry their size in the type (`{ b // b.size = 2^k }`) so that every index is
checked; the recursion copies the even/odd (resp. lower/upper) halves into fresh arrays, which
is `O(K log K)` pointer copies against the same number of big-number operations.
-/

namespace Azurite.AzFermat

variable {N : Nat} [NeZero N]

/-- Algorithm 2.2 on `2^k` residues with root `2^e`: the transform in bit-reversed order. -/
def forwardFFTRec (e : Nat) : (k : Nat) → (a : Array (AzFermat N)) → a.size = 2 ^ k →
    { b : Array (AzFermat N) // b.size = 2 ^ k }
  | 0, a, ha => ⟨a, ha⟩
  | k + 1, a, ha =>
    let evens : Array (AzFermat N) := Array.ofFn fun i : Fin (2 ^ k) =>
      a[2 * i.val]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega)
    let odds : Array (AzFermat N) := Array.ofFn fun i : Fin (2 ^ k) =>
      a[2 * i.val + 1]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega)
    let b := forwardFFTRec (2 * e) k evens Array.size_ofFn
    let c := forwardFFTRec (2 * e) k odds Array.size_ofFn
    ⟨Array.ofFn fun r : Fin (2 ^ (k + 1)) =>
      have hj : r.val / 2 < 2 ^ k := by have := r.isLt; have hK := pow_succ 2 k; omega
      let t := mulPow2 (e * BZ.bitrev k (r.val / 2)) (c.1[r.val / 2]'(Nat.lt_of_lt_of_eq hj c.2.symm))
      if r.val % 2 = 0 then b.1[r.val / 2]'(Nat.lt_of_lt_of_eq hj b.2.symm) + t
      else b.1[r.val / 2]'(Nat.lt_of_lt_of_eq hj b.2.symm) - t,
     Array.size_ofFn⟩

/-- Algorithm 2.3 on `2^k` residues in bit-reversed order with root `2^e`: the backward
transform in natural order (the twiddle `ω^{−j}` is `ω^{K−j} = 2^{e(K−j)}`). -/
def backwardFFTRec (e : Nat) : (k : Nat) → (a : Array (AzFermat N)) → a.size = 2 ^ k →
    { b : Array (AzFermat N) // b.size = 2 ^ k }
  | 0, a, ha => ⟨a, ha⟩
  | k + 1, a, ha =>
    let lo : Array (AzFermat N) := Array.ofFn fun i : Fin (2 ^ k) =>
      a[i.val]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega)
    let hi : Array (AzFermat N) := Array.ofFn fun i : Fin (2 ^ k) =>
      a[2 ^ k + i.val]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega)
    let b := backwardFFTRec (2 * e) k lo Array.size_ofFn
    let c := backwardFFTRec (2 * e) k hi Array.size_ofFn
    ⟨Array.ofFn fun r : Fin (2 ^ (k + 1)) =>
      if hr : r.val < 2 ^ k then
        b.1[r.val]'(Nat.lt_of_lt_of_eq hr b.2.symm)
          + mulPow2 (e * (2 ^ (k + 1) - r.val)) (c.1[r.val]'(Nat.lt_of_lt_of_eq hr c.2.symm))
      else
        have hj : r.val - 2 ^ k < 2 ^ k := by have := r.isLt; have hK := pow_succ 2 k; omega
        b.1[r.val - 2 ^ k]'(Nat.lt_of_lt_of_eq hj b.2.symm)
          - mulPow2 (e * (2 ^ (k + 1) - (r.val - 2 ^ k)))
              (c.1[r.val - 2 ^ k]'(Nat.lt_of_lt_of_eq hj c.2.symm)),
     Array.size_ofFn⟩

/-- The forward transform (bit-reversed order) of an array of `2^k` residues. -/
def forwardFFT (e k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k) : Array (AzFermat N) :=
  (forwardFFTRec e k a ha).1

theorem forwardFFT_size (e k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k) :
    (forwardFFT e k a ha).size = 2 ^ k := (forwardFFTRec e k a ha).2

/-- The backward transform (natural order) of an array of `2^k` residues in bit-reversed
order. -/
def backwardFFT (e k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k) : Array (AzFermat N) :=
  (backwardFFTRec e k a ha).1

theorem backwardFFT_size (e k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k) :
    (backwardFFT e k a ha).size = 2 ^ k := (backwardFFTRec e k a ha).2

end Azurite.AzFermat
