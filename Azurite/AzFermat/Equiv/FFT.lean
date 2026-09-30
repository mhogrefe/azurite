/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFermat.FFT
import Azurite.AzFermat.Equiv.Basic

/-!
# `AzFermat.forwardFFT` and `backwardFFT` agree with `BZ.forwardFFT` and `BZ.backwardFFT`

Position by position through `toZMod`: with `ω = 2^e`,

  `toZMod (forwardFFT e k a ha)[r] = BZ.forwardFFT (2^e) k (toZModFun a) r`
  `toZMod (backwardFFT e k a ha)[r] = BZ.backwardFFT (2^e) k (toZModFun a) r`

where `toZModFun a i` is `toZMod a[i]` for `i < a.size` and `0` beyond.  Together with Theorems
2.1 and 2.2 (`BZ.forwardFFT_eq_dftNat`, `BZ.backwardFFT_eq_dftNat`) this makes the array
transforms the discrete Fourier transform and its inverse over `ZMod (2^N + 1)`.
-/

namespace Azurite.AzFermat

variable {N : Nat}

/-- An array of residues as a function `ℕ → ZMod (2^N + 1)` (zero beyond the array). -/
def toZModFun (a : Array (AzFermat N)) : ℕ → ZMod (2 ^ N + 1) :=
  fun i => if h : i < a.size then toZMod a[i] else 0

theorem toZModFun_of_lt (a : Array (AzFermat N)) {i : ℕ} (h : i < a.size) :
    toZModFun a i = toZMod a[i] := by
  rw [toZModFun, dite_eq_left h]

theorem toZModFun_of_le (a : Array (AzFermat N)) {i : ℕ} (h : a.size ≤ i) :
    toZModFun a i = 0 := by
  rw [toZModFun, dite_eq_right (Nat.not_lt.mpr h)]

variable [NeZero N]

theorem toZMod_forwardFFTRec (e : Nat) : ∀ (k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k)
    (r : Nat) (hr : r < 2 ^ k),
    toZMod ((forwardFFTRec e k a ha).1[r]'(Nat.lt_of_lt_of_eq hr (forwardFFTRec e k a ha).2.symm))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ e) k (toZModFun a) r := by
  intro k
  induction k generalizing e with
  | zero =>
    intro a ha r hr
    obtain rfl : r = 0 := by omega
    rw [BZ.forwardFFT, toZModFun_of_lt]
    rfl
  | succ k ih =>
    intro a ha r hr
    have hK : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    have hj : r / 2 < 2 ^ k := by omega
    -- the even and odd halves as functions
    have heven : toZModFun (Array.ofFn fun i : Fin (2 ^ k) =>
        a[2 * i.val]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega))
        = fun ℓ => toZModFun a (2 * ℓ) := by
      funext ℓ
      by_cases hℓ : ℓ < 2 ^ k
      · rw [toZModFun_of_lt _ (by rw [Array.size_ofFn]; exact hℓ), Array.getElem_ofFn,
          toZModFun_of_lt _ (by omega)]
      · rw [toZModFun_of_le _ (by rw [Array.size_ofFn]; omega), toZModFun_of_le _ (by omega)]
    have hodd : toZModFun (Array.ofFn fun i : Fin (2 ^ k) =>
        a[2 * i.val + 1]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega))
        = fun ℓ => toZModFun a (2 * ℓ + 1) := by
      funext ℓ
      by_cases hℓ : ℓ < 2 ^ k
      · rw [toZModFun_of_lt _ (by rw [Array.size_ofFn]; exact hℓ), Array.getElem_ofFn,
          toZModFun_of_lt _ (by omega)]
      · rw [toZModFun_of_le _ (by rw [Array.size_ofFn]; omega), toZModFun_of_le _ (by omega)]
    rw [BZ.forwardFFT]
    dsimp only
    simp only [forwardFFTRec, Array.getElem_ofFn]
    have hω2 : ((2 : ZMod (2 ^ N + 1)) ^ e) ^ 2 = 2 ^ (2 * e) := by rw [← pow_mul, mul_comm]
    split_ifs with hpar
    · rw [toZMod_add, toZMod_mulPow2, ih (2 * e) _ _ _ hj, ih (2 * e) _ _ _ hj, heven, hodd, hω2,
        ← pow_mul]
      ring
    · rw [toZMod_sub, toZMod_mulPow2, ih (2 * e) _ _ _ hj, ih (2 * e) _ _ _ hj, heven, hodd, hω2,
        ← pow_mul]
      ring

/-- **`forwardFFT` is Algorithm 2.2** (through `toZMod`). -/
theorem toZMod_forwardFFT (e k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k) (r : Nat)
    (hr : r < 2 ^ k) :
    toZMod ((forwardFFT e k a ha)[r]'(Nat.lt_of_lt_of_eq hr (forwardFFT_size e k a ha).symm))
      = BZ.forwardFFT ((2 : ZMod (2 ^ N + 1)) ^ e) k (toZModFun a) r :=
  toZMod_forwardFFTRec e k a ha r hr

theorem toZMod_backwardFFTRec (e : Nat) : ∀ (k : Nat) (a : Array (AzFermat N))
    (ha : a.size = 2 ^ k) (r : Nat) (hr : r < 2 ^ k),
    toZMod ((backwardFFTRec e k a ha).1[r]'(Nat.lt_of_lt_of_eq hr (backwardFFTRec e k a ha).2.symm))
      = BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ e) k (toZModFun a) r := by
  intro k
  induction k generalizing e with
  | zero =>
    intro a ha r hr
    obtain rfl : r = 0 := by omega
    rw [BZ.backwardFFT, toZModFun_of_lt]
    rfl
  | succ k ih =>
    intro a ha r hr
    have hK : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
    -- the lower and upper halves as functions
    have hlo : toZModFun (Array.ofFn fun i : Fin (2 ^ k) =>
        a[i.val]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega))
        = fun s => if s < 2 ^ k then toZModFun a s else 0 := by
      funext s
      by_cases hs : s < 2 ^ k
      · rw [toZModFun_of_lt _ (by rw [Array.size_ofFn]; exact hs), Array.getElem_ofFn,
          toZModFun_of_lt _ (by omega), ite_eq_left hs]
      · rw [toZModFun_of_le _ (by rw [Array.size_ofFn]; omega), ite_eq_right hs]
    have hhi : toZModFun (Array.ofFn fun i : Fin (2 ^ k) =>
        a[2 ^ k + i.val]'(by have := i.isLt; rw [ha]; have hK := pow_succ 2 k; omega))
        = fun s => if s < 2 ^ k then toZModFun a (2 ^ k + s) else 0 := by
      funext s
      by_cases hs : s < 2 ^ k
      · rw [toZModFun_of_lt _ (by rw [Array.size_ofFn]; exact hs), Array.getElem_ofFn,
          toZModFun_of_lt _ (by omega), ite_eq_left hs]
      · rw [toZModFun_of_le _ (by rw [Array.size_ofFn]; omega), ite_eq_right hs]
    -- `BZ.backwardFFT` on the halves only reads positions below `2^k`, so the `if` is harmless
    have hread : ∀ (f g : ℕ → ZMod (2 ^ N + 1)) (j : ℕ), j < 2 ^ k →
        (∀ s, s < 2 ^ k → f s = g s) →
        BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * e)) k f j
          = BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * e)) k g j :=
      fun f g j hj hfg => BZ.backwardFFT_congr k _ f g j hj hfg
    rw [BZ.backwardFFT]
    dsimp only
    simp only [backwardFFTRec, Array.getElem_ofFn]
    have hω2 : ((2 : ZMod (2 ^ N + 1)) ^ e) ^ 2 = 2 ^ (2 * e) := by rw [← pow_mul, mul_comm]
    have hlo' : ∀ j, j < 2 ^ k →
        BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * e)) k
          (fun s => if s < 2 ^ k then toZModFun a s else 0) j
        = BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * e)) k (toZModFun a) j :=
      fun j hj => hread _ _ j hj (fun s hs => by rw [ite_eq_left hs])
    have hhi' : ∀ j, j < 2 ^ k →
        BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * e)) k
          (fun s => if s < 2 ^ k then toZModFun a (2 ^ k + s) else 0) j
        = BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ (2 * e)) k (fun s => toZModFun a (2 ^ k + s)) j :=
      fun j hj => hread _ _ j hj (fun s hs => by rw [ite_eq_left hs])
    split_ifs with hlt
    · rw [toZMod_add, toZMod_mulPow2, ih (2 * e) _ _ _ hlt, ih (2 * e) _ _ _ hlt, hlo, hhi, hω2,
        ← pow_mul, hlo' r hlt, hhi' r hlt]
      ring
    · have hj : r - 2 ^ k < 2 ^ k := by omega
      rw [toZMod_sub, toZMod_mulPow2, ih (2 * e) _ _ _ hj, ih (2 * e) _ _ _ hj, hlo, hhi, hω2,
        ← pow_mul, hlo' _ hj, hhi' _ hj]
      ring

/-- **`backwardFFT` is Algorithm 2.3** (through `toZMod`). -/
theorem toZMod_backwardFFT (e k : Nat) (a : Array (AzFermat N)) (ha : a.size = 2 ^ k) (r : Nat)
    (hr : r < 2 ^ k) :
    toZMod ((backwardFFT e k a ha)[r]'(Nat.lt_of_lt_of_eq hr (backwardFFT_size e k a ha).symm))
      = BZ.backwardFFT ((2 : ZMod (2 ^ N + 1)) ^ e) k (toZModFun a) r :=
  toZMod_backwardFFTRec e k a ha r hr

end Azurite.AzFermat
