/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Add
import Azurite.AzNat.Sub
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Pow2
import Azurite.AzNat.Compare
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.Compare

/-!
# `AzFermat N` — integers modulo `2^N + 1`

The coefficient ring of the Schönhage–Strassen multiplication (Brent–Zimmermann §2.3.3,
`docs/fft_plan.md`).  An element is a canonical `AzNat` residue in `[0, 2^N]` (the top value
`2^N ≡ −1` is a legitimate residue, so the range has `2^N + 1` elements).  Everything the FFT
needs is cheap here:

* `add`, `sub`, `neg`: one `AzNat` addition or subtraction and one conditional correction by the
  modulus;
* `reduceSplit p`: a value `p = hi·2^N + lo` with `hi ≤ 2^N` reduced as `lo − hi`; `reduceAny`
  handles any `p` by recursing on `hi`;
* `mulWith mulFn`: the `AzNat` product by a caller-supplied multiplier (the Toom ladder, or a
  recursive FFT multiplication) followed by `reduceAny`, the total version of `reduceSplit`;
* `mulPow2 t` and `divPow2 t`: multiplication by `2^t` and by `2^{−t}` are a shift followed by
  `reduceSplit`, using `2^N ≡ −1` and `2^{2N} ≡ 1` to bring the exponent into `[0, N]`.  These
  are the FFT's twiddle multiplications (all roots of unity are powers of two) and the final
  division by `K θ^j`.

Correctness against `ZMod (2^N + 1)` is in `Equiv/Basic.lean` (`toZMod_add`, `toZMod_mulWith`,
`toZMod_mulPow2`, …).  The multiplier is a parameter so that the FFT multiplication, which sits
above the Toom ladder in `AzNat/Mul.lean`, can use the ladder for its pointwise products without
an import cycle.  Residues are `AzNat`s and the operations allocate fresh arrays; an in-place
limb-level version is a later optimisation (`docs/fft_plan.md`).
-/

namespace Azurite

/-- Integers modulo `2^N + 1`, as a canonical `AzNat` residue in `[0, 2^N]`. -/
structure AzFermat (N : Nat) where
  /-- The canonical residue, in `[0, 2^N]`. -/
  val : AzNat
  /-- Canonicity. -/
  isLe : val.toNat ≤ 2 ^ N
  deriving DecidableEq

namespace AzFermat

variable {N : Nat}

@[ext] theorem ext {a b : AzFermat N} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- The modulus `2^N + 1` as an `AzNat`. -/
def modulus (N : Nat) : AzNat := AzNat.pow2 N + 1

theorem toNat_modulus : (modulus N).toNat = 2 ^ N + 1 := by
  rw [modulus, AzNat.toNat_add, AzNat.toNat_pow2, AzNat.toNat_one]

instance : Zero (AzFermat N) := ⟨⟨0, by rw [AzNat.toNat_zero]; exact Nat.zero_le _⟩⟩
instance : Inhabited (AzFermat N) := ⟨0⟩

@[simp] theorem val_zero : (0 : AzFermat N).val = 0 := rfl

/-- Addition: the sum, less the modulus when it exceeds `2^N`. -/
def add (a b : AzFermat N) : AzFermat N :=
  if h : a.val + b.val ≤ AzNat.pow2 N then
    ⟨a.val + b.val, by rwa [AzNat.le_iff_toNat_le, AzNat.toNat_pow2] at h⟩
  else
    ⟨a.val + b.val - modulus N, by
      rw [AzNat.le_iff_toNat_le, AzNat.toNat_pow2, AzNat.toNat_add] at h
      have ha := a.isLe
      have hb := b.isLe
      rw [AzNat.toNat_sub, toNat_modulus, AzNat.toNat_add]
      omega⟩

/-- Subtraction: the difference, plus the modulus when it would be negative. -/
def sub (a b : AzFermat N) : AzFermat N :=
  if h : b.val ≤ a.val then
    ⟨a.val - b.val, by rw [AzNat.toNat_sub]; exact le_trans (Nat.sub_le _ _) a.isLe⟩
  else
    ⟨a.val + modulus N - b.val, by
      rw [AzNat.le_iff_toNat_le] at h
      have ha := a.isLe
      have hb := b.isLe
      rw [AzNat.toNat_sub, AzNat.toNat_add, toNat_modulus]
      omega⟩

/-- Negation. -/
def neg (a : AzFermat N) : AzFermat N := sub 0 a

instance : Add (AzFermat N) := ⟨add⟩
instance : Sub (AzFermat N) := ⟨sub⟩
instance : Neg (AzFermat N) := ⟨neg⟩

/-- Reduce a value `p = hi · 2^N + lo` with `hi ≤ 2^N` (a product of two residues, or a residue
shifted by at most `N` bits): `p ≡ lo − hi`. -/
def reduceSplit (p : AzNat) (hp : p.toNat / 2 ^ N ≤ 2 ^ N) : AzFermat N :=
  sub ⟨p.modPow2 N, by
        rw [AzNat.toNat_modPow2]
        exact Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos N))⟩
      ⟨p >>> N, by rwa [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]⟩

/-- Reduce any `AzNat`: by `reduceSplit` when its high part `p / 2^N` is at most `2^N` (always
the case for a product of two residues), otherwise `p = hi · 2^N + lo ≡ lo − hi` with `hi`
reduced recursively.  The test costs one comparison of the high part. -/
def reduceAny [NeZero N] (p : AzNat) : AzFermat N :=
  if h : p >>> N ≤ AzNat.pow2 N then
    reduceSplit p (by
      rwa [AzNat.le_iff_toNat_le, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow,
        AzNat.toNat_pow2] at h)
  else
    sub ⟨p.modPow2 N, by
          rw [AzNat.toNat_modPow2]
          exact Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos N))⟩
        (reduceAny (p >>> N))
termination_by p.toNat
decreasing_by
  rw [AzNat.le_iff_toNat_le, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow,
    AzNat.toNat_pow2] at h
  rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
  have hN : 2 ≤ 2 ^ N := by
    have := NeZero.pos N
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) this
  have hpos : 0 < p.toNat := by
    rcases Nat.eq_zero_or_pos p.toNat with h0 | h0
    · rw [h0, Nat.zero_div] at h; omega
    · exact h0
  exact Nat.div_lt_self hpos (by omega)

/-- Reduce an arbitrary `AzNat` modulo `2^N + 1`. -/
def ofAzNat (N : Nat) [NeZero N] (n : AzNat) : AzFermat N := reduceAny n

/-- Multiplication with the multiplier `mulFn` for the `AzNat` product of the residues. -/
def mulWith [NeZero N] (mulFn : AzNat → AzNat → AzNat) (a b : AzFermat N) : AzFermat N :=
  reduceAny (mulFn a.val b.val)

/-- `x · 2^t` for `t ≤ N`: a shift and a `reduceSplit`. -/
def mulPow2Le (t : Nat) (ht : t ≤ N) (a : AzFermat N) : AzFermat N :=
  reduceSplit (a.val <<< t) (by
    rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
    exact Nat.div_le_of_le_mul
      (Nat.mul_le_mul a.isLe (Nat.pow_le_pow_right (by norm_num) ht)))

/-- `x · 2^t` for any `t`, using `2^{2N} ≡ 1` and `2^N ≡ −1`. -/
def mulPow2 [NeZero N] (t : Nat) (a : AzFermat N) : AzFermat N :=
  if ht : t % (2 * N) ≤ N then
    mulPow2Le (t % (2 * N)) ht a
  else
    neg (mulPow2Le (t % (2 * N) - N) (by
      have := Nat.mod_lt t (Nat.mul_pos two_pos (NeZero.pos N))
      omega) a)

/-- `x · 2^{−t} = x · 2^{2N − (t mod 2N)}`: division by a power of two. -/
def divPow2 [NeZero N] (t : Nat) (a : AzFermat N) : AzFermat N :=
  mulPow2 (2 * N - t % (2 * N)) a

end AzFermat

end Azurite
