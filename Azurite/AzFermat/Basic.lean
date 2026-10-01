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
import Azurite.AzNat.Size
import Azurite.AzNat.Equiv.Size

/-!
# `AzFermat N` — integers modulo `2^N + 1`

The coefficient ring of the Schönhage–Strassen multiplication (Brent–Zimmermann §2.3.3,
`docs/fft_plan.md`).  An element is a canonical `AzNat` residue in `[0, 2^N]` (the top value
`2^N ≡ −1` is a legitimate residue, so the range has `2^N + 1` elements).  Everything the FFT
needs is cheap here:

* `add`, `sub`, `neg`: one `AzNat` addition or subtraction and one conditional correction by the
  modulus;
* `reduceSplit negate p`: a value `p = hi·2^N + lo` with `hi ≤ 2^N` reduced as `lo − hi` (or
  `hi − lo` for `−p`); when `64 ∣ N` the parts are limb slices (`lowPart`, `highPart`);
  `reduceAny` handles any `p` by recursing on `hi`;
* `mulWith mulFn`: the `AzNat` product by a caller-supplied multiplier (the Toom ladder, or a
  recursive FFT multiplication) followed by `reduceAny`, the total version of `reduceSplit`;
* `mulPow2 t` and `divPow2 t`: multiplication by `2^t` and by `2^{−t}` are a shift followed by
  `reduceSplit`, using `2^N ≡ −1` and `2^{2N} ≡ 1` to bring the exponent into `[0, N]`.  These
  are the FFT's twiddle multiplications (all roots of unity are powers of two) and the final
  division by `K θ^j`; `butterfly t b c = (b + 2^t c, b − 2^t c)` is the transform's step, with
  the sign of `2^t` for `N < t mod 2N` handled by swapping the outputs.

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

/-- `s ≤ 2^N`, decided from the bit size and the power-of-two test without building `2^N`:
`s < 2^N` iff `s.size ≤ N`, and `s = 2^N` iff `s.size = N + 1` and `s` is a power of two. -/
theorem toNat_le_two_pow_of_size (s : AzNat) (h : s.size ≤ N) : s.toNat ≤ 2 ^ N :=
  Nat.le_of_lt (Nat.size_le.mp (by rwa [AzNat.size_toNat]))

theorem toNat_eq_two_pow_of_size (s : AzNat) (h1 : s.size = N + 1) (h2 : s.isPowerOfTwo = true) :
    s.toNat = 2 ^ N := by
  obtain ⟨k, hk⟩ := (AzNat.isPowerOfTwo_iff s).mp h2
  have : s.toNat.size = N + 1 := by rw [AzNat.size_toNat, h1]
  rw [hk, Nat.size_pow] at this
  rw [hk]
  congr 1
  omega

theorem two_pow_lt_toNat_of_not (s : AzNat) (h1 : ¬ s.size ≤ N)
    (h2 : ¬ (s.size = N + 1 ∧ s.isPowerOfTwo = true)) : 2 ^ N < s.toNat := by
  have hge : 2 ^ N ≤ s.toNat := by
    have := mt Nat.size_le.mpr (by rwa [AzNat.size_toNat] : ¬ s.toNat.size ≤ N)
    omega
  rcases Nat.lt_or_ge (2 ^ N) s.toNat with hlt | hle
  · exact hlt
  · exfalso
    have heq : s.toNat = 2 ^ N := by omega
    apply h2
    refine ⟨?_, (AzNat.isPowerOfTwo_iff s).mpr ⟨N, heq⟩⟩
    rw [← AzNat.size_toNat, heq, Nat.size_pow]

/-- Addition: the sum, less the modulus when it exceeds `2^N` (the comparison reads the bit
size, so no `2^N` is built). -/
def add (a b : AzFermat N) : AzFermat N :=
  let s := a.val + b.val
  if h : s.size ≤ N then ⟨s, toNat_le_two_pow_of_size s h⟩
  else if h2 : s.size = N + 1 ∧ s.isPowerOfTwo = true then
    ⟨s, le_of_eq (toNat_eq_two_pow_of_size s h2.1 h2.2)⟩
  else
    -- `s − (2^N + 1)` as `(s − 2^N) − 1`: no modulus to build
    ⟨(s - AzNat.pow2 N).subUInt64 1, by
      have ha := a.isLe
      have hb := b.isLe
      have hs : s.toNat = a.val.toNat + b.val.toNat := AzNat.toNat_add _ _
      have := two_pow_lt_toNat_of_not s h h2
      rw [AzNat.toNat_subUInt64, AzNat.toNat_sub, AzNat.toNat_pow2, UInt64.toNat_one]
      omega⟩

/-- Subtraction: the difference, plus the modulus when it would be negative (as
`(a + 2^N − b) + 1`: no modulus to build). -/
def sub (a b : AzFermat N) : AzFermat N :=
  if h : b.val ≤ a.val then
    ⟨a.val - b.val, by rw [AzNat.toNat_sub]; exact le_trans (Nat.sub_le _ _) a.isLe⟩
  else
    ⟨(a.val + AzNat.pow2 N - b.val).addUInt64 1, by
      rw [AzNat.le_iff_toNat_le] at h
      have ha := a.isLe
      have hb := b.isLe
      rw [AzNat.toNat_addUInt64, AzNat.toNat_sub, AzNat.toNat_add, AzNat.toNat_pow2,
        UInt64.toNat_one]
      omega⟩

/-- Negation. -/
def neg (a : AzFermat N) : AzFermat N := sub 0 a

instance : Add (AzFermat N) := ⟨add⟩
instance : Sub (AzFermat N) := ⟨sub⟩
instance : Neg (AzFermat N) := ⟨neg⟩

/-- The value of a limb slice. -/
theorem toNatLimbsList_extract' (a : Array UInt64) (lo n : Nat) :
    AzNat.toNatLimbsList (a.extract lo (lo + n)).toList
      = AzNat.toNatLimbsList ((a.toList.drop lo).take n) := by
  rw [Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]

/-- The low `N` bits of `p`, as a residue. -/
def lowPart (p : AzNat) : AzFermat N :=
  if h64 : N % 64 = 0 then
    -- a limb slice: no arithmetic pass
    ⟨AzNat.ofLimbs (p.limbs.extract 0 (0 + N / 64)), by
      rw [AzNat.toNat_ofLimbs, toNatLimbsList_extract', List.drop_zero, AzNat.toNatLimbsList_take,
        show 64 * (N / 64) = N by omega]
      exact Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos N))⟩
  else
    ⟨p.modPow2 N, by
      rw [AzNat.toNat_modPow2]
      exact Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos N))⟩

/-- The high part `p / 2^N`, as a residue (given `p / 2^N ≤ 2^N`). -/
def highPart (p : AzNat) (hp : p.toNat / 2 ^ N ≤ 2 ^ N) : AzFermat N :=
  if h64 : N % 64 = 0 then
    ⟨AzNat.ofLimbs (p.limbs.extract (N / 64) (N / 64 + p.limbs.size)), by
      rw [AzNat.toNat_ofLimbs, toNatLimbsList_extract',
        List.take_of_length_le (by rw [List.length_drop, Array.length_toList]; omega),
        AzNat.toNatLimbsList_drop, show 64 * (N / 64) = N by omega]
      exact hp⟩
  else
    ⟨p >>> N, by rwa [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]⟩

/-- Reduce a value `p = hi · 2^N + lo` with `hi ≤ 2^N` (a product of two residues, or a residue
shifted by at most `N` bits): `p ≡ lo − hi`, or `hi − lo ≡ −p` when `negate` is set (this folds
the sign of a twiddle `2^t` with `N < t < 2N` into the same subtraction).  When `64 ∣ N` the two
parts are limb slices and the only arithmetic pass is the subtraction. -/
def reduceSplit (negate : Bool) (p : AzNat) (hp : p.toNat / 2 ^ N ≤ 2 ^ N) : AzFermat N :=
  if negate then sub (highPart p hp) (lowPart p) else sub (lowPart p) (highPart p hp)

/-- Reduce any `AzNat`: by `reduceSplit` when its high part `p / 2^N` is at most `2^N` (always
the case for a product of two residues), otherwise `p = hi · 2^N + lo ≡ lo − hi` with `hi`
reduced recursively.  The test costs one comparison of the high part. -/
def reduceAny [NeZero N] (p : AzNat) : AzFermat N :=
  if h : p >>> N ≤ AzNat.pow2 N then
    reduceSplit false p (by
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

/-- `x · 2^t` for `t ≤ N` (`negate = false`), or `−x · 2^t = x · 2^{N+t}` (`negate = true`): a shift
and a `reduceSplit`. -/
def mulPow2Le (t : Nat) (ht : t ≤ N) (negate : Bool) (a : AzFermat N) : AzFermat N :=
  reduceSplit negate (a.val <<< t) (by
    rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
    exact Nat.div_le_of_le_mul
      (Nat.mul_le_mul a.isLe (Nat.pow_le_pow_right (by norm_num) ht)))

/-- `x · 2^t` for any `t`, using `2^{2N} ≡ 1` and `2^N ≡ −1`; the identity is a fast path and
the sign of `2^t` for `N < t mod 2N < 2N` is folded into the reduction. -/
def mulPow2 [NeZero N] (t : Nat) (a : AzFermat N) : AzFermat N :=
  let t' := t % (2 * N)
  if t' = 0 then a
  else if ht : t' ≤ N then mulPow2Le t' ht false a
  else mulPow2Le (t' - N) (by
    have := Nat.mod_lt t (Nat.mul_pos two_pos (NeZero.pos N))
    omega) true a

/-- `x · 2^t` as a magnitude and a sign: `(m, false)` with `m = x · 2^t`, or `(m, true)` with
`m = −x · 2^t` (when `N < t mod 2N`).  The sign is left to the caller, so that a butterfly can
swap its two outputs instead of negating. -/
def mulPow2Split [NeZero N] (t : Nat) (a : AzFermat N) : AzFermat N × Bool :=
  let t' := t % (2 * N)
  if t' = 0 then (a, false)
  else if ht : t' ≤ N then (mulPow2Le t' ht false a, false)
  else (mulPow2Le (t' - N) (by
    have := Nat.mod_lt t (Nat.mul_pos two_pos (NeZero.pos N))
    omega) false a, true)

/-- **The butterfly** `(b + 2^t c, b − 2^t c)`, with the sign of `2^t` (for `N < t mod 2N`)
handled by swapping the outputs rather than negating. -/
def butterfly [NeZero N] (t : Nat) (b c : AzFermat N) : AzFermat N × AzFermat N :=
  let m := mulPow2Split t c
  if m.2 then (sub b m.1, add b m.1) else (add b m.1, sub b m.1)

/-- `x · 2^{−t} = x · 2^{2N − (t mod 2N)}`: division by a power of two. -/
def divPow2 [NeZero N] (t : Nat) (a : AzFermat N) : AzFermat N :=
  mulPow2 (2 * N - t % (2 * N)) a

end AzFermat

end Azurite
