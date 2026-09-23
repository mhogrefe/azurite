/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.Schoolbook
import Azurite.AzNat.Mul.Karatsuba
import Azurite.AzNat.Mul.ToomCook3

namespace Azurite.AzNat

-- ── Limb-level dispatcher and AzNat wrapper ─────────────────────────────────

/-- Default minimum-length threshold for Karatsuba (in 64-bit limbs).  Tuned
    via `Azurite.AzNat.Tune.tuneAzNatDispatch2D`: the 2-D `(minThreshold, k)`
    sweep over an unfiltered random distribution favors a low threshold
    combined with the ratio criterion below. -/
def mulDispatchThreshold : Nat := 16

/-- Default ratio threshold (numerator/denominator).  Karatsuba is used when
    `lenMin / lenMax ≥ mulDispatchKNum / mulDispatchKDen`, i.e.
    `mulDispatchKDen · lenMin ≥ mulDispatchKNum · lenMax`.

    Tuner result: `k ≈ 1/4` (≈ 22% faster than the old `1/2`). -/
def mulDispatchKNum : Nat := 1
def mulDispatchKDen : Nat := 4

/-- Default cutoff (in 64-bit limbs) for switching Karatsuba → Toom-Cook 3.
    Tuned via `tune_aznat_mul_toomcook3`: at `lenMax ≥ 256` limbs (≈ 16384
    bits per operand), Toom-Cook 3 starts winning over Karatsuba.  Below
    256, the sweep is flat (no penalty for staying with Karatsuba);
    above 384, forcing Karatsuba on large pairs becomes measurably slower. -/
def mulDispatchToomCook3Cutoff : Nat := 256

/-- Parametrized limb-level dispatcher (used directly by `Tune`).  Three-way
    dispatch:

    * If `lenMin < minThreshold` OR `kDen · lenMin < kNum · lenMax`
      (too-short or too-unbalanced operands): `schoolbookMulLimbs` on the
      original (unpadded) slices.
    * Else if `lenMax < toomCook3Cutoff` (balanced but not too big):
      `karatsubaMulLimbs` on the lenMax-padded slices.
    * Else (balanced and big): `toomCook3MulLimbs` on the same padded slices. -/
def mulLimbsParam (minThreshold kNum kDen toomCook3Cutoff : Nat)
    (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  let lenMax := max lenA lenB
  let lenMin := min lenA lenB
  if minThreshold ≤ lenMin && kDen * lenMin ≥ kNum * lenMax then
    -- Balanced: extract slices, pad to lenMax, then pick Karatsuba or Toom-Cook 3.
    let aSlice : Array UInt64 := a.extract loA (loA + lenA)
    let bSlice : Array UInt64 := b.extract loB (loB + lenB)
    let aPadded : Array UInt64 := aSlice ++ Array.replicate (lenMax - lenA) 0
    let bPadded : Array UInt64 := bSlice ++ Array.replicate (lenMax - lenB) 0
    have hA' : 0 + lenMax ≤ aPadded.size := by
      show 0 + lenMax ≤ (aSlice ++ Array.replicate (lenMax - lenA) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have hSlice : aSlice.size = lenA := by
        show (a.extract loA (loA + lenA)).size = lenA
        rw [Array.size_extract]; omega
      have hMax : lenA ≤ lenMax := Nat.le_max_left _ _
      omega
    have hB' : 0 + lenMax ≤ bPadded.size := by
      show 0 + lenMax ≤ (bSlice ++ Array.replicate (lenMax - lenB) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have hSlice : bSlice.size = lenB := by
        show (b.extract loB (loB + lenB)).size = lenB
        rw [Array.size_extract]; omega
      have hMax : lenB ≤ lenMax := Nat.le_max_right _ _
      omega
    if toomCook3Cutoff ≤ lenMax then
      -- Toom-Cook 3 with cutoff `toomCook3Cutoff` for self-recursion, falling
      -- back to Karatsuba (with its own tuned schoolbook threshold) below.
      toomCook3MulLimbs toomCook3Cutoff minThreshold aPadded bPadded 0 0 lenMax hA' hB'
    else
      karatsubaMulLimbs minThreshold aPadded bPadded 0 0 lenMax hA' hB'
  else
    schoolbookMulLimbs a b loA lenA loB lenB hA hB

/-- Limb-level multiplication using the default dispatch parameters. -/
def mulLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  mulLimbsParam mulDispatchThreshold mulDispatchKNum mulDispatchKDen
    mulDispatchToomCook3Cutoff a b loA lenA loB lenB hA hB

/-- Lower bound on `mulLimbsParam`'s output: `lenA + lenB ≤ size`.
    Schoolbook gives exactly `lenA + lenB`; Karatsuba/Toom give
    `2 * max lenA lenB` which is also `≥ lenA + lenB`. -/
theorem mulLimbsParam_size_ge (minThreshold kNum kDen toomCook3Cutoff : Nat)
    (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    lenA + lenB ≤ (mulLimbsParam minThreshold kNum kDen toomCook3Cutoff
      a b loA lenA loB lenB hA hB).size := by
  unfold mulLimbsParam
  simp only
  split_ifs
  · rw [toomCook3MulLimbs_size]
    have hmax_a := Nat.le_max_left lenA lenB
    have hmax_b := Nat.le_max_right lenA lenB
    omega
  · rw [karatsubaMulLimbs_size]
    have hmax_a := Nat.le_max_left lenA lenB
    have hmax_b := Nat.le_max_right lenA lenB
    omega
  · rw [schoolbookMulLimbs_size]

/-- Lower bound: `mulLimbs`'s output has at least `lenA + lenB` limbs. -/
theorem mulLimbs_size_ge (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    lenA + lenB ≤ (mulLimbs a b loA lenA loB lenB hA hB).size :=
  mulLimbsParam_size_ge _ _ _ _ a b loA lenA loB lenB hA hB

/-- AzNat wrapper for `mulLimbsParam`; lets the tuner sweep the dispatch
    parameters. -/
def mulDispatchParam (minThreshold kNum kDen toomCook3Cutoff : Nat) (a b : AzNat) : AzNat :=
  ofLimbs (mulLimbsParam minThreshold kNum kDen toomCook3Cutoff
    a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Multiplication of two `AzNat`s.  Dispatches between schoolbook and
    Karatsuba via `mulLimbs`. -/
def mul (a b : AzNat) : AzNat :=
  ofLimbs (mulLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

instance : Mul AzNat := ⟨mul⟩

-- ── Always-one-algorithm wrappers (for benchmarking) ────────────────────────

/-- Multiplication of `AzNat`s forced to use schoolbook.  For benchmarking;
    callers should use `*` (or `mul`) for the dispatched best-of-both. -/
def mulSchoolbook (a b : AzNat) : AzNat :=
  ofLimbs (schoolbookMulLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Multiplication of `AzNat`s forced to use Karatsuba.  Pads the shorter
    operand with high zero limbs.  For benchmarking; callers should use `*`
    (or `mul`) for the dispatched best-of-both. -/
def mulKaratsuba (threshold : Nat) (a b : AzNat) : AzNat :=
  if a.limbs.size = 0 ∨ b.limbs.size = 0 then 0
  else
    let n := max a.limbs.size b.limbs.size
    let aPadded : Array UInt64 := a.limbs ++ Array.replicate (n - a.limbs.size) 0
    let bPadded : Array UInt64 := b.limbs ++ Array.replicate (n - b.limbs.size) 0
    have hA : 0 + n ≤ aPadded.size := by
      show 0 + n ≤ (a.limbs ++ Array.replicate (n - a.limbs.size) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have h := Nat.le_max_left a.limbs.size b.limbs.size
      omega
    have hB : 0 + n ≤ bPadded.size := by
      show 0 + n ≤ (b.limbs ++ Array.replicate (n - b.limbs.size) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have h := Nat.le_max_right a.limbs.size b.limbs.size
      omega
    ofLimbs (karatsubaMulLimbs threshold aPadded bPadded 0 0 n hA hB)

/-- Multiplication of `AzNat`s forced to use Toom-Cook 3-way.  Pads the
    shorter operand with high zero limbs.  For benchmarking; the
    `toomThreshold` is the recursion fallback to Karatsuba (set to ≥ 3),
    and `karaThreshold` is forwarded to Karatsuba's schoolbook fallback. -/
def mulToomCook3 (toomThreshold karaThreshold : Nat) (a b : AzNat) : AzNat :=
  if a.limbs.size = 0 ∨ b.limbs.size = 0 then 0
  else
    let n := max a.limbs.size b.limbs.size
    let aPadded : Array UInt64 := a.limbs ++ Array.replicate (n - a.limbs.size) 0
    let bPadded : Array UInt64 := b.limbs ++ Array.replicate (n - b.limbs.size) 0
    have hA : 0 + n ≤ aPadded.size := by
      show 0 + n ≤ (a.limbs ++ Array.replicate (n - a.limbs.size) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have h := Nat.le_max_left a.limbs.size b.limbs.size
      omega
    have hB : 0 + n ≤ bPadded.size := by
      show 0 + n ≤ (b.limbs ++ Array.replicate (n - b.limbs.size) (0 : UInt64)).size
      rw [Array.size_append, Array.size_replicate]
      have h := Nat.le_max_right a.limbs.size b.limbs.size
      omega
    ofLimbs (toomCook3MulLimbs toomThreshold karaThreshold aPadded bPadded 0 0 n hA hB)

end Azurite.AzNat
