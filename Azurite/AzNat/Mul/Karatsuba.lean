/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Add
import Azurite.AzNat.Sub
import Azurite.AzNat.Mul.Schoolbook

namespace Azurite.AzNat

-- ── absSubLimbsKM stages ────────────────────────────────────────────────────

namespace absSubLimbsKM

/-- Recursive helper for `copySub`.  Iterates `i` from the input value
    up to `k`, setting `r[i]` to the limb value computed from `a`:

    * `i < m`: `r[i] := a[loA+i] − a[loA+k+i] − borrow`,
    * `i ≥ m`: `r[i] := a[loA+i] − borrow` (subtrahend is zero, only
      borrow propagates).

    The buffer `r` is pre-allocated to size `k` and mutated in place. -/
def copySub.go (a : Array UInt64) (loA k m i : Nat) (borrow : Bool)
    (r : Array UInt64) (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k)
    (h_r : r.size = k) (_h_i : i ≤ k) :
    Array UInt64 × Bool :=
  if h : i < k then
    have h_iA : loA + i < a.size := by omega
    have h_i_r : i < r.size := by rw [h_r]; exact h
    let x := a[loA + i]
    if hm : i < m then
      have h_iB : loA + k + i < a.size := by omega
      let y := a[loA + k + i]
      let swb := UInt64.subWithBorrow x y borrow
      copySub.go a loA k m (i + 1) swb.2 (r.set i swb.1 h_i_r) h_a h_le
        (by rw [Array.size_set, h_r]) (by omega)
    else
      let swb := UInt64.subWithBorrow x 0 borrow
      copySub.go a loA k m (i + 1) swb.2 (r.set i swb.1 h_i_r) h_a h_le
        (by rw [Array.size_set, h_r]) (by omega)
  else
    (r, borrow)
  termination_by k - i

/-- Size preservation of `copySub.go`: the buffer stays at size `k`. -/
theorem copySub.go_size (a : Array UInt64) (loA k m i : Nat) (borrow : Bool)
    (r : Array UInt64) (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k)
    (h_r : r.size = k) (h_i : i ≤ k) :
    (copySub.go a loA k m i borrow r h_a h_le h_r h_i).1.size = k := by
  induction h_sub : k - i generalizing r i borrow with
  | zero =>
    have h_ge : k ≤ i := by omega
    rw [copySub.go]
    simp [Nat.not_lt.mpr h_ge, h_r]
  | succ n ih =>
    have h_lt : i < k := by omega
    rw [copySub.go]
    simp only [h_lt, ↓reduceDIte]
    have h_rec : k - (i + 1) = n := by omega
    by_cases hm : i < m
    · simp only [hm, ↓reduceDIte]
      rw [ih _ _ _ (by rw [Array.size_set, h_r]) (by omega) h_rec]
    · simp only [hm, ↓reduceDIte]
      rw [ih _ _ _ (by rw [Array.size_set, h_r]) (by omega) h_rec]

/-- Fused stage 1+2: compute `a[loA..loA+k] - a[loA+k..loA+k+m]` (the
    subtrahend zero-extended to `k` limbs) into a fresh `k`-limb buffer
    in a single pass, returning `(d, borrow)` with `borrow = true` ⇔
    `a[loA..loA+k] < a[loA+k..loA+k+m]`.  This replaces the previous
    two-stage `copy` + `subPart` flow, eliminating the wasted copy of
    the low `m` limbs of `a[loA..loA+k]` (which were overwritten
    immediately by the subtraction). -/
def copySub (a : Array UInt64) (loA k m : Nat)
    (h_a : loA + k + m ≤ a.size) (h_le : m ≤ k)
    (_h_kpos : 0 < k) (_h_mpos : 0 < m) :
    { d : Array UInt64 // d.size = k } × Bool :=
  let r₀ : Array UInt64 := Array.replicate k 0
  have hr₀_sz : r₀.size = k := Array.size_replicate
  let result := copySub.go a loA k m 0 false r₀ h_a h_le hr₀_sz (Nat.zero_le _)
  (⟨result.1, copySub.go_size a loA k m 0 false r₀ h_a h_le hr₀_sz (Nat.zero_le _)⟩,
   result.2)

/-- Stage 3: negate a length-`k` buffer (compute `β^k − toNat d`). -/
def negPart (d : Array UInt64) (k : Nat) (hd : d.size = k) :
    { n : Array UInt64 // n.size = k } :=
  let zero : Array UInt64 := Array.replicate k 0
  have hzero_sz : zero.size = k := Array.size_replicate
  have hzero : 0 + k ≤ zero.size := by rw [hzero_sz]; omega
  have hd' : 0 + k ≤ d.size := by rw [hd]; omega
  let r := subSameLengthLimbs zero d 0 0 k hzero hd'
  ⟨r.1, by
    show (subSameLengthLimbs zero d 0 0 k hzero hd').1.size = k
    rw [subSameLengthLimbs_size, hzero_sz]⟩

end absSubLimbsKM

/--
Compute `|A₀ − A₁|` where `A₀ = a[loA : loA + k]` and `A₁ = a[loA + k : loA + k + m]`
with `m ≤ k`. The result is a fresh `k`-limb array along with a sign bit:
`true` iff `A₀ ≥ A₁`.
-/
def absSubLimbsKM (a : Array UInt64) (loA k m : Nat)
    (hA : loA + k + m ≤ a.size) (h_le : m ≤ k) (h_kpos : 0 < k) (h_mpos : 0 < m) :
    { d : Array UInt64 // d.size = k } × Bool :=
  let cs := absSubLimbsKM.copySub a loA k m hA h_le h_kpos h_mpos
  if cs.2 then
    (absSubLimbsKM.negPart cs.1.1 k cs.1.2, false)
  else
    (cs.1, true)

-- ── karatsubaMulLimbsRec stages ─────────────────────────────────────────────

namespace karatsubaMulLimbsRec

/-- Assemble `C₀ + (C₀ + C₁ ∓ C₂) · β^k + C₁ · β^(2k)` in place in the buffer `C₀ ++ C₁`
    (`−` when `sameSign`, `+` otherwise), in two passes over the middle region `[k, 2 len)`:
    one fused three-input pass adds `C₀ + C₁` (the `2m`-limb overlap by
    `add3SameLengthLimbs.go`, the remaining `2k − 2m` limbs of `C₀` by
    `addSameLengthLimbs.go`, then the two carry bits), and `subGeqLimbs` / `addGeqLimbs`
    applies `C₂`.  Carries out of the top limb are dropped: every step is exact modulo
    `β^(2 len)`, and the final value `A · B` lies below that bound (`assemble_toNat`). -/
def assemble (k m len : Nat) (C₀ C₁ C₂ : Array UInt64) (sameSign : Bool)
    (hC₀ : C₀.size = 2 * k) (hC₁ : C₁.size = 2 * m) (hC₂ : C₂.size = 2 * k)
    (hkm : k + m = len) (h_kpos : 0 < k) (_h_mpos : 0 < m) (h_le : m ≤ k)
    (h_k2m : k ≤ 2 * m) :
    { c : Array UInt64 // c.size = 2 * len } :=
  let acc₀ := C₀ ++ C₁
  have hacc₀ : acc₀.size = 2 * len := by
    show (C₀ ++ C₁).size = 2 * len
    rw [Array.size_append, hC₀, hC₁]; omega
  -- Pass 1a: the `2m`-limb overlap of `C₀` and `C₁`, fused.
  have h1A : k + 2 * m ≤ acc₀.size := by rw [hacc₀]; omega
  have h1B : 0 + 2 * m ≤ C₀.size := by rw [hC₀]; omega
  have h1C : 0 + 2 * m ≤ C₁.size := by rw [hC₁]; omega
  let r₁ := add3SameLengthLimbs.go C₀ C₁ k 0 0 (2 * m) acc₀ 0 false false h1A h1B h1C
  have hr₁ : r₁.1.size = 2 * len := by
    show (add3SameLengthLimbs.go C₀ C₁ k 0 0 (2 * m) acc₀ 0 false false h1A h1B h1C).1.size
      = 2 * len
    rw [add3SameLengthLimbs.go_size, hacc₀]
  -- Pass 1b: the remaining `2k − 2m` limbs of `C₀`, continuing the first carry.
  have h2A : (k + 2 * m) + (2 * k - 2 * m) ≤ r₁.1.size := by rw [hr₁]; omega
  have h2B : 2 * m + (2 * k - 2 * m) ≤ C₀.size := by rw [hC₀]; omega
  let r₂ := addSameLengthLimbs.go C₀ (k + 2 * m) (2 * m) (2 * k - 2 * m) r₁.1 0 r₁.2.1 h2A h2B
  have hr₂ : r₂.1.size = 2 * len := by
    show (addSameLengthLimbs.go C₀ (k + 2 * m) (2 * m) (2 * k - 2 * m) r₁.1 0 r₁.2.1
      h2A h2B).1.size = 2 * len
    rw [addSameLengthLimbs.go_size, hr₁]
  -- Pass 1c, 1d: the second carry of pass 1a and the carry of pass 1b (early-exit loops).
  have h3lo : k + 2 * m ≤ 2 * len := by omega
  have h3hi : 2 * len ≤ r₂.1.size := by rw [hr₂]
  let r₃ := addLimb r₂.1 (k + 2 * m) (2 * len) (if r₁.2.2 then 1 else 0) h3lo h3hi
  have hr₃ : r₃.1.size = 2 * len := by
    show (addLimb r₂.1 (k + 2 * m) (2 * len) (if r₁.2.2 then 1 else 0) h3lo h3hi).1.size
      = 2 * len
    rw [addLimb_size, hr₂]
  have h4lo : 3 * k ≤ 2 * len := by omega
  have h4hi : 2 * len ≤ r₃.1.size := by rw [hr₃]
  let r₄ := addLimb r₃.1 (3 * k) (2 * len) (if r₂.2 then 1 else 0) h4lo h4hi
  have hr₄ : r₄.1.size = 2 * len := by
    show (addLimb r₃.1 (3 * k) (2 * len) (if r₂.2 then 1 else 0) h4lo h4hi).1.size = 2 * len
    rw [addLimb_size, hr₃]
  -- Pass 2: `∓ C₂`.
  have h5A : k + (2 * len - k) ≤ r₄.1.size := by rw [hr₄]; omega
  have h5B : 0 + 2 * k ≤ C₂.size := by rw [hC₂]; omega
  have h5ge : 2 * k ≤ 2 * len - k := by omega
  have h5posA : 0 < 2 * len - k := by omega
  have h5posB : 0 < 2 * k := by omega
  if sameSign then
    ⟨(subGeqLimbs r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA h5posB).1,
      by rw [subGeqLimbs_size, hr₄]⟩
  else
    ⟨(addGeqLimbs r₄.1 C₂ k (2 * len - k) 0 (2 * k) h5A h5B h5ge h5posA h5posB).1,
      by rw [addGeqLimbs_size, hr₄]⟩

end karatsubaMulLimbsRec

/--
Karatsuba multiplication of two equal-length limb slices. Returns a fresh
array of size `2 * len`.

The `threshold` parameter is the size below which we fall back to
`schoolbookMulLimbs`. When `len < max 2 threshold`, schoolbook is used
directly (we always need `len ≥ 2` to split).

Algorithm 1.3 (Karatsuba):
  k := ⌈len/2⌉; m := len - k    (so `m ≤ k`)
  C₀ := A₀ · B₀  (k × k → 2k limbs)
  C₁ := A₁ · B₁  (m × m → 2m limbs)
  C₂ := |A₀ − A₁| · |B₀ − B₁|  (k × k → 2k limbs)
  result := C₀ + (C₀ + C₁ − s · C₂) · β^k + C₁ · β^{2k}
where `s = +1` if `sign(A₀−A₁) = sign(B₀−B₁)`, else `s = −1`.  The assembly
(`karatsubaMulLimbsRec.assemble`) works in place in `C₀ ++ C₁` with two passes over the
middle region.
-/
def karatsubaMulLimbsRec (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < 2 ∨ len < threshold then
    ⟨schoolbookMulLimbs a b loA len loB len hA hB, by
      rw [schoolbookMulLimbs_size]; omega⟩
  else
    have hlen : 2 ≤ len := by omega
    let k := (len + 1) / 2
    let m := len - k
    have hk_pos : 0 < k := by show 0 < (len + 1) / 2; omega
    have hk_lt : k < len := by show (len + 1) / 2 < len; omega
    have hm_pos : 0 < m := by show 0 < len - (len + 1) / 2; omega
    have hm_le : m ≤ k := by show len - (len + 1) / 2 ≤ (len + 1) / 2; omega
    have hm_lt : m < len := by show len - (len + 1) / 2 < len; omega
    have hkm : k + m = len := by
      show (len + 1) / 2 + (len - (len + 1) / 2) = len; omega
    have hA0 : loA + k ≤ a.size := by omega
    have hB0 : loB + k ≤ b.size := by omega
    let C0 := karatsubaMulLimbsRec threshold a b loA loB k hA0 hB0
    have hA1 : (loA + k) + m ≤ a.size := by omega
    have hB1 : (loB + k) + m ≤ b.size := by omega
    let C1 := karatsubaMulLimbsRec threshold a b (loA + k) (loB + k) m hA1 hB1
    have hAabs : loA + k + m ≤ a.size := by omega
    have hBabs : loB + k + m ≤ b.size := by omega
    let absA := absSubLimbsKM a loA k m hAabs hm_le hk_pos hm_pos
    let absB := absSubLimbsKM b loB k m hBabs hm_le hk_pos hm_pos
    have hAabs_lim : 0 + k ≤ absA.1.1.size := by rw [absA.1.2]; omega
    have hBabs_lim : 0 + k ≤ absB.1.1.size := by rw [absB.1.2]; omega
    let C2 := karatsubaMulLimbsRec threshold absA.1.1 absB.1.1 0 0 k hAabs_lim hBabs_lim
    have hk2m : k ≤ 2 * m := by show (len + 1) / 2 ≤ 2 * (len - (len + 1) / 2); omega
    karatsubaMulLimbsRec.assemble k m len C0.1 C1.1 C2.1 (absA.2 == absB.2)
      C0.2 C1.2 C2.2 hkm hk_pos hm_pos hm_le hk2m
  termination_by len
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Karatsuba multiplication of two equal-length limb slices, with the same
    signature shape as `schoolbookMulLimbs` (a single shared `len`).  Falls
    back to `schoolbookMulLimbs` when `len < max 2 threshold`. -/
def karatsubaMulLimbs (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) : Array UInt64 :=
  (karatsubaMulLimbsRec threshold a b loA loB len hA hB).1

/-- The result of Karatsuba multiplication has size `2 * len`. -/
theorem karatsubaMulLimbs_size (threshold : Nat) (a b : Array UInt64)
    (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (karatsubaMulLimbs threshold a b loA loB len hA hB).size = 2 * len :=
  (karatsubaMulLimbsRec threshold a b loA loB len hA hB).2

end Azurite.AzNat
