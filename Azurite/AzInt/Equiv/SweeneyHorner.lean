/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.SweeneyHorner
import Azurite.Transcendental.EulerGamma
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.MulSmall
import Azurite.AzInt.Equiv.ShiftRight
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.MulNat

/-!
## The truncated backward recurrence encloses Sweeney's partial sum

Proofs for `Azurite/AzInt/SweeneyHorner.lean`.

* `SweeneyRepr n l len A B C`: the block `[[A, B], [0, C]]` stands for the index range
  `[l, l + len)`, i.e. `A / C` is the ratio and `B / C` the normalized sum of that range
  (`sweeneyRatio`, `sweeneyPartial`).  The matrix of one index
  (`sweeneyRepr_single`) and the product of two adjacent blocks (`SweeneyRepr.mul`) are the
  only facts about the series that are used.
* `SweeneyState.Encl s Z`: the state stands for `Z`, `|Z · dn − nm| ≤ rn` with `dn > 0`.
  Applying a block maps `Z` to `(A Z + B) / C` (`SweeneyState.Encl.apply`), a truncation keeps
  `Z` (`sweeneyTrim_encl`: the radius absorbs the two floors and `|Z| ≤ 2^j`).
* `sweeneyHorner_encl`: the final state stands for the partial sum, for either loop, and
  `sweeneyHornerEncl_spec`: the fractions `a / d ≤ S ≤ c / d`.
-/

namespace Azurite.AzInt

open Finset

theorem toInt_mulNat (z : AzInt) (a : ℕ) : (z.mulNat a).toInt = z.toInt * a := by
  unfold mulNat
  split_ifs with h
  · rw [toInt_mulUInt64]
    congr 2
    exact UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  · rw [toInt_mul, AzNat.toInt_toAzInt, AzNat.toNat_ofNat]

theorem abs_toInt_real (z : AzInt) : |(z.toInt : ℝ)| = z.abs.toNat := by
  show |((if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ) : ℤ) : ℝ)| = _
  split_ifs <;> simp

/-! ### The series, by index ranges -/

/-- The product of the term ratios `n / (j + 1)` of the indices `l, …, l + k − 1`. -/
noncomputable def sweeneyRatio (n l k : ℕ) : ℝ :=
  ∏ j ∈ range k, ((n : ℝ) / ((l + j + 1 : ℕ) : ℝ))

/-- The range `[l, l + m)` of Sweeney's series, normalized to its start:
`∑_{k<m} ((−1)^(l+k) / (l+k+1)) ∏_{j≤k} n / (l+j+1)`. -/
noncomputable def sweeneyPartial (n l m : ℕ) : ℝ :=
  ∑ k ∈ range m, (-1 : ℝ) ^ (l + k) / ((l + k + 1 : ℕ) : ℝ) * sweeneyRatio n l (k + 1)

theorem sweeneyRatio_add (n l m k : ℕ) :
    sweeneyRatio n l (m + k) = sweeneyRatio n l m * sweeneyRatio n (l + m) k := by
  unfold sweeneyRatio
  rw [prod_range_add]
  congr 1
  exact prod_congr rfl fun j _ => by rw [show l + (m + j) + 1 = l + m + j + 1 by omega]

theorem sweeneyPartial_add (n l m m' : ℕ) :
    sweeneyPartial n l (m + m') = sweeneyPartial n l m
      + sweeneyRatio n l m * sweeneyPartial n (l + m) m' := by
  unfold sweeneyPartial
  rw [sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show l + (m + k) = l + m + k by omega, show m + k + 1 = m + (k + 1) by ring,
    sweeneyRatio_add]
  ring

/-! ### Blocks -/

/-- The block `[[A, B], [0, C]]` stands for the index range `[l, l + len)` of Sweeney's series
with argument `n`. -/
def SweeneyRepr (n l len : ℕ) (A B C : ℝ) : Prop :=
  0 < C ∧ A / C = sweeneyRatio n l len ∧ B / C = sweeneyPartial n l len

theorem sweeneyRepr_one (n l : ℕ) : SweeneyRepr n l 0 1 0 1 := by
  refine ⟨one_pos, ?_, ?_⟩ <;> simp [sweeneyRatio, sweeneyPartial]

/-- The matrix of the index `k`: `[[n (k+1), (−1)^k n], [0, (k+1)²]]`. -/
theorem sweeneyRepr_single (n k : ℕ) :
    SweeneyRepr n k 1 ((n : ℝ) * (k + 1)) ((-1) ^ k * n) (((k : ℝ) + 1) * (k + 1)) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  refine ⟨by positivity, ?_, ?_⟩
  · simp only [sweeneyRatio, range_one, prod_singleton, add_zero]
    push_cast
    field_simp
  · simp only [sweeneyPartial, sweeneyRatio, range_one, sum_singleton, prod_singleton, add_zero,
      zero_add]
    push_cast
    field_simp

/-- The product of the blocks of two adjacent ranges. -/
theorem SweeneyRepr.mul {n l m m' : ℕ} {A₁ B₁ C₁ A₂ B₂ C₂ : ℝ}
    (h₁ : SweeneyRepr n l m A₁ B₁ C₁) (h₂ : SweeneyRepr n (l + m) m' A₂ B₂ C₂) :
    SweeneyRepr n l (m + m') (A₁ * A₂) (A₁ * B₂ + B₁ * C₂) (C₁ * C₂) := by
  obtain ⟨hC₁, hA₁, hB₁⟩ := h₁
  obtain ⟨hC₂, hA₂, hB₂⟩ := h₂
  refine ⟨mul_pos hC₁ hC₂, ?_, ?_⟩
  · rw [sweeneyRatio_add, ← hA₁, ← hA₂]
    field_simp
  · rw [sweeneyPartial_add, ← hA₁, ← hB₁, ← hB₂]
    field_simp
    ring

/-- One more index below a word block, even index. -/
theorem SweeneyRepr.ext_even {n k len A Bp Bn C : ℕ} (hk : k % 2 = 0)
    (h : SweeneyRepr n (k + 1) len A ((Bp : ℝ) - Bn) C) :
    SweeneyRepr n k (1 + len) ((n * (k + 1) * A : ℕ) : ℝ)
      (((n * (k + 1) * Bp + n * C : ℕ) : ℝ) - ((n * (k + 1) * Bn : ℕ) : ℝ))
      (((k + 1) * (k + 1) * C : ℕ) : ℝ) := by
  have := (sweeneyRepr_single n k).mul h
  rw [(Nat.even_iff.mpr hk).neg_one_pow, one_mul] at this
  convert this using 1 <;> push_cast <;> ring

/-- One more index below a word block, odd index. -/
theorem SweeneyRepr.ext_odd {n k len A Bp Bn C : ℕ} (hk : ¬k % 2 = 0)
    (h : SweeneyRepr n (k + 1) len A ((Bp : ℝ) - Bn) C) :
    SweeneyRepr n k (1 + len) ((n * (k + 1) * A : ℕ) : ℝ)
      (((n * (k + 1) * Bp : ℕ) : ℝ) - ((n * (k + 1) * Bn + n * C : ℕ) : ℝ))
      (((k + 1) * (k + 1) * C : ℕ) : ℝ) := by
  have := (sweeneyRepr_single n k).mul h
  rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow] at this
  convert this using 1 <;> push_cast <;> ring

theorem sweeneyRepr_single_even {n k : ℕ} (hk : k % 2 = 0) :
    SweeneyRepr n k 1 ((n * (k + 1) : ℕ) : ℝ) ((n : ℝ) - (0 : ℕ))
      (((k + 1) * (k + 1) : ℕ) : ℝ) := by
  have := sweeneyRepr_single n k
  rw [(Nat.even_iff.mpr hk).neg_one_pow, one_mul] at this
  convert this using 1 <;> push_cast <;> ring

theorem sweeneyRepr_single_odd {n k : ℕ} (hk : ¬k % 2 = 0) :
    SweeneyRepr n k 1 ((n * (k + 1) : ℕ) : ℝ) (((0 : ℕ) : ℝ) - n)
      (((k + 1) * (k + 1) : ℕ) : ℝ) := by
  have := sweeneyRepr_single n k
  rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow] at this
  convert this using 1 <;> push_cast <;> ring

/-! ### States -/

/-- The state stands for `Z`: `|Z · dn − nm| ≤ rn`, with a positive denominator. -/
def SweeneyState.Encl (s : SweeneyState) (Z : ℝ) : Prop :=
  0 < s.dn.toNat ∧ |Z * s.dn.toNat - s.nm.toInt| ≤ s.rn.toNat

/-- A block applied exactly: `Z ↦ (A Z + B) / C`. -/
theorem SweeneyState.Encl.apply {s s' : SweeneyState} {Z A B C : ℝ} (h : s.Encl Z) (hA : 0 ≤ A)
    (hC : 0 < C) (hnm : (s'.nm.toInt : ℝ) = A * s.nm.toInt + B * s.dn.toNat)
    (hdn : (s'.dn.toNat : ℝ) = C * s.dn.toNat) (hrn : (s'.rn.toNat : ℝ) = A * s.rn.toNat) :
    s'.Encl (B / C + A / C * Z) := by
  obtain ⟨hd, hZ⟩ := h
  have hd' : (0 : ℝ) < s.dn.toNat := by exact_mod_cast hd
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ) < s'.dn.toNat := by rw [hdn]; positivity
    exact_mod_cast this
  · rw [hnm, hdn, hrn]
    have e : (B / C + A / C * Z) * (C * s.dn.toNat) - (A * s.nm.toInt + B * s.dn.toNat)
        = A * (Z * s.dn.toNat - s.nm.toInt) := by
      field_simp
      ring
    rw [e, abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left hZ hA

/-- A truncation keeps the value the state stands for. -/
theorem sweeneyTrim_encl {V : ℕ} (hV : 1 ≤ V) {s : SweeneyState} {Z : ℝ} (h : s.Encl Z) :
    (sweeneyTrim V s).Encl Z := by
  unfold sweeneyTrim
  split_ifs with hc
  swap
  · exact h
  obtain ⟨hd, hZ⟩ := h
  set D := s.dn.toNat with hD
  set sd := s.dn.size with hsd
  set sh := (sd - V) / 64 * 64 with hsh
  set mx := max s.nm.abs.size s.rn.size with hmx
  set j := mx + 2 - sd with hj
  have hshle : sh ≤ sd - V := Nat.div_mul_le_self _ _
  have hDlow : 2 ^ (sd - 1) ≤ D := by
    apply Nat.lt_size.mp
    rw [hD, AzNat.size_toNat]
    omega
  have hpD : 2 ^ sh ≤ D := (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hDlow
  -- the new components
  have hdn : (s.dn >>> sh).toNat = D / 2 ^ sh := by
    rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
  have hnm : (s.nm >>> sh).toInt = s.nm.toInt / 2 ^ sh := by
    rw [AzInt.toInt_hShiftRight, Int.shiftRight_eq_div_pow]
    norm_cast
  have hrn : ((s.rn >>> sh) + (AzNat.ofNat 2 + (1 : AzNat) <<< j)).toNat
      = s.rn.toNat / 2 ^ sh + (2 + 2 ^ j) := by
    rw [AzNat.toNat_add, AzNat.toNat_add, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow,
      AzNat.toNat_ofNat, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_one, one_mul]
  refine ⟨?_, ?_⟩
  · show 0 < (s.dn >>> sh).toNat
    rw [hdn]
    exact Nat.div_pos hpD (by positivity)
  show |Z * ((s.dn >>> sh).toNat : ℝ) - ((s.nm >>> sh).toInt : ℝ)|
    ≤ (((s.rn >>> sh) + (AzNat.ofNat 2 + (1 : AzNat) <<< j)).toNat : ℝ)
  rw [hdn, hnm, hrn]
  set p : ℝ := (2 : ℝ) ^ sh with hp
  have hp0 : 0 < p := by positivity
  -- the three floors
  have hDdiv : (D : ℝ) = p * ((D / 2 ^ sh : ℕ) : ℝ) + ((D % 2 ^ sh : ℕ) : ℝ) := by
    rw [hp]; exact_mod_cast (Nat.div_add_mod D (2 ^ sh)).symm
  have hDmod : ((D % 2 ^ sh : ℕ) : ℝ) < p := by
    rw [hp]; exact_mod_cast Nat.mod_lt D (by positivity)
  have hNdiv : (s.nm.toInt : ℝ)
      = p * ((s.nm.toInt / 2 ^ sh : ℤ) : ℝ) + ((s.nm.toInt % 2 ^ sh : ℤ) : ℝ) := by
    rw [hp]; exact_mod_cast (Int.mul_ediv_add_emod s.nm.toInt (2 ^ sh)).symm
  have hNmod0 : (0 : ℝ) ≤ ((s.nm.toInt % 2 ^ sh : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg _ (by positivity)
  have hNmod : ((s.nm.toInt % 2 ^ sh : ℤ) : ℝ) < p := by
    rw [hp]; exact_mod_cast Int.emod_lt_of_pos s.nm.toInt (by positivity)
  have hRdiv : (s.rn.toNat : ℝ)
      = p * ((s.rn.toNat / 2 ^ sh : ℕ) : ℝ) + ((s.rn.toNat % 2 ^ sh : ℕ) : ℝ) := by
    rw [hp]; exact_mod_cast (Nat.div_add_mod s.rn.toNat (2 ^ sh)).symm
  have hRmod : ((s.rn.toNat % 2 ^ sh : ℕ) : ℝ) < p := by
    rw [hp]; exact_mod_cast Nat.mod_lt s.rn.toNat (by positivity)
  -- `|Z| ≤ 2^j`
  have hZj : |Z| ≤ (2 : ℝ) ^ j := by
    have h1 : |Z| * D ≤ (s.nm.abs.toNat : ℝ) + s.rn.toNat := by
      have := abs_sub_abs_le_abs_sub (Z * (D : ℝ)) (s.nm.toInt : ℝ)
      rw [abs_mul, abs_of_nonneg (a := (D : ℝ)) (Nat.cast_nonneg D), abs_toInt_real] at this
      linarith
    have h2 : s.nm.abs.toNat + s.rn.toNat < 2 ^ j * 2 ^ (sd - 1) := by
      have ha : s.nm.abs.toNat < 2 ^ mx :=
        lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right (by norm_num) (by rw [AzNat.size_toNat]; exact le_max_left _ _))
      have hb : s.rn.toNat < 2 ^ mx :=
        lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right (by norm_num) (by rw [AzNat.size_toNat]; exact le_max_right _ _))
      have hc' : 2 ^ (mx + 1) ≤ 2 ^ j * 2 ^ (sd - 1) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (mx + 1) = 2 ^ mx + 2 ^ mx := by rw [pow_succ]; ring
      omega
    have h3 : |Z| * D < (2 : ℝ) ^ j * D := by
      have h2' : ((s.nm.abs.toNat : ℝ) + s.rn.toNat) < (2 : ℝ) ^ j * (2 : ℝ) ^ (sd - 1) := by
        exact_mod_cast h2
      have h4 : (2 : ℝ) ^ j * (2 : ℝ) ^ (sd - 1) ≤ (2 : ℝ) ^ j * D :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hDlow) (by positivity)
      linarith
    exact (lt_of_mul_lt_mul_right h3 (Nat.cast_nonneg D)).le
  -- assemble
  set d' : ℝ := ((D / 2 ^ sh : ℕ) : ℝ) with hd'
  set m' : ℝ := ((s.nm.toInt / 2 ^ sh : ℤ) : ℝ) with hm'
  set r' : ℝ := ((s.rn.toNat / 2 ^ sh : ℕ) : ℝ) with hr'
  set rD : ℝ := ((D % 2 ^ sh : ℕ) : ℝ) with hrD
  set rN : ℝ := ((s.nm.toInt % 2 ^ sh : ℤ) : ℝ) with hrN
  have hrD0 : 0 ≤ rD := Nat.cast_nonneg _
  have hRmod0 : (0 : ℝ) ≤ ((s.rn.toNat % 2 ^ sh : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : p * (Z * d' - m') = (Z * D - s.nm.toInt) - Z * rD + rN := by
    rw [hDdiv, hNdiv]; ring
  have hZr : |Z * rD| ≤ (2 : ℝ) ^ j * p := by
    rw [abs_mul, abs_of_nonneg hrD0]
    exact mul_le_mul hZj hDmod.le hrD0 (by positivity)
  have hkey : p * |Z * d' - m'| ≤ p * (r' + (2 + (2 : ℝ) ^ j)) := by
    rw [← abs_of_pos hp0, ← abs_mul, abs_of_pos hp0, e]
    have t1 := abs_add_le ((Z * D - s.nm.toInt) - Z * rD) rN
    have t2 := abs_sub (Z * (D : ℝ) - s.nm.toInt) (Z * rD)
    rw [abs_of_nonneg hNmod0] at t1
    have hZ' : |Z * (D : ℝ) - s.nm.toInt| ≤ s.rn.toNat := hZ
    nlinarith [hZ', hRdiv, hRmod, hNmod, hZr, t1, t2]
  have := le_of_mul_le_mul_left hkey hp0
  push_cast
  linarith

/-- A word block applied to the state. -/
theorem sweeneyFlush_encl {V : ℕ} (hV : 1 ≤ V) {n l len A Bp Bn C : ℕ} {s : SweeneyState}
    {Z : ℝ} (hr : SweeneyRepr n l len A ((Bp : ℝ) - Bn) C) (h : s.Encl Z) :
    (sweeneyFlush V A Bp Bn C s).Encl
      (sweeneyPartial n l len + sweeneyRatio n l len * Z) := by
  obtain ⟨hC, hA, hB⟩ := hr
  unfold sweeneyFlush
  apply sweeneyTrim_encl hV
  rw [← hA, ← hB]
  refine h.apply (Nat.cast_nonneg A) hC ?_ ?_ ?_
  · show ((if Bn ≤ Bp then s.nm.mulNat A + (s.dn.mulNat (Bp - Bn)).toAzInt
        else s.nm.mulNat A - (s.dn.mulNat (Bn - Bp)).toAzInt).toInt : ℝ) = _
    split_ifs with hb
    · rw [toInt_add, toInt_mulNat, AzNat.toInt_toAzInt, AzNat.toNat_mulNat]
      push_cast [Nat.cast_sub hb]
      ring
    · rw [toInt_sub, toInt_mulNat, AzNat.toInt_toAzInt, AzNat.toNat_mulNat]
      push_cast [Nat.cast_sub (le_of_not_ge hb)]
      ring
  · show ((s.dn.mulNat C).toNat : ℝ) = _
    rw [AzNat.toNat_mulNat]; push_cast; ring
  · show ((s.rn.mulNat A).toNat : ℝ) = _
    rw [AzNat.toNat_mulNat]; push_cast; ring

/-- The long block stands for a range. -/
def SweeneyBlock.Repr (M : SweeneyBlock) (n l len : ℕ) : Prop :=
  SweeneyRepr n l len M.A.toNat M.B.toInt M.C.toNat

theorem SweeneyBlock.repr_one (n l : ℕ) : SweeneyBlock.one.Repr n l 0 := by
  have := sweeneyRepr_one n l
  unfold SweeneyBlock.Repr SweeneyBlock.one
  simp only [AzNat.toNat_ofNat]
  have h0 : (0 : AzInt).toInt = 0 := rfl
  rw [h0]
  exact_mod_cast this

/-- A word block times the long block. -/
theorem sweeneyPush_repr {n l len len' a bp bn c : ℕ} {M : SweeneyBlock}
    (hr : SweeneyRepr n l len a ((bp : ℝ) - bn) c) (hM : M.Repr n (l + len) len') :
    (sweeneyPush a bp bn c M).Repr n l (len + len') := by
  have := hr.mul hM
  unfold SweeneyBlock.Repr sweeneyPush
  convert this using 1
  · rw [AzNat.toNat_mulNat]; push_cast; ring
  · show ((if bn ≤ bp then M.B.mulNat a + (M.C.mulNat (bp - bn)).toAzInt
        else M.B.mulNat a - (M.C.mulNat (bn - bp)).toAzInt).toInt : ℝ) = _
    split_ifs with hb
    · rw [toInt_add, toInt_mulNat, AzNat.toInt_toAzInt, AzNat.toNat_mulNat]
      push_cast [Nat.cast_sub hb]
      ring
    · rw [toInt_sub, toInt_mulNat, AzNat.toInt_toAzInt, AzNat.toNat_mulNat]
      push_cast [Nat.cast_sub (le_of_not_ge hb)]
      ring
  · rw [AzNat.toNat_mulNat]; push_cast; ring

/-- The long block applied to the state. -/
theorem sweeneyApply_encl {V : ℕ} (hV : 1 ≤ V) {n l len : ℕ} {M : SweeneyBlock}
    {s : SweeneyState} {Z : ℝ} (hM : M.Repr n l len) (h : s.Encl Z) :
    (sweeneyApply V M s).Encl
      (sweeneyPartial n l len + sweeneyRatio n l len * Z) := by
  obtain ⟨hC, hA, hB⟩ := hM
  unfold sweeneyApply
  apply sweeneyTrim_encl hV
  rw [← hA, ← hB]
  refine h.apply (Nat.cast_nonneg _) hC ?_ ?_ ?_
  · show ((M.A.toAzInt * s.nm + M.B * s.dn.toAzInt).toInt : ℝ) = _
    rw [toInt_add, toInt_mul, toInt_mul, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt]
    push_cast
    ring
  · show ((M.C * s.dn).toNat : ℝ) = _
    rw [AzNat.toNat_mul]; push_cast; ring
  · show ((M.A * s.rn).toNat : ℝ) = _
    rw [AzNat.toNat_mul]; push_cast; ring

/-! ### The loops -/

/-- The word-block loop: from a pending block for `[k, k + len)` and a state standing for the
range `[k + len, N)`, the final state stands for `[0, N)`. -/
theorem sweeneyHornerLoop_encl {n V N : ℕ} (hV : 1 ≤ V) :
    ∀ (k len A Bp Bn C : ℕ) (s : SweeneyState), k + len ≤ N →
      SweeneyRepr n k len A ((Bp : ℝ) - Bn) C →
      s.Encl (sweeneyPartial n (k + len) (N - (k + len))) →
      (sweeneyHornerLoop n V k A Bp Bn C s).Encl (sweeneyPartial n 0 N)
  | 0, len, A, Bp, Bn, C, s, hN, hr, hs => by
    have := sweeneyFlush_encl hV hr hs
    rw [← sweeneyPartial_add, show len + (N - (0 + len)) = N by omega] at this
    exact this
  | k + 1, len, A, Bp, Bn, C, s, hN, hr, hs => by
    have hflush : (sweeneyFlush V A Bp Bn C s).Encl
        (sweeneyPartial n (k + 1) (N - (k + 1))) := by
      have := sweeneyFlush_encl hV hr hs
      rw [← sweeneyPartial_add,
        show len + (N - (k + 1 + len)) = N - (k + 1) by omega] at this
      exact this
    have hs' : s.Encl (sweeneyPartial n (k + (1 + len)) (N - (k + (1 + len)))) := by
      rw [show k + (1 + len) = k + 1 + len by omega]; exact hs
    rw [sweeneyHornerLoop]
    split_ifs with hf hk hk
    · exact sweeneyHornerLoop_encl hV k (1 + len) _ _ _ _ s (by omega) (hr.ext_even hk) hs'
    · exact sweeneyHornerLoop_encl hV k (1 + len) _ _ _ _ s (by omega) (hr.ext_odd hk) hs'
    · exact sweeneyHornerLoop_encl hV k 1 _ _ _ _ _ (by omega) (sweeneyRepr_single_even hk)
        hflush
    · exact sweeneyHornerLoop_encl hV k 1 _ _ _ _ _ (by omega) (sweeneyRepr_single_odd hk)
        hflush

/-- The two-level loop: a pending word block for `[k, k + len)`, a long block for
`[k + len, k + len + len')` and a state standing for the rest. -/
theorem sweeneyHornerLoop₂_encl {n V Lb N : ℕ} (hV : 1 ≤ V) :
    ∀ (k len len' A Bp Bn C : ℕ) (M : SweeneyBlock) (s : SweeneyState), k + len + len' ≤ N →
      SweeneyRepr n k len A ((Bp : ℝ) - Bn) C → M.Repr n (k + len) len' →
      s.Encl (sweeneyPartial n (k + len + len') (N - (k + len + len'))) →
      (sweeneyHornerLoop₂ n V Lb k A Bp Bn C M s).Encl (sweeneyPartial n 0 N)
  | 0, len, len', A, Bp, Bn, C, M, s, hN, hr, hM, hs => by
    have hs₀ : s.Encl
        (sweeneyPartial n (0 + (len + len')) (N - (0 + (len + len')))) := by
      rw [← add_assoc]; exact hs
    have := sweeneyApply_encl hV (sweeneyPush_repr hr hM) hs₀
    rw [← sweeneyPartial_add,
      show len + len' + (N - (0 + (len + len'))) = N by omega] at this
    exact this
  | k + 1, len, len', A, Bp, Bn, C, M, s, hN, hr, hM, hs => by
    have hpush := sweeneyPush_repr hr hM
    have hs₁ : s.Encl
        (sweeneyPartial n (k + 1 + (len + len')) (N - (k + 1 + (len + len')))) := by
      rw [show k + 1 + (len + len') = k + 1 + len + len' by omega]; exact hs
    have happly : (sweeneyApply V (sweeneyPush A Bp Bn C M) s).Encl
        (sweeneyPartial n (k + 1 + 0) (N - (k + 1 + 0))) := by
      have := sweeneyApply_encl hV hpush hs₁
      rw [← sweeneyPartial_add,
        show len + len' + (N - (k + 1 + (len + len'))) = N - (k + 1) by omega] at this
      exact this
    have hs' : s.Encl
        (sweeneyPartial n (k + (1 + len) + len') (N - (k + (1 + len) + len'))) := by
      rw [show k + (1 + len) + len' = k + 1 + len + len' by omega]; exact hs
    have hM' : M.Repr n (k + (1 + len)) len' := by
      rw [show k + (1 + len) = k + 1 + len by omega]; exact hM
    rw [sweeneyHornerLoop₂]
    split_ifs
    all_goals first
      | exact sweeneyHornerLoop₂_encl hV k (1 + len) len' _ _ _ _ M s (by omega)
          (hr.ext_even (by assumption)) hM' hs'
      | exact sweeneyHornerLoop₂_encl hV k (1 + len) len' _ _ _ _ M s (by omega)
          (hr.ext_odd (by assumption)) hM' hs'
      | exact sweeneyHornerLoop₂_encl hV k 1 0 _ _ _ _ _ _ (by omega)
          (sweeneyRepr_single_even (by assumption)) (SweeneyBlock.repr_one n (k + 1)) happly
      | exact sweeneyHornerLoop₂_encl hV k 1 0 _ _ _ _ _ _ (by omega)
          (sweeneyRepr_single_odd (by assumption)) (SweeneyBlock.repr_one n (k + 1)) happly
      | exact sweeneyHornerLoop₂_encl hV k 1 (len + len') _ _ _ _ _ s (by omega)
          (sweeneyRepr_single_even (by assumption)) hpush hs₁
      | exact sweeneyHornerLoop₂_encl hV k 1 (len + len') _ _ _ _ _ s (by omega)
          (sweeneyRepr_single_odd (by assumption)) hpush hs₁

/-- The normalized sum of the range `[0, N)` is the partial sum of Sweeney's series. -/
theorem sweeneyPartial_zero (n N : ℕ) :
    sweeneyPartial n 0 N = ∑ k ∈ range N, sweeneyTerm (n : ℝ) k := by
  rw [sweeneyPartial]
  refine sum_congr rfl fun k _ => ?_
  have hr : sweeneyRatio n 0 (k + 1) = (n : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    simp only [sweeneyRatio, zero_add]
    rw [prod_div_distrib, prod_const, card_range]
    congr 1
    exact_mod_cast prod_range_add_one_eq_factorial (k + 1)
  rw [hr]
  simp only [sweeneyTerm, zero_add]
  rw [Nat.factorial_succ]
  push_cast
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The truncated recurrence encloses the partial sum of Sweeney's series.** -/
theorem sweeneyHorner_encl (n N : ℕ) {V : ℕ} (hV : 1 ≤ V) (Lb : ℕ) :
    (sweeneyHorner n N V Lb).Encl (∑ k ∈ range N, sweeneyTerm (n : ℝ) k) := by
  rw [← sweeneyPartial_zero]
  have h0 : (⟨0, (1 : AzNat) <<< V, 0⟩ : SweeneyState).Encl
      (sweeneyPartial n N (N - N)) := by
    refine ⟨?_, ?_⟩
    · show 0 < ((1 : AzNat) <<< V).toNat
      rw [AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_one]
      positivity
    · show |_ * (((1 : AzNat) <<< V).toNat : ℝ) - ((0 : AzInt).toInt : ℝ)|
        ≤ ((0 : AzNat).toNat : ℝ)
      have h00 : (0 : AzInt).toInt = 0 := rfl
      rw [Nat.sub_self, h00, AzNat.toNat_zero]
      simp [sweeneyPartial]
  have hr : SweeneyRepr n N 0 ((1 : ℕ) : ℝ) (((0 : ℕ) : ℝ) - (0 : ℕ)) ((1 : ℕ) : ℝ) := by
    have := sweeneyRepr_one n N
    simpa using this
  unfold sweeneyHorner
  split_ifs with hL
  · exact sweeneyHornerLoop_encl hV N 0 1 0 0 1 _ (by omega) hr (by simpa using h0)
  · exact sweeneyHornerLoop₂_encl hV N 0 0 1 0 0 1 _ _ (by omega) hr
      (SweeneyBlock.repr_one n (N + 0)) (by simpa using h0)

/-- **The fractions of `sweeneyHornerEncl` enclose the partial sum** `S ≥ 0`. -/
theorem sweeneyHornerEncl_spec (n N : ℕ) {V : ℕ} (hV : 1 ≤ V) (Lb : ℕ)
    (hS : 0 ≤ ∑ k ∈ range N, sweeneyTerm (n : ℝ) k) :
    0 < (sweeneyHornerEncl n N V Lb).2.2.toNat ∧
      ((sweeneyHornerEncl n N V Lb).1.toNat : ℝ) / (sweeneyHornerEncl n N V Lb).2.2.toNat
        ≤ ∑ k ∈ range N, sweeneyTerm (n : ℝ) k ∧
      ∑ k ∈ range N, sweeneyTerm (n : ℝ) k
        ≤ ((sweeneyHornerEncl n N V Lb).2.1.toNat : ℝ)
          / (sweeneyHornerEncl n N V Lb).2.2.toNat := by
  obtain ⟨hd, hZ⟩ := sweeneyHorner_encl n N hV Lb
  set S := ∑ k ∈ range N, sweeneyTerm (n : ℝ) k with hSdef
  set s := sweeneyHorner n N V Lb with hs
  have hd' : (0 : ℝ) < s.dn.toNat := by exact_mod_cast hd
  rw [abs_le] at hZ
  refine ⟨hd, ?_, ?_⟩
  · show (((if (s.nm - s.rn.toAzInt).sign then (s.nm - s.rn.toAzInt).abs else 0 : AzNat).toNat
      : ℝ)) / s.dn.toNat ≤ S
    rw [div_le_iff₀ hd']
    split_ifs with hsg
    · have e : ((s.nm - s.rn.toAzInt).toInt : ℝ) = ((s.nm - s.rn.toAzInt).abs.toNat : ℝ) := by
        show (((if (s.nm - s.rn.toAzInt).sign then ((s.nm - s.rn.toAzInt).abs.toNat : ℤ)
          else -((s.nm - s.rn.toAzInt).abs.toNat : ℤ)) : ℤ) : ℝ) = _
        rw [ite_eq_left hsg]
        exact Int.cast_natCast _
      rw [← e, toInt_sub, AzNat.toInt_toAzInt]
      push_cast
      linarith [hZ.1]
    · rw [AzNat.toNat_zero, Nat.cast_zero]
      exact mul_nonneg hS hd'.le
  · show S ≤ (((s.nm + s.rn.toAzInt).abs.toNat : ℝ)) / s.dn.toNat
    rw [le_div_iff₀ hd', ← abs_toInt_real, toInt_add, AzNat.toInt_toAzInt]
    push_cast
    exact le_trans (by linarith [hZ.2]) (le_abs_self _)

end Azurite.AzInt
