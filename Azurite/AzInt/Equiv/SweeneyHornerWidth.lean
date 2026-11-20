/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Equiv.SweeneyHorner

/-!
# The width of the truncated recurrence for Sweeney's series

`AzInt/SweeneyHorner.lean` carries the truncation error of the backward recurrence as an exact
radius, and its correctness (`Equiv/SweeneyHorner.lean`) needs nothing about the size of that
radius.  Here the size is bounded, which is what the convergence of the bracket of Euler's
constant needs.

Weight the relative radius `rn / dn` of a state that stands for the range `[l, N)` by the
factor `n^l / l!` (`sweeneyRatio n 0 l`) by which the remaining blocks will multiply it
(`SweeneyState.Rad`).  Then

* applying a block does not change the weighted radius (`SweeneyState.Rad.apply`);
* a truncation multiplies it by at most `1 + 17 · 2^(1−V)` and adds at most
  `11 e^n · 2^(1−V)` (`sweeneyTrim_rad`): the denominator keeps at least `V` bits, and both
  `n^l / l!` and `n^l / l!` times the value of the range are at most `e^n`
  (`sweeneyRatio_zero_le_exp`, `sweeneyRatio_zero_mul_abs_partial_le`).

There are at most `N + 1` truncations, so the final radius is at most `sweeneyU n V (N + 1)`
times the denominator (`sweeneyHorner_radius`), and the two fractions of `sweeneyHornerEncl`
differ by at most twice that (`sweeneyHornerEncl_width`).
-/

namespace Azurite.AzInt

open Finset

/-! ### The series -/

theorem sweeneyRatio_zero (n k : ℕ) :
    sweeneyRatio n 0 k = (n : ℝ) ^ k / (k.factorial : ℝ) := by
  simp only [sweeneyRatio, zero_add]
  rw [prod_div_distrib, prod_const, card_range]
  congr 1
  exact_mod_cast prod_range_add_one_eq_factorial k

theorem sweeneyRatio_nonneg (n l k : ℕ) : 0 ≤ sweeneyRatio n l k :=
  prod_nonneg fun _ _ => by positivity

theorem sweeneyRatio_zero_le_exp (n k : ℕ) : sweeneyRatio n 0 k ≤ Real.exp n := by
  rw [sweeneyRatio_zero]
  have h := Real.sum_le_exp_of_nonneg (x := (n : ℝ)) (Nat.cast_nonneg n) (k + 1)
  rw [sum_range_succ] at h
  have : 0 ≤ ∑ i ∈ range k, (n : ℝ) ^ i / (i.factorial : ℝ) :=
    sum_nonneg fun _ _ => by positivity
  linarith

/-- The weight times the value of a range is at most `e^n`: a part of the exponential
series. -/
theorem sweeneyRatio_zero_mul_abs_partial_le (n l m : ℕ) :
    sweeneyRatio n 0 l * |sweeneyPartial n l m| ≤ Real.exp n := by
  have h0 := sweeneyRatio_nonneg n 0 l
  calc sweeneyRatio n 0 l * |sweeneyPartial n l m|
      ≤ sweeneyRatio n 0 l * ∑ k ∈ range m, sweeneyRatio n l (k + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ h0
        unfold sweeneyPartial
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_nonneg (sweeneyRatio_nonneg _ _ _), abs_of_nonneg (Nat.cast_nonneg _)]
        have h1 : (1 : ℝ) ≤ ((l + k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
        have h2 : (1 : ℝ) / ((l + k + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact h1
        exact mul_le_of_le_one_left (sweeneyRatio_nonneg _ _ _) h2
    _ = ∑ k ∈ range m, sweeneyRatio n 0 (l + (k + 1)) := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ => by rw [sweeneyRatio_add n 0 l (k + 1), zero_add]
    _ = ∑ k ∈ range m, (n : ℝ) ^ (l + 1 + k) / ((l + 1 + k).factorial : ℝ) :=
        sum_congr rfl fun k _ => by
          rw [sweeneyRatio_zero, show l + (k + 1) = l + 1 + k by ring]
    _ ≤ ∑ i ∈ range (l + 1 + m), (n : ℝ) ^ i / (i.factorial : ℝ) := by
        rw [sum_range_add (fun i => (n : ℝ) ^ i / (i.factorial : ℝ)) (l + 1) m]
        have : 0 ≤ ∑ i ∈ range (l + 1), (n : ℝ) ^ i / (i.factorial : ℝ) :=
          sum_nonneg fun _ _ => by positivity
        linarith
    _ ≤ Real.exp n := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg n) _

/-! ### The bound -/

/-- The bound for the weighted relative radius after `c` truncations at `V` bits. -/
noncomputable def sweeneyU (n V c : ℕ) : ℝ :=
  (c : ℝ) * (11 * Real.exp n / 2 ^ (V - 1)) * (1 + 17 / 2 ^ (V - 1)) ^ c

theorem sweeneyU_nonneg (n V c : ℕ) : 0 ≤ sweeneyU n V c := by
  unfold sweeneyU
  positivity

/-- One truncation: `U c (1 + a) + b ≤ U (c + 1)`. -/
theorem sweeneyU_succ (n V c : ℕ) :
    sweeneyU n V c * (1 + 17 / 2 ^ (V - 1)) + 11 * Real.exp n / 2 ^ (V - 1)
      ≤ sweeneyU n V (c + 1) := by
  unfold sweeneyU
  set a : ℝ := 17 / 2 ^ (V - 1) with ha
  set b : ℝ := 11 * Real.exp n / 2 ^ (V - 1) with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have h1 : (1 : ℝ) ≤ (1 + a) ^ (c + 1) := one_le_pow₀ (by linarith)
  have e : ((c + 1 : ℕ) : ℝ) * b * (1 + a) ^ (c + 1)
      = (c : ℝ) * b * (1 + a) ^ c * (1 + a) + b * (1 + a) ^ (c + 1) := by
    push_cast
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h1 hb0]

theorem sweeneyU_mono (n V : ℕ) {c c' : ℕ} (h : c ≤ c') : sweeneyU n V c ≤ sweeneyU n V c' := by
  induction c', h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    refine ih.trans ?_
    have h1 := sweeneyU_succ n V m
    have h2 : (0 : ℝ) ≤ 17 / 2 ^ (V - 1) := by positivity
    have h3 : (0 : ℝ) ≤ 11 * Real.exp n / 2 ^ (V - 1) := by positivity
    nlinarith [sweeneyU_nonneg n V m, mul_nonneg (sweeneyU_nonneg n V m) h2]

/-! ### The weighted radius of a state -/

/-- The radius of a state that stands for the range `[l, N)`, weighted by `n^l / l!`, is at
most `sweeneyU n V c` times the denominator. -/
def SweeneyState.Rad (s : SweeneyState) (n V l c : ℕ) : Prop :=
  sweeneyRatio n 0 l * s.rn.toNat ≤ sweeneyU n V c * s.dn.toNat

theorem SweeneyState.Rad.mono {s : SweeneyState} {n V l c c' : ℕ} (h : s.Rad n V l c)
    (hc : c ≤ c') : s.Rad n V l c' :=
  le_trans h (mul_le_mul_of_nonneg_right (sweeneyU_mono n V hc) (Nat.cast_nonneg _))

/-- A block applied exactly keeps the weighted radius. -/
theorem SweeneyState.Rad.apply {s s' : SweeneyState} {n V l len c : ℕ} {A C : ℝ}
    (h : s.Rad n V (l + len) c) (hC : 0 < C) (hA : A / C = sweeneyRatio n l len)
    (hdn : (s'.dn.toNat : ℝ) = C * s.dn.toNat) (hrn : (s'.rn.toNat : ℝ) = A * s.rn.toNat) :
    s'.Rad n V l c := by
  unfold SweeneyState.Rad at h ⊢
  rw [hdn, hrn]
  have hA' : A = sweeneyRatio n l len * C := by
    rw [← hA]
    field_simp
  rw [sweeneyRatio_add, zero_add] at h
  calc sweeneyRatio n 0 l * (A * s.rn.toNat)
      = C * (sweeneyRatio n 0 l * sweeneyRatio n l len * s.rn.toNat) := by rw [hA']; ring
    _ ≤ C * (sweeneyU n V c * s.dn.toNat) := mul_le_mul_of_nonneg_left h hC.le
    _ = sweeneyU n V c * (C * s.dn.toNat) := by ring

/-- **A truncation**: the weighted radius grows by the factor `1 + 17 · 2^(1−V)` and by
`11 e^n · 2^(1−V)` at most. -/
theorem sweeneyTrim_rad {n V l c : ℕ} (hV : 1 ≤ V) {s : SweeneyState} {Z : ℝ} (h : s.Encl Z)
    (hr : s.Rad n V l c) (hZE : sweeneyRatio n 0 l * |Z| ≤ Real.exp n) :
    (sweeneyTrim V s).Rad n V l (c + 1) := by
  unfold sweeneyTrim
  split_ifs with hc
  swap
  · exact hr.mono (Nat.le_succ c)
  obtain ⟨hd, hZ⟩ := h
  unfold SweeneyState.Rad at hr ⊢
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
  have hDup : D < 2 ^ sd := by
    have := Nat.lt_size_self D
    rwa [hD, AzNat.size_toNat] at this
  have hdn : (s.dn >>> sh).toNat = D / 2 ^ sh := by
    rw [AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
  have hrn : ((s.rn >>> sh) + (AzNat.ofNat 2 + (1 : AzNat) <<< j)).toNat
      = s.rn.toNat / 2 ^ sh + (2 + 2 ^ j) := by
    rw [AzNat.toNat_add, AzNat.toNat_add, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow,
      AzNat.toNat_ofNat, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_one, one_mul]
  show sweeneyRatio n 0 l * (((s.rn >>> sh) + (AzNat.ofNat 2 + (1 : AzNat) <<< j)).toNat : ℝ)
    ≤ sweeneyU n V (c + 1) * ((s.dn >>> sh).toNat : ℝ)
  rw [hdn, hrn]
  set d' := D / 2 ^ sh with hd'
  set R := s.rn.toNat with hR
  -- the new denominator keeps `V` bits
  have hd'low : 2 ^ (V - 1) ≤ d' := by
    have h1 : 2 ^ (sd - 1) / 2 ^ sh ≤ d' := Nat.div_le_div_right hDlow
    rw [Nat.pow_div (by omega) (by norm_num)] at h1
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h1
  have hDlt : D < 2 ^ sh * (d' + 1) := Nat.lt_mul_div_succ D (by positivity)
  -- `2^j D ≤ D + 8 (|nm| + rn)`
  have hjD : 2 ^ j * D ≤ D + 8 * (s.nm.abs.toNat + R) := by
    by_cases hjs : mx + 2 ≤ sd
    · have : j = 0 := by omega
      rw [this, pow_zero, one_mul]
      omega
    · have hmx2 : 2 ≤ mx := by omega
      have hmax : 2 ^ (mx - 1) ≤ s.nm.abs.toNat + R := by
        rcases le_total s.rn.size s.nm.abs.size with hle | hle
        · have : mx = s.nm.abs.size := max_eq_left hle
          have h1 : 2 ^ (mx - 1) ≤ s.nm.abs.toNat := by
            apply Nat.lt_size.mp
            rw [AzNat.size_toNat]
            omega
          omega
        · have : mx = s.rn.size := max_eq_right hle
          have h1 : 2 ^ (mx - 1) ≤ R := by
            apply Nat.lt_size.mp
            rw [hR, AzNat.size_toNat]
            omega
          omega
      have h1 : 2 ^ j * D ≤ 2 ^ j * 2 ^ sd := Nat.mul_le_mul_left _ hDup.le
      have h2 : 2 ^ j * 2 ^ sd = 8 * 2 ^ (mx - 1) := by
        rw [← pow_add, show j + sd = 3 + (mx - 1) by omega, pow_add]
        norm_num
      omega
  -- reals
  set r₀ := sweeneyRatio n 0 l with hr₀
  set U := sweeneyU n V c with hU
  set E := Real.exp (n : ℝ) with hE
  have hr₀0 : 0 ≤ r₀ := sweeneyRatio_nonneg n 0 l
  have hr₀E : r₀ ≤ E := sweeneyRatio_zero_le_exp n l
  have hU0 : 0 ≤ U := sweeneyU_nonneg n V c
  have hE0 : 0 < E := Real.exp_pos _
  have hDr : (0 : ℝ) < D := by exact_mod_cast hd
  set p : ℝ := (2 : ℝ) ^ sh with hp
  have hp0 : 0 < p := by positivity
  have hd'r : (2 : ℝ) ^ (V - 1) ≤ (d' : ℝ) := by exact_mod_cast hd'low
  have hP0 : (0 : ℝ) < (2 : ℝ) ^ (V - 1) := by positivity
  have hDlt' : (D : ℝ) ≤ p * ((d' : ℝ) + 1) := by
    have : (D : ℝ) < ((2 ^ sh * (d' + 1) : ℕ) : ℝ) := by exact_mod_cast hDlt
    push_cast at this
    exact this.le
  -- `|nm| ≤ |Z| D + rn`
  have hnm : (s.nm.abs.toNat : ℝ) ≤ |Z| * D + R := by
    have := abs_sub_abs_le_abs_sub (s.nm.toInt : ℝ) (Z * (D : ℝ))
    rw [abs_mul, abs_of_nonneg (a := (D : ℝ)) (Nat.cast_nonneg D), abs_toInt_real,
      abs_sub_comm] at this
    linarith
  -- the three parts of the new radius
  have t1 : r₀ * ((R / 2 ^ sh : ℕ) : ℝ) ≤ U * ((d' : ℝ) + 1) := by
    have h1 : ((R / 2 ^ sh : ℕ) : ℝ) ≤ (R : ℝ) / p := by
      rw [hp]
      exact_mod_cast Nat.cast_div_le (α := ℝ)
    have h2 : r₀ * ((R : ℝ) / p) ≤ U * (D : ℝ) / p := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hr hp0.le
    have h3 : U * (D : ℝ) / p ≤ U * ((d' : ℝ) + 1) := by
      rw [div_le_iff₀ hp0]
      have := mul_le_mul_of_nonneg_left hDlt' hU0
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hr₀0).trans (h2.trans h3)
  have t2 : r₀ * (2 : ℝ) ^ j ≤ 9 * E + 16 * U := by
    have h1 : (2 : ℝ) ^ j * D ≤ D + 8 * ((s.nm.abs.toNat : ℝ) + R) := by exact_mod_cast hjD
    have h2 : r₀ * ((2 : ℝ) ^ j * D) ≤ r₀ * ((D : ℝ) + 8 * (|Z| * D + R + R)) :=
      mul_le_mul_of_nonneg_left (by linarith) hr₀0
    have h3 : r₀ * ((D : ℝ) + 8 * (|Z| * D + R + R)) ≤ (9 * E + 16 * U) * D := by
      have a1 : r₀ * (D : ℝ) ≤ E * D := mul_le_mul_of_nonneg_right hr₀E hDr.le
      have a2 : r₀ * |Z| * D ≤ E * D := mul_le_mul_of_nonneg_right hZE hDr.le
      nlinarith
    have h4 : r₀ * (2 : ℝ) ^ j * D ≤ (9 * E + 16 * U) * D := by
      rw [mul_assoc]
      exact h2.trans h3
    exact le_of_mul_le_mul_right h4 hDr
  have t3 : r₀ * 2 ≤ 2 * E := by linarith
  have hsum : r₀ * (((R / 2 ^ sh + (2 + 2 ^ j) : ℕ)) : ℝ)
      ≤ U * (d' : ℝ) + 17 * U + 11 * E := by
    push_cast
    nlinarith
  refine hsum.trans ?_
  have hsucc := sweeneyU_succ n V c
  rw [← hU, ← hE] at hsucc
  have hd'0 : (0 : ℝ) ≤ d' := Nat.cast_nonneg _
  have hq : (1 : ℝ) ≤ (d' : ℝ) / 2 ^ (V - 1) := by
    rw [le_div_iff₀ hP0]
    linarith
  have h17 : 17 * U ≤ U * (17 / 2 ^ (V - 1)) * (d' : ℝ) := by
    have : U * (17 / 2 ^ (V - 1)) * (d' : ℝ) = 17 * U * ((d' : ℝ) / 2 ^ (V - 1)) := by
      field_simp
    rw [this]
    nlinarith
  have h11 : 11 * E ≤ 11 * E / 2 ^ (V - 1) * (d' : ℝ) := by
    have : 11 * E / 2 ^ (V - 1) * (d' : ℝ) = 11 * E * ((d' : ℝ) / 2 ^ (V - 1)) := by
      field_simp
    rw [this]
    nlinarith
  have := mul_le_mul_of_nonneg_right hsucc hd'0
  nlinarith

/-- A word block applied to the state, with its truncation. -/
theorem sweeneyFlush_rad {V : ℕ} (hV : 1 ≤ V) {n l len m A Bp Bn C c : ℕ} {s : SweeneyState}
    (hr : SweeneyRepr n l len A ((Bp : ℝ) - Bn) C)
    (h : s.Encl (sweeneyPartial n (l + len) m)) (hrad : s.Rad n V (l + len) c) :
    (sweeneyFlush V A Bp Bn C s).Rad n V l (c + 1) := by
  obtain ⟨hC, hA, hB⟩ := hr
  unfold sweeneyFlush
  have hdn : (((s.dn.mulNat C).toNat : ℕ) : ℝ) = (C : ℝ) * s.dn.toNat := by
    rw [AzNat.toNat_mulNat]; push_cast; ring
  have hrn : (((s.rn.mulNat A).toNat : ℕ) : ℝ) = (A : ℝ) * s.rn.toNat := by
    rw [AzNat.toNat_mulNat]; push_cast; ring
  refine sweeneyTrim_rad hV (Z := sweeneyPartial n l (len + m)) ?_ ?_
    (sweeneyRatio_zero_mul_abs_partial_le n l _)
  · rw [sweeneyPartial_add, ← hA, ← hB]
    refine h.apply (Nat.cast_nonneg A) hC ?_ hdn hrn
    show ((if Bn ≤ Bp then s.nm.mulNat A + (s.dn.mulNat (Bp - Bn)).toAzInt
        else s.nm.mulNat A - (s.dn.mulNat (Bn - Bp)).toAzInt).toInt : ℝ) = _
    split_ifs with hb
    · rw [toInt_add, toInt_mulNat, AzNat.toInt_toAzInt, AzNat.toNat_mulNat]
      push_cast [Nat.cast_sub hb]
      ring
    · rw [toInt_sub, toInt_mulNat, AzNat.toInt_toAzInt, AzNat.toNat_mulNat]
      push_cast [Nat.cast_sub (le_of_not_ge hb)]
      ring
  · exact hrad.apply hC hA hdn hrn

/-- A long block applied to the state, with its truncation. -/
theorem sweeneyApply_rad {V : ℕ} (hV : 1 ≤ V) {n l len m c : ℕ} {M : SweeneyBlock}
    {s : SweeneyState} (hM : M.Repr n l len)
    (h : s.Encl (sweeneyPartial n (l + len) m)) (hrad : s.Rad n V (l + len) c) :
    (sweeneyApply V M s).Rad n V l (c + 1) := by
  obtain ⟨hC, hA, hB⟩ := hM
  unfold sweeneyApply
  have hdn : (((M.C * s.dn).toNat : ℕ) : ℝ) = (M.C.toNat : ℝ) * s.dn.toNat := by
    rw [AzNat.toNat_mul]; push_cast; ring
  have hrn : (((M.A * s.rn).toNat : ℕ) : ℝ) = (M.A.toNat : ℝ) * s.rn.toNat := by
    rw [AzNat.toNat_mul]; push_cast; ring
  refine sweeneyTrim_rad hV (Z := sweeneyPartial n l (len + m)) ?_ ?_
    (sweeneyRatio_zero_mul_abs_partial_le n l _)
  · rw [sweeneyPartial_add, ← hA, ← hB]
    refine h.apply (Nat.cast_nonneg _) hC ?_ hdn hrn
    show ((M.A.toAzInt * s.nm + M.B * s.dn.toAzInt).toInt : ℝ) = _
    rw [toInt_add, toInt_mul, toInt_mul, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt]
    push_cast
    ring
  · exact hrad.apply hC hA hdn hrn

/-! ### The loops -/

/-- The word-block loop: at most one truncation per index, and one at the end. -/
theorem sweeneyHornerLoop_rad {n V N : ℕ} (hV : 1 ≤ V) :
    ∀ (k len A Bp Bn C : ℕ) (s : SweeneyState) (c : ℕ), k + len ≤ N →
      SweeneyRepr n k len A ((Bp : ℝ) - Bn) C →
      s.Encl (sweeneyPartial n (k + len) (N - (k + len))) → s.Rad n V (k + len) c →
      (sweeneyHornerLoop n V k A Bp Bn C s).Rad n V 0 (c + k + 1)
  | 0, len, A, Bp, Bn, C, s, c, hN, hr, hs, hrad => sweeneyFlush_rad hV hr hs hrad
  | k + 1, len, A, Bp, Bn, C, s, c, hN, hr, hs, hrad => by
    have hflush : (sweeneyFlush V A Bp Bn C s).Encl
        (sweeneyPartial n (k + 1) (N - (k + 1))) := by
      have := sweeneyFlush_encl hV hr hs
      rw [← sweeneyPartial_add,
        show len + (N - (k + 1 + len)) = N - (k + 1) by omega] at this
      exact this
    have hflushR : (sweeneyFlush V A Bp Bn C s).Rad n V (k + 1) (c + 1) :=
      sweeneyFlush_rad hV hr hs hrad
    have hs' : s.Encl (sweeneyPartial n (k + (1 + len)) (N - (k + (1 + len)))) := by
      rw [show k + (1 + len) = k + 1 + len by omega]; exact hs
    have hrad' : s.Rad n V (k + (1 + len)) c := by
      rw [show k + (1 + len) = k + 1 + len by omega]; exact hrad
    rw [sweeneyHornerLoop]
    split_ifs with hf hk hk
    · exact (sweeneyHornerLoop_rad (N := N) hV k (1 + len) _ _ _ _ s c (by omega)
        (hr.ext_even hk) hs'
        hrad').mono (by omega)
    · exact (sweeneyHornerLoop_rad (N := N) hV k (1 + len) _ _ _ _ s c (by omega)
        (hr.ext_odd hk) hs'
        hrad').mono (by omega)
    · exact (sweeneyHornerLoop_rad (N := N) hV k 1 _ _ _ _ _ (c + 1) (by omega)
        (sweeneyRepr_single_even hk) hflush hflushR).mono (by omega)
    · exact (sweeneyHornerLoop_rad (N := N) hV k 1 _ _ _ _ _ (c + 1) (by omega)
        (sweeneyRepr_single_odd hk) hflush hflushR).mono (by omega)

/-- The two-level loop. -/
theorem sweeneyHornerLoop₂_rad {n V Lb N : ℕ} (hV : 1 ≤ V) :
    ∀ (k len len' A Bp Bn C : ℕ) (M : SweeneyBlock) (s : SweeneyState) (c : ℕ),
      k + len + len' ≤ N → SweeneyRepr n k len A ((Bp : ℝ) - Bn) C →
      M.Repr n (k + len) len' →
      s.Encl (sweeneyPartial n (k + len + len') (N - (k + len + len'))) →
      s.Rad n V (k + len + len') c →
      (sweeneyHornerLoop₂ n V Lb k A Bp Bn C M s).Rad n V 0 (c + k + 1)
  | 0, len, len', A, Bp, Bn, C, M, s, c, hN, hr, hM, hs, hrad => by
    have hs₀ : s.Encl
        (sweeneyPartial n (0 + (len + len')) (N - (0 + (len + len')))) := by
      rw [← add_assoc]; exact hs
    have hrad₀ : s.Rad n V (0 + (len + len')) c := by
      rw [← add_assoc]; exact hrad
    exact sweeneyApply_rad hV (sweeneyPush_repr hr hM) hs₀ hrad₀
  | k + 1, len, len', A, Bp, Bn, C, M, s, c, hN, hr, hM, hs, hrad => by
    have hpush := sweeneyPush_repr hr hM
    have hs₁ : s.Encl
        (sweeneyPartial n (k + 1 + (len + len')) (N - (k + 1 + (len + len')))) := by
      rw [show k + 1 + (len + len') = k + 1 + len + len' by omega]; exact hs
    have hrad₁ : s.Rad n V (k + 1 + (len + len')) c := by
      rw [show k + 1 + (len + len') = k + 1 + len + len' by omega]; exact hrad
    have happly : (sweeneyApply V (sweeneyPush A Bp Bn C M) s).Encl
        (sweeneyPartial n (k + 1 + 0) (N - (k + 1 + 0))) := by
      have := sweeneyApply_encl hV hpush hs₁
      rw [← sweeneyPartial_add,
        show len + len' + (N - (k + 1 + (len + len'))) = N - (k + 1) by omega] at this
      exact this
    have happlyR : (sweeneyApply V (sweeneyPush A Bp Bn C M) s).Rad n V (k + 1 + 0) (c + 1) :=
      sweeneyApply_rad hV hpush hs₁ hrad₁
    have hs' : s.Encl
        (sweeneyPartial n (k + (1 + len) + len') (N - (k + (1 + len) + len'))) := by
      rw [show k + (1 + len) + len' = k + 1 + len + len' by omega]; exact hs
    have hrad' : s.Rad n V (k + (1 + len) + len') c := by
      rw [show k + (1 + len) + len' = k + 1 + len + len' by omega]; exact hrad
    have hM' : M.Repr n (k + (1 + len)) len' := by
      rw [show k + (1 + len) = k + 1 + len by omega]; exact hM
    rw [sweeneyHornerLoop₂]
    split_ifs with hf hk hL
    · exact (sweeneyHornerLoop₂_rad (N := N) hV k (1 + len) len' _ _ _ _ M s c (by omega)
        (hr.ext_even hk) hM' hs' hrad').mono (by omega)
    · exact (sweeneyHornerLoop₂_rad (N := N) hV k (1 + len) len' _ _ _ _ M s c (by omega)
        (hr.ext_odd hk) hM' hs' hrad').mono (by omega)
    · exact (sweeneyHornerLoop₂_rad (N := N) hV k 1 0 _ _ _ _ _ _ (c + 1) (by omega)
        (sweeneyRepr_single_even (by assumption)) (SweeneyBlock.repr_one n (k + 1)) happly
        happlyR).mono (by omega)
    · exact (sweeneyHornerLoop₂_rad (N := N) hV k 1 0 _ _ _ _ _ _ (c + 1) (by omega)
        (sweeneyRepr_single_odd (by assumption)) (SweeneyBlock.repr_one n (k + 1)) happly
        happlyR).mono (by omega)
    · exact (sweeneyHornerLoop₂_rad (N := N) hV k 1 (len + len') _ _ _ _ _ s c (by omega)
        (sweeneyRepr_single_even (by assumption)) hpush hs₁ hrad₁).mono (by omega)
    · exact (sweeneyHornerLoop₂_rad (N := N) hV k 1 (len + len') _ _ _ _ _ s c (by omega)
        (sweeneyRepr_single_odd (by assumption)) hpush hs₁ hrad₁).mono (by omega)

/-! ### The result -/

/-- **The radius of the truncated recurrence**: at most `sweeneyU n V (N + 1)` times the
denominator. -/
theorem sweeneyHorner_radius (n N : ℕ) {V : ℕ} (hV : 1 ≤ V) (Lb : ℕ) :
    ((sweeneyHorner n N V Lb).rn.toNat : ℝ)
      ≤ sweeneyU n V (N + 1) * (sweeneyHorner n N V Lb).dn.toNat := by
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
  have hrad0 : ∀ l, (⟨0, (1 : AzNat) <<< V, 0⟩ : SweeneyState).Rad n V l 0 := fun l => by
    show sweeneyRatio n 0 l * (((0 : AzNat).toNat : ℕ) : ℝ) ≤ _
    rw [AzNat.toNat_zero, Nat.cast_zero, mul_zero]
    exact mul_nonneg (sweeneyU_nonneg n V 0) (Nat.cast_nonneg _)
  have hr : SweeneyRepr n N 0 ((1 : ℕ) : ℝ) (((0 : ℕ) : ℝ) - (0 : ℕ)) ((1 : ℕ) : ℝ) := by
    have := sweeneyRepr_one n N
    simpa using this
  have key : (sweeneyHorner n N V Lb).Rad n V 0 (0 + N + 1) := by
    unfold sweeneyHorner
    split_ifs with hL
    · exact sweeneyHornerLoop_rad (N := N) hV N 0 1 0 0 1 _ 0 (by omega) hr (by simpa using h0)
        (hrad0 _)
    · exact sweeneyHornerLoop₂_rad (N := N) hV N 0 0 1 0 0 1 _ _ 0 (by omega) hr
        (SweeneyBlock.repr_one n (N + 0)) (by simpa using h0) (hrad0 _)
  unfold SweeneyState.Rad at key
  rw [zero_add] at key
  have h1 : sweeneyRatio n 0 0 = 1 := by simp [sweeneyRatio]
  rwa [h1, one_mul] at key

/-- **The width of `sweeneyHornerEncl`**: the two fractions differ by at most
`2 sweeneyU n V (N + 1)`. -/
theorem sweeneyHornerEncl_width (n N : ℕ) {V : ℕ} (hV : 1 ≤ V) (Lb : ℕ)
    (hS : 0 ≤ ∑ k ∈ range N, sweeneyTerm (n : ℝ) k) :
    ((sweeneyHornerEncl n N V Lb).2.1.toNat : ℝ) / (sweeneyHornerEncl n N V Lb).2.2.toNat
        - ((sweeneyHornerEncl n N V Lb).1.toNat : ℝ) / (sweeneyHornerEncl n N V Lb).2.2.toNat
      ≤ 2 * sweeneyU n V (N + 1) := by
  obtain ⟨hd, hZ⟩ := sweeneyHorner_encl n N hV Lb
  have hrad := sweeneyHorner_radius n N hV Lb
  set S := ∑ k ∈ range N, sweeneyTerm (n : ℝ) k with hSdef
  set s := sweeneyHorner n N V Lb with hs
  have hd' : (0 : ℝ) < s.dn.toNat := by exact_mod_cast hd
  rw [abs_le] at hZ
  have hM0 : (0 : ℝ) ≤ (s.nm.toInt : ℝ) + s.rn.toNat := by
    have := mul_nonneg hS hd'.le
    linarith [hZ.2]
  have hhi : (((s.nm + s.rn.toAzInt).abs.toNat : ℝ)) = (s.nm.toInt : ℝ) + s.rn.toNat := by
    rw [← abs_toInt_real, toInt_add, AzNat.toInt_toAzInt]
    push_cast
    exact abs_of_nonneg hM0
  have hlo : (s.nm.toInt : ℝ) - s.rn.toNat
      ≤ (((if (s.nm - s.rn.toAzInt).sign then (s.nm - s.rn.toAzInt).abs else 0 : AzNat).toNat
        : ℝ)) := by
    split_ifs with hsg
    · have e : ((s.nm - s.rn.toAzInt).toInt : ℝ) = ((s.nm - s.rn.toAzInt).abs.toNat : ℝ) := by
        show (((if (s.nm - s.rn.toAzInt).sign then ((s.nm - s.rn.toAzInt).abs.toNat : ℤ)
          else -((s.nm - s.rn.toAzInt).abs.toNat : ℤ)) : ℤ) : ℝ) = _
        rw [ite_eq_left hsg]
        exact Int.cast_natCast _
      rw [← e, toInt_sub, AzNat.toInt_toAzInt]
      push_cast
      exact le_rfl
    · have e : ((s.nm - s.rn.toAzInt).toInt : ℝ) = -((s.nm - s.rn.toAzInt).abs.toNat : ℝ) := by
        show (((if (s.nm - s.rn.toAzInt).sign then ((s.nm - s.rn.toAzInt).abs.toNat : ℤ)
          else -((s.nm - s.rn.toAzInt).abs.toNat : ℤ)) : ℤ) : ℝ) = _
        rw [ite_eq_right hsg]
        push_cast
        rfl
      rw [toInt_sub, AzNat.toInt_toAzInt] at e
      push_cast at e
      rw [AzNat.toNat_zero, Nat.cast_zero]
      have : (0 : ℝ) ≤ ((s.nm - s.rn.toAzInt).abs.toNat : ℝ) := Nat.cast_nonneg _
      linarith
  show (((s.nm + s.rn.toAzInt).abs.toNat : ℝ)) / s.dn.toNat
    - (((if (s.nm - s.rn.toAzInt).sign then (s.nm - s.rn.toAzInt).abs else 0 : AzNat).toNat
      : ℝ)) / s.dn.toNat ≤ _
  rw [← sub_div, div_le_iff₀ hd', hhi]
  linarith

end Azurite.AzInt
