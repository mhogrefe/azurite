/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PsiZero
import Azurite.AzFloat.Equiv.Digamma
import Azurite.AzFloat.Equiv.ZivSpec
import Azurite.Transcendental.PsiZero

/-!
# Equivalence: the real zeros of the digamma function

`psiZeroPrecRound_eq_or`: `psiZeroPrecRound n p mode` is the correct rounding of the `n`-th
real zero `psiZeroAt n` of `ψ` (`Transcendental/PsiZero.lean`), or `(nan, .eq)` when the fuel of
the Ziv loop runs out.  The steps: `psiZeroInside_zero`, `psiZeroInside_pos` (the float
comparisons place the candidate in the interval of the zero), `psiZeroAround_spec` (the
enclosure from the residual, whatever the candidate), `psiZeroEncl_spec`.
-/

namespace Azurite.AzFloat

open Set

theorem toVal_neg_ofNat (n : ℕ) :
    (-(ofAzNat (AzNat.ofNat n))).toVal = some ((-(n : ℝ) : ℝ) : EReal) := by
  rw [toVal_neg, toVal_ofAzNat_ofNat, Option.map_some, EReal.coe_neg]

/-- The comparisons for `n = 0`: `0 < c ≤ 2`. -/
theorem psiZeroInside_zero {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal))
    (h : psiZeroInside 0 c = true) : 0 < cv ∧ cv ≤ 2 := by
  unfold psiZeroInside at h
  rw [ite_eq_left rfl, Bool.and_eq_true, lt_eq_true_iff toVal_zero' hc,
    le_eq_true_iff hc (toVal_ofAzNat_ofNat 2)] at h
  exact ⟨h.1, by exact_mod_cast h.2⟩

/-- The comparisons for `n ≥ 1`: `c ∈ (−n, −n + 1)`. -/
theorem psiZeroInside_pos {n : ℕ} (hn : 1 ≤ n) {c : AzFloat} {cv : ℝ}
    (hc : c.toVal = some (cv : EReal)) (h : psiZeroInside n c = true) :
    cv ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1) := by
  unfold psiZeroInside at h
  rw [ite_eq_right (by omega), Bool.and_eq_true, lt_eq_true_iff (toVal_neg_ofNat n) hc,
    lt_eq_true_iff hc (toVal_neg_ofNat (n - 1))] at h
  refine ⟨h.1, ?_⟩
  have := h.2
  rw [Nat.cast_sub hn] at this
  push_cast at this
  linarith

/-- **The enclosure around a point of the interval contains the zero**, whatever the point. -/
theorem psiZeroAround_spec {n : ℕ} {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal))
    (hin : psiZeroInside n c = true) {D : Encl} (hD : IsEncl D (DLMF.psiR cv)) {P : ℕ}
    [NeZero P] : IsEncl (psiZeroAround n c D P) (psiZeroAt n) := by
  obtain ⟨d₁, d₂, hd₁, hd₂, h1, h2⟩ := hD
  have hnD : (-D.1).toVal = some ((-d₁ : ℝ) : EReal) := by
    rw [toVal_neg, hd₁, Option.map_some, EReal.coe_neg]
  have hδ := toVal_maxOf hd₂ hnD
  have hδge : |DLMF.psiR cv| ≤ max d₂ (-d₁) := by
    rw [abs_le]
    constructor
    · linarith [le_max_right d₂ (-d₁)]
    · linarith [le_max_left d₂ (-d₁)]
  unfold psiZeroAround
  dsimp only
  have key : ∃ rv : ℝ, (if n = 0 then maxOf D.2 (-D.1) <<< AzInt.ofInt 2
      else maxOf D.2 (-D.1)).toVal = some (rv : EReal) ∧ |psiZeroAt n - cv| ≤ rv := by
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_left rfl]
      obtain ⟨h0, h2'⟩ := psiZeroInside_zero hc hin
      refine ⟨max d₂ (-d₁) * (2 : ℝ) ^ (2 : ℤ), ?_, ?_⟩
      · rw [toVal_shiftLeft_of_toVal hδ, AzInt.toInt_ofInt]
      · have := abs_psiZeroAt_zero_sub_le h0 h2' hδge
        norm_num
        linarith
    · rw [ite_eq_right hn]
      exact ⟨_, hδ, abs_psiZeroAt_sub_le (by omega)
        (psiZeroInside_pos (by omega) hc hin) hδge⟩
  obtain ⟨rv, hr, habs⟩ := key
  rw [abs_le] at habs
  obtain ⟨lo, hlo, hlo1, -⟩ := subFloor_abs hc hr P
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hc hr P
  exact ⟨lo, hi, hlo, hhi, by linarith, by linarith⟩

/-- **Every answer of `psiZeroFast` encloses `xₙ`** (`w ≥ 40`). -/
theorem psiZeroFast_spec (n : ℕ) {w : ℕ} (hw : 40 ≤ w) {b : Encl}
    (h : psiZeroFast n w = some b) : IsEncl b (psiZeroAt n) := by
  unfold psiZeroFast at h
  dsimp only at h
  split_ifs at h with hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hfin, hin⟩ := hc
  obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.mp h
  have hcv := toVal_of_isFinite hfin
  have : NeZero (n.log2 + w + 64) := ⟨by omega⟩
  refine psiZeroAround_spec hcv hin (digammaEncl_spec hcv ?_ ?_ _ (by omega : 64 ≤ w + 24) hD)
  · intro hpos
    have hn : n = 0 := by simpa using hpos
    subst hn
    exact (psiZeroInside_zero hcv hin).1
  · intro hneg
    have hn : 1 ≤ n := by
      have : n ≠ 0 := by simpa using hneg
      omega
    have hmem := psiZeroInside_pos hn hcv hin
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨by linarith [hmem.2], DLMF.not_int_of_mem_Ioo hmem⟩

/-! ### The verified fallback -/

open Filter Topology

theorem two_zpow_neg_nat (k : ℕ) : (2 : ℝ) ^ (-(k : ℤ)) = (1 / 2 : ℝ) ^ k := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- The value of the middle `(2z + 1)/2^(j+1)`. -/
noncomputable def psiZeroMidVal (j : ℕ) (z : ℤ) : ℝ := (2 * (z : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1)

theorem toVal_psiZeroMid (j : ℕ) (a : AzInt) :
    (psiZeroMid j a).toVal = some ((psiZeroMidVal j a.toInt : ℝ) : EReal) := by
  unfold psiZeroMid psiZeroMidVal
  rw [toVal_shiftLeft_of_toVal (toVal_ofAzInt _) _, AzInt.toInt_ofInt, two_zpow_neg_nat,
    AzInt.toInt_add, AzInt.toInt_add, AzInt.toInt_one]
  congr 2
  push_cast
  ring

/-- `[z, z + 1]/2^j` lies in the unit interval of `xₙ`. -/
def PsiZeroIn (n j : ℕ) (z : ℤ) : Prop :=
  (psiZeroLo n : ℝ) ≤ 2 * z * (1 / 2 : ℝ) ^ (j + 1) ∧
    2 * ((z : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1) ≤ psiZeroLo n + 1

/-- `[z, z + 1]/2^j` contains `x`. -/
def PsiZeroHas (x : ℝ) (j : ℕ) (z : ℤ) : Prop :=
  2 * z * (1 / 2 : ℝ) ^ (j + 1) ≤ x ∧ x ≤ 2 * ((z : ℝ) + 1) * (1 / 2 : ℝ) ^ (j + 1)

theorem half_pow_succ' (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1 + 1) = (1 / 2 : ℝ) ^ (j + 1) / 2 := by
  rw [pow_succ]
  ring

theorem PsiZeroIn.init (n : ℕ) : PsiZeroIn n 0 (psiZeroLo n) := by
  unfold PsiZeroIn
  rw [zero_add, pow_one]
  constructor <;> linarith

theorem PsiZeroIn.mid {n j : ℕ} {z : ℤ} (h : PsiZeroIn n j z) :
    (psiZeroLo n : ℝ) + (1 / 2 : ℝ) ^ (j + 1) ≤ psiZeroMidVal j z ∧
      psiZeroMidVal j z + (1 / 2 : ℝ) ^ (j + 1) ≤ psiZeroLo n + 1 := by
  obtain ⟨h1, h2⟩ := h
  unfold psiZeroMidVal
  constructor <;> linarith

theorem PsiZeroIn.right {n j : ℕ} {z : ℤ} (h : PsiZeroIn n j z) :
    PsiZeroIn n (j + 1) (2 * z + 1) := by
  obtain ⟨h1, h2⟩ := h
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  unfold PsiZeroIn
  rw [half_pow_succ']
  push_cast
  constructor <;> linarith

theorem PsiZeroIn.left {n j : ℕ} {z : ℤ} (h : PsiZeroIn n j z) :
    PsiZeroIn n (j + 1) (2 * z) := by
  obtain ⟨h1, h2⟩ := h
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
  unfold PsiZeroIn
  rw [half_pow_succ']
  push_cast
  constructor <;> linarith

theorem PsiZeroHas.mid {x : ℝ} {j : ℕ} {z : ℤ} (h : PsiZeroHas x j z) :
    |psiZeroMidVal j z - x| ≤ (1 / 2 : ℝ) ^ (j + 1) := by
  obtain ⟨h1, h2⟩ := h
  unfold psiZeroMidVal
  rw [abs_le]
  constructor <;> linarith

theorem PsiZeroHas.right {x : ℝ} {j : ℕ} {z : ℤ} (h : PsiZeroHas x j z)
    (hm : psiZeroMidVal j z ≤ x) : PsiZeroHas x (j + 1) (2 * z + 1) := by
  obtain ⟨h1, h2⟩ := h
  unfold psiZeroMidVal at hm
  unfold PsiZeroHas
  rw [half_pow_succ']
  push_cast
  constructor <;> linarith

theorem PsiZeroHas.left {x : ℝ} {j : ℕ} {z : ℤ} (h : PsiZeroHas x j z)
    (hm : x ≤ psiZeroMidVal j z) : PsiZeroHas x (j + 1) (2 * z) := by
  obtain ⟨h1, h2⟩ := h
  unfold psiZeroMidVal at hm
  unfold PsiZeroHas
  rw [half_pow_succ']
  push_cast
  constructor <;> linarith

theorem toInt_double_add_one (a : AzInt) : (a + a + 1).toInt = 2 * a.toInt + 1 := by
  rw [AzInt.toInt_add, AzInt.toInt_add, AzInt.toInt_one, ← two_mul]

theorem toInt_double (a : AzInt) : (a + a).toInt = 2 * a.toInt := by
  rw [AzInt.toInt_add, ← two_mul]

theorem abs_psiZeroLo_le (n : ℕ) : |(psiZeroLo n : ℝ)| ≤ n + 1 := by
  unfold psiZeroLo
  by_cases hn : n = 0
  · subst hn
    norm_num
  · rw [ite_eq_right hn]
    push_cast
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    linarith

/-- A float strictly inside the unit interval is inside the interval of `xₙ`, and `ψ` has
its enclosures there. -/
theorem psiZeroLo_inside {n : ℕ} {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal))
    (h1 : (psiZeroLo n : ℝ) < cv) (h2 : cv < psiZeroLo n + 1) :
    psiZeroInside n c = true ∧ (decide (n = 0) = true → 0 < cv) ∧
      (decide (n = 0) = false → cv < 0 ∧ ∀ k : ℤ, cv ≠ k) := by
  by_cases hn : n = 0
  · subst hn
    have hL : (psiZeroLo 0 : ℝ) = 1 := by simp [psiZeroLo]
    rw [hL] at h1 h2
    refine ⟨?_, fun _ => by linarith, fun h => absurd h (by simp)⟩
    unfold psiZeroInside
    rw [ite_eq_left rfl, Bool.and_eq_true, lt_eq_true_iff toVal_zero' hc,
      le_eq_true_iff hc (toVal_ofAzNat_ofNat 2)]
    refine ⟨by linarith, ?_⟩
    push_cast
    linarith
  · have hL : (psiZeroLo n : ℝ) = -(n : ℝ) := by simp [psiZeroLo, hn]
    rw [hL] at h1 h2
    have hn1 : 1 ≤ n := by omega
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    refine ⟨?_, fun h => absurd h (by simp [hn]),
      fun _ => ⟨by linarith, DLMF.not_int_of_mem_Ioo ⟨h1, h2⟩⟩⟩
    unfold psiZeroInside
    rw [ite_eq_right hn, Bool.and_eq_true, lt_eq_true_iff (toVal_neg_ofNat n) hc,
      lt_eq_true_iff hc (toVal_neg_ofNat (n - 1)), Nat.cast_sub hn1]
    push_cast
    constructor <;> linarith

/-- **The bisection ends at a middle inside the unit interval**, with an enclosure of `ψ`
there. -/
theorem psiZeroBisect_sound (n W : ℕ) (e : AzInt) :
    ∀ (k j : ℕ) (a : AzInt), PsiZeroIn n j a.toInt → ∀ {c : AzFloat} {D : Encl},
      psiZeroBisect n W e k j a = some (c, D) →
      ∃ (j' : ℕ) (a' : AzInt), PsiZeroIn n j' a'.toInt ∧ c = psiZeroMid j' a' ∧
        digammaEncl c e (decide (n = 0)) W = some D
  | 0, j, a, hI, c, D, h => by
    rw [psiZeroBisect] at h
    obtain ⟨D', hD', heq⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨j, a, hI, rfl, hD'⟩
  | k + 1, j, a, hI, c, D, h => by
    rw [psiZeroBisect] at h
    split at h
    · exact absurd h (by simp)
    · rename_i D' hD'
      split_ifs at h with c1 c2
      · exact psiZeroBisect_sound n W e k (j + 1) (a + a + 1)
          (by rw [toInt_double_add_one]; exact hI.right) h
      · exact psiZeroBisect_sound n W e k (j + 1) (a + a)
          (by rw [toInt_double]; exact hI.left) h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨j, a, hI, rfl, hD'⟩

/-- **The bisection follows the zero**: when `ψ` has enclosures of width `ε` at all the
middles around `x`, the bisection ends at such a middle — after all its steps, or at an
enclosure that contains `0`. -/
theorem psiZeroBisect_complete (n W : ℕ) (e : AzInt) {x ε : ℝ}
    (hmono : ∀ cv : ℝ, (psiZeroLo n : ℝ) < cv → cv < psiZeroLo n + 1 →
      (DLMF.psiR cv < 0 → cv ≤ x) ∧ (0 < DLMF.psiR cv → x ≤ cv))
    (H : ∀ (j : ℕ) (a : AzInt), PsiZeroIn n j a.toInt → PsiZeroHas x j a.toInt →
      ∃ D, digammaEncl (psiZeroMid j a) e (decide (n = 0)) W = some D ∧
        AEncl D (DLMF.psiR (psiZeroMidVal j a.toInt)) ε) :
    ∀ (k j : ℕ) (a : AzInt), PsiZeroIn n j a.toInt → PsiZeroHas x j a.toInt →
      ∃ (j' : ℕ) (a' : AzInt) (D : Encl) (l h : ℝ), PsiZeroIn n j' a'.toInt ∧
        PsiZeroHas x j' a'.toInt ∧
        psiZeroBisect n W e k j a = some (psiZeroMid j' a', D) ∧
        D.1.toVal = some (l : EReal) ∧ D.2.toVal = some (h : EReal) ∧
        l ≤ DLMF.psiR (psiZeroMidVal j' a'.toInt) ∧
        DLMF.psiR (psiZeroMidVal j' a'.toInt) ≤ h ∧ h - l ≤ ε ∧
        (j + k ≤ j' ∨ (l ≤ 0 ∧ 0 ≤ h))
  | 0, j, a, hI, hZ => by
    obtain ⟨D, hD, l, h, hl, hh, h1, h2, h3⟩ := H j a hI hZ
    refine ⟨j, a, D, l, h, hI, hZ, ?_, hl, hh, h1, h2, h3, Or.inl le_rfl⟩
    rw [psiZeroBisect, hD, Option.map_some]
  | k + 1, j, a, hI, hZ => by
    obtain ⟨D, hD, l, h, hl, hh, h1, h2, h3⟩ := H j a hI hZ
    obtain ⟨hm1, hm2⟩ := hI.mid
    have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
    obtain ⟨hneg, hpos⟩ := hmono (psiZeroMidVal j a.toInt) (by linarith) (by linarith)
    rw [psiZeroBisect, hD]
    dsimp only
    by_cases c1 : lt D.2 zero = true
    · rw [ite_eq_left c1]
      have hh0 : h < 0 := (lt_eq_true_iff hh toVal_zero').mp c1
      obtain ⟨j', a', D', l', h', i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ :=
        psiZeroBisect_complete n W e hmono H k (j + 1) (a + a + 1)
          (by rw [toInt_double_add_one]; exact hI.right)
          (by rw [toInt_double_add_one]; exact hZ.right (hneg (by linarith)))
      exact ⟨j', a', D', l', h', i1, i2, i3, i4, i5, i6, i7, i8,
        i9.imp_left fun hle => by omega⟩
    · rw [ite_eq_right c1]
      by_cases c2 : lt zero D.1 = true
      · rw [ite_eq_left c2]
        have hl0 : 0 < l := (lt_eq_true_iff toVal_zero' hl).mp c2
        obtain ⟨j', a', D', l', h', i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ :=
          psiZeroBisect_complete n W e hmono H k (j + 1) (a + a)
            (by rw [toInt_double]; exact hI.left)
            (by rw [toInt_double]; exact hZ.left (hpos (by linarith)))
        exact ⟨j', a', D', l', h', i1, i2, i3, i4, i5, i6, i7, i8,
          i9.imp_left fun hle => by omega⟩
      · rw [ite_eq_right c2]
        have hh0 : 0 ≤ h := not_lt.mp fun hlt => c1 ((lt_eq_true_iff hh toVal_zero').mpr hlt)
        have hl0 : l ≤ 0 := not_lt.mp fun hlt => c2 ((lt_eq_true_iff toVal_zero' hl).mpr hlt)
        exact ⟨j, a, D, l, h, hI, hZ, rfl, hl, hh, h1, h2, h3, Or.inr ⟨hl0, hh0⟩⟩

/-- **The width of the enclosure around a point**: `8δ` and the two roundings, when the
enclosure of `ψ` there is within `δ` of `0`. -/
theorem psiZeroAround_width {n : ℕ} {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal))
    (hin : psiZeroInside n c = true) (hcv : |cv| ≤ n + 2) {D : Encl} {l h δ : ℝ}
    (hl : D.1.toVal = some (l : EReal)) (hh : D.2.toVal = some (h : EReal))
    (h1 : l ≤ DLMF.psiR cv) (h2 : DLMF.psiR cv ≤ h) (hδ : max h (-l) ≤ δ) {P : ℕ}
    [NeZero P] :
    AEncl (psiZeroAround n c D P) (psiZeroAt n)
      (8 * δ + 4 * (n + 2 + 4 * δ) * (1 / 2 : ℝ) ^ P) := by
  have hspec := psiZeroAround_spec hc hin ⟨l, h, hl, hh, h1, h2⟩ (P := P)
  have hnD : (-D.1).toVal = some ((-l : ℝ) : EReal) := by
    rw [toVal_neg, hl, Option.map_some, EReal.coe_neg]
  have hm := toVal_maxOf hh hnD
  have hm0 : 0 ≤ max h (-l) := by
    rcases le_total 0 h with h0 | h0
    · exact h0.trans (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_right h (-l))
  have key : ∃ rv : ℝ, (if n = 0 then maxOf D.2 (-D.1) <<< AzInt.ofInt 2
      else maxOf D.2 (-D.1)).toVal = some (rv : EReal) ∧ 0 ≤ rv ∧ rv ≤ 4 * δ := by
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      refine ⟨max h (-l) * (2 : ℝ) ^ (2 : ℤ), ?_, by positivity, ?_⟩
      · rw [toVal_shiftLeft_of_toVal hm, AzInt.toInt_ofInt]
      · norm_num
        linarith
    · rw [ite_eq_right hn]
      exact ⟨_, hm, hm0, by linarith⟩
  obtain ⟨rv, hr, hr0, hr4⟩ := key
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hc hr P
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hc hr P
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ P := by positivity
  have ha1 : |cv - rv| ≤ n + 2 + 4 * δ := by
    have := abs_sub cv rv
    rw [abs_of_nonneg hr0] at this
    linarith
  have ha2 : |cv + rv| ≤ n + 2 + 4 * δ := by
    have := abs_add_le cv rv
    rw [abs_of_nonneg hr0] at this
    linarith
  have hb1 := mul_le_mul_of_nonneg_right ha1 hu0
  have hb2 := mul_le_mul_of_nonneg_right ha2 hu0
  have hA : AEncl (psiZeroAround n c D P) cv
      (8 * δ + 4 * (n + 2 + 4 * δ) * (1 / 2 : ℝ) ^ P) :=
    ⟨lo, hi, hlo, hhi, by linarith, by linarith, by linarith⟩
  exact hA.of_isEncl hspec

/-- **Every answer of the fallback encloses `xₙ`** (`w ≥ 40`). -/
theorem psiZeroFallback_spec (n : ℕ) {w : ℕ} (hw : 40 ≤ w) {b : Encl}
    (h : psiZeroFallback n w = some b) : IsEncl b (psiZeroAt n) := by
  unfold psiZeroFallback at h
  obtain ⟨⟨c, D⟩, hB, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨j', a', hI, rfl, hD⟩ := psiZeroBisect_sound n _ _ _ 0 _
    (by rw [AzInt.toInt_ofInt]; exact PsiZeroIn.init n) hB
  obtain ⟨hm1, hm2⟩ := hI.mid
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j' + 1) := by positivity
  have hc := toVal_psiZeroMid j' a'
  obtain ⟨hin, hpos, hneg⟩ := psiZeroLo_inside hc (by linarith) (by linarith)
  have : NeZero (n.log2 + w + 64) := ⟨by omega⟩
  exact psiZeroAround_spec hc hin (digammaEncl_spec hc hpos hneg _ (by omega) hD)

/-- A narrow enclosure has width at most `2^(−⌊w/2⌋)`. -/
theorem psiZeroNarrow_spec {b : Encl} {x : ℝ} (hb : IsEncl b x) {w : ℕ}
    (h : psiZeroNarrow b w = true) : AEncl b x ((1 / 2 : ℝ) ^ (w / 2)) := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := hb
  obtain ⟨r, hr, hr1, -⟩ := subCeiling_abs hu hl 64
  unfold psiZeroNarrow at h
  rw [le_eq_true_iff hr (toVal_powerOf2 _), AzInt.toInt_ofInt, two_zpow_neg_nat] at h
  exact ⟨l, u, hl, hu, h1, h2, hr1.trans h⟩

/-- **Every answer of `psiZeroEncl` encloses `xₙ`** (`w ≥ 40`). -/
theorem psiZeroEncl_spec (n : ℕ) {w : ℕ} (hw : 40 ≤ w) {b : Encl}
    (h : psiZeroEncl n w = some b) : IsEncl b (psiZeroAt n) := by
  unfold psiZeroEncl at h
  split at h
  · rename_i b' hf
    rw [Option.some.injEq] at h
    subst h
    exact psiZeroFast_spec n hw (Option.filter_eq_some_iff.mp hf).1
  · exact psiZeroFallback_spec n hw h

/-- The zero `xₙ` in its unit interval, where `ψ` is increasing; `ψ` is continuous at `xₙ`. -/
theorem psiZeroAt_facts (n : ℕ) :
    (psiZeroLo n : ℝ) < psiZeroAt n ∧ psiZeroAt n < psiZeroLo n + 1 ∧
      DLMF.psiR (psiZeroAt n) = 0 ∧
      MonotoneOn DLMF.psiR (Ioo (psiZeroLo n : ℝ) (psiZeroLo n + 1)) ∧
      ContinuousAt DLMF.psiR (psiZeroAt n) := by
  by_cases hn : n = 0
  · subst hn
    have hL : (psiZeroLo 0 : ℝ) = 1 := by simp [psiZeroLo]
    obtain ⟨h1, h2, hz⟩ := psiZeroPos_spec
    rw [hL, psiZeroAt_zero]
    refine ⟨h1, by linarith, hz, ?_, ?_⟩
    · exact DLMF.psiR_mono.mono fun y hy => mem_Ioi.mpr (by linarith [hy.1])
    · refine DLMF.continuousAt_psiR fun m h => ?_
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  · have hL : (psiZeroLo n : ℝ) = -(n : ℝ) := by simp [psiZeroLo, hn]
    have hn1 : 1 ≤ n := by omega
    obtain ⟨hmem, hz⟩ := DLMF.psiZero_spec hn1
    rw [hL, psiZeroAt_of_pos hn1]
    exact ⟨hmem.1, hmem.2, hz, (DLMF.psiR_strictMonoOn hn1).monotoneOn,
      DLMF.continuousAt_psiR (DLMF.not_neg_nat_of_mem_Ioo hmem)⟩

theorem sin_ge_of_mem {d a : ℝ} (hd : 0 < d) (h1 : d ≤ a) (h2 : a ≤ 1 - d) :
    Real.sin (d * Real.pi) ≤ Real.sin (a * Real.pi) := by
  have hpi := Real.pi_pos
  have hd2 : d ≤ 1 / 2 := by linarith
  rcases le_total a (1 / 2) with ha | ha
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith)
      (mul_le_mul_of_nonneg_right h1 hpi.le)
  · rw [← Real.sin_pi_sub (a * Real.pi)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith) (by nlinarith) (by nlinarith)

/-- **`ψ` has enclosures of one width at all the middles around `xₙ`**, a width that tends to
`0` with the level. -/
theorem psiZeroMid_digamma_unif (n : ℕ) (e : AzInt) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ W in atTop, ∀ (j : ℕ) (a : AzInt),
      PsiZeroIn n j a.toInt → PsiZeroHas (psiZeroAt n) j a.toInt →
      ∃ D, digammaEncl (psiZeroMid j a) e (decide (n = 0)) W = some D ∧
        AEncl D (DLMF.psiR (psiZeroMidVal j a.toInt)) (E W) := by
  obtain ⟨hx1, hx2, -, -, -⟩ := psiZeroAt_facts n
  by_cases hn : n = 0
  · subst hn
    have hL : (psiZeroLo 0 : ℝ) = 1 := by simp [psiZeroLo]
    refine ⟨dgEU 1 2 e, tendsto_dgEU 1 2 e, ?_⟩
    filter_upwards [digammaPosEncl_conv_unif (α := 1) (β := 2) one_pos e] with W hW
    intro j a hI _
    obtain ⟨hm1, hm2⟩ := hI.mid
    rw [hL] at hm1 hm2
    have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
    refine ⟨_, by simp [digammaEncl], hW _ (by linarith) (by linarith) _ 0
      (LEncl.exact (toVal_psiZeroMid j a) (by linarith)) le_rfl (by positivity)⟩
  · have hL : (psiZeroLo n : ℝ) = -(n : ℝ) := by simp [psiZeroLo, hn]
    rw [hL] at hx1 hx2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = psiZeroAt n := ⟨_, rfl⟩
    rw [← hxdef] at hx1 hx2 ⊢
    obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = min (x + n) (-(n : ℝ) + 1 - x) / 2 := ⟨_, rfl⟩
    have hd0 : 0 < d := by
      rw [hddef]
      exact half_pos (lt_min (by linarith) (by linarith))
    have hdl : 2 * d ≤ x + n := by rw [hddef]; linarith [min_le_left (x + n) (-(n : ℝ) + 1 - x)]
    have hdr : 2 * d ≤ -(n : ℝ) + 1 - x := by
      rw [hddef]; linarith [min_le_right (x + n) (-(n : ℝ) + 1 - x)]
    have hsmin : 0 < Real.sin (d * Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hd0 Real.pi_pos) (by nlinarith [Real.pi_pos])
    obtain ⟨e', he'⟩ : ∃ e' : AzInt, e' = (if e.sign then e else 0) + 1 := ⟨_, rfl⟩
    obtain ⟨E, hE, hev⟩ := digammaReflect_unif
      (Pmax := max |DLMF.psiR n| |DLMF.psiR ((n : ℝ) + 1)|) hsmin
      (tendsto_dgEU n ((n : ℝ) + 1) e')
    refine ⟨E, hE, ?_⟩
    filter_upwards [hev, digammaPosEncl_conv_unif (α := n) (β := (n : ℝ) + 1)
      (by linarith) e', eventually_ge_atTop 64] with W hR hP hW
    intro j a hI hZ
    obtain ⟨hm1, hm2⟩ := hI.mid
    rw [hL] at hm1 hm2
    have hmx := abs_le.mp hZ.mid
    have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 1) := by positivity
    have hc := toVal_psiZeroMid j a
    obtain ⟨cv, hcv⟩ : ∃ cv : ℝ, cv = psiZeroMidVal j a.toInt := ⟨_, rfl⟩
    rw [← hcv] at hm1 hm2 hmx hc ⊢
    have hc1 : -(n : ℝ) + d ≤ cv := by linarith
    have hc2 : cv + d ≤ -(n : ℝ) + 1 := by linarith
    have hneg : cv < 0 := by linarith
    have hni : ∀ k : ℤ, cv ≠ k := DLMF.not_int_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hk1 := gammaNearInt_spec hc
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (gammaNearInt (psiZeroMid j a)).toInt := ⟨_, rfl⟩
    rw [← hk] at hk1
    have hkk := abs_lt.mp hk1
    have hka : -(n : ℤ) ≤ k := by
      have : (-(n : ℝ) - 1) < k := by linarith
      have : (-(n : ℤ) - 1) < k := by exact_mod_cast this
      omega
    have hkb : k ≤ -(n : ℤ) + 1 := by
      have : (k : ℝ) < -(n : ℝ) + 2 := by linarith
      have : k < -(n : ℤ) + 2 := by exact_mod_cast this
      omega
    have ha : d ≤ |cv - k| ∧ |cv - k| ≤ 1 - d := by
      rcases (by omega : k = -(n : ℤ) ∨ k = -(n : ℤ) + 1) with hkv | hkv
      · rw [hkv]
        push_cast
        rw [abs_of_nonneg (by linarith)]
        constructor <;> linarith
      · rw [hkv]
        push_cast
        rw [abs_of_nonpos (by linarith)]
        constructor <;> linarith
    have ha0 : 0 < |cv - k| := lt_of_lt_of_le hd0 ha.1
    have hd : cv - (k : ℝ) ≠ 0 := abs_pos.mp ha0
    have hnx : (-(psiZeroMid j a)).toVal = some ((-cv : ℝ) : EReal) := by
      rw [toVal_neg, hc, Option.map_some, EReal.coe_neg]
    have hpv : |DLMF.psiR (-cv + 1)| ≤ max |DLMF.psiR n| |DLMF.psiR ((n : ℝ) + 1)| := by
      have hn0 : (0 : ℝ) < n := by linarith
      have g1 := DLMF.psiR_mono (mem_Ioi.mpr hn0) (mem_Ioi.mpr (by linarith : (0 : ℝ) < -cv + 1))
        (by linarith : (n : ℝ) ≤ -cv + 1)
      have g2 := DLMF.psiR_mono (mem_Ioi.mpr (by linarith : (0 : ℝ) < -cv + 1))
        (mem_Ioi.mpr (by linarith : (0 : ℝ) < (n : ℝ) + 1)) (by linarith : -cv + 1 ≤ (n : ℝ) + 1)
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (DLMF.psiR n), le_max_left |DLMF.psiR n| |DLMF.psiR ((n : ℝ) + 1)|]
      · linarith [le_abs_self (DLMF.psiR ((n : ℝ) + 1)),
          le_max_right |DLMF.psiR n| |DLMF.psiR ((n : ℝ) + 1)|]
    have hPA : AEncl (digammaPosEncl (Encl.add (W + 32) (Encl.exact (-(psiZeroMid j a)))
        (Encl.exact one)) e' W) (DLMF.psiR (-cv + 1)) (dgEU n ((n : ℝ) + 1) e' W) := by
      have : NeZero (W + 32) := ⟨by omega⟩
      have hu32 : (1 / 2 : ℝ) ^ (W + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
      have hXL := LEncl.add_exact (w := W + 32) (b := Encl.exact one) hu32
        (LEncl.exact hnx (by linarith)) le_rfl toVal_one' toVal_one' zero_le_one
      rw [zero_add] at hXL
      exact hP _ (by linarith) (by linarith) _ _ hXL (by positivity) (six_le_eight W)
    have hF : ∃ (σ : Bool) (A : Encl),
        gammaFracEncl (psiZeroMid j a) (gammaNearInt (psiZeroMid j a)) (W + 16) = some (σ, A) ∧
        LEncl A |cv - k| (6 * (1 / 2 : ℝ) ^ (W + 16)) := by
      have : NeZero (W + 16) := ⟨by omega⟩
      obtain ⟨σ, A, hF, hA⟩ := gammaFracEncl_some hc (gammaNearInt (psiZeroMid j a))
        (by rw [← hk]; exact hd) (W := W + 16)
        ((half_pow_le_of_64 (by omega : 64 ≤ W + 16)).trans (by norm_num))
      rw [sign_mul_eq_abs hA.pos, ← hk] at hA
      exact ⟨σ, A, hF, hA⟩
    obtain ⟨b, v, hb, hA⟩ := hR |cv - k| (DLMF.psiR (-cv + 1)) _ _ ha0 (by linarith [ha.2])
      (sin_ge_of_mem hd0 ha.1 ha.2) hpv hPA hF
    have hsome : digammaNegEncl (psiZeroMid j a) e W = some b := by
      unfold digammaNegEncl
      rw [← he']
      exact hb
    refine ⟨b, ?_, hA.of_isEncl (digammaNegEncl_spec hc hneg hni e hW hsome)⟩
    unfold digammaEncl
    rw [ite_eq_right (by simp [hn])]
    exact hsome

/-- **The fallback converges**: for every `ε > 0` it encloses `xₙ` within `ε` at all large
levels. -/
theorem psiZeroFallback_conv (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∃ b, psiZeroFallback n w = some b ∧ AEncl b (psiZeroAt n) ε := by
  obtain ⟨hx1, hx2, hz, hmonoOn, hcont⟩ := psiZeroAt_facts n
  obtain ⟨E, hE, hev⟩ := psiZeroMid_digamma_unif n (AzInt.ofInt ((n.log2 + 1 : ℕ) : ℤ))
  obtain ⟨η, hη0, hη⟩ := Metric.continuousAt_iff.mp hcont (ε / 32) (by positivity)
  have hu : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 9)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 9)
  have hT : Tendsto (fun w : ℕ => 4 * ((n : ℝ) + 2 + ε / 4) * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (4 * ((n : ℝ) + 2 + ε / 4))
    rwa [mul_zero] at this
  have hmono : ∀ cv : ℝ, (psiZeroLo n : ℝ) < cv → cv < psiZeroLo n + 1 →
      (DLMF.psiR cv < 0 → cv ≤ psiZeroAt n) ∧ (0 < DLMF.psiR cv → psiZeroAt n ≤ cv) := by
    intro cv h1 h2
    constructor
    · intro hlt
      by_contra hc
      have := hmonoOn ⟨hx1, hx2⟩ ⟨h1, h2⟩ (not_le.mp hc).le
      linarith
    · intro hlt
      by_contra hc
      have := hmonoOn ⟨h1, h2⟩ ⟨hx1, hx2⟩ (not_le.mp hc).le
      linarith
  filter_upwards [(tendsto_add_atTop_nat 24).eventually hev,
    (hE.comp (tendsto_add_atTop_nat 24)).eventually (ge_mem_nhds (by positivity : 0 < ε / 32)),
    hu.eventually (gt_mem_nhds hη0), hT.eventually (ge_mem_nhds (by positivity : 0 < ε / 4))]
    with w hH hEw hηw hTw
  obtain ⟨j', a', D, l, h, hI, hZ, hB, hl, hh, h1, h2, h3, hor⟩ :=
    psiZeroBisect_complete n (w + 24) _ hmono hH (w + 8) 0 (AzInt.ofInt (psiZeroLo n))
      (by rw [AzInt.toInt_ofInt]; exact PsiZeroIn.init n)
      (by
        rw [AzInt.toInt_ofInt]
        unfold PsiZeroHas
        rw [zero_add, pow_one]
        constructor <;> linarith)
  obtain ⟨hm1, hm2⟩ := hI.mid
  have hmx := hZ.mid
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j' + 1) := by positivity
  have hc := toVal_psiZeroMid j' a'
  obtain ⟨cv, hcv⟩ : ∃ cv : ℝ, cv = psiZeroMidVal j' a'.toInt := ⟨_, rfl⟩
  rw [← hcv] at hm1 hm2 hmx hc h1 h2
  obtain ⟨hin, -, -⟩ := psiZeroLo_inside hc (by linarith) (by linarith)
  have hEw' : E (w + 24) ≤ ε / 32 := hEw
  have hpsi : |DLMF.psiR cv| ≤ ε / 32 := by
    rcases hor with hj | ⟨hl0, hh0⟩
    · have hle : (1 / 2 : ℝ) ^ (j' + 1) ≤ (1 / 2 : ℝ) ^ (w + 9) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hdist : dist cv (psiZeroAt n) < η := by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hmx.trans hle) hηw
      have := hη hdist
      rw [Real.dist_eq, hz, sub_zero] at this
      exact this.le
    · rw [abs_le]
      constructor <;> linarith
  have hpsi' := abs_le.mp hpsi
  have hδ : max h (-l) ≤ ε / 16 := max_le (by linarith) (by linarith)
  have hcvb : |cv| ≤ n + 2 := by
    have := abs_le.mp (abs_psiZeroLo_le n)
    rw [abs_le]
    constructor <;> linarith
  have : NeZero (n.log2 + w + 64) := ⟨by omega⟩
  have hA := psiZeroAround_width hc hin hcvb hl hh h1 h2 hδ (P := n.log2 + w + 64)
  refine ⟨_, ?_, hA.mono ?_⟩
  · unfold psiZeroFallback
    rw [hB, Option.map_some]
  · have hle : (1 / 2 : ℝ) ^ (n.log2 + w + 64) ≤ (1 / 2 : ℝ) ^ w :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hc0 : (0 : ℝ) ≤ 4 * ((n : ℝ) + 2 + 4 * (ε / 16)) := by positivity
    have := mul_le_mul_of_nonneg_left hle hc0
    have hTw' : 4 * ((n : ℝ) + 2 + ε / 4) * (1 / 2 : ℝ) ^ w ≤ ε / 4 := hTw
    rw [show 4 * (ε / 16) = ε / 4 by ring] at this ⊢
    linarith

/-- **The enclosure of `xₙ` converges**: within every `ε > 0` at all large levels. -/
theorem psiZeroEncl_conv (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∃ b, psiZeroEncl n w = some b ∧ AEncl b (psiZeroAt n) ε := by
  have hhalf : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w / 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_atTop.mpr fun b => (eventually_ge_atTop (2 * b)).mono fun w hw =>
        (Nat.le_div_iff_mul_le two_pos).mpr (by omega))
  filter_upwards [psiZeroFallback_conv n hε, hhalf.eventually (ge_mem_nhds hε),
    eventually_ge_atTop 40] with w hF hw2 hw
  unfold psiZeroEncl
  split
  · rename_i b hf
    obtain ⟨hfast, hnar⟩ := Option.filter_eq_some_iff.mp hf
    exact ⟨b, rfl, (psiZeroNarrow_spec (psiZeroFast_spec n hw hfast) hnar).mono hw2⟩
  · exact hF

/-- The width of an enclosure with finite ends. -/
noncomputable def enclWidth (b : Encl) : ℝ :=
  (b.2.toVal.getD 0).toReal - (b.1.toVal.getD 0).toReal

theorem AEncl.enclWidth {b : Encl} {v ε : ℝ} (h : AEncl b v ε) :
    AEncl b v (enclWidth b) ∧ Azurite.AzFloat.enclWidth b ≤ ε ∧
      0 ≤ Azurite.AzFloat.enclWidth b := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  have hw : Azurite.AzFloat.enclWidth b = u - l := by
    unfold Azurite.AzFloat.enclWidth
    rw [hl, hu]
    simp only [Option.getD_some, EReal.toReal_coe]
  rw [hw]
  exact ⟨⟨l, u, hl, hu, h1, h2, le_rfl⟩, h3, by linarith⟩

/-- Enclosures within every `ε` at all large levels have widths that tend to `0`. -/
theorem exists_width_of_forall_eps {c : ℕ → Option Encl} {v : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∃ b, c w = some b ∧ AEncl b v ε) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ w in atTop, ∃ b, c w = some b ∧ AEncl b v (E w) := by
  refine ⟨fun w => ((c w).map enclWidth).getD 0, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h (ε / 2) (half_pos hε))
    refine ⟨N, fun w hw => ?_⟩
    obtain ⟨b, hb, hA⟩ := hN w hw
    obtain ⟨-, h2, h3⟩ := hA.enclWidth
    simp only [hb, Option.map_some, Option.getD_some, Real.dist_eq, sub_zero]
    rw [abs_of_nonneg h3]
    linarith
  · filter_upwards [h 1 one_pos] with w ⟨b, hb, hA⟩
    refine ⟨b, hb, ?_⟩
    simp only [hb, Option.map_some, Option.getD_some]
    exact hA.enclWidth.1

/-- **The bracket of `xₙ` converges.** -/
theorem psiZeroApprox_bracketConv (n : ℕ) : BracketConv (psiZeroApprox n) (psiZeroAt n) :=
  lnAbsGammaApproxOf_bracketConv
    (exists_width_of_forall_eps fun _ hε => psiZeroEncl_conv n hε)

/-- **The zeros of `ψ` are correctly rounded, or the fuel ran out**, at every fuel. -/
theorem psiZeroPrecRoundFuel_eq_or (fuel n p : ℕ) [NeZero p] (mode : RoundingMode) :
    psiZeroPrecRoundFuel fuel n p mode
        = roundVal p mode (some ((psiZeroAt n : ℝ) : EReal)) ∨
      psiZeroPrecRoundFuel fuel n p mode = (nan, .eq) := by
  unfold psiZeroPrecRoundFuel
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop (psiZeroApprox n) p mode fuel (max 64 (p + 32)))
    (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => lnAbsGammaApproxOf_valid_or_none
        (fun _ hc => psiZeroEncl_spec n (by omega) hc) w p mode)
      _ _ (le_max_left _ _) hz

/-- **The zeros of `ψ` are correctly rounded, or the fuel ran out.** -/
theorem psiZeroPrecRound_eq_or (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    psiZeroPrecRound n p mode = roundVal p mode (some ((psiZeroAt n : ℝ) : EReal)) ∨
      psiZeroPrecRound n p mode = (nan, .eq) :=
  psiZeroPrecRoundFuel_eq_or (lnGammaFuel p) n p mode

/-- **The specification of the zeros of `ψ`** (`ZivSpec`): sound at every fuel, and complete
in the limit of the fuel wherever the zero is no rounding boundary — by the verified
bisection behind the fast enclosure.  Nothing is known about the arithmetic nature of the
zeros, so the sets of known values are empty. -/
theorem psiZeroPrecRoundFuel_zivSpec :
    ZivSpec (fun n : ℕ => some ((psiZeroAt n : ℝ) : EReal)) psiZeroPrecRoundFuel ∅ ∅ where
  sound := fun fuel n p _ mode => psiZeroPrecRoundFuel_eq_or fuel n p mode
  complete := fun n p _ mode hB => by
    have hB' := hB _ rfl
    obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (psiZeroApprox n)
      (psiZeroApprox_bracketConv n) (ne_zero_of_not_mem_floatSet hB') hB' (max 64 (p + 32))
      (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _))
      (fun w hw => (lnAbsGammaApproxOf_valid_or_none
        (fun _ hc => psiZeroEncl_spec n (by omega) hc) w p mode).imp_left
          fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
    refine ⟨F, fun fuel hfuel => ?_⟩
    unfold psiZeroPrecRoundFuel
    rw [ite_eq_right (NeZero.ne p)]
    exact hF fuel hfuel
  dyadic := fun n h => absurd h (Set.notMem_empty _)
  nondyadic := fun n h => absurd h (Set.notMem_empty _)
  correct := fun n hn => by
    rcases hn with h | h <;> exact absurd h (Set.notMem_empty _)

end Azurite.AzFloat
