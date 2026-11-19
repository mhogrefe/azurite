/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Pigeonhole

/-!
# Fel'dman, Lemma 1: Dirichlet's box principle for linear forms

N. I. Fel'dman, *Approximation of certain transcendental numbers. I*, Izv. Akad. Nauk SSSR
Ser. Mat. 15 (1951), 53–74, §1, Lemma 1.

Given `m` real linear forms `L_i(x) = ∑_j a_{ij} x_j` in `r` variables with `|L_i(x)| ≤ A` on
the box `0 ≤ x_j ≤ z`: the `(z + 1)^r` points of the box are mapped into the cube `[−A, A]^m`,
cut into `N^m` small cubes of side `2A/N`.  If `N^m < (z + 1)^r` two points fall into one small
cube, and their difference `x ≠ 0`, `|x_j| ≤ z`, has `|L_i(x)| ≤ 2A/N` (`dirichlet_box`).
Fel'dman takes `N = [Z^(1/m) − 1]`, `Z = (z + 1)^r`: `|L_i(x)| ≤ 2A/(Z^(1/m) − 2)`
(`dirichlet_box_rpow`; his inequality is strict, which fails for `A = 0`).
-/

namespace Azurite.Feldman

open Finset

/-- The index of the small interval containing `t ∈ [0, N]`: `k ≤ t ≤ k + 1`. -/
theorem box_index_bounds {N : ℕ} (hN : 0 < N) {t : ℝ} (h0 : 0 ≤ t) (hN' : t ≤ N) :
    (min (N - 1) ⌊t⌋₊ : ℕ) ≤ t ∧ t ≤ (min (N - 1) ⌊t⌋₊ : ℕ) + 1 := by
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le h0
  have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  rcases le_total ⌊t⌋₊ (N - 1) with h | h
  · rw [min_eq_right h]
    exact ⟨hfl, hlt.le⟩
  · rw [min_eq_left h]
    refine ⟨le_trans (by exact_mod_cast h) hfl, ?_⟩
    have : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [this]
    exact hN'

/-- **Fel'dman, Lemma 1 (Dirichlet's principle)**, with the number `N` of subdivisions as a
parameter. -/
theorem dirichlet_box {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℝ) (z N : ℕ) (A : ℝ)
    (hN : 0 < N) (hcard : N ^ Fintype.card ι < (z + 1) ^ Fintype.card κ)
    (hA : ∀ x : κ → ℕ, (∀ j, x j ≤ z) → ∀ i, |∑ j, a i j * (x j : ℝ)| ≤ A) :
    ∃ x : κ → ℤ, x ≠ 0 ∧ (∀ j, |x j| ≤ z) ∧
      ∀ i, |∑ j, a i j * (x j : ℝ)| ≤ 2 * A / N := by
  classical
  -- the forms on a point of the box
  set L : (κ → Fin (z + 1)) → ι → ℝ := fun x i => ∑ j, a i j * ((x j : ℕ) : ℝ) with hL
  have hLA : ∀ x i, |L x i| ≤ A := fun x i =>
    hA (fun j => (x j : ℕ)) (fun j => Nat.lt_succ_iff.mp (x j).isLt) i
  set t : (κ → Fin (z + 1)) → ι → ℝ := fun x i => (L x i + A) * N / (2 * A) with ht
  let φ : (κ → Fin (z + 1)) → (ι → Fin N) := fun x i =>
    ⟨min (N - 1) ⌊t x i⌋₊, lt_of_le_of_lt (min_le_left _ _) (by omega)⟩
  have hc : Fintype.card (ι → Fin N) < Fintype.card (κ → Fin (z + 1)) := by
    simpa using hcard
  obtain ⟨x, y, hxy, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hc
  refine ⟨fun j => ((x j : ℕ) : ℤ) - ((y j : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro h
    apply hxy
    funext j
    have := congrFun h j
    simp only [Pi.zero_apply] at this
    exact Fin.ext (by omega)
  · intro j
    have h1 := (x j).isLt
    have h2 := (y j).isLt
    change |((x j : ℕ) : ℤ) - ((y j : ℕ) : ℤ)| ≤ (z : ℤ)
    rw [abs_le]
    constructor <;> omega
  · intro i
    have hdiff : ∑ j, a i j * (((((x j : ℕ) : ℤ) - ((y j : ℕ) : ℤ) : ℤ)) : ℝ) = L x i - L y i := by
      simp only [hL, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [hdiff]
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hLA x i)
    rcases hA0.eq_or_lt with hA' | hA'
    · have h1 := hLA x i
      have h2 := hLA y i
      rw [← hA'] at h1 h2 ⊢
      rw [abs_nonpos_iff.mp h1, abs_nonpos_iff.mp h2]
      simp
    · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hrange : ∀ w, 0 ≤ t w i ∧ t w i ≤ N := fun w => by
        have := abs_le.mp (hLA w i)
        simp only [ht]
        constructor
        · apply div_nonneg (mul_nonneg (by linarith) hNr.le) (by linarith)
        · rw [div_le_iff₀ (by linarith)]
          nlinarith
      have hk : (min (N - 1) ⌊t x i⌋₊ : ℕ) = min (N - 1) ⌊t y i⌋₊ := by
        have := congrFun hφ i
        simpa [φ] using this
      obtain ⟨hx1, hx2⟩ := box_index_bounds hN (hrange x).1 (hrange x).2
      obtain ⟨hy1, hy2⟩ := box_index_bounds hN (hrange y).1 (hrange y).2
      rw [hk] at hx1 hx2
      have habs : |t x i - t y i| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have he : L x i - L y i = (t x i - t y i) * (2 * A / N) := by
        simp only [ht]
        field_simp
        ring
      rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * A / N)]
      calc |t x i - t y i| * (2 * A / N) ≤ 1 * (2 * A / N) := by gcongr
        _ = 2 * A / N := one_mul _

/-- **Fel'dman, Lemma 1**, in his form: with `Z = (z + 1)^r`, `m ≤ r` forms and `z ≥ 2`, there
are integers `x_j`, not all zero, `|x_j| ≤ z`, with `|L_i(x)| ≤ 2A/(Z^(1/m) − 2)`. -/
theorem dirichlet_box_rpow {r m : ℕ} (hm : 0 < m) (hmr : m ≤ r) (a : Fin m → Fin r → ℝ)
    (z : ℕ) (hz : 2 ≤ z) (A : ℝ)
    (hA : ∀ x : Fin r → ℕ, (∀ j, x j ≤ z) → ∀ i, |∑ j, a i j * (x j : ℝ)| ≤ A) :
    ∃ x : Fin r → ℤ, x ≠ 0 ∧ (∀ j, |x j| ≤ z) ∧
      ∀ i, |∑ j, a i j * (x j : ℝ)| ≤ 2 * A / ((((z : ℝ) + 1) ^ r) ^ ((m : ℝ)⁻¹) - 2) := by
  set y : ℝ := (((z : ℝ) + 1) ^ r) ^ ((m : ℝ)⁻¹) with hy
  have hz1 : (3 : ℝ) ≤ (z : ℝ) + 1 := by
    have : (2 : ℝ) ≤ z := by exact_mod_cast hz
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hym : y ^ m = ((z : ℝ) + 1) ^ r := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hmR.ne',
      Real.rpow_one]
  have hy3 : 3 ≤ y := by
    have h1 : ((z : ℝ) + 1) ^ m ≤ ((z : ℝ) + 1) ^ r := pow_le_pow_right₀ (by linarith) hmr
    have h2 : (((z : ℝ) + 1) ^ m) ^ ((m : ℝ)⁻¹) = (z : ℝ) + 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hmR.ne',
        Real.rpow_one]
    have h3 : (((z : ℝ) + 1) ^ m) ^ ((m : ℝ)⁻¹) ≤ y :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    linarith
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hfl' : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have hfl3 : 3 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy3)
  have hNcast : ((⌊y⌋₊ - 1 : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hcard : (⌊y⌋₊ - 1) ^ m < (z + 1) ^ r := by
    have : (((⌊y⌋₊ - 1 : ℕ) : ℝ)) ^ m < ((z : ℝ) + 1) ^ r := by
      rw [← hym, hNcast]
      exact pow_lt_pow_left₀ (by linarith) (by
        have : (3 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hfl3
        linarith) hm.ne'
    exact_mod_cast this
  obtain ⟨x, hx0, hxz, hx⟩ := dirichlet_box a z (⌊y⌋₊ - 1) A (by omega)
    (by simpa using hcard) hA
  have hA0 : 0 ≤ A := by
    have := hA (fun _ => 0) (fun _ => Nat.zero_le _) ⟨0, hm⟩
    exact (abs_nonneg _).trans this
  refine ⟨x, hx0, hxz, fun i => (hx i).trans ?_⟩
  rw [hNcast]
  apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- **Fel'dman, Lemma 1** for forms and unknowns indexed by finsets: the unknowns `x_j`,
`j ∈ J`, are not all zero, and `|x_j| ≤ z` everywhere. -/
theorem dirichlet_box_finset {ι κ : Type*} (F : Finset ι) (J : Finset κ) (a : ι → κ → ℝ)
    (z N : ℕ) (A : ℝ) (hN : 0 < N) (hcard : N ^ F.card < (z + 1) ^ J.card)
    (hA : ∀ x : κ → ℕ, (∀ j, x j ≤ z) → ∀ i ∈ F, |∑ j ∈ J, a i j * (x j : ℝ)| ≤ A) :
    ∃ x : κ → ℤ, (∃ j ∈ J, x j ≠ 0) ∧ (∀ j, |x j| ≤ z) ∧
      ∀ i ∈ F, |∑ j ∈ J, a i j * (x j : ℝ)| ≤ 2 * A / N := by
  classical
  obtain ⟨x, hx0, hxz, hx⟩ := dirichlet_box (ι := F) (κ := J) (fun i j => a i j) z N A hN
    (by simpa using hcard)
    (fun x hxz i => by
      have := hA (fun j => if h : j ∈ J then x ⟨j, h⟩ else 0)
        (fun j => by
          by_cases h : j ∈ J
          · simpa [h] using hxz ⟨j, h⟩
          · simp [h]) i i.2
      rw [← Finset.sum_coe_sort J] at this
      simpa using this)
  refine ⟨fun j => if h : j ∈ J then x ⟨j, h⟩ else 0, ?_, fun j => ?_, fun i hi => ?_⟩
  · by_contra hall
    apply hx0
    funext j
    by_contra hj
    exact hall ⟨j, j.2, by simpa using hj⟩
  · by_cases h : j ∈ J
    · simpa [h] using hxz ⟨j, h⟩
    · simp [h]
  · have := hx ⟨i, hi⟩
    rw [← Finset.sum_coe_sort J]
    simpa using this

end Azurite.Feldman
