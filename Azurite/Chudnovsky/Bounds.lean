/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.EtaG2

/-!
# The lattice `ℤ + ℤτ`: parallelograms and bounds for `℘`, `ζ`

For `τ` in the upper half-plane with `|τ| = 1`, `|Re τ| ≤ 1/2` (so for `i` and `ρ`):

* real coordinates `coA`, `coB` with `z = a + bτ`, and `max(|a|, |b|) ≤ 2|z| ≤ 2(|a| + |b|)`;
* the open parallelograms `Upar K = {|a|, |b| < K + 1/2}`: bounded, with frontier at distance
  `≥ 1/4` from the lattice (`far_of_frontier`), containing exactly the lattice points of the
  finite set `latS K`;
* `℘` is bounded and `ζ` grows at most linearly on `{z : dist(z, Λ) ≥ 1/4}`
  (`exists_weierstrassP_bound`, `exists_weierstrassZeta_bound`), by periodicity and
  compactness.
-/

namespace Azurite.Chudnovsky

open Complex Set Metric Filter Topology UpperHalfPlane

variable (τ : ℍ)

/-- The coordinate `b` of `z = a + bτ`. -/
noncomputable def coB (z : ℂ) : ℝ := z.im / (τ : ℂ).im

/-- The coordinate `a` of `z = a + bτ`. -/
noncomputable def coA (z : ℂ) : ℝ := z.re - coB τ z * (τ : ℂ).re

theorem im_ne_zero : (τ : ℂ).im ≠ 0 := ne_of_gt τ.im_pos

theorem coord_eq (z : ℂ) : z = coA τ z + coB τ z * τ := by
  have h := im_ne_zero τ
  apply Complex.ext
  · simp [coA, coB]
  · simp only [coB, add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
    field_simp

theorem coB_add_mul (x y : ℝ) : coB τ (x + y * τ) = y := by
  have h := im_ne_zero τ
  simp only [coB, add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
  field_simp

theorem coA_add_mul (x y : ℝ) : coA τ (x + y * τ) = x := by
  rw [coA, coB_add_mul]
  simp

theorem coB_sub (z w : ℂ) : coB τ (z - w) = coB τ z - coB τ w := by
  simp only [coB, sub_im]
  ring

theorem coA_sub (z w : ℂ) : coA τ (z - w) = coA τ z - coA τ w := by
  simp only [coA, coB_sub, sub_re]
  ring

theorem continuous_coB : Continuous (coB τ) := by
  unfold coB
  fun_prop

theorem continuous_coA : Continuous (coA τ) := by
  unfold coA
  have := continuous_coB τ
  fun_prop

variable {τ}

theorem norm_sq_coord (hn : ‖(τ : ℂ)‖ = 1) (a b : ℝ) :
    ‖(a : ℂ) + b * τ‖ ^ 2 = a ^ 2 + 2 * a * b * (τ : ℂ).re + b ^ 2 := by
  have h1 : (τ : ℂ).re ^ 2 + (τ : ℂ).im ^ 2 = 1 := by
    have := Complex.sq_norm (τ : ℂ)
    rw [hn, Complex.normSq_apply] at this
    linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero, add_im, mul_im, zero_add]
  linear_combination b ^ 2 * h1

theorem abs_coA_le (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) (z : ℂ) :
    |coA τ z| ≤ 2 * ‖z‖ := by
  have h := norm_sq_coord hn (coA τ z) (coB τ z)
  rw [← coord_eq τ z] at h
  have hr2 : (τ : ℂ).re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hr
    nlinarith
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2 |> fun h' => abs_le.mpr ⟨?_, h'⟩
  all_goals nlinarith [sq_nonneg (coB τ z + (τ : ℂ).re * coA τ z), norm_nonneg z,
    sq_nonneg (coA τ z)]

theorem abs_coB_le (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) (z : ℂ) :
    |coB τ z| ≤ 2 * ‖z‖ := by
  have h := norm_sq_coord hn (coA τ z) (coB τ z)
  rw [← coord_eq τ z] at h
  have hr2 : (τ : ℂ).re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hr
    nlinarith
  have hsq : coB τ z ^ 2 ≤ (2 * ‖z‖) ^ 2 := by
    nlinarith [sq_nonneg (coA τ z + (τ : ℂ).re * coB τ z), sq_nonneg (coB τ z)]
  exact abs_le_of_sq_le_sq hsq (by positivity)

theorem norm_le_coord (hn : ‖(τ : ℂ)‖ = 1) (z : ℂ) : ‖z‖ ≤ |coA τ z| + |coB τ z| := by
  conv_lhs => rw [coord_eq τ z]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hn, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

variable (τ)

/-- The open parallelogram `{a + bτ : |a|, |b| < K + 1/2}`. -/
def Upar (K : ℕ) : Set ℂ := {z | |coA τ z| < K + 1 / 2 ∧ |coB τ z| < K + 1 / 2}

/-- The closed parallelogram. -/
def Ucl (K : ℕ) : Set ℂ := {z | |coA τ z| ≤ K + 1 / 2 ∧ |coB τ z| ≤ K + 1 / 2}

theorem isOpen_Upar (K : ℕ) : IsOpen (Upar τ K) :=
  (isOpen_lt (continuous_abs.comp (continuous_coA τ)) continuous_const).inter
    (isOpen_lt (continuous_abs.comp (continuous_coB τ)) continuous_const)

theorem isClosed_Ucl (K : ℕ) : IsClosed (Ucl τ K) :=
  (isClosed_le (continuous_abs.comp (continuous_coA τ)) continuous_const).inter
    (isClosed_le (continuous_abs.comp (continuous_coB τ)) continuous_const)

theorem Upar_subset_Ucl (K : ℕ) : Upar τ K ⊆ Ucl τ K := fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem closure_Upar_subset (K : ℕ) : closure (Upar τ K) ⊆ Ucl τ K :=
  closure_minimal (Upar_subset_Ucl τ K) (isClosed_Ucl τ K)

variable {τ}

theorem norm_le_of_mem_Ucl (hn : ‖(τ : ℂ)‖ = 1) {K : ℕ} {z : ℂ} (hz : z ∈ Ucl τ K) :
    ‖z‖ ≤ 2 * K + 1 := by
  have := norm_le_coord hn z
  have h1 := hz.1
  have h2 := hz.2
  linarith

theorem isBounded_Upar (hn : ‖(τ : ℂ)‖ = 1) (K : ℕ) : Bornology.IsBounded (Upar τ K) :=
  (isBounded_closedBall (x := (0 : ℂ)) (r := 2 * K + 1)).subset fun _ hz =>
    mem_closedBall_zero_iff.mpr (norm_le_of_mem_Ucl hn (Upar_subset_Ucl τ K hz))

theorem frontier_Upar {K : ℕ} {z : ℂ} (hz : z ∈ frontier (Upar τ K)) :
    z ∈ Ucl τ K ∧ (|coA τ z| = K + 1 / 2 ∨ |coB τ z| = K + 1 / 2) := by
  rw [frontier, (isOpen_Upar τ K).interior_eq] at hz
  have hcl := closure_Upar_subset τ K hz.1
  refine ⟨hcl, ?_⟩
  by_contra hne
  push Not at hne
  exact hz.2 ⟨lt_of_le_of_ne hcl.1 hne.1, lt_of_le_of_ne hcl.2 hne.2⟩

theorem mem_lattice_pairOf {z : ℂ} : z ∈ (pairOf τ).lattice ↔ ∃ m n : ℤ, z = m + n * τ := by
  rw [PeriodPair.mem_lattice]
  simp [eq_comm]

theorem half_le_abs_sub_int {x : ℝ} {K : ℕ} (hx : |x| = K + 1 / 2) (m : ℤ) :
    1 / 2 ≤ |x - m| := by
  rcases (abs_eq (by positivity)).mp hx with h | h
  · have h1 : (1 : ℝ) ≤ |((2 * (K : ℤ) + 1 - 2 * m : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by omega)
    have h2 : x - m = ((2 * (K : ℤ) + 1 - 2 * m : ℤ) : ℝ) / 2 := by
      rw [h]; push_cast; ring
    rw [h2, abs_div, abs_two]
    linarith
  · have h1 : (1 : ℝ) ≤ |((-(2 * (K : ℤ) + 1) - 2 * m : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (by omega)
    have h2 : x - m = ((-(2 * (K : ℤ) + 1) - 2 * m : ℤ) : ℝ) / 2 := by
      rw [h]; push_cast; ring
    rw [h2, abs_div, abs_two]
    linarith

/-- The frontier of the parallelogram is at distance `≥ 1/4` from the lattice. -/
theorem far_of_frontier (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) {K : ℕ} {z : ℂ}
    (hz : z ∈ frontier (Upar τ K)) : ∀ l ∈ (pairOf τ).lattice, 1 / 4 ≤ ‖z - l‖ := by
  intro l hl
  obtain ⟨m, n, rfl⟩ := mem_lattice_pairOf.mp hl
  have hA : coA τ (z - (m + n * τ)) = coA τ z - m := by
    rw [coA_sub]
    have := coA_add_mul τ (m : ℝ) (n : ℝ)
    push_cast at this
    rw [this]
  have hB : coB τ (z - (m + n * τ)) = coB τ z - n := by
    rw [coB_sub]
    have := coB_add_mul τ (m : ℝ) (n : ℝ)
    push_cast at this
    rw [this]
  rcases (frontier_Upar hz).2 with h | h
  · have h1 := half_le_abs_sub_int h m
    have h2 := abs_coA_le hn hr (z - (m + n * τ))
    rw [hA] at h2
    linarith
  · have h1 := half_le_abs_sub_int h n
    have h2 := abs_coB_le hn hr (z - (m + n * τ))
    rw [hB] at h2
    linarith

theorem norm_ge_of_frontier (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) {K : ℕ} {z : ℂ}
    (hz : z ∈ frontier (Upar τ K)) : (K : ℝ) / 2 ≤ ‖z‖ := by
  rcases (frontier_Upar hz).2 with h | h
  · have := abs_coA_le hn hr z
    linarith
  · have := abs_coB_le hn hr z
    linarith

variable (τ)

/-- The lattice points `m + nτ`, `|m|, |n| ≤ K`. -/
noncomputable def latS (K : ℕ) : Finset ℂ :=
  ((Finset.Icc (-(K : ℤ)) K) ×ˢ (Finset.Icc (-(K : ℤ)) K)).image
    fun x => (x.1 : ℂ) + x.2 * τ

theorem card_latS_le (K : ℕ) : (latS τ K).card ≤ (2 * K + 1) ^ 2 := by
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Finset.card_product, Int.card_Icc]
  have : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
  rw [this]
  ring

variable {τ}

theorem latS_subset_lattice {K : ℕ} {s : ℂ} (hs : s ∈ latS τ K) : s ∈ (pairOf τ).lattice := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
  exact mem_lattice_pairOf.mpr ⟨x.1, x.2, rfl⟩

theorem norm_le_of_mem_latS (hn : ‖(τ : ℂ)‖ = 1) {K : ℕ} {s : ℂ} (hs : s ∈ latS τ K) :
    ‖s‖ ≤ 2 * K := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hn, mul_one, Complex.norm_intCast, Complex.norm_intCast]
  have h1 : |(x.1 : ℝ)| ≤ K := abs_le.mpr ⟨by exact_mod_cast hx.1.1, by exact_mod_cast hx.1.2⟩
  have h2 : |(x.2 : ℝ)| ≤ K := abs_le.mpr ⟨by exact_mod_cast hx.2.1, by exact_mod_cast hx.2.2⟩
  linarith

theorem mem_latS_of_mem_Ucl {K : ℕ} {l : ℂ} (hl : l ∈ (pairOf τ).lattice) (hU : l ∈ Ucl τ K) :
    l ∈ latS τ K := by
  obtain ⟨m, n, rfl⟩ := mem_lattice_pairOf.mp hl
  have hA : coA τ (m + n * τ) = m := by
    have := coA_add_mul τ (m : ℝ) (n : ℝ)
    push_cast at this
    exact this
  have hB : coB τ (m + n * τ) = n := by
    have := coB_add_mul τ (m : ℝ) (n : ℝ)
    push_cast at this
    exact this
  have h1 := abs_le.mp hU.1
  have h2 := abs_le.mp hU.2
  rw [hA] at h1
  rw [hB] at h2
  have hint : ∀ j : ℤ, -((K : ℝ) + 1 / 2) ≤ j → (j : ℝ) ≤ K + 1 / 2 → -(K : ℤ) ≤ j ∧ j ≤ K := by
    intro j hj1 hj2
    constructor
    · have : ((-(K : ℤ) - 1 : ℤ) : ℝ) < j := by push_cast; linarith
      have : -(K : ℤ) - 1 < j := by exact_mod_cast this
      omega
    · have : (j : ℝ) < (K : ℤ) + 1 := by push_cast; linarith
      have : j < (K : ℤ) + 1 := by exact_mod_cast this
      omega
  refine Finset.mem_image.mpr ⟨(m, n), ?_, rfl⟩
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨hint m h1.1 h1.2, hint n h2.1 h2.2⟩

theorem closure_Upar_subset_compl (K : ℕ) :
    closure (Upar τ K) ⊆ (((pairOf τ).lattice : Set ℂ) \ (latS τ K : Set ℂ))ᶜ := by
  intro z hz hmem
  exact hmem.2 (Finset.mem_coe.mpr (mem_latS_of_mem_Ucl hmem.1 (closure_Upar_subset τ K hz)))

/-! ### Bounds away from the lattice -/

variable (τ)

/-- `z` is at distance `≥ 1/4` from the lattice. -/
def Far (z : ℂ) : Prop := ∀ l ∈ (pairOf τ).lattice, 1 / 4 ≤ ‖z - l‖

variable {τ}

theorem Far.notMem {z : ℂ} (h : Far τ z) : z ∉ (pairOf τ).lattice := fun hz => by
  have := h z hz
  rw [sub_self, norm_zero] at this
  norm_num at this

theorem Far.sub_coe {z l : ℂ} (h : Far τ z) (hl : l ∈ (pairOf τ).lattice) : Far τ (z - l) :=
  fun l' hl' => by
    rw [sub_sub]
    exact h _ (add_mem hl hl')

variable (τ)

/-- The part of the fundamental parallelogram away from the lattice. -/
def fundFar : Set ℂ := Ucl τ 0 ∩ {z | Far τ z}

/-- The lattice point nearest to `z` in the coordinates. -/
noncomputable def nearest (z : ℂ) : ℂ := (round (coA τ z) : ℤ) + (round (coB τ z) : ℤ) * τ

theorem nearest_mem (z : ℂ) : nearest τ z ∈ (pairOf τ).lattice :=
  mem_lattice_pairOf.mpr ⟨_, _, rfl⟩

variable {τ}

theorem isCompact_fundFar (hn : ‖(τ : ℂ)‖ = 1) : IsCompact (fundFar τ) := by
  have hcl : IsClosed {z | Far τ z} := by
    have : {z | Far τ z} = ⋂ l ∈ ((pairOf τ).lattice : Set ℂ), {z : ℂ | 1 / 4 ≤ ‖z - l‖} := by
      ext z
      simp [Far]
    rw [this]
    exact isClosed_biInter fun l _ => isClosed_le continuous_const (by fun_prop)
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_Ucl τ 0).inter hcl) ?_
  exact (isBounded_closedBall (x := (0 : ℂ)) (r := 2 * (0 : ℕ) + 1)).subset fun z hz =>
    mem_closedBall_zero_iff.mpr (norm_le_of_mem_Ucl hn hz.1)

theorem sub_nearest_mem {z : ℂ} (hz : Far τ z) : z - nearest τ z ∈ fundFar τ := by
  refine ⟨⟨?_, ?_⟩, hz.sub_coe (nearest_mem τ z)⟩
  · have h := coA_add_mul τ ((round (coA τ z) : ℤ) : ℝ) ((round (coB τ z) : ℤ) : ℝ)
    push_cast at h
    rw [coA_sub, nearest, h]
    simpa using abs_sub_round (coA τ z)
  · have h := coB_add_mul τ ((round (coA τ z) : ℤ) : ℝ) ((round (coB τ z) : ℤ) : ℝ)
    push_cast at h
    rw [coB_sub, nearest, h]
    simpa using abs_sub_round (coB τ z)

theorem fundFar_subset : fundFar τ ⊆ ((pairOf τ).lattice : Set ℂ)ᶜ := fun _ hz => hz.2.notMem

/-- **`℘` is bounded away from the lattice.** -/
theorem exists_weierstrassP_bound (hn : ‖(τ : ℂ)‖ = 1) :
    ∃ C : ℝ, ∀ z, Far τ z → ‖(pairOf τ).weierstrassP z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_fundFar hn).exists_bound_of_continuousOn
    ((pairOf τ).differentiableOn_weierstrassP.continuousOn.mono fundFar_subset)
  refine ⟨C, fun z hz => ?_⟩
  have h := (pairOf τ).weierstrassP_add_coe (z - nearest τ z) ⟨_, nearest_mem τ z⟩
  simp only [sub_add_cancel] at h
  rw [h]
  exact hC _ (sub_nearest_mem hz)

theorem abs_round_le (x : ℝ) : |((round x : ℤ) : ℝ)| ≤ |x| + 1 / 2 := by
  have h := abs_sub_round x
  have h2 : |((round x : ℤ) : ℝ)| ≤ |x| + |x - round x| := by
    have := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    rw [abs_sub_comm] at this
    linarith
  linarith

/-- **`ζ` grows at most linearly away from the lattice.** -/
theorem exists_weierstrassZeta_bound (hn : ‖(τ : ℂ)‖ = 1) (hr : |(τ : ℂ).re| ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, Far τ z → ‖weierstrassZeta (pairOf τ) z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨C, hC⟩ := (isCompact_fundFar hn).exists_bound_of_continuousOn
    ((differentiableOn_weierstrassZeta (pairOf τ)).continuousOn.mono fundFar_subset)
  set η₁ := quasiPeriod (pairOf τ) 1 with hη₁
  set η₂ := quasiPeriod (pairOf τ) τ with hη₂
  refine ⟨|C| + 2 * (‖η₁‖ + ‖η₂‖), by positivity, fun z hz => ?_⟩
  have hmem := sub_nearest_mem hz
  have h := weierstrassZeta_add_coe (pairOf τ) ⟨_, nearest_mem τ z⟩ (fundFar_subset hmem)
  simp only [sub_add_cancel] at h
  have hq : quasiPeriod (pairOf τ) (nearest τ z)
      = (round (coA τ z) : ℤ) * η₁ + (round (coB τ z) : ℤ) * η₂ := by
    have := quasiPeriod_int_combo (pairOf τ) (round (coA τ z)) (round (coB τ z))
    simpa [nearest] using this
  rw [h, hq]
  have h1 : |((round (coA τ z) : ℤ) : ℝ)| ≤ 2 * ‖z‖ + 1 / 2 := by
    linarith [abs_round_le (coA τ z), abs_coA_le hn hr z]
  have h2 : |((round (coB τ z) : ℤ) : ℝ)| ≤ 2 * ‖z‖ + 1 / 2 := by
    linarith [abs_round_le (coB τ z), abs_coB_le hn hr z]
  have h0 : ‖weierstrassZeta (pairOf τ) (z - nearest τ z)‖ ≤ |C| :=
    (hC _ hmem).trans (le_abs_self C)
  have hz0 := norm_nonneg z
  calc ‖weierstrassZeta (pairOf τ) (z - nearest τ z)
        + ((round (coA τ z) : ℤ) * η₁ + (round (coB τ z) : ℤ) * η₂)‖
      ≤ |C| + (|((round (coA τ z) : ℤ) : ℝ)| * ‖η₁‖ + |((round (coB τ z) : ℤ) : ℝ)| * ‖η₂‖) := by
        refine (norm_add_le _ _).trans (add_le_add h0 ((norm_add_le _ _).trans ?_))
        rw [norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    _ ≤ |C| + ((2 * ‖z‖ + 1 / 2) * ‖η₁‖ + (2 * ‖z‖ + 1 / 2) * ‖η₂‖) := by
        gcongr
    _ ≤ (|C| + 2 * (‖η₁‖ + ‖η₂‖)) * (1 + ‖z‖) := by
        nlinarith [abs_nonneg C, norm_nonneg η₁, norm_nonneg η₂]

end Azurite.Chudnovsky
