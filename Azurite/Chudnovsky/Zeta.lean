/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# The Weierstrass zeta function

For a period pair `L` (Mathlib's `PeriodPair`, with `℘[L]`):

  `ζ(z) = ∑_{l ∈ Λ} (1/(z − l) + 1/l + z/l²)`   (`weierstrassZeta`; the term `l = 0` is `1/z`),

the terms being `z²/(l²(z − l)) = O(|l|⁻³)`.  As for `℘` in Mathlib, the sum with one term left
out (`zetaExcept`) is the tool near a lattice point.

* `differentiableOn_weierstrassZeta`: `ζ` is differentiable off the lattice;
* `deriv_weierstrassZeta`: `ζ′ = −℘` there;
* `weierstrassZeta_neg`: `ζ` is odd.

The quasi-periods are in `Chudnovsky/QuasiPeriod.lean`.
-/

open Module Filter
open scoped Topology

namespace Azurite.Chudnovsky

open PeriodPair

variable (L : PeriodPair)

/-- The term `1/(z − l) + 1/l + z/l²` of the series of `ζ`. -/
noncomputable def zetaTerm (l z : ℂ) : ℂ := 1 / (z - l) + 1 / l + z / l ^ 2

theorem zetaTerm_eq {l z : ℂ} (hl : l ≠ 0) (hz : z ≠ l) :
    zetaTerm l z = z ^ 2 / (l ^ 2 * (z - l)) := by
  unfold zetaTerm
  have : z - l ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

theorem zetaTerm_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖zetaTerm l s‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hl : l ≠ 0 := norm_pos_iff.mp hl0
  have hsl : s ≠ l := by rintro rfl; linarith
  rw [zetaTerm_eq hl hsl, norm_div, norm_mul, norm_pow, norm_pow]
  have h1 : ‖l‖ / 2 ≤ ‖s - l‖ := by
    have := norm_sub_norm_le l s
    rw [norm_sub_rev] at this
    linarith
  have h2 : ‖l‖ ^ (-3 : ℝ) = (‖l‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hl0.le]
    norm_cast
  have hsl0 : 0 < ‖s - l‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsl)
  rw [h2, div_le_iff₀ (by positivity)]
  have h3 : ‖s‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs.le 2
  calc ‖s‖ ^ 2 ≤ r ^ 2 := h3
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * (‖l‖ / 2)) := by
        field_simp
    _ ≤ 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ * (‖l‖ ^ 2 * ‖s - l‖) := by gcongr

/-- `ζ` with the term of `l₀` left out. -/
noncomputable def zetaExcept (l₀ : ℂ) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else zetaTerm l z

/-- **The Weierstrass zeta function** of the lattice of `L`. -/
noncomputable def weierstrassZeta (z : ℂ) : ℂ := ∑' l : L.lattice, zetaTerm l z

theorem hasSumLocallyUniformly_zetaExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) => if l.1 = l₀ then 0 else zetaTerm l z)
      (zetaExcept L l₀) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l => 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _) fun r hr =>
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact zetaTerm_bound r hr s hs l h

theorem differentiableAt_zetaTerm {l z : ℂ} (hz : z ≠ l) :
    DifferentiableAt ℂ (zetaTerm l) z := by
  unfold zetaTerm
  have : z - l ≠ 0 := sub_ne_zero.mpr hz
  fun_prop (disch := assumption)

theorem differentiableOn_zetaExcept (l₀ : ℂ) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {l₀})ᶜ := by
  refine (hasSumLocallyUniformly_zetaExcept L l₀).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s => .fun_sum fun i _ => ?_) L.isOpen_compl_lattice_sdiff
  split_ifs with h
  · simp
  · intro x hx
    refine (differentiableAt_zetaTerm ?_).differentiableWithinAt
    rintro rfl
    exact hx ⟨i.2, h⟩

theorem hasDerivAt_zetaTerm {l z : ℂ} (hz : z ≠ l) :
    HasDerivAt (zetaTerm l) (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  unfold zetaTerm
  have hzl : z - l ≠ 0 := sub_ne_zero.mpr hz
  have h1 : HasDerivAt (fun z : ℂ => 1 / (z - l)) (-(1 / (z - l) ^ 2)) z := by
    have h := (hasDerivAt_inv hzl).comp z ((hasDerivAt_id z).sub_const l)
    convert h using 1
    · funext w
      simp
    · simp
  have h2 : HasDerivAt (fun z : ℂ => z / l ^ 2) (1 / l ^ 2) z := by
    simpa using (hasDerivAt_id z).div_const (l ^ 2)
  have := (h1.add_const (1 / l)).add h2
  convert this using 1
  ring

/-- `(ζ − term)′ = −(℘ − term)` off the other lattice points. -/
theorem eqOn_deriv_zetaExcept (l₀ : ℂ) :
    Set.EqOn (deriv (zetaExcept L l₀)) (fun z => -(L.weierstrassPExcept l₀ z))
      (L.lattice \ {l₀})ᶜ := by
  refine ((hasSumLocallyUniformly_zetaExcept L l₀).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s => ?_) L.isOpen_compl_lattice_sdiff).unique ?_
  · refine .fun_sum fun i _ => ?_
    split_ifs with h
    · simp
    · intro x hx
      refine (differentiableAt_zetaTerm ?_).differentiableWithinAt
      rintro rfl
      exact hx ⟨i.2, h⟩
  · refine ((L.hasSumLocallyUniformly_weierstrassPExcept l₀).tendstoLocallyUniformlyOn.neg).congr
      ?_
    intro s x hx
    simp only [Function.comp_apply, Pi.neg_apply]
    rw [deriv_fun_sum]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · simp
      · have hxi : x ≠ i.1 := by
          rintro rfl
          exact hx ⟨i.2, h⟩
        exact (hasDerivAt_zetaTerm hxi).deriv.symm
    · intro i _
      split_ifs with h
      · simp
      · have hxi : x ≠ i.1 := by
          rintro rfl
          exact hx ⟨i.2, h⟩
        exact differentiableAt_zetaTerm hxi

theorem hasSum_zetaExcept (l₀ : ℂ) (z : ℂ) :
    HasSum (fun l : L.lattice => if l.1 = l₀ then 0 else zetaTerm l z) (zetaExcept L l₀ z) :=
  (hasSumLocallyUniformly_zetaExcept L l₀).hasSum

theorem zetaExcept_add (l₀ : L.lattice) (z : ℂ) :
    zetaExcept L l₀ z + zetaTerm l₀ z = weierstrassZeta L z := by
  trans zetaExcept L l₀ z + ∑' i : L.lattice, if i.1 = l₀.1 then zetaTerm l₀ z else 0
  · congr 1
    rw [tsum_eq_single l₀]
    · simp
    · intro b hb
      rw [ite_eq_right]
      exact fun h => hb (Subtype.ext h)
  rw [zetaExcept, weierstrassZeta, ← Summable.tsum_add]
  · congr with w
    split_ifs with h
    · rw [zero_add, ← h]
    · rw [add_zero]
  · exact ⟨_, hasSum_zetaExcept L _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by
      intro i hi
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
      exact Subtype.ext hi.1))

theorem zetaExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice) :
    zetaExcept L l₀ = weierstrassZeta L := by
  funext z
  unfold zetaExcept weierstrassZeta
  congr with l
  rw [ite_eq_right]
  rintro rfl
  exact hl l.2

/-- `ζ` is differentiable off the lattice. -/
theorem differentiableOn_weierstrassZeta :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ := by
  rw [← zetaExcept_of_notMem L _ L.ω₁_div_two_notMem_lattice]
  convert differentiableOn_zetaExcept L (L.ω₁ / 2) using 2
  simp [L.ω₁_div_two_notMem_lattice]

/-- **`ζ′ = −℘`** off the lattice. -/
theorem deriv_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (weierstrassZeta L) z = -(L.weierstrassP z) := by
  have h := eqOn_deriv_zetaExcept L (L.ω₁ / 2) (x := z) (fun h => hz h.1)
  rw [zetaExcept_of_notMem L _ L.ω₁_div_two_notMem_lattice,
    L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice] at h
  exact h

theorem hasDerivAt_weierstrassZeta {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-(L.weierstrassP z)) z := by
  rw [← deriv_weierstrassZeta L hz]
  exact ((differentiableOn_weierstrassZeta L).differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt

/-- `ζ` is odd. -/
theorem weierstrassZeta_neg (z : ℂ) : weierstrassZeta L (-z) = -weierstrassZeta L z := by
  simp only [weierstrassZeta]
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  congr with l
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, zetaTerm]
  rw [show -z - -(l : ℂ) = -(z - l) by ring]
  simp only [one_div, inv_neg, even_two, Even.neg_pow, neg_div]
  ring

end Azurite.Chudnovsky
