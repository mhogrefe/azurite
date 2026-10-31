/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section15Fractional

/-!
# DLMF §1.15(vii): Fractional derivatives

https://dlmf.nist.gov/1.15.vii

Fractional derivatives `D^α f(x) = dⁿ/dxⁿ I^{n−α} f(x)` (1.15.51), on `x > 0`, for `f`
continuous on `[0, ∞)`. The derivatives are two-sided, so they are taken at interior points
`x > 0`.

* Regularity: `I^ν f` is continuous on `[0, ∞)` (`continuousOn_fracIntegral`), `d/dx I¹ h = h`,
  and `dʲ/dxʲ I^{j+ν} g = I^ν g` (`iteratedDeriv_fracIntegral_add`), all from the semigroup
  property 1.15.48.
* 1.15.51: `fracDeriv` uses `n = ⌊ℜα⌋ + 1`. `dlmf_1_15_51` shows that every integer `n > ℜα`
  gives the same value. At integer orders `fracDeriv` is the ordinary derivative
  (`fracDeriv_natCast`).
* `D^μ I^ν g = I^{ν−μ} g` (`fracDeriv_fracIntegral`) and `D^μ I^μ g = g`.
* 1.15.52: `dlmf_1_15_52`, with `D^k` read either as the ordinary derivative or as the integer
  order fractional derivative (`dlmf_1_15_52_fracDeriv`).
* 1.15.53: `D^α D^β f = D^{α+β} f` for `f = I^γ g` with `ℜγ ≥ ℜ(α + β)` (`dlmf_1_15_53`,
  `dlmf_1_15_53_self`).
* `D^μ t^ρ` in closed form (`fracDeriv_cpow`), and DLMF's remark `D^{1/2} D ≠ D^{3/2}`
  (`dlmf_1_15_vii_half_deriv`).

DLMF discrepancy: 1.15.53 is stated with the only proviso that none of `α`, `β`, `α + β` is an
integer, and that is not enough. `dlmf_1_15_53_counterexample` takes `α = 1/3`, `β = 3/2` and the
continuous `f(t) = t^{1/2}`. Then `D^β f = 0`, so `D^α D^β f = 0`, but
`D^{α+β} f(x) = −(2/9) Γ(3/2)/Γ(5/3) x^{−4/3} ≠ 0`. A condition on `f` is needed; being a
fractional integral `I^γ g` of high enough order suffices.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Regularity of fractional integrals -/

theorem iteratedDeriv_congr_Ioi {F G : ℝ → ℂ} (h : EqOn F G (Ioi 0)) (n : ℕ) {x : ℝ}
    (hx : 0 < x) : iteratedDeriv n F x = iteratedDeriv n G x :=
  EventuallyEq.iteratedDeriv_eq n (Filter.mem_of_superset (Ioi_mem_nhds hx) fun _ hy => h hy)

theorem fracIntegral_congr_Ioi {F G : ℝ → ℂ} (h : EqOn F G (Ioi 0)) (ν : ℂ) {x : ℝ}
    (hx : 0 ≤ x) : fracIntegral ν F x = fracIntegral ν G x := by
  simp only [fracIntegral, fracIntegralFrom]
  congr 1
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => ?_)
  rw [uIoc_of_le hx] at ht
  rw [h (show t ∈ Ioi 0 from ht.1)]

/-- The substituted form `I^ν f(x) = (1/Γ(ν)) ∫_0^x u^{ν−1} f(x − u) du`. -/
theorem fracIntegral_eq_sub (ν : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fracIntegral ν f x = (Gamma ν)⁻¹ * ∫ u in (0 : ℝ)..x, (u : ℂ) ^ (ν - 1) * f (x - u) := by
  simp only [fracIntegral, fracIntegralFrom]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := x)
    (fun u => (u : ℂ) ^ (ν - 1) * f (x - u)) x
  simp only [sub_sub_cancel, sub_zero, sub_self] at h
  rw [← h]

/-- Fractional integrals of functions continuous on `[0, ∞)` are continuous on `[0, ∞)`. -/
theorem continuousOn_fracIntegral {ν : ℂ} (hν : 0 < ν.re) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 0)) : ContinuousOn (fracIntegral ν f) (Ici 0) := by
  intro x₀ hx₀
  set X := x₀ + 1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.mono (Icc_subset_Ici_self :
    Icc (0 : ℝ) X ⊆ Ici 0))
  set g : ℝ → ℝ → ℂ := fun x u => (Ioc 0 x).indicator (fun u => (u : ℂ) ^ (ν - 1) * f (x - u)) u
  have hrep : ∀ x, 0 ≤ x → fracIntegral ν f x = (Gamma ν)⁻¹ * ∫ u, g x u := fun x hx => by
    rw [fracIntegral_eq_sub, intervalIntegral.integral_of_le hx, integral_indicator
      measurableSet_Ioc]
  have hker : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (ν - 1)) (Ioc 0 X) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hx₀.out] : (0 : ℝ) ≤ X)).mp
      (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have hcont : ContinuousWithinAt (fun x => ∫ u, g x u) (Ici 0) x₀ := by
    refine continuousWithinAt_of_dominated (bound := (Ioc 0 X).indicator fun u =>
      M * ‖(u : ℂ) ^ (ν - 1)‖) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 ≤ x)
      refine (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr ?_
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      intro u hu
      refine ContinuousAt.continuousWithinAt ?_ |>.mul ?_
      · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hu.1.ne'))
      · exact (hf (x - u) (show (0 : ℝ) ≤ x - u by linarith [hu.2])).comp
          (continuousWithinAt_const.sub continuousWithinAt_id)
          (fun v hv => show (0 : ℝ) ≤ x - v by linarith [hv.2])
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds
        (show x₀ < X by linarith))] with x (hx : 0 ≤ x) hxX
      refine ae_of_all _ fun u => ?_
      by_cases hu : u ∈ Ioc 0 x
      · have huX : u ∈ Ioc 0 X := ⟨hu.1, hu.2.trans hxX.le⟩
        simp only [g, indicator_of_mem hu, indicator_of_mem huX, norm_mul]
        rw [mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM _ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
          (norm_nonneg _)
      · simp only [g, indicator_of_notMem hu, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 0
          ⟨le_rfl, by linarith [hx₀.out]⟩)) (norm_nonneg _)) _
    · exact (integrable_indicator_iff measurableSet_Ioc).mpr (hker.norm.const_mul M)
    · filter_upwards [(countable_singleton x₀).ae_notMem volume] with u hu
      rcases lt_or_gt_of_ne (show u ≠ x₀ from fun h => hu (by rw [h]; rfl)) with hlt | hgt
      · by_cases hu0 : 0 < u
        · have hev : (fun x => g x u) =ᶠ[𝓝 x₀] fun x => (u : ℂ) ^ (ν - 1) * f (x - u) := by
            filter_upwards [lt_mem_nhds hlt] with x hx
            simp only [g, indicator_of_mem (show u ∈ Ioc 0 x from ⟨hu0, hx.le⟩)]
          refine (ContinuousAt.congr_of_eventuallyEq ?_ hev).continuousWithinAt
          refine continuousAt_const.mul ?_
          have hfa : ContinuousAt f (x₀ - u) :=
            (hf (x₀ - u) (show (0 : ℝ) ≤ x₀ - u by linarith)).continuousAt
              (Ici_mem_nhds (by linarith))
          exact hfa.comp (f := fun x : ℝ => x - u) (by fun_prop)
        · have : (fun x => g x u) = fun _ => 0 := funext fun x => by
            simp only [g, indicator_of_notMem (show u ∉ Ioc 0 x from fun h => hu0 h.1)]
          rw [this]
          exact continuousWithinAt_const
      · have hev : (fun x => g x u) =ᶠ[𝓝 x₀] fun _ => 0 := by
          filter_upwards [gt_mem_nhds hgt] with x hx
          simp only [g, indicator_of_notMem (show u ∉ Ioc 0 x from fun h => by linarith [h.2])]
        exact (continuousAt_const.congr_of_eventuallyEq hev).continuousWithinAt
  refine ((continuousWithinAt_const.mul hcont).congr (fun x hx => hrep x hx) (hrep x₀ hx₀))

/-- `I^1 h(x) = ∫_0^x h`. -/
theorem fracIntegral_one (h : ℝ → ℂ) (x : ℝ) : fracIntegral 1 h x = ∫ t in (0 : ℝ)..x, h t := by
  simp [fracIntegral, fracIntegralFrom]

theorem hasDerivAt_fracIntegral_one {h : ℝ → ℂ} (hc : ContinuousOn h (Ici 0)) {x : ℝ}
    (hx : 0 < x) : HasDerivAt (fracIntegral 1 h) (h x) x := by
  have e : fracIntegral 1 h = fun y => ∫ t in (0 : ℝ)..y, h t := funext (fracIntegral_one h)
  rw [e]
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (by rw [uIcc_of_le hx.le]; exact Icc_subset_Ici_self)).intervalIntegrable)
    ((hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi x hx)
    ((hc x hx.le).continuousAt (Ici_mem_nhds hx))

/-- `d^j/dx^j I^j g = g` on `(0, ∞)` for `g` continuous on `[0, ∞)`, `j ≥ 1`. -/
theorem iteratedDeriv_fracIntegral_nat {g : ℝ → ℂ} (hg : ContinuousOn g (Ici 0)) (m : ℕ) :
    EqOn (iteratedDeriv (m + 1) (fracIntegral ((m + 1 : ℕ) : ℂ) g)) g (Ioi 0) := by
  induction m with
  | zero =>
    intro x hx
    rw [iteratedDeriv_one]
    simpa using (hasDerivAt_fracIntegral_one hg hx).deriv
  | succ m ih =>
    intro x hx
    have hm : 0 < (((m + 1 : ℕ) : ℂ)).re := by simp; positivity
    have hsg : EqOn (fracIntegral ((m + 1 + 1 : ℕ) : ℂ) g)
        (fracIntegral 1 (fracIntegral ((m + 1 : ℕ) : ℂ) g)) (Ioi 0) := fun y hy => by
      rw [dlmf_1_15_48 (by simp) hm hg (le_of_lt hy)]
      congr 1
      push_cast
      ring
    have hd : EqOn (deriv (fracIntegral ((m + 1 + 1 : ℕ) : ℂ) g))
        (fracIntegral ((m + 1 : ℕ) : ℂ) g) (Ioi 0) := fun y hy => by
      rw [EventuallyEq.deriv_eq (Filter.mem_of_superset (Ioi_mem_nhds hy) fun _ hz => hsg hz)]
      exact (hasDerivAt_fracIntegral_one (continuousOn_fracIntegral hm hg) hy).deriv
    rw [iteratedDeriv_succ', iteratedDeriv_congr_Ioi hd _ hx]
    exact ih hx

/-- `d^j/dx^j I^{j+ν} g = I^ν g` on `(0, ∞)`. -/
theorem iteratedDeriv_fracIntegral_add {ν : ℂ} (hν : 0 < ν.re) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ici 0)) (j : ℕ) :
    EqOn (iteratedDeriv j (fracIntegral ((j : ℂ) + ν) g)) (fracIntegral ν g) (Ioi 0) := by
  rcases j with _ | m
  · intro x _; simp
  intro x hx
  have hsg : EqOn (fracIntegral (((m + 1 : ℕ) : ℂ) + ν) g)
      (fracIntegral ((m + 1 : ℕ) : ℂ) (fracIntegral ν g)) (Ioi 0) := fun y hy =>
    (dlmf_1_15_48 (by simp; positivity) hν hg (le_of_lt hy)).symm
  rw [iteratedDeriv_congr_Ioi hsg _ hx]
  exact iteratedDeriv_fracIntegral_nat (continuousOn_fracIntegral hν hg) m hx

theorem iteratedDeriv_add_eq (n j : ℕ) (F : ℝ → ℂ) :
    iteratedDeriv (n + j) F = iteratedDeriv n (iteratedDeriv j F) := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

/-! ### The fractional derivative (1.15.51) -/

/-- The integer `n = ⌊ℜα⌋ + 1 > ℜα` used in the definition of `D^α`; any other integer `n > ℜα`
gives the same value (`dlmf_1_15_51`). -/
noncomputable def fracDerivOrder (α : ℂ) : ℕ := ⌊α.re⌋₊ + 1

theorem lt_fracDerivOrder (α : ℂ) : α.re < fracDerivOrder α := by
  simp only [fracDerivOrder, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

/-- DLMF 1.15.51: the fractional derivative `D^α f(x) = dⁿ/dxⁿ I^{n−α} f(x)`, here with
`n = ⌊ℜα⌋ + 1`. -/
noncomputable def fracDeriv (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  iteratedDeriv (fracDerivOrder α) (fracIntegral ((fracDerivOrder α : ℂ) - α) f) x

theorem iteratedDeriv_fracIntegral_sub_of_le {α : ℂ} {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0))
    {n m : ℕ} (hn : α.re < n) (hnm : n ≤ m) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv m (fracIntegral ((m : ℂ) - α) f) x =
      iteratedDeriv n (fracIntegral ((n : ℂ) - α) f) x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hν : 0 < ((n : ℂ) - α).re := by simp; linarith
  have e : ((n + j : ℕ) : ℂ) - α = (j : ℂ) + ((n : ℂ) - α) := by push_cast; ring
  rw [e, iteratedDeriv_add_eq]
  exact iteratedDeriv_congr_Ioi (iteratedDeriv_fracIntegral_add hν hf j) n hx

/-- DLMF 1.15.51 for every integer `n > ℜα`: `D^α f(x) = dⁿ/dxⁿ I^{n−α} f(x)` for `x > 0`, `f`
continuous on `[0, ∞)`. -/
theorem dlmf_1_15_51 {α : ℂ} {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0)) {n : ℕ}
    (hn : α.re < n) {x : ℝ} (hx : 0 < x) :
    fracDeriv α f x = iteratedDeriv n (fracIntegral ((n : ℂ) - α) f) x := by
  rw [fracDeriv]
  rcases le_total n (fracDerivOrder α) with h | h
  · exact iteratedDeriv_fracIntegral_sub_of_le hf hn h hx
  · exact (iteratedDeriv_fracIntegral_sub_of_le hf (lt_fracDerivOrder α) h hx).symm

theorem fracDeriv_congr_Ioi {F G : ℝ → ℂ} (h : EqOn F G (Ioi 0)) (α : ℂ) {x : ℝ} (hx : 0 < x) :
    fracDeriv α F x = fracDeriv α G x :=
  iteratedDeriv_congr_Ioi (fun _ hy => fracIntegral_congr_Ioi h _ (le_of_lt hy)) _ hx

theorem fracDeriv_zero_fun (α : ℂ) (x : ℝ) : fracDeriv α (fun _ => 0) x = 0 := by
  have : fracIntegral ((fracDerivOrder α : ℂ) - α) (fun _ => (0 : ℂ)) = fun _ => 0 :=
    funext fun _ => by simp [fracIntegral, fracIntegralFrom]
  rw [fracDeriv, this]
  simp

/-- At integer orders the fractional derivative is the ordinary derivative. -/
theorem fracDeriv_natCast {F : ℝ → ℂ} (hF : ContinuousOn F (Ici 0)) (k : ℕ) {x : ℝ}
    (hx : 0 < x) : fracDeriv k F x = iteratedDeriv k F x := by
  have hord : fracDerivOrder (k : ℂ) = k + 1 := by simp [fracDerivOrder]
  rw [fracDeriv, hord, show ((k + 1 : ℕ) : ℂ) - k = ((0 + 1 : ℕ) : ℂ) by push_cast; ring,
    iteratedDeriv_add_eq]
  exact iteratedDeriv_congr_Ioi (iteratedDeriv_fracIntegral_nat hF 0) k hx

/-- `D^μ I^ν g = I^{ν−μ} g` for `ℜν > ℜμ > 0`. -/
theorem fracDeriv_fracIntegral {μ ν : ℂ} (hμ : 0 < μ.re) (hμν : μ.re < ν.re) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ici 0)) {x : ℝ} (hx : 0 < x) :
    fracDeriv μ (fracIntegral ν g) x = fracIntegral (ν - μ) g x := by
  set N := fracDerivOrder μ
  have h1 : 0 < ((N : ℂ) - μ).re := by simp; linarith [lt_fracDerivOrder μ]
  have h2 : 0 < (ν - μ).re := by simp; linarith
  have hsg : EqOn (fracIntegral ((N : ℂ) - μ) (fracIntegral ν g))
      (fracIntegral ((N : ℂ) + (ν - μ)) g) (Ioi 0) := fun y hy => by
    rw [dlmf_1_15_48 h1 (by linarith) hg (le_of_lt hy)]
    congr 1
    ring
  rw [fracDeriv, iteratedDeriv_congr_Ioi hsg _ hx]
  exact iteratedDeriv_fracIntegral_add h2 hg N hx

/-- `D^μ I^μ g = g` for `ℜμ > 0`. -/
theorem fracDeriv_fracIntegral_self {μ : ℂ} (hμ : 0 < μ.re) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ici 0)) {x : ℝ} (hx : 0 < x) :
    fracDeriv μ (fracIntegral μ g) x = g x := by
  set N := fracDerivOrder μ
  have h1 : 0 < ((N : ℂ) - μ).re := by simp; linarith [lt_fracDerivOrder μ]
  have hsg : EqOn (fracIntegral ((N : ℂ) - μ) (fracIntegral μ g))
      (fracIntegral (((⌊μ.re⌋₊ + 1 : ℕ)) : ℂ) g) (Ioi 0) := fun y hy => by
    rw [dlmf_1_15_48 h1 hμ hg (le_of_lt hy)]
    congr 1
    simp [N, fracDerivOrder]
  rw [fracDeriv, iteratedDeriv_congr_Ioi hsg _ hx]
  exact iteratedDeriv_fracIntegral_nat hg _ hx

/-! ### 1.15.52 -/

/-- DLMF 1.15.52: `D^k I^α = D^n I^{α+n−k}` for `k = 1, …, n` (ordinary derivatives `D^k`,
`Dⁿ`), on `(0, ∞)`, for `f` continuous on `[0, ∞)`. -/
theorem dlmf_1_15_52 {α : ℂ} (hα : 0 < α.re) {f : ℝ → ℂ} (hf : ContinuousOn f (Ici 0))
    {k n : ℕ} (hkn : k ≤ n) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fracIntegral α f) x =
      iteratedDeriv n (fracIntegral (α + n - k) f) x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [show α + ((k + j : ℕ) : ℂ) - k = (j : ℂ) + α by push_cast; ring, iteratedDeriv_add_eq]
  exact (iteratedDeriv_congr_Ioi (iteratedDeriv_fracIntegral_add hα hf j) k hx).symm

/-- 1.15.52 with `D^k` read as the fractional derivative of integer order `k` (which agrees with
the ordinary derivative, `fracDeriv_natCast`). -/
theorem dlmf_1_15_52_fracDeriv {α : ℂ} (hα : 0 < α.re) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ici 0)) {k n : ℕ} (hkn : k ≤ n) {x : ℝ} (hx : 0 < x) :
    fracDeriv k (fracIntegral α f) x = iteratedDeriv n (fracIntegral (α + n - k) f) x := by
  rw [fracDeriv_natCast (continuousOn_fracIntegral hα hf) k hx, dlmf_1_15_52 hα hf hkn hx]

/-! ### 1.15.53 -/

/-- The law of exponents `D^α D^β f = D^{α+β} f` (1.15.53) holds on `(0, ∞)` for
`f = I^γ g` with `g` continuous on `[0, ∞)` and `ℜγ > ℜ(α + β)`. -/
theorem dlmf_1_15_53 {α β γ : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : (α + β).re < γ.re)
    {g : ℝ → ℂ} (hg : ContinuousOn g (Ici 0)) {x : ℝ} (hx : 0 < x) :
    fracDeriv α (fracDeriv β (fracIntegral γ g)) x = fracDeriv (α + β) (fracIntegral γ g) x := by
  rw [add_re] at hγ
  have h1 : EqOn (fracDeriv β (fracIntegral γ g)) (fracIntegral (γ - β) g) (Ioi 0) :=
    fun y hy => fracDeriv_fracIntegral hβ (by linarith) hg hy
  rw [fracDeriv_congr_Ioi h1 α hx, fracDeriv_fracIntegral hα (by simp; linarith) hg hx,
    fracDeriv_fracIntegral (by simp; linarith) (by simp; linarith) hg hx]
  congr 1
  ring

/-- The boundary case `γ = α + β` of `dlmf_1_15_53`: both sides equal `g`. -/
theorem dlmf_1_15_53_self {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Ici 0)) {x : ℝ} (hx : 0 < x) :
    fracDeriv α (fracDeriv β (fracIntegral (α + β) g)) x =
      fracDeriv (α + β) (fracIntegral (α + β) g) x := by
  have h1 : EqOn (fracDeriv β (fracIntegral (α + β) g)) (fracIntegral α g) (Ioi 0) :=
    fun y hy => by
      rw [fracDeriv_fracIntegral hβ (by simp; linarith) hg hy]
      congr 1; ring
  rw [fracDeriv_congr_Ioi h1 α hx, fracDeriv_fracIntegral_self hα hg hx,
    fracDeriv_fracIntegral_self (by simp; linarith) hg hx]

/-! ### Powers, and the failure of 1.15.53 in general -/

/-- `I^ν t^ρ = Γ(ρ + 1)/Γ(ρ + ν + 1) x^{ρ+ν}` for `ℜρ > −1`, `ℜν > 0`, `x > 0`. -/
theorem fracIntegral_cpow {ν ρ : ℂ} (hν : 0 < ν.re) (hρ : -1 < ρ.re) {x : ℝ} (hx : 0 < x) :
    fracIntegral ν (fun t => (t : ℂ) ^ ρ) x =
      Gamma (ρ + 1) / Gamma (ρ + ν + 1) * (x : ℂ) ^ (ρ + ν) := by
  have hρ1 : 0 < (ρ + 1).re := by simp; linarith
  have h := (integral_beta_shift hν hρ1 hx).2
  simp only [sub_zero, add_sub_cancel_right] at h
  rw [fracIntegral, fracIntegralFrom, h, show ν + (ρ + 1) - 1 = ρ + ν by ring,
    show ν + (ρ + 1) = ρ + ν + 1 by ring]
  have hGa : Gamma ν ≠ 0 := Gamma_ne_zero_of_re_pos hν
  field_simp

/-- `dⁿ/dxⁿ (c x^s) = c s(s − 1)⋯(s − n + 1) x^{s−n}` on `(0, ∞)`. -/
theorem iteratedDeriv_const_mul_cpow (c s : ℂ) (n : ℕ) :
    EqOn (iteratedDeriv n fun y : ℝ => c * (y : ℂ) ^ s)
      (fun y => c * (∏ j ∈ Finset.range n, (s - j)) * (y : ℂ) ^ (s - n)) (Ioi 0) := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    rw [iteratedDeriv_succ, EventuallyEq.deriv_eq
      (Filter.mem_of_superset (Ioi_mem_nhds hy) fun _ hz => ih hz)]
    have hd := ((Complex.hasStrictDerivAt_cpow_const (c := s - n)
      (ofReal_mem_slitPlane.mpr hy)).hasDerivAt.comp_ofReal).const_mul
      (c * ∏ j ∈ Finset.range n, (s - j))
    rw [hd.deriv, Finset.prod_range_succ]
    push_cast
    ring_nf

/-- The fractional derivative of a power: `D^μ t^ρ = Γ(ρ + 1)/Γ(ρ + n − μ + 1)
(ρ + n − μ)(ρ + n − μ − 1)⋯(ρ − μ + 1) x^{ρ−μ}` with `n = ⌊ℜμ⌋ + 1`, for `x > 0`. -/
theorem fracDeriv_cpow {μ ρ : ℂ} (hρ : -1 < ρ.re) {x : ℝ} (hx : 0 < x) :
    fracDeriv μ (fun t => (t : ℂ) ^ ρ) x =
      Gamma (ρ + 1) / Gamma (ρ + (fracDerivOrder μ - μ) + 1) *
        (∏ j ∈ Finset.range (fracDerivOrder μ), (ρ + (fracDerivOrder μ - μ) - j)) *
          (x : ℂ) ^ (ρ - μ) := by
  have hlt := lt_fracDerivOrder μ
  obtain ⟨N, hN⟩ : ∃ N, fracDerivOrder μ = N := ⟨_, rfl⟩
  rw [hN] at hlt ⊢
  have hν : 0 < ((N : ℂ) - μ).re := by simp; linarith
  have h1 : EqOn (fracIntegral ((N : ℂ) - μ) fun t => (t : ℂ) ^ ρ)
      (fun y => Gamma (ρ + 1) / Gamma (ρ + (N - μ) + 1) * (y : ℂ) ^ (ρ + (N - μ))) (Ioi 0) :=
    fun y hy => fracIntegral_cpow hν hρ hy
  rw [fracDeriv, hN, iteratedDeriv_congr_Ioi h1 _ hx, iteratedDeriv_const_mul_cpow _ _ _ hx]
  rw [show ρ + ((N : ℂ) - μ) - (N : ℂ) = ρ - μ by ring]

theorem fracDerivOrder_eq {μ : ℂ} {n : ℕ} (h1 : (n : ℝ) ≤ μ.re) (h2 : μ.re < n + 1) :
    fracDerivOrder μ = n + 1 := by
  have h : ⌊μ.re⌋₊ = n := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) h1)).mpr ⟨h1, h2⟩
  rw [fracDerivOrder, h]

theorem cpow_ofReal_ne_zero {x : ℝ} (hx : 0 < x) (s : ℂ) : (x : ℂ) ^ s ≠ 0 := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
  exact Complex.exp_ne_zero _

theorem not_isInt_of_mul {q : ℂ} {a b : ℤ} (hb : 0 < b) (hq : q = (a : ℂ) / b) (hab : ¬ b ∣ a) :
    ∀ m : ℤ, q ≠ m := by
  intro m h
  rw [hq] at h
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [div_eq_iff hb'] at h
  have : a = m * b := by exact_mod_cast h
  exact hab ⟨m, by rw [this, mul_comm]⟩

/-- 1.15.53 fails without further hypotheses on `f`, even for `f` continuous on `[0, ∞)` and
none of `α`, `β`, `α + β` an integer: with `α = 1/3`, `β = 3/2`, `f(t) = t^{1/2}`,
`D^β f = 0` (so `D^α D^β f = 0`), while
`D^{α+β} f(x) = −(2/9) Γ(3/2)/Γ(5/3) x^{−4/3} ≠ 0`. -/
theorem dlmf_1_15_53_counterexample :
    ∃ α β : ℂ, 0 < α.re ∧ 0 < β.re ∧ (∀ m : ℤ, α ≠ m ∧ β ≠ m ∧ α + β ≠ m) ∧
      ∃ f : ℝ → ℂ, ContinuousOn f (Ici 0) ∧
        ∀ x : ℝ, 0 < x → fracDeriv α (fracDeriv β f) x ≠ fracDeriv (α + β) f x := by
  refine ⟨1 / 3, 3 / 2, by norm_num, by norm_num, fun m => ⟨?_, ?_, ?_⟩,
    fun t => (t : ℂ) ^ (1 / 2 : ℂ), ?_, fun x hx => ?_⟩
  · exact not_isInt_of_mul (a := 1) (b := 3) (by norm_num) (by norm_num) (by decide) m
  · exact not_isInt_of_mul (a := 3) (b := 2) (by norm_num) (by norm_num) (by decide) m
  · exact not_isInt_of_mul (a := 11) (b := 6) (by norm_num) (by norm_num) (by decide) m
  · exact (Continuous.continuousOn (continuous_iff_continuousAt.mpr fun t =>
      continuousAt_ofReal_cpow_const _ _ (Or.inl (by norm_num))))
  have hρ : -1 < (1 / 2 : ℂ).re := by norm_num
  have hβ : fracDerivOrder (3 / 2 : ℂ) = 1 + 1 :=
    fracDerivOrder_eq (by norm_num) (by norm_num)
  have hαβ : fracDerivOrder (1 / 3 + 3 / 2 : ℂ) = 1 + 1 :=
    fracDerivOrder_eq (by norm_num) (by norm_num)
  have h0 : EqOn (fracDeriv (3 / 2) fun t => (t : ℂ) ^ (1 / 2 : ℂ)) (fun _ => 0) (Ioi 0) :=
    fun y hy => by
      rw [fracDeriv_cpow hρ hy, hβ]
      simp [Finset.prod_range_succ]
      norm_num
  rw [fracDeriv_congr_Ioi h0 _ hx, fracDeriv_zero_fun, fracDeriv_cpow hρ hx, hαβ]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hG1 : Gamma (1 / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG2 : Gamma (1 / 2 + (((1 + 1 : ℕ) : ℂ) - (1 / 3 + 3 / 2)) + 1) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by norm_num)
  refine (mul_ne_zero (mul_ne_zero (div_ne_zero hG1 hG2) ?_) (cpow_ofReal_ne_zero hx _)).symm
  push_cast
  norm_num

/-- DLMF's remark `D^{1/2} D ≠ D^{3/2}`: for `f = 1`, `D^{1/2}(D f) = 0` while
`D^{3/2} f(x) = −(1/4) x^{−3/2}/Γ(3/2) ≠ 0`. -/
theorem dlmf_1_15_vii_half_deriv {x : ℝ} (hx : 0 < x) :
    fracDeriv (1 / 2) (deriv fun _ => (1 : ℂ)) x ≠ fracDeriv (3 / 2) (fun _ => (1 : ℂ)) x := by
  have h1 : (fun _ : ℝ => (1 : ℂ)) = fun t : ℝ => (t : ℂ) ^ (0 : ℂ) :=
    funext fun t => (cpow_zero _).symm
  have hd : (deriv fun _ : ℝ => (1 : ℂ)) = fun _ => 0 := funext fun t => by simp
  have hβ : fracDerivOrder (3 / 2 : ℂ) = 1 + 1 := fracDerivOrder_eq (by norm_num) (by norm_num)
  rw [hd, fracDeriv_zero_fun, h1, fracDeriv_cpow (by norm_num) hx, hβ]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hG1 : Gamma (0 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hG2 : Gamma (0 + (((1 + 1 : ℕ) : ℂ) - 3 / 2) + 1) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by norm_num)
  refine (mul_ne_zero (mul_ne_zero (div_ne_zero hG1 hG2) ?_) (cpow_ofReal_ne_zero hx _)).symm
  push_cast
  norm_num

end Azurite.DLMF
