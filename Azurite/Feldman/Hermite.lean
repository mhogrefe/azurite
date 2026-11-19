/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fel'dman, Lemma 7: Hermite interpolation with small data

N. I. Fel'dman, *Approximation of certain transcendental numbers. I*, Izv. Akad. Nauk SSSR
Ser. Mat. 15 (1951), 53–74, §1, Lemma 7: a function whose derivatives of order `< T` are small
at many points `a_x` is small on a disc.  Fel'dman uses Hermite's interpolation formula as a
contour integral over a circle and small circles round the nodes.  Here the same estimate is
obtained without integrals over a domain with holes:

* **Schwarz's lemma with zeros** (`norm_le_of_zeros`).  An entire `F` that vanishes at the
  points of a multiset `s` (with multiplicities) is `∏_{b ∈ s} (z − b) · G(z)` with `G` entire
  (`exists_eq_prod_mul`, by `dslope` one zero at a time, the orders tracked by
  `analyticOrderAt`), and the maximum principle for `G` on `|w| = r` gives
  `|F(z)| ≤ ∏_b |z − b| · M / d^{|s|}` when `|F| ≤ M` and `|w − b| ≥ d` on the circle.
* **The Hermite interpolant** (`hermH`).  With `Q_x = ∏_{x' ≠ x} (z − a_{x'})^T`, `τ_x` the Taylor
  polynomial of `φ` at `a_x` of degree `< T`, and `V_x` that of `τ_x/Q_x`: `H = ∑_x Q_x V_x`.
  `φ − H` vanishes to order `T` at every node (`vanishTo_sub_hermH`, from Taylor's formula with
  an analytic remainder, `exists_taylor_remainder`), and `H` is small when the data are
  (`norm_hermH_le`): the coefficients of `V_x` by Cauchy's estimates on `|ξ − a_x| = ρ`, where
  `|τ_x| ≤ δ e^ρ` and `|Q_x| ≥ D`.
* **Lemma 7** (`norm_le_of_small_jets`): Schwarz's lemma for `φ − H`, so
  `|φ(z)| ≤ E + (L_z/d)^(T|I|) (M + E)`, `E = |I| L^(T(|I|−1)) T (δ e^ρ/D) (L/ρ)^T`.

The nodes are abstract (`a : ι → ℂ` on a finset `I`); for `π` they are `πix`, `|x| ≤ y₀`, with
`ρ = π/2` and `D ≥ ((π/2)^{2y₀} (y₀!)²)^T`.  The factor `(L_z/d)^(T|I|)` replaces Fel'dman's
`((k₂² + 1)/(k² − 1))^{y₀t₀}`, and derivatives of `φ` follow by Cauchy's estimate at the point
of use.
-/

namespace Azurite.Feldman

open Complex Metric Set Filter Topology

/-! ### Schwarz's lemma with zeros -/

/-- An entire function with zeros at the points of `s`, counted with multiplicity, is the
product of the factors `z − b` and an entire function. -/
theorem exists_eq_prod_mul : ∀ (s : Multiset ℂ) {F : ℂ → ℂ}, Differentiable ℂ F →
    (∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt F c) →
      ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = (s.map fun b => z - b).prod * G z := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
    intro F hF _
    exact ⟨F, hF, fun z => by simp⟩
  | cons b s ih =>
    intro F hF h
    have hFb : F b = 0 := by
      apply apply_eq_zero_of_analyticOrderAt_ne_zero
      intro h0
      have := h b
      rw [h0, Multiset.count_cons_self] at this
      simp at this
    have hG₁ : Differentiable ℂ (dslope F b) := by
      rw [← differentiableOn_univ]
      exact (differentiableOn_dslope (isOpen_univ.mem_nhds (mem_univ b))).mpr
        hF.differentiableOn
    have heq : ∀ z, F z = (z - b) * dslope F b z := fun z => by
      have := sub_smul_dslope F b z
      rw [hFb, sub_zero, smul_eq_mul] at this
      exact this.symm
    have hfun : F = (· - b) * dslope F b := funext heq
    have hord : ∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt (dslope F b) c := by
      intro c
      have hmul : analyticOrderAt F c
          = analyticOrderAt (· - b) c + analyticOrderAt (dslope F b) c := by
        conv_lhs => rw [hfun]
        exact analyticOrderAt_mul (by fun_prop) (hG₁.analyticAt c)
      have hc := h c
      rw [hmul] at hc
      by_cases hcb : c = b
      · subst hcb
        rw [Multiset.count_cons_self, analyticOrderAt_id_sub_const_self] at hc
        push_cast at hc
        rw [add_comm] at hc
        exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp hc
      · rw [Multiset.count_cons_of_ne hcb, analyticOrderAt_id_sub_const_of_ne hcb, zero_add]
          at hc
        exact hc
    obtain ⟨G, hG, hGeq⟩ := ih hG₁ hord
    refine ⟨G, hG, fun z => ?_⟩
    rw [heq z, hGeq z, Multiset.map_cons, Multiset.prod_cons]
    ring

theorem norm_prod_sub (s : Multiset ℂ) (w : ℂ) :
    ‖(s.map fun b => w - b).prod‖ = (s.map fun b => ‖w - b‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih => rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih, Multiset.map_cons,
      Multiset.prod_cons]

theorem pow_card_le_prod_norm_sub (s : Multiset ℂ) (w : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ b ∈ s, d ≤ ‖w - b‖) : d ^ Multiset.card s ≤ (s.map fun b => ‖w - b‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, mul_comm]
    exact mul_le_mul (h b (Multiset.mem_cons_self b s))
      (ih fun c hc => h c (Multiset.mem_cons_of_mem hc)) (by positivity)
      (hd.le.trans (h b (Multiset.mem_cons_self b s)))

/-- **Schwarz's lemma with zeros**: an entire `F` with zeros at the points of `s` (with
multiplicity), `|F| ≤ M` on the circle `|w| = r` and `|w − b| ≥ d > 0` there for the zeros
`b`, satisfies `|F(z)| d^{|s|} ≤ ∏_b |z − b| · M` for `|z| ≤ r`. -/
theorem norm_le_of_zeros {F : ℂ → ℂ} (hF : Differentiable ℂ F) (s : Multiset ℂ)
    (hs : ∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt F c) {r M d : ℝ} (hd : 0 < d)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖F w‖ ≤ M)
    (hdist : ∀ w ∈ sphere (0 : ℂ) r, ∀ b ∈ s, d ≤ ‖w - b‖) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖F z‖ * d ^ Multiset.card s ≤ (s.map fun b => ‖z - b‖).prod * M := by
  obtain ⟨G, hG, hGeq⟩ := exists_eq_prod_mul s hF hs
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hM0 : 0 ≤ M := by
    have hw : (r : ℂ) ∈ sphere (0 : ℂ) r := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (norm_nonneg _).trans (hM _ hw)
  have hnp : ∀ w : ℂ, ‖(s.map fun b => w - b).prod‖ = (s.map fun b => ‖w - b‖).prod :=
    norm_prod_sub s
  -- on the circle `|G| ≤ M / d^{|s|}`
  have hGs : ∀ w ∈ sphere (0 : ℂ) r, ‖G w‖ ≤ M / d ^ Multiset.card s := by
    intro w hw
    have hprod : d ^ Multiset.card s ≤ (s.map fun b => ‖w - b‖).prod :=
      pow_card_le_prod_norm_sub s w hd (hdist w hw)
    have h1 := hM w hw
    rw [hGeq w, norm_mul, hnp] at h1
    rw [le_div_iff₀ (by positivity)]
    calc ‖G w‖ * d ^ Multiset.card s ≤ ‖G w‖ * (s.map fun b => ‖w - b‖).prod :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = (s.map fun b => ‖w - b‖).prod * ‖G w‖ := mul_comm _ _
      _ ≤ M := h1
  have hGz : ‖G z‖ ≤ M / d ^ Multiset.card s := by
    rcases hr.eq_or_lt with h0 | h0
    · have hz0 : z = 0 := by
        rw [← norm_eq_zero]
        exact le_antisymm (h0 ▸ hz) (norm_nonneg _)
      exact hGs z (by rw [mem_sphere_zero_iff_norm, hz0, norm_zero, h0])
    · exact norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
        hG.diffContOnCl (fun w hw => hGs w (frontier_ball_subset_sphere hw))
        (by rw [closure_ball _ h0.ne']; exact mem_closedBall_zero_iff.mpr hz)
  rw [hGeq z, norm_mul, hnp]
  have hpz : 0 ≤ (s.map fun b => ‖z - b‖).prod :=
    Multiset.prod_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp hx
      exact norm_nonneg _
  calc (s.map fun b => ‖z - b‖).prod * ‖G z‖ * d ^ Multiset.card s
      = (s.map fun b => ‖z - b‖).prod * (‖G z‖ * d ^ Multiset.card s) := by ring
    _ ≤ (s.map fun b => ‖z - b‖).prod * M := by
        refine mul_le_mul_of_nonneg_left ?_ hpz
        rw [← le_div_iff₀ (by positivity)]
        exact hGz

/-! ### Taylor polynomials and vanishing to order `T` -/

/-- The Taylor polynomial of degree `< T` of `g` at `a`, as a function. -/
noncomputable def taylorAt (g : ℂ → ℂ) (a : ℂ) (T : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range T, (z - a) ^ i / i.factorial * iteratedDeriv i g a

theorem differentiable_taylorAt (g : ℂ → ℂ) (a : ℂ) (T : ℕ) :
    Differentiable ℂ (taylorAt g a T) := by
  unfold taylorAt
  fun_prop

/-- Taylor's formula with the remainder `(z − a)^T F(z)`, `F` analytic at `a`. -/
theorem exists_taylor_remainder {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a) (T : ℕ) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F a ∧ ∀ z, g z = taylorAt g a T z + (z - a) ^ T * F z := by
  have hg₀ : AnalyticAt ℂ (fun w => g (a + w)) 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => a + w) 0 := by fun_prop
    exact AnalyticAt.comp_of_eq hg h1 (by simp)
  obtain ⟨F₀, hF₀, hF⟩ := hg₀.exists_eq_sum_add_pow_mul T
  refine ⟨fun z => F₀ (z - a), ?_, fun z => ?_⟩
  · have h1 : AnalyticAt ℂ (fun z : ℂ => z - a) a := by fun_prop
    exact AnalyticAt.comp_of_eq hF₀ h1 (by simp)
  · have := hF (z - a)
    rw [show a + (z - a) = z by ring] at this
    rw [this]
    unfold taylorAt
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, iteratedDeriv_comp_const_add]
    simp

/-- `f` vanishes to order `T` at `a`: `f(z) = (z − a)^T g(z)` near `a` with `g` analytic. -/
def VanishTo (T : ℕ) (a : ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝 a, f z = (z - a) ^ T * g z

theorem VanishTo.add {T : ℕ} {a : ℂ} {f₁ f₂ : ℂ → ℂ} (h₁ : VanishTo T a f₁)
    (h₂ : VanishTo T a f₂) : VanishTo T a fun z => f₁ z + f₂ z := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  refine ⟨fun z => g₁ z + g₂ z, hg₁.add hg₂, ?_⟩
  filter_upwards [e₁, e₂] with z h1 h2
  rw [h1, h2]
  ring

theorem VanishTo.sub {T : ℕ} {a : ℂ} {f₁ f₂ : ℂ → ℂ} (h₁ : VanishTo T a f₁)
    (h₂ : VanishTo T a f₂) : VanishTo T a fun z => f₁ z - f₂ z := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  refine ⟨fun z => g₁ z - g₂ z, hg₁.sub hg₂, ?_⟩
  filter_upwards [e₁, e₂] with z h1 h2
  rw [h1, h2]
  ring

theorem VanishTo.sum {T : ℕ} {a : ℂ} {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, VanishTo T a (f i)) : VanishTo T a fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun z => by simp⟩
  | insert i s hi ih =>
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have := h1.add h2
    simpa only [Finset.sum_insert hi] using this

theorem VanishTo.le_order {T : ℕ} {a : ℂ} {f : ℂ → ℂ} (h : VanishTo T a f)
    (hf : AnalyticAt ℂ f a) : (T : ℕ∞) ≤ analyticOrderAt f a := by
  obtain ⟨g, hg, e⟩ := h
  exact (natCast_le_analyticOrderAt hf).mpr ⟨g, hg, by simpa only [smul_eq_mul] using e⟩

/-! ### The Hermite interpolant -/

section Hermite

variable {ι : Type*} [DecidableEq ι] (I : Finset ι) (a : ι → ℂ) (T : ℕ)

/-- `Q_x(z) = ∏_{x' ≠ x} (z − a_{x'})^T`. -/
noncomputable def hermQ (x : ι) (z : ℂ) : ℂ := ∏ x' ∈ I.erase x, (z - a x') ^ T

theorem differentiable_hermQ (x : ι) : Differentiable ℂ (hermQ I a T x) := by
  unfold hermQ
  fun_prop

/-- `V_x`: the Taylor polynomial of degree `< T` at `a_x` of `τ_x/Q_x`, `τ_x` the Taylor
polynomial of `φ` at `a_x`. -/
noncomputable def hermV (φ : ℂ → ℂ) (x : ι) : ℂ → ℂ :=
  taylorAt (fun z => taylorAt φ (a x) T z / hermQ I a T x z) (a x) T

/-- The Hermite interpolant `H = ∑_x Q_x V_x` of `φ` at the nodes `a_x` with multiplicity
`T`. -/
noncomputable def hermH (φ : ℂ → ℂ) (z : ℂ) : ℂ := ∑ x ∈ I, hermQ I a T x z * hermV I a T φ x z

theorem differentiable_hermH (φ : ℂ → ℂ) : Differentiable ℂ (hermH I a T φ) := by
  unfold hermH
  have h1 : ∀ x, Differentiable ℂ (hermV I a T φ x) := fun x => differentiable_taylorAt _ _ _
  have h2 : ∀ x, Differentiable ℂ (hermQ I a T x) := differentiable_hermQ I a T
  fun_prop

/-- `φ − H` vanishes to order `T` at every node. -/
theorem vanishTo_sub_hermH {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {x : ι} (hx : x ∈ I)
    (hQ : hermQ I a T x (a x) ≠ 0) :
    VanishTo T (a x) fun z => φ z - hermH I a T φ z := by
  -- `φ − τ`
  obtain ⟨F₁, hF₁, e₁⟩ := exists_taylor_remainder (hφ.analyticAt (a x)) T
  have h1 : VanishTo T (a x) fun z => φ z - taylorAt φ (a x) T z :=
    ⟨F₁, hF₁, Filter.Eventually.of_forall fun z => by dsimp only; rw [e₁ z]; ring⟩
  -- `τ − Q V`
  have hψ : AnalyticAt ℂ (fun z => taylorAt φ (a x) T z / hermQ I a T x z) (a x) :=
    ((differentiable_taylorAt φ (a x) T).analyticAt _).div
      ((differentiable_hermQ I a T x).analyticAt _) hQ
  obtain ⟨F₂, hF₂, e₂⟩ := exists_taylor_remainder hψ T
  have h2 : VanishTo T (a x) fun z =>
      taylorAt φ (a x) T z - hermQ I a T x z * hermV I a T φ x z := by
    refine ⟨fun z => hermQ I a T x z * F₂ z,
      ((differentiable_hermQ I a T x).analyticAt _).mul hF₂, ?_⟩
    have hne : ∀ᶠ z in 𝓝 (a x), hermQ I a T x z ≠ 0 :=
      (differentiable_hermQ I a T x).continuous.continuousAt.eventually_ne hQ
    filter_upwards [hne] with z hz
    have e := e₂ z
    have hτ : taylorAt φ (a x) T z
        = hermQ I a T x z * (taylorAt φ (a x) T z / hermQ I a T x z) := by
      rw [mul_div_cancel₀ _ hz]
    rw [hτ, e]
    unfold hermV
    ring
  -- the other terms
  have h3 : VanishTo T (a x) fun z =>
      ∑ x' ∈ I.erase x, hermQ I a T x' z * hermV I a T φ x' z := by
    refine VanishTo.sum _ fun x' hx' => ?_
    have hmem : x ∈ I.erase x' :=
      Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hx').symm, hx⟩
    refine ⟨fun z => (∏ x'' ∈ (I.erase x').erase x, (z - a x'') ^ T) * hermV I a T φ x' z,
      ?_, Filter.Eventually.of_forall fun z => ?_⟩
    · have hd : Differentiable ℂ fun z : ℂ =>
          (∏ x'' ∈ (I.erase x').erase x, (z - a x'') ^ T) * hermV I a T φ x' z := by
        have h1 : Differentiable ℂ (hermV I a T φ x') := differentiable_taylorAt _ _ _
        fun_prop
      exact hd.analyticAt _
    · unfold hermQ
      dsimp only
      rw [← Finset.mul_prod_erase (I.erase x') (fun x'' => (z - a x'') ^ T) hmem]
      ring
  have := (h1.add h2).sub h3
  refine (show (fun z => φ z - hermH I a T φ z) = _ from ?_) ▸ this
  funext z
  unfold hermH
  rw [← Finset.add_sum_erase I _ hx]
  ring

variable {I a T}

/-- The Taylor polynomial of `φ` on the disc of radius `ρ` round a node. -/
theorem norm_taylorAt_le {φ : ℂ → ℂ} {c : ℂ} {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ i < T, ‖iteratedDeriv i φ c‖ ≤ δ) {ξ : ℂ} (hξ : ‖ξ - c‖ ≤ ρ) :
    ‖taylorAt φ c T ξ‖ ≤ δ * Real.exp ρ := by
  unfold taylorAt
  calc ‖∑ i ∈ Finset.range T, (ξ - c) ^ i / i.factorial * iteratedDeriv i φ c‖
      ≤ ∑ i ∈ Finset.range T, ρ ^ i / i.factorial * δ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
        exact mul_le_mul (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hξ i) (Nat.cast_nonneg _))
          (hδ i (Finset.mem_range.mp hi)) (norm_nonneg _) (by positivity)
    _ = δ * ∑ i ∈ Finset.range T, ρ ^ i / i.factorial := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ δ * Real.exp ρ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hρ T) hδ0

/-- The Hermite interpolant of small data is small. -/
theorem norm_hermH_le {φ : ℂ → ℂ} {ρ D δ L : ℝ} (hρ : 0 < ρ) (hD0 : 0 < D)
    (hD : ∀ x ∈ I, ∀ ξ ∈ closedBall (a x) ρ, D ≤ ‖hermQ I a T x ξ‖) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ∈ I, ∀ i < T, ‖iteratedDeriv i φ (a x)‖ ≤ δ) (hL : ρ ≤ L) {w : ℂ}
    (hw : ∀ x ∈ I, ‖w - a x‖ ≤ L) :
    ‖hermH I a T φ w‖ ≤ I.card
      * (L ^ (T * (I.card - 1)) * (T * (δ * Real.exp ρ / D) * (L / ρ) ^ T)) := by
  have hL0 : 0 ≤ L := hρ.le.trans hL
  have hB : 1 ≤ L / ρ := (one_le_div hρ).mpr hL
  set C : ℝ := δ * Real.exp ρ / D with hC
  have hC0 : 0 ≤ C := by positivity
  unfold hermH
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [norm_mul]
  -- `|Q_x(w)|`
  have hQw : ‖hermQ I a T x w‖ ≤ L ^ (T * (I.card - 1)) := by
    unfold hermQ
    have hpow : L ^ (T * (I.card - 1)) = ∏ _x' ∈ I.erase x, L ^ T := by
      rw [Finset.prod_const, Finset.card_erase_of_mem hx, ← pow_mul]
    rw [norm_prod, hpow]
    refine Finset.prod_le_prod₀ (fun x' _ => norm_nonneg ((w - a x') ^ T)) fun x' hx' => ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hw x' (Finset.mem_of_mem_erase hx')) T
  -- Cauchy's estimates for `ψ = τ/Q`
  set ψ : ℂ → ℂ := fun z => taylorAt φ (a x) T z / hermQ I a T x z with hψ
  have hQne : ∀ ξ ∈ closedBall (a x) ρ, hermQ I a T x ξ ≠ 0 := fun ξ hξ h0 => by
    have := hD x hx ξ hξ
    rw [h0, norm_zero] at this
    linarith
  have hdiff : DifferentiableOn ℂ ψ (closedBall (a x) ρ) := fun ξ hξ =>
    (((differentiable_taylorAt φ (a x) T).differentiableAt).div
      ((differentiable_hermQ I a T x).differentiableAt) (hQne ξ hξ)).differentiableWithinAt
  have hsphere : ∀ ξ ∈ sphere (a x) ρ, ‖ψ ξ‖ ≤ C := by
    intro ξ hξ
    have hξ' : ξ ∈ closedBall (a x) ρ := sphere_subset_closedBall hξ
    rw [hψ, norm_div]
    exact div_le_div₀ (by positivity)
      (norm_taylorAt_le hρ.le hδ0 (hδ x hx) (by simpa [dist_eq_norm] using hξ')) hD0
      (hD x hx ξ hξ')
  have hcauchy : ∀ j, ‖iteratedDeriv j ψ (a x)‖ ≤ j.factorial * C / ρ ^ j := fun j =>
    norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hρ
      (hdiff.diffContOnCl_ball subset_rfl) hsphere
  -- `|V_x(w)|`
  have hVw : ‖hermV I a T φ x w‖ ≤ T * C * (L / ρ) ^ T := by
    unfold hermV taylorAt
    calc ‖∑ j ∈ Finset.range T, (w - a x) ^ j / j.factorial * iteratedDeriv j ψ (a x)‖
        ≤ ∑ _j ∈ Finset.range T, C * (L / ρ) ^ T := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
          have hj' := Finset.mem_range.mp hj
          have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
          have h1 : ‖w - a x‖ ^ j / j.factorial * ‖iteratedDeriv j ψ (a x)‖
              ≤ ‖w - a x‖ ^ j / j.factorial * (j.factorial * C / ρ ^ j) :=
            mul_le_mul_of_nonneg_left (hcauchy j) (by positivity)
          have h2 : ‖w - a x‖ ^ j / j.factorial * (j.factorial * C / ρ ^ j)
              = C * (‖w - a x‖ / ρ) ^ j := by
            rw [div_pow]
            field_simp
          have h3 : (‖w - a x‖ / ρ) ^ j ≤ (L / ρ) ^ T :=
            (pow_le_pow_left₀ (by positivity)
              (div_le_div_of_nonneg_right (hw x hx) hρ.le) j).trans
              (pow_le_pow_right₀ hB hj'.le)
          rw [h2] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left h3 hC0)
      _ = T * C * (L / ρ) ^ T := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  exact mul_le_mul hQw hVw (norm_nonneg _) (by positivity)

theorem prod_norm_sub_le_pow (s : Multiset ℂ) (z : ℂ) {L : ℝ} (h : ∀ b ∈ s, ‖z - b‖ ≤ L) :
    (s.map fun b => ‖z - b‖).prod ≤ L ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, mul_comm]
    have hprod : 0 ≤ (s.map fun b => ‖z - b‖).prod :=
      Multiset.prod_nonneg fun y hy => by
        obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hy
        exact norm_nonneg _
    exact mul_le_mul (ih fun c hc => h c (Multiset.mem_cons_of_mem hc))
      (h b (Multiset.mem_cons_self b s)) (norm_nonneg _)
      (pow_nonneg ((norm_nonneg _).trans (h b (Multiset.mem_cons_self b s))) _)

/-- **Fel'dman, Lemma 7** (Hermite interpolation with small data).  Let `φ` be entire with
`|φ⁽ⁱ⁾(a_x)| ≤ δ` for `i < T` at the distinct nodes `a_x`, `x ∈ I`.  Suppose `|Q_x| ≥ D > 0` on
the discs `|ξ − a_x| ≤ ρ`; `|w − a_x| ≤ L` for `|w| ≤ r` (`L ≥ ρ`); and on the circle `|w| = r`:
`|w − a_x| ≥ d > 0` and `|φ(w)| ≤ M`.  Then for `|z| ≤ r` with `|z − a_x| ≤ L_z`,

  `|φ(z)| ≤ E + (L_z/d)^(T |I|) (M + E)`,   `E = |I| L^(T(|I|−1)) T (δ e^ρ/D) (L/ρ)^T`. -/
theorem norm_le_of_small_jets {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hinj : Set.InjOn a I)
    {ρ D δ L r d M Lz : ℝ} (hρ : 0 < ρ) (hD0 : 0 < D)
    (hD : ∀ x ∈ I, ∀ ξ ∈ closedBall (a x) ρ, D ≤ ‖hermQ I a T x ξ‖) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ∈ I, ∀ i < T, ‖iteratedDeriv i φ (a x)‖ ≤ δ) (hL : ρ ≤ L)
    (hLr : ∀ w : ℂ, ‖w‖ ≤ r → ∀ x ∈ I, ‖w - a x‖ ≤ L) (hd : 0 < d)
    (hdr : ∀ w ∈ sphere (0 : ℂ) r, ∀ x ∈ I, d ≤ ‖w - a x‖)
    (hM : ∀ w ∈ sphere (0 : ℂ) r, ‖φ w‖ ≤ M) {z : ℂ} (hz : ‖z‖ ≤ r)
    (hLz : ∀ x ∈ I, ‖z - a x‖ ≤ Lz) :
    ‖φ z‖ ≤ I.card * (L ^ (T * (I.card - 1)) * (T * (δ * Real.exp ρ / D) * (L / ρ) ^ T))
      + (Lz / d) ^ (T * I.card) * (M + I.card
        * (L ^ (T * (I.card - 1)) * (T * (δ * Real.exp ρ / D) * (L / ρ) ^ T))) := by
  set E : ℝ := I.card * (L ^ (T * (I.card - 1)) * (T * (δ * Real.exp ρ / D) * (L / ρ) ^ T))
    with hE
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hH : ∀ w : ℂ, ‖w‖ ≤ r → ‖hermH I a T φ w‖ ≤ E := fun w hw =>
    norm_hermH_le hρ hD0 hD hδ0 hδ hL (hLr w hw)
  set F : ℂ → ℂ := fun z => φ z - hermH I a T φ z with hF
  have hFd : Differentiable ℂ F := hφ.sub (differentiable_hermH I a T φ)
  set s : Multiset ℂ := T • (I.val.map a) with hs
  have hnd : (I.val.map a).Nodup :=
    Multiset.Nodup.map_on (fun x hx y hy h => hinj hx hy h) I.nodup
  have hcount : ∀ c, (s.count c : ℕ∞) ≤ analyticOrderAt F c := by
    intro c
    rw [hs, Multiset.count_nsmul]
    by_cases hc : c ∈ I.val.map a
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hc
      rw [Multiset.count_eq_one_of_mem hnd hc, mul_one]
      have hQ : hermQ I a T x (a x) ≠ 0 := fun h0 => by
        have := hD x hx (a x) (mem_closedBall_self hρ.le)
        rw [h0, norm_zero] at this
        linarith
      exact (vanishTo_sub_hermH I a T hφ hx hQ).le_order (hFd.analyticAt _)
    · rw [Multiset.count_eq_zero_of_notMem hc, mul_zero]
      simp
  have hcard : Multiset.card s = T * I.card := by
    rw [hs, Multiset.card_nsmul, Multiset.card_map, Finset.card_val]
  have hmem : ∀ b ∈ s, ∃ x ∈ I, a x = b := fun b hb => by
    have := Multiset.mem_of_mem_nsmul hb
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp this
    exact ⟨x, hx, rfl⟩
  have hFs : ∀ w ∈ sphere (0 : ℂ) r, ‖F w‖ ≤ M + E := fun w hw => by
    have hwn : ‖w‖ ≤ r := (mem_sphere_zero_iff_norm.mp hw).le
    exact (norm_sub_le _ _).trans (add_le_add (hM w hw) (hH w hwn))
  have hME : 0 ≤ M + E := by
    have hw : (r : ℂ) ∈ sphere (0 : ℂ) r := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (norm_nonneg _).trans (hFs _ hw)
  have hmain := norm_le_of_zeros hFd s hcount hd hFs
    (fun w hw b hb => by
      obtain ⟨x, hx, rfl⟩ := hmem b hb
      exact hdr w hw x hx) hz
  have hprod := prod_norm_sub_le_pow s z (L := Lz) fun b hb => by
    obtain ⟨x, hx, rfl⟩ := hmem b hb
    exact hLz x hx
  rw [hcard] at hmain hprod
  have hFz : ‖F z‖ ≤ (Lz / d) ^ (T * I.card) * (M + E) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact hmain.trans (mul_le_mul_of_nonneg_right hprod hME)
  have hφz : φ z = F z + hermH I a T φ z := by rw [hF]; ring
  rw [hφz]
  exact (norm_add_le _ _).trans (by linarith [hH z hz])

end Hermite

end Azurite.Feldman
