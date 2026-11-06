/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Gauss

/-!
# DLMF §4.9(i): Gauss quadrature and Markov's theorem

Tools for the logarithmic continued fractions 4.9.1 and 4.9.2. Their convergents are Padé
approximants of Stieltjes functions `∫ₐᵇ w(t)/(1 + z t) dt`, and these Padé approximants are the
Gauss quadrature sums of `1/(1 + z t)`. Gauss quadrature converges for every continuous integrand
(Markov's theorem), which gives convergence on the whole cut plane.

* `IsPolyFunDeg`: polynomial functions `ℂ → ℂ` of bounded degree.
* `polynomial_eq_zero_of_bound`: a polynomial of degree `< N` that is `O(z^N)` at `0` is `0`.
* `pade_unique`: two rational approximations `A/B`, `A'/B'` of the same function with errors
  `O(z^N)`, where `AB' − A'B` has degree `< N`, satisfy `AB' = A'B`.
* `gaussB`, `gaussA`, `gaussQuad`: the Gauss denominator `∏ₖ (1 + z tₖ)`, the numerator, and
  the quadrature sum `∑ₖ wₖ g(tₖ)`. Also `gaussA_eq`, `gauss_exact_C` (exactness for degree
  `< 2n`).
* `gauss_err_bound`: `B(z) ∫ w/(1 + z t) − A(z) = O(z^{2n})`.
* `gauss_tendsto`: Markov's theorem. Gauss quadrature converges for continuous integrands
  (via Weierstrass approximation and positivity of the Christoffel numbers).
-/

open Polynomial Finset Set MeasureTheory Filter Topology Complex

namespace Azurite.DLMF

/-! ### Polynomial functions of bounded degree -/

/-- `f` is a polynomial function of degree `≤ d`. -/
def IsPolyFunDeg (f : ℂ → ℂ) (d : ℕ) : Prop :=
  ∃ p : ℂ[X], p.natDegree ≤ d ∧ ∀ z, f z = p.eval z

namespace IsPolyFunDeg

variable {f g : ℂ → ℂ} {d e : ℕ}

theorem mono (h : IsPolyFunDeg f d) (hde : d ≤ e) : IsPolyFunDeg f e := by
  obtain ⟨p, hp, he⟩ := h; exact ⟨p, hp.trans hde, he⟩

theorem congr (h : IsPolyFunDeg f d) (e : ∀ z, f z = g z) : IsPolyFunDeg g d := by
  obtain ⟨p, hp, he⟩ := h; exact ⟨p, hp, fun z => by rw [← e, he]⟩

theorem add (hf : IsPolyFunDeg f d) (hg : IsPolyFunDeg g d) :
    IsPolyFunDeg (fun z => f z + g z) d := by
  obtain ⟨p, hp, hpe⟩ := hf; obtain ⟨q, hq, hqe⟩ := hg
  exact ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq), fun z => by simp [hpe, hqe]⟩

theorem sub (hf : IsPolyFunDeg f d) (hg : IsPolyFunDeg g d) :
    IsPolyFunDeg (fun z => f z - g z) d := by
  obtain ⟨p, hp, hpe⟩ := hf; obtain ⟨q, hq, hqe⟩ := hg
  exact ⟨p - q, (natDegree_sub_le _ _).trans (max_le hp hq), fun z => by simp [hpe, hqe]⟩

theorem mul (hf : IsPolyFunDeg f d) (hg : IsPolyFunDeg g e) :
    IsPolyFunDeg (fun z => f z * g z) (d + e) := by
  obtain ⟨p, hp, hpe⟩ := hf; obtain ⟨q, hq, hqe⟩ := hg
  exact ⟨p * q, natDegree_mul_le.trans (add_le_add hp hq), fun z => by simp [hpe, hqe]⟩

theorem const (c : ℂ) : IsPolyFunDeg (fun _ => c) 0 := ⟨C c, by simp, fun z => by simp⟩

theorem id : IsPolyFunDeg (fun z => z) 1 := ⟨X, natDegree_X_le, fun z => by simp⟩

theorem const_mul_id (c : ℂ) : IsPolyFunDeg (fun z => c * z) 1 :=
  ((const c).mul id).mono (by omega)

theorem one_add_mul (c : ℂ) : IsPolyFunDeg (fun z => 1 + z * c) 1 :=
  ((const 1).mono (by omega)).add ((const_mul_id c).congr fun z => by ring)

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} (h : ∀ i ∈ s, IsPolyFunDeg (F i) d) :
    IsPolyFunDeg (fun z => ∑ i ∈ s, F i z) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((const 0).mono (by omega)).congr fun z => by simp
  | insert i s hi ih =>
    exact ((h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))).congr
      fun z => by rw [sum_insert hi]

theorem prod {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} (h : ∀ i ∈ s, IsPolyFunDeg (F i) 1) :
    IsPolyFunDeg (fun z => ∏ i ∈ s, F i z) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const 1).congr fun z => by simp
  | insert i s hi ih =>
    exact (((h i (mem_insert_self i s)).mul (ih fun j hj => h j (mem_insert_of_mem hj))).mono
      (by rw [card_insert_of_notMem hi]; omega)).congr fun z => by rw [prod_insert hi]

theorem continuous (h : IsPolyFunDeg f d) : Continuous f := by
  obtain ⟨p, -, he⟩ := h
  rw [show f = fun z => p.eval z from funext he]; exact p.continuous

end IsPolyFunDeg

/-! ### Vanishing to high order -/

/-- A polynomial of degree `< N` that is `O(z^N)` near `0` vanishes. -/
theorem polynomial_eq_zero_of_bound (N : ℕ) : ∀ (p : ℂ[X]), p.natDegree < N → ∀ {δ C : ℝ},
    0 < δ → (∀ z : ℂ, z ≠ 0 → ‖z‖ < δ → ‖p.eval z‖ ≤ C * ‖z‖ ^ N) → p = 0 := by
  induction N with
  | zero => intro p h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro p hdeg δ C hδ hb
    have h0 : p.eval 0 = 0 := by
      have hc : Tendsto (fun z => p.eval z) (𝓝[≠] 0) (𝓝 (p.eval 0)) :=
        p.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hz : Tendsto (fun z : ℂ => C * ‖z‖ ^ (N + 1)) (𝓝[≠] 0) (𝓝 0) := by
        have : Tendsto (fun z : ℂ => C * ‖z‖ ^ (N + 1)) (𝓝 0) (𝓝 (C * ‖(0 : ℂ)‖ ^ (N + 1))) :=
          (continuous_const.mul (continuous_norm.pow _)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖p.eval z‖ ≤ C * ‖z‖ ^ (N + 1) := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ)]
          with z hz0 hzb
        exact hb z hz0 (by simpa using hzb)
      exact tendsto_nhds_unique hc (squeeze_zero_norm' hev hz)
    have hc0 : p.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero, h0]
    have hpX : ∀ z, p.eval z = z * p.divX.eval z := fun z => by
      conv_lhs => rw [← X_mul_divX_add p]
      simp [hc0]
    rcases N with _ | N
    · rw [eq_C_of_natDegree_eq_zero (by omega : p.natDegree = 0), hc0, C_0]
    have hq : p.divX = 0 := by
      refine ih p.divX (C := C)
        (by rw [natDegree_divX_eq_natDegree_tsub_one]; omega) hδ fun z hz hzδ => ?_
      have h1 := hb z hz hzδ
      rw [hpX, norm_mul, pow_succ] at h1
      have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      exact le_of_mul_le_mul_left (by linarith) hzn
    rw [← X_mul_divX_add p, hq, hc0]; simp

/-- **Uniqueness of Padé-type approximants**: if `B L − A` and `B' L − A'` are `O(z^N)` at `0`
(with `B`, `B'` continuous) and `A B' − A' B` is a polynomial of degree `< N`, then
`A B' = A' B`. -/
theorem pade_unique {A B A' B' L : ℂ → ℂ} {d N : ℕ}
    (hP : IsPolyFunDeg (fun z => A z * B' z - A' z * B z) d) (hdN : d < N)
    (hB : Continuous B) (hB' : Continuous B')
    (hE : ∃ δ > 0, ∃ C, ∀ z, ‖z‖ < δ → ‖B z * L z - A z‖ ≤ C * ‖z‖ ^ N)
    (hE' : ∃ δ > 0, ∃ C, ∀ z, ‖z‖ < δ → ‖B' z * L z - A' z‖ ≤ C * ‖z‖ ^ N) (z : ℂ) :
    A z * B' z = A' z * B z := by
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨δ, hδ, C, hC⟩ := hE
  obtain ⟨δ', hδ', C', hC'⟩ := hE'
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hB.continuousOn
  obtain ⟨M', hM'⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hB'.continuousOn
  have hδ'' : 0 < min (min δ δ') 1 := lt_min (lt_min hδ hδ') one_pos
  have hp0 : p = 0 := polynomial_eq_zero_of_bound N p (by omega) hδ'' fun u _ hu => by
    have hu1 : ‖u‖ < δ := hu.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hu2 : ‖u‖ < δ' := hu.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hu3 : u ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa using (hu.trans_le (min_le_right _ _)).le
    rw [← hpe]
    dsimp only
    have hid : A u * B' u - A' u * B u =
        (B' u * L u - A' u) * B u - (B u * L u - A u) * B' u := by ring
    rw [hid]
    have h1 := hC u hu1
    have h2 := hC' u hu2
    have h3 := hM u hu3
    have h4 := hM' u hu3
    have hn : 0 ≤ ‖u‖ ^ N := by positivity
    have hM0 : 0 ≤ M := (norm_nonneg _).trans h3
    have hM0' : 0 ≤ M' := (norm_nonneg _).trans h4
    calc ‖(B' u * L u - A' u) * B u - (B u * L u - A u) * B' u‖
        ≤ ‖B' u * L u - A' u‖ * ‖B u‖ + ‖B u * L u - A u‖ * ‖B' u‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ (C' * ‖u‖ ^ N) * M + (C * ‖u‖ ^ N) * M' := by
          gcongr
          · exact (norm_nonneg _).trans h2
          · exact (norm_nonneg _).trans h1
      _ = (C' * M + C * M') * ‖u‖ ^ N := by ring
  have := hpe z
  rw [hp0, eval_zero, sub_eq_zero] at this
  exact this

/-! ### Gauss quadrature as rational functions of `z` -/

variable {a b : ℝ} {w : ℝ → ℝ}

/-- The Gauss denominator `∏ₖ (1 + z tₖ)` over the zeros `tₖ` of `p`. -/
noncomputable def gaussB (p : ℝ[X]) (z : ℂ) : ℂ := ∏ k ∈ p.roots.toFinset, (1 + z * k)

/-- The Gauss numerator `∑ₖ wₖ ∏_{j ≠ k} (1 + z tⱼ)`. -/
noncomputable def gaussA (a b : ℝ) (w : ℝ → ℝ) (p : ℝ[X]) (z : ℂ) : ℂ :=
  ∑ k ∈ p.roots.toFinset,
    (christoffel (Ioo a b) w p k : ℂ) * ∏ j ∈ p.roots.toFinset.erase k, (1 + z * j)

/-- The Gauss quadrature sum `∑ₖ wₖ g(tₖ)`. -/
noncomputable def gaussQuad (a b : ℝ) (w : ℝ → ℝ) (p : ℝ[X]) (g : ℝ → ℂ) : ℂ :=
  ∑ k ∈ p.roots.toFinset, (christoffel (Ioo a b) w p k : ℂ) * g k

theorem isPolyFunDeg_gaussB (p : ℝ[X]) :
    IsPolyFunDeg (gaussB p) p.roots.toFinset.card :=
  IsPolyFunDeg.prod _ fun _ _ => IsPolyFunDeg.one_add_mul _

theorem isPolyFunDeg_gaussA (a b : ℝ) (w : ℝ → ℝ) (p : ℝ[X]) :
    IsPolyFunDeg (gaussA a b w p) (p.roots.toFinset.card - 1) :=
  IsPolyFunDeg.sum _ fun k hk => ((IsPolyFunDeg.const _).mul
    (IsPolyFunDeg.prod _ fun j _ => IsPolyFunDeg.one_add_mul _)).mono
      (by rw [card_erase_of_mem hk]; omega)

theorem gaussB_ne_zero {p : ℝ[X]} {z : ℂ} (hz : ∀ k ∈ p.roots.toFinset, 1 + z * k ≠ 0) :
    gaussB p z ≠ 0 :=
  prod_ne_zero_iff.mpr hz

theorem gaussA_eq {p : ℝ[X]} {z : ℂ} (hz : ∀ k ∈ p.roots.toFinset, 1 + z * k ≠ 0) :
    gaussA a b w p z = gaussB p z * gaussQuad a b w p (fun t => 1 / (1 + z * t)) := by
  simp only [gaussA, gaussB, gaussQuad, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [← mul_prod_erase _ _ hk]
  field_simp [hz k hk]

theorem wInt_Ioo_eq (hab : a ≤ b) (f : ℝ[X]) :
    wInt (Ioo a b) w f = ∫ x in a..b, f.eval x * w x := by
  rw [wInt, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- Exactness of Gauss quadrature (3.5.20_1), for complex-valued integrals of real polynomials. -/
theorem gauss_exact_C (hw : IsGaussWeight (Ioo a b) w) (hab : a ≤ b) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic (Ioo a b) w n p) {f : ℝ[X]} (hf : f.degree < (2 * n : ℕ)) :
    (∫ x in a..b, (w x : ℂ) * ((f.eval x : ℝ) : ℂ)) =
      gaussQuad a b w p (fun x => ((f.eval x : ℝ) : ℂ)) := by
  have h := dlmf_3_5_20_1 hw hp hf
  rw [wInt_Ioo_eq hab] at h
  rw [show (fun x => (w x : ℂ) * ((f.eval x : ℝ) : ℂ)) = fun x => ((f.eval x * w x : ℝ) : ℂ) by
    funext x; push_cast; ring, intervalIntegral.integral_ofReal, h]
  simp only [gaussQuad]; push_cast; rfl

theorem gauss_sum_weights (hw : IsGaussWeight (Ioo a b) w) (hab : a ≤ b) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic (Ioo a b) w n p) (hn : 1 ≤ n) :
    ∑ k ∈ p.roots.toFinset, christoffel (Ioo a b) w p k = ∫ x in a..b, w x := by
  have h := dlmf_3_5_20_1 hw hp (f := 1) (by
    rw [degree_one]; exact_mod_cast (by omega : 0 < 2 * n))
  rw [wInt_Ioo_eq hab] at h
  simpa using h.symm

theorem gauss_nodes_mem (hw : IsGaussWeight (Ioo a b) w) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic (Ioo a b) w n p) {k : ℝ} (hk : k ∈ p.roots.toFinset) : k ∈ Ioo a b :=
  (hp.roots_spec hw).2.2 k (Multiset.mem_toFinset.mp hk)

theorem gauss_card (hw : IsGaussWeight (Ioo a b) w) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic (Ioo a b) w n p) : p.roots.toFinset.card = n := by
  obtain ⟨hnd, hc, -⟩ := hp.roots_spec hw
  rw [Multiset.toFinset_card_of_nodup hnd, hc]

/-! ### Markov's theorem -/

/-- **Markov's theorem** (convergence of Gauss quadrature): for a continuous weight `w ≥ 0` on
`[a, b]` and every continuous `g` on `[a, b]`, `∑ₖ wₖ g(tₖ) → ∫ₐᵇ w g` as `n → ∞`. -/
theorem gauss_tendsto (hw : IsGaussWeight (Ioo a b) w) (hwc : Continuous w) (hab : a ≤ b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) {P : ℕ → ℝ[X]} (hP : ∀ n, IsOrthMonic (Ioo a b) w n (P n))
    {g : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) :
    Tendsto (fun n => gaussQuad a b w (P n) g) atTop (𝓝 (∫ x in a..b, (w x : ℂ) * g x)) := by
  set W := ∫ x in a..b, w x with hWdef
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg hab hw0
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (4 * (W + 1)) with hε'def
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨pr, hpr⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (g x).re)
    (continuous_re.comp_continuousOn hg) ε' hε'
  obtain ⟨pi, hpi⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (g x).im)
    (continuous_im.comp_continuousOn hg) ε' hε'
  refine ⟨max pr.natDegree pi.natDegree + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hdr : pr.degree < (2 * n : ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : pr.natDegree < 2 * n))
  have hdi : pi.degree < (2 * n : ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : pi.natDegree < 2 * n))
  set q : ℝ → ℂ := fun x => ((pr.eval x : ℝ) : ℂ) + I * ((pi.eval x : ℝ) : ℂ) with hqdef
  have hq : ∀ x ∈ Icc a b, ‖q x - g x‖ ≤ 2 * ε' := by
    intro x hx
    have hsplit : q x - g x = ((pr.eval x - (g x).re : ℝ) : ℂ) +
        I * ((pi.eval x - (g x).im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hqdef]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, one_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [hpr x hx, hpi x hx]
  have hcont : ∀ f : ℝ[X], Continuous fun x => (w x : ℂ) * ((f.eval x : ℝ) : ℂ) := fun f =>
    (continuous_ofReal.comp hwc).mul (continuous_ofReal.comp f.continuous)
  have hexact : (∫ x in a..b, (w x : ℂ) * q x) = gaussQuad a b w (P n) q := by
    have hsplit : (fun x => (w x : ℂ) * q x) = fun x =>
        (w x : ℂ) * ((pr.eval x : ℝ) : ℂ) + I * ((w x : ℂ) * ((pi.eval x : ℝ) : ℂ)) := by
      funext x; simp only [hqdef]; ring
    rw [hsplit, intervalIntegral.integral_add ((hcont pr).intervalIntegrable _ _)
      (((hcont pi).intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
      gauss_exact_C hw hab (hP n) hdr, gauss_exact_C hw hab (hP n) hdi]
    simp only [gaussQuad, hqdef, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  have hc0 : ∀ k ∈ (P n).roots.toFinset, 0 < christoffel (Ioo a b) w (P n) k :=
    fun k hk => christoffel_pos hw (hP n) hk
  have hsum := gauss_sum_weights hw hab (hP n) hn1
  have hmem : ∀ k ∈ (P n).roots.toFinset, k ∈ Icc a b := fun k hk =>
    Ioo_subset_Icc_self (gauss_nodes_mem hw (hP n) hk)
  have hqc : ContinuousOn q (Icc a b) := by
    simp only [hqdef]
    exact ((continuous_ofReal.comp pr.continuous).add
      (continuous_const.mul (continuous_ofReal.comp pi.continuous))).continuousOn
  have hint : IntervalIntegrable (fun x => (w x : ℂ) * (q x - g x)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact ((continuous_ofReal.comp hwc).continuousOn).mul (hqc.sub hg)
  have hintg : IntervalIntegrable (fun x => (w x : ℂ) * g x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact ((continuous_ofReal.comp hwc).continuousOn).mul hg
  have hintq : IntervalIntegrable (fun x => (w x : ℂ) * q x) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact ((continuous_ofReal.comp hwc).continuousOn).mul hqc
  have hdecomp : gaussQuad a b w (P n) g - ∫ x in a..b, (w x : ℂ) * g x =
      gaussQuad a b w (P n) (fun x => g x - q x) + ∫ x in a..b, (w x : ℂ) * (q x - g x) := by
    have h1 : (∫ x in a..b, (w x : ℂ) * (q x - g x)) =
        (∫ x in a..b, (w x : ℂ) * q x) - ∫ x in a..b, (w x : ℂ) * g x := by
      rw [← intervalIntegral.integral_sub hintq hintg]; congr 1; funext x; ring
    rw [h1, hexact]
    simp only [gaussQuad, mul_sub, sum_sub_distrib]
    ring
  have hb1 : ‖gaussQuad a b w (P n) (fun x => g x - q x)‖ ≤ 2 * ε' * W := by
    simp only [gaussQuad]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ (P n).roots.toFinset,
          ‖(christoffel (Ioo a b) w (P n) k : ℂ) * (g k - q k)‖
        ≤ ∑ k ∈ (P n).roots.toFinset, christoffel (Ioo a b) w (P n) k * (2 * ε') := by
          refine sum_le_sum fun k hk => ?_
          rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hc0 k hk), norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hq k (hmem k hk)) (hc0 k hk).le
      _ = 2 * ε' * W := by rw [← sum_mul, hsum]; ring
  have hb2 : ‖∫ x in a..b, (w x : ℂ) * (q x - g x)‖ ≤ 2 * ε' * W := by
    have := intervalIntegral.norm_integral_le_of_norm_le hab
      (f := fun x => (w x : ℂ) * (q x - g x)) (g := fun x => w x * (2 * ε'))
      (Eventually.of_forall fun x hx => by
        have hx' : x ∈ Icc a b := Ioc_subset_Icc_self hx
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x hx')]
        exact mul_le_mul_of_nonneg_left (hq x hx') (hw0 x hx'))
      ((hwc.mul continuous_const).intervalIntegrable (μ := volume) _ _)
    rw [intervalIntegral.integral_mul_const] at this
    linarith
  rw [dist_eq_norm, hdecomp]
  calc ‖gaussQuad a b w (P n) (fun x => g x - q x) + ∫ x in a..b, (w x : ℂ) * (q x - g x)‖
      ≤ 2 * ε' * W + 2 * ε' * W := (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = ε * (W / (W + 1)) := by rw [hε'def]; field_simp; ring
    _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).mpr (by linarith))

/-! ### The quadrature error near `0` -/

theorem norm_one_add_mul_ge {z : ℂ} {x : ℝ} (hz : ‖z‖ ≤ 1 / 2) (hx : |x| ≤ 1) :
    1 / 2 ≤ ‖1 + z * x‖ := by
  have h1 : ‖z * x‖ ≤ 1 / 2 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg z, abs_nonneg x]
  have := norm_sub_norm_le (1 : ℂ) (-(z * x))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

theorem one_add_mul_ne_zero {z : ℂ} {x : ℝ} (hz : ‖z‖ ≤ 1 / 2) (hx : |x| ≤ 1) :
    1 + z * x ≠ 0 := fun h => by
  have := norm_one_add_mul_ge hz hx; rw [h, norm_zero] at this; norm_num at this

/-- `1/(1 + u) = ∑_{j<N} (−u)^j + (−u)^N/(1 + u)`. -/
theorem inv_one_add_eq_geom (u : ℂ) (hu : 1 + u ≠ 0) (N : ℕ) :
    1 / (1 + u) = ∑ j ∈ range N, (-u) ^ j + (-u) ^ N / (1 + u) := by
  have h := geom_sum_mul (-u) N
  have hs : ∑ j ∈ range N, (-u) ^ j = (1 - (-u) ^ N) / (1 + u) := by
    rw [eq_div_iff hu]; linear_combination -h
  rw [hs]; field_simp; ring

/-- The Gauss error: `B(z) ∫ₐᵇ w/(1 + z t) dt − A(z) = O(z^{2n})` for `[a, b] ⊆ [−1, 1]`. -/
theorem gauss_err_bound (hw : IsGaussWeight (Ioo a b) w) (hwc : Continuous w) (hab : a ≤ b)
    (ha : -1 ≤ a) (hb : b ≤ 1) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic (Ioo a b) w n p) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖gaussB p z * (∫ x in a..b, (w x : ℂ) / (1 + z * x)) - gaussA a b w p z‖ ≤
        C * ‖z‖ ^ (2 * n) := by
  set S := p.roots.toFinset
  set W := ∫ x in a..b, w x
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg hab hw0
  have hmem : ∀ k ∈ S, |k| ≤ 1 := fun k hk => by
    have := gauss_nodes_mem hw hp hk
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  have hc0 : ∀ k ∈ S, 0 < christoffel (Ioo a b) w p k := fun k hk => christoffel_pos hw hp hk
  set Sc := ∑ k ∈ S, christoffel (Ioo a b) w p k
  have hSc : 0 ≤ Sc := sum_nonneg fun k hk => (hc0 k hk).le
  refine ⟨2 ^ S.card * (2 * W + 2 * Sc), fun z hz => ?_⟩
  have hx : ∀ x ∈ uIcc a b, |x| ≤ 1 := fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hne : ∀ k ∈ S, 1 + z * k ≠ 0 := fun k hk => one_add_mul_ne_zero hz (hmem k hk)
  rw [gaussA_eq hne, ← mul_sub]
  set N := 2 * n
  -- the polynomial part is integrated exactly
  have hgeom : ∀ x : ℝ, |x| ≤ 1 → (1 : ℂ) / (1 + z * x) =
      ∑ j ∈ range N, (-z) ^ j * (x : ℂ) ^ j + (-z) ^ N * ((x : ℂ) ^ N / (1 + z * x)) := by
    intro x hx'
    rw [inv_one_add_eq_geom _ (one_add_mul_ne_zero hz hx') N]
    congr 1
    · refine sum_congr rfl fun j _ => ?_; ring
    · ring
  have hcontI : ∀ j : ℕ, Continuous fun x : ℝ => (w x : ℂ) * (x : ℂ) ^ j := fun j =>
    (continuous_ofReal.comp hwc).mul (continuous_ofReal.pow j)
  have hcontR : ContinuousOn (fun x : ℝ => (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x)))
      (uIcc a b) := by
    refine ((continuous_ofReal.comp hwc).continuousOn).mul
      (((continuous_ofReal.pow N).continuousOn).div
        (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
        fun x hx' => one_add_mul_ne_zero hz (hx x hx'))
  have hint_eq : (∫ x in a..b, (w x : ℂ) / (1 + z * x)) =
      ∑ j ∈ range N, (-z) ^ j * (∫ x in a..b, (w x : ℂ) * (x : ℂ) ^ j) +
        (-z) ^ N * ∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x)) := by
    rw [intervalIntegral.integral_congr (g := fun x => ∑ j ∈ range N,
        (-z) ^ j * ((w x : ℂ) * (x : ℂ) ^ j) +
        (-z) ^ N * ((w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x)))) fun x hx' => by
      simp only
      rw [div_eq_mul_one_div (w x : ℂ), hgeom x (hx x hx'), mul_add, mul_sum]
      congr 1
      · refine sum_congr rfl fun j _ => ?_; ring
      · ring]
    have hI1 : IntervalIntegrable (fun x : ℝ => ∑ j ∈ range N,
        (-z) ^ j * ((w x : ℂ) * (x : ℂ) ^ j)) volume a b :=
      (continuous_finsetSum _ fun j _ => continuous_const.mul (hcontI j)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 ((hcontR.intervalIntegrable).const_mul _),
      intervalIntegral.integral_finsetSum fun j _ =>
        ((hcontI j).intervalIntegrable _ _).const_mul _,
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const_mul]
  have hsum_eq : gaussQuad a b w p (fun t => 1 / (1 + z * t)) =
      ∑ j ∈ range N, (-z) ^ j * gaussQuad a b w p (fun x => (x : ℂ) ^ j) +
        (-z) ^ N * gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x)) := by
    simp only [gaussQuad, mul_sum]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [hgeom k (hmem k hk), mul_add, mul_sum]
    congr 1
    · refine sum_congr rfl fun j _ => ?_; ring
    · ring
  have hexact : ∀ j ∈ range N, (∫ x in a..b, (w x : ℂ) * (x : ℂ) ^ j) =
      gaussQuad a b w p (fun x => (x : ℂ) ^ j) := fun j hj => by
    have := gauss_exact_C hw hab hp (f := X ^ j) (by
      rw [degree_X_pow]; exact_mod_cast mem_range.mp hj)
    simpa using this
  have hpoly : ∑ j ∈ range N, (-z) ^ j * (∫ x in a..b, (w x : ℂ) * (x : ℂ) ^ j) =
      ∑ j ∈ range N, (-z) ^ j * gaussQuad a b w p (fun x => (x : ℂ) ^ j) :=
    sum_congr rfl fun j hj => by rw [hexact j hj]
  rw [hint_eq, hsum_eq, hpoly, add_sub_add_left_eq_sub, ← mul_sub]
  -- bounds
  have hB : ‖gaussB p z‖ ≤ 2 ^ S.card := by
    simp only [gaussB]
    rw [norm_prod]
    refine (prod_le_prod₀ (fun k _ => norm_nonneg _) fun k hk => (?_ : _ ≤ (2 : ℝ))).trans
      (by rw [prod_const])
    have := norm_add_le (1 : ℂ) (z * k)
    rw [norm_one, norm_mul, norm_real, Real.norm_eq_abs] at this
    nlinarith [hmem k hk, norm_nonneg z, abs_nonneg k]
  have hR1 : ‖∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))‖ ≤ 2 * W := by
    have := intervalIntegral.norm_integral_le_of_norm_le hab
      (f := fun x => (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))) (g := fun x => w x * 2)
      (Eventually.of_forall fun x hx' => by
        have hx'' : x ∈ Icc a b := Ioc_subset_Icc_self hx'
        have hxa : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx''.1], by linarith [hx''.2]⟩
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x hx''), norm_div,
          norm_pow, norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 x hx'')
        have h1 := norm_one_add_mul_ge hz hxa
        rw [div_le_iff₀ (by linarith)]
        have : |x| ^ N ≤ 1 := pow_le_one₀ (abs_nonneg x) hxa
        linarith)
      ((hwc.mul continuous_const).intervalIntegrable (μ := volume) _ _)
    rw [intervalIntegral.integral_mul_const] at this
    linarith
  have hR2 : ‖gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x))‖ ≤ 2 * Sc := by
    simp only [gaussQuad]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hc0 k hk), norm_div, norm_pow,
      norm_real, Real.norm_eq_abs]
    have h1 := norm_one_add_mul_ge hz (hmem k hk)
    have : |k| ^ N ≤ 1 := pow_le_one₀ (abs_nonneg k) (hmem k hk)
    have h2 : |k| ^ N / ‖1 + z * k‖ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith [hc0 k hk]
  rw [norm_mul, norm_mul, norm_pow, norm_neg]
  have h3 : ‖(∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))) -
      gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x))‖ ≤ 2 * W + 2 * Sc :=
    (norm_sub_le _ _).trans (add_le_add hR1 hR2)
  calc ‖gaussB p z‖ * (‖z‖ ^ N * ‖(∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))) -
        gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x))‖)
      ≤ 2 ^ S.card * (‖z‖ ^ N * (2 * W + 2 * Sc)) := by gcongr
    _ = 2 ^ S.card * (2 * W + 2 * Sc) * ‖z‖ ^ N := by ring

end Azurite.DLMF
