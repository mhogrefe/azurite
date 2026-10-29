/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9CauchyJordan
import Azurite.DLMF.Chapter1.Section10Laurent
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Order

/-!
# DLMF §1.10(iv): Residue Theorem

Formalizations of <https://dlmf.nist.gov/1.10.iv>, for positively oriented Jordan curves `C`
(closed piecewise-`C¹`, `ClosedPiecewiseC1` with `IsJordanCurve`), "within `C`" being
`jordanInterior`.

* Principal parts: `principalPart` (`∑_{m≥1} a_{−m}(z − s)^{−m}`, convergent and analytic on
  `z ≠ s`: `summable_principalPart`, `differentiableOn_principalPart`, `principalPart_term_bound`),
  `norm_sub_principalPart_le` (the Taylor part is bounded near `s`),
  `ClosedPiecewiseC1.contourIntegral_principalPart` (`∮_C = 2πi Res_s 𝒩(C, s)`).
* 1.10.8: `ClosedPiecewiseC1.contourIntegral_eq_sum_residues`, `dlmf_1_10_8`, under DLMF's
  hypotheses (analytic within, continuous within and on `C`, except at finitely many
  singularities within `C`; residues in the sense of `Section10Laurent`).  Proof: subtract all
  principal parts, remove the resulting removable singularities
  (`differentiableOn_update_limUnder_of_bddAbove`) and apply Cauchy's theorem with boundary
  continuity (`Section9CauchyJordan`).
* 1.10.9 (phase or argument principle), for `f` analytic on an open `U ⊇` (interior ∪ `C`) except
  at finitely many zeros/poles `t` inside, `f = (z − t)^{n(t)} g` with `g(t) ≠ 0`, and nonvanishing
  elsewhere on the closed region; `N − P = ∑ n(t)`: `residue_mul_logDeriv` (residue of `φ f′/f` is
  `n φ(t)`), `ClosedPiecewiseC1.contourIntegral_mul_logDeriv`, `dlmf_1_10_9` (integral form),
  `dlmf_1_10_9_phase` (`(2π)⁻¹ Δ_C ph f` for any continuous branch `θ` of the phase; via
  `eq_exp_primitive_mul`, `contourIntegral_logDeriv_eq_phase`, `eq_zero_of_int_valued`).
* 1.10.10: `dlmf_1_10_10`.
* Rouché's theorem: `dlmf_1_10_iv_rouche` (zeros counted with `analyticOrderAt`; finiteness of the
  zero sets and of the orders from `exists_zeros_finset`, via the identity theorem on the connected
  component of `U` containing the closed region; `contourIntegral_logDeriv_eq_card`).
-/

open Filter Topology Set Metric Complex MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Principal parts -/

/-- The principal part `∑_{m ≥ 1} a_{−m} (z − s)^{−m}` of `f` at an isolated singularity `s`. -/
noncomputable def principalPart (f : ℂ → ℂ) (s : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, laurentCoeff f s (R / 2) (-((m + 1 : ℕ) : ℤ)) * (z - s) ^ (-((m + 1 : ℕ) : ℤ))

theorem sphere_subset_annulus {s : ℂ} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    sphere s ρ ⊆ annulus s 0 R := fun w hw => by
  rw [mem_sphere, dist_eq_norm] at hw
  exact ⟨by rw [hw]; exact hρ, by rw [hw]; exact hρR⟩

/-- Geometric bound for the terms of the principal part away from `s`. -/
theorem principalPart_term_bound {f : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus s 0 R)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C q : ℝ, 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧ ∀ (m : ℕ) (z : ℂ), δ ≤ ‖z - s‖ →
      ‖laurentCoeff f s (R / 2) (-((m + 1 : ℕ) : ℤ)) * (z - s) ^ (-((m + 1 : ℕ) : ℤ))‖ ≤
        C * q ^ m := by
  set ρ := min (R / 2) (δ / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρR : ρ < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρδ : ρ ≤ δ / 2 := min_le_right _ _
  obtain ⟨M, hM⟩ := (isCompact_sphere s ρ).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_annulus hρ hρR))
  set M' := max M 0
  have hM' : ∀ w ∈ sphere s ρ, ‖f w‖ ≤ M' := fun w hw => (hM w hw).trans (le_max_left _ _)
  refine ⟨M' * (ρ / δ), ρ / δ, by positivity, by positivity,
    (div_lt_one hδ).mpr (by linarith), fun m z hz => ?_⟩
  rw [laurentCoeff_eq le_rfl hf ⟨by linarith, by linarith⟩ ⟨hρ, hρR⟩, norm_mul, norm_zpow]
  have hb := norm_laurentCoeff_le hρ hM' (-((m + 1 : ℕ) : ℤ))
  rw [neg_neg, zpow_natCast] at hb
  have hz0 : 0 < ‖z - s‖ := hδ.trans_le hz
  rw [zpow_neg, zpow_natCast]
  calc ‖laurentCoeff f s ρ (-((m + 1 : ℕ) : ℤ))‖ * (‖z - s‖ ^ (m + 1))⁻¹
      ≤ M' * ρ ^ (m + 1) * (δ ^ (m + 1))⁻¹ :=
        mul_le_mul hb (inv_anti₀ (by positivity) (pow_le_pow_left₀ hδ.le hz _)) (by positivity)
          (by positivity)
    _ = M' * (ρ / δ) * (ρ / δ) ^ m := by
        rw [div_pow, pow_succ ρ m, pow_succ δ m, mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring

theorem summable_principalPart {f : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus s 0 R)) {z : ℂ} (hz : z ≠ s) :
    Summable fun m : ℕ =>
      laurentCoeff f s (R / 2) (-((m + 1 : ℕ) : ℤ)) * (z - s) ^ (-((m + 1 : ℕ) : ℤ)) := by
  have hδ : 0 < ‖z - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨C, q, -, hq0, hq1, hb⟩ := principalPart_term_bound hR hf hδ
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left C)
    fun m => hb m z le_rfl

/-- The principal part is analytic away from `s`. -/
theorem differentiableOn_principalPart {f : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus s 0 R)) :
    DifferentiableOn ℂ (principalPart f s R) {z | z ≠ s} := by
  intro z hz
  have hδ : 0 < ‖z - s‖ / 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr (show z ≠ s from hz))
    positivity
  obtain ⟨C, q, -, hq0, hq1, hb⟩ := principalPart_term_bound hR hf hδ
  set U := {w : ℂ | ‖z - s‖ / 2 < ‖w - s‖}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_sub_right s).norm
  have hzU : z ∈ U := by
    show ‖z - s‖ / 2 < ‖z - s‖
    linarith
  have hd : DifferentiableOn ℂ (principalPart f s R) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one hq0 hq1).mul_left C) (fun m w hw => ?_) hU
      fun m w hw => hb m w (le_of_lt hw)
    have hw0 : w - s ≠ 0 := by
      intro h
      have : ‖z - s‖ / 2 < ‖w - s‖ := hw
      rw [h, norm_zero] at this
      linarith
    exact (differentiableAt_const _ |>.mul
      ((differentiableAt_id.sub_const s).zpow (Or.inl hw0))).differentiableWithinAt
  exact (hd.differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

/-- Near `s`, `f` minus its principal part (the Taylor part) is bounded. -/
theorem norm_sub_principalPart_le {f : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus s 0 R)) :
    ∃ B, ∀ z : ℂ, 0 < ‖z - s‖ → ‖z - s‖ ≤ R / 4 → ‖f z - principalPart f s R z‖ ≤ B := by
  have hρ : 0 < R / 2 := by linarith
  obtain ⟨M, hM⟩ := (isCompact_sphere s (R / 2)).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_annulus hρ (by linarith)))
  set M' := max M 0
  have hM' : ∀ w ∈ sphere s (R / 2), ‖f w‖ ≤ M' := fun w hw => (hM w hw).trans (le_max_left _ _)
  refine ⟨M' * 2, fun z hz0 hz => ?_⟩
  have hzA : z ∈ annulus s 0 R := ⟨hz0, by linarith⟩
  obtain ⟨S₁, S₂, h1, h2, hsum⟩ := hasSum_laurent (r := R / 2) le_rfl hf
    ⟨hρ, by linarith⟩ hzA
  have hP : principalPart f s R z = S₂ := h2.tsum_eq
  rw [hP, ← hsum, add_sub_cancel_right]
  refine h1.norm_le_of_bounded (hasSum_geometric_two.mul_left M') fun n => ?_
  rw [norm_mul, norm_pow]
  have hb := norm_laurentCoeff_le hρ hM' n
  rw [zpow_neg, zpow_natCast] at hb
  calc ‖laurentCoeff f s (R / 2) n‖ * ‖z - s‖ ^ n ≤ M' * ((R / 2) ^ n)⁻¹ * (R / 4) ^ n :=
        mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity) (by positivity)
    _ = M' * (1 / 2) ^ n := by
        rw [show R / 4 = R / 2 * (1 / 2) by ring, mul_pow]
        field_simp

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

open Azurite.DLMF

theorem contourIntegral_finset_sum {ι : Type*} (t : Finset ι) {F : ι → ℂ → ℂ}
    (hF : ∀ i ∈ t, ContinuousOn (F i) P.curve) :
    P.contourIntegral (fun z => ∑ i ∈ t, F i z) = ∑ i ∈ t, P.contourIntegral (F i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using P.contourIntegral_const_mul 0 (fun _ => 0)
  | insert j t hj ih =>
    simp only [Finset.sum_insert hj]
    rw [P.contourIntegral_add (hF j (Finset.mem_insert_self j t))
      (continuousOn_finsetSum _ fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-- `∮_C (principal part at s) = 2πi · Res_s · 𝒩(C, s)`. -/
theorem contourIntegral_principalPart {f : ℂ → ℂ} {s : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus s 0 R)) (hs : s ∉ P.curve) :
    P.contourIntegral (principalPart f s R) =
      2 * π * I * residue f s R * P.windingNumber s := by
  set term : ℕ → ℂ → ℂ := fun m z =>
    laurentCoeff f s (R / 2) (-((m + 1 : ℕ) : ℤ)) * (z - s) ^ (-((m + 1 : ℕ) : ℤ))
  set val := 2 * π * I * residue f s R * P.windingNumber s
  have hδ : 0 < infDist s P.curve :=
    (P.isCompact_curve.isClosed.notMem_iff_infDist_pos ⟨c a, a, ⟨le_rfl, P.a_le_b⟩, rfl⟩).mp hs
  have hdist : ∀ z ∈ P.curve, infDist s P.curve ≤ ‖z - s‖ := fun z hz => by
    rw [← dist_eq_norm, dist_comm]; exact infDist_le_dist_of_mem hz
  obtain ⟨C, q, hC0, hq0, hq1, hb⟩ := principalPart_term_bound hR hf hδ
  have hne : ∀ z ∈ P.curve, z - s ≠ 0 := fun z hz h => hs (by rwa [sub_eq_zero.mp h] at hz)
  have hterm_cont : ∀ m, ContinuousOn (term m) P.curve := fun m =>
    continuousOn_const.mul (continuousOn_of_forall_continuousAt fun z hz =>
      (continuous_sub_right s).continuousAt.zpow₀ _ (Or.inl (hne z hz)))
  have hPc : ContinuousOn (principalPart f s R) P.curve := fun z hz =>
    ((differentiableOn_principalPart hR hf).differentiableAt
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds
        (show z ≠ s from fun h => hne z hz (by rw [h, sub_self])))).continuousAt.continuousWithinAt
  -- the partial sums integrate to `val`
  have hpartial : ∀ N : ℕ,
      P.contourIntegral (fun z => ∑ m ∈ Finset.range (N + 1), term m z) = val := by
    intro N
    rw [P.contourIntegral_finset_sum _ fun m _ => hterm_cont m, Finset.sum_range_succ']
    have hzero : ∀ m ∈ Finset.range N, P.contourIntegral (term (m + 1)) = 0 := by
      intro m _
      have : term (m + 1) = fun z => laurentCoeff f s (R / 2) (-((m + 1 + 1 : ℕ) : ℤ)) *
          ((z - s) ^ (m + 2))⁻¹ := by
        funext z
        simp only [term, zpow_neg, zpow_natCast]
      rw [this, P.contourIntegral_const_mul, P.contourIntegral_inv_pow_eq_zero hs, mul_zero]
    rw [Finset.sum_eq_zero hzero, zero_add]
    have : term 0 = fun z => residue f s R * (z - s)⁻¹ := by
      funext z
      simp [term, residue]
    rw [this, P.contourIntegral_const_mul, P.contourIntegral_inv_eq hs]
    ring
  -- tail estimate
  have htail : ∀ N : ℕ, ∀ z ∈ P.curve,
      ‖principalPart f s R z - ∑ m ∈ Finset.range (N + 1), term m z‖ ≤
        C * q ^ (N + 1) * (1 - q)⁻¹ := by
    intro N z hz
    have hsum := summable_principalPart hR hf
      (show z ≠ s from fun h => hne z hz (by rw [h, sub_self]))
    rw [principalPart, ← hsum.sum_add_tsum_nat_add (N + 1), add_sub_cancel_left]
    refine ((hsum.comp_injective (add_left_injective (N + 1))).hasSum).norm_le_of_bounded
      (((hasSum_geometric_of_lt_one hq0 hq1).mul_left (C * q ^ (N + 1)))) fun m => ?_
    calc ‖term (m + (N + 1)) z‖ ≤ C * q ^ (m + (N + 1)) := hb _ z (hdist z hz)
      _ = C * q ^ (N + 1) * q ^ m := by rw [pow_add]; ring
  have hL0 := P.length_nonneg
  have hlim : Tendsto (fun N : ℕ => P.length * (C * q ^ (N + 1) * (1 - q)⁻¹)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1))
    have h2 := (this.const_mul C).mul_const (1 - q)⁻¹ |>.const_mul P.length
    simpa [Function.comp_def] using h2
  have hle : ∀ N : ℕ, ‖P.contourIntegral (principalPart f s R) - val‖ ≤
      P.length * (C * q ^ (N + 1) * (1 - q)⁻¹) := by
    intro N
    rw [← hpartial N, ← P.contourIntegral_sub hPc
      (continuousOn_finsetSum _ fun m _ => hterm_cont m)]
    exact P.norm_contourIntegral_le fun z hz => htail N z hz
  have h0 : ‖P.contourIntegral (principalPart f s R) - val‖ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hle)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- **Residue theorem** (DLMF 1.10.8): `f` analytic within the positively oriented Jordan curve
`C` and continuous within and on `C`, except at finitely many singularities `S` within `C`. The
radii `R s` describe punctured disks around the singularities inside the interior that contain no
other singularity. -/
theorem contourIntegral_eq_sum_residues (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ} {S : Finset ℂ}
    (hS : ↑S ⊆ jordanInterior c a b)
    (hfc : ContinuousOn f ((jordanInterior c a b ∪ P.curve) \ ↑S))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b \ ↑S)) (R : ℂ → ℝ)
    (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ jordanInterior c a b ∧
      ∀ t ∈ S, t ≠ s → R s ≤ dist t s) :
    P.contourIntegral f = 2 * π * I * ∑ s ∈ S, residue f s (R s) := by
  classical
  set D := jordanInterior c a b with hDdef
  have hDo : IsOpen D := isOpen_jordanInterior hJ.continuousOn
  have hSc : IsClosed (↑S : Set ℂ) := S.finite_toSet.isClosed
  have hcurveS : ∀ z ∈ P.curve, z ∉ S := fun z hz hzS =>
    jordanInterior_subset (hS hzS) hz
  -- `f` is analytic on each punctured disk
  have hann : ∀ s ∈ S, annulus s 0 (R s) ⊆ D \ ↑S := by
    intro s hs z hz
    refine ⟨(hR s hs).2.1 (by rw [mem_ball, dist_eq_norm]; exact hz.2), fun hzS => ?_⟩
    by_cases hzs : z = s
    · have h1 : 0 < ‖z - s‖ := hz.1
      rw [hzs, sub_self, norm_zero] at h1
      exact lt_irrefl _ h1
    · have := (hR s hs).2.2 z hzS hzs
      rw [dist_eq_norm] at this
      linarith [hz.2]
  have hfs : ∀ s ∈ S, DifferentiableOn ℂ f (annulus s 0 (R s)) := fun s hs =>
    hfd.mono (hann s hs)
  have hPd : ∀ s ∈ S, DifferentiableOn ℂ (principalPart f s (R s)) {z | z ≠ s} := fun s hs =>
    differentiableOn_principalPart (hR s hs).1 (hfs s hs)
  have hPat : ∀ s ∈ S, ∀ z, z ≠ s → DifferentiableAt ℂ (principalPart f s (R s)) z :=
    fun s hs z hz => (hPd s hs).differentiableAt
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hz)
  set Q : ℂ → ℂ := fun z => ∑ s ∈ S, principalPart f s (R s) z with hQ
  set g : ℂ → ℂ := fun z => f z - Q z with hg
  have hQat : ∀ z, z ∉ S → DifferentiableAt ℂ Q z := fun z hz =>
    DifferentiableAt.fun_sum fun s hs => hPat s hs z (fun h => hz (h ▸ hs))
  set G : ℂ → ℂ := fun z => if z ∈ S then limUnder (𝓝[≠] z) g else g z with hG
  have hGg : ∀ z, z ∉ S → G =ᶠ[𝓝 z] g := fun z hz => by
    filter_upwards [hSc.isOpen_compl.mem_nhds hz] with w hw
    simp only [hG, show w ∉ S from hw, ↓reduceIte]
  -- differentiability of `G` on the interior
  have hGd : ∀ z ∈ D, DifferentiableAt ℂ G z := by
    intro z hz
    by_cases hzS : z ∈ S
    · set r := R z / 4 with hrdef
      have hr : 0 < r := by have := (hR z hzS).1; positivity
      have hball : ∀ w ∈ ball z r, w ≠ z → w ∈ annulus z 0 (R z) := fun w hw hwz => by
        rw [mem_ball, dist_eq_norm] at hw
        exact ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hwz), by linarith [(hR z hzS).1, hrdef]⟩
      have hnotS : ∀ w ∈ ball z r, w ≠ z → w ∉ S := fun w hw hwz =>
        ((hann z hzS) (hball w hw hwz)).2
      -- `g` is differentiable on the punctured ball
      have hgd : DifferentiableOn ℂ g (ball z r \ {z}) := fun w hw => by
        have hwz : w ≠ z := hw.2
        exact ((hfs z hzS).differentiableAt ((isOpen_annulus z 0 (R z)).mem_nhds
          (hball w hw.1 hwz))).sub (hQat w (hnotS w hw.1 hwz)) |>.differentiableWithinAt
      -- `g` is bounded on the punctured ball
      obtain ⟨B, hB⟩ := norm_sub_principalPart_le (hR z hzS).1 (hfs z hzS)
      have hK : ∀ t ∈ S.erase z, ∃ K, ∀ w ∈ closedBall z r, ‖principalPart f t (R t) w‖ ≤ K := by
        intro t ht
        have htz : t ≠ z := Finset.ne_of_mem_erase ht
        have htS : t ∈ S := Finset.mem_of_mem_erase ht
        refine (isCompact_closedBall z r).exists_bound_of_continuousOn fun w hw => ?_
        refine (hPat t htS w fun h => ?_).continuousAt.continuousWithinAt
        rw [h, mem_closedBall] at hw
        have := (hR z hzS).2.2 t htS htz
        linarith [(hR z hzS).1, hrdef]
      choose! K hK using hK
      have hbdd : BddAbove (norm ∘ g '' (ball z r \ {z})) := by
        refine ⟨B + ∑ t ∈ S.erase z, K t, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have hwz : w ≠ z := hw.2
        have hw' : ‖w - z‖ < r := by rw [← dist_eq_norm]; exact hw.1
        simp only [Function.comp_apply, hg, hQ]
        rw [← Finset.add_sum_erase S _ hzS, ← sub_sub]
        refine (norm_sub_le _ _).trans (add_le_add (hB w (norm_pos_iff.mpr
          (sub_ne_zero.mpr hwz)) hw'.le) ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => hK t ht w ?_)
        exact ball_subset_closedBall hw.1
      have hupd := differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds z hr) hgd hbdd
      have hev : G =ᶠ[𝓝 z] Function.update g z (limUnder (𝓝[≠] z) g) := by
        filter_upwards [ball_mem_nhds z hr] with w hw
        by_cases hwz : w = z
        · subst hwz
          simp [hG, hzS]
        · simp only [hG, Function.update_of_ne hwz, hnotS w hw hwz, ↓reduceIte]
      exact (hupd.differentiableAt (ball_mem_nhds z hr)).congr_of_eventuallyEq hev
    · have hfz : DifferentiableAt ℂ f z :=
        hfd.differentiableAt ((hDo.sdiff hSc).mem_nhds ⟨hz, hzS⟩)
      exact (hfz.sub (hQat z hzS)).congr_of_eventuallyEq (hGg z hzS)
  -- continuity of `G` on the closed region
  have hGc : ContinuousOn G (D ∪ P.curve) := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact (hGd z (hS hzS)).continuousAt.continuousWithinAt
    · have hfw : ContinuousWithinAt f (D ∪ P.curve) z :=
        (hfc z ⟨hz, hzS⟩).mono_of_mem_nhdsWithin (by
          rw [Set.sdiff_eq]
          exact inter_mem_nhdsWithin _ (hSc.isOpen_compl.mem_nhds hzS))
      have hgw : ContinuousWithinAt g (D ∪ P.curve) z :=
        hfw.sub (hQat z hzS).continuousAt.continuousWithinAt
      exact hgw.congr_of_eventuallyEq (nhdsWithin_le_nhds (hGg z hzS))
        (by simp only [hG, hzS, ↓reduceIte])
  have hzero := P.contourIntegral_eq_zero_of_continuousOn hJ hGc
    fun z hz => (hGd z hz).differentiableWithinAt
  have hcurve_eq : P.contourIntegral G = P.contourIntegral g :=
    P.contourIntegral_congr fun z hz => by simp only [hG, hcurveS z hz, ↓reduceIte]
  have hfcurve : ContinuousOn f P.curve := hfc.mono fun z hz => ⟨Or.inr hz, hcurveS z hz⟩
  have hQc : ∀ s ∈ S, ContinuousOn (principalPart f s (R s)) P.curve := fun s hs z hz =>
    (hPat s hs z fun h => hcurveS z hz (h ▸ hs)).continuousAt.continuousWithinAt
  rw [hcurve_eq, P.contourIntegral_sub hfcurve (continuousOn_finsetSum _ hQc),
    P.contourIntegral_finset_sum _ hQc, sub_eq_zero] at hzero
  rw [hzero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [P.contourIntegral_principalPart (hR s hs).1 (hfs s hs) (fun h => hcurveS s h hs),
    hpos s (hS hs), Int.cast_one, mul_one]

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

/-! ### Logarithmic derivatives -/

/-- At a zero (`n > 0`) or pole (`n < 0`) of order `|n|`, `f = (z − t)ⁿ g` with `g(t) ≠ 0`, the
residue of `φ f′/f` is `n φ(t)`. -/
theorem residue_mul_logDeriv {f φ g : ℂ → ℂ} {t : ℂ} {R : ℝ} {n : ℤ} (hR : 0 < R)
    (hfd : DifferentiableOn ℂ f (annulus t 0 R)) (hf0 : ∀ z ∈ annulus t 0 R, f z ≠ 0)
    (hφ : Differentiable ℂ φ) (hg : AnalyticAt ℂ g t) (hgt : g t ≠ 0)
    (hfg : ∀ᶠ z in 𝓝[≠] t, f z = (z - t) ^ n * g z) :
    residue (fun z => φ z * (deriv f z / f z)) t R = n * φ t := by
  obtain ⟨ε₁, hε₁, hfac⟩ : ∃ ε > 0, ∀ z, dist z t < ε → z ≠ t → f z = (z - t) ^ n * g z := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hfg
    exact hfg
  obtain ⟨ε₂, hε₂, hgd⟩ : ∃ ε > 0, ∀ z, dist z t < ε → AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    Metric.eventually_nhds_iff.mp (hg.eventually_analyticAt.and
      (hg.continuousAt.eventually_ne hgt))
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  set ρ := min (R / 2) (ε / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρR : ρ < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hε1 : ε ≤ ε₁ := min_le_left _ _
  have hε2 : ε ≤ ε₂ := min_le_right _ _
  have hAo := isOpen_annulus t 0 R
  have hFd : DifferentiableOn ℂ (fun z => φ z * (deriv f z / f z)) (annulus t 0 R) :=
    hφ.differentiableOn.mul ((hfd.deriv hAo).div hfd hf0)
  rw [residue_eq hFd ⟨hρ, hρR⟩]
  have hderiv : ∀ z, dist z t < ε → z ≠ t →
      deriv f z = n * (z - t) ^ (n - 1) * g z + (z - t) ^ n * deriv g z := by
    intro z hz hzt
    have hev : f =ᶠ[𝓝 z] fun w => (w - t) ^ n * g w := by
      have hopen : IsOpen {w : ℂ | dist w t < ε ∧ w ≠ t} :=
        (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
          (isOpen_ne_fun continuous_id continuous_const)
      filter_upwards [hopen.mem_nhds ⟨hz, hzt⟩] with w hw
      exact hfac w (lt_of_lt_of_le hw.1 hε1) hw.2
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun w => (w - t) ^ n) (n * (z - t) ^ (n - 1)) z := by
      have := (hasDerivAt_zpow n (z - t) (Or.inl (sub_ne_zero.mpr hzt))).comp z
        ((hasDerivAt_id z).sub_const t)
      rw [mul_one] at this
      exact this
    exact (h1.mul (hgd z (lt_of_lt_of_le hz hε2)).1.differentiableAt.hasDerivAt).deriv
  have hsph : EqOn (fun z => φ z * (deriv f z / f z))
      (fun z => (z - t)⁻¹ • ((n : ℂ) * φ z) + φ z * (deriv g z / g z)) (sphere t ρ) := by
    intro z hz
    have hzd : dist z t = ρ := hz
    have hzt : z ≠ t := by
      rintro rfl
      rw [dist_self] at hzd
      linarith
    have hzε : dist z t < ε := by rw [hzd]; exact hρε
    have hne : z - t ≠ 0 := sub_ne_zero.mpr hzt
    have hgz : g z ≠ 0 := (hgd z (lt_of_lt_of_le hzε hε2)).2
    simp only [smul_eq_mul]
    rw [hderiv z hzε hzt, hfac z (lt_of_lt_of_le hzε hε1) hzt, zpow_sub_one₀ hne]
    have hpow : (z - t) ^ n ≠ 0 := zpow_ne_zero n hne
    field_simp
  have hcb : closedBall t ρ ⊆ ball t ε := closedBall_subset_ball hρε
  have hgdc : ∀ z ∈ closedBall t ρ, AnalyticAt ℂ g z ∧ g z ≠ 0 := fun z hz =>
    hgd z (lt_of_lt_of_le (hcb hz) hε2)
  have hG : ∀ z ∈ closedBall t ρ, DifferentiableAt ℂ (fun z => φ z * (deriv g z / g z)) z :=
    fun z hz => (hφ z).mul ((hgdc z hz).1.deriv.differentiableAt.div
      (hgdc z hz).1.differentiableAt (hgdc z hz).2)
  have h1 : (∮ z in C(t, ρ), (z - t)⁻¹ • ((n : ℂ) * φ z)) = (2 * π * I : ℂ) • ((n : ℂ) * φ t) :=
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      (mem_ball_self hρ) (continuous_const.mul hφ.continuous).continuousOn
      fun z _ => (differentiableAt_const _).mul (hφ z)
  have h2 : (∮ z in C(t, ρ), φ z * (deriv g z / g z)) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le countable_empty
      (fun z hz => (hG z hz).continuousAt.continuousWithinAt)
      fun z hz => hG z (ball_subset_closedBall hz.1)
  have hi1 : CircleIntegrable (fun z => (z - t)⁻¹ • ((n : ℂ) * φ z)) t ρ := by
    refine ContinuousOn.circleIntegrable hρ.le fun z hz => ?_
    have hzt : z - t ≠ 0 := by
      intro h
      have hzd : dist z t = ρ := hz
      rw [dist_eq_norm, h, norm_zero] at hzd
      linarith
    exact (((continuous_sub_right t).continuousAt.inv₀ hzt).smul
      (continuous_const.mul hφ.continuous).continuousAt).continuousWithinAt
  have hi2 : CircleIntegrable (fun z => φ z * (deriv g z / g z)) t ρ :=
    ContinuousOn.circleIntegrable hρ.le fun z hz =>
      (hG z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  rw [circleIntegral.integral_congr hρ.le hsph, circleIntegral.integral_add hi1 hi2, h1, h2,
    add_zero, smul_eq_mul]
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

open Azurite.DLMF

/-- **Argument principle** (weighted): for `f` analytic on an open `U ⊇` (interior ∪ `C`) except
at finitely many zeros and poles `t ∈ T` inside, with `f = (z − t)^{n t} g`, `g(t) ≠ 0`, and `f`
nonvanishing elsewhere on the closed region, `∮_C φ f′/f = 2πi ∑ n(t) φ(t)` for entire `φ`. -/
theorem contourIntegral_mul_logDeriv (hJ : IsJordanCurve c a b) (hpos : P.IsPositivelyOriented)
    {f φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hDU : jordanInterior c a b ∪ P.curve ⊆ U)
    {T : Finset ℂ} (hT : ↑T ⊆ jordanInterior c a b) (hfd : DifferentiableOn ℂ f (U \ ↑T))
    (hf0 : ∀ z ∈ (jordanInterior c a b ∪ P.curve) \ ↑T, f z ≠ 0) (n : ℂ → ℤ)
    (hn : ∀ t ∈ T, ∃ g : ℂ → ℂ, AnalyticAt ℂ g t ∧ g t ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] t, f z = (z - t) ^ n t * g z)
    (hφ : Differentiable ℂ φ) :
    P.contourIntegral (fun z => φ z * (deriv f z / f z)) =
      2 * π * I * ∑ t ∈ T, (n t : ℂ) * φ t := by
  classical
  set D := jordanInterior c a b
  have hDo : IsOpen D := isOpen_jordanInterior hJ.continuousOn
  have hSc : IsClosed (↑T : Set ℂ) := T.finite_toSet.isClosed
  have hVo : IsOpen (U \ ↑T) := hU.sdiff hSc
  have hfd' : DifferentiableOn ℂ (deriv f) (U \ ↑T) := hfd.deriv hVo
  set F : ℂ → ℂ := fun z => φ z * (deriv f z / f z)
  have hFat : ∀ z ∈ (D ∪ P.curve) \ ↑T, DifferentiableAt ℂ F z := fun z hz => by
    have hzV : z ∈ U \ ↑T := ⟨hDU hz.1, hz.2⟩
    exact (hφ z).mul ((hfd'.differentiableAt (hVo.mem_nhds hzV)).div
      (hfd.differentiableAt (hVo.mem_nhds hzV)) (hf0 z hz))
  -- radii isolating each point of `T` inside the interior
  have hrad : ∀ t ∈ T, ∃ r > 0, ball t r ⊆ D \ (↑T \ {t}) := by
    intro t ht
    have ho : IsOpen (D \ (↑T \ {t})) := hDo.sdiff (T.finite_toSet.sdiff).isClosed
    exact Metric.isOpen_iff.mp ho t ⟨hT ht, fun h => h.2 rfl⟩
  choose! R hR0 hRb using hrad
  have hR : ∀ t ∈ T, 0 < R t ∧ ball t (R t) ⊆ D ∧ ∀ t' ∈ T, t' ≠ t → R t ≤ dist t' t := by
    intro t ht
    refine ⟨hR0 t ht, fun z hz => (hRb t ht hz).1, fun t' ht' hne => ?_⟩
    by_contra hlt
    push Not at hlt
    exact (hRb t ht (mem_ball.mpr hlt)).2 ⟨ht', hne⟩
  have hres := P.contourIntegral_eq_sum_residues hJ hpos (f := F) hT
    (fun z hz => (hFat z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hFat z ⟨Or.inl hz.1, hz.2⟩).differentiableWithinAt) R hR
  rw [hres]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨g, hg, hgt, hfg⟩ := hn t ht
  have hann : annulus t 0 (R t) ⊆ D \ ↑T := by
    intro z hz
    have hzb := (hRb t ht) (by rw [mem_ball, dist_eq_norm]; exact hz.2)
    have h1 : 0 < ‖z - t‖ := hz.1
    refine ⟨hzb.1, fun hzT => hzb.2 ⟨hzT, ?_⟩⟩
    rintro rfl
    rw [sub_self, norm_zero] at h1
    exact lt_irrefl _ h1
  exact residue_mul_logDeriv (hR0 t ht)
    (hfd.mono fun z hz => ⟨hDU (Or.inl (hann hz).1), (hann hz).2⟩)
    (fun z hz => hf0 z ⟨Or.inl (hann hz).1, (hann hz).2⟩) hφ hg hgt hfg

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

variable {c : ℝ → ℂ} {a b : ℝ}

/-- **DLMF 1.10.8** (residue theorem), single-integral form. -/
theorem dlmf_1_10_8 (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ} {S : Finset ℂ}
    (hS : ↑S ⊆ jordanInterior c a b)
    (hfc : ContinuousOn f ((jordanInterior c a b ∪ c '' Icc a b) \ ↑S))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b \ ↑S)) (R : ℂ → ℝ)
    (hR : ∀ s ∈ S, 0 < R s ∧ ball s (R s) ⊆ jordanInterior c a b ∧
      ∀ t ∈ S, t ≠ s → R s ≤ dist t s) :
    1 / (2 * π * I) * contourIntegral f c a b = ∑ s ∈ S, residue f s (R s) := by
  have hcurve : ContinuousOn f P.curve := hfc.mono fun z hz =>
    ⟨Or.inr hz, fun hzS => jordanInterior_subset (hS hzS) hz⟩
  rw [← P.contourIntegral_eq hcurve, P.contourIntegral_eq_sum_residues hJ hpos hS hfc hfd R hR,
    one_div, inv_mul_cancel_left₀ two_pi_I_ne_zero]

theorem continuousOn_mul_logDeriv_curve (P : ClosedPiecewiseC1 c a b) {f φ : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) {T : Finset ℂ}
    (hT : ↑T ⊆ jordanInterior c a b) (hfd : DifferentiableOn ℂ f (U \ ↑T))
    (hf0 : ∀ z ∈ (jordanInterior c a b ∪ c '' Icc a b) \ ↑T, f z ≠ 0)
    (hφ : Differentiable ℂ φ) : ContinuousOn (fun z => φ z * (deriv f z / f z)) P.curve := by
  have hVo : IsOpen (U \ ↑T) := hU.sdiff T.finite_toSet.isClosed
  intro z hz
  have hzT : z ∉ (↑T : Set ℂ) := fun h => jordanInterior_subset (hT h) hz
  have hzV : z ∈ U \ ↑T := ⟨hDU (Or.inr hz), hzT⟩
  exact ((hφ z).mul (((hfd.deriv hVo).differentiableAt (hVo.mem_nhds hzV)).div
    (hfd.differentiableAt (hVo.mem_nhds hzV))
      (hf0 z ⟨Or.inr hz, hzT⟩))).continuousAt.continuousWithinAt

/-- **DLMF 1.10.9** (phase principle, integral form): `N − P = (2πi)⁻¹ ∫_C f′/f dz`, where
`N − P = ∑ n(t)` counts zeros (`n > 0`) and poles (`n < 0`) with multiplicity. -/
theorem dlmf_1_10_9 (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) {T : Finset ℂ}
    (hT : ↑T ⊆ jordanInterior c a b) (hfd : DifferentiableOn ℂ f (U \ ↑T))
    (hf0 : ∀ z ∈ (jordanInterior c a b ∪ c '' Icc a b) \ ↑T, f z ≠ 0) (n : ℂ → ℤ)
    (hn : ∀ t ∈ T, ∃ g : ℂ → ℂ, AnalyticAt ℂ g t ∧ g t ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] t, f z = (z - t) ^ n t * g z) :
    ((∑ t ∈ T, n t : ℤ) : ℂ) =
      1 / (2 * π * I) * contourIntegral (fun z => deriv f z / f z) c a b := by
  have hc := continuousOn_mul_logDeriv_curve P hU hDU hT hfd hf0 (differentiable_const 1)
  simp only [one_mul] at hc
  rw [← P.contourIntegral_eq hc]
  have h := P.contourIntegral_mul_logDeriv hJ hpos hU hDU hT hfd hf0 n hn
    (differentiable_const (1 : ℂ))
  simp only [one_mul, mul_one] at h
  rw [h, one_div, inv_mul_cancel_left₀ two_pi_I_ne_zero]
  push_cast
  rfl

/-- **DLMF 1.10.10**: `(2πi)⁻¹ ∫_C z f′(z)/f(z) dz` = (sum of locations of zeros) − (sum of
locations of poles), counted with multiplicity. -/
theorem dlmf_1_10_10 (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) {T : Finset ℂ}
    (hT : ↑T ⊆ jordanInterior c a b) (hfd : DifferentiableOn ℂ f (U \ ↑T))
    (hf0 : ∀ z ∈ (jordanInterior c a b ∪ c '' Icc a b) \ ↑T, f z ≠ 0) (n : ℂ → ℤ)
    (hn : ∀ t ∈ T, ∃ g : ℂ → ℂ, AnalyticAt ℂ g t ∧ g t ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] t, f z = (z - t) ^ n t * g z) :
    1 / (2 * π * I) * contourIntegral (fun z => z * (deriv f z / f z)) c a b =
      ∑ t ∈ T, (n t : ℂ) * t := by
  rw [← P.contourIntegral_eq (continuousOn_mul_logDeriv_curve (φ := fun z => z) P hU hDU hT hfd
    hf0 differentiable_id), P.contourIntegral_mul_logDeriv (φ := fun z => z) hJ hpos hU hDU hT hfd
    hf0 n hn differentiable_id, one_div, inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-! ### Zeros inside a Jordan curve and Rouché's theorem -/

/-- An analytic function on a neighbourhood of a Jordan region that does not vanish on the curve
has finitely many zeros inside, each of finite order. -/
theorem exists_zeros_finset (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b) {h : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hC : ∀ z ∈ c '' Icc a b, h z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∈ jordanInterior c a b ∧ h z = 0) ∧
      ∀ z ∈ Z, analyticOrderAt h z ≠ ⊤ := by
  classical
  set D := jordanInterior c a b
  obtain ⟨-, -, -, hDconn, -, -, -, -, hfront, -⟩ := dlmf_1_9_iii_jordan hJ
  have hclos : closure D = D ∪ c '' Icc a b := by rw [closure_eq_self_union_frontier, hfront]
  have hK : IsCompact (closure D) := by
    rw [hclos]
    exact P.isCompact_jordanInterior_union hJ
  have hc₀ : c a ∈ closure D := by rw [hclos]; exact Or.inr ⟨a, ⟨le_rfl, P.a_le_b⟩, rfl⟩
  set V := connectedComponentIn U (c a)
  have hKV : closure D ⊆ V := hDconn.closure.isPreconnected.subset_connectedComponentIn hc₀
    (hclos ▸ hDU)
  have hVo : IsOpen V := hU.connectedComponentIn
  have hVU : V ⊆ U := connectedComponentIn_subset _ _
  have hAV : AnalyticOnNhd ℂ h V := (hh.mono hVU).analyticOnNhd hVo
  have hkey : ∀ x ∈ V, ¬ ∃ᶠ z in 𝓝[≠] x, h z = 0 := by
    intro x hx hfreq
    have := hAV.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_connectedComponentIn hx hfreq (hKV hc₀)
    exact hC _ ⟨a, ⟨le_rfl, P.a_le_b⟩, rfl⟩ this
  have hfin : {z | z ∈ D ∧ h z = 0}.Finite := by
    by_contra hinf
    obtain ⟨x, hxK, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK
      fun z hz => subset_closure hz.1
    refine hkey x (hKV hxK) ?_
    rw [accPt_iff_frequently] at hacc
    rw [frequently_nhdsWithin_iff]
    exact hacc.mono fun y hy => ⟨hy.2.2, hy.1⟩
  refine ⟨hfin.toFinset, fun z => by simp, fun z hz htop => ?_⟩
  rw [Set.Finite.mem_toFinset] at hz
  rw [analyticOrderAt_eq_top] at htop
  exact hkey z (hKV (subset_closure hz.1))
    (eventually_nhdsWithin_of_eventually_nhds htop).frequently

/-- Factorization at a zero of finite order, in the form required by the argument principle. -/
theorem exists_factor_of_analyticOrderAt {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀)
    (htop : analyticOrderAt h z₀ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] z₀, h z = (z - z₀) ^ (((analyticOrderAt h z₀).toNat : ℕ) : ℤ) * g z := by
  obtain ⟨g, hg, hg0, hev⟩ := (hh.analyticOrderAt_eq_natCast).mp
    (ENat.natCast_toNat htop).symm
  refine ⟨g, hg, hg0, (eventually_nhdsWithin_of_eventually_nhds hev).mono fun z hz => ?_⟩
  rw [hz, smul_eq_mul, zpow_natCast]

/-- `∮_C h′/h = 2πi · (number of zeros of `h` inside `C`, with multiplicity)`. -/
theorem contourIntegral_logDeriv_eq_card (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hC : ∀ z ∈ c '' Icc a b, h z ≠ 0) {Z : Finset ℂ}
    (hZ : ∀ z, z ∈ Z ↔ z ∈ jordanInterior c a b ∧ h z = 0)
    (hZtop : ∀ z ∈ Z, analyticOrderAt h z ≠ ⊤) :
    P.contourIntegral (fun z => deriv h z / h z) =
      2 * π * I * ((∑ z ∈ Z, (analyticOrderAt h z).toNat : ℕ) : ℂ) := by
  have hT : ↑Z ⊆ jordanInterior c a b := fun z hz => ((hZ z).mp hz).1
  have hf0 : ∀ z ∈ (jordanInterior c a b ∪ c '' Icc a b) \ ↑Z, h z ≠ 0 := by
    rintro z ⟨hz | hz, hzZ⟩ h0
    · exact hzZ ((hZ z).mpr ⟨hz, h0⟩)
    · exact hC z hz h0
  have hint := P.contourIntegral_mul_logDeriv hJ hpos (φ := fun _ => 1) hU hDU hT
    (hh.mono sdiff_subset) hf0 (fun z => ((analyticOrderAt h z).toNat : ℤ))
    (fun t ht => exists_factor_of_analyticOrderAt
      ((hh.analyticOnNhd hU) t (hDU (Or.inl (hT ht)))) (hZtop t ht))
    (differentiable_const 1)
  simp only [one_mul, mul_one] at hint
  rw [hint]
  push_cast
  rfl

/-- **Rouché's theorem** (DLMF §1.10(iv)): if `f`, `g` are analytic on and inside the Jordan curve
`C` and `|g| < |f|` on `C`, then `f` and `f + g` have the same number of zeros inside `C`
(counted with multiplicity; the zero sets are finite and the orders finite). -/
theorem dlmf_1_10_iv_rouche (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) (hlt : ∀ z ∈ c '' Icc a b, ‖g z‖ < ‖f z‖) :
    ∃ Zf Zfg : Finset ℂ, (∀ z, z ∈ Zf ↔ z ∈ jordanInterior c a b ∧ f z = 0) ∧
      (∀ z, z ∈ Zfg ↔ z ∈ jordanInterior c a b ∧ f z + g z = 0) ∧
      (∀ z ∈ Zf, analyticOrderAt f z ≠ ⊤) ∧
      (∀ z ∈ Zfg, analyticOrderAt (fun w => f w + g w) z ≠ ⊤) ∧
      ∑ z ∈ Zf, (analyticOrderAt f z).toNat =
        ∑ z ∈ Zfg, (analyticOrderAt (fun w => f w + g w) z).toNat := by
  set h : ℂ → ℂ := fun w => f w + g w
  have hh : DifferentiableOn ℂ h U := hf.add hg
  have hfC : ∀ z ∈ c '' Icc a b, f z ≠ 0 := fun z hz h0 => by
    have := hlt z hz
    rw [h0, norm_zero] at this
    exact absurd this (not_lt.mpr (norm_nonneg _))
  have hhC : ∀ z ∈ c '' Icc a b, h z ≠ 0 := fun z hz h0 => by
    have h1 := hlt z hz
    have h2 : f z = -g z := eq_neg_of_add_eq_zero_left h0
    rw [h2, norm_neg] at h1
    exact lt_irrefl _ h1
  obtain ⟨Zf, hZf, hZftop⟩ := exists_zeros_finset P hJ hU hDU hf hfC
  obtain ⟨Zh, hZh, hZhtop⟩ := exists_zeros_finset P hJ hU hDU hh hhC
  refine ⟨Zf, Zh, hZf, hZh, hZftop, hZhtop, ?_⟩
  have I1 := contourIntegral_logDeriv_eq_card P hJ hpos hU hDU hf hfC hZf hZftop
  have I2 := contourIntegral_logDeriv_eq_card P hJ hpos hU hDU hh hhC hZh hZhtop
  -- the two logarithmic derivatives have the same integral
  have hcurveU : ∀ z ∈ P.curve, z ∈ U := fun z hz => hDU (Or.inr hz)
  have hdf : ∀ z ∈ P.curve, DifferentiableAt ℂ f z := fun z hz =>
    hf.differentiableAt (hU.mem_nhds (hcurveU z hz))
  have hdg : ∀ z ∈ P.curve, DifferentiableAt ℂ g z := fun z hz =>
    hg.differentiableAt (hU.mem_nhds (hcurveU z hz))
  have hdd : ∀ (k : ℂ → ℂ), DifferentiableOn ℂ k U → ∀ z ∈ P.curve,
      DifferentiableAt ℂ (deriv k) z := fun k hk z hz =>
    (hk.deriv hU).differentiableAt (hU.mem_nhds (hcurveU z hz))
  have hcont : ∀ (k : ℂ → ℂ), DifferentiableOn ℂ k U → (∀ z ∈ c '' Icc a b, k z ≠ 0) →
      ContinuousOn (fun z => deriv k z / k z) P.curve := fun k hk hk0 z hz =>
    ((hdd k hk z hz).div (hk.differentiableAt (hU.mem_nhds (hcurveU z hz)))
      (hk0 z hz)).continuousAt.continuousWithinAt
  have hdiff : P.contourIntegral (fun z => deriv h z / h z - deriv f z / f z) = 0 := by
    refine P.contourIntegral_eq_zero_of_hasDerivAt
      (F := fun z => log (h z / f z)) (fun z hz => ?_)
      ((hcont h hh hhC).sub (hcont f hf hfC))
    have hf0 := hfC z hz
    have hh0 := hhC z hz
    have hslit : h z / f z ∈ slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      have hq : ‖g z / f z‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hf0)]
        exact hlt z hz
      have hre := abs_re_le_norm (g z / f z)
      have : h z / f z = 1 + g z / f z := by
        simp only [h]
        field_simp
      rw [this, add_re, one_re]
      linarith [(abs_le.mp (hre.trans hq.le)).1, abs_lt.mp (hre.trans_lt hq)]
    have hdh : HasDerivAt h (deriv f z + deriv g z) z :=
      (hdf z hz).hasDerivAt.add (hdg z hz).hasDerivAt
    have hq : HasDerivAt (fun z => h z / f z)
        (((deriv f z + deriv g z) * f z - h z * deriv f z) / f z ^ 2) z :=
      hdh.div (hdf z hz).hasDerivAt hf0
    have hlog := hq.clog hslit
    refine hlog.congr_deriv ?_
    rw [hdh.deriv]
    field_simp
  rw [P.contourIntegral_sub (hcont h hh hhC) (hcont f hf hfC), sub_eq_zero, I1, I2] at hdiff
  have := mul_left_cancel₀ two_pi_I_ne_zero hdiff
  exact_mod_cast this.symm

end Azurite.DLMF

/-! ### The phase principle -/

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

theorem ae_piece_eq {F : ℂ → ℂ} {i : ℕ} (hi : i < P.n) :
    ∀ᵐ s ∂volume, s ∈ Ι (P.t i) (P.t (i + 1)) →
      F (P.g i s) * deriv (P.g i) s = F (c s) * deriv c s := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (P.t (i + 1)))]
    with s hs hsI
  rw [uIoc_of_le (P.lt i hi).le] at hsI
  have hsIoo : s ∈ Ioo (P.t i) (P.t (i + 1)) :=
    ⟨hsI.1, lt_of_le_of_ne hsI.2 fun h => hs (by simp [h])⟩
  have hev : c =ᶠ[𝓝 s] P.g i := eventually_of_mem (Ioo_mem_nhds hsIoo.1 hsIoo.2)
    fun x hx => P.eqOn i hi (Ioo_subset_Icc_self hx)
  rw [hev.deriv_eq, P.eqOn i hi (Ioo_subset_Icc_self hsIoo)]

theorem intervalIntegrable_full {F : ℂ → ℂ} (hF : ContinuousOn F P.curve) :
    IntervalIntegrable (fun s => F (c s) * deriv c s) volume a b := by
  have hint : ∀ i < P.n,
      IntervalIntegrable (fun s => F (c s) * deriv c s) volume (P.t i) (P.t (i + 1)) :=
    fun i hi => (P.intervalIntegrable_piece hF hi).congr_ae (ae_restrict_of_ae_restrict_of_subset
      subset_rfl ((ae_restrict_iff' measurableSet_uIoc).mpr (P.ae_piece_eq hi)))
  have := IntervalIntegrable.trans_iterate hint
  rwa [P.first, P.last] at this

/-- Along the curve, `h(c(t)) = exp(∫ₐᵗ h′/h dz) h(c(a))`. -/
theorem eq_exp_primitive_mul {h : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hcV : P.curve ⊆ V)
    (hd : DifferentiableOn ℂ h V) (h0 : ∀ z ∈ P.curve, h z ≠ 0) :
    ∀ t ∈ Icc a b, h (c t) =
      exp (∫ s in a..t, deriv h (c s) / h (c s) * deriv c s) * h (c a) := by
  set F : ℂ → ℂ := fun z => deriv h z / h z
  have hFd : ∀ z ∈ P.curve, DifferentiableAt ℂ F z := fun z hz =>
    ((hd.deriv hV).differentiableAt (hV.mem_nhds (hcV hz))).div
      (hd.differentiableAt (hV.mem_nhds (hcV hz))) (h0 z hz)
  have hFc : ContinuousOn F P.curve := fun z hz => (hFd z hz).continuousAt.continuousWithinAt
  set k : ℝ → ℂ := fun s => F (c s) * deriv c s
  have hkint := P.intervalIntegrable_full hFc
  set L : ℝ → ℂ := fun t => ∫ s in a..t, k s
  have hab := P.a_le_b
  have hLc : ContinuousOn L (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval' hkint left_mem_uIcc
    rwa [uIcc_of_le hab] at this
  have hmaps : MapsTo c (Icc a b) P.curve := fun t ht => ⟨t, ht, rfl⟩
  have hhc : ContinuousOn (fun t => h (c t)) (Icc a b) :=
    (hd.continuousOn.mono hcV).comp P.continuousOn hmaps
  set E : ℝ → ℂ := fun t => exp (-L t) * h (c t)
  have hEc : ContinuousOn E (Icc a b) := (hLc.neg.cexp).mul hhc
  -- `E` has zero derivative inside each piece
  have hderiv : ∀ i < P.n, ∀ t ∈ Ioo (P.t i) (P.t (i + 1)), HasDerivAt E 0 t := by
    intro i hi t ht
    have hsub : Icc (P.t i) (P.t (i + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (P.t_mem_Icc hi.le).1 (P.t_mem_Icc hi).2
    have hev : c =ᶠ[𝓝 t] P.g i := eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)
      fun x hx => P.eqOn i hi (Ioo_subset_Icc_self hx)
    have hgd := (P.contDiff i hi).differentiable one_ne_zero
    have hct : HasDerivAt c (deriv (P.g i) t) t := (hgd t).hasDerivAt.congr_of_eventuallyEq hev
    have hcurve : c t ∈ P.curve := hmaps (hsub (Ioo_subset_Icc_self ht))
    have hhd : HasDerivAt (fun s => h (c s)) (deriv h (c t) * deriv (P.g i) t) t :=
      (hd.differentiableAt (hV.mem_nhds (hcV hcurve))).hasDerivAt.comp t hct
    -- continuity of `k` near `t`
    have hkc : ∀ s ∈ Ioo (P.t i) (P.t (i + 1)), ContinuousAt k s := by
      intro s hs
      have hevs : c =ᶠ[𝓝 s] P.g i := eventually_of_mem (Ioo_mem_nhds hs.1 hs.2)
        fun x hx => P.eqOn i hi (Ioo_subset_Icc_self hx)
      have hk' : k =ᶠ[𝓝 s] fun s => F (P.g i s) * deriv (P.g i) s := by
        filter_upwards [hevs, hevs.deriv] with x hx hx'
        simp only [k, hx, hx']
      refine ContinuousAt.congr ?_ hk'.symm
      have hgs : P.g i s ∈ P.curve := P.mem_curve_of_mem_piece hi (Ioo_subset_Icc_self hs)
      exact ((hFd _ hgs).continuousAt.comp (hgd s).continuousAt).mul
        (((P.contDiff i hi).continuous_deriv le_rfl).continuousAt)
    have hmeas : StronglyMeasurableAtFilter k (𝓝 t) :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (fun s hs => (hkc s hs).continuousWithinAt) t ht
    have hLd : HasDerivAt L (k t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hkint.mono_set (by
          rw [uIcc_of_le hab, uIcc_of_le (hsub (Ioo_subset_Icc_self ht)).1]
          exact Icc_subset_Icc le_rfl (hsub (Ioo_subset_Icc_self ht)).2)) hmeas (hkc t ht)
    have hE := (hLd.neg.cexp).mul hhd
    convert hE using 1
    have hct' : deriv c t = deriv (P.g i) t := hct.deriv
    simp only [k, F, hct']
    have := h0 _ hcurve
    field_simp
    ring
  -- hence constant on each piece
  have hpiece : ∀ i < P.n, ∀ t ∈ Icc (P.t i) (P.t (i + 1)), E t = E (P.t i) := by
    intro i hi
    have hlt := P.lt i hi
    have hsub : Icc (P.t i) (P.t (i + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (P.t_mem_Icc hi.le).1 (P.t_mem_Icc hi).2
    set m := (P.t i + P.t (i + 1)) / 2 with hmdef
    have hm : m ∈ Ioo (P.t i) (P.t (i + 1)) := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
    have hconst : EqOn E (fun _ => E m) (Ioo (P.t i) (P.t (i + 1))) := fun x hx =>
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        (fun y hy => (hderiv i hi y hy).differentiableAt.differentiableWithinAt)
        (fun y hy => (hderiv i hi y hy).deriv) hx hm
    have hext := hconst.of_subset_closure (hEc.mono hsub) continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hlt.ne])
    intro t ht
    rw [hext ht, hext (left_mem_Icc.mpr hlt.le)]
  have hknots : ∀ i ≤ P.n, E (P.t i) = E a := by
    intro i
    induction i with
    | zero => intro _; rw [P.first]
    | succ i ih =>
      intro hi
      rw [← ih (by omega), hpiece i (by omega) _ (right_mem_Icc.mpr (P.lt i (by omega)).le)]
  have hEa : ∀ t ∈ Icc a b, E t = E a := by
    intro t ht
    rcases Nat.eq_zero_or_pos P.n with hn | hn
    · have hab' : a = b := by
        have h2 := P.last
        rw [hn] at h2
        exact P.first.symm.trans h2
      have : t = a := le_antisymm (hab' ▸ ht.2) ht.1
      rw [this]
    · obtain ⟨i, hi, hti⟩ := P.exists_piece ht hn
      rw [hpiece i hi t hti, hknots i hi.le]
  intro t ht
  have h1 := hEa t ht
  simp only [E, L, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, one_mul] at h1
  rw [← h1, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- An integer-valued continuous function on `[a, b]` vanishing at `a` vanishes identically. -/
theorem eq_zero_of_int_valued {u : ℝ → ℝ} {a b : ℝ} (hu : ContinuousOn u (Icc a b))
    (hint : ∀ t ∈ Icc a b, ∃ n : ℤ, u t = n) (ha : u a = 0) : ∀ t ∈ Icc a b, u t = 0 := by
  intro t ht
  obtain ⟨n, hn⟩ := hint t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hhalf : ∀ s ∈ Icc a b, u s ≠ 1 / 2 ∧ u s ≠ -(1 / 2) := by
    intro s hs
    obtain ⟨m, hm⟩ := hint s hs
    rw [hm]
    constructor
    · intro h
      rcases le_or_gt m 0 with hm0 | hm0
      · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
        linarith
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
    · intro h
      rcases le_or_gt 0 m with hm0 | hm0
      · have : (0 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith
      · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm0
        linarith
  by_contra hne
  rw [hn] at hne
  rcases lt_or_gt_of_ne (show n ≠ 0 by rintro rfl; simp at hne) with hneg | hpos
  · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
    obtain ⟨s, hs, hus⟩ := intermediate_value_Icc' ht.1 (hu.mono hsub)
      (show (-(1 / 2) : ℝ) ∈ Icc (u t) (u a) from ⟨by rw [hn]; linarith, by rw [ha]; norm_num⟩)
    exact (hhalf s (hsub hs)).2 hus
  · have hle : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    obtain ⟨s, hs, hus⟩ := intermediate_value_Icc ht.1 (hu.mono hsub)
      (show (1 / 2 : ℝ) ∈ Icc (u a) (u t) from ⟨by rw [ha]; norm_num, by rw [hn]; linarith⟩)
    exact (hhalf s (hsub hs)).1 hus

/-- **Phase form of the argument principle**: if `θ` is a continuous branch of `ph h(c(t))`,
then `∮_C h′/h dz = i (θ(b) − θ(a))`. -/
theorem contourIntegral_logDeriv_eq_phase {h : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hcV : P.curve ⊆ V) (hd : DifferentiableOn ℂ h V) (h0 : ∀ z ∈ P.curve, h z ≠ 0)
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc a b))
    (hph : ∀ t ∈ Icc a b, h (c t) = ‖h (c t)‖ * exp (θ t * I)) :
    P.contourIntegral (fun z => deriv h z / h z) = I * ((θ b - θ a : ℝ) : ℂ) := by
  have hFc : ContinuousOn (fun z => deriv h z / h z) P.curve := fun z hz =>
    (((hd.deriv hV).differentiableAt (hV.mem_nhds (hcV hz))).div
      (hd.differentiableAt (hV.mem_nhds (hcV hz))) (h0 z hz)).continuousAt.continuousWithinAt
  rw [P.contourIntegral_eq hFc]
  unfold Azurite.DLMF.contourIntegral
  set L : ℝ → ℂ := fun t => ∫ s in a..t, deriv h (c s) / h (c s) * deriv c s with hLdef
  show L b = _
  have hab := P.a_le_b
  have hexp := P.eq_exp_primitive_mul hV hcV hd h0
  have hmaps : MapsTo c (Icc a b) P.curve := fun t ht => ⟨t, ht, rfl⟩
  have haI : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hca : h (c a) ≠ 0 := h0 _ (hmaps haI)
  have hnpos : ∀ t ∈ Icc a b, 0 < ‖h (c t)‖ := fun t ht => norm_pos_iff.mpr (h0 _ (hmaps ht))
  have hkint := P.intervalIntegrable_full hFc
  have hLc : ContinuousOn L (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval' hkint left_mem_uIcc
    rwa [uIcc_of_le hab] at this
  have hhc : ContinuousOn (fun t => h (c t)) (Icc a b) :=
    (hd.continuousOn.mono hcV).comp P.continuousOn hmaps
  set Ψ : ℝ → ℂ := fun t => L t - ((Real.log (‖h (c t)‖ / ‖h (c a)‖) : ℂ) +
    I * ((θ t - θ a : ℝ) : ℂ)) with hΨ
  have hΨexp : ∀ t ∈ Icc a b, exp (Ψ t) = 1 := by
    intro t ht
    have e1 : exp (L t) = h (c t) / h (c a) := by
      rw [hexp t ht, mul_div_cancel_right₀ _ hca]
    have e2 : exp ((Real.log (‖h (c t)‖ / ‖h (c a)‖) : ℂ) + I * ((θ t - θ a : ℝ) : ℂ)) =
        h (c t) / h (c a) := by
      rw [exp_add, ← ofReal_exp, Real.exp_log (div_pos (hnpos t ht) (hnpos a haI))]
      conv_rhs => rw [hph t ht, hph a haI]
      rw [show I * ((θ t - θ a : ℝ) : ℂ) = θ t * I - θ a * I by push_cast; ring, exp_sub]
      have hea : exp (θ a * I) ≠ 0 := exp_ne_zero _
      have hna : (‖h (c a)‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hnpos a haI).ne'
      push_cast
      field_simp
    rw [hΨ, exp_sub, e1, e2, div_self (div_ne_zero (h0 _ (hmaps ht)) hca)]
  have hΨc : ContinuousOn Ψ (Icc a b) := by
    refine hLc.sub (ContinuousOn.add ?_ ?_)
    · refine continuous_ofReal.comp_continuousOn (ContinuousOn.log ?_ fun t ht => ?_)
      · exact (continuous_norm.comp_continuousOn hhc).div_const _
      · exact (div_pos (hnpos t ht) (hnpos a haI)).ne'
    · exact continuousOn_const.mul (continuous_ofReal.comp_continuousOn (hθ.sub continuousOn_const))
  set u : ℝ → ℝ := fun t => (Ψ t).im / (2 * π)
  have hInt : ∀ t ∈ Icc a b, ∃ n : ℤ, Ψ t = n * (2 * π * I) := fun t ht =>
    exp_eq_one_iff.mp (hΨexp t ht)
  have hu : ∀ t ∈ Icc a b, ∃ n : ℤ, u t = n := fun t ht => by
    obtain ⟨n, hn⟩ := hInt t ht
    refine ⟨n, ?_⟩
    show (Ψ t).im / (2 * π) = n
    rw [hn]
    simp
  have hΨa : Ψ a = 0 := by simp [hΨ, hLdef, Real.log_one, div_self (hnpos a haI).ne']
  have hu0 := eq_zero_of_int_valued
    ((continuous_im.comp_continuousOn hΨc).div_const (2 * π)) hu (by simp [hΨa])
  have hbI : b ∈ Icc a b := right_mem_Icc.mpr hab
  obtain ⟨n, hn⟩ := hInt b hbI
  have hn0 : n = 0 := by
    have h1 : (Ψ b).im / (2 * π) = 0 := hu0 b hbI
    rw [hn] at h1
    simpa using h1
  rw [hn0, Int.cast_zero, zero_mul] at hn
  have hcb : c b = c a := P.closed.symm
  simp only [hΨ, hcb, div_self (hnpos a haI).ne', Real.log_one, ofReal_zero, zero_add] at hn
  exact sub_eq_zero.mp hn

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

variable {c : ℝ → ℂ} {a b : ℝ}

/-- **DLMF 1.10.9** (phase principle): `N − P = (2π)⁻¹ Δ_C(ph f(z))`, where `θ` is any continuous
branch of `ph f(c(t))` along `C`. -/
theorem dlmf_1_10_9_phase (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b)
    (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hDU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) {T : Finset ℂ}
    (hT : ↑T ⊆ jordanInterior c a b) (hfd : DifferentiableOn ℂ f (U \ ↑T))
    (hf0 : ∀ z ∈ (jordanInterior c a b ∪ c '' Icc a b) \ ↑T, f z ≠ 0) (n : ℂ → ℤ)
    (hn : ∀ t ∈ T, ∃ g : ℂ → ℂ, AnalyticAt ℂ g t ∧ g t ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] t, f z = (z - t) ^ n t * g z)
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc a b))
    (hph : ∀ t ∈ Icc a b, f (c t) = ‖f (c t)‖ * exp (θ t * I)) :
    ((∑ t ∈ T, n t : ℤ) : ℝ) = (θ b - θ a) / (2 * π) := by
  have h1 := dlmf_1_10_9 P hJ hpos hU hDU hT hfd hf0 n hn
  have hc := continuousOn_mul_logDeriv_curve P hU hDU hT hfd hf0 (differentiable_const 1)
  simp only [one_mul] at hc
  have hcurveV : P.curve ⊆ U \ ↑T := fun z hz =>
    ⟨hDU (Or.inr hz), fun h => jordanInterior_subset (hT h) hz⟩
  have h2 := P.contourIntegral_logDeriv_eq_phase (hU.sdiff T.finite_toSet.isClosed) hcurveV hfd
    (fun z hz => hf0 z ⟨Or.inr hz, (hcurveV hz).2⟩) hθ hph
  rw [← P.contourIntegral_eq hc, h2] at h1
  have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
  have : (((∑ t ∈ T, n t : ℤ) : ℝ) : ℂ) = (((θ b - θ a) / (2 * π) : ℝ) : ℂ) := by
    push_cast at h1 ⊢
    rw [h1]
    field_simp
  exact_mod_cast this

end Azurite.DLMF
