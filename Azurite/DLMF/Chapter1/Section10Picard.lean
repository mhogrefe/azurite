/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section10Schottky
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# DLMF §1.10(iii): Picard's theorem

Formalizations of the remarks in <https://dlmf.nist.gov/1.10.iii> on essential singularities,
via Bloch's theorem (`Section10Bloch.lean`) and Schottky's theorem (`Section10Schottky.lean`).

* `norm_le_chainBound`: Schottky's bound carried around a circle `|z − z₀| = ρ` by sixteen steps
  either way, with a bound `chainBound t` independent of `ρ`.
* `norm_le_of_annulus` (maximum principle on an annulus), `bdd_of_infinite`, `bdd_or_inv_bdd`:
  a function omitting `0` and `1` in a punctured disk is bounded, or has bounded reciprocal, in a
  smaller punctured disk.
* `laurentCoeff_eq_zero_of_eq_div_pow`, `not_essential_of_eq_div_pow`,
  `exists_eq_div_pow_of_bdd` (Riemann's extension), `exists_eq_div_pow_of_inv_bdd`,
  `not_essential_of_omits`.
* **Picard's theorem**: `dlmf_1_10_iii_picard` (in every punctured neighbourhood of an isolated
  essential singularity at most one value is omitted) and `dlmf_1_10_iii_picard_infinite` (DLMF's
  form: every value except possibly one is assumed infinitely many times); `little_picard`.
* Infinitely many poles: `IsEssentialSingularityAtInftyOfPoles` (DLMF's naming of `∞` as an
  essential singularity of a meromorphic function with infinitely many poles), with
  `IsMeromorphicDLMF.finite_poles` (finitely many poles in each disk), `exists_pole_norm_gt` (the
  poles accumulate at `∞`) and `not_differentiableOn_inv_of_poles` (`∞` is not isolated).
-/

open Filter Topology Set Metric Complex
open scoped Real

namespace Azurite.DLMF

/-! ### Schottky's bound carried around a circle -/

/-- The bounds obtained after `k` Schottky steps from the initial bound `t`. -/
noncomputable def chainSeq (t : ℝ) : ℕ → ℝ
  | 0 => t
  | k + 1 => max (chainSeq t k) (schottkyBound (chainSeq t k))

/-- The bound on a whole circle: sixteen steps of angle `1/4` either way cover `[−π, π]`. -/
noncomputable def chainBound (t : ℝ) : ℝ := chainSeq t 16

theorem norm_ofReal_mul_exp_sub {ρ θ θ' : ℝ} (hρ : 0 ≤ ρ) :
    ‖(ρ : ℂ) * cexp (θ * I) - ρ * cexp (θ' * I)‖ ≤ ρ * |θ - θ'| := by
  have e : (ρ : ℂ) * cexp (θ * I) - ρ * cexp (θ' * I) =
      ρ * cexp (θ' * I) * (cexp (I * ((θ - θ' : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_assoc, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  gcongr
  exact (Real.norm_exp_I_mul_ofReal_sub_one_le).trans_eq (Real.norm_eq_abs _)

/-- **Schottky along a circle**: if `G` omits `0` and `1` on `0 < |z − z₀| < r` and
`|G(z₀ + ρ)| ≤ t`, where `3ρ/2 ≤ r`, then `|G| ≤ chainBound t` on `|z − z₀| = ρ`. -/
theorem norm_le_chainBound {G : ℂ → ℂ} {z₀ : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : 3 * ρ / 2 ≤ r)
    (hG : DifferentiableOn ℂ G (annulus z₀ 0 r)) (h0 : ∀ z ∈ annulus z₀ 0 r, G z ≠ 0)
    (h1 : ∀ z ∈ annulus z₀ 0 r, G z ≠ 1) {t : ℝ} (ht : ‖G (z₀ + ρ)‖ ≤ t) :
    ∀ z ∈ sphere z₀ ρ, ‖G z‖ ≤ chainBound t := by
  have step : ∀ k : ℕ, ∀ θ : ℝ, |θ| ≤ k / 4 →
      ‖G (z₀ + ρ * cexp (θ * I))‖ ≤ chainSeq t k := by
    intro k
    induction k with
    | zero =>
      intro θ hθ
      have : θ = 0 := abs_nonpos_iff.mp (by simpa using hθ)
      simpa [this, chainSeq] using ht
    | succ k ih =>
      intro θ hθ
      set θ' := max (-(k / 4 : ℝ)) (min θ (k / 4)) with hθ'
      have hθ'k : |θ'| ≤ k / 4 := by
        have : (0 : ℝ) ≤ k / 4 := by positivity
        rw [abs_le]; constructor
        · exact le_max_left _ _
        · exact max_le (by linarith) (min_le_right _ _)
      have hdθ : |θ - θ'| ≤ 1 / 4 := by
        have : (0 : ℝ) ≤ k / 4 := by positivity
        push_cast at hθ
        rw [abs_le] at hθ ⊢
        rw [hθ']
        simp only [max_def, min_def]
        split_ifs <;> constructor <;> linarith
      set c := z₀ + ρ * cexp (θ' * I) with hc
      have hcn : ‖c - z₀‖ = ρ := by
        rw [hc, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hsub : ball c (ρ / 2) ⊆ annulus z₀ 0 r := by
        intro z hz
        rw [mem_ball, dist_eq_norm] at hz
        have a1 := norm_sub_le (z - z₀) (z - c)
        have a2 := norm_sub_le (z - c) (z₀ - c)
        rw [show z - z₀ - (z - c) = c - z₀ by ring] at a1
        rw [show z - c - (z₀ - c) = z - z₀ by ring, norm_sub_rev z₀ c] at a2
        constructor <;> linarith
      have hS := schottky (c := c) (R := ρ / 2) (by linarith) (hG.mono hsub)
        (fun z hz => h0 z (hsub hz)) (fun z hz => h1 z (hsub hz)) (ih θ' hθ'k)
        (z := z₀ + ρ * cexp (θ * I)) (by
          rw [mem_closedBall, dist_eq_norm, hc, add_sub_add_left_eq_sub]
          calc _ ≤ ρ * |θ - θ'| := norm_ofReal_mul_exp_sub hρ.le
            _ ≤ ρ * (1 / 4) := by gcongr
            _ = ρ / 2 / 2 := by ring)
      exact hS.trans (le_max_right _ _)
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have e : z = z₀ + ρ * cexp ((arg (z - z₀) : ℂ) * I) := by
    rw [← hz, Complex.norm_mul_exp_arg_mul_I]; ring
  rw [e]
  refine step 16 _ ?_
  have := Complex.abs_arg_le_pi (z - z₀)
  have := Real.pi_le_four
  push_cast; linarith

/-! ### Boundedness near the singularity -/

theorem closure_annulus_subset {z₀ : ℂ} {a b : ℝ} :
    closure (annulus z₀ a b) ⊆ {z | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    ((isClosed_le continuous_const (continuous_sub_right z₀).norm).inter
      (isClosed_le (continuous_sub_right z₀).norm continuous_const))

/-- **Maximum principle on an annulus**: a bound on both boundary circles bounds the interior. -/
theorem norm_le_of_annulus {H : ℂ → ℂ} {z₀ : ℂ} {a b r C : ℝ} (ha : 0 < a) (hbr : b < r)
    (hH : DifferentiableOn ℂ H (annulus z₀ 0 r)) (hCa : ∀ z ∈ sphere z₀ a, ‖H z‖ ≤ C)
    (hCb : ∀ z ∈ sphere z₀ b, ‖H z‖ ≤ C) {z : ℂ} (hz : z ∈ annulus z₀ a b) : ‖H z‖ ≤ C := by
  have hsub : closure (annulus z₀ a b) ⊆ annulus z₀ 0 r := fun w hw => by
    have := closure_annulus_subset hw
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  refine Complex.norm_le_of_forall_mem_frontier_norm_le ?_ ?_ ?_ (subset_closure hz)
  · exact isBounded_ball.subset fun w hw => by
      rw [mem_ball, dist_eq_norm]; exact hw.2
  · exact ⟨hH.mono (subset_closure.trans hsub), (hH.continuousOn).mono hsub⟩
  · intro w hw
    rw [(isOpen_annulus z₀ a b).frontier_eq] at hw
    have h1 := closure_annulus_subset hw.1
    have h2 : ¬ (a < ‖w - z₀‖ ∧ ‖w - z₀‖ < b) := hw.2
    rcases eq_or_lt_of_le h1.1 with h | h
    · exact hCa w (by rw [mem_sphere_iff_norm]; exact h.symm)
    · rcases eq_or_lt_of_le h1.2 with h' | h'
      · exact hCb w (by rw [mem_sphere_iff_norm]; exact h')
      · exact absurd ⟨h, h'⟩ h2

/-- If `H` omits `0` and `1` near `z₀` and `|H(z₀ + ρₙ)| ≤ 1` along infinitely many radii
`ρₙ = r/(4·2ⁿ)`, then `H` is bounded in a punctured disk around `z₀`. -/
theorem bdd_of_infinite {H : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hH : DifferentiableOn ℂ H (annulus z₀ 0 r)) (h0 : ∀ z ∈ annulus z₀ 0 r, H z ≠ 0)
    (h1 : ∀ z ∈ annulus z₀ 0 r, H z ≠ 1) {S : Set ℕ} (hS : S.Infinite)
    (hSb : ∀ n ∈ S, ‖H (z₀ + (r / 4 * (1 / 2) ^ n : ℝ))‖ ≤ 1) :
    ∃ δ > 0, ∀ z ∈ annulus z₀ 0 δ, ‖H z‖ ≤ chainBound 1 := by
  set ρ : ℕ → ℝ := fun n => r / 4 * (1 / 2) ^ n with hρ
  have hρpos : ∀ n, 0 < ρ n := fun n => by positivity
  have hρle : ∀ n, ρ n ≤ r / 4 := fun n =>
    mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hρanti : Antitone ρ := fun m n hmn =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)
      (by positivity)
  have hsph : ∀ n ∈ S, ∀ z ∈ sphere z₀ (ρ n), ‖H z‖ ≤ chainBound 1 := fun n hn =>
    norm_le_chainBound (hρpos n) (by linarith [hρle n]) hH h0 h1 (hSb n hn)
  obtain ⟨n₀, hn₀⟩ := hS.nonempty
  refine ⟨ρ n₀, hρpos n₀, fun z hz => ?_⟩
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ‖z - z₀‖ / (r / 4) by
    have := hz.1; positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨n, hnS, hNn'⟩ := hS.exists_gt N
  have hNn := hNn'.le
  have hρn : ρ n < ‖z - z₀‖ := by
    have := hρanti hNn
    have : ρ N < ‖z - z₀‖ := by
      simp only [hρ]
      rw [lt_div_iff₀ (by positivity)] at hN; linarith
    linarith
  exact norm_le_of_annulus (hρpos n) (show ρ n₀ < r by linarith [hρle n₀]) hH (hsph n hnS)
    (hsph n₀ hn₀) ⟨hρn, hz.2⟩

/-- A function omitting `0` and `1` in a punctured disk is bounded, or has bounded reciprocal,
in a smaller punctured disk. -/
theorem bdd_or_inv_bdd {G : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (annulus z₀ 0 r)) (h0 : ∀ z ∈ annulus z₀ 0 r, G z ≠ 0)
    (h1 : ∀ z ∈ annulus z₀ 0 r, G z ≠ 1) :
    (∃ δ > 0, ∀ z ∈ annulus z₀ 0 δ, ‖G z‖ ≤ chainBound 1) ∨
      ∃ δ > 0, ∀ z ∈ annulus z₀ 0 δ, ‖(G z)⁻¹‖ ≤ chainBound 1 := by
  set p : ℕ → ℂ := fun n => z₀ + (r / 4 * (1 / 2) ^ n : ℝ)
  have hU : {n | ‖G (p n)‖ ≤ 1} ∪ {n | ‖(G (p n))⁻¹‖ ≤ 1} = univ := by
    ext n
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true, norm_inv]
    rcases le_total ‖G (p n)‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)
  have hinf : ({n | ‖G (p n)‖ ≤ 1} ∪ {n | ‖(G (p n))⁻¹‖ ≤ 1}).Infinite := by
    rw [hU]; exact infinite_univ
  rcases infinite_union.mp hinf with h | h
  · exact Or.inl (bdd_of_infinite hr hG h0 h1 h fun n hn => hn)
  · refine Or.inr (bdd_of_infinite (H := fun z => (G z)⁻¹) hr (hG.inv h0)
      (fun z hz => inv_ne_zero (h0 z hz)) (fun z hz h' => h1 z hz ?_) h fun n hn => hn)
    simpa using congrArg (·⁻¹) h'

/-! ### Not an essential singularity -/

theorem ball_diff_eq_annulus (z₀ : ℂ) (δ : ℝ) : ball z₀ δ \ {z₀} = annulus z₀ 0 δ := by
  ext z
  simp only [Set.mem_sdiff, mem_ball, dist_eq_norm, mem_singleton_iff, annulus, mem_ofPred_eq,
    norm_pos_iff, sub_ne_zero]
  tauto

/-- If `f(z) = φ(z)/(z − z₀)ᵐ` near `z₀`, with `φ` holomorphic at `z₀`, then `aₙ = 0` for
`n < −m`. -/
theorem laurentCoeff_eq_zero_of_eq_div_pow {f φ : ℂ → ℂ} {z₀ : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 R)) (hδ : 0 < δ)
    (hφ : DifferentiableOn ℂ φ (ball z₀ δ)) {m : ℕ}
    (heq : ∀ z ∈ annulus z₀ 0 δ, f z = φ z / (z - z₀) ^ m) {n : ℤ} (hn : n < -(m : ℤ)) :
    laurentCoeff f z₀ (R / 2) n = 0 := by
  set ρ := min δ R / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρδ : ρ < δ := by have := min_le_left δ R; linarith
  have hρR : ρ < R := by have := min_le_right δ R; linarith
  rw [laurentCoeff_eq le_rfl hf ⟨by linarith, by linarith⟩ ⟨hρ0, hρR⟩ n, laurentCoeff]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -(m : ℤ) + -(n + 1) := ⟨(-(m : ℤ) + -(n + 1)).toNat, by
    rw [Int.toNat_of_nonneg (by omega)]⟩
  have hcongr : EqOn (fun z => f z / (z - z₀) ^ (n + 1)) (fun z => φ z * (z - z₀) ^ k)
      (sphere z₀ ρ) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hne : z - z₀ ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; linarith
    have hpow : (z - z₀) ^ k = ((z - z₀) ^ m)⁻¹ * ((z - z₀) ^ (n + 1))⁻¹ := by
      rw [← zpow_natCast, hk, zpow_add₀ hne, zpow_neg, zpow_neg, zpow_natCast]
    simp only
    rw [heq z ⟨by rw [hz]; exact hρ0, by rw [hz]; exact hρδ⟩, hpow]
    ring
  rw [circleIntegral.integral_congr hρ0.le hcongr,
    circleIntegral_eq_zero_of_differentiable_on_off_countable hρ0.le countable_empty, mul_zero]
  · exact ((hφ.mono (closedBall_subset_ball hρδ)).continuousOn).mul (by fun_prop)
  · intro z hz
    exact ((hφ.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hρδ.le hz.1))).mul
      (by fun_prop))

/-- Such an `f` does not have an essential singularity at `z₀`. -/
theorem not_essential_of_eq_div_pow {f φ : ℂ → ℂ} {z₀ : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 R)) (hδ : 0 < δ)
    (hφ : DifferentiableOn ℂ φ (ball z₀ δ)) {m : ℕ}
    (heq : ∀ z ∈ annulus z₀ 0 δ, f z = φ z / (z - z₀) ^ m) :
    ¬ IsEssentialSingularity f z₀ R := by
  refine fun h => h ((finite_Icc (-(m : ℤ)) (-1)).subset fun n hn => ?_)
  refine ⟨?_, by have := hn.1; omega⟩
  by_contra h'
  exact hn.2 (laurentCoeff_eq_zero_of_eq_div_pow hR hf hδ hφ heq (by omega))

/-- **Riemann's extension**: a function bounded in a punctured disk is `φ/(z − z₀)⁰`. -/
theorem exists_eq_div_pow_of_bdd {f : ℂ → ℂ} {z₀ : ℂ} {δ C : ℝ}
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 δ)) (hδ : 0 < δ)
    (hC : ∀ z ∈ annulus z₀ 0 δ, ‖f z‖ ≤ C) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ δ) ∧
      ∀ z ∈ annulus z₀ 0 δ, f z = φ z / (z - z₀) ^ 0 := by
  refine ⟨_, Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds z₀ hδ)
    (by rwa [ball_diff_eq_annulus]) ⟨C, ?_⟩, fun z hz => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [ball_diff_eq_annulus] at hz
    exact hC z hz
  · have hz0 : z ≠ z₀ := by
      intro h; have := hz.1; rw [h, sub_self, norm_zero] at this; exact lt_irrefl _ this
    rw [pow_zero, div_one, Function.update_of_ne hz0]

/-- If `1/(f − a)` is bounded in a punctured disk, then `f = φ/(z − z₀)ᵐ` near `z₀`. -/
theorem exists_eq_div_pow_of_inv_bdd {f : ℂ → ℂ} {z₀ a : ℂ} {δ C : ℝ}
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 δ)) (hδ : 0 < δ)
    (ha : ∀ z ∈ annulus z₀ 0 δ, f z ≠ a) (hC : ∀ z ∈ annulus z₀ 0 δ, ‖(f z - a)⁻¹‖ ≤ C) :
    ∃ ε > 0, ∃ m : ℕ, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ ε) ∧
      ∀ z ∈ annulus z₀ 0 ε, f z = φ z / (z - z₀) ^ m := by
  set u : ℂ → ℂ := fun z => (f z - a)⁻¹ with hu
  have hud : DifferentiableOn ℂ u (annulus z₀ 0 δ) :=
    (hf.sub_const a).inv fun z hz => sub_ne_zero.mpr (ha z hz)
  obtain ⟨φ, hφ, hφeq⟩ := exists_eq_div_pow_of_bdd hud hδ hC
  have hφu : ∀ z ∈ annulus z₀ 0 δ, φ z = u z := fun z hz => by
    rw [hφeq z hz, pow_zero, div_one]
  have han : AnalyticAt ℂ φ z₀ := hφ.analyticAt (ball_mem_nhds z₀ hδ)
  have hnz : ¬ ∀ᶠ z in 𝓝 z₀, φ z = 0 := by
    intro h
    obtain ⟨ε, hε, hεφ⟩ := Metric.eventually_nhds_iff_ball.mp h
    set z := z₀ + (min ε δ / 2 : ℝ) with hz
    have hmin : 0 < min ε δ := lt_min hε hδ
    have hzn : ‖z - z₀‖ = min ε δ / 2 := by
      rw [hz, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hzA : z ∈ annulus z₀ 0 δ :=
      ⟨by rw [hzn]; positivity, by rw [hzn]; linarith [min_le_right ε δ]⟩
    have := hεφ z (by rw [mem_ball, dist_eq_norm, hzn]; linarith [min_le_left ε δ])
    rw [hφu z hzA, hu] at this
    exact inv_ne_zero (sub_ne_zero.mpr (ha z hzA)) this
  obtain ⟨m, k, hk, hk0, hkeq⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ k z ∧ k z ≠ 0 ∧ φ z = (z - z₀) ^ m • k z ∧
      z ∈ ball z₀ δ :=
    hk.eventually_analyticAt.and ((hk.continuousAt.eventually_ne hk0).and
      (hkeq.and (ball_mem_nhds z₀ hδ)))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, m, fun z => a * (z - z₀) ^ m + (k z)⁻¹, ?_, fun z hz => ?_⟩
  · intro z hz
    obtain ⟨hkz, hk0z, -, -⟩ := hεP z hz
    exact ((by fun_prop : DifferentiableAt ℂ (fun z => a * (z - z₀) ^ m) z).add
      (hkz.differentiableAt.inv hk0z)).differentiableWithinAt
  · have hzb : z ∈ ball z₀ ε := by rw [mem_ball, dist_eq_norm]; exact hz.2
    obtain ⟨-, hk0z, heqz, hzδ⟩ := hεP z hzb
    have hzA : z ∈ annulus z₀ 0 δ := by
      rw [← ball_diff_eq_annulus] at hz ⊢; exact ⟨hzδ, hz.2⟩
    have hne : z - z₀ ≠ 0 := by
      have := hz.1; intro h; rw [h, norm_zero] at this; exact lt_irrefl _ this
    have hfa : f z - a ≠ 0 := sub_ne_zero.mpr (ha z hzA)
    rw [hφu z hzA, hu, smul_eq_mul] at heqz
    have hf' : f z = a + ((z - z₀) ^ m * k z)⁻¹ := by
      rw [← heqz, inv_inv]; ring
    rw [hf']
    field_simp

/-! ### Picard's theorem -/

/-- A function omitting two values in a punctured disk around `z₀` does not have an essential
singularity there. -/
theorem not_essential_of_omits {f : ℂ → ℂ} {z₀ a b : ℂ} {R r : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (annulus z₀ 0 R)) (hr : 0 < r) (hrR : r ≤ R) (hab : a ≠ b)
    (ha : ∀ z ∈ annulus z₀ 0 r, f z ≠ a) (hb : ∀ z ∈ annulus z₀ 0 r, f z ≠ b) :
    ¬ IsEssentialSingularity f z₀ R := by
  have hsub : ∀ {s : ℝ}, s ≤ r → annulus z₀ 0 s ⊆ annulus z₀ 0 R := fun hs z hz =>
    ⟨hz.1, by linarith [hz.2]⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  set G : ℂ → ℂ := fun z => (f z - a) / (b - a) with hG
  have hGd : DifferentiableOn ℂ G (annulus z₀ 0 r) :=
    ((hf.mono (hsub le_rfl)).sub_const a).div_const _
  have hG0 : ∀ z ∈ annulus z₀ 0 r, G z ≠ 0 := fun z hz =>
    div_ne_zero (sub_ne_zero.mpr (ha z hz)) hba
  have hG1 : ∀ z ∈ annulus z₀ 0 r, G z ≠ 1 := fun z hz h =>
    hb z hz (by rw [hG, div_eq_one_iff_eq hba] at h; linear_combination h)
  have hmin : ∀ {δ : ℝ}, 0 < δ → 0 < min δ r := fun hδ => lt_min hδ hr
  have hsubmin : ∀ δ : ℝ, annulus z₀ 0 (min δ r) ⊆ annulus z₀ 0 δ := fun δ z hz =>
    ⟨hz.1, hz.2.trans_le (min_le_left _ _)⟩
  rcases bdd_or_inv_bdd hr hGd hG0 hG1 with ⟨δ, hδ, hB⟩ | ⟨δ, hδ, hB⟩
  · obtain ⟨φ, hφ, heq⟩ := exists_eq_div_pow_of_bdd (hf.mono (hsub (min_le_right δ r)))
      (hmin hδ) (C := ‖a‖ + ‖b - a‖ * chainBound 1) fun z hz => by
        have e : f z = a + (b - a) * G z := by rw [hG]; field_simp; ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
        gcongr
        exact hB z (hsubmin δ hz)
    exact not_essential_of_eq_div_pow hR hf (hmin hδ) hφ heq
  · obtain ⟨ε, hε, m, φ, hφ, heq⟩ := exists_eq_div_pow_of_inv_bdd
      (hf.mono (hsub (min_le_right δ r))) (hmin hδ)
      (fun z hz => ha z ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩)
      (C := chainBound 1 * ‖(b - a)⁻¹‖) fun z hz => by
        have e : (f z - a)⁻¹ = (G z)⁻¹ * (b - a)⁻¹ := by rw [hG, inv_div]; field_simp
        rw [e, norm_mul]
        gcongr
        exact hB z (hsubmin δ hz)
    exact not_essential_of_eq_div_pow hR hf hε hφ heq

/-- **Picard's (great) theorem**, DLMF §1.10(iii): in any neighbourhood of an isolated
essential singularity, `f` assumes every complex value, except possibly one. -/
theorem dlmf_1_10_iii_picard {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hf : IsIsolatedSingularity f z₀ R)
    (he : IsEssentialSingularity f z₀ R) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (f '' annulus z₀ 0 r)ᶜ.Subsingleton := by
  intro a ha b hb
  by_contra hab
  exact not_essential_of_omits hf.1 hf.2.1 hr hrR hab (fun z hz h => ha ⟨z, hz, h⟩)
    (fun z hz h => hb ⟨z, hz, h⟩) he

/-- **Picard's (great) theorem**, DLMF §1.10(iii), as stated there: in any neighbourhood of an
isolated essential singularity, `f` assumes every complex value, except possibly one,
infinitely many times. -/
theorem dlmf_1_10_iii_picard_infinite {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : IsIsolatedSingularity f z₀ R) (he : IsEssentialSingularity f z₀ R) {r : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    {w : ℂ | {z | z ∈ annulus z₀ 0 r ∧ f z = w}.Finite}.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hT := Set.Finite.union ha hb
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ z ∈ {z | z ∈ annulus z₀ 0 r ∧ f z = a} ∪ {z | z ∈ annulus z₀ 0 r ∧ f z = b},
        ε < ‖z - z₀‖) ∧ ε < r ∧ 0 < ε := by
    refine ((hT.eventually_all).mpr fun z hz => ?_).and
      (((eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
    have : 0 < ‖z - z₀‖ := by rcases hz with hz | hz <;> exact hz.1.1
    exact (eventually_lt_nhds this).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hεT, hεr, hε⟩ := hev.exists
  have homit : ∀ w ∈ ({a, b} : Set ℂ), ∀ z ∈ annulus z₀ 0 ε, f z ≠ w := by
    intro w hw z hz h
    have hzr : z ∈ annulus z₀ 0 r := ⟨hz.1, hz.2.trans hεr⟩
    have := hεT z (by
      rcases hw with rfl | rfl
      · exact Or.inl ⟨hzr, h⟩
      · exact Or.inr ⟨hzr, h⟩)
    linarith [hz.2]
  exact not_essential_of_omits hf.1 hf.2.1 hε (hεr.le.trans hrR) hab
    (homit a (by simp)) (homit b (by simp)) he

/-- **Picard's little theorem**: an entire function omitting two values is constant. -/
theorem little_picard {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℂ} (hab : a ≠ b)
    (ha : ∀ z, f z ≠ a) (hb : ∀ z, f z ≠ b) (z w : ℂ) : f z = f w := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  set G : ℂ → ℂ := fun z => (f z - a) / (b - a) with hG
  have hGd : Differentiable ℂ G := (hf.sub_const a).div_const _
  have hbdd : ∀ z, ‖G z‖ ≤ schottkyBound ‖G 0‖ := fun z =>
    schottky (c := 0) (R := 2 * ‖z‖ + 2) (by positivity) hGd.differentiableOn
      (fun y _ => div_ne_zero (sub_ne_zero.mpr (ha y)) hba)
      (fun y _ h => hb y (by rw [hG, div_eq_one_iff_eq hba] at h; linear_combination h)) le_rfl
      (by rw [mem_closedBall, dist_zero_right]; linarith)
  have := Differentiable.apply_eq_apply_of_bounded hGd
    (isBounded_closedBall (x := (0 : ℂ)) (r := schottkyBound ‖G 0‖) |>.subset
      (range_subset_iff.mpr fun z => by rw [mem_closedBall, dist_zero_right]; exact hbdd z)) z w
  rw [hG, div_left_inj' hba, sub_left_inj] at this
  exact this

/-! ### Infinitely many poles: an essential singularity at `∞` -/

/-- DLMF §1.10(iii): if a meromorphic function has infinitely many poles, the point at infinity
is called an essential singularity (it is the limit point of the poles; see
`exists_pole_norm_gt`). -/
def IsEssentialSingularityAtInftyOfPoles (f : ℂ → ℂ) : Prop :=
  IsMeromorphicDLMF f ∧ {z | ¬ AnalyticAt ℂ f z}.Infinite

/-- The poles of a meromorphic function are isolated. -/
theorem IsMeromorphicDLMF.exists_ball (hf : IsMeromorphicDLMF f) (x : ℂ) :
    ∃ ε > 0, ∀ y ∈ ball x ε, y ≠ x → AnalyticAt ℂ f y := by
  rcases hf x with h | ⟨R, hR, hd, -⟩
  · obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.mp h.eventually_analyticAt
    exact ⟨ε, hε, fun y hy _ => hεP y hy⟩
  · refine ⟨R, hR, fun y hy hyx => hd.analyticAt ((isOpen_annulus x 0 R).mem_nhds ?_)⟩
    rw [mem_ball, dist_eq_norm] at hy
    exact ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hyx), hy⟩

/-- A meromorphic function has only finitely many poles in each disk. -/
theorem IsMeromorphicDLMF.finite_poles (hf : IsMeromorphicDLMF f) (R : ℝ) :
    ({z | ¬ AnalyticAt ℂ f z} ∩ closedBall 0 R).Finite := by
  choose ε hε hεP using hf.exists_ball
  obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) R).elim_nhds_subcover
    (fun x => ball x (ε x)) fun x _ => ball_mem_nhds x (hε x)
  refine t.finite_toSet.subset fun z ⟨hz, hzK⟩ => ?_
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (ht hzK)
  by_cases h : z = x
  · rw [h]; exact hx
  · exact absurd (hεP x z hzx h) hz

/-- The poles of a meromorphic function with infinitely many poles accumulate at `∞`. -/
theorem exists_pole_norm_gt (hf : IsEssentialSingularityAtInftyOfPoles f) (R : ℝ) :
    ∃ z, R < ‖z‖ ∧ ¬ AnalyticAt ℂ f z := by
  by_contra h
  push Not at h
  refine hf.2 ((hf.1.finite_poles R).subset fun z hz => ⟨hz, ?_⟩)
  rw [mem_closedBall, dist_zero_right]
  by_contra h'
  exact hz (h z (not_le.mp h'))

/-- In that case `∞` is not an isolated singularity: `f(1/w)` is not holomorphic in any
punctured disk around `w = 0`. -/
theorem not_differentiableOn_inv_of_poles (hf : IsEssentialSingularityAtInftyOfPoles f) {R : ℝ}
    (hR : 0 < R) : ¬ DifferentiableOn ℂ (fun w => f w⁻¹) (annulus 0 0 R) := by
  intro hd
  obtain ⟨z, hz, hza⟩ := exists_pole_norm_gt hf R⁻¹
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact absurd hz (not_lt.mpr (inv_pos.mpr hR).le)
  set U := {y : ℂ | R⁻¹ < ‖y‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hmaps : MapsTo (fun y : ℂ => y⁻¹) U (annulus 0 0 R) := fun y hy => by
    have hy0 : 0 < ‖y‖ := (inv_pos.mpr hR).trans hy
    refine ⟨by rw [sub_zero, norm_inv]; positivity, ?_⟩
    rw [sub_zero, norm_inv]
    exact (inv_lt_comm₀ hy0 hR).mpr hy
  have hdU : DifferentiableOn ℂ f U := by
    refine (hd.comp (differentiableOn_inv.mono fun y hy => ?_) hmaps).congr fun y _ => ?_
    · exact norm_pos_iff.mp ((inv_pos.mpr hR).trans hy)
    · simp
  exact hza (hdU.analyticAt (hU.mem_nhds hz))

end Azurite.DLMF
