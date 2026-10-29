/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13
import Mathlib.Analysis.Complex.Liouville

/-!
# DLMF §1.13(ii): Equations with a Parameter

Formalization of <https://dlmf.nist.gov/1.13#ii>: for
`∂²w/∂z² + f(u, z) ∂w/∂z + g(u, z) w = 0` (1.13.7) with `u ∈ U`, `z ∈ D`, `f` and `g` jointly
continuous and analytic in `u` for fixed `z`, if `w` and `∂w/∂z` are analytic in `u` at one
`z₀ ∈ D`, then `w`, `∂w/∂z` and `∂²w/∂z²` are analytic in `u` at every `z ∈ D` (`dlmf_1_13_ii`).
`D` need only be open and connected. DLMF's further assumption that `f`, `g` are analytic in `z`
for fixed `u` is not used, beyond the solutions `w(u, ·)` being given.

**Method** (`exists_hasDerivAt_param`). With `Y = (w, ∂w/∂z)` and the system matrix `odeC`, the
difference quotients `Q_h = (Y(u₀ + h, ·) − Y(u₀, ·))/h` solve a perturbed linear system
(`odeC_quot`, `odeC_quot_sub`). Cauchy estimates in `u`, uniform over a chain from `z₀` to `z`
(`param_bounds`, `param_quot_bounds`), together with Gronwall along the chain
(`norm_le_along_chain_gronwall`), bound `Q_h` and give `‖Q_h(z) − Q_k(z)‖ ≤ ψ(h) + ψ(k)` with
`ψ → 0`. Completeness (`exists_tendsto_of_dist_le`) then gives the derivative in `u`.
-/

open Filter Topology Set Metric Complex

namespace Azurite.DLMF

/-! ### Constant-coefficient form of the system -/

/-- `(Y₂, −(b Y₁ + a Y₂))`: the system matrix of (1.13.1) at a point,
`odeA f g z = odeC (f z) (g z)`. -/
def odeC (a b : ℂ) (Y : ℂ × ℂ) : ℂ × ℂ := (Y.2, -(b * Y.1 + a * Y.2))

theorem norm_odeC_le {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (Y : ℂ × ℂ) :
    ‖odeC a b Y‖ ≤ (1 + 2 * M) * ‖Y‖ :=
  norm_odeA_le (f := fun _ => a) (g := fun _ => b) (z := 0) ha hb Y

theorem norm_zero_neg_le (α β : ℂ) (Y : ℂ × ℂ) :
    ‖((0 : ℂ), -(β * Y.1 + α * Y.2))‖ ≤ (‖α‖ + ‖β‖) * ‖Y‖ := by
  have h1 := norm_fst_le Y
  have h2 := norm_snd_le Y
  rw [norm_prod_le_iff]
  refine ⟨by simp; positivity, ?_⟩
  simp only [norm_neg]
  calc ‖β * Y.1 + α * Y.2‖ ≤ ‖β‖ * ‖Y.1‖ + ‖α‖ * ‖Y.2‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
    _ ≤ ‖β‖ * ‖Y‖ + ‖α‖ * ‖Y‖ := by gcongr
    _ = _ := by ring

theorem norm_odeC_sub_le (a b a' b' : ℂ) (Y : ℂ × ℂ) :
    ‖odeC a b Y - odeC a' b' Y‖ ≤ (‖a - a'‖ + ‖b - b'‖) * ‖Y‖ := by
  have : odeC a b Y - odeC a' b' Y = ((0 : ℂ), -((b - b') * Y.1 + (a - a') * Y.2)) := by
    ext <;> simp [odeC]
    ring
  rw [this]
  exact norm_zero_neg_le _ _ Y

theorem norm_smul_odeC_sub_le (k a0 b0 ak bk : ℂ) (Y : ℂ × ℂ) :
    ‖k⁻¹ • (odeC ak bk Y - odeC a0 b0 Y)‖ ≤ (‖k⁻¹ * (ak - a0)‖ + ‖k⁻¹ * (bk - b0)‖) * ‖Y‖ := by
  have : k⁻¹ • (odeC ak bk Y - odeC a0 b0 Y) =
      ((0 : ℂ), -((k⁻¹ * (bk - b0)) * Y.1 + (k⁻¹ * (ak - a0)) * Y.2)) := by
    ext <;> simp [odeC]
    ring
  rw [this]
  exact norm_zero_neg_le _ _ Y

theorem norm_smul_odeC_sub_sub_le (h k a0 b0 ah bh ak bk : ℂ) (Y : ℂ × ℂ) :
    ‖h⁻¹ • (odeC ah bh Y - odeC a0 b0 Y) - k⁻¹ • (odeC ak bk Y - odeC a0 b0 Y)‖ ≤
      (‖h⁻¹ * (ah - a0) - k⁻¹ * (ak - a0)‖ + ‖h⁻¹ * (bh - b0) - k⁻¹ * (bk - b0)‖) * ‖Y‖ := by
  have : h⁻¹ • (odeC ah bh Y - odeC a0 b0 Y) - k⁻¹ • (odeC ak bk Y - odeC a0 b0 Y) =
      ((0 : ℂ), -((h⁻¹ * (bh - b0) - k⁻¹ * (bk - b0)) * Y.1 +
        (h⁻¹ * (ah - a0) - k⁻¹ * (ak - a0)) * Y.2)) := by
    ext <;> simp [odeC]
    ring
  rw [this]
  exact norm_zero_neg_le _ _ Y

/-- The difference-quotient equation: `k⁻¹(A_k Y_k − A₀ Y₀) = A_k Q_k + k⁻¹(A_k − A₀) Y₀`. -/
theorem odeC_quot (k a0 b0 ak bk : ℂ) (Y0 Yk : ℂ × ℂ) :
    k⁻¹ • (odeC ak bk Yk - odeC a0 b0 Y0) =
      odeC ak bk (k⁻¹ • (Yk - Y0)) + k⁻¹ • (odeC ak bk Y0 - odeC a0 b0 Y0) := by
  ext <;> simp [odeC]
  ring

/-- The equation for the difference of two difference quotients. -/
theorem odeC_quot_sub (h k a0 b0 ah bh ak bk : ℂ) (Y0 Yh Yk : ℂ × ℂ) :
    h⁻¹ • (odeC ah bh Yh - odeC a0 b0 Y0) - k⁻¹ • (odeC ak bk Yk - odeC a0 b0 Y0) =
      odeC ah bh (h⁻¹ • (Yh - Y0) - k⁻¹ • (Yk - Y0)) +
        (odeC ah bh (k⁻¹ • (Yk - Y0)) - odeC ak bk (k⁻¹ • (Yk - Y0))) +
        (h⁻¹ • (odeC ah bh Y0 - odeC a0 b0 Y0) - k⁻¹ • (odeC ak bk Y0 - odeC a0 b0 Y0)) := by
  ext <;> simp [odeC]
  ring

/-! ### Cauchy estimates in the parameter -/

/-- Lipschitz and second-order Taylor bounds for an analytic function from a bound on a disk. -/
theorem param_bounds {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ U)
    {u₀ : ℂ} {r M : ℝ} (hr : 0 < r) (hball : closedBall u₀ r ⊆ U)
    (hM : ∀ u ∈ closedBall u₀ r, ‖φ u‖ ≤ M) :
    (∀ a ∈ closedBall u₀ (r / 2), ∀ b ∈ closedBall u₀ (r / 2),
      ‖φ b - φ a‖ ≤ 2 * M / r * ‖b - a‖) ∧
    ∀ h : ℂ, ‖h‖ ≤ r / 4 → ‖φ (u₀ + h) - φ u₀ - h * deriv φ u₀‖ ≤ 8 * M / r ^ 2 * ‖h‖ ^ 2 := by
  have hdiff : ∀ x ∈ closedBall u₀ r, DifferentiableAt ℂ φ x := fun x hx =>
    hφ.differentiableAt (hU.mem_nhds (hball hx))
  have hsub : ∀ {a : ℂ} {ρ σ : ℝ}, a ∈ closedBall u₀ σ → ρ + σ ≤ r →
      closedBall a ρ ⊆ closedBall u₀ r := fun {a ρ σ} ha hρσ x hx => by
    rw [mem_closedBall] at ha hx ⊢
    linarith [dist_triangle x a u₀]
  have hd1 : ∀ a ∈ closedBall u₀ (r / 2), ‖deriv φ a‖ ≤ 2 * M / r := fun a ha => by
    have hρ : (0 : ℝ) < r / 2 := by positivity
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      (DifferentiableOn.diffContOnCl (by
        rw [closure_ball a hρ.ne']
        exact hφ.mono ((hsub ha (by linarith)).trans hball)))
      (fun x hx => hM x (hsub ha (le_of_eq (by ring)) (sphere_subset_closedBall hx)))
    calc ‖deriv φ a‖ ≤ M / (r / 2) := this
      _ = 2 * M / r := by field_simp
  refine ⟨fun a ha b hb => (convex_closedBall u₀ (r / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => hdiff x (closedBall_subset_closedBall (by linarith) hx)) hd1 ha hb, ?_⟩
  have hd2 : ∀ a ∈ closedBall u₀ (r / 4), ‖deriv (deriv φ) a‖ ≤ 8 * M / r ^ 2 := fun a ha => by
    have hρ : (0 : ℝ) < r / 4 := by positivity
    have hsub2 : closedBall a (r / 4) ⊆ closedBall u₀ (r / 2) := fun x hx => by
      rw [mem_closedBall] at ha hx ⊢
      linarith [dist_triangle x a u₀]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      (DifferentiableOn.diffContOnCl (by
        rw [closure_ball a hρ.ne']
        exact (hφ.deriv hU).mono (hsub2.trans ((closedBall_subset_closedBall
          (by linarith)).trans hball))))
      (fun x hx => hd1 x (hsub2 (sphere_subset_closedBall hx)))
    calc ‖deriv (deriv φ) a‖ ≤ 2 * M / r / (r / 4) := this
      _ = 8 * M / r ^ 2 := by field_simp; ring
  have hdd : ∀ x ∈ closedBall u₀ (r / 4), DifferentiableAt ℂ (deriv φ) x := fun x hx =>
    (hφ.deriv hU).differentiableAt (hU.mem_nhds (hball (closedBall_subset_closedBall
      (by linarith) hx)))
  intro h hh
  have hs : closedBall u₀ ‖h‖ ⊆ closedBall u₀ (r / 4) := closedBall_subset_closedBall hh
  have hlip : ∀ x ∈ closedBall u₀ ‖h‖, ‖deriv φ x - deriv φ u₀‖ ≤ 8 * M / r ^ 2 * ‖h‖ :=
    fun x hx => by
      have := (convex_closedBall u₀ (r / 4)).norm_image_sub_le_of_norm_deriv_le hdd hd2
        (mem_closedBall_self (by linarith)) (hs hx)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM u₀ (mem_closedBall_self hr.le))
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← dist_eq_norm]
      exact hx
  have hg : ∀ x ∈ closedBall u₀ ‖h‖, HasDerivWithinAt (fun v => φ v - v * deriv φ u₀)
      (deriv φ x - deriv φ u₀) (closedBall u₀ ‖h‖) x := fun x hx => by
    have := ((hdiff x (closedBall_subset_closedBall (by linarith) (hs hx))).hasDerivAt.sub
      ((hasDerivAt_id x).mul_const (deriv φ u₀)))
    exact (this.congr_deriv (by simp)).hasDerivWithinAt
  have := (convex_closedBall u₀ ‖h‖).norm_image_sub_le_of_norm_hasDerivWithin_le hg hlip
    (mem_closedBall_self (norm_nonneg h))
    (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  calc ‖φ (u₀ + h) - φ u₀ - h * deriv φ u₀‖
      = ‖(φ (u₀ + h) - (u₀ + h) * deriv φ u₀) - (φ u₀ - u₀ * deriv φ u₀)‖ := by ring_nf
    _ ≤ 8 * M / r ^ 2 * ‖h‖ * ‖u₀ + h - u₀‖ := this
    _ = 8 * M / r ^ 2 * ‖h‖ ^ 2 := by rw [add_sub_cancel_left]; ring

/-- Bounds on difference quotients `Δ_h φ = (φ(u₀ + h) − φ(u₀))/h` from `param_bounds`. -/
theorem param_quot_bounds {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) {u₀ : ℂ} {r M : ℝ} (hr : 0 < r)
    (hball : closedBall u₀ r ⊆ U) (hM : ∀ u ∈ closedBall u₀ r, ‖φ u‖ ≤ M) {h k : ℂ}
    (hh0 : h ≠ 0) (hk0 : k ≠ 0) (hh : ‖h‖ ≤ r / 4) (hk : ‖k‖ ≤ r / 4) :
    ‖h⁻¹ * (φ (u₀ + h) - φ u₀)‖ ≤ 2 * M / r ∧
    ‖h⁻¹ * (φ (u₀ + h) - φ u₀) - k⁻¹ * (φ (u₀ + k) - φ u₀)‖ ≤
      8 * M / r ^ 2 * (‖h‖ + ‖k‖) ∧
    ‖φ (u₀ + h) - φ (u₀ + k)‖ ≤ 2 * M / r * ‖h - k‖ := by
  obtain ⟨hlip, htay⟩ := param_bounds hU hφ hr hball hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM u₀ (mem_closedBall_self hr.le))
  have mem : ∀ t : ℂ, ‖t‖ ≤ r / 4 → u₀ + t ∈ closedBall u₀ (r / 2) := fun t ht => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    linarith
  have hquot : ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ r / 4 →
      ‖t⁻¹ * (φ (u₀ + t) - φ u₀) - deriv φ u₀‖ ≤ 8 * M / r ^ 2 * ‖t‖ := fun t ht0 ht => by
    have hn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    rw [show t⁻¹ * (φ (u₀ + t) - φ u₀) - deriv φ u₀ =
        t⁻¹ * (φ (u₀ + t) - φ u₀ - t * deriv φ u₀) by field_simp, norm_mul, norm_inv]
    rw [inv_mul_le_iff₀ hn]
    calc _ ≤ 8 * M / r ^ 2 * ‖t‖ ^ 2 := htay t ht
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · have := hlip u₀ (mem_closedBall_self (by positivity)) (u₀ + h) (mem h hh)
    rw [add_sub_cancel_left] at this
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hh0)]
    linarith
  · calc _ ≤ ‖h⁻¹ * (φ (u₀ + h) - φ u₀) - deriv φ u₀‖ +
          ‖k⁻¹ * (φ (u₀ + k) - φ u₀) - deriv φ u₀‖ := by
          rw [← norm_neg (k⁻¹ * _ - _)]
          convert norm_add_le _ _ using 2
          ring
      _ ≤ 8 * M / r ^ 2 * ‖h‖ + 8 * M / r ^ 2 * ‖k‖ :=
          add_le_add (hquot h hh0 hh) (hquot k hk0 hk)
      _ = _ := by ring
  · have := hlip (u₀ + k) (mem k hk) (u₀ + h) (mem h hh)
    rwa [add_sub_add_left_eq_sub] at this

/-- A function whose values at `h` and `k` differ by at most `ψ h + ψ k`, with `ψ → 0`, has a
limit (completeness). -/
theorem exists_tendsto_of_dist_le {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {l : Filter α} [l.NeBot] {F : α → E} {ψ : α → ℝ} (hψ : Tendsto ψ l (𝓝 0)) {S : Set α}
    (hS : S ∈ l) (hF : ∀ h ∈ S, ∀ k ∈ S, ‖F h - F k‖ ≤ ψ h + ψ k) :
    ∃ L, Tendsto F l (𝓝 L) := by
  have hc : Cauchy (map F l) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨F '' (S ∩ {h | ψ h < ε / 2}), ?_, ?_⟩⟩
    · exact mem_map.2 (mem_of_superset (inter_mem hS
        (hψ.eventually (gt_mem_nhds (by positivity)))) (subset_preimage_image _ _))
    · rintro _ ⟨h, ⟨hS', hh⟩, rfl⟩ _ ⟨k, ⟨hk', hk⟩, rfl⟩
      have hh' : ψ h < ε / 2 := hh
      have hk'' : ψ k < ε / 2 := hk
      rw [dist_eq_norm]
      linarith [hF h hS' k hk']
  obtain ⟨L, hL⟩ := CompleteSpace.complete hc
  exact ⟨L, hL⟩

/-! ### Analytic dependence on the parameter -/

section Parameter

variable {U D : Set ℂ} {f g w : ℂ → ℂ → ℂ}

/-- The core of §1.13(ii): `u ↦ (w(u, z), ∂w/∂z(u, z))` is complex differentiable at every
`u₀ ∈ U`. The difference quotients in `u` satisfy a perturbed linear system; Gronwall along a
chain from `z₀` to `z`, with Cauchy estimates in `u` uniform on the chain, shows that they are
Cauchy as the increment tends to `0`. -/
theorem exists_hasDerivAt_param (hU : IsOpen U) (hDo : IsOpen D) (hDc : IsConnected D)
    (hfc : ContinuousOn (Function.uncurry f) (U ×ˢ D))
    (hgc : ContinuousOn (Function.uncurry g) (U ×ˢ D))
    (hfu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => f u z) U)
    (hgu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => g u z) U)
    (hw : ∀ u ∈ U, IsODESolution D (f u) (g u) (w u)) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h0 : DifferentiableOn ℂ (fun u => w u z₀) U)
    (h1 : DifferentiableOn ℂ (fun u => deriv (w u) z₀) U) {u₀ : ℂ} (hu₀ : u₀ ∈ U) {z : ℂ}
    (hz : z ∈ D) : ∃ L, HasDerivAt (fun u => (w u z, deriv (w u) z)) L u₀ := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℂ → ℂ → ℂ × ℂ, Y = fun u ζ => (w u ζ, deriv (w u) ζ) := ⟨_, rfl⟩
  suffices H : ∃ L, HasDerivAt (fun u => Y u z) L u₀ by simpa [hYdef] using H
  have hY : ∀ u ∈ U, ∀ ζ ∈ D, HasDerivAt (Y u) (odeC (f u ζ) (g u ζ) (Y u ζ)) ζ :=
    fun u hu ζ hζ => by
      obtain ⟨a, b⟩ := (hw u hu).hasDerivAt hDo hζ
      rw [hYdef]
      refine (a.prodMk b).congr_deriv ?_
      simp only [odeC, Prod.mk.injEq, true_and]
      ring
  -- a chain from `z₀` to `z`
  obtain ⟨v, m, hv0, hvm, hch⟩ := exists_chain_of_polygonallyJoined
    (((dlmf_1_9_ii_domain hDo).mp hDc).2 z₀ hz₀ z hz)
  have hKD := chainSet_subset hch
  have hK := isChain_chainSet v m
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = ∑ j ∈ Finset.range m, ‖v (j + 1) - v j‖ := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := hℓdef ▸ Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hℓ : ∀ i < m, ‖v (i + 1) - v i‖ ≤ ℓ := fun i hi => hℓdef ▸ norm_side_le_sum v hi
  -- a disk in the parameter
  obtain ⟨r₀, hr₀, hballU⟩ := Metric.isOpen_iff.mp hU u₀ hu₀
  obtain ⟨r, hrdef⟩ : ∃ r, r = r₀ / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; positivity
  have hball : closedBall u₀ r ⊆ U := (closedBall_subset_ball (by linarith)).trans hballU
  -- bounds for `f`, `g` and `Y(u₀, ·)`
  have hC : IsCompact (closedBall u₀ r ×ˢ chainSet v m) :=
    (isCompact_closedBall _ _).prod (isCompact_chainSet v m)
  have hCU : closedBall u₀ r ×ˢ chainSet v m ⊆ U ×ˢ D := prod_mono hball hKD
  obtain ⟨Mf, hMf⟩ := hC.exists_bound_of_continuousOn (hfc.mono hCU)
  obtain ⟨Mg, hMg⟩ := hC.exists_bound_of_continuousOn (hgc.mono hCU)
  obtain ⟨M, hMdef⟩ : ∃ M, M = max (max Mf Mg) 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ le_max_right _ _
  have hfM : ∀ u ∈ closedBall u₀ r, ∀ ζ ∈ chainSet v m, ‖f u ζ‖ ≤ M := fun u hu ζ hζ =>
    (hMf (u, ζ) ⟨hu, hζ⟩).trans (hMdef ▸ (le_max_left _ _).trans (le_max_left _ _))
  have hgM : ∀ u ∈ closedBall u₀ r, ∀ ζ ∈ chainSet v m, ‖g u ζ‖ ≤ M := fun u hu ζ hζ =>
    (hMg (u, ζ) ⟨hu, hζ⟩).trans (hMdef ▸ (le_max_right _ _).trans (le_max_left _ _))
  have hYc : ContinuousOn (Y u₀) D := fun ζ hζ =>
    (hY u₀ hu₀ ζ hζ).continuousAt.continuousWithinAt
  obtain ⟨BY₀, hBY₀⟩ := (isCompact_chainSet v m).exists_bound_of_continuousOn (hYc.mono hKD)
  obtain ⟨BY, hBYdef⟩ : ∃ BY, BY = max BY₀ 0 := ⟨_, rfl⟩
  have hBY0 : 0 ≤ BY := hBYdef ▸ le_max_right _ _
  have hBY : ∀ ζ ∈ chainSet v m, ‖Y u₀ ζ‖ ≤ BY := fun ζ hζ =>
    (hBY₀ ζ hζ).trans (hBYdef ▸ le_max_left _ _)
  -- the initial data
  obtain ⟨c', hc⟩ : ∃ c', HasDerivAt (fun u => Y u z₀) c' u₀ := by
    rw [hYdef]
    exact ⟨_, ((h0.differentiableAt (hU.mem_nhds hu₀)).hasDerivAt).prodMk
      ((h1.differentiableAt (hU.mem_nhds hu₀)).hasDerivAt)⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hc
  -- difference quotients
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ → ℂ × ℂ, Q = fun t ζ => t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ) :=
    ⟨_, rfl⟩
  set S : Set ℂ := {t | t ≠ 0 ∧ ‖t‖ ≤ r / 4 ∧ ‖Q t z₀ - c'‖ ≤ 1} with hSdef
  have hS : S ∈ 𝓝[≠] (0 : ℂ) := by
    have h3 := hslope.eventually (closedBall_mem_nhds c' one_pos)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (closedBall_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < r / 4)), h3] with t ha hb hc
    refine ⟨ha, mem_closedBall_zero_iff.mp hb, ?_⟩
    rw [hQ]
    simpa [mem_closedBall, dist_eq_norm] using hc
  have hmem : ∀ t ∈ S, u₀ + t ∈ closedBall u₀ r := fun t ht => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    linarith [ht.2.1]
  have hQd : ∀ t ∈ S, ∀ ζ ∈ D, HasDerivAt (Q t) (t⁻¹ • (odeC (f (u₀ + t) ζ) (g (u₀ + t) ζ)
      (Y (u₀ + t) ζ) - odeC (f u₀ ζ) (g u₀ ζ) (Y u₀ ζ))) ζ := fun t ht ζ hζ => by
    rw [hQ]
    exact ((hY _ (hball (hmem t ht)) ζ hζ).sub (hY u₀ hu₀ ζ hζ)).const_smul t⁻¹
  have hPf : ∀ ζ ∈ chainSet v m, ∀ s ∈ S, ∀ t ∈ S,
      ‖s⁻¹ * (f (u₀ + s) ζ - f u₀ ζ)‖ ≤ 2 * M / r ∧
      ‖s⁻¹ * (f (u₀ + s) ζ - f u₀ ζ) - t⁻¹ * (f (u₀ + t) ζ - f u₀ ζ)‖ ≤
        8 * M / r ^ 2 * (‖s‖ + ‖t‖) ∧
      ‖f (u₀ + s) ζ - f (u₀ + t) ζ‖ ≤ 2 * M / r * ‖s - t‖ := fun ζ hζ s hs t ht =>
    param_quot_bounds hU (hfu ζ (hKD hζ)) hr hball (fun u hu => hfM u hu ζ hζ) hs.1 ht.1
      hs.2.1 ht.2.1
  have hPg : ∀ ζ ∈ chainSet v m, ∀ s ∈ S, ∀ t ∈ S,
      ‖s⁻¹ * (g (u₀ + s) ζ - g u₀ ζ)‖ ≤ 2 * M / r ∧
      ‖s⁻¹ * (g (u₀ + s) ζ - g u₀ ζ) - t⁻¹ * (g (u₀ + t) ζ - g u₀ ζ)‖ ≤
        8 * M / r ^ 2 * (‖s‖ + ‖t‖) ∧
      ‖g (u₀ + s) ζ - g (u₀ + t) ζ‖ ≤ 2 * M / r * ‖s - t‖ := fun ζ hζ s hs t ht =>
    param_quot_bounds hU (hgu ζ (hKD hζ)) hr hball (fun u hu => hgM u hu ζ hζ) hs.1 ht.1
      hs.2.1 ht.2.1
  have hMr : 0 ≤ 2 * M / r := by positivity
  have hMr2 : 0 ≤ 8 * M / r ^ 2 := by positivity
  have hKc : 0 ≤ ℓ * (1 + 2 * M) := mul_nonneg hℓ0 (by linarith)
  -- a uniform bound on the difference quotients along the chain
  obtain ⟨BQ, hBQdef⟩ : ∃ BQ, BQ = Real.exp (ℓ * (1 + 2 * M) * m) *
      ((‖c'‖ + 1) + m * (ℓ * (4 * M / r * BY))) := ⟨_, rfl⟩
  have hBQ0 : 0 ≤ BQ := by
    rw [hBQdef]
    exact mul_nonneg (Real.exp_pos _).le (by positivity)
  have hQb : ∀ t ∈ S, ∀ i < m, ∀ τ ∈ Icc (i : ℝ) (i + 1), ‖Q t (polySeg v i τ)‖ ≤ BQ := by
    intro t ht
    have := norm_le_along_chain_gronwall hch hℓ (hQd t ht) (K := ℓ * (1 + 2 * M))
      (ε := ℓ * (4 * M / r * BY)) (δ := ‖c'‖ + 1) hKc (by positivity) ?_ ?_
    · rw [hBQdef]
      exact this.1
    · rw [hv0]
      linarith [norm_sub_norm_le (Q t z₀) c', ht.2.2]
    · intro i hi τ hτ
      have hζ := polySeg_mem hK hi hτ
      rw [odeC_quot]
      have e1 := norm_odeC_le (hfM _ (hmem t ht) _ hζ) (hgM _ (hmem t ht) _ hζ)
        (t⁻¹ • (Y (u₀ + t) (polySeg v i τ) - Y u₀ (polySeg v i τ)))
      have e2 := norm_smul_odeC_sub_le t (f u₀ (polySeg v i τ)) (g u₀ (polySeg v i τ))
        (f (u₀ + t) (polySeg v i τ)) (g (u₀ + t) (polySeg v i τ)) (Y u₀ (polySeg v i τ))
      have pf := (hPf _ hζ t ht t ht).1
      have pg := (hPg _ hζ t ht t ht).1
      have hy := hBY _ hζ
      have hQe : Q t (polySeg v i τ) =
          t⁻¹ • (Y (u₀ + t) (polySeg v i τ) - Y u₀ (polySeg v i τ)) := by rw [hQ]
      rw [hQe]
      calc ℓ * ‖_ + _‖
          ≤ ℓ * ((1 + 2 * M) * ‖t⁻¹ • (Y (u₀ + t) (polySeg v i τ) - Y u₀ (polySeg v i τ))‖ +
            (2 * M / r + 2 * M / r) * BY) :=
            mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add e1
              (e2.trans (mul_le_mul (add_le_add pf pg) hy (norm_nonneg _) (by positivity)))))
              hℓ0
        _ = _ := by ring
  -- the Cauchy estimate for the difference quotients
  obtain ⟨A, hAdef⟩ : ∃ A, A = ℓ * (4 * M / r * BQ + 16 * M / r ^ 2 * BY) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  set ψ : ℂ → ℝ := fun t => Real.exp (ℓ * (1 + 2 * M) * m) * (‖Q t z₀ - c'‖ + m * A * ‖t‖)
    with hψdef
  have hcl : ∀ s ∈ S, ∀ t ∈ S, ‖Q s z - Q t z‖ ≤ ψ s + ψ t := by
    intro s hs t ht
    have hd : ∀ ζ ∈ D, HasDerivAt (fun ζ => Q s ζ - Q t ζ)
        (s⁻¹ • (odeC (f (u₀ + s) ζ) (g (u₀ + s) ζ) (Y (u₀ + s) ζ) -
          odeC (f u₀ ζ) (g u₀ ζ) (Y u₀ ζ)) -
        t⁻¹ • (odeC (f (u₀ + t) ζ) (g (u₀ + t) ζ) (Y (u₀ + t) ζ) -
          odeC (f u₀ ζ) (g u₀ ζ) (Y u₀ ζ))) ζ := fun ζ hζ =>
      (hQd s hs ζ hζ).sub (hQd t ht ζ hζ)
    have hε0 : 0 ≤ ℓ * (4 * M / r * ‖s - t‖ * BQ + 16 * M / r ^ 2 * (‖s‖ + ‖t‖) * BY) := by
      positivity
    have := norm_le_along_chain_gronwall hch hℓ hd (K := ℓ * (1 + 2 * M))
      (ε := ℓ * (4 * M / r * ‖s - t‖ * BQ + 16 * M / r ^ 2 * (‖s‖ + ‖t‖) * BY))
      (δ := ‖Q s z₀ - Q t z₀‖) hKc hε0 (by rw [hv0]) ?_
    · have hδ : ‖Q s z₀ - Q t z₀‖ ≤ ‖Q s z₀ - c'‖ + ‖Q t z₀ - c'‖ := by
        rw [← norm_neg (Q t z₀ - c')]
        convert norm_add_le _ _ using 2
        abel
      have hst : ‖s - t‖ ≤ ‖s‖ + ‖t‖ := norm_sub_le s t
      have hε : ℓ * (4 * M / r * ‖s - t‖ * BQ + 16 * M / r ^ 2 * (‖s‖ + ‖t‖) * BY) ≤
          A * (‖s‖ + ‖t‖) := by
        rw [hAdef]
        have : 4 * M / r * ‖s - t‖ * BQ ≤ 4 * M / r * (‖s‖ + ‖t‖) * BQ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hst (by positivity)) hBQ0
        nlinarith
      have hz' := this.2
      rw [hvm] at hz'
      refine hz'.trans ?_
      simp only [hψdef]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hE := Real.exp_pos (ℓ * (1 + 2 * M) * m)
      nlinarith [mul_le_mul_of_nonneg_left hε hm0]
    · intro i hi τ hτ
      have hζ := polySeg_mem hK hi hτ
      rw [odeC_quot_sub]
      set ζ := polySeg v i τ
      have e1 := norm_odeC_le (hfM _ (hmem s hs) _ hζ) (hgM _ (hmem s hs) _ hζ)
        (s⁻¹ • (Y (u₀ + s) ζ - Y u₀ ζ) - t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ))
      have e2 := norm_odeC_sub_le (f (u₀ + s) ζ) (g (u₀ + s) ζ) (f (u₀ + t) ζ) (g (u₀ + t) ζ)
        (t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ))
      have e3 := norm_smul_odeC_sub_sub_le s t (f u₀ ζ) (g u₀ ζ) (f (u₀ + s) ζ) (g (u₀ + s) ζ)
        (f (u₀ + t) ζ) (g (u₀ + t) ζ) (Y u₀ ζ)
      obtain ⟨-, pf2, pf3⟩ := hPf _ hζ s hs t ht
      obtain ⟨-, pg2, pg3⟩ := hPg _ hζ s hs t ht
      have hy := hBY _ hζ
      have hq : ‖t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ)‖ ≤ BQ := by
        have := hQb t ht i hi τ hτ
        rwa [hQ] at this
      have hQe : Q s ζ - Q t ζ =
          s⁻¹ • (Y (u₀ + s) ζ - Y u₀ ζ) - t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ) := by rw [hQ]
      rw [hQe]
      have e2' : ‖odeC (f (u₀ + s) ζ) (g (u₀ + s) ζ) (t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ)) -
          odeC (f (u₀ + t) ζ) (g (u₀ + t) ζ) (t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ))‖ ≤
          4 * M / r * ‖s - t‖ * BQ :=
        e2.trans ((mul_le_mul (add_le_add pf3 pg3) hq (norm_nonneg _) (by positivity)).trans
          (le_of_eq (by ring)))
      have e3' : ‖s⁻¹ • (odeC (f (u₀ + s) ζ) (g (u₀ + s) ζ) (Y u₀ ζ) -
          odeC (f u₀ ζ) (g u₀ ζ) (Y u₀ ζ)) - t⁻¹ • (odeC (f (u₀ + t) ζ) (g (u₀ + t) ζ)
          (Y u₀ ζ) - odeC (f u₀ ζ) (g u₀ ζ) (Y u₀ ζ))‖ ≤
          16 * M / r ^ 2 * (‖s‖ + ‖t‖) * BY :=
        e3.trans ((mul_le_mul (add_le_add pf2 pg2) hy (norm_nonneg _) (by positivity)).trans
          (le_of_eq (by ring)))
      calc ℓ * ‖_‖
          ≤ ℓ * ((1 + 2 * M) * ‖s⁻¹ • (Y (u₀ + s) ζ - Y u₀ ζ) - t⁻¹ • (Y (u₀ + t) ζ - Y u₀ ζ)‖
            + 4 * M / r * ‖s - t‖ * BQ + 16 * M / r ^ 2 * (‖s‖ + ‖t‖) * BY) :=
            mul_le_mul_of_nonneg_left (norm_add₃_le.trans
              (add_le_add (add_le_add e1 e2') e3')) hℓ0
        _ = _ := by ring
  -- `ψ → 0`
  have hψ : Tendsto ψ (𝓝[≠] 0) (𝓝 0) := by
    have hq : Tendsto (fun t => Q t z₀) (𝓝[≠] 0) (𝓝 c') := by
      rw [hQ]
      exact hslope
    have hn : Tendsto (fun t : ℂ => ‖t‖) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_norm_zero.mono_left nhdsWithin_le_nhds
    have := ((hq.sub_const c').norm.add (hn.const_mul ((m : ℝ) * A))).const_mul
      (Real.exp (ℓ * (1 + 2 * M) * m))
    simp only [sub_self, norm_zero, mul_zero, add_zero] at this
    simpa only [hψdef, mul_assoc] using this
  obtain ⟨L, hL⟩ := exists_tendsto_of_dist_le (F := fun t => Q t z) hψ hS hcl
  refine ⟨L, hasDerivAt_iff_tendsto_slope_zero.mpr ?_⟩
  rw [hQ] at hL
  exact hL

/-- **DLMF §1.13(ii)**: for `∂²w/∂z² + f(u, z) ∂w/∂z + g(u, z) w = 0` (1.13.7) with `f`, `g`
jointly continuous on `U × D` and analytic in `u` for fixed `z`, if `w` and `∂w/∂z` are analytic
in `u` at one `z₀ ∈ D`, then `w`, `∂w/∂z` and `∂²w/∂z²` are analytic in `u` at every `z ∈ D`.
(DLMF also assumes analyticity in `z` for fixed `u`, which the proof does not need beyond the
existence of the solutions `w(u, ·)`.) -/
theorem dlmf_1_13_ii (hU : IsOpen U) (hDo : IsOpen D) (hDc : IsConnected D)
    (hfc : ContinuousOn (Function.uncurry f) (U ×ˢ D))
    (hgc : ContinuousOn (Function.uncurry g) (U ×ˢ D))
    (hfu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => f u z) U)
    (hgu : ∀ z ∈ D, DifferentiableOn ℂ (fun u => g u z) U)
    (hw : ∀ u ∈ U, IsODESolution D (f u) (g u) (w u)) {z₀ : ℂ} (hz₀ : z₀ ∈ D)
    (h0 : AnalyticOnNhd ℂ (fun u => w u z₀) U)
    (h1 : AnalyticOnNhd ℂ (fun u => deriv (w u) z₀) U) {z : ℂ} (hz : z ∈ D) :
    AnalyticOnNhd ℂ (fun u => w u z) U ∧ AnalyticOnNhd ℂ (fun u => deriv (w u) z) U ∧
      AnalyticOnNhd ℂ (fun u => deriv (deriv (w u)) z) U := by
  have hd : ∀ u ∈ U, DifferentiableAt ℂ (fun u => (w u z, deriv (w u) z)) u := fun u hu =>
    (exists_hasDerivAt_param hU hDo hDc hfc hgc hfu hgu hw hz₀ h0.differentiableOn
      h1.differentiableOn hu hz).choose_spec.differentiableAt
  have d1 : DifferentiableOn ℂ (fun u => w u z) U := fun u hu =>
    (hd u hu).fst.differentiableWithinAt
  have d2 : DifferentiableOn ℂ (fun u => deriv (w u) z) U := fun u hu =>
    (hd u hu).snd.differentiableWithinAt
  have d3 : DifferentiableOn ℂ (fun u => deriv (deriv (w u)) z) U :=
    (((hfu z hz).mul d2).add ((hgu z hz).mul d1)).neg.congr fun u hu => by
      simp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
      linear_combination (hw u hu).2 z hz
  exact ⟨d1.analyticOnNhd hU, d2.analyticOnNhd hU, d3.analyticOnNhd hU⟩

end Parameter

end Azurite.DLMF
