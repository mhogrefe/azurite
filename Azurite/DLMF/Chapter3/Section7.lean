/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section13Inhomogeneous
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# DLMF §3.7(i)–(ii): ordinary differential equations, the Taylor-series method

* §3.7(i): 3.7.1 `w″ + f w′ + g w = h` with `f`, `g`, `h` analytic in a domain `D` is §1.13's
  `IsInhomSolution D f g h w`; homogeneous (`h = 0`) it is `IsODESolution`
  (`dlmf_3_7_1_homogeneous`).
* 3.7.3–3.7.4: the coefficient functions `f_s`, `g_s`, `h_s` (`taylorF`, `taylorG`, `taylorH`;
  `dlmf_3_7_3`, `dlmf_3_7_4`), analytic in `D`; 3.7.2 `w^{(s)} = f_s w + g_s w′ + h_s`
  (`dlmf_3_7_2`).
* 3.7.5–3.7.9: the matrix `𝐀(τ, z)` and vector `𝐛(τ, z)` (`taylorA`, `taylorB`). The six series
  converge for `|τ| < R` whenever `f`, `g`, `h` are analytic in the disk `B(z, R)`
  (`dlmf_3_7_8_9`; their sums are the solutions with data `(1, 0)`, `(0, 1)`, `(0, 0)` at `z`,
  which exist since a disk is a simply-connected domain, `isSCDomain_ball`), and the Taylor step
  3.7.5 holds (`dlmf_3_7_5`).
* Integration along the partition `z₀ = a, …, z_P = b` (`IsTaylorPath`, `taylorPath`): exact
  (`dlmf_3_7_ii_exact`); errors committed at the steps propagate as homogeneous solutions
  (`taylorPath_sub`); forward integration is stable when the wanted solution grows at least as
  fast as all other solutions (`dlmf_3_7_ii_forward_stable`), and backward integration from
  `w(b)`, `w′(b)` when it decays at least as fast (`dlmf_3_7_ii_backward_stable`).

The pointers (§1.13, §2.7, Ascher–Petzold, Hairer et al., Iserles) are not formalized.
-/

open Filter Topology Set Metric Complex
open scoped Nat Matrix

namespace Azurite.DLMF

/-- **DLMF 3.7.1**, homogeneous case: `h = 0` gives §1.13's equation 1.13.1. -/
theorem dlmf_3_7_1_homogeneous (D : Set ℂ) (f g w : ℂ → ℂ) :
    IsInhomSolution D f g (fun _ => 0) w ↔ IsODESolution D f g w := Iff.rfl

/-! ### Open disks are simply-connected domains -/

/-- The ray `{c + t (p − c) : t ≥ 1}` from `p ≠ c` away from `c` has `∞` in its closure. -/
theorem infty_mem_closure_ray {c p : ℂ} (hp : p ≠ c) :
    (OnePoint.infty : OnePoint ℂ) ∈
      closure (((↑) : ℂ → OnePoint ℂ) '' ((fun t : ℝ => c + t • (p - c)) '' Ici 1)) := by
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  rintro s ⟨-, hs⟩
  obtain ⟨M, hM⟩ := hs.isBounded.subset_closedBall c
  have hpc : 0 < ‖p - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  set t : ℝ := max 1 ((|M| + 1) / ‖p - c‖)
  have ht1 : 1 ≤ t := le_max_left _ _
  have hty : (|M| + 1) / ‖p - c‖ ≤ t := le_max_right _ _
  refine ⟨_, ⟨c + t • (p - c), ⟨t, ht1, rfl⟩, rfl⟩, Or.inl ⟨c + t • (p - c), fun hmem => ?_, rfl⟩⟩
  have h1 := mem_closedBall.mp (hM hmem)
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith)] at h1
  rw [div_le_iff₀ hpc] at hty
  linarith [le_abs_self M]

/-- **An open disk is a simply-connected domain** in the sense of §1.13(i): its complement in
`ℂ ∪ {∞}` is the union of the closed rays from its points to `∞`. -/
theorem isSCDomain_ball (c : ℂ) {r : ℝ} (hr : 0 < r) : IsSCDomain (ball c r) where
  isOpen := isOpen_ball
  isConnected := (convex_ball c r).isConnected (nonempty_ball.mpr hr)
  simplyConnected := by
    rw [IsSimplyConnectedDLMF]
    have hcl : IsClosed (((↑) : ℂ → OnePoint ℂ) '' ball c r)ᶜ :=
      (OnePoint.isOpen_image_coe.mpr isOpen_ball).isClosed_compl
    refine ⟨⟨OnePoint.infty, fun ⟨x, _, hx⟩ => OnePoint.coe_ne_infty x hx⟩,
      isPreconnected_of_forall OnePoint.infty fun y hy => ?_⟩
    induction y using OnePoint.rec with
    | infty => exact ⟨{OnePoint.infty}, by simp, rfl, rfl, isPreconnected_singleton⟩
    | coe p =>
      have hp : p ∉ ball c r := fun h => hy ⟨p, h, rfl⟩
      have hpc : r ≤ ‖p - c‖ := by simpa [dist_eq_norm] using hp
      have hpne : p ≠ c := fun h => by simp [h] at hpc; linarith
      set R := ((fun t : ℝ => c + t • (p - c)) '' Ici 1)
      have hcont : Continuous fun t : ℝ => c + t • (p - c) := by fun_prop
      have hRc : IsPreconnected R := isPreconnected_Ici.image _ hcont.continuousOn
      refine ⟨closure (((↑) : ℂ → OnePoint ℂ) '' R), ?_, infty_mem_closure_ray hpne,
        subset_closure ⟨p, ⟨1, self_mem_Ici, by simp⟩, rfl⟩,
        (hRc.image _ OnePoint.continuous_coe.continuousOn).closure⟩
      refine closure_minimal ?_ hcl
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ ⟨x, hx, hxe⟩
      rw [OnePoint.coe_injective.eq_iff] at hxe
      subst hxe
      have : ‖t • (p - c)‖ < r := by simpa [dist_eq_norm] using hx
      rw [norm_smul, Real.norm_of_nonneg (by linarith [mem_Ici.mp ht])] at this
      nlinarith [mem_Ici.mp ht]

/-! ### 3.7.2–3.7.4: the coefficient functions `f_s`, `g_s`, `h_s` -/

/-- The pair `(f_s, g_s)` of 3.7.2: `(f₀, g₀) = (1, 0)` and
`(f_s, g_s) = (f′_{s−1} − g g_{s−1}, f_{s−1} − f g_{s−1} + g′_{s−1})`. -/
noncomputable def taylorFG (f g : ℂ → ℂ) : ℕ → (ℂ → ℂ) × (ℂ → ℂ)
  | 0 => (fun _ => 1, fun _ => 0)
  | s + 1 => (fun z => deriv (taylorFG f g s).1 z - g z * (taylorFG f g s).2 z,
      fun z => (taylorFG f g s).1 z - f z * (taylorFG f g s).2 z + deriv (taylorFG f g s).2 z)

/-- `f_s` of 3.7.2. -/
noncomputable def taylorF (f g : ℂ → ℂ) (s : ℕ) : ℂ → ℂ := (taylorFG f g s).1

/-- `g_s` of 3.7.2. -/
noncomputable def taylorG (f g : ℂ → ℂ) (s : ℕ) : ℂ → ℂ := (taylorFG f g s).2

/-- `h_s` of 3.7.2: `h₀ = 0` and `h_s = h g_{s−1} + h′_{s−1}`. -/
noncomputable def taylorH (f g h : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | s + 1 => fun z => h z * taylorG f g s z + deriv (taylorH f g h s) z

/-- **DLMF 3.7.3**. -/
theorem dlmf_3_7_3 (f g h : ℂ → ℂ) :
    taylorF f g 0 = (fun _ => 1) ∧ taylorG f g 0 = (fun _ => 0) ∧ taylorH f g h 0 = (fun _ => 0) ∧
      taylorF f g 1 = (fun _ => 0) ∧ taylorG f g 1 = (fun _ => 1) ∧
        taylorH f g h 1 = (fun _ => 0) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> funext z <;>
    simp [taylorF, taylorG, taylorH, taylorFG]

/-- **DLMF 3.7.4** (`s ≥ 2`; it holds for `s = 1` as well). -/
theorem dlmf_3_7_4 (f g h : ℂ → ℂ) {s : ℕ} (hs : 1 ≤ s) (z : ℂ) :
    taylorF f g s z = deriv (taylorF f g (s - 1)) z - g z * taylorG f g (s - 1) z ∧
      taylorG f g s z =
        taylorF f g (s - 1) z - f z * taylorG f g (s - 1) z + deriv (taylorG f g (s - 1)) z ∧
      taylorH f g h s z = h z * taylorG f g (s - 1) z + deriv (taylorH f g h (s - 1)) z := by
  obtain ⟨s, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  exact ⟨rfl, rfl, rfl⟩

section Coefficients

variable {D : Set ℂ} {f g h : ℂ → ℂ}

theorem taylorFG_differentiableOn (hDo : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (s : ℕ) :
    DifferentiableOn ℂ (taylorF f g s) D ∧ DifferentiableOn ℂ (taylorG f g s) D := by
  induction s with
  | zero => exact ⟨differentiableOn_const _, differentiableOn_const _⟩
  | succ s ih =>
    exact ⟨(ih.1.deriv hDo).sub (hg.mul ih.2),
      (ih.1.sub (hf.mul ih.2)).add (ih.2.deriv hDo)⟩

theorem taylorH_differentiableOn (hDo : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) (s : ℕ) :
    DifferentiableOn ℂ (taylorH f g h s) D := by
  induction s with
  | zero => exact differentiableOn_const _
  | succ s ih => exact (hh.mul (taylorFG_differentiableOn hDo hf hg s).2).add (ih.deriv hDo)

/-- For the homogeneous equation all `h_s` vanish. -/
theorem taylorH_zero (f g : ℂ → ℂ) (s : ℕ) : taylorH f g (fun _ => 0) s = fun _ => 0 := by
  induction s with
  | zero => rfl
  | succ s ih => funext z; simp [taylorH, ih]

/-- **DLMF 3.7.2**: for a solution of 3.7.1 (`IsInhomSolution D f g h w`, with `f`, `g`, `h`
analytic in the domain `D`), `w^{(s)} = f_s w + g_s w′ + h_s` in `D`. -/
theorem dlmf_3_7_2 (hDo : IsOpen D) (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) (s : ℕ) :
    ∀ z ∈ D, iteratedDeriv s w z =
      taylorF f g s z * w z + taylorG f g s z * deriv w z + taylorH f g h s z := by
  induction s with
  | zero => intro z _; simp [taylorF, taylorG, taylorH, taylorFG]
  | succ s ih =>
    intro z hz
    have hev : iteratedDeriv s w =ᶠ[𝓝 z]
        fun y => taylorF f g s y * w y + taylorG f g s y * deriv w y + taylorH f g h s y := by
      filter_upwards [hDo.mem_nhds hz] with y hy using ih y hy
    have hN := hDo.mem_nhds hz
    have hF := ((taylorFG_differentiableOn hDo hf hg s).1.differentiableAt hN).hasDerivAt
    have hG := ((taylorFG_differentiableOn hDo hf hg s).2.differentiableAt hN).hasDerivAt
    have hH := ((taylorH_differentiableOn hDo hf hg hh s).differentiableAt hN).hasDerivAt
    obtain ⟨hw1, hw2⟩ := hw.hasDerivAt hDo hz
    have hd : HasDerivAt
        (fun y => taylorF f g s y * w y + taylorG f g s y * deriv w y + taylorH f g h s y) _ z :=
      ((hF.mul hw1).add (hG.mul hw2)).add hH
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
    simp only [taylorF, taylorG, taylorH, taylorFG]
    ring

/-! ### 3.7.5–3.7.9: one Taylor step -/

/-- **DLMF 3.7.6** with the entries 3.7.8. -/
noncomputable def taylorA (f g : ℂ → ℂ) (τ z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![∑' s : ℕ, τ ^ s / s ! * taylorF f g s z, ∑' s : ℕ, τ ^ s / s ! * taylorG f g s z;
    ∑' s : ℕ, τ ^ s / s ! * taylorF f g (s + 1) z, ∑' s : ℕ, τ ^ s / s ! * taylorG f g (s + 1) z]

/-- **DLMF 3.7.7** with the entries 3.7.9. -/
noncomputable def taylorB (f g h : ℂ → ℂ) (τ z : ℂ) : Fin 2 → ℂ :=
  ![∑' s : ℕ, τ ^ s / s ! * taylorH f g h s z, ∑' s : ℕ, τ ^ s / s ! * taylorH f g h (s + 1) z]

/-- Taylor expansions of `w` and `w′` about `z` for a solution of 3.7.1 in a disk about `z`,
with the coefficients rewritten by 3.7.2. -/
theorem hasSum_taylor_sol {z : ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (ball z R))
    (hg : DifferentiableOn ℂ g (ball z R)) (hh : DifferentiableOn ℂ h (ball z R)) {w : ℂ → ℂ}
    (hw : IsInhomSolution (ball z R) f g h w) {τ : ℂ} (hτ : ‖τ‖ < R) :
    HasSum (fun s : ℕ => τ ^ s / s ! *
        (taylorF f g s z * w z + taylorG f g s z * deriv w z + taylorH f g h s z)) (w (z + τ)) ∧
      HasSum (fun s : ℕ => τ ^ s / s ! * (taylorF f g (s + 1) z * w z +
        taylorG f g (s + 1) z * deriv w z + taylorH f g h (s + 1) z)) (deriv w (z + τ)) := by
  have hz : z ∈ ball z R := mem_ball_self (lt_of_le_of_lt (norm_nonneg _) hτ)
  have hzτ : z + τ ∈ ball z R := by simpa [dist_eq_norm] using hτ
  have h1 := Complex.hasSum_taylorSeries_on_ball hw.1 hzτ
  have h2 := Complex.hasSum_taylorSeries_on_ball (hw.1.deriv isOpen_ball) hzτ
  refine ⟨?_, ?_⟩
  · convert h1 using 1
    funext s
    rw [← dlmf_3_7_2 isOpen_ball hf hg hh hw s z hz]
    simp only [add_sub_cancel_left, smul_eq_mul]
    ring
  · convert h2 using 1
    funext s
    rw [← iteratedDeriv_succ', ← dlmf_3_7_2 isOpen_ball hf hg hh hw (s + 1) z hz]
    simp only [add_sub_cancel_left, smul_eq_mul]
    ring

/-- **DLMF 3.7.8–3.7.9**: the six series converge for `|τ|` less than the radius of any disk
about `z` in which `f`, `g`, `h` are analytic. Their sums are the values at `z + τ` of the
solutions with data `(1, 0)`, `(0, 1)` (homogeneous) and `(0, 0)` (inhomogeneous) at `z`. -/
theorem dlmf_3_7_8_9 {z : ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (ball z R))
    (hg : DifferentiableOn ℂ g (ball z R)) (hh : DifferentiableOn ℂ h (ball z R)) {τ : ℂ}
    (hτ : ‖τ‖ < R) :
    HasSum (fun s : ℕ => τ ^ s / s ! * taylorF f g s z) (taylorA f g τ z 0 0) ∧
      HasSum (fun s : ℕ => τ ^ s / s ! * taylorG f g s z) (taylorA f g τ z 0 1) ∧
      HasSum (fun s : ℕ => τ ^ s / s ! * taylorF f g (s + 1) z) (taylorA f g τ z 1 0) ∧
      HasSum (fun s : ℕ => τ ^ s / s ! * taylorG f g (s + 1) z) (taylorA f g τ z 1 1) ∧
      HasSum (fun s : ℕ => τ ^ s / s ! * taylorH f g h s z) (taylorB f g h τ z 0) ∧
      HasSum (fun s : ℕ => τ ^ s / s ! * taylorH f g h (s + 1) z) (taylorB f g h τ z 1) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hτ
  have hz : z ∈ ball z R := mem_ball_self hR
  have h0 : DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) (ball z R) := differentiableOn_const _
  obtain ⟨u, hu, hu0, hu1⟩ := dlmf_1_13_iii_exists (isSCDomain_ball z hR) hf hg h0 hz 1 0
  obtain ⟨v, hv, hv0, hv1⟩ := dlmf_1_13_iii_exists (isSCDomain_ball z hR) hf hg h0 hz 0 1
  obtain ⟨p, hp, hp0, hp1⟩ := dlmf_1_13_iii_exists (isSCDomain_ball z hR) hf hg hh hz 0 0
  obtain ⟨hu', hu''⟩ := hasSum_taylor_sol hf hg h0 hu hτ
  obtain ⟨hv', hv''⟩ := hasSum_taylor_sol hf hg h0 hv hτ
  obtain ⟨hp', hp''⟩ := hasSum_taylor_sol hf hg hh hp hτ
  simp only [hu0, hu1, hv0, hv1, hp0, hp1, taylorH_zero, mul_one, mul_zero, add_zero,
    zero_add] at hu' hu'' hv' hv'' hp' hp''
  simp only [taylorA, taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  exact ⟨hu'.summable.hasSum, hv'.summable.hasSum, hu''.summable.hasSum, hv''.summable.hasSum,
    hp'.summable.hasSum, hp''.summable.hasSum⟩

/-- **DLMF 3.7.5**: one Taylor step from `z` to `z + τ`, for a solution of 3.7.1 in `D` and any
disk `B(z, R) ⊆ D` with `|τ| < R`. -/
theorem dlmf_3_7_5 (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) {z τ : ℂ} {R : ℝ}
    (hzR : ball z R ⊆ D) (hτ : ‖τ‖ < R) :
    ![w (z + τ), deriv w (z + τ)] =
      taylorA f g τ z *ᵥ ![w z, deriv w z] + taylorB f g h τ z := by
  have hwR : IsInhomSolution (ball z R) f g h w := ⟨hw.1.mono hzR, fun y hy => hw.2 y (hzR hy)⟩
  obtain ⟨hw', hw''⟩ := hasSum_taylor_sol (hf.mono hzR) (hg.mono hzR) (hh.mono hzR) hwR hτ
  obtain ⟨a00, a01, a10, a11, b0, b1⟩ :=
    dlmf_3_7_8_9 (hf.mono hzR) (hg.mono hzR) (hh.mono hzR) hτ
  have e0 := ((a00.mul_right (w z)).add (a01.mul_right (deriv w z))).add b0
  have e1 := ((a10.mul_right (w z)).add (a11.mul_right (deriv w z))).add b1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.cons_val_one]
    refine hw'.unique (e0.congr_fun fun s => ?_)
    ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Pi.add_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero]
    refine hw''.unique (e1.congr_fun fun s => ?_)
    ring

end Coefficients

/-! ### Integration along a path -/

section Path

variable {D : Set ℂ} {f g h : ℂ → ℂ}

/-- The state vector `[w(z), w′(z)]` of 3.7.5. -/
noncomputable def odeState (w : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ := ![w z, deriv w z]

/-- The partition `z₀, z₁, …, z_P` of a path in `D`: `z₀ ∈ D`, and each step `zⱼ → z_{j+1}`
(`τⱼ = z_{j+1} − zⱼ`) stays in a disk about `zⱼ` contained in `D`, so that 3.7.5 applies. -/
def IsTaylorPath (D : Set ℂ) (zs : ℕ → ℂ) (P : ℕ) : Prop :=
  zs 0 ∈ D ∧ ∀ j < P, ∃ R, ball (zs j) R ⊆ D ∧ ‖zs (j + 1) - zs j‖ < R

theorem IsTaylorPath.mem {zs : ℕ → ℂ} {P : ℕ} (hP : IsTaylorPath D zs P) :
    ∀ j ≤ P, zs j ∈ D := by
  intro j hj
  cases j with
  | zero => exact hP.1
  | succ i =>
    obtain ⟨R, hR, hτ⟩ := hP.2 i (by omega)
    exact hR (by rw [mem_ball, dist_eq_norm]; exact hτ)

/-- Successive application of 3.7.5 along `z₀, z₁, …` starting from `Y₀`, with an error `δⱼ`
committed at step `j` (`δ = 0`: exact arithmetic). -/
noncomputable def taylorPath (f g h : ℂ → ℂ) (zs : ℕ → ℂ) (Y₀ : Fin 2 → ℂ)
    (δ : ℕ → Fin 2 → ℂ) : ℕ → Fin 2 → ℂ
  | 0 => Y₀ + δ 0
  | j + 1 => taylorA f g (zs (j + 1) - zs j) (zs j) *ᵥ taylorPath f g h zs Y₀ δ j +
      taylorB f g h (zs (j + 1) - zs j) (zs j) + δ (j + 1)

theorem taylorB_zero (f g : ℂ → ℂ) (τ z : ℂ) : taylorB f g (fun _ => 0) τ z = 0 := by
  funext i
  fin_cases i <;> simp [taylorB, taylorH_zero]

/-- 3.7.5 for consecutive points of the path. -/
theorem odeState_succ (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ}
    {P : ℕ} (hP : IsTaylorPath D zs P) {j : ℕ} (hj : j < P) :
    odeState w (zs (j + 1)) = taylorA f g (zs (j + 1) - zs j) (zs j) *ᵥ odeState w (zs j) +
      taylorB f g h (zs (j + 1) - zs j) (zs j) := by
  obtain ⟨R, hR, hτ⟩ := hP.2 j hj
  have := dlmf_3_7_5 hf hg hh hw hR hτ
  rwa [add_sub_cancel] at this

/-- **DLMF §3.7(ii)**: in exact arithmetic, successive application of 3.7.5 for
`j = 0, 1, …, P − 1`, beginning with `w(a)` and `w′(a)` (`a = z₀`), yields `w(zⱼ)` and `w′(zⱼ)`
for `j = 0, 1, …, P`. -/
theorem dlmf_3_7_ii_exact (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ}
    {P : ℕ} (hP : IsTaylorPath D zs P) :
    ∀ j ≤ P, taylorPath f g h zs (odeState w (zs 0)) 0 j = odeState w (zs j) := by
  intro j hj
  induction j with
  | zero => simp [taylorPath]
  | succ j ih =>
    simp only [taylorPath, Pi.zero_apply, add_zero]
    rw [ih (by omega), odeState_succ hf hg hh hw hP (by omega)]

/-- Error propagation: the errors `δⱼ` committed at the steps `j ≤ k` reach `z_k` as the
homogeneous solutions `Vⱼ` with state `δⱼ` at `zⱼ`. -/
theorem taylorPath_sub (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ} (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ}
    {P : ℕ} (hP : IsTaylorPath D zs P) {δ : ℕ → Fin 2 → ℂ} {V : ℕ → ℂ → ℂ}
    (hV : ∀ j, IsInhomSolution D f g (fun _ => 0) (V j))
    (hV0 : ∀ j ≤ P, odeState (V j) (zs j) = δ j) :
    ∀ k ≤ P, taylorPath f g h zs (odeState w (zs 0)) δ k - odeState w (zs k) =
      ∑ j ∈ Finset.range (k + 1), odeState (V j) (zs k) := by
  have h0 : DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) D := differentiableOn_const _
  intro k hk
  induction k with
  | zero => simp [taylorPath, hV0 0 hk]
  | succ k ih =>
    have hsum : ∀ j, odeState (V j) (zs (k + 1)) =
        taylorA f g (zs (k + 1) - zs k) (zs k) *ᵥ odeState (V j) (zs k) := fun j => by
      rw [odeState_succ hf hg h0 (hV j) hP (by omega), taylorB_zero, add_zero]
    rw [Finset.sum_range_succ, hV0 (k + 1) hk, Finset.sum_congr rfl fun j _ => hsum j,
      ← Matrix.mulVec_sum, ← ih (by omega), Matrix.mulVec_sub,
      odeState_succ hf hg hh hw hP (by omega)]
    simp only [taylorPath]
    abel

/-- **DLMF §3.7(ii)**, forward integration is stable when the wanted solution "grows in magnitude
at least as fast as all other solutions of 3.7.1 as we pass along 𝒫 from `a` to `b`": if for
every solution `v` of the homogeneous equation and all `j ≤ k ≤ P`,
`‖v(z_k)‖/‖w(z_k)‖ ≤ C ‖v(zⱼ)‖/‖w(zⱼ)‖` (states `[v, v′]`, `[w, w′]`), then the relative error
at `z_k` is at most `C` times the sum of the relative errors `‖δⱼ‖/‖w(zⱼ)‖` committed at the
steps `j ≤ k`. -/
theorem dlmf_3_7_ii_forward_stable (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ}
    (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ} {P : ℕ} (hP : IsTaylorPath D zs P)
    (δ : ℕ → Fin 2 → ℂ) {C : ℝ}
    (hdom : ∀ v, IsInhomSolution D f g (fun _ => 0) v → ∀ j k, j ≤ k → k ≤ P →
      ‖odeState v (zs k)‖ * ‖odeState w (zs j)‖ ≤ C * ‖odeState v (zs j)‖ * ‖odeState w (zs k)‖)
    (hW : ∀ j ≤ P, odeState w (zs j) ≠ 0) :
    ∀ k ≤ P, ‖taylorPath f g h zs (odeState w (zs 0)) δ k - odeState w (zs k)‖ /
        ‖odeState w (zs k)‖ ≤ C * ∑ j ∈ Finset.range (k + 1), ‖δ j‖ / ‖odeState w (zs j)‖ := by
  have h0 : DifferentiableOn ℂ (fun _ : ℂ => (0 : ℂ)) D := differentiableOn_const _
  have hex : ∀ j, ∃ v, IsInhomSolution D f g (fun _ => 0) v ∧
      (j ≤ P → odeState v (zs j) = δ j) := fun j => by
    by_cases hj : j ≤ P
    · obtain ⟨v, hv, hv0, hv1⟩ := dlmf_1_13_iii_exists hD hf hg h0 (hP.mem j hj) (δ j 0) (δ j 1)
      refine ⟨v, hv, fun _ => ?_⟩
      funext i
      fin_cases i <;> simp [odeState, hv0, hv1]
    · refine ⟨fun _ => 0, ⟨differentiableOn_const _, fun z _ => by simp⟩, fun h => absurd h hj⟩
  choose V hV hV0 using hex
  intro k hk
  have hWk := norm_pos_iff.mpr (hW k hk)
  rw [taylorPath_sub hf hg hh hw hP hV hV0 k hk, div_le_iff₀ hWk, Finset.mul_sum,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hWj := norm_pos_iff.mpr (hW j (hjk.trans hk))
  have := hdom (V j) (hV j) j k hjk hk
  rw [hV0 j (hjk.trans hk)] at this
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hWj]
  linarith

/-- **DLMF §3.7(ii)**, backward integration: "if `w(z)` is decaying at least as fast as all other
solutions along 𝒫, then we may reverse the labeling of the `zⱼ` along 𝒫 and begin with initial
values `w(b)` and `w′(b)`". With `‖v(zⱼ)‖/‖w(zⱼ)‖ ≤ C ‖v(z_k)‖/‖w(z_k)‖` for `j ≤ k ≤ P`, the
iteration along `z_P, z_{P−1}, …, z₀` is stable in the sense of `dlmf_3_7_ii_forward_stable`. -/
theorem dlmf_3_7_ii_backward_stable (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D) {w : ℂ → ℂ}
    (hw : IsInhomSolution D f g h w) {zs : ℕ → ℂ} {P : ℕ}
    (hP : IsTaylorPath D (fun j => zs (P - j)) P) (δ : ℕ → Fin 2 → ℂ) {C : ℝ}
    (hdec : ∀ v, IsInhomSolution D f g (fun _ => 0) v → ∀ j k, j ≤ k → k ≤ P →
      ‖odeState v (zs j)‖ * ‖odeState w (zs k)‖ ≤ C * ‖odeState v (zs k)‖ * ‖odeState w (zs j)‖)
    (hW : ∀ j ≤ P, odeState w (zs j) ≠ 0) :
    ∀ k ≤ P, ‖taylorPath f g h (fun j => zs (P - j)) (odeState w (zs P)) δ k -
        odeState w (zs (P - k))‖ / ‖odeState w (zs (P - k))‖ ≤
      C * ∑ j ∈ Finset.range (k + 1), ‖δ j‖ / ‖odeState w (zs (P - j))‖ := by
  have := dlmf_3_7_ii_forward_stable hD hf hg hh hw hP δ
    (fun v hv j k hjk hkP => hdec v hv (P - k) (P - j) (by omega) (by omega))
    (fun j hj => hW (P - j) (by omega))
  simpa using this

end Path

end Azurite.DLMF
