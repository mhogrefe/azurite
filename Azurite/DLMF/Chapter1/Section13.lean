/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section13Primitive

/-!
# DLMF §1.13(i): Existence of Solutions

Formalizations of <https://dlmf.nist.gov/1.13#i> for `w″ + f(z) w′ + g(z) w = 0` (1.13.1) with
`f`, `g` analytic in a simply-connected domain `D` (`IsSCDomain`: open, connected, and with
connected complement in `ℂ ∪ {∞}`).

**Method.** Solutions of (1.13.1) are the first components of solutions of the system
`Y′ = A(z) Y` with `Y = (w, w′)` (`odeA`). Primitives exist on `D` (`Section13Primitive.lean`), so
the Picard iterates `Y_{k+1} = c + ∫_{z₀}^z A Y_k` are defined on all of `D` (`picard`). Along a
polygonal chain from `z₀` with sides of length at most `ℓ`, on which `|f|, |g| ≤ M`, the
differences satisfy `‖Y_{k+1} − Y_k‖ ≤ ‖c‖ ((1 + 2M) ℓ t)^{k+1} / (k + 1)!` (`norm_iter_le`). This
bound is uniform on a small disk about each point of `D`, so the iterates converge locally
uniformly to a solution. The same estimate applied to `Y = (w, w′)` with zero data gives
uniqueness, without analytic continuation.

**Results.**
* 1.13.1: `IsODESolution`; solutions are analytic (`IsODESolution.analyticOnNhd`), and linear
  combinations of solutions are solutions (`IsODESolution.linearCombo`).
* Existence and uniqueness for prescribed `w(z₀)`, `w′(z₀)` (`dlmf_1_13_i_exists`,
  `dlmf_1_13_i_eq_zero`, `dlmf_1_13_i_unique`), and infinitely many solutions
  (`dlmf_1_13_i_infinite`).
* 1.13.2–1.13.3: fundamental pairs (`IsFundamentalPair`, `dlmf_1_13_2`), and the pair normalized
  at `z₀` (`dlmf_1_13_3`).
* 1.13.4: the Wronskian and its determinant form (`wronskian`, `dlmf_1_13_4`), and the
  `n`-argument Wronskian `det [w_k^{(j−1)}]` (`wronskianN`, `wronskianN_two`).
* 1.13.5: Abel's identity `𝒲 = c e^{−∫ f}` for any primitive of `f` (`dlmf_1_13_5`), and with the
  primitive normalized at `z₀` (`dlmf_1_13_5_primitive`). The Wronskian vanishes nowhere or
  identically (`wronskian_eq_zero_or_ne_zero`), and is constant when `f = 0`
  (`dlmf_1_13_i_wronskian_const`).
* The `n`th-order version of 1.13.5 (Ince §5.2): Jacobi's formula for the derivative of a
  determinant (`hasDerivAt_det`) gives `𝒲′ = −a_n 𝒲` for solutions of
  `w^{(n+1)} + ∑ a_j w^{(j)} = 0` (`IsODESolutionN`, `dlmf_1_13_5_orderN`). With a nonvanishing
  leading coefficient, the exponent is the quotient of the two top coefficients
  (`dlmf_1_13_5_orderN_general`).
* 1.13.6: being a fundamental pair, a nonvanishing Wronskian and linear independence are
  equivalent (`dlmf_1_13_6`).
-/

open Filter Topology Set Metric Complex
open scoped Nat

namespace Azurite.DLMF

/-- A simply-connected domain in the sense of DLMF §1.13(i): open, connected, and with connected
complement in `ℂ ∪ {∞}`. -/
structure IsSCDomain (D : Set ℂ) : Prop where
  isOpen : IsOpen D
  isConnected : IsConnected D
  simplyConnected : IsSimplyConnectedDLMF D

/-- **DLMF (1.13.1)**: `w` solves `w″ + f(z) w′ + g(z) w = 0` in `D`. -/
def IsODESolution (D : Set ℂ) (f g w : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ w D ∧ ∀ z ∈ D, deriv (deriv w) z + f z * deriv w z + g z * w z = 0

variable {D : Set ℂ} {f g : ℂ → ℂ}

theorem IsODESolution.hasDerivAt (hDo : IsOpen D) {w : ℂ → ℂ} (hw : IsODESolution D f g w)
    {z : ℂ} (hz : z ∈ D) :
    HasDerivAt w (deriv w z) z ∧ HasDerivAt (deriv w) (-(f z * deriv w z + g z * w z)) z := by
  refine ⟨(hw.1.differentiableAt (hDo.mem_nhds hz)).hasDerivAt, ?_⟩
  have := ((hw.1.deriv hDo).differentiableAt (hDo.mem_nhds hz)).hasDerivAt
  convert this using 1
  linear_combination -(hw.2 z hz)

theorem isODESolution_of_hasDerivAt (hDo : IsOpen D) {w w' : ℂ → ℂ}
    (h : ∀ z ∈ D, HasDerivAt w (w' z) z ∧ HasDerivAt w' (-(f z * w' z + g z * w z)) z) :
    IsODESolution D f g w := by
  refine ⟨fun z hz => (h z hz).1.differentiableAt.differentiableWithinAt, fun z hz => ?_⟩
  have heq : deriv w =ᶠ[𝓝 z] w' := by
    filter_upwards [hDo.mem_nhds hz] with y hy using (h y hy).1.deriv
  rw [heq.deriv_eq, (h z hz).2.deriv, (h z hz).1.deriv]
  ring

/-- Solutions are analytic in `D`. -/
theorem IsODESolution.analyticOnNhd (hDo : IsOpen D) {w : ℂ → ℂ} (hw : IsODESolution D f g w) :
    AnalyticOnNhd ℂ w D :=
  hw.1.analyticOnNhd hDo

/-- Linear combinations of solutions are solutions. -/
theorem IsODESolution.linearCombo (hDo : IsOpen D) {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) (A B : ℂ) :
    IsODESolution D f g (fun z => A * w₁ z + B * w₂ z) := by
  refine isODESolution_of_hasDerivAt hDo (w' := fun z => A * deriv w₁ z + B * deriv w₂ z)
    fun z hz => ?_
  obtain ⟨a1, a2⟩ := h₁.hasDerivAt hDo hz
  obtain ⟨b1, b2⟩ := h₂.hasDerivAt hDo hz
  refine ⟨(a1.const_mul A).add (b1.const_mul B), ?_⟩
  convert (a2.const_mul A).add (b2.const_mul B) using 1
  ring

theorem IsODESolution.hasDerivAt_linearCombo (hDo : IsOpen D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsODESolution D f g w₁) (h₂ : IsODESolution D f g w₂) (A B : ℂ) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (fun z => A * w₁ z + B * w₂ z) (A * deriv w₁ z + B * deriv w₂ z) z :=
  (((h₁.hasDerivAt hDo hz).1).const_mul A).add (((h₂.hasDerivAt hDo hz).1).const_mul B)

/-! ### The first-order system -/

/-- The system `Y′ = A(z) Y` equivalent to (1.13.1), for `Y = (w, w′)`. -/
def odeA (f g : ℂ → ℂ) (z : ℂ) (Y : ℂ × ℂ) : ℂ × ℂ := (Y.2, -(g z * Y.1 + f z * Y.2))

theorem odeA_sub (z : ℂ) (Y Y' : ℂ × ℂ) :
    odeA f g z Y - odeA f g z Y' = odeA f g z (Y - Y') := by
  ext <;> simp only [odeA, Prod.fst_sub, Prod.snd_sub]
  ring

theorem norm_odeA_le {M : ℝ} {z : ℂ} (hf : ‖f z‖ ≤ M) (hg : ‖g z‖ ≤ M) (Y : ℂ × ℂ) :
    ‖odeA f g z Y‖ ≤ (1 + 2 * M) * ‖Y‖ := by
  have h1 := norm_fst_le Y
  have h2 := norm_snd_le Y
  have hM : 0 ≤ M := (norm_nonneg _).trans hf
  have hY := norm_nonneg Y
  rw [norm_prod_le_iff]
  constructor
  · simp only [odeA]; nlinarith
  · simp only [odeA, norm_neg]
    calc ‖g z * Y.1 + f z * Y.2‖ ≤ ‖g z‖ * ‖Y.1‖ + ‖f z‖ * ‖Y.2‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ M * ‖Y‖ + M * ‖Y‖ := by gcongr
      _ ≤ _ := by nlinarith

theorem differentiableOn_odeA (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    {Y : ℂ → ℂ × ℂ} (hY : DifferentiableOn ℂ Y D) :
    DifferentiableOn ℂ (fun z => odeA f g z (Y z)) D :=
  hY.snd.prodMk ((hg.mul hY.fst).add (hf.mul hY.snd)).neg

/-! ### Normalized primitives and Picard iteration -/

open Classical in
/-- A primitive of `h` on `D` vanishing at `z₀` (when one exists). -/
noncomputable def prim (D : Set ℂ) (z₀ : ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  if H : ∃ F : ℂ → ℂ, F z₀ = 0 ∧ ∀ z ∈ D, HasDerivAt F (h z) z then H.choose else 0

theorem prim_spec (hD : IsSCDomain D) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) : prim D z₀ h z₀ = 0 ∧ ∀ z ∈ D, HasDerivAt (prim D z₀ h) (h z) z := by
  have H := exists_primitive_of_simplyConnected hD.isOpen hD.isConnected hD.simplyConnected hh hz₀
  simp only [prim, H, ↓reduceDIte]
  exact H.choose_spec

/-- Componentwise normalized primitive of a `ℂ²`-valued function. -/
noncomputable def primP (D : Set ℂ) (z₀ : ℂ) (Φ : ℂ → ℂ × ℂ) (z : ℂ) : ℂ × ℂ :=
  (prim D z₀ (fun ζ => (Φ ζ).1) z, prim D z₀ (fun ζ => (Φ ζ).2) z)

theorem primP_spec (hD : IsSCDomain D) {Φ : ℂ → ℂ × ℂ} (hΦ : DifferentiableOn ℂ Φ D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) : primP D z₀ Φ z₀ = 0 ∧ ∀ z ∈ D, HasDerivAt (primP D z₀ Φ) (Φ z) z := by
  obtain ⟨a0, a⟩ := prim_spec hD hΦ.fst hz₀
  obtain ⟨b0, b⟩ := prim_spec hD hΦ.snd hz₀
  exact ⟨by simp [primP, a0, b0], fun z hz => (a z hz).prodMk (b z hz)⟩

/-- Picard iterates `Y₀ = c`, `Y_{k+1}(z) = c + ∫_{z₀}^z A(ζ) Y_k(ζ) dζ`. -/
noncomputable def picard (D : Set ℂ) (z₀ : ℂ) (f g : ℂ → ℂ) (c : ℂ × ℂ) : ℕ → ℂ → ℂ × ℂ
  | 0 => fun _ => c
  | k + 1 => fun z => c + primP D z₀ (fun ζ => odeA f g ζ (picard D z₀ f g c k ζ)) z

/-- Successive differences of the Picard iterates (with the initial datum in front). -/
noncomputable def picardDiff (D : Set ℂ) (z₀ : ℂ) (f g : ℂ → ℂ) (c : ℂ × ℂ) : ℕ → ℂ → ℂ × ℂ
  | 0 => fun _ => c
  | k + 1 => fun z => picard D z₀ f g c (k + 1) z - picard D z₀ f g c k z

section Picard

variable (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
  {z₀ : ℂ} (hz₀ : z₀ ∈ D) (c : ℂ × ℂ)
include hD hf hg hz₀

theorem picard_differentiableOn (k : ℕ) : DifferentiableOn ℂ (picard D z₀ f g c k) D := by
  induction k with
  | zero => exact differentiableOn_const c
  | succ k ih =>
    intro z hz
    exact (((primP_spec hD (differentiableOn_odeA hf hg ih) hz₀).2 z hz).const_add
      c).differentiableAt.differentiableWithinAt

theorem picard_hasDerivAt (k : ℕ) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (picard D z₀ f g c (k + 1)) (odeA f g z (picard D z₀ f g c k z)) z :=
  ((primP_spec hD (differentiableOn_odeA hf hg
    (picard_differentiableOn hD hf hg hz₀ c k)) hz₀).2 z hz).const_add c

theorem picard_at (k : ℕ) : picard D z₀ f g c k z₀ = c := by
  cases k with
  | zero => rfl
  | succ k =>
    simp [picard, (primP_spec hD (differentiableOn_odeA hf hg
      (picard_differentiableOn hD hf hg hz₀ c k)) hz₀).1]

theorem picardDiff_hasDerivAt (k : ℕ) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (picardDiff D z₀ f g c (k + 1)) (odeA f g z (picardDiff D z₀ f g c k z)) z := by
  cases k with
  | zero =>
    exact (picard_hasDerivAt hD hf hg hz₀ c 0 hz).sub_const c
  | succ k =>
    have := (picard_hasDerivAt hD hf hg hz₀ c (k + 1) hz).sub
      (picard_hasDerivAt hD hf hg hz₀ c k hz)
    rwa [odeA_sub] at this

theorem picardDiff_at (k : ℕ) : picardDiff D z₀ f g c (k + 1) z₀ = 0 := by
  simp [picardDiff, picard_at hD hf hg hz₀]

end Picard

theorem picard_eq_sum (D : Set ℂ) (z₀ : ℂ) (f g : ℂ → ℂ) (c : ℂ × ℂ) (N : ℕ) (z : ℂ) :
    picard D z₀ f g c N z = c + ∑ k ∈ Finset.range N, picardDiff D z₀ f g c (k + 1) z := by
  induction N with
  | zero => simp [picard]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    simp [picardDiff]

/-! ### The basic estimate -/

theorem hasDerivAt_expTerm (C μ : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun t => C * (μ * t) ^ (k + 1) / (k + 1)!) (C * μ * (μ * t) ^ k / k !) t := by
  have := ((((hasDerivAt_id t).const_mul μ).pow (k + 1)).const_mul C).div_const
    ((k + 1)! : ℝ)
  convert this using 1
  · funext x
    simp
  · rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    simp only [id]
    field_simp

/-- Along a chain on which `‖f‖, ‖g‖ ≤ M` and the sides have length `≤ ℓ`, a sequence with
`F_{k+1}′ = A F_k` and `F_{k+1}(v₀) = 0` satisfies `‖F_k‖ ≤ C ((1 + 2M) ℓ t)^k / k!`. -/
theorem norm_iter_le {v : ℕ → ℂ} {m : ℕ} (hch : IsChain D v m) {ℓ M C : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hM0 : 0 ≤ M) (hℓ : ∀ i < m, ‖v (i + 1) - v i‖ ≤ ℓ)
    (hM : ∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1), ‖f (polySeg v i t)‖ ≤ M ∧ ‖g (polySeg v i t)‖ ≤ M)
    (F : ℕ → ℂ → ℂ × ℂ) (hF0 : ∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1), ‖F 0 (polySeg v i t)‖ ≤ C)
    (hFd : ∀ k, ∀ z ∈ D, HasDerivAt (F (k + 1)) (odeA f g z (F k z)) z)
    (hFz : ∀ k, F (k + 1) (v 0) = 0) :
    ∀ k, ∀ i < m, ∀ t ∈ Icc (i : ℝ) (i + 1),
      ‖F k (polySeg v i t)‖ ≤ C * ((1 + 2 * M) * ℓ * t) ^ k / k ! := by
  intro k
  induction k with
  | zero => intro i hi t ht; simpa using hF0 i hi t ht
  | succ k ih =>
    refine norm_le_along_chain hch hℓ (hFd k) (hFz k) (hasDerivAt_expTerm C _ k) (by simp) ?_
    intro i hi t ht
    have hA := norm_odeA_le (hM i hi t ht).1 (hM i hi t ht).2 (F k (polySeg v i t))
    calc ℓ * ‖odeA f g _ (F k _)‖
        ≤ ℓ * ((1 + 2 * M) * (C * ((1 + 2 * M) * ℓ * t) ^ k / k !)) :=
          mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left (ih i hi t ht)
            (by linarith))) hℓ0
      _ = C * ((1 + 2 * M) * ℓ) * ((1 + 2 * M) * ℓ * t) ^ k / k ! := by ring

/-! ### Chains, compact sets and bounds -/

/-- The union of the sides of a chain. -/
def chainSet (v : ℕ → ℂ) (m : ℕ) : Set ℂ := ⋃ i ∈ Finset.range m, segment ℝ (v i) (v (i + 1))

theorem isCompact_chainSet (v : ℕ → ℂ) (m : ℕ) : IsCompact (chainSet v m) :=
  (Finset.range m).isCompact_biUnion fun i _ => by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)

theorem isChain_chainSet (v : ℕ → ℂ) (m : ℕ) : IsChain (chainSet v m) v m :=
  fun i hi _ hy => mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hy⟩

theorem chainSet_subset {v : ℕ → ℂ} {m : ℕ} (hch : IsChain D v m) : chainSet v m ⊆ D :=
  iUnion₂_subset fun i hi => hch i (Finset.mem_range.1 hi)

theorem IsChain.mono {E : Set ℂ} {v : ℕ → ℂ} {m : ℕ} (h : IsChain D v m) (hDE : D ⊆ E) :
    IsChain E v m :=
  fun i hi => (h i hi).trans hDE

theorem norm_side_le_sum (v : ℕ → ℂ) {m i : ℕ} (hi : i < m) :
    ‖v (i + 1) - v i‖ ≤ ∑ j ∈ Finset.range m, ‖v (j + 1) - v j‖ :=
  Finset.single_le_sum (f := fun j => ‖v (j + 1) - v j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 hi)

theorem exists_bound_fg {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D) :
    ∃ M, 0 ≤ M ∧ ∀ z ∈ K, ‖f z‖ ≤ M ∧ ‖g z‖ ≤ M := by
  obtain ⟨Mf, hMf⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKD)
  obtain ⟨Mg, hMg⟩ := hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKD)
  exact ⟨max (max Mf Mg) 0, le_max_right _ _, fun z hz =>
    ⟨(hMf z hz).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hMg z hz).trans ((le_max_right _ _).trans (le_max_left _ _))⟩⟩

/-! ### Convergence of the Picard iterates -/

/-- The limit `c + ∑ (Y_{k+1} − Y_k)` of the Picard iterates. -/
noncomputable def picardLim (D : Set ℂ) (z₀ : ℂ) (f g : ℂ → ℂ) (c : ℂ × ℂ) (z : ℂ) : ℂ × ℂ :=
  c + ∑' k, picardDiff D z₀ f g c (k + 1) z

section Existence

variable (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
  {z₀ : ℂ} (hz₀ : z₀ ∈ D)
include hD hf hg hz₀

/-- Locally on `D`, the Picard differences are dominated by an exponential series: reach `x` by a
chain from `z₀` and every point of a small disk about `x` by one more side. -/
theorem picardDiff_local_bound (c : ℂ × ℂ) {x : ℂ} (hx : x ∈ D) :
    ∃ ρ > 0, ∃ M, 0 ≤ M ∧ (∀ z ∈ closedBall x ρ, ‖f z‖ ≤ M ∧ ‖g z‖ ≤ M) ∧ ∃ L, 0 ≤ L ∧
      ∀ k, ∀ z ∈ closedBall x ρ,
        ‖picardDiff D z₀ f g c (k + 1) z‖ ≤ ‖c‖ * (L ^ (k + 1) / (k + 1)!) := by
  obtain ⟨v, m, hv0, hvm, hch⟩ := exists_chain_of_polygonallyJoined
    (((dlmf_1_9_ii_domain hD.isOpen).mp hD.isConnected).2 z₀ hz₀ x hx)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD.isOpen x hx
  have hρ0 : 0 < r / 2 := by positivity
  have hcb : closedBall x (r / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hball
  have hKc : IsCompact (chainSet v m ∪ closedBall x (r / 2)) :=
    (isCompact_chainSet v m).union (isCompact_closedBall x _)
  have hKD : chainSet v m ∪ closedBall x (r / 2) ⊆ D := union_subset (chainSet_subset hch) hcb
  obtain ⟨M, hM0, hM⟩ := exists_bound_fg hKc hKD hf hg
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = ∑ j ∈ Finset.range m, ‖v (j + 1) - v j‖ + r / 2 := ⟨_, rfl⟩
  have hS : 0 ≤ ∑ j ∈ Finset.range m, ‖v (j + 1) - v j‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hℓ0 : 0 ≤ ℓ := by linarith
  refine ⟨r / 2, hρ0, M, hM0, fun z hz => hM z (subset_union_right hz),
    (1 + 2 * M) * ℓ * (m + 1), mul_nonneg (mul_nonneg (by linarith) hℓ0) (by positivity),
    fun k z hz => ?_⟩
  have hvu : v m = chainSeg x z 0 := by simp [chainSeg, hvm]
  have e0 := chainAppend_add hvu 0
  have e1 := chainAppend_add hvu 1
  rw [add_zero] at e0
  have hwK : IsChain (chainSet v m ∪ closedBall x (r / 2)) (chainAppend v m (chainSeg x z))
      (m + 1) :=
    isChain_append hvu ((isChain_chainSet v m).mono subset_union_left)
      (isChain_seg (((convex_closedBall x _).segment_subset (mem_closedBall_self hρ0.le)
        hz).trans subset_union_right))
  have hwℓ : ∀ i < m + 1, ‖chainAppend v m (chainSeg x z) (i + 1) -
      chainAppend v m (chainSeg x z) i‖ ≤ ℓ := by
    intro i hi
    rcases (Nat.lt_succ_iff.mp hi).lt_or_eq with him | rfl
    · simp only [chainAppend, him.le, Nat.succ_le_of_lt him, ↓reduceIte]
      linarith [norm_side_le_sum v him]
    · rw [e1, e0]
      simp only [chainSeg, one_ne_zero, ↓reduceIte]
      rw [mem_closedBall, dist_eq_norm] at hz
      linarith
  have hb := norm_iter_le (f := f) (g := g) (C := ‖c‖) (hwK.mono hKD) hℓ0 hM0 hwℓ
    (fun i hi t ht => hM _ (polySeg_mem hwK hi ht)) (picardDiff D z₀ f g c)
    (fun _ _ _ _ => le_rfl) (fun k z hz => picardDiff_hasDerivAt hD hf hg hz₀ c k hz)
    (fun k => by rw [chainAppend_zero, hv0]; exact picardDiff_at hD hf hg hz₀ c k)
    (k + 1) m (by omega) (m + 1) ⟨by linarith, le_rfl⟩
  rw [polySeg_right, e1] at hb
  simp only [chainSeg, one_ne_zero, ↓reduceIte] at hb
  exact hb.trans (le_of_eq (by ring))

theorem picard_tendstoUniformlyOn_local (c : ℂ × ℂ) {x : ℂ} (hx : x ∈ D) :
    ∃ ρ > 0, ∃ M, 0 ≤ M ∧ (∀ z ∈ closedBall x ρ, ‖f z‖ ≤ M ∧ ‖g z‖ ≤ M) ∧
      TendstoUniformlyOn (picard D z₀ f g c) (picardLim D z₀ f g c) atTop (closedBall x ρ) := by
  obtain ⟨ρ, hρ, M, hM0, hM, L, -, hb⟩ := picardDiff_local_bound hD hf hg hz₀ c hx
  refine ⟨ρ, hρ, M, hM0, hM, ?_⟩
  have hsum : Summable fun k : ℕ => ‖c‖ * (L ^ (k + 1) / (k + 1)!) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial L)).mul_left _
  have hU := tendstoUniformlyOn_tsum_nat hsum (fun k z hz => hb k z hz)
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro ε hε
  filter_upwards [hU ε hε] with N hN z hz
  rw [picard_eq_sum, picardLim, dist_add_left]
  exact hN z hz

theorem picardLim_hasDerivAt (c : ℂ × ℂ) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (picardLim D z₀ f g c) (odeA f g z (picardLim D z₀ f g c z)) z := by
  have hloc := fun {x} (hx : x ∈ D) => picard_tendstoUniformlyOn_local hD hf hg hz₀ c hx
  have hP : TendstoLocallyUniformlyOn (picard D z₀ f g c) (picardLim D z₀ f g c) atTop D := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨ρ, hρ, -, -, -, hU⟩ := hloc hx
    exact ⟨closedBall x ρ, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hρ),
      Metric.tendstoUniformlyOn_iff.mp hU ε hε⟩
  have hA : TendstoLocallyUniformlyOn (fun n z => odeA f g z (picard D z₀ f g c n z))
      (fun z => odeA f g z (picardLim D z₀ f g c z)) atTop D := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨ρ, hρ, M, hM0, hM, hU⟩ := hloc hx
    refine ⟨closedBall x ρ, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hρ), ?_⟩
    have hpos : 0 < 1 + 2 * M := by linarith
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU (ε / (1 + 2 * M)) (div_pos hε hpos)]
      with n hn y hy
    have hny := hn y hy
    rw [dist_eq_norm] at hny ⊢
    rw [odeA_sub]
    calc _ ≤ (1 + 2 * M) * ‖picardLim D z₀ f g c y - picard D z₀ f g c n y‖ :=
          norm_odeA_le (hM y hy).1 (hM y hy).2 _
      _ < (1 + 2 * M) * (ε / (1 + 2 * M)) := by gcongr
      _ = ε := by field_simp
  exact hasDerivAt_of_tendstoLocallyUniformlyOn (f := fun n => picard D z₀ f g c (n + 1))
    hD.isOpen hA (Eventually.of_forall fun n x hx => picard_hasDerivAt hD hf hg hz₀ c n hx)
    (fun x hx => (hP.tendsto_at hx).comp (tendsto_add_atTop_nat 1)) hz

theorem picardLim_at (c : ℂ × ℂ) : picardLim D z₀ f g c z₀ = c := by
  simp [picardLim, picardDiff_at hD hf hg hz₀]

/-- **DLMF §1.13(i)** (existence): (1.13.1) has an analytic solution in `D` with any prescribed
`w(z₀)` and `w′(z₀)`. -/
theorem dlmf_1_13_i_exists (a b : ℂ) :
    ∃ w, IsODESolution D f g w ∧ w z₀ = a ∧ deriv w z₀ = b := by
  have hY := fun z (hz : z ∈ D) => picardLim_hasDerivAt hD hf hg hz₀ (a, b) hz
  have h1 : ∀ z ∈ D, HasDerivAt (fun z => (picardLim D z₀ f g (a, b) z).1)
      (picardLim D z₀ f g (a, b) z).2 z := fun z hz => by
    simpa [odeA, Function.comp_def] using hasFDerivAt_fst.comp_hasDerivAt z (hY z hz)
  have h2 : ∀ z ∈ D, HasDerivAt (fun z => (picardLim D z₀ f g (a, b) z).2)
      (-(f z * (picardLim D z₀ f g (a, b) z).2 + g z * (picardLim D z₀ f g (a, b) z).1)) z :=
    fun z hz => by
      have := hasFDerivAt_snd.comp_hasDerivAt z (hY z hz)
      simp only [odeA, Function.comp_def, ContinuousLinearMap.coe_snd'] at this
      exact this.congr_deriv (by ring)
  refine ⟨_, isODESolution_of_hasDerivAt hD.isOpen fun z hz => ⟨h1 z hz, h2 z hz⟩, ?_, ?_⟩
  · simp [picardLim_at hD hf hg hz₀]
  · rw [(h1 z₀ hz₀).deriv, picardLim_at hD hf hg hz₀]

/-- **DLMF §1.13(i)** (uniqueness): a solution with `w(z₀) = w′(z₀) = 0` vanishes in `D`. -/
theorem dlmf_1_13_i_eq_zero {w : ℂ → ℂ} (hw : IsODESolution D f g w) (h0 : w z₀ = 0)
    (h1 : deriv w z₀ = 0) : ∀ z ∈ D, w z = 0 := by
  have hY : ∀ z ∈ D, HasDerivAt (fun z => (w z, deriv w z))
      (odeA f g z (w z, deriv w z)) z := fun z hz => by
    obtain ⟨a, b⟩ := hw.hasDerivAt hD.isOpen hz
    refine (a.prodMk b).congr_deriv ?_
    simp only [odeA, Prod.mk.injEq, true_and]
    ring
  have hY0 : (w z₀, deriv w z₀) = 0 := by simp [h0, h1]
  intro z hz
  obtain ⟨v, m, hv0, hvm, hch⟩ := exists_chain_of_polygonallyJoined
    (((dlmf_1_9_ii_domain hD.isOpen).mp hD.isConnected).2 z₀ hz₀ z hz)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [← hvm, hv0, h0]
  obtain ⟨M, hM0, hM⟩ := exists_bound_fg (isCompact_chainSet v m) (chainSet_subset hch) hf hg
  have hYc : ContinuousOn (fun z => (w z, deriv w z)) D :=
    fun z hz => (hY z hz).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_chainSet v m).exists_bound_of_continuousOn
    (hYc.mono (chainSet_subset hch))
  have hℓ0 : 0 ≤ ∑ j ∈ Finset.range m, ‖v (j + 1) - v j‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK := isChain_chainSet v m
  have hb := norm_iter_le hch hℓ0 hM0 (fun i hi => norm_side_le_sum v hi)
    (fun i hi t ht => hM _ (polySeg_mem hK hi ht)) (fun _ z => (w z, deriv w z))
    (fun i hi t ht => hC _ (polySeg_mem hK hi ht)) (fun _ z hz => hY z hz)
    (fun _ => by rw [hv0]; exact hY0)
  have hlast : polySeg v (m - 1) ((m - 1 : ℕ) + 1) = z := by
    rw [polySeg_right, Nat.sub_add_cancel hm, hvm]
  obtain ⟨x, hx⟩ : ∃ x, x = (1 + 2 * M) * (∑ j ∈ Finset.range m, ‖v (j + 1) - v j‖) *
      (((m - 1 : ℕ) : ℝ) + 1) := ⟨_, rfl⟩
  have hle : ∀ k : ℕ, ‖(w z, deriv w z)‖ ≤ C * (x ^ k / k !) := fun k => by
    have := hb k (m - 1) (by omega) _ ⟨by linarith, le_rfl⟩
    rw [hlast, mul_div_assoc] at this
    rwa [hx]
  have hlim : Tendsto (fun k : ℕ => C * (x ^ k / k !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop x).const_mul C
  have hYz := norm_le_zero_iff.mp (ge_of_tendsto' hlim hle)
  exact congrArg Prod.fst hYz

/-- **DLMF §1.13(i)** (uniqueness): solutions with the same `w(z₀)` and `w′(z₀)` agree in `D`. -/
theorem dlmf_1_13_i_unique {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) (h0 : w₁ z₀ = w₂ z₀) (h1 : deriv w₁ z₀ = deriv w₂ z₀) :
    ∀ z ∈ D, w₁ z = w₂ z := by
  have := dlmf_1_13_i_eq_zero hD hf hg hz₀ (h₁.linearCombo hD.isOpen h₂ 1 (-1))
    (by rw [h0]; ring)
    (by rw [(h₁.hasDerivAt_linearCombo hD.isOpen h₂ 1 (-1) hz₀).deriv, h1]; ring)
  intro z hz
  linear_combination this z hz

end Existence

/-- **DLMF §1.13(i)**: (1.13.1) has infinitely many analytic solutions in `D` (counted as
functions on `D`). -/
theorem dlmf_1_13_i_infinite (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    (hg : DifferentiableOn ℂ g D) :
    Set.Infinite ((fun w (z : D) => w z) '' {w | IsODESolution D f g w}) := by
  obtain ⟨z₀, hz₀⟩ := hD.isConnected.nonempty
  choose W hW using fun a : ℂ => dlmf_1_13_i_exists hD hf hg hz₀ a 0
  refine Set.infinite_of_injective_forall_mem (f := fun a (z : D) => W a z) ?_
    fun a => ⟨W a, (hW a).1, rfl⟩
  intro a b hab
  have := congrFun hab ⟨z₀, hz₀⟩
  simp only at this
  rwa [(hW a).2.1, (hW b).2.1] at this

/-! ### Fundamental pairs and the Wronskian -/

/-- **DLMF (1.13.2)**: `w₁, w₂` are a *fundamental pair* if every solution is `A w₁ + B w₂`. -/
def IsFundamentalPair (D : Set ℂ) (f g w₁ w₂ : ℂ → ℂ) : Prop :=
  IsODESolution D f g w₁ ∧ IsODESolution D f g w₂ ∧
    ∀ w, IsODESolution D f g w → ∃ A B : ℂ, ∀ z ∈ D, w z = A * w₁ z + B * w₂ z

/-- **DLMF (1.13.2)**. -/
theorem dlmf_1_13_2 {w₁ w₂ : ℂ → ℂ} (h : IsFundamentalPair D f g w₁ w₂) {w : ℂ → ℂ}
    (hw : IsODESolution D f g w) : ∃ A B : ℂ, ∀ z ∈ D, w z = A * w₁ z + B * w₂ z :=
  h.2.2 w hw

/-- **DLMF (1.13.4)**: the Wronskian `𝒲{w₁, w₂} = w₁ w₂′ − w₂ w₁′`. -/
noncomputable def wronskian (w₁ w₂ : ℂ → ℂ) (z : ℂ) : ℂ := w₁ z * deriv w₂ z - w₂ z * deriv w₁ z

/-- **DLMF (1.13.4)**: the determinant form. -/
theorem dlmf_1_13_4 (w₁ w₂ : ℂ → ℂ) (z : ℂ) :
    wronskian w₁ w₂ z = !![w₁ z, w₂ z; deriv w₁ z, deriv w₂ z].det := by
  rw [Matrix.det_fin_two_of]
  rfl

/-- **DLMF §1.13(i)**: the `n`-argument Wronskian `𝒲{w₁, …, wₙ} = det [w_k^{(j−1)}]`. -/
noncomputable def wronskianN {n : ℕ} (w : Fin n → ℂ → ℂ) (z : ℂ) : ℂ :=
  (Matrix.of fun j k : Fin n => iteratedDeriv j (w k) z).det

theorem wronskianN_two (w₁ w₂ : ℂ → ℂ) (z : ℂ) : wronskianN ![w₁, w₂] z = wronskian w₁ w₂ z := by
  simp [wronskianN, Matrix.det_fin_two, wronskian, iteratedDeriv_one]

/-- The basic algebra behind Cramer's rule. -/
theorem exists_kernel_of_det_eq_zero {p q p' q' : ℂ} (h : p * q' - q * p' = 0) :
    ∃ A B : ℂ, ¬(A = 0 ∧ B = 0) ∧ A * p + B * q = 0 ∧ A * p' + B * q' = 0 := by
  by_cases h1 : p = 0 ∧ q = 0
  · by_cases h2 : p' = 0 ∧ q' = 0
    · exact ⟨1, 0, by simp, by simp [h1.1], by simp [h2.1]⟩
    · exact ⟨q', -p', fun h => h2 ⟨by simpa using h.2, h.1⟩, by linear_combination h, by ring⟩
  · exact ⟨q, -p, fun h => h1 ⟨by simpa using h.2, h.1⟩, by ring, by linear_combination -h⟩

theorem wronskian_hasDerivAt (hDo : IsOpen D) {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (wronskian w₁ w₂) (-f z * wronskian w₁ w₂ z) z := by
  obtain ⟨a1, a2⟩ := h₁.hasDerivAt hDo hz
  obtain ⟨b1, b2⟩ := h₂.hasDerivAt hDo hz
  exact ((a1.mul b2).sub (b1.mul a2)).congr_deriv (by simp only [wronskian]; ring)

/-- `W′ = −q W` and `F′ = q` on a connected open set force `W = c e^{−F}`. -/
theorem exists_eq_mul_exp_neg (hDo : IsOpen D) (hDc : IsPreconnected D) {W q F : ℂ → ℂ}
    (hW : ∀ z ∈ D, HasDerivAt W (-q z * W z) z) (hF : ∀ z ∈ D, HasDerivAt F (q z) z) :
    ∃ c, ∀ z ∈ D, W z = c * exp (-F z) := by
  have hP : ∀ z ∈ D, HasDerivAt (fun z => W z * exp (F z)) 0 z := fun z hz =>
    ((hW z hz).mul (hF z hz).cexp).congr_deriv (by ring)
  obtain ⟨c, hc⟩ := hDo.exists_is_const_of_deriv_eq_zero hDc
    (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hP z hz).deriv)
  refine ⟨c, fun z hz => ?_⟩
  rw [← hc z hz, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- **DLMF (1.13.5)** (Abel's identity): `𝒲{w₁, w₂} = c e^{−∫ f(z) dz}` for any primitive
`∫ f(z) dz` of `f` in the (connected, open) domain. -/
theorem dlmf_1_13_5 (hDo : IsOpen D) (hDc : IsPreconnected D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsODESolution D f g w₁) (h₂ : IsODESolution D f g w₂) {F : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) :
    ∃ c, ∀ z ∈ D, wronskian w₁ w₂ z = c * exp (-F z) :=
  exists_eq_mul_exp_neg hDo hDc (fun _ hz => wronskian_hasDerivAt hDo h₁ h₂ hz) hF

/-- **DLMF (1.13.5)** on a simply-connected domain, with `∫ f(z) dz` normalized to vanish at `z₀`:
`𝒲(z) = 𝒲(z₀) e^{−∫_{z₀}^z f}`. In particular `𝒲` vanishes either nowhere or identically. -/
theorem dlmf_1_13_5_primitive (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁) (h₂ : IsODESolution D f g w₂) :
    ∃ F : ℂ → ℂ, F z₀ = 0 ∧ (∀ z ∈ D, HasDerivAt F (f z) z) ∧
      ∀ z ∈ D, wronskian w₁ w₂ z = wronskian w₁ w₂ z₀ * exp (-F z) := by
  obtain ⟨F, hF0, hF⟩ := exists_primitive_of_simplyConnected hD.isOpen hD.isConnected
    hD.simplyConnected hf hz₀
  obtain ⟨c, hc⟩ := dlmf_1_13_5 hD.isOpen hD.isConnected.isPreconnected h₁ h₂ hF
  have : wronskian w₁ w₂ z₀ = c := by simpa [hF0] using hc z₀ hz₀
  exact ⟨F, hF0, hF, fun z hz => by rw [this]; exact hc z hz⟩

theorem wronskian_eq_zero_or_ne_zero (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D)
    {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁) (h₂ : IsODESolution D f g w₂) :
    (∀ z ∈ D, wronskian w₁ w₂ z = 0) ∨ ∀ z ∈ D, wronskian w₁ w₂ z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := hD.isConnected.nonempty
  obtain ⟨F, -, -, hW⟩ := dlmf_1_13_5_primitive hD hf hz₀ h₁ h₂
  by_cases h : wronskian w₁ w₂ z₀ = 0
  · exact Or.inl fun z hz => by rw [hW z hz, h, zero_mul]
  · exact Or.inr fun z hz => by rw [hW z hz]; exact mul_ne_zero h (Complex.exp_ne_zero _)

/-- **DLMF §1.13(i)**: if `f = 0`, the Wronskian is constant. -/
theorem dlmf_1_13_i_wronskian_const (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hf0 : ∀ z ∈ D, f z = 0) {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) : ∃ c, ∀ z ∈ D, wronskian w₁ w₂ z = c := by
  obtain ⟨c, hc⟩ := dlmf_1_13_5 hDo hDc h₁ h₂ (F := fun _ => 0) fun z hz => by
    rw [hf0 z hz]; exact hasDerivAt_const z 0
  exact ⟨c, fun z hz => by simpa using hc z hz⟩

section Fundamental

variable (hD : IsSCDomain D) (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
include hD hf hg

theorem isFundamentalPair_of_wronskian_ne_zero {z₀ : ℂ} (hz₀ : z₀ ∈ D) {w₁ w₂ : ℂ → ℂ}
    (h₁ : IsODESolution D f g w₁) (h₂ : IsODESolution D f g w₂)
    (hW : wronskian w₁ w₂ z₀ ≠ 0) : IsFundamentalPair D f g w₁ w₂ := by
  refine ⟨h₁, h₂, fun w hw => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (w z₀ * deriv w₂ z₀ - w₂ z₀ * deriv w z₀) / wronskian w₁ w₂ z₀ :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (w₁ z₀ * deriv w z₀ - deriv w₁ z₀ * w z₀) / wronskian w₁ w₂ z₀ :=
    ⟨_, rfl⟩
  have hc := h₁.linearCombo hD.isOpen h₂ A B
  have hAW : A * wronskian w₁ w₂ z₀ = w z₀ * deriv w₂ z₀ - w₂ z₀ * deriv w z₀ := by
    rw [hA, div_mul_cancel₀ _ hW]
  have hBW : B * wronskian w₁ w₂ z₀ = w₁ z₀ * deriv w z₀ - deriv w₁ z₀ * w z₀ := by
    rw [hB, div_mul_cancel₀ _ hW]
  have := dlmf_1_13_i_eq_zero hD hf hg hz₀ (hw.linearCombo hD.isOpen hc 1 (-1)) ?_ ?_
  · exact ⟨A, B, fun z hz => by linear_combination this z hz⟩
  · refine (mul_left_inj' hW).mp ?_
    unfold wronskian at hAW hBW ⊢
    linear_combination (-(w₁ z₀)) * hAW - w₂ z₀ * hBW
  · rw [(hw.hasDerivAt_linearCombo hD.isOpen hc 1 (-1) hz₀).deriv,
      (h₁.hasDerivAt_linearCombo hD.isOpen h₂ A B hz₀).deriv]
    refine (mul_left_inj' hW).mp ?_
    unfold wronskian at hAW hBW ⊢
    linear_combination (-(deriv w₁ z₀)) * hAW - deriv w₂ z₀ * hBW

/-- **DLMF (1.13.3)**: the solutions with `w₁(z₀) = 1, w₁′(z₀) = 0, w₂(z₀) = 0, w₂′(z₀) = 1`
form a fundamental pair. -/
theorem dlmf_1_13_3 {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ w₁ w₂, IsFundamentalPair D f g w₁ w₂ ∧
      w₁ z₀ = 1 ∧ deriv w₁ z₀ = 0 ∧ w₂ z₀ = 0 ∧ deriv w₂ z₀ = 1 := by
  obtain ⟨w₁, h₁, a0, a1⟩ := dlmf_1_13_i_exists hD hf hg hz₀ 1 0
  obtain ⟨w₂, h₂, b0, b1⟩ := dlmf_1_13_i_exists hD hf hg hz₀ 0 1
  refine ⟨w₁, w₂, isFundamentalPair_of_wronskian_ne_zero hD hf hg hz₀ h₁ h₂ ?_, a0, a1, b0, b1⟩
  simp [wronskian, a0, a1, b0, b1]

/-- **DLMF (1.13.6)**: for two solutions, the following are equivalent: they form a fundamental
pair; their Wronskian does not vanish in `D`; they are linearly independent. -/
theorem dlmf_1_13_6 {w₁ w₂ : ℂ → ℂ} (h₁ : IsODESolution D f g w₁)
    (h₂ : IsODESolution D f g w₂) :
    List.TFAE [IsFundamentalPair D f g w₁ w₂, ∀ z ∈ D, wronskian w₁ w₂ z ≠ 0,
      ∀ A B : ℂ, (∀ z ∈ D, A * w₁ z + B * w₂ z = 0) → A = 0 ∧ B = 0] := by
  obtain ⟨z₀, hz₀⟩ := hD.isConnected.nonempty
  have hderiv : ∀ {u : ℂ → ℂ} {a b : ℂ}, (∀ z ∈ D, u z = a * w₁ z + b * w₂ z) →
      deriv u z₀ = a * deriv w₁ z₀ + b * deriv w₂ z₀ := by
    intro u a b h
    have : u =ᶠ[𝓝 z₀] fun z => a * w₁ z + b * w₂ z := by
      filter_upwards [hD.isOpen.mem_nhds hz₀] with z hz using h z hz
    rw [this.deriv_eq, (h₁.hasDerivAt_linearCombo hD.isOpen h₂ a b hz₀).deriv]
  tfae_have 2 → 1 := fun hW =>
    isFundamentalPair_of_wronskian_ne_zero hD hf hg hz₀ h₁ h₂ (hW z₀ hz₀)
  tfae_have 1 → 3 := by
    rintro ⟨-, -, hfund⟩ A B hAB
    obtain ⟨u₁, hu₁, hu₁0, hu₁1⟩ := dlmf_1_13_i_exists hD hf hg hz₀ 1 0
    obtain ⟨u₂, hu₂, hu₂0, hu₂1⟩ := dlmf_1_13_i_exists hD hf hg hz₀ 0 1
    obtain ⟨a, b, hab⟩ := hfund u₁ hu₁
    obtain ⟨c, d, hcd⟩ := hfund u₂ hu₂
    have e1 := hab z₀ hz₀
    have e2 := hderiv hab
    have e3 := hcd z₀ hz₀
    have e4 := hderiv hcd
    rw [hu₁0] at e1
    rw [hu₁1] at e2
    rw [hu₂0] at e3
    rw [hu₂1] at e4
    have hW : wronskian w₁ w₂ z₀ * (a * d - b * c) = 1 := by
      unfold wronskian
      linear_combination -(c * deriv w₁ z₀ + d * deriv w₂ z₀) * e1 - e4 +
        (c * w₁ z₀ + d * w₂ z₀) * e2
    have hW0 := left_ne_zero_of_mul_eq_one hW
    have hz := hAB z₀ hz₀
    have hz' : A * deriv w₁ z₀ + B * deriv w₂ z₀ = 0 := by
      have := hderiv (u := fun _ => 0) fun z hz => (hAB z hz).symm
      rw [deriv_const] at this
      exact this.symm
    have hA : A * wronskian w₁ w₂ z₀ = 0 := by
      unfold wronskian
      linear_combination deriv w₂ z₀ * hz - w₂ z₀ * hz'
    have hB : B * wronskian w₁ w₂ z₀ = 0 := by
      unfold wronskian
      linear_combination w₁ z₀ * hz' - deriv w₁ z₀ * hz
    exact ⟨(mul_eq_zero.mp hA).resolve_right hW0, (mul_eq_zero.mp hB).resolve_right hW0⟩
  tfae_have 3 → 2 := by
    intro hli z₁ hz₁ hW
    obtain ⟨A, B, hne, hv, hd⟩ := exists_kernel_of_det_eq_zero hW
    have := dlmf_1_13_i_eq_zero hD hf hg hz₁ (h₁.linearCombo hD.isOpen h₂ A B) hv
      (by rw [(h₁.hasDerivAt_linearCombo hD.isOpen h₂ A B hz₁).deriv]; exact hd)
    exact hne (hli A B this)
  tfae_finish

end Fundamental

/-! ### Abel's identity for `n`th-order equations -/

/-- **Jacobi's formula**: the derivative of a determinant is the sum of the determinants with one
row differentiated. -/
theorem hasDerivAt_det {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℂ → Matrix ι ι ℂ}
    {M' : Matrix ι ι ℂ} {z : ℂ} (hM : ∀ i j, HasDerivAt (fun z => M z i j) (M' i j) z) :
    HasDerivAt (fun z => (M z).det) (∑ i, ((M z).updateRow i (M' i)).det) z := by
  let d : ContinuousMultilinearMap ℂ (fun _ : ι => ι → ℂ) ℂ :=
    { toMultilinearMap := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap
      cont := continuous_id.matrix_det }
  have hrows : HasDerivAt (fun z => (M z : ι → ι → ℂ)) M' z :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hM i j
  have := (d.hasFDerivAt (M z)).comp_hasDerivAt z hrows
  refine this.congr_deriv ?_
  erw [ContinuousMultilinearMap.linearDeriv_apply]
  rfl

/-- **DLMF §1.13(i)**: `w` solves `w^{(n+1)} + ∑_{j ≤ n} a_j(z) w^{(j)} = 0` in `D`. -/
def IsODESolutionN (D : Set ℂ) {n : ℕ} (a : Fin (n + 1) → ℂ → ℂ) (w : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ w D ∧
    ∀ z ∈ D, iteratedDeriv (n + 1) w z + ∑ j, a j z * iteratedDeriv j w z = 0

theorem hasDerivAt_iteratedDeriv (hDo : IsOpen D) {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w D)
    (j : ℕ) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (iteratedDeriv j w) (iteratedDeriv (j + 1) w z) z := by
  rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
  exact (((hw.analyticOnNhd hDo).iterated_deriv j).differentiableOn.differentiableAt
    (hDo.mem_nhds hz)).hasDerivAt

theorem wronskianN_hasDerivAt (hDo : IsOpen D) {n : ℕ} {a : Fin (n + 1) → ℂ → ℂ}
    {w : Fin (n + 1) → ℂ → ℂ} (hw : ∀ k, IsODESolutionN D a (w k)) {z : ℂ} (hz : z ∈ D) :
    HasDerivAt (wronskianN w) (-a (Fin.last n) z * wronskianN w z) z := by
  have h := hasDerivAt_det
    (M := fun z => Matrix.of fun j k : Fin (n + 1) => iteratedDeriv j (w k) z)
    (M' := Matrix.of fun j k : Fin (n + 1) => iteratedDeriv (j + 1) (w k) z)
    (fun j k => hasDerivAt_iteratedDeriv hDo (hw k).1 j hz)
  refine h.congr_deriv ?_
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin n, ((Matrix.of fun j k : Fin (n + 1) => iteratedDeriv j (w k) z).updateRow
      i.castSucc ((Matrix.of fun j k : Fin (n + 1) => iteratedDeriv (j + 1) (w k) z)
        i.castSucc)).det = 0 := fun i => by
    have hi : i.castSucc < i.succ := Fin.castSucc_lt_succ
    refine Matrix.det_zero_of_row_eq hi.ne ?_
    ext k
    simp [Matrix.updateRow_ne hi.ne']
  have h2 : (Matrix.of fun j k : Fin (n + 1) => iteratedDeriv (j + 1) (w k) z) (Fin.last n) =
      ∑ i, (-a i z) • (Matrix.of fun j k : Fin (n + 1) => iteratedDeriv j (w k) z) i := by
    ext k
    simp only [Matrix.of_apply, Fin.val_last, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      neg_mul, Finset.sum_neg_distrib]
    linear_combination (hw k).2 z hz
  rw [Finset.sum_eq_zero fun i _ => h1 i, zero_add, h2, Matrix.det_updateRow_sum, smul_eq_mul]
  rfl

/-- **DLMF §1.13(i)** (Abel's identity for `n`th-order equations): for solutions
`w₁, …, w_{n+1}` of `w^{(n+1)} + ∑ a_j w^{(j)} = 0`, `𝒲 = c e^{−∫ a_n(z) dz}`. -/
theorem dlmf_1_13_5_orderN (hDo : IsOpen D) (hDc : IsPreconnected D) {n : ℕ}
    {a : Fin (n + 1) → ℂ → ℂ} {w : Fin (n + 1) → ℂ → ℂ} (hw : ∀ k, IsODESolutionN D a (w k))
    {F : ℂ → ℂ} (hF : ∀ z ∈ D, HasDerivAt F (a (Fin.last n) z) z) :
    ∃ c, ∀ z ∈ D, wronskianN w z = c * exp (-F z) :=
  exists_eq_mul_exp_neg hDo hDc (fun _ hz => wronskianN_hasDerivAt hDo hw hz) hF

/-- **DLMF §1.13(i)** (Abel's identity, general leading coefficient): for solutions of
`∑_{j ≤ n+1} b_j(z) w^{(j)} = 0` with `b_{n+1}` nonvanishing, `𝒲 = c e^{−∫ b_n / b_{n+1}}`. -/
theorem dlmf_1_13_5_orderN_general (hDo : IsOpen D) (hDc : IsPreconnected D) {n : ℕ}
    {b : Fin (n + 2) → ℂ → ℂ} (hb : ∀ z ∈ D, b (Fin.last (n + 1)) z ≠ 0)
    {w : Fin (n + 1) → ℂ → ℂ} (hw : ∀ k, DifferentiableOn ℂ (w k) D)
    (heq : ∀ k, ∀ z ∈ D, ∑ j, b j z * iteratedDeriv j (w k) z = 0) {F : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (b (Fin.last n).castSucc z / b (Fin.last (n + 1)) z) z) :
    ∃ c, ∀ z ∈ D, wronskianN w z = c * exp (-F z) := by
  refine dlmf_1_13_5_orderN hDo hDc (a := fun j z => b j.castSucc z / b (Fin.last (n + 1)) z)
    (fun k => ⟨hw k, fun z hz => ?_⟩) hF
  have h := heq k z hz
  rw [Fin.sum_univ_castSucc] at h
  have hz' := hb z hz
  simp only [Fin.val_castSucc, Fin.val_last] at h ⊢
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp
  linear_combination h

end Azurite.DLMF
