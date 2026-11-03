/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11TerminantAsymp

/-!
# DLMF §2.11(iv): Stokes phenomenon

* Two expansions in `π/2 < ph z < 3π/2` (`dlmf_2_11_iv_two_expansions`): 2.11.6 and 2.11.7 both
  hold in every closed subsector, although `E_p` is analytic there (`differentiable_genExpInt`):
  the change of form is the Stokes phenomenon.
* The function `c(θ)` of 2.11.16 (`stokesC`): `c(θ)² = 2(1 + e^{iθ} + i(θ − π))`
  (`stokesC_sq`), continuous on `(−π, 3π)` (`continuousOn_stokesC`) with `c(θ) ∼ π − θ` as
  `θ → π` (`tendsto_stokesC_div`), and it is the only such branch (`stokesC_unique`).
* "if `0 ≤ θ ≤ π − δ`, then `c(θ)` lies in the right half-plane" and "when
  `π + δ ≤ θ ≤ 3π − δ`, `c(θ)` is in the left half-plane": `stokesC_re_pos` (all of `(−π, π)`),
  `stokesC_re_neg` (all of `(π, 3π)`).
* The Gaussian factor of `erfc(√(ρ/2) c(θ))` (7.12.1) has exactly the size of the other terms of
  2.11.15: `|exp(−(√(ρ/2) c(θ))²)| = |e^{−ρ−z}|`, `z = ρe^{iθ}` (`dlmf_2_11_iv_same_order`); it is
  exponentially small except on `θ = π` (`norm_exp_neg_stokes_le`).
* Stokes lines: the ray `θ = π` is where `e^{−z}` achieves maximum dominance over powers of `z`,
  `|e^{−z}| = e^{−|z| cos θ} ≤ e^{|z|}` with equality exactly on `θ = π + 2πk`
  (`stokes_line_max_dominance`).

Not formalized: the asymptotics of `erfc` itself (§7.12, not yet available), hence the smooth
switching and the accuracy claims on `θ = π` (they rest on 2.11.15, deferred in §2.11(iii)), and
Figure 2.11.1.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Two expansions in one sector -/

/-- **Two different asymptotic expansions, 2.11.6 and 2.11.7, are available in
`π/2 < ph z < 3π/2`.** -/
theorem dlmf_2_11_iv_two_expansions (p : ℂ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C₁ C₂ : ℝ, ∀ w : ℂ, π / 2 + δ ≤ w.im → w.im ≤ 3 * π / 2 - δ → 0 ≤ w.re →
      ‖genExpInt p w - cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
          (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s‖ ≤
        C₁ * (‖cexp (-cexp w)‖ / ‖cexp w‖ ^ (n + 1)) ∧
      ‖genExpInt p w - 2 * π * I * cexp (-(p * π * I)) / Complex.Gamma p * cexp ((p - 1) * w) -
          cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
            (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s‖ ≤
        C₂ * (‖cexp (-cexp w)‖ / ‖cexp w‖ ^ (n + 1)) := by
  obtain ⟨C₁, h₁⟩ := dlmf_2_11_6 p n hδ hδ'
  obtain ⟨C₂, h₂⟩ := dlmf_2_11_7 p n hδ hδ'
  refine ⟨C₁, C₂, fun w hw₁ hw₂ hre => ⟨h₁ w ?_ hre, h₂ w hw₁ (by linarith [Real.pi_pos]) hre⟩⟩
  rw [abs_le]; constructor <;> linarith [Real.pi_pos]

/-! ### The function `c(θ)` -/

/-- `c(θ)² = 2(1 + e^{iθ} + i(θ − π))` (2.11.16). -/
noncomputable def stokesQ (θ : ℝ) : ℂ := 2 * (1 + cexp (θ * I) + I * (θ - π))

/-- **DLMF 2.11.16**: `c(θ) = (π − θ) (c(θ)²/(θ − π)²)^{1/2}` (principal root), `c(π) = 0`: the
branch of `√(2(1 + e^{iθ} + i(θ − π)))` continuous on `(−π, 3π)` with `c(θ) ∼ π − θ`. -/
noncomputable def stokesC (θ : ℝ) : ℂ :=
  if θ = π then 0 else ((π - θ : ℝ) : ℂ) * (stokesQ θ / ((θ - π : ℝ) : ℂ) ^ 2) ^ (2⁻¹ : ℂ)

theorem stokesQ_re (θ : ℝ) : (stokesQ θ).re = 2 * (1 + Real.cos θ) := by
  simp [stokesQ, Complex.exp_ofReal_mul_I_re]

theorem stokesQ_pi : stokesQ π = 0 := by
  rw [stokesQ, Complex.exp_pi_mul_I]; simp

/-- `Re(c(θ)²/(θ − π)²) > 0` for `θ ∈ (−π, 3π) ∖ {π}`. -/
theorem stokesR_re_pos {θ : ℝ} (h₁ : -π < θ) (h₂ : θ < 3 * π) (hne : θ ≠ π) :
    0 < (stokesQ θ / ((θ - π : ℝ) : ℂ) ^ 2).re := by
  have hs : (θ - π) ≠ 0 := sub_ne_zero.mpr hne
  rw [show ((θ - π : ℝ) : ℂ) ^ 2 = (((θ - π) ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.div_ofReal_re,
    stokesQ_re]
  apply div_pos _ (by positivity)
  have : Real.cos θ ≠ -1 := by
    intro h
    rw [Real.cos_eq_neg_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk1 : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
    have hk2 : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have : (k : ℝ) = 0 := by
      have a : (-1 : ℤ) < k := by exact_mod_cast hk1
      have b : k < (1 : ℤ) := by exact_mod_cast hk2
      have : k = 0 := by omega
      simp [this]
    rw [this] at hk; apply hne; linarith
  have := Real.neg_one_le_cos θ
  have : -1 < Real.cos θ := lt_of_le_of_ne this (Ne.symm ‹_›)
  linarith

/-- `Re(x^{1/2}) > 0` for `x` off the closed negative real axis. -/
theorem re_cpow_inv_two_pos {x : ℂ} (hx : 0 < x.re) : 0 < (x ^ (2⁻¹ : ℂ)).re := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have him : (Complex.log x * 2⁻¹).im = arg x / 2 := by
    rw [Complex.mul_im, Complex.log_im]; simp; ring
  rw [him]
  rw [abs_lt] at harg
  constructor <;> linarith [Real.pi_pos]

theorem stokesC_of_ne {θ : ℝ} (hne : θ ≠ π) :
    stokesC θ = ((π - θ : ℝ) : ℂ) * (stokesQ θ / ((θ - π : ℝ) : ℂ) ^ 2) ^ (2⁻¹ : ℂ) := by
  simp only [stokesC, hne, ↓reduceIte]

/-- `c(θ)² = 2(1 + e^{iθ} + i(θ − π))`. -/
theorem stokesC_sq (θ : ℝ) : stokesC θ ^ 2 = stokesQ θ := by
  by_cases hne : θ = π
  · simp only [stokesC, hne, ↓reduceIte, stokesQ_pi]; ring
  have hs : ((θ - π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
  rw [stokesC_of_ne hne, mul_pow, Complex.cpow_ofNat_inv_pow]
  push_cast
  have : (θ : ℂ) - π ≠ 0 := by exact_mod_cast hs
  field_simp
  ring

/-- **`c(θ)` lies in the right half-plane for `−π < θ < π`** (DLMF: `0 ≤ θ ≤ π − δ`). -/
theorem stokesC_re_pos {θ : ℝ} (h₁ : -π < θ) (h₂ : θ < π) : 0 < (stokesC θ).re := by
  rw [stokesC_of_ne h₂.ne, Complex.re_ofReal_mul]
  exact mul_pos (by linarith) (re_cpow_inv_two_pos (stokesR_re_pos h₁ (by linarith) h₂.ne))

/-- **`c(θ)` lies in the left half-plane for `π < θ < 3π`** (DLMF: `π + δ ≤ θ ≤ 3π − δ`). -/
theorem stokesC_re_neg {θ : ℝ} (h₁ : π < θ) (h₂ : θ < 3 * π) : (stokesC θ).re < 0 := by
  rw [stokesC_of_ne h₁.ne', Complex.re_ofReal_mul]
  exact mul_neg_of_neg_of_pos (by linarith)
    (re_cpow_inv_two_pos (stokesR_re_pos (by linarith [Real.pi_pos]) h₂ h₁.ne'))

/-- `c(θ)²/(θ − π)² → 1` as `θ → π`. -/
theorem tendsto_stokesR :
    Tendsto (fun θ : ℝ => stokesQ θ / ((θ - π : ℝ) : ℂ) ^ 2) (𝓝[≠] π) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 (ε * 9 / 4 / 2), by positivity, fun θ hθ hd => ?_⟩
  have hne : θ ≠ π := hθ
  set s := θ - π
  have hs0 : s ≠ 0 := sub_ne_zero.mpr hne
  have hds : |s| < min 1 (ε * 9 / 4 / 2) := by rwa [Real.dist_eq] at hd
  have hs1 : ‖(s : ℂ) * I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact (hds.trans_le (min_le_left _ _)).le
  have hb := Complex.exp_bound hs1 (n := 3) (by norm_num)
  have hθs : (θ : ℂ) = s + π := by simp only [s]; push_cast; ring
  have hexp : cexp (θ * I) = -cexp (s * I) := by
    rw [hθs, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hQ : stokesQ θ - ((s : ℝ) : ℂ) ^ 2 = -2 * (cexp (s * I) -
      ∑ m ∈ Finset.range 3, ((s : ℂ) * I) ^ m / m.factorial) := by
    simp only [stokesQ, hexp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    rw [show (θ : ℂ) - π = s by rw [hθs]; ring]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0
  rw [dist_eq_norm, show stokesQ θ / ((s : ℝ) : ℂ) ^ 2 - 1 =
    (stokesQ θ - ((s : ℝ) : ℂ) ^ 2) / ((s : ℝ) : ℂ) ^ 2 by field_simp, hQ, norm_div, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hsn : ‖(s : ℂ) * I‖ = |s| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hsn] at hb
  have hspos : 0 < |s| := abs_pos.mpr hs0
  calc ‖(-2 : ℂ)‖ * ‖cexp (s * I) - ∑ m ∈ Finset.range 3, ((s : ℂ) * I) ^ m / m.factorial‖ /
        |s| ^ 2 ≤ 2 * (|s| ^ 3 * ((Nat.succ 3 : ℝ) * ((Nat.factorial 3 * 3 : ℕ) : ℝ)⁻¹)) /
          |s| ^ 2 := by
        gcongr
        · simp
        · simpa using hb
    _ = 4 / 9 * |s| := by
        simp only [Nat.succ_eq_add_one, Nat.factorial]
        push_cast
        field_simp
        ring
    _ < ε := by
        have := hds.trans_le (min_le_right _ _)
        linarith

/-- **`c(θ) ∼ π − θ` as `θ → π`**. -/
theorem tendsto_stokesC_div :
    Tendsto (fun θ : ℝ => stokesC θ / ((π - θ : ℝ) : ℂ)) (𝓝[≠] π) (𝓝 1) := by
  have h := ((continuousAt_cpow_const (a := (1 : ℂ)) (b := (2⁻¹ : ℂ))
    (by simp [Complex.one_mem_slitPlane])).tendsto.comp tendsto_stokesR)
  rw [Complex.one_cpow] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hne : θ ≠ π := hθ
  have hs : ((π - θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))
  simp only [Function.comp_apply]
  rw [stokesC_of_ne hne, mul_div_cancel_left₀ _ hs]

/-- `c` is continuous on `(−π, 3π)`. -/
theorem continuousOn_stokesC : ContinuousOn stokesC (Ioo (-π) (3 * π)) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hne : θ = π
  · subst hne
    rw [continuousAt_iff_punctured_nhds, show stokesC π = 0 by simp [stokesC] ]
    have hg : Tendsto (fun x : ℝ => ((π - x : ℝ) : ℂ)) (𝓝[≠] π) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => ((π - x : ℝ) : ℂ) := by fun_prop
      have := (hc.tendsto π).mono_left (nhdsWithin_le_nhds (s := {π}ᶜ))
      simpa using this
    have h := tendsto_stokesC_div.mul hg
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hs : ((π - x : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx))
    field_simp
  · have hR := stokesR_re_pos hθ.1 hθ.2 hne
    have hev : stokesC =ᶠ[𝓝 θ] fun x => ((π - x : ℝ) : ℂ) *
        (stokesQ x / ((x - π : ℝ) : ℂ) ^ 2) ^ (2⁻¹ : ℂ) := by
      filter_upwards [isOpen_ne.mem_nhds hne] with x hx
      exact stokesC_of_ne hx
    refine ContinuousAt.congr ?_ hev.symm
    have hs : ((θ - π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne)
    have hQ : Continuous stokesQ := by unfold stokesQ; fun_prop
    have h1 : ContinuousAt (fun x : ℝ => stokesQ x / ((x - π : ℝ) : ℂ) ^ 2) θ := by
      refine hQ.continuousAt.div (by fun_prop) (pow_ne_zero _ hs)
    exact (by fun_prop : Continuous fun x : ℝ => ((π - x : ℝ) : ℂ)).continuousAt.mul
      ((continuousAt_cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hR))).comp
        (f := fun x : ℝ => stokesQ x / ((x - π : ℝ) : ℂ) ^ 2) h1)

/-- A continuous `±1`-valued function on an interval that takes the value `1` is `1`. -/
theorem eq_one_of_sq_eq_one {s : Set ℝ} (hs : s.OrdConnected) {f : ℝ → ℂ} (hf : ContinuousOn f s)
    (h1 : ∀ x ∈ s, f x = 1 ∨ f x = -1) {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hfx₀ : f x₀ = 1) :
    ∀ x ∈ s, f x = 1 := by
  intro y hy
  rcases h1 y hy with h | h
  · exact h
  exfalso
  have hsub := hs.uIcc_subset hx₀ hy
  have hc : ContinuousOn (fun x => (f x).re) (uIcc x₀ y) :=
    (Complex.continuous_re.comp_continuousOn (hf.mono hsub))
  have h0 : (0 : ℝ) ∈ uIcc ((f x₀).re) ((f y).re) := by
    rw [hfx₀, h]; simp
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hc h0
  rcases h1 z (hsub hz) with h' | h' <;> simp [h'] at hz0

/-- **`c` is the only such branch**: a continuous `c'` on `(−π, 3π)` with
`c'(θ)² = 2(1 + e^{iθ} + i(θ − π))` and `c'(θ) ∼ π − θ` as `θ → π` is `c`. -/
theorem stokesC_unique {c' : ℝ → ℂ} (hc : ContinuousOn c' (Ioo (-π) (3 * π)))
    (hsq : ∀ θ ∈ Ioo (-π) (3 * π), c' θ ^ 2 = stokesQ θ)
    (hlim : Tendsto (fun θ => c' θ / ((π - θ : ℝ) : ℂ)) (𝓝[≠] π) (𝓝 1)) :
    ∀ θ ∈ Ioo (-π) (3 * π), c' θ = stokesC θ := by
  have hne0 : ∀ θ ∈ Ioo (-π) (3 * π), θ ≠ π → stokesC θ ≠ 0 := fun θ hθ hne h => by
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := stokesC_re_pos hθ.1 h1; rw [h] at this; simp at this
    · have := stokesC_re_neg h1 hθ.2; rw [h] at this; simp at this
  set f : ℝ → ℂ := fun θ => c' θ / stokesC θ
  have hpm : ∀ θ ∈ Ioo (-π) (3 * π), θ ≠ π → f θ = 1 ∨ f θ = -1 := fun θ hθ hne => by
    have h0 := hne0 θ hθ hne
    have : f θ ^ 2 = 1 := by
      simp only [f]
      rw [div_pow, hsq θ hθ, stokesC_sq,
        div_self (by rw [← stokesC_sq]; exact pow_ne_zero 2 h0)]
    exact sq_eq_one_iff.mp this
  have hf_lim : Tendsto f (𝓝[≠] π) (𝓝 1) := by
    have := hlim.div tendsto_stokesC_div one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hs : ((π - θ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hθ))
    simp only [f, Pi.div_apply]
    rw [div_div_div_cancel_right₀ hs]
  have hf_cont : ∀ t : Set ℝ, t ⊆ Ioo (-π) (3 * π) → π ∉ t → ContinuousOn f t := fun t ht hπ =>
    fun θ hθ => ((hc θ (ht hθ)).div ((continuousOn_stokesC θ (ht hθ)))
      (hne0 θ (ht hθ) (fun h => hπ (h ▸ hθ)))).mono ht
  have hev : ∀ᶠ θ in 𝓝[≠] π, 0 < (f θ).re :=
    (Complex.continuous_re.tendsto 1).comp hf_lim |>.eventually (lt_mem_nhds (by simp))
  -- left side
  have hL : ∀ θ ∈ Ioo (-π) π, f θ = 1 := by
    have hb : ∀ᶠ θ in 𝓝[<] π, 0 < (f θ).re ∧ θ ∈ Ioo (-π) π := by
      refine (hev.filter_mono (nhdsWithin_mono _ (fun x hx => ne_of_lt hx))).and ?_
      exact Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    obtain ⟨θ₁, hθ₁, hθ₁s⟩ := hb.exists
    have h1 : f θ₁ = 1 := by
      rcases hpm θ₁ ⟨hθ₁s.1, by linarith [hθ₁s.2, Real.pi_pos]⟩ hθ₁s.2.ne with h | h
      · exact h
      · rw [h] at hθ₁; simp at hθ₁; linarith
    exact eq_one_of_sq_eq_one ordConnected_Ioo (hf_cont _ (Ioo_subset_Ioo_right
      (by linarith [Real.pi_pos])) (fun h => lt_irrefl _ h.2))
      (fun θ hθ => hpm θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩ hθ.2.ne) hθ₁s h1
  -- right side
  have hR : ∀ θ ∈ Ioo π (3 * π), f θ = 1 := by
    have hb : ∀ᶠ θ in 𝓝[>] π, 0 < (f θ).re ∧ θ ∈ Ioo π (3 * π) := by
      refine (hev.filter_mono (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))).and ?_
      exact Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    obtain ⟨θ₁, hθ₁, hθ₁s⟩ := hb.exists
    have h1 : f θ₁ = 1 := by
      rcases hpm θ₁ ⟨by linarith [hθ₁s.1, Real.pi_pos], hθ₁s.2⟩ hθ₁s.1.ne' with h | h
      · exact h
      · rw [h] at hθ₁; simp at hθ₁; linarith
    exact eq_one_of_sq_eq_one ordConnected_Ioo (hf_cont _ (Ioo_subset_Ioo_left
      (by linarith [Real.pi_pos])) (fun h => lt_irrefl _ h.1))
      (fun θ hθ => hpm θ ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩ hθ.1.ne') hθ₁s h1
  intro θ hθ
  rcases lt_trichotomy θ π with h | h | h
  · have := hL θ ⟨hθ.1, h⟩
    simp only [f] at this
    exact (div_eq_one_iff_eq (hne0 θ hθ h.ne)).mp this
  · subst h
    have := hsq π hθ
    rw [stokesQ_pi] at this
    rw [pow_eq_zero_iff two_ne_zero |>.mp this]
    simp [stokesC]
  · have := hR θ ⟨h, hθ.2⟩
    simp only [f] at this
    exact (div_eq_one_iff_eq (hne0 θ hθ h.ne')).mp this

/-! ### The size of the Gaussian factor -/

/-- **"Of the same exponentially-small order of magnitude as the contribution from the other
terms in 2.11.15"**: `|exp(−(√(ρ/2) c(θ))²)| = |e^{−ρ−z}|`, `z = ρe^{iθ}`. -/
theorem dlmf_2_11_iv_same_order {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    ‖cexp (-((Real.sqrt (ρ / 2) : ℂ) * stokesC θ) ^ 2)‖ =
      ‖cexp (-(ρ : ℂ) - ρ * cexp (θ * I))‖ := by
  rw [mul_pow, stokesC_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity),
    Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [stokesQ, Complex.exp_ofReal_mul_I_re]
  ring

/-- The Gaussian factor is exponentially small, `≤ e^{−ρ(1 + cos θ)}`, except on the Stokes line
`θ = π` (mod `2π`). -/
theorem norm_exp_neg_stokes_le {ρ : ℝ} (hρ : 0 ≤ ρ) (θ : ℝ) :
    ‖cexp (-((Real.sqrt (ρ / 2) : ℂ) * stokesC θ) ^ 2)‖ = Real.exp (-(ρ * (1 + Real.cos θ))) := by
  rw [dlmf_2_11_iv_same_order hρ, Complex.norm_exp]
  congr 1
  simp [Complex.exp_ofReal_mul_I_re]
  ring

/-! ### Stokes lines -/

/-- **Stokes line**: `|e^{−z}| = e^{−|z| cos θ} ≤ e^{|z|}`, with equality exactly when
`θ = π + 2πk`, i.e. on the ray `ph z = π` (and its images on the Riemann surface) `e^{−z}`
achieves maximum dominance. -/
theorem stokes_line_max_dominance {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖cexp (-(r * cexp (θ * I)))‖ ≤ Real.exp r ∧
      (‖cexp (-(r * cexp (θ * I)))‖ = Real.exp r ↔ ∃ k : ℤ, θ = π + k * (2 * π)) := by
  have hn : ‖cexp (-(r * cexp (θ * I)))‖ = Real.exp (-(r * Real.cos θ)) := by
    rw [Complex.norm_exp]; simp [Complex.exp_ofReal_mul_I_re]
  rw [hn]
  refine ⟨Real.exp_le_exp.mpr (by nlinarith [Real.neg_one_le_cos θ]), ?_⟩
  rw [Real.exp_eq_exp]
  constructor
  · intro h
    have hc : Real.cos θ = -1 := by
      have : r * (Real.cos θ + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hc
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [show π + k * (2 * π) = π + (k : ℤ) * (2 * π) by rfl, Real.cos_add_int_mul_two_pi,
      Real.cos_pi]
    ring

end Azurite.DLMF
