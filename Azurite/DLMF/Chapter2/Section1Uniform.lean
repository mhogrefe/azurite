/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1Expansion

/-!
# DLMF §2.1(iv): uniform asymptotic expansions

* `dlmf_2_1_iv_sector`: in a closed sector `α ≤ ph x ≤ β`, 2.1.13 is uniform in `ph x ∈ [α, β]`
  as `|x| → ∞` (bounds for `x = re^{iθ}`, `r > R`, uniformly in `θ`).
* 2.1.18: `IsUnifAsympExpansionDLMF` (uniform in a parameter `u ∈ 𝐔`, coefficients `aₛ(u)`),
  `IsUnifAsympExpansionAtDLMF` (finite limit point `c`); both imply the pointwise expansions.
* `dlmf_2_1_iv_not_uniform`: `e^{−x/u}`, `u > 0`, has the null expansion for each `u` but not
  uniformly.
-/

open Set Filter Topology Asymptotics Complex

namespace Azurite.DLMF

/-! ### Closed sectors: uniformity in the phase -/

theorem div_zpow_neg_natCast {𝕜 : Type*} [NormedField 𝕜] (u x : 𝕜) (n : ℕ) :
    u / x ^ (-(n : ℤ)) = x ^ n * u := by
  rw [zpow_neg, zpow_natCast, div_inv_eq_mul, mul_comm]

/-- **DLMF §2.1(iv)**: if `𝐗` is the closed sector `α ≤ ph x ≤ β`, the asymptotic property 2.1.13
holds uniformly with respect to `ph x ∈ [α, β]` as `|x| → ∞`. -/
theorem dlmf_2_1_iv_sector {α β : ℝ} (hα : -Real.pi < α) (hβ : β ≤ Real.pi) {f : ℂ → ℂ}
    {a : ℕ → ℂ} :
    IsAsympExpansionDLMF {x : ℂ | x ≠ 0 ∧ arg x ∈ Icc α β} f a ↔
      ∀ n : ℕ, 0 < n → ∃ C R : ℝ, ∀ θ ∈ Icc α β, ∀ r : ℝ, R < r →
        ‖((r : ℂ) * exp (θ * I)) ^ n * (f ((r : ℂ) * exp (θ * I)) -
          ∑ s ∈ Finset.range n, a s * ((r : ℂ) * exp (θ * I)) ^ (-(s : ℤ)))‖ ≤ C := by
  set X := {x : ℂ | x ≠ 0 ∧ arg x ∈ Icc α β}
  have hpolar : ∀ θ ∈ Icc α β, ∀ r : ℝ, 0 < r →
      (r : ℂ) * exp (θ * I) ∈ X ∧ ‖(r : ℂ) * exp (θ * I)‖ = r := fun θ hθ r hr => by
    have hθ' : θ ∈ Ioc (-Real.pi) Real.pi := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    refine ⟨⟨mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _), ?_⟩, ?_⟩
    · rw [arg_real_mul _ hr, arg_exp_mul_I_of_mem hθ']; exact hθ
    · rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_of_nonneg hr.le]
  refine forall_congr' fun n => forall_congr' fun _ => ?_
  simp only [IsBigODLMF, IsBoundedUnder, IsBounded, eventually_map, div_zpow_neg_natCast]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨R, hR⟩ := eventually_cobounded_inf_principal.mp hC
    refine ⟨C, max R 0, fun θ hθ r hr => ?_⟩
    obtain ⟨hX, hn⟩ := hpolar θ hθ r (lt_of_le_of_lt (le_max_right _ _) hr)
    exact hR _ hX (by rw [hn]; exact lt_of_le_of_lt (le_max_left _ _) hr)
  · rintro ⟨C, R, h⟩
    refine ⟨C, eventually_cobounded_inf_principal.mpr ⟨max R 0, fun x hx hxR => ?_⟩⟩
    have e := norm_mul_exp_arg_mul_I x
    have := h (arg x) hx.2 ‖x‖ (lt_of_le_of_lt (le_max_left _ _) hxR)
    rwa [e] at this

/-! ### Uniformity with respect to parameters (2.1.18) -/

section Parameters

variable {ι 𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF 2.1.18**: `f(u, x) ∼ ∑ aₛ(u)x^{−s}` as `x → ∞` in `𝐗`, uniformly for `u ∈ 𝐔`: for each
`n ≥ 0`, `|xⁿ(f(u, x) − ∑_{s<n} aₛ(u)x^{−s})|` is bounded as `x → ∞` in `𝐗`, uniformly for
`u ∈ 𝐔`. -/
def IsUnifAsympExpansionDLMF (U : Set ι) (X : Set 𝕜) (f : ι → 𝕜 → 𝕜) (a : ℕ → ι → 𝕜) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ᶠ x in Bornology.cobounded 𝕜 ⊓ 𝓟 X, ∀ u ∈ U,
    ‖x ^ n * (f u x - ∑ s ∈ Finset.range n, a s u * x ^ (-(s : ℤ)))‖ ≤ C

/-- **DLMF §2.1(iv)**: the same at a finite limit point `c`: for each `n`,
`|(x − c)^{−n}(f(u, x) − ∑_{s<n} aₛ(u)(x − c)ˢ)|` is bounded as `x → c` in `𝐗`, uniformly for
`u ∈ 𝐔`. -/
def IsUnifAsympExpansionAtDLMF (U : Set ι) (X : Set 𝕜) (c : 𝕜) (f : ι → 𝕜 → 𝕜)
    (a : ℕ → ι → 𝕜) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ᶠ x in approachIn X c, ∀ u ∈ U,
    ‖(f u x - ∑ s ∈ Finset.range n, a s u * (x - c) ^ s) / (x - c) ^ n‖ ≤ C

/-- A uniform expansion is an expansion 2.1.14 for each fixed `u ∈ 𝐔`. -/
theorem IsUnifAsympExpansionDLMF.isAsympExpansion {U : Set ι} {X : Set 𝕜} {f : ι → 𝕜 → 𝕜}
    {a : ℕ → ι → 𝕜} (h : IsUnifAsympExpansionDLMF U X f a) {u : ι} (hu : u ∈ U) :
    IsAsympExpansionDLMF X (f u) fun s => a s u := fun n _ => by
  obtain ⟨C, hC⟩ := h n
  refine ⟨C, eventually_map.mpr ?_⟩
  filter_upwards [hC] with x hx
  rw [div_zpow_neg_natCast]
  exact hx u hu

/-- A uniform expansion at `c` is an expansion 2.1.16 for each fixed `u ∈ 𝐔`. -/
theorem IsUnifAsympExpansionAtDLMF.isAsympExpansionAt {U : Set ι} {X : Set 𝕜} {c : 𝕜}
    {f : ι → 𝕜 → 𝕜} {a : ℕ → ι → 𝕜} (h : IsUnifAsympExpansionAtDLMF U X c f a) {u : ι}
    (hu : u ∈ U) : IsAsympExpansionAtDLMF X c (f u) fun s => a s u := fun n => by
  obtain ⟨C, hC⟩ := h n
  exact ⟨C, eventually_map.mpr (hC.mono fun x hx => hx u hu)⟩

end Parameters

/-- Uniformity is a genuine condition: for `u ∈ (0, ∞)`, each `f(u, x) = e^{−x/u}` has the null
expansion as `x → +∞`, but not uniformly in `u`. -/
theorem dlmf_2_1_iv_not_uniform :
    (∀ u ∈ Ioi (0 : ℝ), IsAsympExpansionDLMF (Ioi (0 : ℝ)) (fun x => Real.exp (-(x / u))) 0) ∧
      ¬ IsUnifAsympExpansionDLMF (Ioi (0 : ℝ)) (Ioi (0 : ℝ))
        (fun u x => Real.exp (-(x / u))) fun _ _ => 0 := by
  set L := Bornology.cobounded ℝ ⊓ 𝓟 (Ioi (0 : ℝ))
  have hL : Tendsto (fun x : ℝ => x) L atTop := by
    refine (tendsto_norm_cobounded_atTop.mono_left (inf_le_left : L ≤ _)).congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self (Ioi (0 : ℝ)))] with x hx
    exact Real.norm_of_nonneg (le_of_lt hx)
  have hpos : ∀ᶠ x in L, 0 < x :=
    mem_inf_of_right (mem_principal_self (Ioi (0 : ℝ)))
  refine ⟨fun u hu => isAsympExpansionDLMF_zero_of_tendsto fun n => ?_, ?_⟩
  · have hu' : (0 : ℝ) < u := hu
    have h := (tendsto_pow_mul_exp_neg_mul n (inv_pos.mpr hu')).comp hL
    refine h.congr' ?_
    filter_upwards with x
    simp only [Function.comp_apply, div_eq_mul_inv, mul_comm x]
  · intro h
    obtain ⟨C, hC⟩ := h 1
    have hne : L.NeBot := atInf_neBot (by
      intro hb
      obtain ⟨R, hR⟩ := hb.bddAbove
      have := hR (show max R 0 + 1 ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; positivity)
      linarith [le_max_left R 0])
    obtain ⟨x, hx, hxC, hx0⟩ := (hC.and ((hL.eventually_ge_atTop (2 * |C| + 2)).and hpos)).exists
    have hb := hx (2 * x) (by simp; linarith)
    simp only [pow_one, Finset.range_one, Finset.sum_singleton, zero_mul, sub_zero,
      Real.norm_eq_abs] at hb
    rw [show x / (2 * x) = 1 / 2 by field_simp, abs_mul, abs_of_pos hx0,
      abs_of_pos (Real.exp_pos _)] at hb
    have he : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2 : ℝ)); linarith
    nlinarith [le_abs_self C]

end Azurite.DLMF
