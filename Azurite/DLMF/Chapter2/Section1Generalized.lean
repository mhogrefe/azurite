/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1Uniform

/-!
# DLMF §2.1(v): generalized asymptotic expansions

* `IsAsympScaleDLMF` (2.1.19), `IsGenAsympExpansionDLMF` (2.1.20–2.1.21), along any filter (`x → c`
  in `𝐗`, `c` finite or infinite); `IsUnifGenAsympExpansionDLMF` (uniform in a parameter).
* `isAsympExpansionDLMF_iff_gen`: Poincaré expansions are generalized expansions for the scale
  `{x^{−s}}`.
* `IsGenAsympExpansionDLMF.term_isBigO` (`fₛ = O(φₛ)`), `.remainder_isLittleO`;
  `isGenAsympExpansion_trivial` (non-uniqueness).
* `dlmf_2_1_v_mul_counterexample`: multiplication does not carry over (scale `1, x⁻¹, x⁻³, …`).
* `dlmf_2_1_v_convergent_wrong_sum`: a convergent expansion whose sum is not the function.
-/

open Set Filter Topology Asymptotics

namespace Azurite.DLMF

section Defs

variable {α ι 𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF 2.1.19**: `{φₛ}` is an asymptotic sequence (scale) as `x → c` in `𝐗` (the filter `l`):
`φₛ₊₁(x) = o(φₛ(x))` for each `s`. -/
def IsAsympScaleDLMF (l : Filter α) (φ : ℕ → α → 𝕜) : Prop :=
  ∀ s, IsLittleODLMF l (φ (s + 1)) (φ s)

/-- **DLMF 2.1.20–2.1.21**: `f(x) ∼ ∑ fₛ(x); {φₛ(x)}`: `{φₛ}` is a scale and
`f(x) = ∑_{s=0}^{n−1} fₛ(x) + O(φₙ(x))` for `n = 0, 1, 2, …`. -/
def IsGenAsympExpansionDLMF (l : Filter α) (φ : ℕ → α → 𝕜) (f : α → 𝕜) (fs : ℕ → α → 𝕜) :
    Prop :=
  IsAsympScaleDLMF l φ ∧
    ∀ n : ℕ, IsBigODLMF l (fun x => f x - ∑ s ∈ Finset.range n, fs s x) (φ n)

/-- **DLMF §2.1(v)**: generalized asymptotic expansions uniform with respect to a parameter
`u ∈ 𝐔` (as in §2.1(iv)); the scale and the terms may depend on `u`. -/
def IsUnifGenAsympExpansionDLMF (U : Set ι) (l : Filter α) (φ : ℕ → ι → α → 𝕜)
    (f : ι → α → 𝕜) (fs : ℕ → ι → α → 𝕜) : Prop :=
  (∀ u ∈ U, IsAsympScaleDLMF l fun s => φ s u) ∧
    ∀ n : ℕ, ∃ C : ℝ, ∀ᶠ x in l, ∀ u ∈ U,
      ‖(f u x - ∑ s ∈ Finset.range n, fs s u x) / φ n u x‖ ≤ C

theorem IsUnifGenAsympExpansionDLMF.isGenAsympExpansion {U : Set ι} {l : Filter α}
    {φ : ℕ → ι → α → 𝕜} {f : ι → α → 𝕜} {fs : ℕ → ι → α → 𝕜}
    (h : IsUnifGenAsympExpansionDLMF U l φ f fs) {u : ι} (hu : u ∈ U) :
    IsGenAsympExpansionDLMF l (fun s => φ s u) (f u) fun s => fs s u :=
  ⟨h.1 u hu, fun n => by
    obtain ⟨C, hC⟩ := h.2 n
    exact ⟨C, eventually_map.mpr (hC.mono fun x hx => hx u hu)⟩⟩

end Defs

/-! ### Poincaré expansions are generalized expansions -/

section Poincare

variable {𝕜 : Type*} [NormedField 𝕜]

theorem isAsympScale_zpow (X : Set 𝕜) :
    IsAsympScaleDLMF (Bornology.cobounded 𝕜 ⊓ 𝓟 X) fun s x => x ^ (-(s : ℤ)) := fun s => by
  refine (tendsto_inv_atInf X).congr' ?_
  filter_upwards [eventually_ne_zero_atInf X] with x hx
  rw [zpow_neg_natCast_eq, zpow_neg_natCast_eq, pow_succ]
  field_simp

theorem isBigODLMF_partial_iff (X : Set 𝕜) (f : 𝕜 → 𝕜) (a : ℕ → 𝕜) (n : ℕ) :
    IsBigODLMF (Bornology.cobounded 𝕜 ⊓ 𝓟 X)
      (fun x => f x - ∑ s ∈ Finset.range n, a s * x ^ (-(s : ℤ))) (fun x => x ^ (-(n : ℤ))) ↔
      (fun x => f x - (PowerSeries.trunc n (PowerSeries.mk a)).eval x⁻¹)
        =O[Bornology.cobounded 𝕜 ⊓ 𝓟 X] fun x => x⁻¹ ^ n := by
  rw [dlmf_2_1_3 ((eventually_ne_zero_atInf X).mono fun x hx => zpow_ne_zero _ hx)]
  simp only [sum_zpow_eq_eval]
  simp only [zpow_neg_natCast_eq]

/-- **DLMF §2.1(v)**: a Poincaré expansion 2.1.14 is the generalized expansion with respect to the
scale `{x^{−s}}` with terms `fₛ(x) = aₛx^{−s}`. -/
theorem isAsympExpansionDLMF_iff_gen {X : Set 𝕜} {f : 𝕜 → 𝕜} {a : ℕ → 𝕜} :
    IsAsympExpansionDLMF X f a ↔ IsGenAsympExpansionDLMF (Bornology.cobounded 𝕜 ⊓ 𝓟 X)
      (fun s x => x ^ (-(s : ℤ))) f (fun s x => a s * x ^ (-(s : ℤ))) := by
  refine ⟨fun h => ⟨isAsympScale_zpow X, fun n => ?_⟩, fun h n _ => h.2 n⟩
  exact (isBigODLMF_partial_iff X f a n).mpr (isAsympExpansionDLMF_iff.mp h n)

end Poincare

/-! ### Elementary properties -/

section Properties

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {φ : ℕ → α → 𝕜} {f : α → 𝕜}
  {fs : ℕ → α → 𝕜}

/-- Each term is of the order of its scale function: `fₛ = O(φₛ)`. -/
theorem IsGenAsympExpansionDLMF.term_isBigO (h : IsGenAsympExpansionDLMF l φ f fs)
    (hφ : ∀ s, ∀ᶠ x in l, φ s x ≠ 0) (s : ℕ) : IsBigODLMF l (fs s) (φ s) := by
  rw [dlmf_2_1_3 (hφ s)]
  have h0 := (dlmf_2_1_3 (hφ s)).mp (h.2 s)
  have h1 := (dlmf_2_1_3 (hφ (s + 1))).mp (h.2 (s + 1))
  have hsc := ((dlmf_2_1_2 (hφ s)).mp (h.1 s)).isBigO
  refine (h0.sub (h1.trans hsc)).congr_left fun x => ?_
  rw [Finset.sum_range_succ]; ring

/-- The remainder after `n + 1` terms is `o(φₙ)`. -/
theorem IsGenAsympExpansionDLMF.remainder_isLittleO (h : IsGenAsympExpansionDLMF l φ f fs)
    (hφ : ∀ s, ∀ᶠ x in l, φ s x ≠ 0) (n : ℕ) :
    IsLittleODLMF l (fun x => f x - ∑ s ∈ Finset.range (n + 1), fs s x) (φ n) := by
  rw [dlmf_2_1_2 (hφ n)]
  exact ((dlmf_2_1_3 (hφ (n + 1))).mp (h.2 (n + 1))).trans_isLittleO
    ((dlmf_2_1_2 (hφ n)).mp (h.1 n))

/-- Generalized expansions are not unique: if `f = O(φ₀)` then `f, 0, 0, …` is a generalized
expansion of `f` with respect to any scale. -/
theorem isGenAsympExpansion_trivial (hφ : IsAsympScaleDLMF l φ) (hf : IsBigODLMF l f (φ 0)) :
    IsGenAsympExpansionDLMF l φ f fun s => if s = 0 then f else 0 := by
  refine ⟨hφ, fun n => ?_⟩
  rcases n with _ | n
  · simpa using hf
  · have : (fun x => f x - ∑ s ∈ Finset.range (n + 1), (if s = 0 then f else 0) x) = 0 := by
      funext x
      rw [Finset.sum_range_succ']
      simp
    rw [this]
    exact ⟨0, eventually_map.mpr (Eventually.of_forall fun x => by simp)⟩

end Properties

/-! ### Cautionary examples -/

/-- The scale `1, x⁻¹, x⁻³, x⁻⁴, x⁻⁵, …` as `x → +∞`. -/
noncomputable def gapScale : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun x => x⁻¹
  | s + 2 => fun x => x⁻¹ ^ (s + 3)

/-- The terms `1, x⁻¹, 0, 0, …`. -/
noncomputable def gapTerms : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun x => x⁻¹
  | _ + 2 => fun _ => 0

theorem isAsympScale_gapScale : IsAsympScaleDLMF atTop gapScale := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  intro s
  rcases s with _ | _ | s
  · simpa [gapScale, IsLittleODLMF] using hinv
  · have := hinv.pow 2
    rw [zero_pow two_ne_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [gapScale]
    rw [eq_div_iff (inv_ne_zero hx.ne')]; ring
  · refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [gapScale]
    rw [eq_div_iff (pow_ne_zero _ (inv_ne_zero hx.ne'))]; ring

theorem isGenAsympExpansion_gap :
    IsGenAsympExpansionDLMF atTop gapScale (fun x => 1 + x⁻¹) gapTerms := by
  refine ⟨isAsympScale_gapScale, fun n => ?_⟩
  rcases n with _ | _ | n
  · refine ⟨2, eventually_map.mpr ?_⟩
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, gapScale, div_one,
      Real.norm_eq_abs]
    have : 0 < x⁻¹ := by positivity
    have : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
    rw [abs_of_pos (by positivity)]; linarith
  · refine ⟨1, eventually_map.mpr ?_⟩
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [gapScale, gapTerms, hx.ne']
  · refine ⟨0, eventually_map.mpr (Eventually.of_forall fun x => ?_)⟩
    have : ∑ s ∈ Finset.range (n + 2), gapTerms s x = 1 + x⁻¹ := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp [gapTerms, add_comm]
    simp [this]

/-- **DLMF §2.1(v)**: multiplication does not carry over to generalized expansions. With the
scale `1, x⁻¹, x⁻³, x⁻⁴, …`, `f = 1 + x⁻¹` has the expansion `1 + x⁻¹`, but `f²` does not have
the product expansion `1 + 2x⁻¹ + x⁻²`: `f² − 1 − 2x⁻¹ = x⁻²` is not `O(x⁻³)`. -/
theorem dlmf_2_1_v_mul_counterexample :
    IsGenAsympExpansionDLMF atTop gapScale (fun x => 1 + x⁻¹) gapTerms ∧
      ¬ IsGenAsympExpansionDLMF atTop gapScale (fun x => (1 + x⁻¹) * (1 + x⁻¹))
        fun n x => ∑ p ∈ Finset.antidiagonal n, gapTerms p.1 x * gapTerms p.2 x := by
  refine ⟨isGenAsympExpansion_gap, fun h => ?_⟩
  obtain ⟨C, hC⟩ := h.2 2
  have hC' := eventually_map.mp hC
  obtain ⟨x, hx, hxC, hx0⟩ :=
    (hC'.and ((eventually_ge_atTop (|C| + 1)).and (eventually_gt_atTop (0 : ℝ)))).exists
  have hsum : ∑ s ∈ Finset.range 2, ∑ p ∈ Finset.antidiagonal s, gapTerms p.1 x * gapTerms p.2 x =
      1 + 2 * x⁻¹ := by
    simp [Finset.sum_range_succ, Finset.Nat.antidiagonal_succ, gapTerms]; ring
  beta_reduce at hx
  rw [hsum] at hx
  have e : ((1 + x⁻¹) * (1 + x⁻¹) - (1 + 2 * x⁻¹)) / gapScale 2 x = x := by
    simp only [gapScale]
    have hx' : x ≠ 0 := hx0.ne'
    rw [div_eq_iff (pow_ne_zero _ (inv_ne_zero hx')), inv_pow]
    field_simp
    ring
  rw [e, Real.norm_eq_abs, abs_of_pos hx0] at hx
  linarith [le_abs_self C]

/-- **DLMF §2.1(v)**: a generalized (here even Poincaré) expansion can converge without its sum
being the function represented: `e^{−x} ∼ 0 + 0 + ⋯; {x^{−s}}` as `x → +∞`, and the series
converges, to `0 ≠ e^{−x}`. -/
theorem dlmf_2_1_v_convergent_wrong_sum :
    IsGenAsympExpansionDLMF atTop (fun s (x : ℝ) => x ^ (-(s : ℤ))) (fun x => Real.exp (-x))
        (fun _ _ => 0) ∧
      ∀ x : ℝ, HasSum (fun s : ℕ => (fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) s x) 0 ∧
        (0 : ℝ) ≠ Real.exp (-x) := by
  refine ⟨⟨fun s => ?_, fun n => ?_⟩, fun x => ⟨hasSum_zero, (Real.exp_pos _).ne⟩⟩
  · refine tendsto_inv_atTop_zero.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [zpow_neg_natCast_eq, zpow_neg_natCast_eq, pow_succ]
    field_simp
  · have h := tendsto_pow_mul_exp_neg_mul n one_pos
    refine (h.norm.isBoundedUnder_le).mono_le ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Finset.sum_const_zero, sub_zero, div_zpow_neg_natCast, one_mul, norm_mul,
      norm_pow]
    exact le_rfl

end Azurite.DLMF
