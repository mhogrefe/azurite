/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section9Series
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# DLMF §2.1(i): asymptotic and order symbols

The symbols are defined literally by ratios, as in DLMF, along an arbitrary filter `l`
("as `x → c` in `𝐗`" is `approachIn 𝐗 c = 𝓝[𝐗 ∖ {c}] c`, proper exactly when `c` is a limit
point of `𝐗`; `x → +∞` is `atTop`, `x → ∞` in a sector of `ℂ` is `cobounded ℂ ⊓ 𝓟 S`).

* `AsympEqDLMF` (2.1.1), `IsLittleODLMF` (2.1.2), `IsBigODLMF` (2.1.3), `IsBigOOnDLMF` (`O` on a
  whole set); `dlmf_2_1_1`–`dlmf_2_1_3`, `dlmf_2_1_3_on`: equal to Mathlib's `~[l]`, `=o[l]`,
  `=O[l]` when `φ` is eventually nonzero.
* Examples 2.1.4–2.1.7; `dlmf_2_1_5_sector` (`|ph x| ≤ ½π − δ`), `dlmf_2_1_5_ray`, and
  `dlmf_2_1_5_not_halfPlane` (fails in `|ph x| < ½π`).
* `dlmf_2_1_8` (tails of convergent power series), `dlmf_2_1_9`.
* 2.1.10 as inclusions of the classes `littleOSet`, `bigOSet`: `dlmf_2_1_10_1`, `dlmf_2_1_10_2`,
  `dlmf_2_1_10_1_not_reversible`. DLMF imprecision: the second relation *is* reversible
  (`dlmf_2_1_10_2_reverse`, `dlmf_2_1_10_2_eq`).
-/

open Set Filter Topology Asymptotics
open scoped Pointwise

namespace Azurite.DLMF

/-! ### Definitions (2.1.1–2.1.3) -/

section Defs

variable {α 𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF 2.1.1**: `f(x) ∼ φ(x)` along `l`, i.e. `f(x)/φ(x) → 1`. -/
def AsympEqDLMF (l : Filter α) (f φ : α → 𝕜) : Prop :=
  Tendsto (fun x => f x / φ x) l (𝓝 1)

/-- **DLMF 2.1.2**: `f(x) = o(φ(x))` along `l`, i.e. `f(x)/φ(x) → 0`. -/
def IsLittleODLMF (l : Filter α) (f φ : α → 𝕜) : Prop :=
  Tendsto (fun x => f x / φ x) l (𝓝 0)

/-- **DLMF 2.1.3**: `f(x) = O(φ(x))` along `l`, i.e. `|f(x)/φ(x)|` is bounded (eventually). -/
def IsBigODLMF (l : Filter α) (f φ : α → 𝕜) : Prop :=
  IsBoundedUnder (· ≤ ·) l fun x => ‖f x / φ x‖

/-- **DLMF §2.1(i)**: `f(x) = O(φ(x))` on the whole set `X`. -/
def IsBigOOnDLMF (X : Set α) (f φ : α → 𝕜) : Prop :=
  ∃ C, ∀ x ∈ X, ‖f x / φ x‖ ≤ C

end Defs

/-- "`x → c` in `X`": the filter of punctured neighbourhoods of `c` within `X`. -/
def approachIn {β : Type*} [TopologicalSpace β] (X : Set β) (c : β) : Filter β :=
  𝓝[X \ {c}] c

/-- `x → c` in `X` makes sense (the filter is proper) exactly when `c` is a limit point of `X`. -/
theorem approachIn_neBot_iff {β : Type*} [TopologicalSpace β] (X : Set β) (c : β) :
    (approachIn X c).NeBot ↔ AccPt c (𝓟 X) := by
  rw [approachIn, AccPt, nhdsWithin, nhdsWithin, inf_assoc, inf_principal, sdiff_eq, inter_comm]

theorem approachIn_univ {β : Type*} [TopologicalSpace β] (c : β) :
    approachIn univ c = 𝓝[≠] c := by
  rw [approachIn, ← compl_eq_univ_sdiff]

section Bridges

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {f φ : α → 𝕜}

/-- 2.1.1 agrees with Mathlib's `~[l]` when `φ` is eventually nonzero. -/
theorem dlmf_2_1_1 (hφ : ∀ᶠ x in l, φ x ≠ 0) : AsympEqDLMF l f φ ↔ f ~[l] φ :=
  (isEquivalent_iff_tendsto_one hφ).symm

/-- 2.1.2 agrees with Mathlib's `=o[l]` when `φ` is eventually nonzero. -/
theorem dlmf_2_1_2 (hφ : ∀ᶠ x in l, φ x ≠ 0) : IsLittleODLMF l f φ ↔ f =o[l] φ :=
  (isLittleO_iff_tendsto' (hφ.mono fun _ h h0 => absurd h0 h)).symm

/-- 2.1.3 agrees with Mathlib's `=O[l]` when `φ` is eventually nonzero. -/
theorem dlmf_2_1_3 (hφ : ∀ᶠ x in l, φ x ≠ 0) : IsBigODLMF l f φ ↔ f =O[l] φ :=
  (isBigO_iff_div_isBoundedUnder (hφ.mono fun _ h h0 => absurd h0 h)).symm

/-- `O` on a whole set agrees with Mathlib's `=O[𝓟 X]` when `φ` has no zeros on `X`. -/
theorem dlmf_2_1_3_on {X : Set α} (hφ : ∀ x ∈ X, φ x ≠ 0) : IsBigOOnDLMF X f φ ↔ f =O[𝓟 X] φ := by
  rw [isBigO_iff_div_isBoundedUnder (eventually_principal.mpr fun x hx h0 => absurd h0 (hφ x hx))]
  simp only [IsBigOOnDLMF, IsBoundedUnder, IsBounded, eventually_map, eventually_principal]

end Bridges

/-! ### Examples (2.1.4–2.1.7) -/

/-- **DLMF 2.1.4**: `tanh x ∼ x` as `x → 0` in `ℂ`. -/
theorem dlmf_2_1_4 : AsympEqDLMF (approachIn univ (0 : ℂ)) Complex.tanh id := by
  rw [AsympEqDLMF, approachIn_univ]
  have hs : Tendsto (fun z : ℂ => Complex.sinh z / z) (𝓝[≠] 0) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (Complex.hasDerivAt_sinh 0)
    rw [Complex.cosh_zero] at h
    refine h.congr fun z => ?_
    simp [slope_def_field, div_eq_inv_mul]
  have hc : Tendsto Complex.cosh (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have := (Complex.continuous_cosh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [Complex.cosh_zero] at this
  have := hs.div hc one_ne_zero
  rw [div_one] at this
  refine this.congr fun z => ?_
  simp only [Pi.div_apply, id, Complex.tanh_eq_sinh_div_cosh]
  ring

/-- **DLMF 2.1.5**: `e^{−x} = o(1)` as `x → +∞` in `ℝ`. -/
theorem dlmf_2_1_5 : IsLittleODLMF atTop (fun x : ℝ => Real.exp (-x)) 1 := by
  simpa [IsLittleODLMF] using Real.tendsto_exp_neg_atTop_nhds_zero

/-- **DLMF §2.1(i)**: in 2.1.5, `ℝ` can be replaced by the whole sector `|ph x| ≤ ½π − δ`
(`0 < δ ≤ ½π`), `x → ∞` meaning `|x| → ∞`. -/
theorem dlmf_2_1_5_sector {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ Real.pi / 2) :
    IsLittleODLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ Real.pi / 2 - δ})
      (fun z => Complex.exp (-z)) 1 := by
  rw [IsLittleODLMF]
  simp only [Pi.one_apply, div_one]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- `ℜz ≥ |z| sin δ` in the sector
  have hre : ∀ z : ℂ, |Complex.arg z| ≤ Real.pi / 2 - δ → ‖z‖ * Real.sin δ ≤ z.re := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | h0
    · simp
    have hc := Complex.cos_arg h0
    have hcos : Real.sin δ ≤ Real.cos (Complex.arg z) := by
      rw [← Real.cos_abs (Complex.arg z), ← Real.cos_pi_div_two_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz
    rw [hc, le_div_iff₀ (norm_pos_iff.mpr h0)] at hcos
    linarith
  have hsin : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hnorm : Tendsto (fun z : ℂ => ‖z‖ * Real.sin δ)
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ Real.pi / 2 - δ}) atTop :=
    (tendsto_norm_cobounded_atTop.mono_left inf_le_left).atTop_mul_const hsin
  have hlim := Real.tendsto_exp_neg_atTop_nhds_zero.comp hnorm
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
  rw [Complex.norm_exp, Function.comp_apply, Complex.neg_re]
  exact Real.exp_le_exp.mpr (by linarith [hre z hz])

/-- **DLMF §2.1(i)**: in 2.1.5, `ℝ` can be replaced by any fixed ray `ph x = θ`, `|θ| < ½π`. -/
theorem dlmf_2_1_5_ray {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    IsLittleODLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | Complex.arg z = θ})
      (fun z => Complex.exp (-z)) 1 :=
  (dlmf_2_1_5_sector (δ := Real.pi / 2 - |θ|) (by linarith)
    (by linarith [abs_nonneg θ])).mono_left
    (inf_le_inf_left _ (principal_mono.mpr fun z hz => by
      simp only [mem_ofPred_eq] at hz ⊢; rw [hz]; linarith))

/-- **DLMF §2.1(i)**: 2.1.5 does not hold as `x → ∞` in the open half-plane `|ph x| < ½π`
(along `x = 1 + it`, `|e^{−x}| = e^{−1}`). -/
theorem dlmf_2_1_5_not_halfPlane :
    ¬ IsLittleODLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| < Real.pi / 2})
      (fun z => Complex.exp (-z)) 1 := by
  intro h
  simp only [IsLittleODLMF, Pi.one_apply, div_one] at h
  have hg : Tendsto (fun t : ℝ => (1 : ℂ) + t * Complex.I) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| < Real.pi / 2}) := by
    refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr
      (Eventually.of_forall fun t => Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp)))⟩
    refine tendsto_atTop_mono (fun t => ?_) tendsto_abs_atTop_atTop
    have := Complex.abs_im_le_norm ((1 : ℂ) + t * Complex.I)
    simpa using this
  have hc := (h.comp hg).norm
  have hconst : (fun t : ℝ => ‖Complex.exp (-((1 : ℂ) + t * Complex.I))‖) =
      fun _ => Real.exp (-1) := by
    funext t; rw [Complex.norm_exp]; simp
  simp only [Function.comp_def, norm_zero] at hc
  rw [hconst] at hc
  exact (Real.exp_pos (-1)).ne' (tendsto_nhds_unique tendsto_const_nhds hc)

/-- **DLMF 2.1.6**: `sin(πx + x⁻¹) = O(x⁻¹)` as `x → ±∞` in `ℤ` (indeed with constant `1` on
all of `ℤ`). -/
theorem dlmf_2_1_6 : IsBigODLMF (atTop ⊔ atBot)
    (fun n : ℤ => Real.sin (Real.pi * n + (n : ℝ)⁻¹)) fun n => (n : ℝ)⁻¹ := by
  refine isBoundedUnder_of ⟨1, fun n => ?_⟩
  show ‖Real.sin (Real.pi * n + (n : ℝ)⁻¹) / (n : ℝ)⁻¹‖ ≤ 1
  rw [show Real.pi * n + (n : ℝ)⁻¹ = (n : ℝ)⁻¹ + n * Real.pi by ring, Real.sin_add_int_mul_pi,
    norm_div, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact div_le_one_of_le₀ Real.abs_sin_le_abs (abs_nonneg _)

/-- **DLMF 2.1.7**: `e^{ix} = O(1)` for `x ∈ ℝ`. -/
theorem dlmf_2_1_7 : IsBigOOnDLMF univ (fun x : ℝ => Complex.exp (x * Complex.I)) 1 :=
  ⟨1, fun x _ => by simp [Complex.norm_exp_ofReal_mul_I]⟩

/-! ### Power series (2.1.8–2.1.9) -/

/-- **DLMF 2.1.8**: if `∑ aₛ zˢ` converges for all sufficiently small `|z|`, then for each
`n ≥ 0`, `∑_{s=n}^∞ aₛ zˢ = O(zⁿ)` as `z → 0` in `ℂ`. -/
theorem dlmf_2_1_8 (a : ℕ → ℂ)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), ∃ S, SeriesConverges (fun s => a s * z ^ s) S) (n : ℕ) :
    IsBigODLMF (approachIn univ (0 : ℂ))
      (fun z => ∑' s, a (s + n) * z ^ (s + n)) fun z => z ^ n := by
  rw [approachIn_univ]
  -- a nonzero point of convergence, and bounded terms there
  obtain ⟨z₀, ⟨S, hS⟩, hz₀⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ))).exists
  obtain ⟨M, hM⟩ := hS.tendsto_zero.norm.bddAbove_range
  have hM' : ∀ s, ‖a s * z₀ ^ s‖ ≤ M := fun s => hM ⟨s, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' 0)
  set r := ‖z₀‖
  have hr : 0 < r := norm_pos_iff.mpr hz₀
  refine ⟨2 * M / r ^ n, eventually_map.mpr ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (half_pos hr))] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  set ρ := ‖z‖ / r
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ : ρ ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]; linarith
  have hterm : ∀ s, ‖a (s + n) * z ^ (s + n)‖ ≤ M * ρ ^ n * (1 / 2) ^ s := fun s => by
    have e : ‖a (s + n) * z ^ (s + n)‖ = ‖a (s + n) * z₀ ^ (s + n)‖ * ρ ^ (s + n) := by
      simp only [norm_mul, norm_pow, ρ, div_pow]
      field_simp
      rfl
    rw [e, pow_add ρ s n, mul_comm (ρ ^ s), ← mul_assoc]
    have h1 : ρ ^ s ≤ (1 / 2) ^ s := pow_le_pow_left₀ hρ0 hρ s
    have h2 := hM' (s + n)
    calc ‖a (s + n) * z₀ ^ (s + n)‖ * ρ ^ n * ρ ^ s ≤ M * ρ ^ n * ρ ^ s := by gcongr
      _ ≤ M * ρ ^ n * (1 / 2) ^ s := by gcongr
  have hsum : HasSum (fun s : ℕ => M * ρ ^ n * (1 / 2) ^ s) (M * ρ ^ n * 2) :=
    hasSum_geometric_two.mul_left _
  have hT := tsum_of_norm_bounded hsum hterm
  rw [norm_div, norm_pow]
  rcases eq_or_ne (‖z‖ ^ n) 0 with h0 | h0
  · rw [h0, div_zero]; positivity
  · rw [div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm h0))]
    refine hT.trans (le_of_eq ?_)
    simp only [ρ, div_pow]
    field_simp

/-- **DLMF 2.1.9**: `e^z = 1 + z + O(z²)` as `z → 0` in `ℂ`. -/
theorem dlmf_2_1_9 : IsBigODLMF (approachIn univ (0 : ℂ))
    (fun z => Complex.exp z - (1 + z)) fun z => z ^ 2 := by
  rw [approachIn_univ]
  refine ⟨1, eventually_map.mpr ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [norm_div, norm_pow, ← sub_sub]
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  · exact div_le_one_of_le₀ (Complex.norm_exp_sub_one_sub_id_le hz) (by positivity)

/-! ### Generic use of `o` and `O` (2.1.10) -/

section Generic

variable {α 𝕜 : Type*} [NormedField 𝕜] (l : Filter α) (φ : α → 𝕜)

/-- The class `o(φ)` along `l`. -/
def littleOSet : Set (α → 𝕜) := {f | IsLittleODLMF l f φ}

/-- The class `O(φ)` along `l`. -/
def bigOSet : Set (α → 𝕜) := {f | IsBigODLMF l f φ}

/-- **DLMF 2.1.10**, first relation: `o(φ) = O(φ)`, meaning `o(φ) ⊆ O(φ)`. -/
theorem dlmf_2_1_10_1 : littleOSet l φ ⊆ bigOSet l φ := fun _ hf =>
  (show Tendsto _ l (𝓝 (0 : 𝕜)) from hf).norm.isBoundedUnder_le

/-- **DLMF 2.1.10**, second relation: `o(φ) + o(φ) = o(φ)`, meaning `o(φ) + o(φ) ⊆ o(φ)`. -/
theorem dlmf_2_1_10_2 : littleOSet l φ + littleOSet l φ ⊆ littleOSet l φ := by
  rintro _ ⟨f, hf, g, hg, rfl⟩
  have h := (show Tendsto _ l (𝓝 (0 : 𝕜)) from hf).add (show Tendsto _ l (𝓝 (0 : 𝕜)) from hg)
  rw [add_zero] at h
  exact h.congr fun x => by simp only [Pi.add_apply, add_div]

/-- **DLMF §2.1(i)**: the first relation of 2.1.10 is not reversible: `O(φ) ⊄ o(φ)` (`φ` itself
is `O(φ)` but not `o(φ)`). -/
theorem dlmf_2_1_10_1_not_reversible [l.NeBot] (hφ : ∀ᶠ x in l, φ x ≠ 0) :
    ¬ bigOSet l φ ⊆ littleOSet l φ := by
  intro h
  have h1 : Tendsto (fun x => φ x / φ x) l (𝓝 1) :=
    tendsto_const_nhds.congr' (hφ.mono fun x hx => (div_self hx).symm)
  have hmem : φ ∈ bigOSet l φ := h1.norm.isBoundedUnder_le
  exact one_ne_zero (tendsto_nhds_unique h1 (h hmem))

/-- **DLMF imprecision in §2.1(i)**: contrary to DLMF's remark that the relations of 2.1.10 "are
not reversible", the second one is: `o(φ) ⊆ o(φ) + o(φ)` (write `f = f + 0`), so
`o(φ) + o(φ) = o(φ)` holds as an equality of classes. -/
theorem dlmf_2_1_10_2_reverse : littleOSet l φ ⊆ littleOSet l φ + littleOSet l φ := by
  intro f hf
  refine ⟨f, hf, 0, ?_, add_zero f⟩
  show Tendsto _ l (𝓝 0)
  simp only [Pi.zero_apply, zero_div, tendsto_const_nhds]

/-- 2.1.10, second relation, as an equality of classes. -/
theorem dlmf_2_1_10_2_eq : littleOSet l φ + littleOSet l φ = littleOSet l φ :=
  (dlmf_2_1_10_2 l φ).antisymm (dlmf_2_1_10_2_reverse l φ)

end Generic

end Azurite.DLMF
