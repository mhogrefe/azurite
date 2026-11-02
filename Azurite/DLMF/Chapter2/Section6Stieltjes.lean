/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

import Azurite.DLMF.Chapter1.Section14Stieltjes
import Azurite.DLMF.Chapter1.Section14TableMellin
import Azurite.DLMF.Chapter2.Section5LaplaceGrowth
import Azurite.DLMF.Chapter2.Section6

/-!
# DLMF §2.6(ii): Stieltjes Transform — definitions and convergence

The Stieltjes transform `𝓢f(z) = ∫₀^∞ f(t)/(t + z) dt` (2.6.8, `stieltjesT`) of a function `f`
locally integrable on `[0, ∞)` with the expansion `f(t) ∼ ∑ aₛ t^{−s−α}` as `t → ∞`, `0 < α ≤ 1`
(2.6.9, `StieltjesSetup`), and the remainders `fₙ` of 2.6.10 (`stieltjesRem`).

* The distributional pairings of 2.6.11–2.6.16 and 2.6.19 are recorded as definitions:
  `pairing` (2.6.11), `powPairing` (2.6.12–2.6.13), `logPairing` (2.6.14), `repeatedIntegralTail`
  (2.6.15, the `n`th repeated integral `f_{n,n}`), `remPairing` (2.6.16), `deltaPairing` (2.6.19).
* 2.6.18 (`stieltjesC`): `cₛ = (−1)^s/(s−1)! · 𝓜f(s)`, where `𝓜f` is `mellinCont`: `𝓜f₁(z)` plus
  the meromorphic continuation of `𝓜f₂(z)` from `ℜz < α` (`mellinTrunc₂ContZero`, DLMF 2.5.27). For
  `f` merely locally integrable on `[0, ∞)` the Mellin integral itself need not converge anywhere
  (`𝓜f₁` needs `ℜz ≥ 1`, `𝓜f₂` needs `ℜz < α ≤ 1`), so this is the only available reading of
  DLMF's "`𝓜f(s)` or its analytic continuation" (`docs/dlmf_errata.md`); it agrees with `𝓜f`
  whenever the latter converges (`mellinCont_eq_mellin`). The key evaluation is
  `mellinCont_eq_mellin_rem`: for `n + α < ℜz < n + 1 + α`, `ℜz ≥ 1`,
  `𝓜f(z) = ∫₀^∞ t^{z−1} f_{n+1}(t) dt`, an absolutely convergent integral.
* 2.6.22 (`stieltjesTest`): `φ_ε(t) = e^{−εt}/(t + z)`; 2.6.25 (`dlmf_2_6_25`):
  `⟨f, φ_ε⟩ → 𝓢f(z)` as `ε → 0+`.
* Convergence: `𝓢f(z)` converges absolutely for `z ∈ slitPlane` (`|ph z| < π`),
  `StieltjesSetup.integrableOn_stieltjesT`; the integrals `∫₀^∞ τⁿ fₙ(τ)/(τ + z) dτ` of 2.6.30
  (`integrableOn_pow_mul_rem_div`) and `∫₀^∞ τⁿ f_{n+1}(τ) dτ` (`mellinConvergent_rem_succ`,
  `0 < α < 1`) converge absolutely as well.

The expansions 2.6.27–2.6.30 are in `Section6StieltjesExpansion`, the Example 2.6.7 in
`Section6StieltjesExample`.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### 2.6.8, 2.6.10–2.6.16, 2.6.18, 2.6.19, 2.6.22: definitions -/

/-- **DLMF 2.6.8**: the Stieltjes transform `𝓢f(z) = ∫₀^∞ f(t)/(t + z) dt`. -/
noncomputable def stieltjesT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), f t / (t + z)

/-- **DLMF 2.6.10**: the remainder `fₙ(t) = f(t) − ∑_{s<n} aₛ t^{−s−α}`. -/
noncomputable def stieltjesRem (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  f t - ∑ s ∈ Finset.range n, a s * (t : ℂ) ^ (-((s : ℂ) + α))

/-- **DLMF 2.6.11**: the distribution of a locally integrable `f`, `⟨f, φ⟩ = ∫₀^∞ f(t) φ(t) dt`. -/
noncomputable def pairing (f φ : ℝ → ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), f t * φ t

/-- **DLMF 2.6.12–2.6.13**: the distribution assigned to `t^{−s−α}`,
`⟨t^{−s−α}, φ⟩ = (1/(α)ₛ) ∫₀^∞ t^{−α} φ^{(s)}(t) dt`, with `(α)ₛ = α(α+1)⋯(α+s−1)`; for `s = 0`
this is 2.6.12, `⟨t^{−α}, φ⟩ = ∫₀^∞ t^{−α} φ(t) dt`. -/
noncomputable def powPairing (α : ℝ) (s : ℕ) (φ : ℝ → ℂ) : ℂ :=
  (1 / ∏ j ∈ Finset.range s, ((α : ℂ) + j)) *
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(α : ℂ)) * iteratedDeriv s φ t

/-- **DLMF 2.6.14** (`α = 1`): `⟨t^{−s−1}, φ⟩ = −(1/s!) ∫₀^∞ (ln t) φ^{(s+1)}(t) dt`. -/
noncomputable def logPairing (s : ℕ) (φ : ℝ → ℂ) : ℂ :=
  -(1 / (Nat.factorial s : ℂ)) * ∫ t in Ioi (0 : ℝ), (Real.log t : ℂ) * iteratedDeriv (s + 1) φ t

/-- **DLMF 2.6.15**: the `n`th repeated integral from `∞` of `g` (for `n ≥ 1`),
`g_{n,n}(t) = ((−1)ⁿ/(n−1)!) ∫_t^∞ (τ − t)^{n−1} g(τ) dτ`. -/
noncomputable def repeatedIntegralTail (g : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (-1) ^ n / (Nat.factorial (n - 1) : ℂ) * ∫ τ in Ioi t, ((τ - t : ℝ) : ℂ) ^ (n - 1) * g τ

/-- **DLMF 2.6.16**: the distribution assigned to `fₙ`,
`⟨fₙ, φ⟩ = (−1)ⁿ ∫₀^∞ f_{n,n}(t) φ^{(n)}(t) dt`. -/
noncomputable def remPairing (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) (φ : ℝ → ℂ) : ℂ :=
  (-1) ^ n *
    ∫ t in Ioi (0 : ℝ), repeatedIntegralTail (stieltjesRem f a α n) n t * iteratedDeriv n φ t

/-- **DLMF 2.6.19**: `⟨δ^{(s)}, φ⟩ = (−1)^s φ^{(s)}(0)`. -/
noncomputable def deltaPairing (s : ℕ) (φ : ℝ → ℂ) : ℂ := (-1) ^ s * iteratedDeriv s φ 0

/-- **DLMF 2.6.22**: the test function `φ_ε(t) = e^{−εt}/(t + z)`. -/
noncomputable def stieltjesTest (z : ℂ) (ε t : ℝ) : ℂ := cexp (-((ε : ℂ) * t)) / (t + z)

/-- The continued Mellin transform of 2.6.18: `𝓜f(z) := 𝓜f₁(z) + [𝓜f₂]_cont(z)`, the second term
being the meromorphic continuation (DLMF 2.5.27, `mellinTrunc₂ContZero`) of
`𝓜f₂(z) = ∫₁^∞ t^{z−1} f(t) dt` from `ℜz < α`, with simple poles at `z = s + α`. -/
noncomputable def mellinCont (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  mellin (trunc₁ f) z + mellinTrunc₂ContZero f a (fun s : ℕ => (s : ℂ) + α) z

/-- **DLMF 2.6.18**: `cₛ = ((−1)^s/(s−1)!) 𝓜f(s)`, `s ≥ 1`, with `𝓜f` the continued Mellin
transform `mellinCont`. -/
noncomputable def stieltjesC (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (s : ℕ) : ℂ :=
  (-1) ^ s / (Nat.factorial (s - 1) : ℂ) * mellinCont f a α s

/-! ### 2.6.9: the hypotheses -/

/-- **DLMF §2.6(ii)**: `f` locally integrable on `[0, ∞)` with the expansion 2.6.9,
`f(t) ∼ ∑ aₛ t^{−s−α}` as `t → ∞`, `0 < α ≤ 1`. -/
structure StieltjesSetup (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) : Prop where
  f_loc : ∀ R : ℝ, IntegrableOn f (Icc 0 R)
  f_exp : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-((s : ℂ) + α))) f
    fun s t => a s * (t : ℂ) ^ (-((s : ℂ) + α))
  α_pos : 0 < α
  α_le : α ≤ 1

/-! ### Elementary bounds -/

/-- For `z ∈ slitPlane`, `‖t + z‖ ≥ c (1 + t)` on `t ≥ 0`. -/
theorem exists_mul_one_add_le_norm_add {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ c > 0, ∀ t : ℝ, 0 ≤ t → c * (1 + t) ≤ ‖(t : ℂ) + z‖ := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_le_norm isCompact_singleton (singleton_subset_iff.mpr hz)
  exact ⟨c, hc, fun t ht => by rw [add_comm (t : ℂ)]; exact h z rfl t ht⟩

theorem ofReal_add_ne_zero {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) + z ≠ 0 := by
  rw [add_comm]
  exact add_ofReal_ne_zero hz ht

theorem continuousOn_inv_ofReal_add {z : ℂ} (hz : z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => ((t : ℂ) + z)⁻¹) (Ici 0) :=
  ContinuousOn.inv₀ (continuous_ofReal.continuousOn.add continuousOn_const) fun _ ht =>
    ofReal_add_ne_zero hz ht

/-- `tⁿ/(t + z) = O(t^{n−1})` as `t → ∞`. -/
theorem isBigO_pow_div_add {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    (fun t : ℝ => (t : ℂ) ^ n / (t + z)) =O[atTop] fun t => t ^ ((n : ℝ) - 1) := by
  obtain ⟨c, hc, h⟩ := exists_mul_one_add_le_norm_add hz
  refine IsBigO.of_bound (1 / c) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hpos : 0 < ‖(t : ℂ) + z‖ := lt_of_lt_of_le (by positivity) (h t ht0.le)
  rw [norm_div, norm_pow, norm_real, Real.norm_of_nonneg ht0.le, Real.norm_of_nonneg
    (Real.rpow_nonneg ht0.le _), Real.rpow_sub_one ht0.ne', Real.rpow_natCast,
    div_le_iff₀ hpos]
  calc t ^ n = t ^ n / (c * t) * (c * t) := by field_simp
    _ ≤ t ^ n / (c * t) * ‖(t : ℂ) + z‖ := by
      gcongr
      linarith [h t ht0.le]
    _ = 1 / c * (t ^ n / t) * ‖(t : ℂ) + z‖ := by field_simp

/-! ### Consequences of the setup -/

namespace StieltjesSetup

variable {f : ℝ → ℂ} {a : ℕ → ℂ} {α : ℝ} (hS : StieltjesSetup f a α)
include hS

theorem hloc : LocallyIntegrableOn f (Ioi 0) := fun x hx =>
  ⟨Icc 0 (x + 1), mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by simpa using hx) (by linarith)),
    hS.f_loc (x + 1)⟩

theorem f_int₁ : IntegrableOn f (Ioc 0 1) := (hS.f_loc 1).mono_set Ioc_subset_Icc_self

omit hS in
theorem β_mono : StrictMono fun s : ℕ => ((s : ℂ) + α).re := by
  intro m n h
  simp only [add_re, natCast_re, ofReal_re]
  have := (Nat.cast_lt (α := ℝ)).mpr h
  linarith

omit hS in
theorem β_tendsto : Tendsto (fun s : ℕ => ((s : ℂ) + α).re) atTop atTop := by
  simp only [add_re, natCast_re, ofReal_re]
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

omit hS in
theorem rem_zero : stieltjesRem f a α 0 = f := by
  ext t
  simp [stieltjesRem]

omit hS in
/-- `fₙ(t) = aₙ t^{−n−α} + f_{n+1}(t)`. -/
theorem rem_eq_add_succ (n : ℕ) (t : ℝ) :
    stieltjesRem f a α n t = a n * (t : ℂ) ^ (-((n : ℂ) + α)) + stieltjesRem f a α (n + 1) t := by
  simp only [stieltjesRem, Finset.sum_range_succ]
  ring

/-- `fₙ = O(t^{−n−α})` as `t → ∞`. -/
theorem rem_isBigO (n : ℕ) : stieltjesRem f a α n =O[atTop] (· ^ (-(n + α))) := by
  have := isBigO_rpow_re_of_isBigODLMF_cpow_top (hS.f_exp.2 n)
  simp only [add_re, natCast_re, ofReal_re] at this
  exact this

theorem f_isBigO : f =O[atTop] (· ^ (-α)) := by
  have := hS.rem_isBigO 0
  simp only [rem_zero, Nat.cast_zero, zero_add] at this
  exact this

theorem locallyIntegrableOn_rem (n : ℕ) : LocallyIntegrableOn (stieltjesRem f a α n) (Ioi 0) :=
  hS.hloc.sub ((continuousOn_finsetSum _ fun _ _ =>
    continuousOn_const.mul (continuousOn_ofReal_cpow_Ioi _)).locallyIntegrableOn measurableSet_Ioi)

omit hS in
theorem continuousOn_pow_div_add {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    ContinuousOn (fun t : ℝ => (t : ℂ) ^ n / (t + z)) (Ioi 0) :=
  (continuous_ofReal.continuousOn.pow n).div (continuous_ofReal.continuousOn.add continuousOn_const)
    fun _ ht => ofReal_add_ne_zero hz (le_of_lt ht)

theorem locallyIntegrableOn_pow_div_add_mul_rem {z : ℂ} (hz : z ∈ slitPlane) (n m : ℕ) :
    LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ n / (t + z) * stieltjesRem f a α m t) (Ioi 0) :=
  (hS.locallyIntegrableOn_rem m).continuousOn_mul (continuousOn_pow_div_add hz n)
    isOpen_Ioi.isLocallyClosed

/-- `tⁿ/(t + z) · fₙ(t) = O(t^{−1−α})` as `t → ∞`. -/
theorem isBigO_pow_div_add_mul_rem {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    (fun t : ℝ => (t : ℂ) ^ n / (t + z) * stieltjesRem f a α n t) =O[atTop]
      fun t => t ^ (-(1 + α)) := by
  have h := (isBigO_pow_div_add hz n).mul (hS.rem_isBigO n)
  refine h.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [← Real.rpow_add ht]
  congr 1
  ring

/-! ### Integrability on `(0, 1]` and `(1, ∞)` -/

omit hS in
/-- A function locally integrable on `(0, ∞)` and `O(t^{−b})`, `b > 1`, at `∞` is integrable on
`(1, ∞)`. -/
theorem integrableOn_Ioi_one_of_isBigO {G : ℝ → ℂ} (hloc : LocallyIntegrableOn G (Ioi 0)) {b : ℝ}
    (hG : G =O[atTop] (· ^ (-b))) (hb : 1 < b) : IntegrableOn G (Ioi 1) := by
  have h := mellinConvergent_trunc₂ hloc hG (z := 1) (by simpa using hb)
  have h' : IntegrableOn (trunc₂ G) (Ioi 0) := by
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp
  exact (h'.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun
    (fun t ht => trunc₂_apply_of_one_lt ht) measurableSet_Ioi

omit hS in
theorem integrableOn_Ioc_mul_of_continuousOn {g h : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1))
    (hh : IntegrableOn h (Ioc 0 1)) : IntegrableOn (fun t => g t * h t) (Ioc 0 1) := by
  have hh' : IntegrableOn h (Icc 0 1) := by rwa [integrableOn_Icc_iff_integrableOn_Ioc]
  exact (hh'.continuousOn_mul hg isCompact_Icc).mono_set Ioc_subset_Icc_self

omit hS in
/-- `t^w` is integrable on `(0, 1]` for `ℜw > −1`. -/
theorem integrableOn_Ioc_cpow {w : ℂ} (hw : -1 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ w) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_cpow' hw)

/-- `tⁿ fₘ(t)` is integrable on `(0, 1]` when `m < n + 2 − α`. -/
theorem integrableOn_Ioc_pow_mul_rem (n m : ℕ) (hm : (m : ℝ) < n + 2 - α) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α m t) (Ioc 0 1) := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * f t) (Ioc 0 1) :=
    integrableOn_Ioc_mul_of_continuousOn (continuous_ofReal.continuousOn.pow n) hS.f_int₁
  have h2 : IntegrableOn (fun t : ℝ => ∑ s ∈ Finset.range m,
      a s * (t : ℂ) ^ ((n : ℂ) - ((s : ℂ) + α))) (Ioc 0 1) := by
    refine integrable_finsetSum _ fun s hs => ?_
    have hs' : (s : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hs
    refine (integrableOn_Ioc_cpow ?_).const_mul (a s)
    simp only [sub_re, natCast_re, add_re, ofReal_re]
    linarith
  refine (h1.sub h2).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp only [Pi.sub_apply, stieltjesRem, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_left_comm, ← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), sub_eq_add_neg]

/-- `tⁿ fₙ(t)/(t + z)` is integrable on `(0, ∞)` for `z ∈ slitPlane` (the integral of 2.6.30). -/
theorem integrableOn_pow_mul_rem_div {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * stieltjesRem f a α n t / (t + z)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have := integrableOn_Ioc_mul_of_continuousOn
      ((continuousOn_inv_ofReal_add hz).mono Icc_subset_Ici_self)
      (hS.integrableOn_Ioc_pow_mul_rem n n (by linarith [hS.α_le]))
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioc
    ring
  · refine (integrableOn_Ioi_one_of_isBigO (hS.locallyIntegrableOn_pow_div_add_mul_rem hz n n)
      (hS.isBigO_pow_div_add_mul_rem hz n) (by linarith [hS.α_pos])).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    ring

/-- **Convergence of 2.6.8**: `𝓢f(z)` converges absolutely for `|ph z| < π`. -/
theorem integrableOn_stieltjesT {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ => f t / (t + z)) (Ioi 0) := by
  simpa [rem_zero] using hS.integrableOn_pow_mul_rem_div hz 0

/-! ### The continued Mellin transform -/

omit hS in
/-- `𝓜f₁(z)` converges for `ℜz ≥ 1` when `f` is integrable on `(0, 1]`. -/
theorem mellinConvergent_trunc₁_of_integrableOn {g : ℝ → ℂ} (hg : IntegrableOn g (Ioc 0 1)) {z : ℂ}
    (hz : 1 ≤ z.re) : MellinConvergent (trunc₁ g) z := by
  have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * g t) (Ioc 0 1) := by
    refine Integrable.bdd_mul (c := 1) hg (((continuousOn_ofReal_cpow_Ioi (z - 1)).mono
      Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re]
    exact Real.rpow_le_one ht.1.le ht.2 (by linarith)
  have : (fun t : ℝ => (t : ℂ) ^ (z - 1) • trunc₁ g t) =
      (Ioc 0 1).indicator fun t : ℝ => (t : ℂ) ^ (z - 1) * g t := by
    ext t
    simp only [trunc₁, smul_eq_mul, indicator]
    split_ifs <;> simp
  rw [MellinConvergent, this]
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr hI).integrableOn

omit hS in
/-- `𝓜(f − ∑_{s<N} cₛ t^{wₛ})₁(z) = 𝓜f₁(z) − ∑_{s<N} cₛ/(z + wₛ)` for `ℜz + ℜwₛ > 0`. -/
theorem mellin_trunc₁_sub_sum {g : ℝ → ℂ} {z : ℂ} (hg : MellinConvergent (trunc₁ g) z) {N : ℕ}
    {c w : ℕ → ℂ} (hw : ∀ s < N, 0 < z.re + (w s).re) :
    MellinConvergent (trunc₁ fun t => g t - ∑ s ∈ Finset.range N, c s * (t : ℂ) ^ w s) z ∧
      mellin (trunc₁ fun t => g t - ∑ s ∈ Finset.range N, c s * (t : ℂ) ^ w s) z =
        mellin (trunc₁ g) z - ∑ s ∈ Finset.range N, c s / (z + w s) := by
  induction N with
  | zero => exact ⟨by simpa using hg, by simp⟩
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih fun s hs => hw s (hs.trans (Nat.lt_succ_self N))
    have hpow := hasMellin_cpow_Ioc (w N) (hw N (Nat.lt_succ_self N))
    have hterm : HasMellin ((Ioc 0 1).indicator fun t : ℝ => c N * (t : ℂ) ^ w N) z
        (c N * (1 / (z + w N))) := by
      have h1 : ((Ioc 0 1).indicator fun t : ℝ => c N * (t : ℂ) ^ w N) =
          fun t => c N • (Ioc 0 1).indicator (fun t : ℝ => (t : ℂ) ^ w N) t := by
        ext t
        simp [indicator]
      rw [h1, ← hpow.2]
      exact ⟨hpow.1.const_smul (c N), mellin_const_smul _ _ _⟩
    have hsplit : (trunc₁ fun t => g t - ∑ s ∈ Finset.range (N + 1), c s * (t : ℂ) ^ w s) =
        fun t => trunc₁ (fun t => g t - ∑ s ∈ Finset.range N, c s * (t : ℂ) ^ w s) t -
          (Ioc 0 1).indicator (fun t : ℝ => c N * (t : ℂ) ^ w N) t := by
      ext t
      by_cases ht : t ∈ Ioc 0 1
      · simp only [trunc₁, Finset.sum_range_succ, indicator_of_mem ht]
        ring
      · simp only [trunc₁, indicator_of_notMem ht, sub_zero]
    have := hasMellin_sub ih1 hterm.1
    rw [← hsplit, hterm.2] at this
    refine ⟨this.1, ?_⟩
    rw [this.2, ih2, Finset.sum_range_succ, one_div, ← div_eq_mul_inv]
    ring

/-- `mellinCont` agrees with `𝓜f` on the strip where the Mellin integral converges. -/
theorem mellinCont_eq_mellin {z : ℂ} (hz : z.re < α) (h₁ : MellinConvergent (trunc₁ f) z) :
    mellinCont f a α z = mellin f z := by
  rw [mellinCont, mellinTrunc₂ContZero_eq hS.hloc β_mono β_tendsto hS.f_exp (by simpa using hz),
    ← mellin_eq_trunc_add h₁ (mellinConvergent_trunc₂ hS.hloc hS.f_isBigO hz)]

/-- The explicit continuation 2.5.25 for `𝓜f₂`: for `ℜz < n + 1 + α` and `z ≠ s + α`, `s ≤ n`,
`[𝓜f₂]_cont(z) = −∑_{s≤n} aₛ/(z − s − α) + ∫₁^∞ t^{z−1} f_{n+1}(t) dt`. -/
theorem mellinTrunc₂ContZero_eq_sum_add {n : ℕ} {z : ℂ} (hz : z.re < n + 1 + α)
    (hz' : ∀ s ≤ n, z ≠ s + α) :
    mellinTrunc₂ContZero f a (fun s : ℕ => (s : ℂ) + α) z =
      -∑ s ∈ Finset.range (n + 1), a s / (z - ((s : ℂ) + α)) +
        mellin (trunc₂ (stieltjesRem f a α (n + 1))) z := by
  have hmem : -z ∈ contDomain (fun s : ℕ => (s : ℂ) + α) (n + 1) := by
    refine ⟨?_, fun s hs h => ?_⟩
    · simp only [add_re, natCast_re, ofReal_re, neg_re, one_re, Nat.cast_add, Nat.cast_one]
      linarith
    · exact hz' s (Nat.lt_succ_iff.mp hs) (neg_injective h)
  rw [mellinTrunc₂ContZero, mellinTrunc₁Cont_eq β_mono (isGenAsympExpansion_inv hS.f_exp)
    (locallyIntegrableOn_comp_inv hS.hloc) hmem, mellinTrunc₁Ext, mellin_trunc₂_eq_inv]
  have hfun : truncRem (fun t : ℝ => f t⁻¹) a (fun s : ℕ => (s : ℂ) + α) (n + 1) =
      trunc₁ fun u : ℝ => stieltjesRem f a α (n + 1) u⁻¹ := by
    ext u
    simp only [truncRem, trunc₁, indicator]
    split_ifs with hu
    · simp only [expPartial, stieltjesRem]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ofReal_inv_cpow_neg hu.1]
    · rfl
  rw [hfun]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← div_neg, neg_sub, neg_add_eq_sub]

/-- **The key evaluation**: for `n + α < ℜz < n + 1 + α` with `ℜz ≥ 1`,
`𝓜f(z) = ∫₀^∞ t^{z−1} f_{n+1}(t) dt`, and the integral converges absolutely. -/
theorem mellinCont_eq_mellin_rem {n : ℕ} {z : ℂ} (hz1 : 1 ≤ z.re) (hz2 : n + α < z.re)
    (hz3 : z.re < n + 1 + α) :
    MellinConvergent (stieltjesRem f a α (n + 1)) z ∧
      mellinCont f a α z = mellin (stieltjesRem f a α (n + 1)) z := by
  have hw : ∀ s < n + 1, 0 < z.re + (-((s : ℂ) + α)).re := fun s hs => by
    have : (s : ℝ) ≤ n := Nat.cast_le.mpr (Nat.lt_succ_iff.mp hs)
    simp only [neg_re, add_re, natCast_re, ofReal_re]
    linarith
  obtain ⟨h₁, e₁⟩ := mellin_trunc₁_sub_sum (mellinConvergent_trunc₁_of_integrableOn hS.f_int₁ hz1)
    hw (c := a)
  have h₂ : MellinConvergent (trunc₂ (stieltjesRem f a α (n + 1))) z :=
    mellinConvergent_trunc₂ (hS.locallyIntegrableOn_rem (n + 1)) (hS.rem_isBigO (n + 1))
      (by push_cast; linarith)
  have hz' : ∀ s ≤ n, z ≠ s + α := fun s hs h => by
    have := congrArg Complex.re h
    simp only [add_re, natCast_re, ofReal_re] at this
    have : (s : ℝ) ≤ n := Nat.cast_le.mpr hs
    linarith
  have hrem : (fun t : ℝ => f t - ∑ s ∈ Finset.range (n + 1), a s * (t : ℂ) ^ (-((s : ℂ) + α))) =
      stieltjesRem f a α (n + 1) := rfl
  rw [hrem] at h₁ e₁
  refine ⟨?_, ?_⟩
  · have := hasMellin_add h₁ h₂
    simpa only [trunc₁_add_trunc₂] using this.1
  · rw [mellinCont, hS.mellinTrunc₂ContZero_eq_sum_add hz3 hz', mellin_eq_trunc_add h₁ h₂, e₁]
    have : ∑ s ∈ Finset.range (n + 1), a s / (z + -((s : ℂ) + α)) =
        ∑ s ∈ Finset.range (n + 1), a s / (z - ((s : ℂ) + α)) :=
      Finset.sum_congr rfl fun s _ => by rw [← sub_eq_add_neg]
    rw [this]
    ring

/-- `∫₀^∞ τⁿ f_{n+1}(τ) dτ` converges absolutely for `0 < α < 1`. -/
theorem mellinConvergent_rem_succ (hα : α < 1) (n : ℕ) :
    MellinConvergent (stieltjesRem f a α (n + 1)) ((n : ℂ) + 1) :=
  (hS.mellinCont_eq_mellin_rem (n := n) (by simp) (by simp; linarith)
    (by simp; linarith [hS.α_pos])).1

/-- `𝓜f(n + 1) = ∫₀^∞ τⁿ f_{n+1}(τ) dτ` for `0 < α < 1`. -/
theorem mellinCont_succ_eq (hα : α < 1) (n : ℕ) :
    mellinCont f a α ((n : ℂ) + 1) =
      ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ := by
  rw [(hS.mellinCont_eq_mellin_rem (n := n) (by simp) (by simp; linarith)
    (by simp; linarith [hS.α_pos])).2, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  rw [add_sub_cancel_right, cpow_natCast, smul_eq_mul]

/-! ### 2.6.25 -/

/-- **DLMF 2.6.25**: `⟨f, φ_ε⟩ → 𝓢f(z)` as `ε → 0+`, by dominated convergence. -/
theorem dlmf_2_6_25 {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun ε : ℝ => pairing f (stieltjesTest z ε)) (𝓝[>] 0) (𝓝 (stieltjesT f z)) := by
  have hint := hS.integrableOn_stieltjesT hz
  simp only [pairing, stieltjesTest, stieltjesT]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t / (t + z)‖)
    (Eventually.of_forall fun ε => ?_) ?_ hint.norm (Eventually.of_forall fun t => ?_)
  · have : (fun t : ℝ => f t * (cexp (-((ε : ℂ) * t)) / (t + z))) =
        fun t : ℝ => cexp (-((ε : ℂ) * t)) * (f t / (t + z)) := by
      ext t
      ring
    rw [this]
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hint.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : f t * (cexp (-((ε : ℂ) * t)) / (t + z)) = cexp (-((ε : ℂ) * t)) * (f t / (t + z)) := by
      ring
    rw [this, norm_mul, ← ofReal_mul, ← ofReal_neg, ← ofReal_exp, norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hε' : (0 : ℝ) < ε := hε
    have ht' : (0 : ℝ) < t := ht
    calc Real.exp (-(ε * t)) * ‖f t / (t + z)‖ ≤ 1 * ‖f t / (t + z)‖ := by
          gcongr
          rw [Real.exp_le_one_iff]
          nlinarith
      _ = ‖f t / (t + z)‖ := one_mul _
  · have hc : Tendsto (fun ε : ℝ => f t * (cexp (-((ε : ℂ) * t)) / (t + z))) (𝓝 0)
        (𝓝 (f t * (cexp (-(((0 : ℝ) : ℂ) * t)) / (t + z)))) := by
      refine Continuous.tendsto ?_ 0
      fun_prop
    simp only [ofReal_zero, zero_mul, neg_zero, exp_zero, one_div] at hc
    rw [div_eq_mul_inv]
    exact hc.mono_left nhdsWithin_le_nhds

end StieltjesSetup

end Azurite.DLMF
