/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18ODE
import Azurite.DLMF.Chapter1.Section14HilbertDense

/-!
# DLMF §1.18(viii), Example 1: a bound state for every attractive well

https://dlmf.nist.gov/1.18.viii

DLMF, after Simon (1976), states that `−d²/dx² + q` on `ℝ` has a negative eigenvalue whenever
`q < 0` on some interval and `∫ q ≤ 0`. This file proves it for continuous `q` vanishing outside
`[−R, R]` (`dlmf_1_18_viii_simon`): there are `κ > 0` and a nonzero `ψ ∈ L²(ℝ)`, twice
differentiable, with `−ψ″ + qψ = −κ²ψ`. DLMF omits Simon's decay hypothesis
`∫ (1 + x²)|q| < ∞`; compact support is the case proven here.

The proof is a shooting argument, not min-max. Let `u_κ` solve `u″ = (q + κ²)u` with
`u(−R) = 1` and `u′(−R) = κ`, so `u_κ = e^{κ(x+R)}` on `(−∞, −R]` (`simonU_left`). A zero of the
matching function `G(κ) = u_κ′(R) + κ u_κ(R)` (`simonG`) makes `u_κ = u_κ(R) e^{−κ(x−R)}` on
`[R, ∞)` (`simonU_right`), so `u_κ ∈ L²`. The steps:

* For `κ = k₀` with `k₀² > sup |q|`, `(u u′)′ = u′² + (q + k₀²)u² ≥ 0`, so `u u′ ≥ k₀`, so `u > 0`
  on `[−R, R]` and `G(k₀) > 0` (`simonU_k0_pos`, `simonG_k0_pos`).
* If some `u_κ` with `κ ∈ [0, k₀]` vanishes on `[−R, R]`, the largest such `κ₁` (a compact set)
  has `u_{κ₁} ≥ 0` there, by continuity from above. Its zero cannot be interior, since that
  would be a double zero, so it is at `R`. There `u′(R) < 0`, so `G(κ₁) < 0`.
* Otherwise `u₀ > 0` on `[−R, R]`, and Jacobi's identity `∫ q = u₀′(R)/u₀(R) + ∫ (u₀′/u₀)²`
  gives `G(0) = u₀′(R) < 0`, unless `q = 0` (`simonG_zero_neg`).
* The intermediate value theorem gives `κ > 0` with `G(κ) = 0` (`exists_simonG_eq_zero`).

The solutions come from `Section18ODE` (Picard iteration, joint continuity in `(κ, x)`,
Grönwall uniqueness). The two-dimensional analog is not formalized.
-/

open Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-- The decay rate `κ`, clamped to `[0, k₀]` so the shooting potential stays bounded. -/
noncomputable def simonClamp (k0 κ : ℝ) : ℝ := max 0 (min κ k0)

/-- The shooting potential `q(x) + κ²`. -/
noncomputable def simonV (q : ℝ → ℝ) (k0 κ x : ℝ) : ℝ := q x + simonClamp k0 κ ^ 2

/-- The shooting solution: `u″ = (q + κ²) u`, `u(−R) = 1`, `u′(−R) = κ`. -/
noncomputable def simonU (q : ℝ → ℝ) (k0 R κ x : ℝ) : ℝ :=
  odeSol (simonV q k0) (fun _ => 1) (simonClamp k0) (-R) κ x

/-- The derivative of the shooting solution. -/
noncomputable def simonUD (q : ℝ → ℝ) (k0 R κ x : ℝ) : ℝ :=
  odeSolD (simonV q k0) (fun _ => 1) (simonClamp k0) (-R) κ x

/-- The matching function `u′(R) + κ u(R)`; a zero gives a decaying solution on `[R, ∞)`. -/
noncomputable def simonG (q : ℝ → ℝ) (k0 R κ : ℝ) : ℝ :=
  simonUD q k0 R κ R + κ * simonU q k0 R κ R

theorem simonClamp_of_mem {k0 κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ k0) : simonClamp k0 κ = κ := by
  rw [simonClamp, min_eq_left h1, max_eq_right h0]

theorem continuous_simonClamp (k0 : ℝ) : Continuous (simonClamp k0) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem simonClamp_nonneg (k0 κ : ℝ) : 0 ≤ simonClamp k0 κ := le_max_left _ _

theorem simonClamp_le {k0 : ℝ} (hk0 : 0 ≤ k0) (κ : ℝ) : simonClamp k0 κ ≤ k0 :=
  max_le hk0 (min_le_right _ _)

section Shooting

variable {q : ℝ → ℝ} (hq : Continuous q) {Mq : ℝ} (hMq : ∀ x, |q x| ≤ Mq) {k0 : ℝ}
  (hk0 : 0 ≤ k0) (R : ℝ)

include hq in
theorem continuous_simonV : Continuous fun p : ℝ × ℝ => simonV q k0 p.1 p.2 :=
  (hq.comp continuous_snd).add (((continuous_simonClamp k0).comp continuous_fst).pow 2)

include hMq hk0 in
theorem abs_simonV_le (κ t : ℝ) : |simonV q k0 κ t| ≤ Mq + k0 ^ 2 := by
  unfold simonV
  have h0 := simonClamp_nonneg k0 κ
  have h1 := simonClamp_le hk0 κ
  calc |q t + simonClamp k0 κ ^ 2| ≤ |q t| + |simonClamp k0 κ ^ 2| := abs_add_le _ _
    _ ≤ Mq + k0 ^ 2 := by
      rw [abs_of_nonneg (pow_nonneg h0 2)]
      gcongr
      exact hMq t

include hk0 in
theorem simon_hBa (κ : ℝ) : |(fun _ : ℝ => (1 : ℝ)) κ| ≤ 1 + k0 := by simp; linarith

include hk0 in
theorem simon_hBb (κ : ℝ) : |simonClamp k0 κ| ≤ 1 + k0 := by
  rw [abs_of_nonneg (simonClamp_nonneg k0 κ)]; linarith [simonClamp_le hk0 κ]

include hq hMq hk0 in
theorem hasDerivAt_simonU (κ x : ℝ) :
    HasDerivAt (simonU q k0 R κ) (simonUD q k0 R κ x) x :=
  hasDerivAt_odeSol (-R) (continuous_simonV hq) continuous_const (continuous_simonClamp k0)
    (abs_simonV_le hMq hk0) (simon_hBa hk0) (simon_hBb hk0) κ x

include hq hMq hk0 in
theorem hasDerivAt_simonUD (κ x : ℝ) :
    HasDerivAt (simonUD q k0 R κ) (simonV q k0 κ x * simonU q k0 R κ x) x :=
  hasDerivAt_odeSolD (-R) (continuous_simonV hq) continuous_const (continuous_simonClamp k0)
    (abs_simonV_le hMq hk0) (simon_hBa hk0) (simon_hBb hk0) κ x

include hq hMq hk0 in
theorem continuous_simonU : Continuous fun p : ℝ × ℝ => simonU q k0 R p.1 p.2 :=
  continuous_odeSol (-R) (continuous_simonV hq) continuous_const (continuous_simonClamp k0)
    (abs_simonV_le hMq hk0) (simon_hBa hk0) (simon_hBb hk0)

include hq hMq hk0 in
theorem continuous_simonUD : Continuous fun p : ℝ × ℝ => simonUD q k0 R p.1 p.2 :=
  continuous_odeSolD (-R) (continuous_simonV hq) continuous_const (continuous_simonClamp k0)
    (abs_simonV_le hMq hk0) (simon_hBa hk0) (simon_hBb hk0)

include hq hMq hk0 in
theorem simonU_init (κ : ℝ) : simonU q k0 R κ (-R) = 1 :=
  odeSol_init (-R) (continuous_simonV hq) continuous_const (continuous_simonClamp k0)
    (abs_simonV_le hMq hk0) (simon_hBa hk0) (simon_hBb hk0) κ

theorem simonUD_init (κ : ℝ) : simonUD q k0 R κ (-R) = simonClamp k0 κ :=
  odeSolD_init (-R) κ

include hq hMq hk0 in
theorem continuous_simonU_x (κ : ℝ) : Continuous (simonU q k0 R κ) :=
  (continuous_simonU hq hMq hk0 R).comp (continuous_const.prodMk continuous_id)

include hq hMq hk0 in
theorem continuous_simonG : Continuous (simonG q k0 R) :=
  ((continuous_simonUD hq hMq hk0 R).comp (continuous_id.prodMk continuous_const)).add
    (continuous_id.mul
      ((continuous_simonU hq hMq hk0 R).comp (continuous_id.prodMk continuous_const)))

include hq hMq hk0 in
/-- A shooting solution never has a double zero, since it starts at `u(−R) = 1`. -/
theorem simonU_not_double_zero (κ x1 : ℝ) (h0 : simonU q k0 R κ x1 = 0)
    (h1 : simonUD q k0 R κ x1 = 0) : False := by
  have := ode2_eq_zero (abs_simonV_le hMq hk0 κ) (hasDerivAt_simonU hq hMq hk0 R κ)
    (hasDerivAt_simonUD hq hMq hk0 R κ) h0 h1 (-R)
  rw [simonU_init hq hMq hk0] at this
  exact one_ne_zero this

/-! ### Large `κ`: no zero and `G(k₀) > 0` -/

include hq hMq hk0 in
theorem simonU_mul_UD_k0 (hk0M : Mq < k0 ^ 2) (x : ℝ) (hx : -R ≤ x) :
    k0 ≤ simonU q k0 R k0 x * simonUD q k0 R k0 x := by
  have hc : simonClamp k0 k0 = k0 := simonClamp_of_mem hk0 le_rfl
  have hVpos : ∀ x, 0 < simonV q k0 k0 x := fun x => by
    have := neg_abs_le (q x)
    have := hMq x
    simp only [simonV, hc]
    linarith
  have hmono := monotone_of_hasDerivAt_nonneg
    (f := fun x => simonU q k0 R k0 x * simonUD q k0 R k0 x)
    (fun x => (hasDerivAt_simonU hq hMq hk0 R k0 x).mul (hasDerivAt_simonUD hq hMq hk0 R k0 x))
    fun x => by
      have := hVpos x
      have := mul_self_nonneg (simonUD q k0 R k0 x)
      have := mul_self_nonneg (simonU q k0 R k0 x)
      simp only [Pi.zero_apply]
      nlinarith
  have := hmono hx
  simp only [simonU_init hq hMq hk0, simonUD_init, hc, one_mul] at this
  exact this

include hq hMq hk0 in
theorem simonU_k0_pos (hk0M : Mq < k0 ^ 2) (x : ℝ) (hx : -R ≤ x) :
    0 < simonU q k0 R k0 x := by
  have hk0p : 0 < k0 := by
    rcases hk0.lt_or_eq with h | h
    · exact h
    · have := (abs_nonneg (q 0)).trans (hMq 0)
      rw [← h] at hk0M
      linarith
  have hne : ∀ y, -R ≤ y → simonU q k0 R k0 y ≠ 0 := fun y hy h0 => by
    have := simonU_mul_UD_k0 hq hMq hk0 R hk0M y hy
    rw [h0, zero_mul] at this
    linarith
  by_contra hneg
  push Not at hneg
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hx
    (continuous_simonU_x hq hMq hk0 R k0).continuousOn
    (show (0 : ℝ) ∈ Icc (simonU q k0 R k0 x) (simonU q k0 R k0 (-R)) by
      rw [simonU_init hq hMq hk0]; exact ⟨hneg, zero_le_one⟩)
  exact hne y hy.1 hy0

include hq hMq hk0 in
theorem simonG_k0_pos (hk0M : Mq < k0 ^ 2) (hR : 0 ≤ R) : 0 < simonG q k0 R k0 := by
  have hu := simonU_k0_pos hq hMq hk0 R hk0M R (by linarith)
  have hk0p : 0 < k0 := by
    have := simonU_mul_UD_k0 hq hMq hk0 R hk0M R (by linarith)
    rcases hk0.lt_or_eq with h | h
    · exact h
    · have := (abs_nonneg (q 0)).trans (hMq 0)
      rw [← h] at hk0M
      linarith
  have hud := pos_of_mul_pos_right
    (hk0p.trans_le (simonU_mul_UD_k0 hq hMq hk0 R hk0M R (by linarith))) hu.le
  unfold simonG
  positivity

/-! ### `κ = 0`: Jacobi's identity -/

include hq hMq hk0 in
/-- If the zero-energy solution has no zero on `[−R, R]`, Jacobi's identity
`∫ q = u′(R)/u(R) + ∫ (u′/u)²` forces `u′(R) < 0`, i.e. `G(0) < 0`, unless `q = 0`. -/
theorem simonG_zero_neg (hR : 0 < R) (hpos : ∀ x ∈ Icc (-R) R, 0 < simonU q k0 R 0 x)
    (hsupp : ∀ x, R ≤ |x| → q x = 0) (hint : ∫ x in -R..R, q x ≤ 0) (hneg : ∃ x, q x < 0) :
    simonG q k0 R 0 < 0 := by
  set u := simonU q k0 R 0
  set u' := simonUD q k0 R 0
  have hc : simonClamp k0 0 = 0 := simonClamp_of_mem le_rfl hk0
  have hV : ∀ x, simonV q k0 0 x = q x := fun x => by simp [simonV, hc]
  have hu := hasDerivAt_simonU hq hMq hk0 R 0
  have hu' := hasDerivAt_simonUD hq hMq hk0 R 0
  have hcu : Continuous u := continuous_simonU_x hq hMq hk0 R 0
  have hcu' : Continuous u' :=
    (continuous_simonUD hq hMq hk0 R).comp (continuous_const.prodMk continuous_id)
  have hRR : -R ≤ R := by linarith
  have hI : uIcc (-R) R = Icc (-R) R := uIcc_of_le hRR
  set h : ℝ → ℝ := fun x => u' x / u x
  have hch : ContinuousOn h (Icc (-R) R) :=
    hcu'.continuousOn.div hcu.continuousOn fun x hx => (hpos x hx).ne'
  have hderiv : ∀ x ∈ uIcc (-R) R, HasDerivAt h (q x - h x ^ 2) x := fun x hx => by
    rw [hI] at hx
    have hx0 : simonU q k0 R 0 x ≠ 0 := (hpos x hx).ne'
    refine ((hu' x).div (hu x) hx0).congr_deriv ?_
    rw [hV]
    simp only [h, u, u']
    field_simp
  have hcont : ContinuousOn (fun x => h x ^ 2) (uIcc (-R) R) := by rw [hI]; exact hch.pow 2
  have hqi : IntervalIntegrable q volume (-R) R := hq.intervalIntegrable _ _
  have hhi : IntervalIntegrable (fun x => h x ^ 2) volume (-R) R := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hqi.sub hhi)
  rw [intervalIntegral.integral_sub hqi hhi] at hftc
  have hinit : h (-R) = 0 := by simp [h, u', u, simonUD_init, hc]
  rw [hinit, sub_zero] at hftc
  have hG : simonG q k0 R 0 = u' R := by simp [simonG, u']
  rw [hG]
  by_contra hG0
  push Not at hG0
  have hhR : 0 ≤ h R := div_nonneg hG0 (hpos R ⟨hRR, le_rfl⟩).le
  have hsq : ∫ x in -R..R, h x ^ 2 ≤ 0 := by linarith
  -- `h` vanishes on `(−R, R)`.
  have hzero : ∀ c ∈ Ioo (-R) R, h c = 0 := by
    intro c hc0
    by_contra hcne
    set S := Ioo (-R) R ∩ (fun x => h x ^ 2) ⁻¹' Ioi 0
    have hSo : IsOpen S :=
      ((hch.mono Ioo_subset_Icc_self).pow 2).isOpen_inter_preimage isOpen_Ioo isOpen_Ioi
    have hcS : c ∈ S := ⟨hc0, by simp only [mem_preimage, mem_Ioi]; positivity⟩
    have hSpos := hSo.measure_pos volume ⟨c, hcS⟩
    have hsub : S ⊆ Function.support (fun x => h x ^ 2) ∩ Ioc (-R) R := fun x hx =>
      ⟨(mem_Ioi.mp hx.2).ne', Ioo_subset_Ioc_self hx.1⟩
    have := (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun x => sq_nonneg (h x)) hhi).mpr ⟨by linarith, hSpos.trans_le
        (measure_mono hsub)⟩
    linarith
  -- Hence `u′ = 0` there, so `q u = u″ = 0`, so `q = 0`.
  have hq0 : ∀ c ∈ Ioo (-R) R, q c = 0 := by
    intro c hc0
    have hev : u' =ᶠ[𝓝 c] fun _ => 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hc0] with y hy
      have := hzero y hy
      simp only [h, div_eq_zero_iff] at this
      exact this.resolve_right (hpos y (Ioo_subset_Icc_self hy)).ne'
    have h2 := (hu' c).unique ((hasDerivAt_const c (0 : ℝ)).congr_of_eventuallyEq hev)
    rw [hV] at h2
    exact (mul_eq_zero.mp h2).resolve_right (hpos c (Ioo_subset_Icc_self hc0)).ne'
  obtain ⟨x, hx⟩ := hneg
  have : q x = 0 := by
    rcases lt_or_ge |x| R with h' | h'
    · exact hq0 x (abs_lt.mp h')
    · exact hsupp x h'
  linarith

/-! ### The shooting argument -/

include hq hMq hk0 in
/-- There is `κ ∈ (0, k₀]` with `u′(R) + κ u(R) = 0`. -/
theorem exists_simonG_eq_zero (hR : 0 < R) (hk0M : Mq < k0 ^ 2)
    (hsupp : ∀ x, R ≤ |x| → q x = 0) (hint : ∫ x in -R..R, q x ≤ 0) (hneg : ∃ x, q x < 0) :
    ∃ κ, 0 < κ ∧ κ ≤ k0 ∧ simonG q k0 R κ = 0 := by
  have hRR : -R ≤ R := by linarith
  have hG0 := simonG_k0_pos hq hMq hk0 R hk0M hR.le
  have hcG := continuous_simonG hq hMq hk0 R
  have hcu := continuous_simonU hq hMq hk0 R
  have hivt : ∀ κ1, 0 ≤ κ1 → κ1 ≤ k0 → simonG q k0 R κ1 < 0 →
      ∃ κ, 0 < κ ∧ κ ≤ k0 ∧ simonG q k0 R κ = 0 := fun κ1 h0 h1 hneg1 => by
    obtain ⟨κ, hκ, hGκ⟩ := intermediate_value_Icc h1 hcG.continuousOn
      (show (0 : ℝ) ∈ Icc (simonG q k0 R κ1) (simonG q k0 R k0) from ⟨hneg1.le, hG0.le⟩)
    refine ⟨κ, h0.trans_lt (lt_of_le_of_ne hκ.1 ?_), hκ.2, hGκ⟩
    rintro rfl
    linarith
  set K : Set (ℝ × ℝ) := Icc 0 k0 ×ˢ Icc (-R) R
  set Z : Set ℝ := Prod.fst '' (K ∩ {p | simonU q k0 R p.1 p.2 ≤ 0})
  have hZc : IsCompact Z :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le hcu continuous_const)).image continuous_fst
  rcases Z.eq_empty_or_nonempty with hZ | hZ
  · refine hivt 0 le_rfl hk0 (simonG_zero_neg hq hMq hk0 R hR (fun x hx => ?_) hsupp hint hneg)
    by_contra hle
    push Not at hle
    have : (0 : ℝ) ∈ Z := ⟨(0, x), ⟨⟨⟨le_rfl, hk0⟩, hx⟩, hle⟩, rfl⟩
    rw [hZ] at this
    exact this
  · obtain ⟨⟨κ1, x⟩, ⟨⟨hk1, hx⟩, hux⟩, hκ1⟩ := hZc.sSup_mem hZ
    change κ1 ∈ Icc 0 k0 at hk1
    change x ∈ Icc (-R) R at hx
    change simonU q k0 R κ1 x ≤ 0 at hux
    change κ1 = sSup Z at hκ1
    have habove : ∀ κ, κ1 < κ → κ ≤ k0 → ∀ y ∈ Icc (-R) R, 0 < simonU q k0 R κ y := by
      intro κ h1 h2 y hy
      by_contra hle
      push Not at hle
      have hmem : κ ∈ Z := ⟨(κ, y), ⟨⟨⟨hk1.1.trans h1.le, h2⟩, hy⟩, hle⟩, rfl⟩
      have := (le_csSup hZc.bddAbove hmem).trans_eq hκ1.symm
      linarith
    have hlt : κ1 < k0 := lt_of_le_of_ne hk1.2 fun h => by
      rw [h] at hux
      linarith [simonU_k0_pos hq hMq hk0 R hk0M x hx.1]
    have hnn : ∀ y ∈ Icc (-R) R, 0 ≤ simonU q k0 R κ1 y := fun y hy => by
      have ht : Tendsto (fun κ => simonU q k0 R κ y) (𝓝[>] κ1) (𝓝 (simonU q k0 R κ1 y)) :=
        ((hcu.comp (continuous_id.prodMk continuous_const)).tendsto κ1).mono_left
          nhdsWithin_le_nhds
      refine ge_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT hlt] with κ hκ
      exact (habove κ hκ.1 hκ.2.le y hy).le
    have hux0 : simonU q k0 R κ1 x = 0 := le_antisymm hux (hnn x hx)
    have hxR : x = R := by
      by_contra hxR
      have hxlt : x < R := lt_of_le_of_ne hx.2 hxR
      have hxm : -R < x := lt_of_le_of_ne hx.1 fun h => by
        rw [← h, simonU_init hq hMq hk0] at hux0
        exact one_ne_zero hux0
      have hmin : IsLocalMin (simonU q k0 R κ1) x := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hxm, hxlt⟩] with y hy
        rw [hux0]
        exact hnn y (Ioo_subset_Icc_self hy)
      exact simonU_not_double_zero hq hMq hk0 R κ1 x hux0
        (hmin.hasDerivAt_eq_zero (hasDerivAt_simonU hq hMq hk0 R κ1 x))
    subst hxR
    -- `u′(R) ≤ 0` from the left difference quotients, and `≠ 0` by uniqueness.
    have hd := (hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_simonU hq hMq hk0 x κ1 x)).mono_left
      (nhdsLT_le_nhdsNE x)
    have hle : simonUD q k0 x κ1 x ≤ 0 := by
      refine le_of_tendsto hd ?_
      filter_upwards [Ioo_mem_nhdsLT (show -x < x by linarith)] with y hy
      rw [slope_def_field, hux0, sub_zero]
      exact div_nonpos_of_nonneg_of_nonpos (hnn y (Ioo_subset_Icc_self hy)) (by linarith [hy.2])
    have hne : simonUD q k0 x κ1 x ≠ 0 := simonU_not_double_zero hq hMq hk0 x κ1 x hux0
    refine hivt κ1 hk1.1 hk1.2 ?_
    rw [simonG, hux0, mul_zero, add_zero]
    exact lt_of_le_of_ne hle hne

/-! ### Exponential tails -/

include hq hMq hk0 in
/-- On `(−∞, −R]` the shooting solution is `e^{κ(x + R)}`. -/
theorem simonU_left (hsupp : ∀ x, R ≤ |x| → q x = 0) (hR : 0 ≤ R) {κ : ℝ} (h0 : 0 ≤ κ)
    (h1 : κ ≤ k0) (x : ℝ) (hx : x ≤ -R) : simonU q k0 R κ x = Real.exp (κ * (x + R)) := by
  have hc := simonClamp_of_mem h0 h1
  have hqx : ∀ y, y ≤ -R → q y = 0 := fun y hy =>
    hsupp y (by rw [abs_of_nonpos (by linarith)]; linarith)
  have he : ∀ y, HasDerivAt (fun y => Real.exp (κ * (y + R))) (κ * Real.exp (κ * (y + R))) y :=
    fun y => (((hasDerivAt_id y).add_const R).const_mul κ).exp.congr_deriv (by simp; ring)
  have := ode2_eq_zero_left (W := fun _ => κ ^ 2) (K := κ ^ 2) (x1 := -R)
    (w := fun y => simonU q k0 R κ y - Real.exp (κ * (y + R)))
    (w' := fun y => simonUD q k0 R κ y - κ * Real.exp (κ * (y + R)))
    (fun _ _ => by rw [abs_of_nonneg (sq_nonneg κ)])
    (fun y _ => (hasDerivAt_simonU hq hMq hk0 R κ y).sub (he y))
    (fun y hy => ((hasDerivAt_simonUD hq hMq hk0 R κ y).sub ((he y).const_mul κ)).congr_deriv
      (by simp only [simonV, hqx y hy, hc]; ring))
    (by simp [simonU_init hq hMq hk0]) (by simp [simonUD_init, hc]) x hx
  linarith

include hq hMq hk0 in
/-- On `[R, ∞)`, when `u′(R) + κ u(R) = 0`, the shooting solution is `u(R) e^{−κ(x − R)}`. -/
theorem simonU_right (hsupp : ∀ x, R ≤ |x| → q x = 0) (hR : 0 ≤ R) {κ : ℝ} (h0 : 0 ≤ κ)
    (h1 : κ ≤ k0) (hG : simonG q k0 R κ = 0) (x : ℝ) (hx : R ≤ x) :
    simonU q k0 R κ x = simonU q k0 R κ R * Real.exp (-(κ * (x - R))) := by
  have hc := simonClamp_of_mem h0 h1
  have hqx : ∀ y, R ≤ y → q y = 0 := fun y hy =>
    hsupp y (by rw [abs_of_nonneg (by linarith)]; linarith)
  set c := simonU q k0 R κ R
  have he : ∀ y, HasDerivAt (fun y => c * Real.exp (-(κ * (y - R))))
      (c * (-κ * Real.exp (-(κ * (y - R))))) y := fun y =>
    ((((hasDerivAt_id y).sub_const R).const_mul κ).neg.exp.const_mul c).congr_deriv
      (by simp only [id, mul_one, Pi.neg_apply]; ring)
  have := ode2_eq_zero_right (W := fun _ => κ ^ 2) (K := κ ^ 2) (x1 := R)
    (w := fun y => simonU q k0 R κ y - c * Real.exp (-(κ * (y - R))))
    (w' := fun y => simonUD q k0 R κ y - c * (-κ * Real.exp (-(κ * (y - R)))))
    (fun _ _ => by rw [abs_of_nonneg (sq_nonneg κ)])
    (fun y _ => (hasDerivAt_simonU hq hMq hk0 R κ y).sub (he y))
    (fun y hy => ((hasDerivAt_simonUD hq hMq hk0 R κ y).sub
      ((((((hasDerivAt_id y).sub_const R).const_mul κ).neg.exp.const_mul (-κ)).const_mul c)))
      |>.congr_deriv (by simp only [simonV, hqx y hy, hc, id, Pi.neg_apply]; ring))
    (by simp [c]) (by simp only [simonG] at hG; simp; linarith) x hx
  linarith

end Shooting

/-- **DLMF §1.18(viii), Example 1** (Simon's theorem, in one dimension): if `q` is continuous
and vanishes outside `[−R, R]`, `∫ q ≤ 0`, and `q < 0` somewhere, then `−d²/dx² + q` has a
negative eigenvalue `−κ²` with an `L²` eigenfunction. The eigenfunction is found by shooting
in `κ` from `e^{κ(x + R)}` on the left until it matches `e^{−κ x}` on the right. -/
theorem dlmf_1_18_viii_simon {q : ℝ → ℝ} (hq : Continuous q) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ x, R ≤ |x| → q x = 0) (hint : ∫ x, q x ≤ 0) (hneg : ∃ x, q x < 0) :
    ∃ κ > 0, ∃ ψ : ℝ → ℝ, ψ ≠ 0 ∧ MemLp ψ 2 volume ∧
      (∀ x, HasDerivAt ψ (deriv ψ x) x ∧ HasDerivAt (deriv ψ) (deriv (deriv ψ) x) x) ∧
      ∀ x, -deriv (deriv ψ) x + q x * ψ x = -κ ^ 2 * ψ x := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-R) R) hq.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by linarith, hR.le⟩)
  have hout : ∀ x, x ∉ Ioo (-R) R → R ≤ |x| := fun x hx => by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hMq : ∀ x, |q x| ≤ C := fun x => by
    by_cases hx : x ∈ Icc (-R) R
    · exact hC x hx
    · rw [hsupp x (hout x fun h => hx (Ioo_subset_Icc_self h)), abs_zero]
      exact hC0
  set k0 := Real.sqrt C + 1
  have hk0 : 0 ≤ k0 := by positivity
  have hk0M : C < k0 ^ 2 := by nlinarith [Real.sq_sqrt hC0, Real.sqrt_nonneg C]
  have hint' : ∫ x in -R..R, q x ≤ 0 := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        hsupp x (hout x fun h => hx (Ioo_subset_Ioc_self h))]
    exact hint
  obtain ⟨κ, hκ, hκk, hG⟩ := exists_simonG_eq_zero hq hMq hk0 R hR hk0M hsupp hint' hneg
  have hc := simonClamp_of_mem hκ.le hκk
  have hψ := hasDerivAt_simonU hq hMq hk0 R κ
  have hψ' := hasDerivAt_simonUD hq hMq hk0 R κ
  have hd : deriv (simonU q k0 R κ) = simonUD q k0 R κ := funext fun x => (hψ x).deriv
  have hdd : ∀ x, deriv (deriv (simonU q k0 R κ)) x =
      simonV q k0 κ x * (simonU q k0 R κ) x := fun x => by
    rw [hd]; exact (hψ' x).deriv
  have hcψ : Continuous (simonU q k0 R κ) := continuous_simonU_x hq hMq hk0 R κ
  refine ⟨κ, hκ, (simonU q k0 R κ), fun h => ?_, ?_, fun x => ⟨?_, ?_⟩, fun x => ?_⟩
  · have := congrFun h (-R)
    simp only [simonU_init hq hMq hk0, Pi.zero_apply] at this
    exact one_ne_zero this
  · obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-R) R)
      hcψ.continuousOn
    have h1 : 1 ≤ C1 := by
      have := hC1 (-R) ⟨le_rfl, by linarith⟩
      rwa [simonU_init hq hMq hk0, norm_one] at this
    set D := C1 * Real.exp (κ * R)
    have hbound : ∀ x, |(simonU q k0 R κ) x| ≤ D * Real.exp (-(κ * |x|)) := fun x => by
      rcases lt_or_ge x (-R) with hx | hx
      · rw [simonU_left hq hMq hk0 R hsupp hR.le hκ.le hκk x hx.le,
          abs_of_pos (Real.exp_pos _), abs_of_neg (by linarith),
          show κ * (x + R) = κ * R + -(κ * -x) by ring, Real.exp_add, mul_assoc]
        exact le_mul_of_one_le_left (by positivity) h1
      rcases le_or_gt x R with hx' | hx'
      · have hxR : |x| ≤ R := abs_le.mpr ⟨hx, hx'⟩
        have h2 : 1 ≤ Real.exp (κ * R) * Real.exp (-(κ * |x|)) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        have h3 : |(simonU q k0 R κ) x| ≤ C1 := by
          have := hC1 x ⟨hx, hx'⟩
          rwa [Real.norm_eq_abs] at this
        calc |(simonU q k0 R κ) x| ≤ C1 * 1 := by rw [mul_one]; exact h3
          _ ≤ C1 * (Real.exp (κ * R) * Real.exp (-(κ * |x|))) := by gcongr
          _ = D * Real.exp (-(κ * |x|)) := by ring
      · rw [simonU_right hq hMq hk0 R hsupp hR.le hκ.le hκk hG x hx'.le, abs_mul,
          abs_of_pos (Real.exp_pos _), abs_of_pos (show 0 < x by linarith),
          show -(κ * (x - R)) = κ * R + -(κ * x) by ring, Real.exp_add]
        have h3 : |(simonU q k0 R κ) R| ≤ C1 := by
          have := hC1 R ⟨by linarith, le_rfl⟩
          rwa [Real.norm_eq_abs] at this
        calc |simonU q k0 R κ R| * (Real.exp (κ * R) * Real.exp (-(κ * x)))
            ≤ C1 * (Real.exp (κ * R) * Real.exp (-(κ * x))) := by gcongr
          _ = D * Real.exp (-(κ * x)) := by ring
    refine (memLp_two_iff_integrable_sq_norm hcψ.aestronglyMeasurable).mpr ?_
    refine ((integrable_exp_neg_abs (b := 2 * κ) (by positivity)).const_mul (D ^ 2)).mono'
      (hcψ.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg _) (hbound x) 2
    rw [sq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  · rw [hd]; exact hψ x
  · rw [hd, (hψ' x).deriv]; exact hψ' x
  · rw [hdd]
    simp only [simonV, hc]
    ring

end Azurite.DLMF
