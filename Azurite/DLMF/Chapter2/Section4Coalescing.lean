/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4Saddle

/-!
# DLMF §2.4(v): Coalescing saddle points, Chester–Friedman–Ursell (2.4.17–2.4.21)

`I(α, z) = ∫_𝒫 e^{−zp(α,t)} q(α,t) dt` (2.4.17, `cfuIntegral`), where two simple zeros of
`∂p(α,t)/∂t` on the path coalesce for `α = α̂`. DLMF prescribes the cubic change of variable
2.4.18, `p(α,t) = ⅓w³ + aw² + bw + c`, with `a`, `b` "chosen so that the zeros of `∂p/∂t`
correspond to the zeros `w₁(α)`, `w₂(α)` of `w² + 2aw + b`". The transformation is taken as data:
`CFUTransform p U w a b c` says that `w` is analytic and injective on the open set `U ⊇ 𝒫` with
`w′ ≠ 0`, and `p = ⅓w³ + aw² + bw + c` there (for one value of `α`). Its existence and analytic
dependence on `α` through the confluence is the theorem of Chester, Friedman and Ursell (1957),
which DLMF does not state and which is not proved here.

What DLMF asserts is then proved:

* 2.4.18: `∂p/∂t = (w² + 2aw + b) w′`, so the saddle points are the points with `w = w₁, w₂`
  (`dlmf_2_4_18`); two distinct saddle points give `w₁ + w₂ = −2a`, `w₁w₂ = b`
  (`dlmf_2_4_18_vieta`); the two zeros coalesce (a double zero of `∂p/∂t`) exactly when
  `b = a²`, at `w = −a` (`dlmf_2_4_18_coalesce`).
* 2.4.20: `f(α,w) = q dt/dw = q (w² + 2aw + b)/(∂p/∂t)` (`dlmf_2_4_20`), and `f` is analytic at
  `w₁`, `w₂` and at their confluence (`dlmf_2_4_20_analytic`): the inverse `t = t(w)` is analytic
  on the image of `U` (inverse function theorem).
* 2.4.19: `I(α,z) = e^{−cz} ∫_𝒬 exp(−z(⅓w³ + aw² + bw)) f(α,w) dw` along the `w`-image of the
  path (`dlmf_2_4_19`).
* 2.4.21: with `w = z^{−1/3}v − a` (`z = ζ³`), `z(⅓w³ + aw² + bw) = ⅓v³ + (b − a²)ζ²v +
  ζ³(⅔a³ − ab)` (`dlmf_2_4_21_cubic`), and
  `I(α,z) = e^{−z(c + ⅔a³ − ab)} z^{−1/3} ∫ exp(−(⅓v³ + (b − a²)z^{2/3}v)) f(α, z^{−1/3}v − a) dv`
  (`dlmf_2_4_21`), the integral "reducible to an Airy function or a Scorer function" (DLMF gives
  no formula; the identification with `Ai`, `Hi`, `Gi` is §9.5 and is not formalized here).
-/

open Set Filter Topology Complex
open scoped Interval

namespace Azurite.DLMF

/-- **DLMF 2.4.17**: `I(α, z) = ∫_𝒫 e^{−zp(α,t)} q(α,t) dt` along `t = γ(α, u)`, `u₀ ≤ u ≤ u₁`. -/
noncomputable def cfuIntegral {ι : Type*} (p q : ι → ℂ → ℂ) (γ γ' : ι → ℝ → ℂ) (u₀ u₁ : ℝ)
    (α : ι) (z : ℂ) : ℂ :=
  ∫ u in u₀..u₁, cexp (-(z * p α (γ α u))) * q α (γ α u) * γ' α u

/-- The cubic `⅓w³ + aw² + bw + c` of 2.4.18. -/
noncomputable def cfuCubic (a b c w : ℂ) : ℂ := w ^ 3 / 3 + a * w ^ 2 + b * w + c

/-- Its derivative, the quadratic `w² + 2aw + b`. -/
def cfuQuad (a b w : ℂ) : ℂ := w ^ 2 + 2 * a * w + b

theorem hasDerivAt_cfuCubic (a b c w : ℂ) : HasDerivAt (cfuCubic a b c) (cfuQuad a b w) w := by
  have := (((((hasDerivAt_id' w).pow 3).div_const 3).add
    (((hasDerivAt_id' w).pow 2).const_mul a)).add ((hasDerivAt_id' w).const_mul b)).add_const c
  refine this.congr_deriv ?_
  simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one, cfuQuad]
  ring

theorem hasDerivAt_cfuQuad (a b w : ℂ) : HasDerivAt (cfuQuad a b) (2 * w + 2 * a) w := by
  have := ((((hasDerivAt_id' w).pow 2).add ((hasDerivAt_id' w).const_mul (2 * a))).add_const b)
  refine this.congr_deriv ?_
  simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one]

theorem differentiable_cfuCubic (a b c : ℂ) : Differentiable ℂ (cfuCubic a b c) := fun w =>
  (hasDerivAt_cfuCubic a b c w).differentiableAt

theorem cfuCubic_eq (a b c w : ℂ) : cfuCubic a b c w = cfuCubic a b 0 w + c := by
  unfold cfuCubic
  ring

/-- `w² + 2aw + b = 0 ↔ (w + a)² = a² − b`: the roots are `w₁, w₂ = −a ± (a² − b)^{1/2}`. -/
theorem cfuQuad_eq_zero_iff (a b x : ℂ) : cfuQuad a b x = 0 ↔ (x + a) ^ 2 = a ^ 2 - b := by
  unfold cfuQuad
  constructor <;> intro h <;> linear_combination h

/-- **DLMF 2.4.18**: the change of variable `p(t) = ⅓w³ + aw² + bw + c` on an open set `U`
containing the path, `w` analytic, one-to-one, with `w′ ≠ 0`. -/
structure CFUTransform (p : ℂ → ℂ) (U : Set ℂ) (w : ℂ → ℂ) (a b c : ℂ) : Prop where
  U_open : IsOpen U
  w_diff : DifferentiableOn ℂ w U
  w_inj : InjOn w U
  deriv_ne : ∀ t ∈ U, deriv w t ≠ 0
  p_eq : ∀ t ∈ U, p t = cfuCubic a b c (w t)

namespace CFUTransform

variable {p : ℂ → ℂ} {U : Set ℂ} {w : ℂ → ℂ} {a b c : ℂ}

theorem analyticAt_w (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) : AnalyticAt ℂ w t :=
  h.w_diff.analyticAt (h.U_open.mem_nhds ht)

/-- `∂p/∂t = (w² + 2aw + b) w′`. -/
theorem hasDerivAt_p (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    HasDerivAt p (cfuQuad a b (w t) * deriv w t) t := by
  have h1 := (hasDerivAt_cfuCubic a b c (w t)).comp t
    (h.analyticAt_w ht).differentiableAt.hasDerivAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [h.U_open.mem_nhds ht] with s hs
  exact h.p_eq s hs

theorem deriv_p (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    deriv p t = cfuQuad a b (w t) * deriv w t :=
  (h.hasDerivAt_p ht).deriv

theorem analyticAt_p (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) : AnalyticAt ℂ p t := by
  have : AnalyticAt ℂ (cfuCubic a b c ∘ w) t :=
    ((differentiable_cfuCubic a b c).analyticAt _).comp (h.analyticAt_w ht)
  refine this.congr ?_
  filter_upwards [h.U_open.mem_nhds ht] with s hs
  exact (h.p_eq s hs).symm

/-- **DLMF 2.4.18**: the saddle points are the points where `w² + 2aw + b = 0`. -/
theorem dlmf_2_4_18 (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    deriv p t = 0 ↔ cfuQuad a b (w t) = 0 := by
  rw [h.deriv_p ht, mul_eq_zero, or_iff_left (h.deriv_ne t ht)]

/-- Two distinct saddle points `t₁ ≠ t₂`: `w₁ + w₂ = −2a` and `w₁w₂ = b`. -/
theorem dlmf_2_4_18_vieta (h : CFUTransform p U w a b c) {t₁ t₂ : ℂ} (ht₁ : t₁ ∈ U)
    (ht₂ : t₂ ∈ U) (hne : t₁ ≠ t₂) (h₁ : deriv p t₁ = 0) (h₂ : deriv p t₂ = 0) :
    w t₁ + w t₂ = -(2 * a) ∧ w t₁ * w t₂ = b := by
  have e₁ := (h.dlmf_2_4_18 ht₁).mp h₁
  have e₂ := (h.dlmf_2_4_18 ht₂).mp h₂
  have hw : w t₁ ≠ w t₂ := fun e => hne (h.w_inj ht₁ ht₂ e)
  unfold cfuQuad at e₁ e₂
  have hs : w t₁ + w t₂ = -(2 * a) := by
    have : (w t₁ - w t₂) * (w t₁ + w t₂ + 2 * a) = 0 := by linear_combination e₁ - e₂
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hw
    · linear_combination h0
  exact ⟨hs, by linear_combination w t₁ * hs - e₁⟩

/-- The two saddle points coalesce (a double zero of `∂p/∂t`) exactly when `b = a²`, at `w = −a`:
the quadratic is then `(w + a)²`. -/
theorem dlmf_2_4_18_coalesce (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    (deriv p t = 0 ∧ deriv (deriv p) t = 0) ↔ (w t = -a ∧ b = a ^ 2) := by
  have hev : deriv p =ᶠ[𝓝 t] fun s => cfuQuad a b (w s) * deriv w s := by
    filter_upwards [h.U_open.mem_nhds ht] with s hs
    exact h.deriv_p hs
  have hw := h.analyticAt_w ht
  have hQ : HasDerivAt (fun s => cfuQuad a b (w s)) ((2 * w t + 2 * a) * deriv w t) t :=
    (hasDerivAt_cfuQuad a b (w t)).comp t hw.differentiableAt.hasDerivAt
  have h2 : deriv (deriv p) t =
      (2 * w t + 2 * a) * deriv w t ^ 2 + cfuQuad a b (w t) * deriv (deriv w) t := by
    have hprod : HasDerivAt (fun s => cfuQuad a b (w s) * deriv w s)
        ((2 * w t + 2 * a) * deriv w t * deriv w t + cfuQuad a b (w t) * deriv (deriv w) t) t :=
      hQ.mul hw.deriv.differentiableAt.hasDerivAt
    rw [Filter.EventuallyEq.deriv_eq hev, hprod.deriv]
    ring
  rw [h.dlmf_2_4_18 ht, h2]
  constructor
  · rintro ⟨hQ0, hd⟩
    rw [hQ0, zero_mul, add_zero] at hd
    have h0 : 2 * w t + 2 * a = 0 := by
      rcases mul_eq_zero.mp hd with h0 | h0
      · exact h0
      · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h0) (h.deriv_ne t ht)
    have hw' : w t = -a := by linear_combination h0 / 2
    refine ⟨hw', ?_⟩
    rw [hw'] at hQ0
    unfold cfuQuad at hQ0
    linear_combination hQ0
  · rintro ⟨hw', hb⟩
    have hQ0 : cfuQuad a b (w t) = 0 := by
      rw [hw', hb]
      unfold cfuQuad
      ring
    refine ⟨hQ0, ?_⟩
    rw [hQ0, hw']
    ring

/-! ### The inverse `t = t(w)` and `f(α, w)` -/

/-- The inverse `t = t(w)` of `w = w(t)` on `U`. -/
noncomputable def inv (_h : CFUTransform p U w a b c) : ℂ → ℂ := Function.invFunOn w U

theorem inv_w (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) : h.inv (w t) = t :=
  h.w_inj.leftInvOn_invFunOn ht

theorem eventuallyEq_localInverse (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    h.inv =ᶠ[𝓝 (w t)]
      (h.analyticAt_w ht).hasStrictDerivAt.localInverse w (deriv w t) t (h.deriv_ne t ht) := by
  have hsd := (h.analyticAt_w ht).hasStrictDerivAt
  set g := hsd.localInverse w (deriv w t) t (h.deriv_ne t ht) with hg
  have hga : g (w t) = t := (hsd.eventually_left_inverse (h.deriv_ne t ht)).self_of_nhds
  have hcont : ContinuousAt g (w t) :=
    (hsd.to_localInverse (h.deriv_ne t ht)).hasDerivAt.continuousAt
  have hU : ∀ᶠ s in 𝓝 (g (w t)), s ∈ U := by
    rw [hga]
    exact h.U_open.mem_nhds ht
  filter_upwards [hcont.eventually hU, hsd.eventually_right_inverse (h.deriv_ne t ht)] with y hy
    hwy
  calc h.inv y = h.inv (w (g y)) := by rw [hwy]
    _ = g y := h.inv_w hy

theorem analyticAt_inv (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    AnalyticAt ℂ h.inv (w t) :=
  ((h.analyticAt_w ht).analyticAt_localInverse (h.deriv_ne t ht)).congr
    (h.eventuallyEq_localInverse ht).symm

theorem hasDerivAt_inv (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    HasDerivAt h.inv (deriv w t)⁻¹ (w t) :=
  ((h.analyticAt_w ht).hasStrictDerivAt.to_localInverse (h.deriv_ne t ht)).hasDerivAt
    |>.congr_of_eventuallyEq (h.eventuallyEq_localInverse ht)

theorem deriv_inv (h : CFUTransform p U w a b c) {t : ℂ} (ht : t ∈ U) :
    deriv h.inv (w t) = (deriv w t)⁻¹ :=
  (h.hasDerivAt_inv ht).deriv

/-- **DLMF 2.4.20**: `f(α, w) = q(α, t) dt/dw`. -/
noncomputable def amp (h : CFUTransform p U w a b c) (q : ℂ → ℂ) (v : ℂ) : ℂ :=
  q (h.inv v) * deriv h.inv v

theorem amp_w (h : CFUTransform p U w a b c) (q : ℂ → ℂ) {t : ℂ} (ht : t ∈ U) :
    h.amp q (w t) = q t / deriv w t := by
  rw [amp, h.inv_w ht, h.deriv_inv ht, div_eq_mul_inv]

/-- **DLMF 2.4.20**: `f(α, w) = q(α,t) (w² + 2aw + b)/(∂p(α,t)/∂t)` away from the saddle points. -/
theorem dlmf_2_4_20 (h : CFUTransform p U w a b c) (q : ℂ → ℂ) {t : ℂ} (ht : t ∈ U)
    (hp : deriv p t ≠ 0) : h.amp q (w t) = q t * cfuQuad a b (w t) / deriv p t := by
  have hne := h.deriv_ne t ht
  have hQ : cfuQuad a b (w t) ≠ 0 := by
    intro e
    rw [h.deriv_p ht, e, zero_mul] at hp
    exact hp rfl
  rw [h.amp_w q ht, h.deriv_p ht]
  field_simp

/-- **DLMF 2.4.20**: `f(α, w)` is analytic at `w = w₁(α)`, `w₂(α)`, and at their confluence (at
every `w(t)`, `t ∈ U`). -/
theorem dlmf_2_4_20_analytic (h : CFUTransform p U w a b c) {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q U) {t : ℂ} (ht : t ∈ U) : AnalyticAt ℂ (h.amp q) (w t) := by
  have hinv := h.analyticAt_inv ht
  have hq' : AnalyticAt ℂ q (h.inv (w t)) := by
    rw [h.inv_w ht]
    exact hq.analyticAt (h.U_open.mem_nhds ht)
  exact (hq'.comp hinv).mul hinv.deriv

/-! ### 2.4.19 and 2.4.21 -/

/-- **DLMF 2.4.19**: `I(α,z) = e^{−cz} ∫_𝒬 exp(−z(⅓w³ + aw² + bw)) f(α,w) dw`, `𝒬 = w(𝒫)`. -/
theorem dlmf_2_4_19 {ι : Type*} {p q : ι → ℂ → ℂ} {γ γ' : ι → ℝ → ℂ} {u₀ u₁ : ℝ} (α : ι)
    (h : CFUTransform (p α) U w a b c) (hγ : ∀ u ∈ [[u₀, u₁]], γ α u ∈ U)
    (hγd : ∀ u ∈ [[u₀, u₁]], HasDerivAt (γ α) (γ' α u) u) (z : ℂ) :
    cfuIntegral p q γ γ' u₀ u₁ α z = cexp (-(c * z)) *
      ∫ u in u₀..u₁, cexp (-(z * cfuCubic a b 0 (w (γ α u)))) * h.amp (q α) (w (γ α u)) *
        deriv (fun u => w (γ α u)) u := by
  rw [cfuIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  have ht := hγ u hu
  have hne := h.deriv_ne (γ α u) ht
  have hd : deriv (fun u => w (γ α u)) u = deriv w (γ α u) * γ' α u :=
    ((h.analyticAt_w ht).differentiableAt.hasDerivAt.comp u (hγd u hu)).deriv
  rw [hd, h.amp_w (q α) ht, h.p_eq (γ α u) ht, cfuCubic_eq, mul_add, neg_add, Complex.exp_add]
  field_simp

/-- **DLMF 2.4.21**: with `w = z^{−1/3} v − a`, `z = ζ³`,
`z(⅓w³ + aw² + bw) = ⅓v³ + (b − a²) ζ² v + ζ³(⅔a³ − ab)`. -/
theorem dlmf_2_4_21_cubic (a b : ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) (v : ℂ) :
    ζ ^ 3 * cfuCubic a b 0 (v / ζ - a) =
      v ^ 3 / 3 + (b - a ^ 2) * ζ ^ 2 * v + ζ ^ 3 * (2 * a ^ 3 / 3 - a * b) := by
  unfold cfuCubic
  field_simp
  ring

/-- **DLMF 2.4.21**: `I(α,z) = e^{−z(c + ⅔a³ − ab)} z^{−1/3} ∫ exp(−(⅓v³ + (b − a²) z^{2/3} v))
f(α, z^{−1/3}v − a) dv` along `v = z^{1/3}(w + a)`, with `z = ζ³`: the integral of Airy type. -/
theorem dlmf_2_4_21 {ι : Type*} {p q : ι → ℂ → ℂ} {γ γ' : ι → ℝ → ℂ} {u₀ u₁ : ℝ} (α : ι)
    (h : CFUTransform (p α) U w a b c) (hγ : ∀ u ∈ [[u₀, u₁]], γ α u ∈ U)
    (hγd : ∀ u ∈ [[u₀, u₁]], HasDerivAt (γ α) (γ' α u) u) {ζ : ℂ} (hζ : ζ ≠ 0) :
    cfuIntegral p q γ γ' u₀ u₁ α (ζ ^ 3) =
      cexp (-(ζ ^ 3 * (c + (2 * a ^ 3 / 3 - a * b)))) * ζ⁻¹ *
        ∫ u in u₀..u₁, cexp (-((ζ * (w (γ α u) + a)) ^ 3 / 3 +
            (b - a ^ 2) * ζ ^ 2 * (ζ * (w (γ α u) + a)))) *
          h.amp (q α) (ζ * (w (γ α u) + a) / ζ - a) * deriv (fun u => ζ * (w (γ α u) + a)) u := by
  rw [cfuIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  have ht := hγ u hu
  have hne := h.deriv_ne (γ α u) ht
  have hd : deriv (fun u => ζ * (w (γ α u) + a)) u = ζ * (deriv w (γ α u) * γ' α u) :=
    ((((h.analyticAt_w ht).differentiableAt.hasDerivAt.comp u (hγd u hu)).add_const a).const_mul
      ζ).deriv
  have hv : ζ * (w (γ α u) + a) / ζ - a = w (γ α u) := by
    rw [mul_div_cancel_left₀ _ hζ, add_sub_cancel_right]
  have e2 := dlmf_2_4_21_cubic a b hζ (ζ * (w (γ α u) + a))
  rw [hv] at e2
  have e3 : (ζ * (w (γ α u) + a)) ^ 3 / 3 + (b - a ^ 2) * ζ ^ 2 * (ζ * (w (γ α u) + a)) =
      ζ ^ 3 * cfuCubic a b 0 (w (γ α u)) - ζ ^ 3 * (2 * a ^ 3 / 3 - a * b) := by
    linear_combination -e2
  rw [hd, hv, h.amp_w (q α) ht, h.p_eq (γ α u) ht, e3, cfuCubic_eq]
  have : cexp (-(ζ ^ 3 * (cfuCubic a b 0 (w (γ α u)) + c))) =
      cexp (-(ζ ^ 3 * (c + (2 * a ^ 3 / 3 - a * b)))) *
        cexp (-(ζ ^ 3 * cfuCubic a b 0 (w (γ α u)) - ζ ^ 3 * (2 * a ^ 3 / 3 - a * b))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [this]
  field_simp

end CFUTransform

end Azurite.DLMF
