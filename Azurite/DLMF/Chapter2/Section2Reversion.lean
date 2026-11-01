/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section2
import Azurite.DLMF.Chapter2.Section2Lagrange

/-!
# DLMF §2.2: reversion of asymptotic expansions (2.2.7–2.2.8)

* `exists_reversion_series`: the formal `Ψ = 1/x` in powers of `w = 1/y`, via Mathlib's
  compositional inverse `substInvOfIsUnit`.
* `dlmf_2_2_8`: if `f(x) ∼ x + f₀ + f₁x⁻¹ + ⋯` (and `f` is as in 2.2.1), then
  `x(y) ∼ y − F₀ − F₁y⁻¹ − ⋯` with Lagrange's coefficients. The proof bootstraps `1/x(y) ∼ Ψ(1/y)`
  (`isBigO_eval_sub_eval`, `coeff_mul_subst_trunc`) and then uses `inv_subst_eq_lagrangeF`.
* `dlmf_2_2_8_coeff`: `sFₛ` is the coefficient of `x⁻¹` in the expansion of `f(x)ˢ`.
-/

open Set Filter Topology Asymptotics PowerSeries

namespace Azurite.DLMF

/-! ### Helpers -/

/-- `x → ∞` in `(c, ∞) ⊆ ℝ` is `x → +∞`. -/
theorem cobounded_inf_Ioi (c : ℝ) : Bornology.cobounded ℝ ⊓ 𝓟 (Ioi c) = atTop := by
  refine le_antisymm ?_ ?_
  · have h : Tendsto (fun x : ℝ => x) (Bornology.cobounded ℝ ⊓ 𝓟 (Ioi c)) atTop := by
      refine (tendsto_norm_cobounded_atTop.mono_left inf_le_left).congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self (Ioi c)),
        (tendsto_norm_cobounded_atTop.mono_left inf_le_left).eventually_gt_atTop |c|]
        with x hx hxc
      rw [Real.norm_eq_abs] at hxc ⊢
      exact abs_of_pos (by
        rcases le_or_gt 0 x with h | h
        · rcases h.lt_or_eq with h | h
          · exact h
          · rw [← h, abs_zero] at hxc; linarith [abs_nonneg c]
        · rw [abs_of_neg h] at hxc; linarith [neg_abs_le c, mem_Ioi.mp hx])
    exact h
  · refine le_inf (tendsto_norm_atTop_iff_cobounded.mp ?_) (le_principal_iff.mpr (Ioi_mem_atTop c))
    exact tendsto_abs_atTop_atTop

section General

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {y f : α → 𝕜}

/-- Dividing an expansion without constant term by `y` shifts the coefficients. -/
theorem HasPowExpansion.div_var {A : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A)
    (hA : constantCoeff A = 0) (hy0 : ∀ᶠ x in l, y x ≠ 0) :
    HasPowExpansion l y (fun x => f x / y x) (mk fun n => coeff (n + 1) A) := fun n => by
  have h := (hf (n + 1)).mul (isBigO_refl (fun x => (y x)⁻¹) l)
  refine h.congr' ?_ ?_
  · filter_upwards [hy0] with x hx
    rw [eval_trunc_eq_sum, eval_trunc_eq_sum, Finset.sum_range_succ',
      coeff_zero_eq_constantCoeff_apply, hA]
    simp only [coeff_mk, zero_mul, add_zero]
    field_simp
    rw [Finset.mul_sum]
    ring_nf
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · filter_upwards [hy0] with x hx
    field_simp
    ring

/-- A polynomial is Lipschitz on bounded sets: if `a, b = O(1)` and `a − b = O(ψ)`, then
`P(a) − P(b) = O(ψ)`. -/
theorem isBigO_eval_sub_eval {ψ : α → 𝕜} (P : Polynomial 𝕜) {a b : α → 𝕜}
    (ha : a =O[l] fun _ => (1 : 𝕜)) (hb : b =O[l] fun _ => (1 : 𝕜))
    (hab : (fun x => a x - b x) =O[l] ψ) :
    (fun x => P.eval (a x) - P.eval (b x)) =O[l] ψ := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    refine (hp.add hq).congr_left fun x => ?_
    simp only [Polynomial.eval_add]; ring
  | monomial k c =>
    have hg : (fun x => ∑ i ∈ Finset.range k, a x ^ i * b x ^ (k - 1 - i)) =O[l]
        fun _ => (1 : 𝕜) := by
      refine IsBigO.fun_sum fun i _ => ?_
      have := (ha.pow i).mul (hb.pow (k - 1 - i))
      simpa using this
    have := ((hg.mul hab).const_mul_left c).congr_right (fun x => one_mul (ψ x))
    refine this.congr_left fun x => ?_
    simp only [Polynomial.eval_monomial]
    rw [geom_sum₂_mul]; ring

end General

/-! ### A formal congruence -/

section Formal

variable {K : Type*} [Field K]

theorem coe_comp_eq_subst (p q : Polynomial K) (hq : HasSubst (q : K⟦X⟧)) :
    ((p.comp q : Polynomial K) : K⟦X⟧) = (p : K⟦X⟧).subst (q : K⟦X⟧) := by
  rw [subst_coe hq, Polynomial.comp_eq_aeval]
  have := Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom K) q p
  simpa [Polynomial.coeToPowerSeries.algHom_apply] using this.symm

theorem X_pow_dvd_sub_trunc (n : ℕ) (A : K⟦X⟧) : X ^ n ∣ A - (trunc n A : K⟦X⟧) := by
  rw [X_pow_dvd_iff]
  intro d hd
  rw [map_sub, Polynomial.coeff_coe, coeff_trunc, ite_eq_left_iff.mpr (fun h => absurd hd h),
    sub_self]

/-- `Ψ · G(Ψ) ≡ Q · Gₙ(Q) (mod Xⁿ)` for `Q = truncₙ Ψ`, `Gₙ = truncₙ G` (`Ψ(0) = 0`). -/
theorem coeff_mul_subst_trunc {G Ψ : K⟦X⟧} (hΨ0 : constantCoeff Ψ = 0) (n : ℕ) :
    ∀ d < n, coeff d (Ψ * G.subst Ψ) =
      Polynomial.coeff (trunc n Ψ * (trunc n G).comp (trunc n Ψ)) d := by
  have hs : HasSubst Ψ := HasSubst.of_constantCoeff_zero' hΨ0
  set Q := trunc n Ψ
  set T := trunc n G
  have hQ0 : constantCoeff (Q : K⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · rw [coeff_zero_eq_constantCoeff_apply, hΨ0]
    · rfl
  have hsQ : HasSubst (Q : K⟦X⟧) := HasSubst.of_constantCoeff_zero' hQ0
  have hdvd : X ^ n ∣ Ψ * G.subst Ψ - ((Q * T.comp Q : Polynomial K) : K⟦X⟧) := by
    rw [Polynomial.coe_mul, coe_comp_eq_subst T Q hsQ]
    have h1 : X ^ n ∣ Ψ - (Q : K⟦X⟧) := X_pow_dvd_sub_trunc n Ψ
    have h2 : X ^ n ∣ G.subst Ψ - (T : K⟦X⟧).subst Ψ := by
      rw [← subst_sub hs]
      obtain ⟨S, hS⟩ := X_pow_dvd_sub_trunc n G
      rw [hS, subst_mul hs, subst_pow hs, subst_X hs]
      exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hΨ0) n).mul_right _
    have h3 : X ^ n ∣ (T : K⟦X⟧).subst Ψ - (T : K⟦X⟧).subst (Q : K⟦X⟧) := by
      rw [subst_coe hs, subst_coe hsQ, Polynomial.aeval_def, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map]
      exact h1.trans (Polynomial.sub_dvd_eval_sub _ _ _)
    have e : Ψ * G.subst Ψ - (Q : K⟦X⟧) * (T : K⟦X⟧).subst (Q : K⟦X⟧) =
        (Ψ - Q) * G.subst Ψ + Q * (G.subst Ψ - (T : K⟦X⟧).subst Ψ) +
          Q * ((T : K⟦X⟧).subst Ψ - (T : K⟦X⟧).subst (Q : K⟦X⟧)) := by ring
    rw [e]
    exact dvd_add (dvd_add (h1.mul_right _) (h2.mul_left _)) (h3.mul_left _)
  intro d hd
  have := (X_pow_dvd_iff.mp hdvd) d hd
  rw [map_sub, sub_eq_zero, Polynomial.coeff_coe] at this
  exact this

end Formal

theorem HasPowExpansion.congr' {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {y f g : α → 𝕜}
    {A : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A) (hfg : f =ᶠ[l] g) : HasPowExpansion l y g A :=
  fun n => (hf n).congr' (hfg.mono fun x hx => by simp only [hx]) EventuallyEq.rfl

/-! ### The reversion theorem -/

/-- The formal solution `Ψ = 1/x` (in powers of `w = 1/y`) of `y = x + G(1/x)`: the compositional
inverse of `v/(1 + vG(v))`, which satisfies `Ψ = w (1 + Ψ G(Ψ))`. -/
theorem exists_reversion_series {K : Type*} [Field K] (G : K⟦X⟧) :
    ∃ Ψ : K⟦X⟧, constantCoeff Ψ = 0 ∧ Ψ = X * (1 + X * G).subst Ψ := by
  set φ := 1 + X * G
  have hφ0 : constantCoeff φ ≠ 0 := by rw [constantCoeff_one_add_X_mul]; exact one_ne_zero
  set Φ := X * φ⁻¹
  have hΦ0 : constantCoeff Φ = 0 := by simp [Φ]
  have hΦ1 : IsUnit (coeff 1 Φ) := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv]
    exact (inv_ne_zero hφ0).isUnit
  set Ψ := Φ.substInvOfIsUnit hΦ1
  have hΨ0 : constantCoeff Ψ = 0 := constantCoeff_substInvOfIsUnit Φ hΦ1
  have hs : HasSubst Ψ := HasSubst.substInvOfIsUnit Φ hΦ1
  have hΦΨ : Φ.subst Ψ = X := subst_substInvOfIsUnit_right Φ hΦ0 hΦ1
  have hone : (φ⁻¹).subst Ψ * φ.subst Ψ = 1 := by
    rw [← subst_mul hs, PowerSeries.inv_mul_cancel φ hφ0]
    have := subst_C (S := K) (a := Ψ) (1 : K)
    simpa using this
  refine ⟨Ψ, hΨ0, ?_⟩
  have h : Ψ * (φ⁻¹).subst Ψ = X := by
    rw [← hΦΨ, subst_mul hs, subst_X hs]
  calc Ψ = Ψ * ((φ⁻¹).subst Ψ * φ.subst Ψ) := by rw [hone, mul_one]
    _ = X * φ.subst Ψ := by rw [← mul_assoc, h]

/-- **DLMF 2.2.7–2.2.8** (reversion, Lagrange's formula): let `f` be continuous and strictly
increasing on `(a, ∞)` (continuous at `a`), with `f(x) ∼ x + f₀ + f₁x⁻¹ + f₂x⁻² + ⋯` as
`x → ∞`. Then the root `x(y)` of `f(x) = y` satisfies `x ∼ y − F₀ − F₁y⁻¹ − F₂y⁻² − ⋯` as
`y → ∞`, where `F₀ = f₀` and `sFₛ` is the coefficient of `x⁻¹` in the expansion of `f(x)ˢ`
(`lagrangeF`, see `dlmf_2_2_8_coeff`). -/
theorem dlmf_2_2_8 {f : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a))
    (hm : StrictMonoOn f (Ioi a)) {fc : ℕ → ℝ}
    (hexp : IsAsympExpansionDLMF (Ioi a) (fun x => f x - x) fc) :
    IsAsympExpansionDLMF (Ioi (f a)) (fun y => rootDLMF f a y - y) fun s => -lagrangeF fc s := by
  set G := mk fc
  have hG : HasPowExpansion atTop (fun x => x⁻¹) (fun x => f x - x) G := by
    have := isAsympExpansionDLMF_iff.mp hexp
    rwa [cobounded_inf_Ioi] at this
  have hinvT : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  -- `f(x) ∼ x`
  have hfx : AsympEqDLMF atTop f id := by
    have h1 := (hG.isBigO_one hinvT).mul (isBigO_refl (fun x : ℝ => x⁻¹) atTop)
    have h2 := (h1.trans_tendsto (by simpa using hinvT)).const_add 1
    rw [add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [id]; field_simp; ring
  set xr := rootDLMF f a
  have hxr : Tendsto xr atTop atTop := tendsto_rootDLMF hf hm hfx
  have hspec : ∀ᶠ y in atTop, a < xr y ∧ f (xr y) = y :=
    (eventually_gt_atTop (f a)).mono fun y hy =>
      ⟨(rootDLMF_spec hf hm hfx hy).1, (rootDLMF_spec hf hm hfx hy).2.1⟩
  set v : ℝ → ℝ := fun y => (xr y)⁻¹
  set w : ℝ → ℝ := fun y => y⁻¹
  have hw : Tendsto w atTop (𝓝 0) := hinvT
  have hw0 : ∀ᶠ y in atTop, w y ≠ 0 :=
    (eventually_gt_atTop 0).mono fun y hy => inv_ne_zero hy.ne'
  have hxr0 : ∀ᶠ y in atTop, 0 < xr y := hxr.eventually_gt_atTop 0
  have hv : Tendsto v atTop (𝓝 0) := hinvT.comp hxr
  have hvw : v =O[atTop] w := by
    have h := ((dlmf_2_2_2 hf hm hfx).inv₀ one_ne_zero)
    rw [inv_one] at h
    refine ((h.isBigO_one ℝ).mul (isBigO_refl w atTop)).congr' ?_ ?_
    · filter_upwards [hxr0, eventually_gt_atTop 0] with y h1 h2
      simp only [v, w, id]
      rw [show rootDLMF f a y = xr y from rfl]
      field_simp
    · exact Eventually.of_forall fun y => one_mul _
  have hgx : HasPowExpansion atTop v (fun y => f (xr y) - xr y) G :=
    hG.comp_tendsto hxr
  -- the formal series `Ψ`
  obtain ⟨Ψ, hΨ0, hΨ⟩ := exists_reversion_series G
  have hs : HasSubst Ψ := HasSubst.of_constantCoeff_zero' hΨ0
  have hΨ' : Ψ = X + X * (Ψ * G.subst Ψ) := by
    conv_lhs => rw [hΨ]
    rw [subst_add hs, subst_mul hs, subst_X hs]
    have := subst_C (S := ℝ) (a := Ψ) (1 : ℝ)
    simp only [map_one] at this
    rw [this]; ring
  -- the bootstrap: `v ∼ Ψ(w)`
  have hV : HasPowExpansion atTop w v Ψ := by
    intro n
    induction n with
    | zero =>
      simpa [trunc_zero'] using hv.isBigO_one ℝ
    | succ n ih =>
      set Q := trunc n Ψ
      set T := trunc n G
      set P : Polynomial ℝ := Polynomial.X * T
      set R : Polynomial ℝ := Polynomial.X + Polynomial.X * P.comp Q
      have hid : ∀ᶠ y in atTop, v y = w y + w y * (v y * (f (xr y) - xr y)) := by
        filter_upwards [hspec, hxr0, eventually_gt_atTop 0] with y h h0 hy0
        rw [h.2]; simp only [v, w]; field_simp; ring
      have e1 : (fun y => (f (xr y) - xr y) - T.eval (v y)) =O[atTop] fun y => w y ^ n :=
        (hgx n).trans (hvw.pow n)
      have e2 : (fun y => w y * (v y * (f (xr y) - xr y) - P.eval (v y))) =O[atTop]
          fun y => w y ^ (n + 1) := by
        have := (hw.isBigO_one ℝ).mul (hvw.mul e1)
        refine this.congr (fun y => ?_) (fun y => ?_)
        · simp only [P, Polynomial.eval_mul, Polynomial.eval_X]; ring
        · ring
      have hQb : (fun y => Q.eval (w y)) =O[atTop] fun _ => (1 : ℝ) :=
        ((Q.continuous.tendsto 0).comp hw).isBigO_one ℝ
      have e3 : (fun y => w y * (P.eval (v y) - P.eval (Q.eval (w y)))) =O[atTop]
          fun y => w y ^ (n + 1) := by
        have := (isBigO_refl w atTop).mul (isBigO_eval_sub_eval P (hv.isBigO_one ℝ) hQb ih)
        exact this.congr_right fun y => by ring
      have e4 : (fun y => R.eval (w y) - (trunc (n + 1) Ψ).eval (w y)) =O[atTop]
          fun y => w y ^ (n + 1) := by
        have := isBigO_eval_of_coeff_eq_zero hw (p := R - trunc (n + 1) Ψ) (n := n + 1)
          fun d hd => by
            rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left_iff.mpr (fun h => absurd hd h),
              sub_eq_zero]
            have hc := congrArg (coeff d) hΨ'
            rcases d with _ | d
            · simp [R, hΨ0]
            · have hd' : d < n := by omega
              have key := coeff_mul_subst_trunc (G := G) hΨ0 n d hd'
              rw [hc]
              have eR : R.coeff (d + 1) = Polynomial.X.coeff (d + 1) +
                  (Q * T.comp Q).coeff d := by
                simp only [R, P, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.mul_comp,
                  Polynomial.X_comp]
              have eS : coeff (d + 1) (X + X * (Ψ * G.subst Ψ)) =
                  coeff (d + 1) (X : ℝ⟦X⟧) + coeff d (Ψ * G.subst Ψ) := by
                rw [map_add, coeff_succ_X_mul]
              rw [eR, eS, key]
              congr 1
              rw [Polynomial.coeff_X, PowerSeries.coeff_X]
              by_cases h : d + 1 = 1
              · simp [h]
              · simp
        simpa only [Polynomial.eval_sub] using this
      refine ((e2.add e3).add e4).congr' ?_ EventuallyEq.rfl
      filter_upwards [hid] with y hy
      simp only [R, P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_comp]
      conv_rhs => rw [hy]
      ring
  -- read off `x(y) − y`
  set U := (1 + X * G).subst Ψ
  have hU : HasPowExpansion atTop w (fun y => v y / w y) U := by
    have h := hV.div_var hΨ0 hw0
    have e : (mk fun n => coeff (n + 1) Ψ) = U := by
      ext n; rw [coeff_mk]; conv_lhs => rw [hΨ]
      rw [coeff_succ_X_mul]
    rwa [e] at h
  have hU0 : constantCoeff U ≠ 0 := by
    have := constantCoeff_subst_of_constantCoeff_zero (a := Ψ) hΨ0 (1 + X * G)
    have e : constantCoeff U = constantCoeff (1 + X * G) := this
    rw [e, constantCoeff_one_add_X_mul]; exact one_ne_zero
  have hUinv := hU.inv hw hU0
  have hUeq : U⁻¹ = (1 + X * G)⁻¹.subst Ψ := by
    have hone : ((1 + X * G)⁻¹.subst Ψ : ℝ⟦X⟧) * U = 1 := by
      rw [← subst_mul hs, PowerSeries.inv_mul_cancel _ (by
        rw [constantCoeff_one_add_X_mul]; exact one_ne_zero)]
      have := subst_C (S := ℝ) (a := Ψ) (1 : ℝ)
      simpa using this
    exact ((PowerSeries.eq_inv_iff_mul_eq_one hU0).mpr hone).symm
  rw [hUeq, inv_subst_eq_lagrangeF hΨ0 hΨ] at hUinv
  have h1 := hUinv.sub (hasPowExpansion_polynomial hw 1)
  simp only [Polynomial.eval_one, Polynomial.coe_one, sub_sub_cancel_left] at h1
  have h2 := h1.div_var (by simp) hw0
  rw [isAsympExpansionDLMF_iff, cobounded_inf_Ioi]
  have e : (mk fun n => coeff (n + 1) (-(X * mk (lagrangeF fc)))) =
      mk fun s => -lagrangeF fc s := by
    ext n; simp [coeff_succ_X_mul]
  rw [e] at h2
  refine h2.congr' ?_
  filter_upwards [hxr0, eventually_gt_atTop 0] with y h0 hy0
  simp only [v, w, Pi.sub_apply]
  field_simp

theorem HasPowExpansion.pow {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {y f : α → 𝕜}
    (hy : Tendsto y l (𝓝 0)) {A : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A) (s : ℕ) :
    HasPowExpansion l y (fun x => f x ^ s) (A ^ s) := by
  induction s with
  | zero => simpa using hasPowExpansion_polynomial hy 1
  | succ s ih =>
    have := ih.mul hy hf
    rw [pow_succ]
    convert this using 1
    funext x; simp [pow_succ]

/-- **DLMF §2.2**: the meaning of `lagrangeF`: `f(x)ˢ x^{−s} ∼ ∑ₖ eₖx^{−k}` with
`eₖ = [vᵏ](1 + f₀v + f₁v² + ⋯)ˢ`, i.e. `f(x)ˢ ∼ ∑ₖ eₖ x^{s−k}`; the coefficient of `x⁻¹` is
`e_{s+1} = s Fₛ` (`s ≥ 1`). -/
theorem dlmf_2_2_8_coeff {f : ℝ → ℝ} {a : ℝ} {fc : ℕ → ℝ}
    (hexp : IsAsympExpansionDLMF (Ioi a) (fun x => f x - x) fc) (s : ℕ) :
    IsAsympExpansionDLMF (Ioi a) (fun x => f x ^ s * x ^ (-(s : ℤ)))
        (fun k => coeff k ((1 + X * mk fc) ^ s)) ∧
      (1 ≤ s → (s : ℝ) * lagrangeF fc s = coeff (s + 1) ((1 + X * mk fc) ^ s)) := by
  refine ⟨?_, fun hs => ?_⟩
  · have hG : HasPowExpansion atTop (fun x => x⁻¹) (fun x => f x - x) (mk fc) := by
      have := isAsympExpansionDLMF_iff.mp hexp
      rwa [cobounded_inf_Ioi] at this
    have hinvT : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have h1 := (hasPowExpansion_polynomial hinvT 1).add
      ((hasPowExpansion_polynomial hinvT Polynomial.X).mul hinvT hG)
    simp only [Polynomial.eval_one, Polynomial.eval_X, Polynomial.coe_one,
      Polynomial.coe_X] at h1
    have h2 := h1.pow hinvT s
    rw [isAsympExpansionDLMF_iff, cobounded_inf_Ioi]
    have e : (mk fun k => coeff k ((1 + X * mk fc) ^ s)) = (1 + X * mk fc) ^ s := by
      ext; simp
    rw [e]
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Pi.add_apply, Pi.mul_apply, zpow_neg, zpow_natCast]
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    ring
  · simp only [lagrangeF, show s ≠ 0 by omega, ↓reduceIte]
    have : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    field_simp

end Azurite.DLMF
