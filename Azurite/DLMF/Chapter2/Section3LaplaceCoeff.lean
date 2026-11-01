/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3LaplaceSeries

/-!
# DLMF §2.3(iii): the coefficients of Laplace's method (2.3.15–2.3.18)

With `p(t) − p(a) = (t − a)^μ P(t − a)` and `q(t) = (t − a)^{λ−1} Q(t − a)` (2.3.14, as
asymptotic series):

* `laplaceMethodCoeff`: `bₛ = (1/μ)[tˢ] Q P^{−(λ+s)/μ}` (2.3.18).
* `laplaceMethod_formal`: `Q (μP + XP′)⁻¹ P^{(μ−λ)/μ} = B(X P^{1/μ})` with `B = ∑ bₛ wˢ`, by
  Lagrange inversion (second form).
* `dlmf_2_3_16`: `q(t)/p′(t) ∼ ∑ bₛ v^{(s+λ−μ)/μ}`, via `w = v^{1/μ} = (t − a) P^{1/μ}` and
  `HasPowExpansion.change_var`.
* `dlmf_2_3_17`: the closed forms of `b₀, b₁, b₂` (from `coeff_rpowPS_one_two`).
* `dlmf_2_3_18`: `q/v^{(λ+s)/μ} ∼ ∑ₖ cₖ (t − a)^{k−s−1}`; the residue (`k = s`) is `μ bₛ`.
* `dlmf_2_3_15`: Laplace's method under DLMF's conditions (a)–(c) on a range `S ⊆ (a, ∞)`
  containing some `(a, a + δ)` (e.g. `(a, b)`, `b ≤ ∞`).
-/

open Set Filter Topology Asymptotics PowerSeries MeasureTheory

namespace Azurite.DLMF

/-- Real power series as complex ones. -/
noncomputable abbrev toCPS : ℝ⟦X⟧ →+* ℂ⟦X⟧ := PowerSeries.map Complex.ofRealHom

theorem constantCoeff_toCPS (A : ℝ⟦X⟧) :
    constantCoeff (toCPS A) = Complex.ofReal (constantCoeff A) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
  rfl

/-- **DLMF 2.3.18**: `bₛ = (1/μ) [tˢ] Q(t) P(t)^{−(λ+s)/μ}` with `P = ∑ pₛ tˢ`, `Q = ∑ qₛ tˢ`:
the residue at `a` of `q(t)/(p(t) − p(a))^{(λ+s)/μ}` (`dlmf_2_3_18`). -/
noncomputable def laplaceMethodCoeff (ps : ℕ → ℝ) (qs : ℕ → ℂ) (lam μ : ℝ) (s : ℕ) : ℂ :=
  (1 / μ : ℂ) * coeff s (mk qs * toCPS (rpowPS (mk ps) (-((lam + s) / μ))))

/-- The series `μP + XP′` of the differentiated expansion `p′(t)/(t − a)^{μ−1}`. -/
theorem mk_derivExp (ps : ℕ → ℝ) (μ : ℝ) :
    mk (fun s => ((s : ℝ) + μ) * ps s) = C μ * mk ps + X * d⁄dX (mk ps) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [map_add, coeff_C_mul, coeff_succ_X_mul, coeff_derivative]
    simp only [coeff_mk]
    push_cast
    ring

/-- The formal identity behind 2.3.16 and 2.3.18: with `U = P^{1/μ}` and `D = μP + XP′`,
`Q D⁻¹ P^{(μ−λ)/μ} = B(XU)` where `B = ∑ bₛ wˢ` has the coefficients of 2.3.18. -/
theorem laplaceMethod_formal {ps : ℕ → ℝ} (qs : ℕ → ℂ) {lam μ : ℝ} (hμ : 0 < μ)
    (hp0 : 0 < ps 0) :
    mk qs * (toCPS (mk fun s => ((s : ℝ) + μ) * ps s))⁻¹ *
        toCPS (rpowPS (mk ps) ((μ - lam) / μ)) =
      (mk (laplaceMethodCoeff ps qs lam μ)).subst (X * toCPS (rpowPS (mk ps) (1 / μ))) := by
  set P := mk ps with hPdef
  have hP : 0 < constantCoeff P := by simpa [hPdef] using hp0
  set R : ℝ → ℂ⟦X⟧ := fun β => toCPS (rpowPS P β) with hRdef
  have hRmul : ∀ β γ, R β * R γ = R (β + γ) := fun β γ => by
    simp only [hRdef, ← map_mul, rpowPS_mul hP]
  have hR0 : R 0 = 1 := by simp only [hRdef, rpowPS_zero hP, map_one]
  have hRc : ∀ β, constantCoeff (R β) = ((ps 0 ^ β : ℝ) : ℂ) := fun β => by
    simp only [hRdef, constantCoeff_toCPS, constantCoeff_rpowPS hP]
    simp [hPdef]
  have hRc0 : ∀ β, constantCoeff (R β) ≠ 0 := fun β => by
    rw [hRc]; exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hp0 _).ne'
  set Pc := toCPS P with hPc
  have hR1 : R 1 = Pc := by rw [hRdef]; simp only [rpowPS_one hP]; rfl
  set Dc := toCPS (mk fun s => ((s : ℝ) + μ) * ps s) with hDc
  have e6 : Dc = C (μ : ℂ) * Pc + X * d⁄dX Pc := by
    rw [hDc, mk_derivExp, map_add, map_mul, map_mul, map_C, map_X, hPc, derivative_map_ofReal]
    rfl
  have hDc0 : constantCoeff Dc ≠ 0 := by
    rw [hDc, constantCoeff_toCPS, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    push_cast
    exact mul_ne_zero (by simp [hμ.ne']) (by exact_mod_cast hp0.ne')
  set φ := R (-(1 / μ)) with hφ
  set Uc := R (1 / μ) with hUc
  have e4 : φ * Uc = 1 := by rw [hφ, hUc, hRmul, neg_add_cancel, hR0]
  have e5 : d⁄dX φ * Pc = C ((-(1 / μ) : ℝ) : ℂ) * φ * d⁄dX Pc := by
    have h := congrArg toCPS (derivative_rpowPS_mul hP (-(1 / μ)))
    rw [map_mul, map_mul, map_mul, map_C, ← derivative_map_ofReal,
      ← derivative_map_ofReal] at h
    exact h
  set iP := R (-1) with hiP
  have e1 : Pc * iP = 1 := by rw [← hR1, hiP, hRmul, add_neg_cancel, hR0]
  have e2 : Dc⁻¹ * Dc = 1 := PowerSeries.inv_mul_cancel _ hDc0
  have e3 : C ((1 / μ : ℝ) : ℂ) * C (μ : ℂ) = 1 := by
    rw [← map_mul]; push_cast; rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hμ.ne'), map_one]
  -- the reversion `Ψ` of `X U`
  have hXU0 : constantCoeff (X * Uc) = 0 := by simp
  have hXU1 : IsUnit (coeff 1 (X * Uc)) := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    exact (hRc0 _).isUnit
  set Ψ := substInvOfIsUnit (X * Uc) hXU1 with hΨdef
  have hΨ0 : constantCoeff Ψ = 0 := constantCoeff_substInvOfIsUnit _ _
  have hsΨ : HasSubst Ψ := HasSubst.substInvOfIsUnit _ _
  have hsXU : HasSubst (X * Uc) := HasSubst.of_constantCoeff_zero' hXU0
  have hΨr : (X * Uc).subst Ψ = X := subst_substInvOfIsUnit_right _ hXU0 _
  have hΨl : Ψ.subst (X * Uc) = X := subst_substInvOfIsUnit_left _ hXU0 _
  have hΨ : Ψ = X * φ.subst Ψ := by
    have h1 : (Uc * φ).subst Ψ = 1 := by
      rw [mul_comm, e4, ← coe_substAlgHom hsΨ, map_one]
    rw [subst_mul hsΨ, subst_X hsΨ] at hΨr
    rw [subst_mul hsΨ] at h1
    calc Ψ = Ψ * (Uc.subst Ψ * φ.subst Ψ) := by rw [h1, mul_one]
      _ = X * φ.subst Ψ := by rw [← mul_assoc, hΨr]
  have hφ0 : constantCoeff φ ≠ 0 := hRc0 _
  -- the series identity
  set Rm := R ((μ - lam) / μ)
  set A := mk qs * Dc⁻¹ * Rm with hA
  have stepA : d⁄dX φ * Uc = C ((-(1 / μ) : ℝ) : ℂ) * d⁄dX Pc * iP := by
    calc d⁄dX φ * Uc = d⁄dX φ * Uc * (Pc * iP) := by rw [e1, mul_one]
      _ = (d⁄dX φ * Pc) * Uc * iP := by ring
      _ = C ((-(1 / μ) : ℝ) : ℂ) * (φ * Uc) * d⁄dX Pc * iP := by rw [e5]; ring
      _ = _ := by rw [e4]; ring
  have stepB : 1 - X * (d⁄dX φ * Uc) = C ((1 / μ : ℝ) : ℂ) * Dc * iP := by
    rw [stepA, e6]
    have hneg : C ((-(1 / μ) : ℝ) : ℂ) = -C ((1 / μ : ℝ) : ℂ) := by
      rw [← map_neg]; push_cast; rfl
    rw [hneg]
    linear_combination (-(Pc * iP)) * e3 - e1
  have e7 : ∀ s : ℕ, Rm * φ ^ s * iP = R (-((lam + s) / μ)) := fun s => by
    have hpow : φ ^ s = R (s * (-(1 / μ))) := by
      rw [hφ, hRdef]; simp only; rw [← map_pow, rpowPS_pow hP]
    rw [hpow, hRmul, hiP, hRmul]
    congr 1
    field_simp
    ring
  have key : ∀ s : ℕ, A * φ ^ s - X * (A * φ ^ s * d⁄dX φ * Uc) =
      C ((1 / μ : ℝ) : ℂ) * (mk qs * R (-((lam + s) / μ))) := fun s => by
    calc A * φ ^ s - X * (A * φ ^ s * d⁄dX φ * Uc) = A * φ ^ s * (1 - X * (d⁄dX φ * Uc)) := by
          ring
      _ = C ((1 / μ : ℝ) : ℂ) * mk qs * (Dc⁻¹ * Dc) * (Rm * φ ^ s * iP) := by
          rw [stepB, hA]; ring
      _ = _ := by rw [e2, e7]; ring
  have hsub : A.subst Ψ = mk (laplaceMethodCoeff ps qs lam μ) := by
    ext s
    rw [lagrange_inversion_second hΨ0 hφ0 hΨ A s, coeff_mk, laplaceMethodCoeff]
    have hc : coeff s (A * φ ^ s - X * (A * φ ^ (s - 1) * d⁄dX φ)) =
        coeff s (A * φ ^ s - X * (A * φ ^ s * d⁄dX φ * Uc)) := by
      rcases s with _ | s
      · simp only [map_sub, coeff_zero_X_mul]
      · have h3 : A * φ ^ (s + 1 - 1) * d⁄dX φ = A * φ ^ (s + 1) * d⁄dX φ * Uc := by
          rw [Nat.add_sub_cancel, pow_succ]
          linear_combination (-(A * φ ^ s * d⁄dX φ)) * e4
        rw [h3]
    rw [hc, key, coeff_C_mul]
    simp only [Complex.ofReal_div, Complex.ofReal_one]
    rfl
  rw [← hsub, subst_comp_subst_apply hsΨ hsXU, hΨl, X_subst]

/-! ### Converting between DLMF scales and power-series expansions -/

theorem tendsto_sub_self_nhdsGT (a : ℝ) : Tendsto (fun t : ℝ => t - a) (𝓝[>] a) (𝓝 0) := by
  have h := ((continuous_sub_right a).tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
  simpa using h

/-- A real expansion in `(t − a)^{s+c}` is `f/(t−a)^c ∼ ∑ aₛ (t−a)ˢ`. -/
theorem hasPowExpansion_div_rpow_real {a c : ℝ} {f : ℝ → ℝ} {as : ℕ → ℝ}
    (h : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + c)) f
      (fun s t => as s * (t - a) ^ ((s : ℝ) + c))) :
    HasPowExpansion (𝓝[>] a) (fun t => t - a) (fun t => f t / (t - a) ^ c) (mk as) :=
  fun n => by
    obtain ⟨C, hC⟩ := h.2 n
    rw [eventually_map] at hC
    refine IsBigO.of_bound C ?_
    filter_upwards [hC, self_mem_nhdsWithin] with t ht hta
    have hτ : 0 < t - a := sub_pos.mpr hta
    have hc0 : 0 < (t - a) ^ c := Real.rpow_pos_of_pos hτ c
    have e : f t / (t - a) ^ c - (trunc n (mk as)).eval (t - a) =
        (f t - ∑ s ∈ Finset.range n, as s * (t - a) ^ ((s : ℝ) + c)) /
          (t - a) ^ ((n : ℝ) + c) * (t - a) ^ n := by
      rw [eval_trunc_eq_sum]
      simp only [coeff_mk, Real.rpow_add hτ, Real.rpow_natCast, ← mul_assoc, ← Finset.sum_mul]
      have := pow_pos hτ n
      field_simp
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

/-- The same for complex-valued functions with real scales. -/
theorem hasPowExpansion_div_rpow_complex {a c : ℝ} {f : ℝ → ℂ} {as : ℕ → ℂ}
    (h : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (((t - a) ^ ((s : ℝ) + c) : ℝ) : ℂ)) f
      (fun s t => as s * (((t - a) ^ ((s : ℝ) + c) : ℝ) : ℂ))) :
    HasPowExpansion (𝓝[>] a) (fun t => ((t - a : ℝ) : ℂ))
      (fun t => f t / (((t - a) ^ c : ℝ) : ℂ)) (mk as) := fun n => by
  obtain ⟨C, hC⟩ := h.2 n
  rw [eventually_map] at hC
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, self_mem_nhdsWithin] with t ht hta
  have hτ : 0 < t - a := sub_pos.mpr hta
  have hc0 : (((t - a) ^ c : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ c).ne'
  have hτ0 : ((t - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have e : f t / (((t - a) ^ c : ℝ) : ℂ) - (trunc n (mk as)).eval ((t - a : ℝ) : ℂ) =
      (f t - ∑ s ∈ Finset.range n, as s * (((t - a) ^ ((s : ℝ) + c) : ℝ) : ℂ)) /
        (((t - a) ^ ((n : ℝ) + c) : ℝ) : ℂ) * ((t - a : ℝ) : ℂ) ^ n := by
    rw [eval_trunc_eq_sum]
    simp only [coeff_mk, Real.rpow_add hτ, Real.rpow_natCast, Complex.ofReal_mul,
      Complex.ofReal_pow]
    field_simp
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e, norm_mul]
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

/-- Back to DLMF form: if `F ∼ ∑ bₛ wˢ` (`w > 0`, `w → 0`), then
`wᵉ F ∼ ∑ bₛ w^{s+e}` with the scale `w^{s+e}`. -/
theorem isGenAsympExpansion_of_hasPowExpansion {α : Type*} {l : Filter α} {w : α → ℝ}
    (hw : ∀ᶠ x in l, 0 < w x) (hw0 : Tendsto w l (𝓝 0)) {F : α → ℂ} {b : ℕ → ℂ} (e : ℝ)
    (hF : HasPowExpansion l (fun x => (w x : ℂ)) F (mk b)) :
    IsGenAsympExpansionDLMF l (fun s x => ((w x ^ ((s : ℝ) + e) : ℝ) : ℂ))
      (fun x => ((w x ^ e : ℝ) : ℂ) * F x) (fun s x => b s * ((w x ^ ((s : ℝ) + e) : ℝ) : ℂ)) := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · have h := (Complex.continuous_ofReal.tendsto 0).comp hw0
    rw [Complex.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [hw] with x hx
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_div, ← Real.rpow_sub hx]
    push_cast
    ring_nf
    rw [Real.rpow_one]
  · obtain ⟨C, hC⟩ := (hF n).bound
    refine ⟨C, eventually_map.mpr ?_⟩
    filter_upwards [hC, hw] with x hx hwx
    have hp : ∀ r : ℝ, ((w x ^ r : ℝ) : ℂ) ≠ 0 := fun r =>
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hwx r).ne'
    have e1 : (((w x ^ e : ℝ) : ℂ) * F x - ∑ s ∈ Finset.range n,
        b s * ((w x ^ ((s : ℝ) + e) : ℝ) : ℂ)) / ((w x ^ ((n : ℝ) + e) : ℝ) : ℂ) =
        (F x - (trunc n (mk b)).eval (w x : ℂ)) / (w x : ℂ) ^ n := by
      rw [eval_trunc_eq_sum]
      simp only [coeff_mk, Real.rpow_add hwx, Real.rpow_natCast, Complex.ofReal_mul,
        Complex.ofReal_pow]
      have := hp e
      have hw' : (w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwx.ne'
      field_simp
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [e1, norm_div, div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero n
      (Complex.ofReal_ne_zero.mpr hwx.ne')))]
    exact hx

/-- `IsGenAsympExpansionDLMF` is unchanged by eventually equal data. -/
theorem IsGenAsympExpansionDLMF.congr' {α : Type*} {l : Filter α} {φ φ' : ℕ → α → ℂ}
    {f f' : α → ℂ} {fs fs' : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs)
    (hφ : ∀ s, φ s =ᶠ[l] φ' s) (hf : f =ᶠ[l] f') (hfs : ∀ s, fs s =ᶠ[l] fs' s) :
    IsGenAsympExpansionDLMF l φ' f' fs' := by
  refine ⟨fun s => (h.1 s).congr' ?_, fun n => ?_⟩
  · filter_upwards [hφ s, hφ (s + 1)] with x h1 h2
    rw [h1, h2]
  · obtain ⟨C, hC⟩ := h.2 n
    refine ⟨C, eventually_map.mpr ?_⟩
    rw [eventually_map] at hC
    have hall : ∀ᶠ x in l, ∀ s ∈ Finset.range n, fs s x = fs' s x :=
      (Filter.eventually_all_finset _).mpr fun s _ => hfs s
    filter_upwards [hC, hφ n, hf, hall] with x hx h1 h2 h3
    rw [← h1, ← h2, Finset.sum_congr rfl fun s hs => (h3 s hs).symm]
    exact hx

/-! ### The expansion 2.3.16 -/

theorem HasPowExpansion.congr_var {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α}
    {y z F : α → 𝕜} {A : 𝕜⟦X⟧} (h : HasPowExpansion l y F A) (hyz : y =ᶠ[l] z) :
    HasPowExpansion l z F A := fun n =>
  (h n).congr' (hyz.mono fun x hx => by simp only [hx]) (hyz.mono fun x hx => by simp only [hx])

theorem constantCoeff_mk' {K : Type*} [CommRing K] (c : ℕ → K) : constantCoeff (mk c) = c 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]

/-- **DLMF 2.3.16**: under 2.3.14 (with the differentiated expansion of `p`, `p₀ > 0`),
`q(t)/p′(t) ∼ ∑ bₛ v^{(s+λ−μ)/μ}` as `t → a+` (equivalently `v = p(t) − p(a) → 0+`), with the
coefficients `bₛ` of 2.3.18 (`laplaceMethodCoeff`). -/
theorem dlmf_2_3_16 {p p' : ℝ → ℝ} {q : ℝ → ℂ} {a lam μ : ℝ} {ps : ℕ → ℝ} {qs : ℕ → ℂ}
    (hμ : 0 < μ) (hp0 : 0 < ps 0)
    (hp : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ)))
    (hp' : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - 1)) p'
      (fun s t => ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)))
    (hq : IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => (((t - a) ^ ((s : ℝ) + lam - 1) : ℝ) : ℂ)) q
      (fun s t => qs s * (((t - a) ^ ((s : ℝ) + lam - 1) : ℝ) : ℂ))) :
    IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => (((p t - p a) ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) (fun t => q t / p' t)
      (fun s t => laplaceMethodCoeff ps qs lam μ s *
        (((p t - p a) ^ (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ)) := by
  have hy := tendsto_sub_self_nhdsGT a
  have hyc : Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ)) (𝓝[>] a) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hy
    rw [Complex.ofReal_zero] at h
    exact h
  simp only [add_sub_assoc] at hp' hq
  have hf := hasPowExpansion_div_rpow_real hp
  have hg := hasPowExpansion_div_rpow_real (as := fun s => ((s : ℝ) + μ) * ps s) hp'
  have hh := hasPowExpansion_div_rpow_complex hq
  set f₁ : ℝ → ℝ := fun t => (p t - p a) / (t - a) ^ μ with hf₁
  set g : ℝ → ℝ := fun t => p' t / (t - a) ^ (μ - 1) with hgdef
  have hP : 0 < constantCoeff (mk ps) := by rw [constantCoeff_mk']; exact hp0
  have hD : 0 < constantCoeff (mk fun s => ((s : ℝ) + μ) * ps s) := by
    rw [constantCoeff_mk']; push_cast; rw [zero_add]; exact mul_pos hμ hp0
  have hfpos : ∀ᶠ t in 𝓝[>] a, 0 < f₁ t := (hf.tendsto hy).eventually (lt_mem_nhds hP)
  have hgpos : ∀ᶠ t in 𝓝[>] a, 0 < g t := (hg.tendsto hy).eventually (lt_mem_nhds hD)
  have hτpos : ∀ᶠ t in 𝓝[>] a, 0 < t - a :=
    eventually_mem_nhdsWithin.mono fun t ht => sub_pos.mpr ht
  -- the expansion of `F₀ = (q/(t−a)^{λ−1}) (p′/(t−a)^{μ−1})⁻¹ f₁^{(μ−λ)/μ}`
  have hD0 : constantCoeff (toCPS (mk fun s => ((s : ℝ) + μ) * ps s)) ≠ 0 := by
    rw [constantCoeff_toCPS]; exact Complex.ofReal_ne_zero.mpr hD.ne'
  have h2 := hg.ofReal.inv hyc hD0
  have h3 := (hf.rpow hy hP ((μ - lam) / μ)).ofReal
  have hF0 := (hh.mul hyc h2).mul hyc h3
  have hu := (hf.rpow hy hP (1 / μ)).ofReal
  have hU0 : constantCoeff (toCPS (rpowPS (mk ps) (1 / μ))) ≠ 0 := by
    rw [constantCoeff_toCPS, constantCoeff_rpowPS hP]
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hP _).ne'
  have hB := hF0.change_var hyc hu hU0 (laplaceMethod_formal qs hμ hp0)
  -- the variable `w = v^{1/μ}`
  set w : ℝ → ℝ := fun t => (p t - p a) ^ (1 / μ) with hwdef
  have hv : ∀ t, 0 < t - a → 0 < f₁ t → p t - p a = f₁ t * (t - a) ^ μ := fun t hτ _ => by
    rw [hf₁]; simp only; rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hτ μ).ne']
  have hvpos : ∀ᶠ t in 𝓝[>] a, 0 < p t - p a := by
    filter_upwards [hτpos, hfpos] with t hτ hft
    rw [hv t hτ hft]; exact mul_pos hft (Real.rpow_pos_of_pos hτ μ)
  have hwz : ∀ᶠ t in 𝓝[>] a, ((t - a : ℝ) : ℂ) * ((f₁ t ^ (1 / μ) : ℝ) : ℂ) = (w t : ℂ) := by
    filter_upwards [hτpos, hfpos] with t hτ hft
    rw [hwdef]; simp only
    rw [hv t hτ hft, Real.mul_rpow hft.le (Real.rpow_nonneg hτ.le _), ← Real.rpow_mul hτ.le,
      mul_one_div_cancel hμ.ne', Real.rpow_one]
    push_cast; ring
  have hBw := hB.congr_var hwz
  have hwpos : ∀ᶠ t in 𝓝[>] a, 0 < w t :=
    hvpos.mono fun t ht => Real.rpow_pos_of_pos ht _
  have hvt : Tendsto (fun t => p t - p a) (𝓝[>] a) (𝓝 0) := by
    have h1 := (hf.tendsto hy).mul (hy.rpow_const (Or.inr hμ.le))
    rw [Real.zero_rpow hμ.ne', mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hτpos, hfpos] with t hτ hft
    exact (hv t hτ hft).symm
  have hw0 : Tendsto w (𝓝[>] a) (𝓝 0) := by
    have h1 := hvt.rpow_const (p := 1 / μ) (Or.inr (by positivity))
    rwa [Real.zero_rpow (by positivity)] at h1
  have hG := isGenAsympExpansion_of_hasPowExpansion hwpos hw0 (lam - μ) hBw
  -- back to the variable `v`
  have hpow : ∀ t, 0 < p t - p a → ∀ x : ℝ, w t ^ x = (p t - p a) ^ (x / μ) := fun t hvt x => by
    rw [hwdef]; simp only; rw [← Real.rpow_mul hvt.le]; congr 1; ring
  refine hG.congr' (fun s => ?_) ?_ (fun s => ?_)
  · filter_upwards [hvpos] with t hvt
    rw [hpow t hvt]; congr 3; ring
  · filter_upwards [hτpos, hfpos, hgpos, hvpos] with t hτ hft hgt hvt
    have hp't : 0 < p' t := by
      have : p' t = g t * (t - a) ^ (μ - 1) := by
        rw [hgdef]; simp only; rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hτ _).ne']
      rw [this]; exact mul_pos hgt (Real.rpow_pos_of_pos hτ _)
    have hreal : w t ^ (lam - μ) * f₁ t ^ ((μ - lam) / μ) * (t - a) ^ (μ - 1) =
        (t - a) ^ (lam - 1) := by
      have e1 : w t ^ (lam - μ) = (t - a) ^ (lam - μ) * f₁ t ^ ((lam - μ) / μ) := by
        rw [hpow t hvt, hv t hτ hft, Real.mul_rpow hft.le (Real.rpow_nonneg hτ.le _),
          ← Real.rpow_mul hτ.le, mul_comm]
        congr 2
        field_simp
      have e2 : f₁ t ^ ((lam - μ) / μ) * f₁ t ^ ((μ - lam) / μ) = 1 := by
        rw [← Real.rpow_add hft, show (lam - μ) / μ + (μ - lam) / μ = 0 by ring,
          Real.rpow_zero]
      have e3 : (t - a) ^ (lam - μ) * (t - a) ^ (μ - 1) = (t - a) ^ (lam - 1) := by
        rw [← Real.rpow_add hτ]; congr 1; ring
      rw [e1]
      calc (t - a) ^ (lam - μ) * f₁ t ^ ((lam - μ) / μ) * f₁ t ^ ((μ - lam) / μ) *
            (t - a) ^ (μ - 1) =
          ((t - a) ^ (lam - μ) * (t - a) ^ (μ - 1)) *
            (f₁ t ^ ((lam - μ) / μ) * f₁ t ^ ((μ - lam) / μ)) := by ring
        _ = _ := by rw [e2, e3, mul_one]
    have hc : ((w t ^ (lam - μ) : ℝ) : ℂ) * ((f₁ t ^ ((μ - lam) / μ) : ℝ) : ℂ) *
        (((t - a) ^ (μ - 1) : ℝ) : ℂ) = (((t - a) ^ (lam - 1) : ℝ) : ℂ) := by
      exact_mod_cast hreal
    have h1 : (((t - a) ^ (lam - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ _).ne'
    have h2 : (((t - a) ^ (μ - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ _).ne'
    have h3 : (p' t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp't.ne'
    have h4 : ((w t ^ (lam - μ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hvt _) _).ne'
    have h5 : ((f₁ t ^ ((μ - lam) / μ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hft _).ne'
    simp only [Pi.mul_apply, hgdef, Complex.ofReal_div]
    rw [← hc]
    field_simp
  · filter_upwards [hvpos] with t hvt
    rw [hpow t hvt]; congr 3; ring

/-! ### The residue form 2.3.18 -/

/-- **DLMF 2.3.18**: `q(t)/(p(t) − p(a))^{(λ+s)/μ} ∼ ∑ₖ cₖ (t − a)^{k−s−1}` as `t → a+` with
`cₖ = [tᵏ] Q P^{−(λ+s)/μ}`; its residue at `a` (the coefficient of `(t − a)^{−1}`, `k = s`)
is `μ bₛ`. -/
theorem dlmf_2_3_18 {p : ℝ → ℝ} {q : ℝ → ℂ} {a lam μ : ℝ} {ps : ℕ → ℝ} {qs : ℕ → ℂ}
    (hμ : 0 < μ) (hp0 : 0 < ps 0)
    (hp : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ)))
    (hq : IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => (((t - a) ^ ((s : ℝ) + lam - 1) : ℝ) : ℂ)) q
      (fun s t => qs s * (((t - a) ^ ((s : ℝ) + lam - 1) : ℝ) : ℂ))) (s : ℕ) :
    IsGenAsympExpansionDLMF (𝓝[>] a) (fun k t => (((t - a) ^ ((k : ℝ) - s - 1) : ℝ) : ℂ))
        (fun t => q t / (((p t - p a) ^ ((lam + s) / μ) : ℝ) : ℂ))
        (fun k t => coeff k (mk qs * toCPS (rpowPS (mk ps) (-((lam + s) / μ)))) *
          (((t - a) ^ ((k : ℝ) - s - 1) : ℝ) : ℂ)) ∧
      laplaceMethodCoeff ps qs lam μ s =
        (1 / μ : ℂ) * coeff s (mk qs * toCPS (rpowPS (mk ps) (-((lam + s) / μ)))) := by
  refine ⟨?_, rfl⟩
  have hy := tendsto_sub_self_nhdsGT a
  have hyc : Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ)) (𝓝[>] a) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp hy
    rw [Complex.ofReal_zero] at h
    exact h
  simp only [add_sub_assoc] at hq
  have hf := hasPowExpansion_div_rpow_real hp
  have hh := hasPowExpansion_div_rpow_complex hq
  set f₁ : ℝ → ℝ := fun t => (p t - p a) / (t - a) ^ μ with hf₁
  have hP : 0 < constantCoeff (mk ps) := by rw [constantCoeff_mk']; exact hp0
  have hfpos : ∀ᶠ t in 𝓝[>] a, 0 < f₁ t := (hf.tendsto hy).eventually (lt_mem_nhds hP)
  have hτpos : ∀ᶠ t in 𝓝[>] a, 0 < t - a :=
    eventually_mem_nhdsWithin.mono fun t ht => sub_pos.mpr ht
  set β := (lam + s) / μ
  have hG0 := hh.mul hyc (hf.rpow hy hP (-β)).ofReal
  have hG : HasPowExpansion (𝓝[>] a) (fun t => ((t - a : ℝ) : ℂ))
      ((fun t => q t / (((t - a) ^ (lam - 1) : ℝ) : ℂ)) * fun x => ((f₁ x ^ (-β) : ℝ) : ℂ))
      (mk fun k => coeff k (mk qs * toCPS (rpowPS (mk ps) (-β)))) := by
    have e : (mk fun k => coeff k (mk qs * toCPS (rpowPS (mk ps) (-β)))) =
        mk qs * toCPS (rpowPS (mk ps) (-β)) := by ext k; simp
    rw [e]; exact hG0
  have hE := isGenAsympExpansion_of_hasPowExpansion (w := fun t => t - a) hτpos hy
    (-(s : ℝ) - 1) hG
  have hexp : ∀ k : ℕ, (k : ℝ) + (-(s : ℝ) - 1) = (k : ℝ) - s - 1 := fun k => by ring
  refine hE.congr' (fun k => ?_) ?_ (fun k => ?_)
  · exact Eventually.of_forall fun t => by
      show (((t - a) ^ ((k : ℝ) + (-(s : ℝ) - 1)) : ℝ) : ℂ) = _
      rw [hexp]
  · filter_upwards [hτpos, hfpos] with t hτ hft
    have hv : p t - p a = f₁ t * (t - a) ^ μ := by
      rw [hf₁]; simp only; rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hτ μ).ne']
    have hreal : (t - a) ^ (-(s : ℝ) - 1) * f₁ t ^ (-β) * (p t - p a) ^ β =
        (t - a) ^ (lam - 1) := by
      rw [hv, Real.mul_rpow hft.le (Real.rpow_nonneg hτ.le _), ← Real.rpow_mul hτ.le]
      calc (t - a) ^ (-(s : ℝ) - 1) * f₁ t ^ (-β) * (f₁ t ^ β * (t - a) ^ (μ * β)) =
          ((t - a) ^ (-(s : ℝ) - 1) * (t - a) ^ (μ * β)) * (f₁ t ^ (-β) * f₁ t ^ β) := by ring
        _ = _ := by
          rw [← Real.rpow_add hft, neg_add_cancel, Real.rpow_zero, mul_one,
            ← Real.rpow_add hτ]
          congr 1
          simp only [β]
          field_simp
          ring
    have hc : (((t - a) ^ (-(s : ℝ) - 1) : ℝ) : ℂ) * ((f₁ t ^ (-β) : ℝ) : ℂ) *
        (((p t - p a) ^ β : ℝ) : ℂ) = (((t - a) ^ (lam - 1) : ℝ) : ℂ) := by
      exact_mod_cast hreal
    have h1 : (((t - a) ^ (lam - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ _).ne'
    have h2 : (((p t - p a) ^ β : ℝ) : ℂ) ≠ 0 := by
      rw [hv]
      exact Complex.ofReal_ne_zero.mpr
        (Real.rpow_pos_of_pos (mul_pos hft (Real.rpow_pos_of_pos hτ μ)) _).ne'
    have h3 : (((t - a) ^ (-(s : ℝ) - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ _).ne'
    have h4 : ((f₁ t ^ (-β) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hft _).ne'
    simp only [Pi.mul_apply]
    rw [← hc]
    field_simp
  · exact Eventually.of_forall fun t => by
      show _ * (((t - a) ^ ((k : ℝ) + (-(s : ℝ) - 1)) : ℝ) : ℂ) = _
      rw [hexp]

/-! ### The first coefficients 2.3.17 -/

theorem coeff_one_mul' {K : Type*} [CommRing K] (f g : K⟦X⟧) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

theorem coeff_zero_mul' {K : Type*} [CommRing K] (f g : K⟦X⟧) :
    coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  rw [coeff_mul]
  simp

theorem coeff_two_mul' {K : Type*} [CommRing K] (f g : K⟦X⟧) :
    coeff 2 (f * g) = coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp
  ring

theorem coeff_rpowPS_one_two {P : ℝ⟦X⟧} (hP : 0 < constantCoeff P) (β : ℝ) :
    coeff 1 (rpowPS P β) * coeff 0 P = β * coeff 0 P ^ β * coeff 1 P ∧
      2 * coeff 2 (rpowPS P β) * coeff 0 P =
        2 * β * coeff 0 P ^ β * coeff 2 P + (β - 1) * coeff 1 (rpowPS P β) * coeff 1 P := by
  have hr0 : coeff 0 (rpowPS P β) = coeff 0 P ^ β := by
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_rpowPS hP]
  have hD := derivative_rpowPS_mul hP β
  have h0 := congrArg (coeff 0) hD
  have h1 := congrArg (coeff 1) hD
  rw [mul_assoc, coeff_C_mul] at h0 h1
  rw [coeff_zero_mul', coeff_zero_mul', coeff_derivative, coeff_derivative, hr0] at h0
  rw [coeff_one_mul', coeff_one_mul', coeff_derivative, coeff_derivative, coeff_derivative,
    coeff_derivative, hr0] at h1
  push_cast at h0 h1
  constructor
  · linear_combination h0
  · linear_combination h1

theorem coeff_toCPS (k : ℕ) (A : ℝ⟦X⟧) : coeff k (toCPS A) = Complex.ofReal (coeff k A) := by
  rw [coeff_map]; rfl

/-- **DLMF 2.3.17**: the first three coefficients,
`b₀ = q₀/(μ p₀^{λ/μ})`, `b₁ = (q₁/μ − (λ+1)p₁q₀/(μ²p₀))/p₀^{(λ+1)/μ}`, and
`b₂ = (q₂/μ − (λ+2)(p₁q₁ + p₂q₀)/(μ²p₀) + (λ+2)(λ+μ+2)p₁²q₀/(2μ³p₀²))/p₀^{(λ+2)/μ}`. -/
theorem dlmf_2_3_17 {ps : ℕ → ℝ} (qs : ℕ → ℂ) {lam μ : ℝ} (hμ : 0 < μ) (hp0 : 0 < ps 0) :
    laplaceMethodCoeff ps qs lam μ 0 = qs 0 / (μ * (ps 0 ^ (lam / μ) : ℝ)) ∧
    laplaceMethodCoeff ps qs lam μ 1 =
      (qs 1 / μ - (lam + 1) * ps 1 * qs 0 / (μ ^ 2 * ps 0)) / (ps 0 ^ ((lam + 1) / μ) : ℝ) ∧
    laplaceMethodCoeff ps qs lam μ 2 =
      (qs 2 / μ - (lam + 2) * (ps 1 * qs 1 + ps 2 * qs 0) / (μ ^ 2 * ps 0) +
        (lam + 2) * (lam + μ + 2) * ps 1 ^ 2 * qs 0 / (2 * μ ^ 3 * ps 0 ^ 2)) /
        (ps 0 ^ ((lam + 2) / μ) : ℝ) := by
  have hP : 0 < constantCoeff (mk ps) := by rw [constantCoeff_mk']; exact hp0
  have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
  have hp0c : (ps 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp0.ne'
  have hr0 : ∀ γ : ℝ, coeff 0 (rpowPS (mk ps) (-γ)) = (ps 0 ^ γ)⁻¹ := fun γ => by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_rpowPS hP, constantCoeff_mk',
      Real.rpow_neg hp0.le]
  have hσ : ∀ γ : ℝ, ((ps 0 ^ γ : ℝ) : ℂ) ≠ 0 := fun γ =>
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hp0 γ).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [laplaceMethodCoeff, coeff_zero_mul', coeff_mk, coeff_toCPS]
    simp only [Nat.cast_zero, add_zero]
    rw [hr0]
    push_cast
    have := hσ (lam / μ)
    field_simp
  · obtain ⟨h1, -⟩ := coeff_rpowPS_one_two hP (-((lam + 1) / μ))
    simp only [coeff_mk] at h1
    rw [Real.rpow_neg hp0.le] at h1
    have hr1 : coeff 1 (rpowPS (mk ps) (-((lam + 1) / μ))) =
        -((lam + 1) / μ) * (ps 0 ^ ((lam + 1) / μ))⁻¹ * ps 1 / ps 0 := by
      rw [eq_div_iff hp0.ne']; linear_combination h1
    rw [laplaceMethodCoeff, coeff_one_mul', coeff_mk, coeff_mk, coeff_toCPS, coeff_toCPS]
    simp only [Nat.cast_one]
    rw [hr1, hr0]
    push_cast
    have := hσ ((lam + 1) / μ)
    field_simp
    ring
  · obtain ⟨h1, h2⟩ := coeff_rpowPS_one_two hP (-((lam + 2) / μ))
    simp only [coeff_mk] at h1 h2
    rw [Real.rpow_neg hp0.le] at h1 h2
    have hr1 : coeff 1 (rpowPS (mk ps) (-((lam + 2) / μ))) =
        -((lam + 2) / μ) * (ps 0 ^ ((lam + 2) / μ))⁻¹ * ps 1 / ps 0 := by
      rw [eq_div_iff hp0.ne']; linear_combination h1
    rw [hr1] at h2
    have hr2 : coeff 2 (rpowPS (mk ps) (-((lam + 2) / μ))) =
        (2 * -((lam + 2) / μ) * (ps 0 ^ ((lam + 2) / μ))⁻¹ * ps 2 +
          (-((lam + 2) / μ) - 1) * (-((lam + 2) / μ) * (ps 0 ^ ((lam + 2) / μ))⁻¹ * ps 1 /
            ps 0) * ps 1) / (2 * ps 0) := by
      rw [eq_div_iff (by positivity)]; linear_combination h2
    rw [laplaceMethodCoeff, coeff_two_mul', coeff_mk, coeff_mk, coeff_mk, coeff_toCPS,
      coeff_toCPS, coeff_toCPS]
    simp only [Nat.cast_ofNat]
    rw [hr2, hr1, hr0]
    push_cast
    have := hσ ((lam + 2) / μ)
    field_simp
    ring

/-! ### Laplace's method 2.3.15 -/

theorem laplace_p'_eventually_pos {p' : ℝ → ℝ} {a μ : ℝ} {ps : ℕ → ℝ} (hμ : 0 < μ)
    (hp0 : 0 < ps 0)
    (hp' : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - 1)) p'
      (fun s t => ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1))) :
    ∀ᶠ t in 𝓝[>] a, 0 < p' t := by
  simp only [add_sub_assoc] at hp'
  have hg := hasPowExpansion_div_rpow_real (as := fun s => ((s : ℝ) + μ) * ps s) hp'
  have hD : 0 < constantCoeff (mk fun s => ((s : ℝ) + μ) * ps s) := by
    rw [constantCoeff_mk']; push_cast; rw [zero_add]; exact mul_pos hμ hp0
  filter_upwards [(hg.tendsto (tendsto_sub_self_nhdsGT a)).eventually (lt_mem_nhds hD),
    self_mem_nhdsWithin] with t hgt hta
  have hτ : 0 < t - a := sub_pos.mpr hta
  have : p' t = p' t / (t - a) ^ (μ - 1) * (t - a) ^ (μ - 1) := by
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hτ _).ne']
  rw [this]
  exact mul_pos hgt (Real.rpow_pos_of_pos hτ _)

theorem laplace_p_tendsto {p : ℝ → ℝ} {a μ : ℝ} {ps : ℕ → ℝ} (hμ : 0 < μ)
    (hp : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ))) :
    Tendsto p (𝓝[>] a) (𝓝 (p a)) := by
  have hy := tendsto_sub_self_nhdsGT a
  have hf := hasPowExpansion_div_rpow_real hp
  have h1 := (hf.tendsto hy).mul (hy.rpow_const (Or.inr hμ.le))
  rw [Real.zero_rpow hμ.ne', mul_zero] at h1
  have h2 := h1.add_const (p a)
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t hta
  have hτ : 0 < t - a := sub_pos.mpr hta
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hτ μ).ne', sub_add_cancel]

/-- **DLMF 2.3.15 (Laplace's method)**: for `I(x) = ∫ e^{−xp(t)} q(t) dt` over a range `S`
starting at `a` (2.3.13), under (a) `p′` and `q` continuous on some `(a, a + δ)` (where `p′`
is the derivative of `p`) and the minimum of `p` on `S` approached only at `a`, (b) the
expansions 2.3.14 of `p` (differentiable, `p₀ > 0`) and `q`, and (c) absolute convergence for
large `x`:
`I(x) ∼ e^{−xp(a)} ∑ Γ((s+λ)/μ) bₛ x^{−(s+λ)/μ}` as `x → +∞`, with the `bₛ` of 2.3.16–2.3.18. -/
theorem dlmf_2_3_15 {p p' : ℝ → ℝ} {q : ℝ → ℂ} {S : Set ℝ} {a lam μ x₀ : ℝ} {ps : ℕ → ℝ}
    {qs : ℕ → ℂ} (hlam : 0 < lam) (hμ : 0 < μ) (hp0 : 0 < ps 0)
    (hS : MeasurableSet S) (hSa : S ⊆ Ioi a) (hSc : ∃ δ, 0 < δ ∧ Ioo a (a + δ) ⊆ S)
    (hreg : ∃ δ, 0 < δ ∧ (∀ t ∈ Ioo a (a + δ), HasDerivAt p (p' t) t) ∧
      ContinuousOn p' (Ioo a (a + δ)) ∧ ContinuousOn q (Ioo a (a + δ)))
    (hmin : ∀ δ, 0 < δ → ∃ η, 0 < η ∧ ∀ t ∈ S, a + δ ≤ t → p a + η ≤ p t)
    (hp : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ)))
    (hp' : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - 1)) p'
      (fun s t => ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)))
    (hq : IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => (((t - a) ^ ((s : ℝ) + lam - 1) : ℝ) : ℂ)) q
      (fun s t => qs s * (((t - a) ^ ((s : ℝ) + lam - 1) : ℝ) : ℂ)))
    (hint : ∀ x, x₀ ≤ x → IntegrableOn (fun t => (Real.exp (-(x * p t)) : ℂ) * q t) S) :
    IsGenAsympExpansionDLMF atTop
      (fun s x => (Real.exp (-(x * p a)) : ℂ) * ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))
      (fun x => ∫ t in S, (Real.exp (-(x * p t)) : ℂ) * q t)
      (fun s x => (Real.exp (-(x * p a)) : ℂ) * ((Real.Gamma (watsonExp lam μ s) : ℂ) *
        laplaceMethodCoeff ps qs lam μ s * ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))) := by
  obtain ⟨δ₁, hδ₁, hS1⟩ := hSc
  obtain ⟨δ₂, hδ₂, hd, hp'c, hqc⟩ := hreg
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (laplace_p'_eventually_pos hμ hp0 hp')
  have hu' : a < u := hu
  set δ₀ := min (min δ₁ δ₂) (u - a)
  have hδ₀ : 0 < δ₀ := lt_min (lt_min hδ₁ hδ₂) (by linarith)
  have hsub : ∀ δ, δ₀ ≤ δ → Ioo a (a + δ₀) ⊆ Ioo a (a + δ) := fun δ h =>
    Ioo_subset_Ioo_right (by linarith)
  have h1 : δ₀ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : δ₀ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : a + δ₀ ≤ u := by linarith [min_le_right (min δ₁ δ₂) (u - a)]
  exact laplace_method_core hlam hμ hδ₀ hS hSa ((hsub δ₁ h1).trans hS1)
    (fun t ht => hd t (hsub δ₂ h2 ht))
    (fun t ht => hus ⟨ht.1, ht.2.trans_le h3⟩)
    (hp'c.mono (hsub δ₂ h2)) (hqc.mono (hsub δ₂ h2)) (laplace_p_tendsto hμ hp) hmin hint
    (dlmf_2_3_16 hμ hp0 hp hp' hq)

end Azurite.DLMF
