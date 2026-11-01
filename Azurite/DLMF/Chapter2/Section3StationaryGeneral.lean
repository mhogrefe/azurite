/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3StationaryInv

/-!
# DLMF §2.3(iv): the method of stationary phase (2.3.19–2.3.23)

The range `S = (a, b)` is any open order-connected set above `a` containing some `(a, a + δ)`;
`t → b−` is the filter `upperEnd S`, so `b` may be finite or `∞`. With `v = p(t) − p(a)` and its
smooth inverse `t(v)`, the integral becomes `e^{ixp(a)} ∫ e^{ixv} Q(v) dv`, `Q = P₀ ∘ t`, and
`statP_comp_expansion` turns `statP_sub_bound` into the differentiated expansion of `Q` at `0+`.

* `dlmf_2_3_23_d`: case (d), `p(b) = ∞`: 2.3.20 applies to `Q` directly; the uniform convergence
  2.3.22 is transported by the substitution. DLMF's extra condition `P₀(b) = 0` is not needed.
* `dlmf_2_3_23`: `p(b)` finite with (c) the limits `Pₛ(b)`: a smooth cutoff splits `Q`; the part
  near `0` is 2.3.20, the part near `V = p(b) − p(a)` is `fourier_endpoint_iter`
  (`−e^{ixV} ∑ Pₛ(b)(i/x)^{s+1}`). The two-series "∼" is stated as an error
  `O(x^{−(N+λ)/μ} + x^{−(M+1)})` after `N` and `M` terms.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

/-- The filter `t → b−` at the upper end of a set `S`. -/
def upperEnd (S : Set ℝ) : Filter ℝ := ⨅ t ∈ S, 𝓟 (S ∩ Ioi t)

theorem mem_upperEnd {S : Set ℝ} {t : ℝ} (ht : t ∈ S) : S ∩ Ioi t ∈ upperEnd S :=
  mem_iInf_of_mem t (mem_iInf_of_mem ht (mem_principal_self _))

theorem tendsto_upperEnd_iff {α : Type*} {F : Filter α} {S : Set ℝ} {g : α → ℝ} :
    Tendsto g F (upperEnd S) ↔ ∀ t ∈ S, ∀ᶠ x in F, g x ∈ S ∧ t < g x := by
  simp only [upperEnd, tendsto_iInf, tendsto_principal]
  rfl

theorem upperEnd_neBot {S : Set ℝ} (hS : IsOpen S) (hne : S.Nonempty) : (upperEnd S).NeBot := by
  rw [upperEnd, iInf_subtype']
  have : Nonempty S := hne.to_subtype
  refine iInf_neBot_of_directed ?_ fun t => ?_
  · intro t t'
    refine ⟨if (t : ℝ) ≤ t' then t' else t, ?_, ?_⟩ <;> split_ifs with h <;>
      simp only [ge_iff_le, le_principal_iff, mem_principal] <;> intro x hx <;>
      exact ⟨hx.1, by have := hx.2; simp only [mem_Ioi] at this ⊢; linarith⟩
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS t t.2
    refine principal_neBot_iff.mpr ⟨t + ε / 2, hball ?_, by simp only [mem_Ioi]; linarith⟩
    rw [Metric.mem_ball, Real.dist_eq, show t + ε / 2 - t = ε / 2 by ring,
      abs_of_pos (half_pos hε)]
    linarith

/-! ### The range of `v = p − p(a)` -/

section Range

variable {v : ℝ → ℝ} {S : Set ℝ} {a : ℝ} (hSo : IsOpen S) (hSc : S.OrdConnected)
  (hSa : S ⊆ Ioi a) (hSδ : ∃ δ, 0 < δ ∧ Ioo a (a + δ) ⊆ S) (hvc : ContinuousOn v S)
  (hmono : StrictMonoOn v S) (h0 : Tendsto v (𝓝[>] a) (𝓝 0))

include hSa hSδ hmono h0 in
theorem range_pos {t : ℝ} (ht : t ∈ S) : 0 < v t := by
  obtain ⟨δ, hδ, hsub⟩ := hSδ
  have hta : a < t := hSa ht
  set s := (a + min t (a + δ)) / 2
  have hs1 : a < s := by have := lt_min hta (by linarith : a < a + δ); simp only [s]; linarith
  have hs2 : s < t := by have := min_le_left t (a + δ); simp only [s]; linarith
  have hs3 : s < a + δ := by have := min_le_right t (a + δ); simp only [s]; linarith
  have hsS : s ∈ S := hsub ⟨hs1, hs3⟩
  have hvs : 0 ≤ v s := by
    refine le_of_tendsto h0 ?_
    filter_upwards [Ioo_mem_nhdsGT hs1] with s' hs'
    exact (hmono (hsub ⟨hs'.1, hs'.2.trans hs3⟩) hsS hs'.2).le
  exact hvs.trans_lt (hmono hsS ht hs2)

include hvc hSc hmono in
theorem mem_image_of_between {w : ℝ} {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) (hsw : v s < w)
    (hwt : w < v t) : w ∈ v '' S := by
  have hst : s < t := by
    by_contra h
    exact absurd (hsw.trans hwt) (not_lt.mpr (hmono.monotoneOn ht hs (not_lt.mp h)))
  obtain ⟨r, hr, hrw⟩ := intermediate_value_Icc hst.le (hvc.mono (hSc.out hs ht))
    ⟨hsw.le, hwt.le⟩
  exact ⟨r, hSc.out hs ht hr, hrw⟩

include hSδ h0 in
theorem exists_below {w : ℝ} (hw : 0 < w) : ∃ s ∈ S, v s < w := by
  obtain ⟨δ, hδ, hsub⟩ := hSδ
  obtain ⟨s, hs1, hs2⟩ := ((h0.eventually (gt_mem_nhds hw)).and
    (Ioo_mem_nhdsGT (by linarith : a < a + δ))).exists
  exact ⟨s, hsub hs2, hs1⟩

include hvc hSc hSo hSa hSδ hmono h0 in
/-- `v(S) = (0, V)` when `p(b)` is finite. -/
theorem image_eq_Ioo {V : ℝ} (hV : Tendsto v (upperEnd S) (𝓝 V)) : v '' S = Ioo 0 V := by
  have hne : S.Nonempty := by
    obtain ⟨δ, hδ, hsub⟩ := hSδ
    exact ⟨a + δ / 2, hsub ⟨by linarith, by linarith⟩⟩
  have := upperEnd_neBot hSo hne
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨range_pos hSa hSδ hmono h0 ht, ?_⟩
    obtain ⟨t', ht'S, htt'⟩ := (tendsto_upperEnd_iff.mp tendsto_id t ht).exists
    refine (hmono ht ht'S htt').trans_le (ge_of_tendsto hV ?_)
    filter_upwards [tendsto_upperEnd_iff.mp tendsto_id t' ht'S] with t'' ht''
    exact (hmono ht'S ht''.1 ht''.2).le
  · rintro ⟨hw0, hwV⟩
    obtain ⟨s, hs, hsw⟩ := exists_below hSδ h0 hw0
    obtain ⟨t, ht1, ht2⟩ := ((hV.eventually (lt_mem_nhds hwV)).and
      (tendsto_upperEnd_iff.mp tendsto_id s hs)).exists
    exact mem_image_of_between hSc hvc hmono hs ht2.1 hsw ht1

include hvc hSc hSo hSa hSδ hmono h0 in
/-- `v(S) = (0, ∞)` when `p(b) = ∞`. -/
theorem image_eq_Ioi (hV : Tendsto v (upperEnd S) atTop) : v '' S = Ioi 0 := by
  have hne : S.Nonempty := by
    obtain ⟨δ, hδ, hsub⟩ := hSδ
    exact ⟨a + δ / 2, hsub ⟨by linarith, by linarith⟩⟩
  have := upperEnd_neBot hSo hne
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact range_pos hSa hSδ hmono h0 ht
  · intro hw0
    obtain ⟨s, hs, hsw⟩ := exists_below hSδ h0 hw0
    obtain ⟨t, ht1, ht2⟩ := ((hV.eventually (eventually_gt_atTop w)).and
      (tendsto_upperEnd_iff.mp tendsto_id s hs)).exists
    exact mem_image_of_between hSc hvc hmono hs ht2.1 hsw ht1

end Range

theorem isAsympScale_rpow_nhdsGT {e : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (he : ∀ s, e (s + 1) = e s + c) :
    IsAsympScaleDLMF (𝓝[>] (0 : ℝ)) fun s w => ((w ^ e s : ℝ) : ℂ) := fun s => by
  have h := ((Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).tendsto).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [Real.zero_rpow hc.ne'] at h
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
  rw [Complex.ofReal_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : (0 : ℝ) < w := hw
  simp only [Function.comp_apply]
  rw [← Complex.ofReal_div, ← Real.rpow_sub hw', he s]
  congr 2
  ring

/-! ### The expansion of `Q(v) = P₀(t(v))` as `v → 0+` -/

/-- The bounds of `statP_sub_bound`, read in the variable `v`, are the differentiated expansion
of `Q = P₀ ∘ t` required by 2.3.20. -/
theorem statP_comp_expansion {p p' : ℝ → ℝ} {q : ℝ → ℂ} {S T : Set ℝ} {a lam μ : ℝ}
    {ps : ℕ → ℝ} {qs : ℕ → ℂ} (hμ : 0 < μ) (hp0 : 0 < ps 0)
    (hSa : S ⊆ Ioi a) (hSδ : ∃ δ, 0 < δ ∧ Ioo a (a + δ) ⊆ S)
    (hps : ContDiffOn ℝ ∞ p S) (hqs : ContDiffOn ℝ ∞ q S)
    (hd : ∀ t ∈ S, HasDerivAt p (p' t) t) (hmono : StrictMonoOn (fun t => p t - p a) S)
    (hp : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - k))
      (iteratedDeriv k fun t => p t - p a)
      (fun s t => ps s * (descPochhammer ℝ k).eval ((s : ℝ) + μ) * (t - a) ^ ((s : ℝ) + μ - k)))
    (hq : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)) (iteratedDeriv k q)
      (fun s t => qs s * (((descPochhammer ℝ k).eval ((s : ℝ) + lam - 1) : ℝ) : ℂ) *
        ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)))
    {g : ℝ → ℝ} (hgS : ∀ w ∈ T, g w ∈ S) (hgv : ∀ w ∈ T, p (g w) - p a = w)
    (hTpos : ∀ t ∈ S, 0 < p t - p a) (hT0 : ∀ t ∈ S, Ioo 0 (p t - p a) ⊆ T)
    {Q : ℝ → ℂ} (hQk : ∀ k, ∀ w ∈ T, iteratedDeriv k Q w = statP p' q k (g w)) (k : ℕ) :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun s w => ((w ^ (((s : ℝ) + lam - μ) / μ - k) : ℝ) : ℂ)) (iteratedDeriv k Q)
      (fun s w => laplaceMethodCoeff ps qs lam μ s *
        (((descPochhammer ℝ k).eval (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ) *
        ((w ^ (((s : ℝ) + lam - μ) / μ - k) : ℝ) : ℂ)) := by
  obtain ⟨δS, hδS, hsubS⟩ := hSδ
  refine ⟨isAsympScale_rpow_nhdsGT (one_div_pos.mpr hμ) fun s => ?_, fun N => ?_⟩
  · push_cast; field_simp; ring
  obtain ⟨δ', C, hδ', hb⟩ := statP_sub_bound (p := p) (p' := p') (q := q) (lam := lam) hμ hp0
    hδS (fun t ht => hd t (hsubS ht)) (hps.mono hsubS) (hqs.mono hsubS) hp hq N k
  set t₀ := a + min δ' δS / 2
  have hm : 0 < min δ' δS := lt_min hδ' hδS
  have ht₀S : t₀ ∈ S := hsubS ⟨by simp only [t₀]; linarith, by
    simp only [t₀]; linarith [min_le_right δ' δS]⟩
  have hε := hTpos t₀ ht₀S
  refine ⟨C, eventually_map.mpr ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hε] with w hw
  have hwT : w ∈ T := hT0 t₀ ht₀S hw
  have hgwS := hgS w hwT
  have hgw : p (g w) - p a = w := hgv w hwT
  have hlt : g w < t₀ := by
    by_contra h
    have := hmono.monotoneOn ht₀S hgwS (not_lt.mp h)
    linarith [hw.2]
  have hga : a < g w := hSa hgwS
  have hbd := hb (g w) ⟨hga, hlt.trans_le (by simp only [t₀]; linarith [min_le_left δ' δS])⟩
  rw [hgw] at hbd
  have hw0 : (0 : ℝ) < w := hw.1
  have hφ : 0 < w ^ (((N : ℝ) + lam - μ) / μ - k) := Real.rpow_pos_of_pos hw0 _
  rw [hQk k w hwT, norm_div, Complex.norm_real, Real.norm_of_nonneg hφ.le, div_le_iff₀ hφ]
  exact hbd

/-! ### The substitution -/

section Subst

variable {p p' : ℝ → ℝ} {q : ℝ → ℂ} {S : Set ℝ} {a : ℝ} (hSo : IsOpen S) (hSc : S.OrdConnected)
  (hSa : S ⊆ Ioi a) (hSδ : ∃ δ, 0 < δ ∧ Ioo a (a + δ) ⊆ S) (hps : ContDiffOn ℝ ∞ p S)
  (hd : ∀ t ∈ S, HasDerivAt p (p' t) t) (hpos : ∀ t ∈ S, 0 < p' t)
  (h0 : Tendsto (fun t => p t - p a) (𝓝[>] a) (𝓝 0))

include hSo hSc hd hpos in
theorem strictMonoOn_sub : StrictMonoOn (fun t => p t - p a) S := by
  refine strictMonoOn_of_deriv_pos hSc.convex (fun t ht =>
    (((hd t ht).sub_const (p a)).continuousAt.continuousWithinAt)) fun t ht => ?_
  rw [hSo.interior_eq] at ht
  rw [((hd t ht).sub_const (p a)).deriv]
  exact hpos t ht

include hSc hSδ in
theorem Ioc_subset_of_mem {T : ℝ} (hT : T ∈ S) : Ioc a T ⊆ S := by
  intro t ht
  obtain ⟨δ, hδ, hsubδ⟩ := hSδ
  set s := (a + min t (a + δ)) / 2
  have hs1 : a < s := by
    have := lt_min ht.1 (by linarith : a < a + δ); simp only [s]; linarith
  have hs2 : s ≤ t := by
    have := min_le_left t (a + δ); have := ht.1; simp only [s]; linarith
  have hs3 : s < a + δ := by have := min_le_right t (a + δ); simp only [s]; linarith
  exact hSc.out (hsubδ ⟨hs1, hs3⟩) hT ⟨hs2, ht.2⟩

include hSo hSc hSa hSδ hd hpos h0 in
theorem image_Ioc_sub {T : ℝ} (hT : T ∈ S) :
    (fun t => p t - p a) '' Ioc a T = Ioc 0 (p T - p a) := by
  have hmono := strictMonoOn_sub (a := a) hSo hSc hd hpos
  have hvc : ContinuousOn (fun t => p t - p a) S := fun t ht =>
    ((hd t ht).sub_const (p a)).continuousAt.continuousWithinAt
  have hsub : ∀ t ∈ Ioc a T, t ∈ S := by
    intro t ht
    obtain ⟨δ, hδ, hsubδ⟩ := hSδ
    set s := (a + min t (a + δ)) / 2
    have hs1 : a < s := by
      have := lt_min ht.1 (by linarith : a < a + δ); simp only [s]; linarith
    have hs2 : s ≤ t := by
      have := min_le_left t (a + δ); have := ht.1; simp only [s]; linarith
    have hs3 : s < a + δ := by have := min_le_right t (a + δ); simp only [s]; linarith
    exact hSc.out (hsubδ ⟨hs1, hs3⟩) hT ⟨hs2, ht.2⟩
  ext w
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨range_pos hSa hSδ hmono h0 (hsub t ht), hmono.monotoneOn (hsub t ht) hT ht.2⟩
  · rintro ⟨hw0, hwT⟩
    rcases eq_or_lt_of_le hwT with h | h
    · exact ⟨T, ⟨hSa hT, le_rfl⟩, h.symm⟩
    · obtain ⟨s, hs, hsw⟩ := exists_below hSδ h0 hw0
      obtain ⟨r, hrS, hrw⟩ := mem_image_of_between hSc hvc hmono hs hT hsw h
      refine ⟨r, ⟨hSa hrS, ?_⟩, hrw⟩
      by_contra hr
      exact absurd (hmono hT hrS (not_le.mp hr)) (by rw [hrw]; exact not_lt.mpr h.le)

end Subst

/-! ### The case `p(b) = ∞` -/

theorem norm_cexp_I_mul_real (x y : ℝ) : ‖cexp (I * x * y)‖ = 1 := by
  rw [show I * (x : ℂ) * y = ((x * y : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

/-- **DLMF 2.3.23**, case (d): `p(b) = ∞`. Under (a) `p`, `q` infinitely differentiable on the
range `S = (a, b)` with `p′ > 0`, (b) the expansions 2.3.14 with all their derivatives, and
(d) each `∫ e^{ixp(t)} Pₛ(t) p′(t) dt` converging at `b` uniformly for large `x` (with
`Pₛ = statP`, 2.3.21), the improper integral `∫_a^b e^{ixp(t)} q(t) dt` (`T → b−` is the filter
`upperEnd S`) satisfies
`∼ e^{ixp(a)} ∑ e^{(s+λ)πi/(2μ)} Γ((s+λ)/μ) bₛ x^{−(s+λ)/μ}` with the `bₛ` of §2.3(iii).
DLMF's further condition `P₀(b) = 0` is not needed. -/
theorem dlmf_2_3_23_d {p p' : ℝ → ℝ} {q : ℝ → ℂ} {S : Set ℝ} {a lam μ : ℝ} {ps : ℕ → ℝ}
    {qs : ℕ → ℂ} (hlam : 0 < lam) (hμ : 0 < μ) (hp0 : 0 < ps 0)
    (hSo : IsOpen S) (hSc : S.OrdConnected) (hSa : S ⊆ Ioi a)
    (hSδ : ∃ δ, 0 < δ ∧ Ioo a (a + δ) ⊆ S)
    (hps : ContDiffOn ℝ ∞ p S) (hqs : ContDiffOn ℝ ∞ q S)
    (hd : ∀ t ∈ S, HasDerivAt p (p' t) t) (hpos : ∀ t ∈ S, 0 < p' t)
    (hp : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - k))
      (iteratedDeriv k fun t => p t - p a)
      (fun s t => ps s * (descPochhammer ℝ k).eval ((s : ℝ) + μ) * (t - a) ^ ((s : ℝ) + μ - k)))
    (hq : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)) (iteratedDeriv k q)
      (fun s t => qs s * (((descPochhammer ℝ k).eval ((s : ℝ) + lam - 1) : ℝ) : ℂ) *
        ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)))
    (hpb : Tendsto p (upperEnd S) atTop)
    (hunif : ∀ s, ∃ t₁ ∈ S, ∃ X₀ : ℝ, ∃ G : ℝ → ℂ, TendstoUniformlyOn (fun T (x : ℝ) =>
      ∫ t in t₁..T, cexp (I * x * p t) * statP p' q s t * p' t) G (upperEnd S) (Ici X₀)) :
    IsGenAsympExpansionDLMF atTop
      (fun s (x : ℝ) => cexp (I * x * p a) * ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))
      (fun x : ℝ => limUnder (upperEnd S) fun T => ∫ t in a..T, cexp (I * x * p t) * q t)
      (fun s (x : ℝ) => cexp (I * x * p a) * (cexp ((((s : ℝ) + lam) * Real.pi / (2 * μ) : ℝ) * I) *
        (Real.Gamma (watsonExp lam μ s) : ℂ) * laplaceMethodCoeff ps qs lam μ s *
        ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ))) := by
  set v : ℝ → ℝ := fun t => p t - p a with hvdef
  have hpk0 : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ)) := by
    have h := hp 0
    simp only [Nat.cast_zero, sub_zero, iteratedDeriv_zero, descPochhammer_zero,
      Polynomial.eval_one, mul_one] at h
    exact h
  have h0 : Tendsto v (𝓝[>] a) (𝓝 0) := by
    have h := (laplace_p_tendsto hμ hpk0).sub_const (p a)
    rwa [sub_self] at h
  have hmono := strictMonoOn_sub (a := a) hSo hSc hd hpos
  have hvd : ∀ t ∈ S, HasDerivAt v (p' t) t := fun t ht => (hd t ht).sub_const (p a)
  have hvs : ContDiffOn ℝ ∞ v S := hps.sub contDiffOn_const
  have hvc : ContinuousOn v S := fun t ht => (hvd t ht).continuousAt.continuousWithinAt
  obtain ⟨g, -, hgv, hgw, hgc, hgd⟩ := exists_smooth_inverse hSo hvs hvd hpos hmono
  have hvtop : Tendsto v (upperEnd S) atTop := by
    refine (tendsto_atTop_add_const_right _ (-p a) hpb).congr fun t => ?_
    simp [hvdef, sub_eq_add_neg]
  have hT : v '' S = Ioi 0 := image_eq_Ioi hSo hSc hSa hSδ hvc hmono h0 hvtop
  set Q : ℝ → ℂ := fun w => statP p' q 0 (g w) with hQdef
  have hgS : ∀ w ∈ Ioi (0 : ℝ), g w ∈ S := fun w hw => (hgw w (hT ▸ hw)).1
  have hgvw : ∀ w ∈ Ioi (0 : ℝ), v (g w) = w := fun w hw => (hgw w (hT ▸ hw)).2
  have hgd' : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt g (p' (g w))⁻¹ w := fun w hw => hgd w (hT ▸ hw)
  have hgc' : ContDiffOn ℝ ∞ g (Ioi 0) := hT ▸ hgc
  have hQc : ContDiffOn ℝ ∞ Q (Ioi 0) := contDiffOn_statP_comp hSo hps hd hpos hqs hgS hgc'
  have hQk : ∀ k, ∀ w ∈ Ioi (0 : ℝ), iteratedDeriv k Q w = statP p' q k (g w) :=
    fun k w hw => iteratedDeriv_statP_comp hSo hps hd hpos hqs isOpen_Ioi hgS hgd' k hw
  have hexpQ := statP_comp_expansion (T := Ioi 0) hμ hp0 hSa hSδ hps hqs hd hmono hp hq hgS hgvw
    (fun t ht => range_pos hSa hSδ hmono h0 ht) (fun _ _ => Ioo_subset_Ioi_self) hQk
  have hp'c : ContinuousOn p' S :=
    ((contDiffOn_deriv_of_isOpen hSo hps).congr fun t ht => ((hd t ht).deriv).symm).continuousOn
  have hQkc : ∀ k, ContinuousOn (iteratedDeriv k Q) (Ioi 0) := fun k =>
    continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioi hQc k
  have hgtop : Tendsto g atTop (upperEnd S) := tendsto_upperEnd_iff.mpr fun t ht => by
    filter_upwards [eventually_gt_atTop (v t), eventually_gt_atTop 0] with W hW hW0
    refine ⟨hgS W hW0, ?_⟩
    by_contra h
    have h1 := hmono.monotoneOn (hgS W hW0) ht (not_lt.mp h)
    have h2 := hgvw W hW0
    simp only [hvdef] at h2 hW
    linarith
  -- the substitution on `[t₁, T]`
  have hsubst : ∀ (s : ℕ) (x : ℝ) {t₁ T : ℝ}, t₁ ∈ S → T ∈ S →
      ∫ t in t₁..T, cexp (I * x * p t) * statP p' q s t * p' t =
        cexp (I * x * p a) * ∫ w in v t₁..v T, cexp (I * x * w) * iteratedDeriv s Q w := by
    intro s x t₁ T ht₁ hT
    have hU : uIcc t₁ T ⊆ S := hSc.uIcc_subset ht₁ hT
    rw [← intervalIntegral.integral_deriv_smul_comp' (fun t ht => hvd t (hU ht))
      (hp'c.mono hU), ← intervalIntegral.integral_const_mul]
    · refine intervalIntegral.integral_congr fun t ht => ?_
      simp only [Function.comp_apply]
      have htS := hU ht
      rw [hQk s (v t) (range_pos hSa hSδ hmono h0 htS), hgv t htS, Complex.real_smul,
        show I * (x : ℂ) * p t = I * x * p a + I * x * ((v t : ℝ) : ℂ) by
          simp only [hvdef]; push_cast; ring, Complex.exp_add]
      ring
    · refine ContinuousOn.mul (by fun_prop) ((hQkc s).mono ?_)
      rintro _ ⟨t, ht, rfl⟩
      exact range_pos hSa hSδ hmono h0 (hU ht)
  have hunifQ : ∀ s, ∃ X₀ : ℝ, ∃ G : ℝ → ℂ, TendstoUniformlyOn (fun W (x : ℝ) =>
      ∫ w in (1 : ℝ)..W, cexp (I * x * w) * iteratedDeriv s Q w) G atTop (Ici X₀) := by
    intro s
    obtain ⟨t₁, ht₁, X₀, G, hG⟩ := hunif s
    have hv1 : 0 < v t₁ := range_pos hSa hSδ hmono h0 ht₁
    refine ⟨X₀, fun x => (∫ w in (1 : ℝ)..v t₁, cexp (I * x * w) * iteratedDeriv s Q w) +
      cexp (-(I * x * p a)) * G x, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff] at hG ⊢
    intro ε hε
    filter_upwards [hgtop.eventually (hG ε hε), eventually_gt_atTop 0] with W hW hW0 x hx
    have hWS := hgS W hW0
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_mul_of_contDiffOn hQc s x one_pos hv1)
      (intervalIntegrable_exp_mul_of_contDiffOn hQc s x hv1 hW0)
    have e2 := hsubst s x ht₁ hWS
    rw [hgvw W hW0] at e2
    rw [← e1, dist_add_left, dist_eq_norm]
    have hc : cexp (-(I * x * p a)) * cexp (I * x * p a) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have : ∫ w in v t₁..W, cexp (I * x * w) * iteratedDeriv s Q w =
        cexp (-(I * x * p a)) * ∫ t in t₁..g W, cexp (I * x * p t) * statP p' q s t * p' t := by
      rw [e2, ← mul_assoc, hc, one_mul]
    rw [this, ← mul_sub, norm_mul, show -(I * (x : ℂ) * p a) = ((-(x * p a) : ℝ) : ℂ) * I by
      push_cast; ring, norm_exp_ofReal_mul_I, one_mul, ← dist_eq_norm]
    exact hW x hx
  have h20 := dlmf_2_3_20 hlam hμ hQc hexpQ hunifQ
  -- the improper integral in `t` is `e^{ixp(a)}` times the one in `v`
  obtain ⟨X₀, G₀, hG₀⟩ := hunifQ 0
  obtain ⟨b₀, C₀, hb₀, -, h₀⟩ := exists_bound_of_isBigODLMF_nhdsGT ((hexpQ 0).2 0)
    (fun w hw => ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hw _).ne') zero_lt_one
  have hQ0 : ∀ w ∈ Ioc 0 b₀, ‖Q w‖ ≤ C₀ * w ^ ((((0 : ℕ) : ℝ) + lam - μ) / μ - ((0 : ℕ) : ℝ)) :=
    fun w hw => by
      have h := h₀ w hw
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, iteratedDeriv_zero,
        Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hw.1.le _)] at h
      simpa using h
  have hQint : ∀ x : ℝ, ∀ W, 0 ≤ W →
      IntervalIntegrable (fun w => cexp (I * x * w) * Q w) volume 0 W := fun x W hW =>
    intervalIntegrable_exp_mul_of_bound hQc.continuousOn hb₀ (by
      have := watsonExp_pos hlam hμ 0
      simp only [watsonExp] at this
      have : (((0 : ℕ) : ℝ) + lam - μ) / μ = (((0 : ℕ) : ℝ) + lam) / μ - 1 := by field_simp
      push_cast at *; linarith) hQ0 x hW
  have hne : S.Nonempty := by
    obtain ⟨δ, hδ, hsub⟩ := hSδ
    exact ⟨a + δ / 2, hsub ⟨by linarith, by linarith⟩⟩
  have := upperEnd_neBot hSo hne
  obtain ⟨t₀, ht₀⟩ := hne
  have hlimI : ∀ x : ℝ, X₀ ≤ x → (limUnder (upperEnd S) fun T => ∫ t in a..T,
      cexp (I * x * p t) * q t) = cexp (I * x * p a) * fourierIoiIntegral Q 0 x := by
    intro x hx
    have hQlim : Tendsto (fun W => ∫ w in (0 : ℝ)..W, cexp (I * x * w) * Q w) atTop
        (𝓝 ((∫ w in (0 : ℝ)..1, cexp (I * x * w) * Q w) + G₀ x)) := by
      refine ((hG₀.tendsto_at (show x ∈ Ici X₀ from hx)).const_add _).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with W hW
      have h1W := intervalIntegrable_exp_mul_of_contDiffOn hQc 0 x one_pos
        (by linarith : (0 : ℝ) < W)
      simp only [iteratedDeriv_zero] at h1W ⊢
      rw [intervalIntegral.integral_add_adjacent_intervals (hQint x 1 zero_le_one) h1W]
    have hIeq : ∀ T ∈ S, ∫ t in a..T, cexp (I * x * p t) * q t =
        cexp (I * x * p a) * ∫ w in (0 : ℝ)..v T, cexp (I * x * w) * Q w := by
      intro T hT
      have hsub := Ioc_subset_of_mem hSc hSδ hT
      have hvT := range_pos hSa hSδ hmono h0 hT
      rw [intervalIntegral.integral_of_le (le_of_lt (hSa hT)),
        intervalIntegral.integral_of_le hvT.le, ← image_Ioc_sub hSo hSc hSa hSδ hd hpos h0 hT,
        integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc
          (fun t ht => (hvd t (hsub ht)).hasDerivWithinAt)
          (hmono.injOn.mono hsub), ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have htS := hsub ht
      have hp't : (p' t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos t htS).ne'
      simp only [hQdef, statP]
      rw [hgv t htS, abs_of_pos (hpos t htS), Complex.real_smul,
        show I * (x : ℂ) * p t = I * x * p a + I * x * ((v t : ℝ) : ℂ) by
          simp only [hvdef]; push_cast; ring, Complex.exp_add]
      field_simp
    have hIlim : Tendsto (fun T => ∫ t in a..T, cexp (I * x * p t) * q t) (upperEnd S)
        (𝓝 (cexp (I * x * p a) * ((∫ w in (0 : ℝ)..1, cexp (I * x * w) * Q w) + G₀ x))) := by
      refine ((hQlim.comp hvtop).const_mul _).congr' ?_
      filter_upwards [tendsto_upperEnd_iff.mp tendsto_id t₀ ht₀] with T hT
      exact (hIeq T hT.1).symm
    rw [hIlim.limUnder_eq, hQlim.limUnder_eq.symm]
    rfl
  refine ⟨?_, fun n => ?_⟩
  · have h := isAsympScale_rpow_neg_mul (one_div_pos.mpr hμ) (watsonExp_succ (lam := lam) hμ)
      (w := fun x : ℝ => cexp (I * x * p a)) (Eventually.of_forall fun x => Complex.exp_ne_zero _)
    simpa only [mul_comm] using h
  · obtain ⟨C, hC⟩ := h20.2 n
    rw [eventually_map] at hC
    refine ⟨C, eventually_map.mpr ?_⟩
    filter_upwards [hC, eventually_ge_atTop X₀] with x hx hxX
    rw [hlimI x hxX, ← Finset.mul_sum, ← mul_sub,
      mul_div_mul_left _ _ (Complex.exp_ne_zero _)]
    exact hx

/-! ### The endpoint `b` when `p(b)` is finite -/

section Endpoint

variable {G : ℕ → ℝ → ℂ} {α β : ℝ} (hαβ : α < β) (hc : ∀ j, ContinuousOn (G j) (Icc α β))
  (hd : ∀ j, ∀ w ∈ Ioo α β, HasDerivAt (G j) (G (j + 1) w) w) (h0 : ∀ j, G j α = 0)
include hαβ hc hd h0

theorem fourier_endpoint_step (j : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ w in α..β, cexp (I * x * w) * G j w =
      -(I / x) * (cexp (I * x * β) * G j β) +
        (I / x) * ∫ w in α..β, cexp (I * x * w) * G (j + 1) w := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hU : uIcc α β = Icc α β := uIcc_of_le hαβ.le
  have hv : ∀ w : ℝ, HasDerivAt (fun w : ℝ => cexp (I * x * w) / (I * x)) (cexp (I * x * w)) w :=
    fun w => by
      have h := ((hasDerivAt_id (w : ℂ)).const_mul (I * (x : ℂ))).cexp.comp_ofReal.div_const
        (I * (x : ℂ))
      convert h using 1
      · ext; simp
      · simp only [id]; field_simp
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := G j) (v := fun w : ℝ => cexp (I * x * w) / (I * x)) (u' := G (j + 1))
    (v' := fun w : ℝ => cexp (I * x * w)) (by rw [hU]; exact hc j)
    (by fun_prop) (fun w hw => by
      rw [min_eq_left hαβ.le, max_eq_right hαβ.le] at hw
      exact (hd j w hw).hasDerivWithinAt)
    (fun w _ => (hv w).hasDerivWithinAt)
    ((hc (j + 1)).intervalIntegrable_of_Icc hαβ.le)
    ((by fun_prop : Continuous fun w : ℝ => cexp (I * x * w)).intervalIntegrable _ _)
  have e1 : ∫ w in α..β, cexp (I * x * w) * G j w = ∫ w in α..β, G j w * cexp (I * x * w) := by
    simp_rw [mul_comm (cexp _)]
  have e2 : ∫ w in α..β, G (j + 1) w * (cexp (I * x * w) / (I * x)) =
      (1 / (I * x)) * ∫ w in α..β, cexp (I * x * w) * G (j + 1) w := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext w; ring
  rw [e1, key, e2, h0 j, zero_mul, sub_zero]
  have hI : I / (x : ℂ) = -(1 / (I * x)) := by field_simp; rw [I_sq]
  rw [hI]
  ring

theorem fourier_endpoint_iter (M : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ w in α..β, cexp (I * x * w) * G 0 w =
      -(cexp (I * x * β) * ∑ j ∈ Finset.range M, G j β * (I / x) ^ (j + 1)) +
        (I / x) ^ M * ∫ w in α..β, cexp (I * x * w) * G M w := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, fourier_endpoint_step hαβ hc hd h0 M hx, Finset.sum_range_succ]
    ring

end Endpoint

/-! ### The case `p(b)` finite (2.3.23) -/

/-- **DLMF 2.3.23**: if `p(b) = lim_{t→b−} p(t)` is finite and (c) each `Pₛ(t)` (2.3.21) has a
limit `Pₛ(b)` as `t → b−`, then under (a), (b) both endpoints contribute:
`∫_a^b e^{ixp(t)} q(t) dt ∼ e^{ixp(a)} ∑ e^{(s+λ)πi/(2μ)} Γ((s+λ)/μ) bₛ x^{−(s+λ)/μ}
  − e^{ixp(b)} ∑ Pₛ(b) (i/x)^{s+1}`, in the sense that the error after `N` and `M` terms is
`O(x^{−(N+λ)/μ} + x^{−(M+1)})`. -/
theorem dlmf_2_3_23 {p p' : ℝ → ℝ} {q : ℝ → ℂ} {S : Set ℝ} {a lam μ : ℝ} {ps : ℕ → ℝ}
    {qs : ℕ → ℂ} (hlam : 0 < lam) (hμ : 0 < μ) (hp0 : 0 < ps 0)
    (hSo : IsOpen S) (hSc : S.OrdConnected) (hSa : S ⊆ Ioi a)
    (hSδ : ∃ δ, 0 < δ ∧ Ioo a (a + δ) ⊆ S)
    (hps : ContDiffOn ℝ ∞ p S) (hqs : ContDiffOn ℝ ∞ q S)
    (hd : ∀ t ∈ S, HasDerivAt p (p' t) t) (hpos : ∀ t ∈ S, 0 < p' t)
    (hp : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - k))
      (iteratedDeriv k fun t => p t - p a)
      (fun s t => ps s * (descPochhammer ℝ k).eval ((s : ℝ) + μ) * (t - a) ^ ((s : ℝ) + μ - k)))
    (hq : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)) (iteratedDeriv k q)
      (fun s t => qs s * (((descPochhammer ℝ k).eval ((s : ℝ) + lam - 1) : ℝ) : ℂ) *
        ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)))
    {pb : ℝ} {Pb : ℕ → ℂ} (hpb : Tendsto p (upperEnd S) (𝓝 pb))
    (hPb : ∀ s, Tendsto (statP p' q s) (upperEnd S) (𝓝 (Pb s))) (N M : ℕ) :
    ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
      ‖(∫ t in S, cexp (I * x * p t) * q t) -
          cexp (I * x * p a) * ∑ s ∈ Finset.range N,
            cexp ((((s : ℝ) + lam) * Real.pi / (2 * μ) : ℝ) * I) *
              (Real.Gamma (watsonExp lam μ s) : ℂ) * laplaceMethodCoeff ps qs lam μ s *
              ((x ^ (-watsonExp lam μ s) : ℝ) : ℂ) +
          cexp (I * x * pb) * ∑ s ∈ Finset.range M, Pb s * (I / x) ^ (s + 1)‖ ≤
        C * (x ^ (-watsonExp lam μ N) + x ^ (-((M : ℝ) + 1))) := by
  set v : ℝ → ℝ := fun t => p t - p a with hvdef
  have hpk0 : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ)) := by
    have h := hp 0
    simp only [Nat.cast_zero, sub_zero, iteratedDeriv_zero, descPochhammer_zero,
      Polynomial.eval_one, mul_one] at h
    exact h
  have h0 : Tendsto v (𝓝[>] a) (𝓝 0) := by
    have h := (laplace_p_tendsto hμ hpk0).sub_const (p a)
    rwa [sub_self] at h
  have hmono := strictMonoOn_sub (a := a) hSo hSc hd hpos
  have hvd : ∀ t ∈ S, HasDerivAt v (p' t) t := fun t ht => (hd t ht).sub_const (p a)
  have hvs : ContDiffOn ℝ ∞ v S := hps.sub contDiffOn_const
  have hvc : ContinuousOn v S := fun t ht => (hvd t ht).continuousAt.continuousWithinAt
  obtain ⟨g, -, hgv, hgw, hgc, hgd⟩ := exists_smooth_inverse hSo hvs hvd hpos hmono
  set V := pb - p a with hVdef
  have hvV : Tendsto v (upperEnd S) (𝓝 V) := hpb.sub_const (p a)
  have hT : v '' S = Ioo 0 V := image_eq_Ioo hSo hSc hSa hSδ hvc hmono h0 hvV
  have hne : S.Nonempty := by
    obtain ⟨δ, hδ, hsub⟩ := hSδ
    exact ⟨a + δ / 2, hsub ⟨by linarith, by linarith⟩⟩
  have hNeBot := upperEnd_neBot hSo hne
  obtain ⟨t₀, ht₀⟩ := hne
  have hV : 0 < V := by
    have h := (show v t₀ ∈ Ioo 0 V by rw [← hT]; exact ⟨t₀, ht₀, rfl⟩)
    exact h.1.trans h.2
  set Q : ℝ → ℂ := fun w => statP p' q 0 (g w) with hQdef
  have hgS : ∀ w ∈ Ioo 0 V, g w ∈ S := fun w hw => (hgw w (hT ▸ hw)).1
  have hgvw : ∀ w ∈ Ioo 0 V, v (g w) = w := fun w hw => (hgw w (hT ▸ hw)).2
  have hgd' : ∀ w ∈ Ioo 0 V, HasDerivAt g (p' (g w))⁻¹ w := fun w hw => hgd w (hT ▸ hw)
  have hgc' : ContDiffOn ℝ ∞ g (Ioo 0 V) := hT ▸ hgc
  have hQc : ContDiffOn ℝ ∞ Q (Ioo 0 V) := contDiffOn_statP_comp hSo hps hd hpos hqs hgS hgc'
  have hQk : ∀ k, ∀ w ∈ Ioo 0 V, iteratedDeriv k Q w = statP p' q k (g w) :=
    fun k w hw => iteratedDeriv_statP_comp hSo hps hd hpos hqs isOpen_Ioo hgS hgd' k hw
  have hvltV : ∀ t ∈ S, v t < V := fun t ht => by
    have h := (show v t ∈ Ioo 0 V by rw [← hT]; exact ⟨t, ht, rfl⟩)
    exact h.2
  have hexpQ := statP_comp_expansion (T := Ioo 0 V) hμ hp0 hSa hSδ hps hqs hd hmono hp hq hgS
    hgvw (fun t ht => range_pos hSa hSδ hmono h0 ht)
    (fun t ht => Ioo_subset_Ioo_right (hvltV t ht).le) hQk
  -- limits at `V−`
  have hgV : Tendsto g (𝓝[<] V) (upperEnd S) := tendsto_upperEnd_iff.mpr fun t ht => by
    filter_upwards [Ioo_mem_nhdsLT (hvltV t ht)] with w hw
    have hw' : w ∈ Ioo 0 V := ⟨(range_pos hSa hSδ hmono h0 ht).trans hw.1, hw.2⟩
    refine ⟨hgS w hw', ?_⟩
    by_contra h
    have h1 := hmono.monotoneOn (hgS w hw') ht (not_lt.mp h)
    have h2 := hgvw w hw'
    simp only [hvdef] at h1 h2 hw
    linarith [hw.1]
  have hQlim : ∀ k, Tendsto (iteratedDeriv k Q) (𝓝[<] V) (𝓝 (Pb k)) := fun k => by
    refine ((hPb k).comp hgV).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hV] with w hw
    exact (hQk k w hw).symm
  -- the cutoff in `v`
  set κ : ℝ → ℝ := fun w => spCutoff (3 * w / V) with hκdef
  have hκc : ContDiff ℝ ∞ κ := spCutoff_contDiff.comp (by fun_prop)
  have hκ1 : ∀ w, w ≤ V / 3 → κ w = 1 := fun w hw => spCutoff_eq_one (by
    rw [div_le_one hV]; linarith)
  have hκ0 : ∀ w, 2 * V / 3 ≤ w → κ w = 0 := fun w hw => spCutoff_eq_zero (by
    rw [le_div_iff₀ hV]; linarith)
  set Qn : ℝ → ℂ := fun w => Q w * (κ w : ℂ) with hQndef
  set Qf : ℝ → ℂ := fun w => Q w * ((1 - κ w : ℝ) : ℂ) with hQfdef
  have hκC : ContDiff ℝ ∞ fun w => (κ w : ℂ) := ofRealCLM.contDiff.comp hκc
  have hκC' : ContDiff ℝ ∞ fun w => ((1 - κ w : ℝ) : ℂ) :=
    ofRealCLM.contDiff.comp (contDiff_const.sub hκc)
  have hQnc : ContDiffOn ℝ ∞ Qn (Ioi 0) := by
    refine contDiffOn_of_locally_contDiffOn fun w hw => ?_
    rcases lt_or_ge w V with h | h
    · exact ⟨Ioo 0 V, isOpen_Ioo, ⟨hw, h⟩, (hQc.mul hκC.contDiffOn).mono inter_subset_right⟩
    · refine ⟨Ioi (2 * V / 3), isOpen_Ioi, by simp only [mem_Ioi]; linarith, ?_⟩
      refine contDiffOn_const (c := (0 : ℂ)).congr fun u hu => ?_
      simp [hQndef, hκ0 u (le_of_lt hu.2)]
  have hQfc : ContDiffOn ℝ ∞ Qf (Ioo 0 V) := hQc.mul hκC'.contDiffOn
  have hQnQ : ∀ k, iteratedDeriv k Qn =ᶠ[𝓝[>] 0] iteratedDeriv k Q := fun k => by
    filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < V / 3)] with w hw
    refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
    filter_upwards [Iio_mem_nhds hw.2] with u hu
    simp [hQndef, hκ1 u (le_of_lt hu)]
  have hexpQn : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun s w => ((w ^ (((s : ℝ) + lam - μ) / μ - k) : ℝ) : ℂ)) (iteratedDeriv k Qn)
      (fun s w => laplaceMethodCoeff ps qs lam μ s *
        (((descPochhammer ℝ k).eval (((s : ℝ) + lam - μ) / μ) : ℝ) : ℂ) *
        ((w ^ (((s : ℝ) + lam - μ) / μ - k) : ℝ) : ℂ)) := fun k =>
    (hexpQ k).congr' (fun _ => EventuallyEq.rfl) (hQnQ k).symm (fun _ => EventuallyEq.rfl)
  have hQnzero : ∀ k w, 2 * V / 3 < w → iteratedDeriv k Qn w = 0 := fun k w hw => by
    have h : Qn =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hw] with u hu
      simp [hQndef, hκ0 u (le_of_lt hu)]
    rw [h.iteratedDeriv_eq]
    rcases k with _ | k
    · simp
    · simp
  have hunifQn : ∀ s, ∃ X₀ : ℝ, ∃ G : ℝ → ℂ, TendstoUniformlyOn (fun W (x : ℝ) =>
      ∫ w in (1 : ℝ)..W, cexp (I * x * w) * iteratedDeriv s Qn w) G atTop (Ici X₀) := by
    intro s
    refine ⟨0, fun x => ∫ w in (1 : ℝ)..max 1 V, cexp (I * x * w) * iteratedDeriv s Qn w, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [eventually_ge_atTop (max 1 V)] with W hW x _
    have hz : ∫ w in max 1 V..W, cexp (I * x * w) * iteratedDeriv s Qn w = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun w hw => by
        rw [uIcc_of_le hW] at hw
        simp only
        rw [hQnzero s w (by linarith [hw.1, le_max_right 1 V]), mul_zero]]
      simp
    have hm : (0 : ℝ) < max 1 V := lt_max_of_lt_left one_pos
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_mul_of_contDiffOn hQnc s x (u := 1) (v := max 1 V) one_pos hm)
      (intervalIntegrable_exp_mul_of_contDiffOn hQnc s x (u := max 1 V) (v := W) hm
        (by linarith [le_max_left 1 V])), hz, add_zero, dist_self]
    exact hε
  have h20 := dlmf_2_3_20 hlam hμ hQnc hexpQn hunifQn
  -- the far part near `V`
  set Gf : ℕ → ℝ → ℂ := fun j w => if w < V then iteratedDeriv j Qf w else Pb j with hGfdef
  have hQfd : ∀ j, ∀ w ∈ Ioo 0 V,
      HasDerivAt (iteratedDeriv j Qf) (iteratedDeriv (j + 1) Qf w) w := fun j w hw =>
    hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioo hQfc j hw
  have hQfQ : ∀ j w, 2 * V / 3 < w → iteratedDeriv j Qf w = iteratedDeriv j Q w := fun j w hw =>
    Filter.EventuallyEq.iteratedDeriv_eq j (by
      filter_upwards [Ioi_mem_nhds hw] with u hu
      simp [hQfdef, hκ0 u (le_of_lt hu)])
  have hQf0 : ∀ j w, w < V / 3 → iteratedDeriv j Qf w = 0 := fun j w hw => by
    have h : Qf =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hw] with u hu
      simp [hQfdef, hκ1 u (le_of_lt hu)]
    rw [h.iteratedDeriv_eq]
    rcases j with _ | j
    · simp
    · simp
  have hGfeq : ∀ j, ∀ w < V, Gf j =ᶠ[𝓝 w] iteratedDeriv j Qf := fun j w hw => by
    filter_upwards [Iio_mem_nhds hw] with u hu
    have huV : u < V := hu
    simp only [hGfdef, huV, ↓reduceIte]
  have hGc : ∀ j, ContinuousOn (Gf j) (Icc (V / 3) V) := by
    intro j w hw
    rcases eq_or_lt_of_le hw.2 with h | h
    · rw [h]
      have hlim : Tendsto (Gf j) (𝓝[<] V) (𝓝 (Gf j V)) := by
        have hGw : Gf j V = Pb j := by simp [hGfdef]
        rw [hGw]
        refine (hQlim j).congr' ?_
        filter_upwards [Ioo_mem_nhdsLT (by linarith : 2 * V / 3 < V)] with u hu
        simp only [hGfdef, hu.2, ↓reduceIte]
        exact (hQfQ j u hu.1).symm
      exact (continuousWithinAt_Iio_iff_Iic.mp hlim).mono fun u hu => hu.2
    · have hw0 : 0 < w := by linarith [hw.1]
      exact ((hQfd j w ⟨hw0, h⟩).continuousAt.congr (hGfeq j w h).symm).continuousWithinAt
  have hGd : ∀ j, ∀ w ∈ Ioo (V / 3) V, HasDerivAt (Gf j) (Gf (j + 1) w) w := by
    intro j w hw
    have hw0 : 0 < w := by linarith [hw.1]
    have h := (hQfd j w ⟨hw0, hw.2⟩).congr_of_eventuallyEq (hGfeq j w hw.2)
    simpa [hGfdef, hw.2] using h
  have hG0 : ∀ j, Gf j (V / 3) = 0 := by
    intro j
    have hlt : V / 3 < V := by linarith
    simp only [hGfdef, hlt, ↓reduceIte]
    have hc := (hQfd j (V / 3) ⟨by positivity, hlt⟩).continuousAt
    refine tendsto_nhds_unique (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (V / 3))))
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hQf0 j u hu).symm
  set B := ∫ w in V / 3..V, ‖Gf (M + 1) w‖
  -- integrability and the bound near `0`
  obtain ⟨b₀, C₀, hb₀, -, h₀⟩ := exists_bound_of_isBigODLMF_nhdsGT ((hexpQn 0).2 0)
    (fun w hw => ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hw _).ne') zero_lt_one
  have hQn0 : ∀ w ∈ Ioc 0 b₀,
      ‖Qn w‖ ≤ C₀ * w ^ ((((0 : ℕ) : ℝ) + lam - μ) / μ - ((0 : ℕ) : ℝ)) := fun w hw => by
    have h := h₀ w hw
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, iteratedDeriv_zero,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hw.1.le _)] at h
    simpa using h
  have hQnint : ∀ x : ℝ, ∀ W, 0 ≤ W →
      IntervalIntegrable (fun w => cexp (I * x * w) * Qn w) volume 0 W := fun x W hW =>
    intervalIntegrable_exp_mul_of_bound hQnc.continuousOn hb₀ (by
      have := watsonExp_pos hlam hμ 0
      simp only [watsonExp] at this
      have : (((0 : ℕ) : ℝ) + lam - μ) / μ = (((0 : ℕ) : ℝ) + lam) / μ - 1 := by field_simp
      push_cast at *; linarith) hQn0 x hW
  -- the integral over `S` in the variable `v`
  have hIS : ∀ x : ℝ, ∫ t in S, cexp (I * x * p t) * q t =
      cexp (I * x * p a) * ((∫ w in (0 : ℝ)..V, cexp (I * x * w) * Qn w) +
        ∫ w in V / 3..V, cexp (I * x * w) * Gf 0 w) := by
    intro x
    have h1 : ∫ t in S, cexp (I * x * p t) * q t =
        cexp (I * x * p a) * ∫ w in Ioo 0 V, cexp (I * x * w) * Q w := by
      rw [← hT, integral_image_eq_integral_abs_deriv_smul hSo.measurableSet
        (fun t ht => (hvd t ht).hasDerivWithinAt) hmono.injOn, ← integral_const_mul]
      refine setIntegral_congr_fun hSo.measurableSet fun t ht => ?_
      have hp't : (p' t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hpos t ht).ne'
      simp only [hQdef, statP]
      rw [hgv t ht, abs_of_pos (hpos t ht), Complex.real_smul,
        show I * (x : ℂ) * p t = I * x * p a + I * x * ((v t : ℝ) : ℂ) by
          simp only [hvdef]; push_cast; ring, Complex.exp_add]
      field_simp
    have hGint : IntervalIntegrable (fun w : ℝ => cexp (I * x * w) * Gf 0 w) volume (V / 3) V :=
      ContinuousOn.intervalIntegrable_of_Icc (by linarith) ((by fun_prop :
        Continuous fun w : ℝ => cexp (I * x * w)).continuousOn.mul (hGc 0))
    have hQfint : IntegrableOn (fun w : ℝ => cexp (I * x * w) * Qf w) (Ioo 0 V) := by
      rw [← Ioc_union_Ioo_eq_Ioo (by linarith : (0 : ℝ) ≤ V / 3) (by linarith : V / 3 < V)]
      refine IntegrableOn.union ?_ ?_
      · refine (integrableOn_zero).congr_fun (fun w hw => ?_) measurableSet_Ioc
        simp [hQfdef, hκ1 w hw.2]
      · have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp hGint
        refine h.congr_fun (fun w hw => ?_) measurableSet_Ioo
        simp [hGfdef, hw.2]
    have hQnint' : IntegrableOn (fun w : ℝ => cexp (I * x * w) * Qn w) (Ioo 0 V) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hV.le).mp (hQnint x V hV.le)
    rw [h1]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun w : ℝ => cexp (I * x * w) * Qn w +
      cexp (I * x * w) * Qf w) (fun w _ => by
        simp only [hQndef, hQfdef]; push_cast; ring), integral_add hQnint' hQfint,
      intervalIntegral.integral_of_le hV.le, integral_Ioc_eq_integral_Ioo]
    congr 1
    rw [← Ioc_union_Ioo_eq_Ioo (by linarith : (0 : ℝ) ≤ V / 3) (by linarith : V / 3 < V),
      setIntegral_union (disjoint_left.mpr fun w h1 h2 => not_lt.mpr h1.2 h2.1 :
        Disjoint (Ioc (0 : ℝ) (V / 3)) (Ioo (V / 3) V)) measurableSet_Ioo
        (hQfint.mono_set (Ioc_subset_Ioo_right (by linarith)))
        (hQfint.mono_set (Ioo_subset_Ioo_left (by linarith))),
      intervalIntegral.integral_of_le (by linarith),
      integral_Ioc_eq_integral_Ioo (x := V / 3) (y := V)]
    have hz : ∫ w in Ioc 0 (V / 3), cexp (I * x * w) * Qf w = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℂ)) fun w hw => by
        simp [hQfdef, hκ1 w hw.2]]
      simp
    rw [hz, zero_add]
    refine setIntegral_congr_fun measurableSet_Ioo fun w hw => ?_
    simp [hGfdef, hw.2]
  -- the Fourier integral of `Qn`
  have hFn : ∀ x : ℝ, fourierIoiIntegral Qn 0 x = ∫ w in (0 : ℝ)..V, cexp (I * x * w) * Qn w := by
    intro x
    refine (tendsto_const_nhds.congr' ?_).limUnder_eq
    filter_upwards [eventually_ge_atTop V] with W hW
    have hVW := intervalIntegrable_exp_mul_of_contDiffOn hQnc 0 x (u := V) (v := W) hV
      (hV.trans_le hW)
    simp only [iteratedDeriv_zero] at hVW
    rw [← intervalIntegral.integral_add_adjacent_intervals (hQnint x V hV.le) hVW]
    have hz : ∫ w in V..W, cexp (I * x * w) * Qn w = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun w hw => by
        rw [uIcc_of_le hW] at hw
        have := hQnzero 0 w (by linarith [hw.1])
        simp only [iteratedDeriv_zero] at this
        simp [this]]
      simp
    rw [hz, add_zero]
  -- the error estimate
  obtain ⟨C₁, hC₁⟩ := h20.2 N
  rw [eventually_map] at hC₁
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hC₁
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _
  refine ⟨|C₁| + ‖Pb M‖ + B, max X₁ 1, fun x hx => ?_⟩
  have hxX : X₁ ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hb := hX₁ x hxX
  set α := watsonExp lam μ
  have hpN : 0 < x ^ (-α N) := Real.rpow_pos_of_pos hx0 _
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpN.le, div_le_iff₀ hpN] at hb
  have hiter := fourier_endpoint_iter (G := Gf) (by linarith : V / 3 < V) hGc hGd hG0 (M + 1) hx0
  have hGV : ∀ j, Gf j V = Pb j := fun j => by simp [hGfdef]
  set Fn := fourierIoiIntegral Qn 0 x
  set Tn := ∑ s ∈ Finset.range N, cexp ((((s : ℝ) + lam) * Real.pi / (2 * μ) : ℝ) * I) *
    (Real.Gamma (α s) : ℂ) * laplaceMethodCoeff ps qs lam μ s * ((x ^ (-α s) : ℝ) : ℂ)
  set J := ∫ w in V / 3..V, cexp (I * x * w) * Gf (M + 1) w
  set PM := ∑ s ∈ Finset.range M, Pb s * (I / (x : ℂ)) ^ (s + 1)
  have hsumM : ∑ j ∈ Finset.range (M + 1), Gf j V * (I / (x : ℂ)) ^ (j + 1) =
      PM + Pb M * (I / x) ^ (M + 1) := by
    rw [Finset.sum_range_succ, hGV]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hGV]
  have hpb' : cexp (I * x * pb) = cexp (I * x * p a) * cexp (I * x * V) := by
    rw [← Complex.exp_add]; congr 1; simp only [hVdef]; push_cast; ring
  have hE : (∫ t in S, cexp (I * x * p t) * q t) - cexp (I * x * p a) * Tn +
      cexp (I * x * pb) * PM = cexp (I * x * p a) * ((Fn - Tn) -
        cexp (I * x * V) * (Pb M * (I / x) ^ (M + 1)) + (I / x) ^ (M + 1) * J) := by
    rw [hIS x, ← hFn x, hiter, hsumM, hpb']
    ring
  have hIx : ‖(I / (x : ℂ)) ^ (M + 1)‖ = x ^ (-((M : ℝ) + 1)) := by
    rw [norm_pow, norm_div, norm_I, Complex.norm_real, Real.norm_of_nonneg hx0.le,
      Real.rpow_neg hx0.le, show ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, one_div_pow, one_div]
  have hJ : ‖J‖ ≤ B := norm_integral_exp_mul_le (by linarith)
  rw [hE, norm_mul, norm_cexp_I_mul_real, one_mul]
  have hpM : 0 ≤ x ^ (-((M : ℝ) + 1)) := Real.rpow_nonneg hx0.le _
  calc _ ≤ ‖Fn - Tn‖ + ‖cexp (I * x * V) * (Pb M * (I / x) ^ (M + 1))‖ +
        ‖(I / (x : ℂ)) ^ (M + 1) * J‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C₁ * x ^ (-α N) + ‖Pb M‖ * x ^ (-((M : ℝ) + 1)) + x ^ (-((M : ℝ) + 1)) * B := by
        rw [norm_mul, norm_cexp_I_mul_real, one_mul, norm_mul, hIx, norm_mul, hIx]
        gcongr
    _ ≤ _ := by
        have hC : C₁ * x ^ (-α N) ≤ |C₁| * x ^ (-α N) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hpN.le
        have hpN' := hpN.le
        nlinarith [abs_nonneg C₁, norm_nonneg (Pb M)]

end Azurite.DLMF
