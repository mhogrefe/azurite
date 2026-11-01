/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3LaplaceCoeff

/-!
# DLMF §2.3(iv): differentiable asymptotic expansions at an endpoint

* `DExp a J F c S`: `F` and its first `J` derivatives have the expansions
  `F⁽ʲ⁾(t) ∼ (t − a)^{c−j} S⁽ʲ⁾(t − a)` (`S⁽ʲ⁺¹⁾ = lopPS (c − j) S⁽ʲ⁾`, `lopPS c S = cS + XS′`).
  Closed under sums, products, inverses, real powers of positive functions and re-indexing
  (`DExp.add`, `.mul`, `.inv`, `.rpow_real`, `.reindex`), and obtained from DLMF's
  "infinitely differentiable" expansions (`dexp_of_isGen`, `dexp_ofReal_of_isGen`).
* `statP` (**2.3.21**): `Pₛ = ((1/p′) d/dt)ˢ (q/p′)`; `DExp.dop` for the operator `(1/p′) d/dt`.
* `statP_sub_bound`: the differentiated form of 2.3.16,
  `Pₖ(t) − ∑_{s<N} bₛ (d/dv)ᵏ v^{(s+λ−μ)/μ} = O(v^{(N+λ−μ)/μ − k})` as `t → a+`. The proof
  applies `(1/p′) d/dt` `k` times to the remainder of 2.3.16 and uses that the first `N`
  coefficients of its expansion vanish (`coeff_eq_zero_of_isBigO`).
-/

open Set Filter Topology Asymptotics PowerSeries
open scoped ContDiff

namespace Azurite.DLMF

/-- The formal operator `S ↦ cS + XS′`, i.e. `(t − a)^{1−c} d/dt [(t − a)^c S(t − a)]`. -/
noncomputable def lopPS (c : ℝ) (S : ℂ⟦X⟧) : ℂ⟦X⟧ := C (c : ℂ) * S + X * d⁄dX S

/-- `F` has, together with its first `J` derivatives, the expansions
`F⁽ʲ⁾(t) ∼ (t − a)^{c−j} S⁽ʲ⁾(t − a)` as `t → a+`, where `S⁽ʲ⁺¹⁾ = lopPS (c − j) S⁽ʲ⁾`. -/
def DExp (a : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ⟦X⟧ → Prop
  | 0, F, c, S => HasPowExpansion (𝓝[>] a) (fun t => ((t - a : ℝ) : ℂ))
      (fun t => F t / (((t - a) ^ c : ℝ) : ℂ)) S
  | J + 1, F, c, S => DExp a 0 F c S ∧ (∀ᶠ t in 𝓝[>] a, DifferentiableAt ℝ F t) ∧
      DExp a J (deriv F) (c - 1) (lopPS c S)

variable {a : ℝ}

theorem dexp_zero_iff {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} :
    DExp a 0 F c S ↔ HasPowExpansion (𝓝[>] a) (fun t => ((t - a : ℝ) : ℂ))
      (fun t => F t / (((t - a) ^ c : ℝ) : ℂ)) S := by simp only [DExp]

theorem dexp_succ_iff {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} :
    DExp a (J + 1) F c S ↔ DExp a 0 F c S ∧ (∀ᶠ t in 𝓝[>] a, DifferentiableAt ℝ F t) ∧
      DExp a J (deriv F) (c - 1) (lopPS c S) := by simp only [DExp]

theorem tendsto_ofReal_sub_nhdsGT (a : ℝ) :
    Tendsto (fun t : ℝ => ((t - a : ℝ) : ℂ)) (𝓝[>] a) (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_sub_self_nhdsGT a)
  rw [Complex.ofReal_zero] at h
  exact h

theorem eventually_sub_pos_nhdsGT (a : ℝ) : ∀ᶠ t in 𝓝[>] a, 0 < t - a :=
  eventually_mem_nhdsWithin.mono fun _ ht => sub_pos.mpr ht

/-- An eventual property on `(a, a + δ)` holds on a neighbourhood of eventually every point. -/
theorem eventually_eventually_nhds_of_nhdsGT {p : ℝ → Prop} (h : ∀ᶠ t in 𝓝[>] a, p t) :
    ∀ᶠ t in 𝓝[>] a, ∀ᶠ u in 𝓝 t, p u := by
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  filter_upwards [Ioo_mem_nhdsGT hu] with _t ht
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with w hw using hus hw

theorem eventually_deriv_eq_of_eventuallyEq {F G : ℝ → ℂ} (h : F =ᶠ[𝓝[>] a] G) :
    ∀ᶠ t in 𝓝[>] a, deriv F t = deriv G t := by
  filter_upwards [eventually_eventually_nhds_of_nhdsGT h] with t ht
  exact Filter.EventuallyEq.deriv_eq ht

theorem DExp.zero {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} (h : DExp a J F c S) :
    DExp a 0 F c S := by
  cases J with
  | zero => exact h
  | succ J => exact (dexp_succ_iff.mp h).1

theorem DExp.mono : ∀ {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧}, DExp a (J + 1) F c S →
    DExp a J F c S
  | 0, _, _, _, h => (dexp_succ_iff.mp h).1
  | J + 1, _, _, _, h => by
    obtain ⟨h1, h2, h3⟩ := dexp_succ_iff.mp h
    exact dexp_succ_iff.mpr ⟨h1, h2, DExp.mono h3⟩

theorem DExp.mono_le {J K : ℕ} (hJK : J ≤ K) {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧}
    (h : DExp a K F c S) : DExp a J F c S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJK
  clear hJK
  induction d with
  | zero => exact h
  | succ d ih => exact ih (DExp.mono h)

theorem DExp.congr : ∀ {J : ℕ} {F G : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧}, DExp a J F c S →
    F =ᶠ[𝓝[>] a] G → DExp a J G c S
  | 0, _, _, _, _, h, hFG => dexp_zero_iff.mpr (HasPowExpansion.congr' (dexp_zero_iff.mp h)
      (hFG.mono fun t ht => by simp only [ht]))
  | J + 1, _, _, _, _, h, hFG => by
    obtain ⟨h1, h2, h3⟩ := dexp_succ_iff.mp h
    refine dexp_succ_iff.mpr ⟨DExp.congr (J := 0) h1 hFG, ?_, DExp.congr h3 ?_⟩
    · filter_upwards [h2, eventually_eventually_nhds_of_nhdsGT hFG] with t ht hFGt
      exact ht.congr_of_eventuallyEq (Filter.EventuallyEq.symm hFGt)
    · exact eventually_deriv_eq_of_eventuallyEq hFG

theorem DExp.congr_exp {J : ℕ} {F : ℝ → ℂ} {c c' : ℝ} {S : ℂ⟦X⟧} (h : DExp a J F c S)
    (hc : c = c') : DExp a J F c' S := hc ▸ h

theorem DExp.congr_series {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S S' : ℂ⟦X⟧} (h : DExp a J F c S)
    (hS : S = S') : DExp a J F c S' := hS ▸ h

/-! ### Closure properties -/

theorem lopPS_add (c : ℝ) (S T : ℂ⟦X⟧) : lopPS c (S + T) = lopPS c S + lopPS c T := by
  simp only [lopPS, map_add]; ring

theorem lopPS_const_mul (c : ℝ) (k : ℂ) (S : ℂ⟦X⟧) : lopPS c (C k * S) = C k * lopPS c S := by
  simp only [lopPS, Derivation.leibniz, derivative_C, smul_eq_mul, mul_zero, add_zero]; ring

theorem lopPS_mul (c d : ℝ) (S T : ℂ⟦X⟧) :
    lopPS (c + d) (S * T) = lopPS c S * T + S * lopPS d T := by
  simp only [lopPS, Derivation.leibniz, smul_eq_mul]; push_cast; rw [map_add]; ring

theorem DExp.add : ∀ {J : ℕ} {F G : ℝ → ℂ} {c : ℝ} {S T : ℂ⟦X⟧}, DExp a J F c S →
    DExp a J G c T → DExp a J (fun t => F t + G t) c (S + T)
  | 0, _, _, _, _, _, hF, hG => dexp_zero_iff.mpr (((dexp_zero_iff.mp hF).add
      (dexp_zero_iff.mp hG)).congr' (Eventually.of_forall fun t => by simp [add_div]))
  | J + 1, F, G, c, S, T, hF, hG => by
    obtain ⟨hF1, hF2, hF3⟩ := dexp_succ_iff.mp hF
    obtain ⟨hG1, hG2, hG3⟩ := dexp_succ_iff.mp hG
    refine dexp_succ_iff.mpr ⟨DExp.add hF1 hG1, ?_, ?_⟩
    · filter_upwards [hF2, hG2] with t h1 h2 using h1.add h2
    · rw [lopPS_add]
      refine (DExp.add hF3 hG3).congr ?_
      filter_upwards [eventually_eventually_nhds_of_nhdsGT (hF2.and hG2)] with t ht
      have ht0 := ht.self_of_nhds
      exact (deriv_add ht0.1 ht0.2).symm

theorem DExp.const_mul : ∀ {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} (k : ℂ), DExp a J F c S →
    DExp a J (fun t => k * F t) c (C k * S)
  | 0, _, _, _, k, hF => dexp_zero_iff.mpr (((dexp_zero_iff.mp hF).const_mul k).congr'
      (Eventually.of_forall fun t => by simp [mul_div_assoc]))
  | J + 1, F, c, S, k, hF => by
    obtain ⟨hF1, hF2, hF3⟩ := dexp_succ_iff.mp hF
    refine dexp_succ_iff.mpr ⟨DExp.const_mul k hF1, ?_, ?_⟩
    · filter_upwards [hF2] with t h1 using h1.const_mul k
    · rw [lopPS_const_mul]
      refine (DExp.const_mul k hF3).congr ?_
      filter_upwards [hF2] with t ht
      exact (deriv_const_mul k ht).symm

theorem DExp.neg {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} (hF : DExp a J F c S) :
    DExp a J (fun t => -F t) c (-S) := by
  have h := DExp.const_mul (-1) hF
  refine (h.congr (Eventually.of_forall fun t => by simp)).congr_series ?_
  simp

theorem DExp.sub {J : ℕ} {F G : ℝ → ℂ} {c : ℝ} {S T : ℂ⟦X⟧} (hF : DExp a J F c S)
    (hG : DExp a J G c T) : DExp a J (fun t => F t - G t) c (S - T) := by
  have h := hF.add hG.neg
  exact (h.congr (Eventually.of_forall fun t => by simp [sub_eq_add_neg])).congr_series
    (by rw [sub_eq_add_neg])

theorem rpow_add_sub_ofReal {t c d : ℝ} (ht : 0 < t - a) :
    ((((t - a) ^ (c + d)) : ℝ) : ℂ) = ((((t - a) ^ c) : ℝ) : ℂ) * ((((t - a) ^ d) : ℝ) : ℂ) := by
  rw [Real.rpow_add ht, Complex.ofReal_mul]

theorem DExp.mul : ∀ {J : ℕ} {F G : ℝ → ℂ} {c d : ℝ} {S T : ℂ⟦X⟧}, DExp a J F c S →
    DExp a J G d T → DExp a J (fun t => F t * G t) (c + d) (S * T)
  | 0, F, G, c, d, S, T, hF, hG => by
    refine dexp_zero_iff.mpr ((((dexp_zero_iff.mp hF).mul (tendsto_ofReal_sub_nhdsGT a)
      (dexp_zero_iff.mp hG))).congr' ?_)
    filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
    simp only [Pi.mul_apply]
    rw [rpow_add_sub_ofReal ht]
    have h1 : ((((t - a) ^ c) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'
    have h2 : ((((t - a) ^ d) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'
    field_simp
  | J + 1, F, G, c, d, S, T, hF, hG => by
    obtain ⟨hF1, hF2, hF3⟩ := dexp_succ_iff.mp hF
    obtain ⟨hG1, hG2, hG3⟩ := dexp_succ_iff.mp hG
    refine dexp_succ_iff.mpr ⟨DExp.mul hF1 hG1, ?_, ?_⟩
    · filter_upwards [hF2, hG2] with t h1 h2 using h1.mul h2
    · rw [lopPS_mul]
      have e1 := DExp.mul hF3 hG.mono
      have e2 := DExp.mul hF.mono hG3
      refine ((e1.congr_exp (show c - 1 + d = c + d - 1 by ring)).add
        (e2.congr_exp (show c + (d - 1) = c + d - 1 by ring))).congr ?_
      filter_upwards [eventually_eventually_nhds_of_nhdsGT (hF2.and hG2)] with t ht
      have ht0 := ht.self_of_nhds
      exact (deriv_mul ht0.1 ht0.2).symm

theorem lopPS_inv (c : ℝ) {S : ℂ⟦X⟧} (hS : constantCoeff S ≠ 0) :
    lopPS (-c) S⁻¹ = -lopPS c S * S⁻¹ * S⁻¹ := by
  have h1 : S * S⁻¹ = 1 := PowerSeries.mul_inv_cancel S hS
  simp only [lopPS, derivative_inv']
  push_cast
  rw [map_neg]
  linear_combination (C (c : ℂ) * S⁻¹) * h1

theorem DExp.ne_zero {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} (h : DExp a J F c S)
    (hS : constantCoeff S ≠ 0) : ∀ᶠ t in 𝓝[>] a, F t ≠ 0 := by
  have h0 := dexp_zero_iff.mp h.zero
  filter_upwards [(h0.tendsto (tendsto_ofReal_sub_nhdsGT a)).eventually_ne hS] with t ht hF
  exact ht (by rw [hF, zero_div])

theorem DExp.inv : ∀ {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧}, DExp a J F c S →
    constantCoeff S ≠ 0 → DExp a J (fun t => (F t)⁻¹) (-c) S⁻¹
  | 0, F, c, S, hF, hS => by
    refine dexp_zero_iff.mpr (((dexp_zero_iff.mp hF).inv (tendsto_ofReal_sub_nhdsGT a)
      hS).congr' ?_)
    filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
    rw [Real.rpow_neg ht.le, Complex.ofReal_inv, inv_div, div_inv_eq_mul, div_eq_mul_inv,
      mul_comm]
  | J + 1, F, c, S, hF, hS => by
    obtain ⟨hF1, hF2, hF3⟩ := dexp_succ_iff.mp hF
    have hne := hF.ne_zero hS
    refine dexp_succ_iff.mpr ⟨DExp.inv hF1 hS, ?_, ?_⟩
    · filter_upwards [hF2, hne] with t h1 h2 using h1.inv h2
    · have hi := DExp.inv hF.mono hS
      have e := (hF3.neg.mul hi).mul hi
      rw [lopPS_inv c hS]
      refine (e.congr_exp (by ring)).congr ?_
      filter_upwards [hF2, hne] with t h1 h2
      rw [deriv_fun_inv'' h1 h2]
      field_simp

theorem X_mul_derivative_X_pow (s : ℕ) : X * d⁄dX ((X : ℂ⟦X⟧) ^ s) = C (s : ℂ) * X ^ s := by
  rcases s with _ | s
  · simp
  · rw [Derivation.leibniz_pow, derivative_X]
    push_cast
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
    rw [map_add, map_one, map_natCast]
    push_cast
    ring

theorem lopPS_X_pow_mul (c : ℝ) (s : ℕ) (T : ℂ⟦X⟧) :
    lopPS c (X ^ s * T) = X ^ s * lopPS (c + s) T := by
  have h := X_mul_derivative_X_pow s
  simp only [lopPS, Derivation.leibniz, smul_eq_mul]
  push_cast
  rw [map_add]
  linear_combination T * h

/-- The powers `(t − a)ᵉ`. -/
theorem dexp_rpow_sub : ∀ (J : ℕ) (e : ℝ),
    DExp a J (fun t => ((((t - a) ^ e) : ℝ) : ℂ)) e 1
  | 0, e => by
    refine dexp_zero_iff.mpr (((hasPowExpansion_const (tendsto_ofReal_sub_nhdsGT a)
      (1 : ℂ))).congr' ?_ |> fun h => by rwa [map_one] at h)
    filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
    rw [div_self (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne')]
  | J + 1, e => by
    refine dexp_succ_iff.mpr ⟨dexp_rpow_sub 0 e, ?_, ?_⟩
    · filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
      exact ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).comp t
        ((hasDerivAt_id t).sub_const a)).ofReal_comp.differentiableAt
    · have h := (dexp_rpow_sub J (e - 1)).const_mul (e : ℂ)
      refine (h.congr ?_).congr_series ?_
      · filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
        have h0 : HasDerivAt (fun x : ℝ => x ^ e) (e * (t - a) ^ (e - 1)) (t - a) :=
          Real.hasDerivAt_rpow_const (Or.inl ht.ne')
        have hd : HasDerivAt (fun t => ((((t - a) ^ e) : ℝ) : ℂ))
            (((e * (t - a) ^ (e - 1) : ℝ)) : ℂ) t := (h0.comp_sub_const t a).ofReal_comp
        rw [hd.deriv]
        push_cast
        ring
      · simp [lopPS]

/-- Re-indexing: `(t−a)^{c+s} T = (t−a)^c (Xˢ T)`. -/
theorem DExp.reindex : ∀ {J : ℕ} {F : ℝ → ℂ} {c : ℝ} (s : ℕ) {T : ℂ⟦X⟧},
    DExp a J F (c + s) T → DExp a J F c (X ^ s * T)
  | 0, F, c, s, T, hF => by
    have hy := tendsto_ofReal_sub_nhdsGT a
    refine dexp_zero_iff.mpr ((((hasPowExpansion_id hy).pow hy s).mul hy
      (dexp_zero_iff.mp hF)).congr' ?_)
    filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
    simp only [Pi.mul_apply]
    rw [rpow_add_sub_ofReal ht, Real.rpow_natCast, Complex.ofReal_pow]
    have h1 : ((((t - a) ^ c) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne'
    have h2 : ((t - a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    field_simp
  | J + 1, F, c, s, T, hF => by
    obtain ⟨hF1, hF2, hF3⟩ := dexp_succ_iff.mp hF
    refine dexp_succ_iff.mpr ⟨DExp.reindex s hF1, hF2, ?_⟩
    rw [lopPS_X_pow_mul]
    exact DExp.reindex s (hF3.congr_exp (by ring))

/-! ### Real powers of a positive function -/

theorem HasPowExpansion.of_ofReal {α : Type*} {l : Filter α} {y f : α → ℝ} {A : ℝ⟦X⟧}
    (h : HasPowExpansion l (fun x => (y x : ℂ)) (fun x => (f x : ℂ)) (toCPS A)) :
    HasPowExpansion l y f A := fun n => by
  have h1 := h n
  rw [← isBigO_norm_left, ← isBigO_norm_right] at h1 ⊢
  refine h1.congr (fun x => ?_) (fun x => ?_)
  · beta_reduce
    rw [trunc_map, Polynomial.eval_map, show ((y x : ℂ)) = Complex.ofRealHom (y x) from rfl,
      Polynomial.eval₂_at_apply, Complex.ofRealHom_eq_coe, ← Complex.ofReal_sub,
      Complex.norm_real]
  · beta_reduce
    rw [← Complex.ofReal_pow, Complex.norm_real]

theorem coeff_lopPS (c : ℝ) (S : ℂ⟦X⟧) (n : ℕ) :
    coeff n (lopPS c S) = ((c : ℂ) + n) * coeff n S := by
  rcases n with _ | n
  · simp [lopPS]
  · rw [lopPS, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem lopPS_zero_rpowPS {P : ℝ⟦X⟧} (hP : 0 < constantCoeff P) (β : ℝ) :
    lopPS 0 (toCPS (rpowPS P β)) =
      C (β : ℂ) * toCPS (rpowPS P β) * (toCPS P)⁻¹ * lopPS 0 (toCPS P) := by
  have hD := congrArg toCPS (derivative_rpowPS_mul hP β)
  rw [map_mul, map_mul, map_mul, map_C, ← derivative_map_ofReal, ← derivative_map_ofReal] at hD
  have hP0 : constantCoeff (toCPS P) ≠ 0 := by
    rw [constantCoeff_toCPS]; exact Complex.ofReal_ne_zero.mpr hP.ne'
  have hinv : toCPS P * (toCPS P)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hP0
  simp only [lopPS, Complex.ofReal_zero, map_zero, zero_mul, zero_add]
  linear_combination (X * (toCPS P)⁻¹) * hD - (X * d⁄dX (toCPS (rpowPS P β))) * hinv

theorem DExp.rpow_real : ∀ {J : ℕ} {f : ℝ → ℝ} {P : ℝ⟦X⟧},
    DExp a J (fun t => (f t : ℂ)) 0 (toCPS P) → 0 < constantCoeff P → ∀ β : ℝ,
    DExp a J (fun t => ((f t ^ β : ℝ) : ℂ)) 0 (toCPS (rpowPS P β))
  | 0, f, P, hF, hP, β => by
    have hy := tendsto_sub_self_nhdsGT a
    have h0 := dexp_zero_iff.mp hF
    have hreal : HasPowExpansion (𝓝[>] a) (fun t => t - a) f P := by
      refine HasPowExpansion.of_ofReal (h0.congr' (Eventually.of_forall fun t => ?_))
      simp
    refine dexp_zero_iff.mpr (((hreal.rpow hy hP β).ofReal).congr'
      (Eventually.of_forall fun t => ?_))
    simp
  | J + 1, f, P, hF, hP, β => by
    obtain ⟨hF1, hF2, hF3⟩ := dexp_succ_iff.mp hF
    have hP0 : constantCoeff (toCPS P) ≠ 0 := by
      rw [constantCoeff_toCPS]; exact Complex.ofReal_ne_zero.mpr hP.ne'
    have hfpos : ∀ᶠ t in 𝓝[>] a, 0 < f t := by
      have h0 := dexp_zero_iff.mp hF1
      have ht := h0.tendsto (tendsto_ofReal_sub_nhdsGT a)
      rw [constantCoeff_toCPS] at ht
      have hre := (Complex.continuous_re.tendsto _).comp ht
      simp only [Complex.ofReal_re] at hre
      filter_upwards [hre.eventually (lt_mem_nhds hP)] with t ht
      simpa using ht
    have hfd : ∀ᶠ t in 𝓝[>] a, DifferentiableAt ℝ f t := by
      filter_upwards [hF2] with t ht
      have := (Complex.reCLM.differentiableAt.comp t ht)
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
      simp
    refine dexp_succ_iff.mpr ⟨DExp.rpow_real hF1 hP β, ?_, ?_⟩
    · filter_upwards [hfd, hfpos] with t h1 h2
      exact ((h1.rpow_const (Or.inl h2.ne')).hasDerivAt.ofReal_comp).differentiableAt
    · have e := (((DExp.rpow_real hF.mono hP β).const_mul (β : ℂ)).mul
        (hF.mono.inv hP0)).mul hF3
      rw [lopPS_zero_rpowPS hP β]
      refine (e.congr_exp (by ring)).congr ?_
      filter_upwards [hfd, hfpos] with t h1 h2
      have hd1 : deriv (fun t => (f t : ℂ)) t = ((deriv f t : ℝ) : ℂ) :=
        h1.hasDerivAt.ofReal_comp.deriv
      have hd2 : deriv (fun t => ((f t ^ β : ℝ) : ℂ)) t =
          ((β * f t ^ (β - 1) * deriv f t : ℝ) : ℂ) := by
        have := (h1.hasDerivAt.rpow_const (p := β) (Or.inl h2.ne')).ofReal_comp
        rw [this.deriv]
        push_cast
        ring
      rw [hd1, hd2, Real.rpow_sub_one h2.ne']
      have : (f t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2.ne'
      push_cast
      field_simp

/-! ### From DLMF's differentiable expansions -/

/-- Complex `F`: the expansions of all `F⁽ᵏ⁾` give `DExp` of every order. -/
theorem dexp_of_isGen {F : ℝ → ℂ} {c δ : ℝ} {coef : ℕ → ℂ} (hδ : 0 < δ)
    (hF : ContDiffOn ℝ ∞ F (Ioo a (a + δ)))
    (h : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + c - k)) : ℝ) : ℂ)) (iteratedDeriv k F)
      (fun s t => coef s * (((descPochhammer ℝ k).eval ((s : ℝ) + c) : ℝ) : ℂ) *
        ((((t - a) ^ ((s : ℝ) + c - k)) : ℝ) : ℂ))) (J : ℕ) :
    DExp a J F c (mk coef) := by
  suffices key : ∀ J k : ℕ, DExp a J (iteratedDeriv k F) (c - k)
      (mk fun s => coef s * (((descPochhammer ℝ k).eval ((s : ℝ) + c) : ℝ) : ℂ)) by
    have := key J 0
    simpa using this
  intro J
  induction J with
  | zero =>
    intro k
    have hk := h k
    simp only [add_sub_assoc] at hk
    exact dexp_zero_iff.mpr (hasPowExpansion_div_rpow_complex hk)
  | succ J ih =>
    intro k
    refine dexp_succ_iff.mpr ⟨?_, ?_, ?_⟩
    · have hk := h k
      simp only [add_sub_assoc] at hk
      exact dexp_zero_iff.mpr (hasPowExpansion_div_rpow_complex hk)
    · filter_upwards [Ioo_mem_nhdsGT (by linarith : a < a + δ)] with t ht
      exact (hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioo hF k ht).differentiableAt
    · have e := ih (k + 1)
      refine ((e.congr_exp (by push_cast; ring)).congr ?_).congr_series ?_
      · filter_upwards [Ioo_mem_nhdsGT (by linarith : a < a + δ)] with t ht
        exact (hasDerivAt_iteratedDeriv_of_contDiffOn isOpen_Ioo hF k ht).deriv.symm
      · ext n
        rw [coeff_lopPS, coeff_mk, coeff_mk, descPochhammer_succ_eval]
        push_cast
        ring

theorem hasDerivAt_iteratedDeriv_real {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (s : ℕ) {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (iteratedDeriv s f) (iteratedDeriv (s + 1) f t) t := by
  have hlt : ((s : ℕ) : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.natCast_lt_top s
  have hd := (hf.differentiableOn_iteratedDerivWithin hlt hU.uniqueDiffOn) t ht
  have heq : iteratedDerivWithin s f U =ᶠ[𝓝 t] iteratedDeriv s f :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds ht) (iteratedDerivWithin_of_isOpen hU)
  have hda : DifferentiableAt ℝ (iteratedDeriv s f) t :=
    ((hd.differentiableAt (hU.mem_nhds ht)).congr_of_eventuallyEq heq.symm)
  rw [iteratedDeriv_succ]
  exact hda.hasDerivAt

/-- Real `f`: the expansions of all `f⁽ᵏ⁾` give `DExp` of every order for `↑f`. -/
theorem dexp_ofReal_of_isGen {f : ℝ → ℝ} {c δ : ℝ} {coef : ℕ → ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a (a + δ)))
    (h : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => (t - a) ^ ((s : ℝ) + c - k)) (iteratedDeriv k f)
      (fun s t => coef s * (descPochhammer ℝ k).eval ((s : ℝ) + c) *
        (t - a) ^ ((s : ℝ) + c - k))) (J : ℕ) :
    DExp a J (fun t => (f t : ℂ)) c (toCPS (mk coef)) := by
  suffices key : ∀ J k : ℕ, DExp a J (fun t => ((iteratedDeriv k f t : ℝ) : ℂ)) (c - k)
      (toCPS (mk fun s => coef s * (descPochhammer ℝ k).eval ((s : ℝ) + c))) by
    have := key J 0
    simpa using this
  have base : ∀ k : ℕ, DExp a 0 (fun t => ((iteratedDeriv k f t : ℝ) : ℂ)) (c - k)
      (toCPS (mk fun s => coef s * (descPochhammer ℝ k).eval ((s : ℝ) + c))) := fun k => by
    have hk := h k
    simp only [add_sub_assoc] at hk
    refine dexp_zero_iff.mpr (((hasPowExpansion_div_rpow_real hk).ofReal).congr'
      (Eventually.of_forall fun t => ?_))
    simp
  intro J
  induction J with
  | zero => exact base
  | succ J ih =>
    intro k
    refine dexp_succ_iff.mpr ⟨base k, ?_, ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT (by linarith : a < a + δ)] with t ht
      exact (hasDerivAt_iteratedDeriv_real isOpen_Ioo hf k ht).ofReal_comp.differentiableAt
    · have e := ih (k + 1)
      refine ((e.congr_exp (by push_cast; ring)).congr ?_).congr_series ?_
      · filter_upwards [Ioo_mem_nhdsGT (by linarith : a < a + δ)] with t ht
        exact (hasDerivAt_iteratedDeriv_real isOpen_Ioo hf k ht).ofReal_comp.deriv.symm
      · ext n
        rw [coeff_lopPS, coeff_toCPS, coeff_toCPS, coeff_mk, coeff_mk, descPochhammer_succ_eval]
        push_cast
        ring

/-! ### The operator `(1/p′) d/dt` and orders of vanishing -/

/-- `F ↦ F′/p′`. -/
noncomputable def dopF (p' : ℝ → ℝ) (F : ℝ → ℂ) : ℝ → ℂ := fun t => deriv F t / (p' t : ℂ)

/-- **DLMF 2.3.21**: `Pₛ(t) = ((1/p′(t)) d/dt)ˢ (q(t)/p′(t))`. -/
noncomputable def statP (p' : ℝ → ℝ) (q : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun t => q t / (p' t : ℂ)
  | k + 1 => dopF p' (statP p' q k)

theorem DExp.dop {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} {p' : ℝ → ℝ} {μ : ℝ} {D : ℂ⟦X⟧}
    (hF : DExp a (J + 1) F c S) (hp : DExp a J (fun t => (p' t : ℂ)) (μ - 1) D)
    (hD : constantCoeff D ≠ 0) : DExp a J (dopF p' F) (c - μ) (lopPS c S * D⁻¹) :=
  (((dexp_succ_iff.mp hF).2.2.mul (hp.inv hD)).congr_exp (by ring)).congr
    (Eventually.of_forall fun t => by simp [dopF, div_eq_mul_inv])

theorem X_pow_dvd_lopPS_mul {N : ℕ} {S : ℂ⟦X⟧} (hS : X ^ N ∣ S) (c : ℝ) (D : ℂ⟦X⟧) :
    X ^ N ∣ lopPS c S * D := by
  obtain ⟨T, rfl⟩ := hS
  rw [lopPS_X_pow_mul, mul_assoc]
  exact dvd_mul_right _ _

theorem DExp.zero_fun (J : ℕ) (c : ℝ) : DExp a J (fun _ => 0) c 0 := by
  have h := (dexp_rpow_sub (a := a) J c).const_mul (0 : ℂ)
  exact (h.congr (Eventually.of_forall fun t => by simp)).congr_series (by simp)

theorem DExp.sum {J : ℕ} {c : ℝ} {ι : Type*} (T : Finset ι) {F : ι → ℝ → ℂ} {S : ι → ℂ⟦X⟧}
    (h : ∀ i ∈ T, DExp a J (F i) c (S i)) :
    DExp a J (fun t => ∑ i ∈ T, F i t) c (∑ i ∈ T, S i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using DExp.zero_fun J c
  | insert i T hi ih =>
    have h1 := h i (Finset.mem_insert_self i T)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    refine ((h1.add h2).congr (Eventually.of_forall fun t => ?_)).congr_series ?_
    · simp [Finset.sum_insert hi]
    · rw [Finset.sum_insert hi]

/-- If `F ∼ S(y)` and `F = O(y^N)`, the first `N` coefficients of `S` vanish. -/
theorem coeff_eq_zero_of_isBigO {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} [l.NeBot]
    {y F : α → 𝕜} {S : 𝕜⟦X⟧} (hy : Tendsto y l (𝓝 0)) (hy0 : ∀ᶠ x in l, y x ≠ 0)
    (hF : HasPowExpansion l y F S) {N : ℕ} (hO : F =O[l] fun x => y x ^ N) :
    X ^ N ∣ S := by
  rw [X_pow_dvd_iff]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have htr : trunc n S = 0 := by
      ext d
      rw [coeff_trunc, Polynomial.coeff_zero]
      split_ifs with hd
      · exact ih d hd (hd.trans hn)
      · rfl
    have hlim := (hasPowExpansion_iff_tendsto hy hy0).mp hF n
    simp only [htr, Polynomial.eval_zero, sub_zero] at hlim
    have h0 : Tendsto (fun x => F x / y x ^ n) l (𝓝 0) := by
      have hO' : (fun x => F x / y x ^ n) =O[l] fun x => y x ^ (N - n) := by
        refine (hO.mul (isBigO_refl (fun x => (y x ^ n)⁻¹) l)).congr' (Eventually.of_forall
          fun x => by simp [div_eq_mul_inv]) ?_
        filter_upwards [hy0] with x hx
        rw [← pow_sub₀ _ hx (by omega)]
      refine hO'.trans_tendsto ?_
      have := hy.pow (N - n)
      rwa [zero_pow (by omega)] at this
    exact tendsto_nhds_unique hlim h0

/-- A bound from an expansion whose first `N` coefficients vanish. -/
theorem DExp.bound_of_dvd {J : ℕ} {F : ℝ → ℂ} {c : ℝ} {S : ℂ⟦X⟧} (h : DExp a J F c S) {N : ℕ}
    (hS : X ^ N ∣ S) : ∃ δ C, 0 < δ ∧ ∀ t ∈ Ioo a (a + δ), ‖F t‖ ≤ C * (t - a) ^ (c + N) := by
  have h0 := dexp_zero_iff.mp h.zero N
  rw [trunc_eq_of_X_pow_dvd_sub (B := 0) (by simpa using hS), map_zero] at h0
  obtain ⟨C, hC⟩ := h0.bound
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hC.and (eventually_sub_pos_nhdsGT a))
  refine ⟨u - a, C, by linarith [show a < u from hu], fun t ht => ?_⟩
  obtain ⟨h1, hτ⟩ := hus ⟨ht.1, by linarith [ht.2]⟩
  have hc0 : 0 < (t - a) ^ c := Real.rpow_pos_of_pos hτ c
  simp only [Polynomial.eval_zero, sub_zero, norm_div, Complex.norm_real, norm_pow,
    Real.norm_of_nonneg hc0.le, Real.norm_of_nonneg hτ.le] at h1
  rw [div_le_iff₀ hc0] at h1
  rw [Real.rpow_add hτ, Real.rpow_natCast]
  linarith [h1]

/-! ### The differentiated expansion of `q/p′` in powers of `p(t) − p(a)` -/

theorem IsGenAsympExpansionDLMF.congr_gen {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α}
    {φ φ' : ℕ → α → 𝕜} {f f' : α → 𝕜} {fs fs' : ℕ → α → 𝕜}
    (h : IsGenAsympExpansionDLMF l φ f fs)
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

/-- The exponents `(s + λ − μ)/μ` of 2.3.16. -/
noncomputable def spExp (lam μ : ℝ) (s : ℕ) : ℝ := ((s : ℝ) + lam - μ) / μ

/-- **The differentiated form of 2.3.16**: under the differentiable expansions 2.3.14,
`Pₖ(t) − ∑_{s<N} bₛ (d/dv)ᵏ v^{(s+λ−μ)/μ} = O(v^{(N+λ−μ)/μ − k})` as `t → a+`. -/
theorem statP_sub_bound {p p' : ℝ → ℝ} {q : ℝ → ℂ} {a lam μ δ : ℝ} {ps : ℕ → ℝ} {qs : ℕ → ℂ}
    (hμ : 0 < μ) (hp0 : 0 < ps 0) (hδ : 0 < δ)
    (hpd : ∀ t ∈ Ioo a (a + δ), HasDerivAt p (p' t) t)
    (hps : ContDiffOn ℝ ∞ p (Ioo a (a + δ))) (hqs : ContDiffOn ℝ ∞ q (Ioo a (a + δ)))
    (hp : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - k))
      (iteratedDeriv k fun t => p t - p a)
      (fun s t => ps s * (descPochhammer ℝ k).eval ((s : ℝ) + μ) * (t - a) ^ ((s : ℝ) + μ - k)))
    (hq : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ)) (iteratedDeriv k q)
      (fun s t => qs s * (((descPochhammer ℝ k).eval ((s : ℝ) + lam - 1) : ℝ) : ℂ) *
        ((((t - a) ^ ((s : ℝ) + lam - 1 - k)) : ℝ) : ℂ))) (N k : ℕ) :
    ∃ δ' C, 0 < δ' ∧ ∀ t ∈ Ioo a (a + δ'),
      ‖statP p' q k t - ∑ s ∈ Finset.range N, laplaceMethodCoeff ps qs lam μ s *
        (((descPochhammer ℝ k).eval (spExp lam μ s) : ℝ) : ℂ) *
          (((p t - p a) ^ (spExp lam μ s - k) : ℝ) : ℂ)‖ ≤
        C * (p t - p a) ^ (spExp lam μ N - k) := by
  set v : ℝ → ℝ := fun t => p t - p a with hvdef
  set b := laplaceMethodCoeff ps qs lam μ with hbdef
  set e := spExp lam μ with hedef
  set c := lam - μ with hcdef
  set P : ℝ⟦X⟧ := mk ps with hPdef
  set Dc : ℂ⟦X⟧ := toCPS (mk fun s => ((s : ℝ) + μ) * ps s) with hDcdef
  have hP : 0 < constantCoeff P := by rw [hPdef, constantCoeff_mk']; exact hp0
  have hIoo : Ioo a (a + δ) ∈ 𝓝[>] a := Ioo_mem_nhdsGT (by linarith)
  -- the expansions of `v`, `p′`, `q`
  have hvC : ∀ J, DExp a J (fun t => (v t : ℂ)) μ (toCPS P) := fun J =>
    dexp_ofReal_of_isGen hδ (hps.sub contDiffOn_const) hp J
  have hp'C : ∀ J, DExp a J (fun t => (p' t : ℂ)) (μ - 1) Dc := fun J => by
    have h := (dexp_succ_iff.mp (hvC (J + 1))).2.2
    refine (h.congr ?_).congr_series ?_
    · filter_upwards [hIoo] with t ht
      exact ((hpd t ht).sub_const (p a)).ofReal_comp.deriv
    · ext n
      rw [coeff_lopPS, hDcdef, coeff_toCPS, coeff_toCPS, coeff_mk, coeff_mk]
      push_cast; ring
  have hq' : ∀ k : ℕ, IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + (lam - 1) - k)) : ℝ) : ℂ)) (iteratedDeriv k q)
      (fun s t => qs s * (((descPochhammer ℝ k).eval ((s : ℝ) + (lam - 1)) : ℝ) : ℂ) *
        ((((t - a) ^ ((s : ℝ) + (lam - 1) - k)) : ℝ) : ℂ)) := fun k => by
    simp only [← add_sub_assoc]
    exact hq k
  have hqC : ∀ J, DExp a J q (lam - 1) (mk qs) := fun J => dexp_of_isGen hδ hqs hq' J
  have hD0 : constantCoeff Dc ≠ 0 := by
    rw [hDcdef, constantCoeff_toCPS, constantCoeff_mk']
    refine Complex.ofReal_ne_zero.mpr ?_
    have : ((0 : ℕ) : ℝ) + μ = μ := by simp
    rw [this]; exact (mul_pos hμ hp0).ne'
  -- `f₁ = v/(t − a)^μ`
  set f₁ : ℝ → ℝ := fun t => v t / (t - a) ^ μ with hf₁
  have hf1C : ∀ J, DExp a J (fun t => (f₁ t : ℂ)) 0 (toCPS P) := fun J => by
    have h := (hvC J).mul (dexp_rpow_sub (a := a) J (-μ))
    refine ((h.congr_exp (by ring)).congr ?_).congr_series (by rw [mul_one])
    filter_upwards [eventually_sub_pos_nhdsGT a] with t ht
    rw [hf₁]
    simp only
    rw [Real.rpow_neg ht.le]
    push_cast
    ring
  have hf1t : Tendsto f₁ (𝓝[>] a) (𝓝 (ps 0)) := by
    have h0 := (dexp_zero_iff.mp (hf1C 0)).tendsto (tendsto_ofReal_sub_nhdsGT a)
    rw [constantCoeff_toCPS, hPdef, constantCoeff_mk'] at h0
    have hre := (Complex.continuous_re.tendsto _).comp h0
    simp only [Complex.ofReal_re] at hre
    refine hre.congr' (Eventually.of_forall fun t => ?_)
    simp
  have hfpos : ∀ᶠ t in 𝓝[>] a, 0 < f₁ t := hf1t.eventually (lt_mem_nhds hp0)
  have hv_eq : ∀ t, 0 < t - a → v t = f₁ t * (t - a) ^ μ := fun t ht => by
    rw [hf₁]; simp only; rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht μ).ne']
  have hvpow : ∀ t, 0 < t - a → 0 < f₁ t → ∀ r : ℝ,
      v t ^ r = f₁ t ^ r * (t - a) ^ (μ * r) := fun t ht hf r => by
    rw [hv_eq t ht, Real.mul_rpow hf.le (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
  have hve : ∀ J (s : ℕ), DExp a J (fun t => ((v t ^ e s : ℝ) : ℂ)) c
      (X ^ s * toCPS (rpowPS P (e s))) := fun J s => by
    have h := (dexp_rpow_sub (a := a) J (μ * e s)).mul ((hf1C J).rpow_real hP (e s))
    have h2 : DExp a J (fun t => ((v t ^ e s : ℝ) : ℂ)) (c + s) (toCPS (rpowPS P (e s))) := by
      refine ((h.congr_exp ?_).congr ?_).congr_series (one_mul _)
      · simp only [hedef, spExp, hcdef]; field_simp; ring
      · filter_upwards [eventually_sub_pos_nhdsGT a, hfpos] with t ht hf
        rw [hvpow t ht hf]
        push_cast
        ring
    exact DExp.reindex s h2
  -- the expansion of `E₀ = q/p′ − ∑ bₛ v^{eₛ}`
  set S0 : ℂ⟦X⟧ := mk qs * Dc⁻¹ - ∑ s ∈ Finset.range N, C (b s) * (X ^ s * toCPS (rpowPS P (e s)))
    with hS0def
  set E0 : ℝ → ℂ := fun t => statP p' q 0 t - ∑ s ∈ Finset.range N, b s * ((v t ^ e s : ℝ) : ℂ)
    with hE0def
  have hE0 : ∀ J, DExp a J E0 c S0 := fun J => by
    have h1 := ((hqC J).mul ((hp'C J).inv hD0)).congr_exp (show lam - 1 + -(μ - 1) = c by ring)
    have h2 := DExp.sum (Finset.range N) fun s _ => (hve J s).const_mul (b s)
    refine (h1.sub h2).congr (Eventually.of_forall fun t => ?_)
    simp [hE0def, statP, div_eq_mul_inv]
  -- 2.3.16 gives `E₀ = O(v^{e_N})`, hence `X^N ∣ S₀`
  have hpk0 : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ))
      (fun t => p t - p a) (fun s t => ps s * (t - a) ^ ((s : ℝ) + μ)) := by
    have h := hp 0
    simp only [Nat.cast_zero, sub_zero, iteratedDeriv_zero, descPochhammer_zero,
      Polynomial.eval_one, mul_one] at h
    exact h
  have hpk1 : IsGenAsympExpansionDLMF (𝓝[>] a) (fun s t => (t - a) ^ ((s : ℝ) + μ - 1)) p'
      (fun s t => ((s : ℝ) + μ) * ps s * (t - a) ^ ((s : ℝ) + μ - 1)) := by
    have h := hp 1
    simp only [Nat.cast_one, iteratedDeriv_one, descPochhammer_one, Polynomial.eval_X] at h
    refine h.congr_gen (fun s => EventuallyEq.rfl) ?_ (fun s => Eventually.of_forall fun t => by
      ring)
    filter_upwards [hIoo] with t ht
    exact ((hpd t ht).sub_const (p a)).deriv
  have hqk0 : IsGenAsympExpansionDLMF (𝓝[>] a)
      (fun s t => ((((t - a) ^ ((s : ℝ) + lam - 1)) : ℝ) : ℂ)) q
      (fun s t => qs s * ((((t - a) ^ ((s : ℝ) + lam - 1)) : ℝ) : ℂ)) := by
    have h := hq 0
    simp only [Nat.cast_zero, sub_zero, iteratedDeriv_zero, descPochhammer_zero,
      Polynomial.eval_one, Complex.ofReal_one, mul_one] at h
    exact h
  have h16 := (dlmf_2_3_16 hμ hp0 hpk0 hpk1 hqk0).2 N
  obtain ⟨C₁, hC₁⟩ := h16
  rw [eventually_map] at hC₁
  have hτ := eventually_sub_pos_nhdsGT a
  have hvpos : ∀ᶠ t in 𝓝[>] a, 0 < v t := by
    filter_upwards [hτ, hfpos] with t ht hf
    rw [hv_eq t ht]; exact mul_pos hf (Real.rpow_pos_of_pos ht μ)
  -- `f₁` stays between `p₀/2` and `2p₀`
  have hfr : ∀ᶠ t in 𝓝[>] a, ps 0 / 2 ≤ f₁ t ∧ f₁ t ≤ 2 * ps 0 := by
    filter_upwards [hf1t.eventually (le_mem_nhds (by linarith : ps 0 / 2 < ps 0)),
      hf1t.eventually (ge_mem_nhds (by linarith : ps 0 < 2 * ps 0))] with t h1 h2
    exact ⟨h1, h2⟩
  have hrange : ∀ r : ℝ, ∀ x, ps 0 / 2 ≤ x → x ≤ 2 * ps 0 →
      min ((ps 0 / 2) ^ r) ((2 * ps 0) ^ r) ≤ x ^ r ∧
        x ^ r ≤ max ((ps 0 / 2) ^ r) ((2 * ps 0) ^ r) :=
    fun r x h1 h2 => by
      have hA : 0 < ps 0 / 2 := by linarith
      rcases le_total 0 r with hr | hr
      · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hA.le h1 hr),
          (Real.rpow_le_rpow (hA.le.trans h1) h2 hr).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (hA.trans_le h1) h2 hr),
          (Real.rpow_le_rpow_of_nonpos hA h1 hr).trans (le_max_left _ _)⟩
  -- `E₀/(t − a)^c = O((t − a)^N)`
  set MN := max ((ps 0 / 2) ^ e N) ((2 * ps 0) ^ e N)
  have hO : (fun t => E0 t / ((((t - a) ^ c) : ℝ) : ℂ)) =O[𝓝[>] a]
      fun t => ((t - a : ℝ) : ℂ) ^ N := by
    refine IsBigO.of_bound (|C₁| * MN) ?_
    filter_upwards [hC₁, hτ, hfpos, hfr] with t h ht hf hfr'
    change ‖E0 t / ((v t ^ e N : ℝ) : ℂ)‖ ≤ C₁ at h
    have hv0 : 0 < v t := by
      rw [hv_eq t ht]; exact mul_pos hf (Real.rpow_pos_of_pos ht μ)
    have hvN : 0 < v t ^ e N := Real.rpow_pos_of_pos hv0 _
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hvN.le, div_le_iff₀ hvN] at h
    have hc0 : 0 < (t - a) ^ c := Real.rpow_pos_of_pos ht c
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc0.le, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg ht.le, div_le_iff₀ hc0]
    have hμe : μ * e N = c + N := by simp only [hedef, spExp, hcdef]; field_simp; ring
    rw [hvpow t ht hf, hμe, Real.rpow_add ht, Real.rpow_natCast] at h
    have hM := (hrange (e N) (f₁ t) hfr'.1 hfr'.2).2
    have hfN : 0 ≤ f₁ t ^ e N := Real.rpow_nonneg hf.le _
    calc ‖E0 t‖ ≤ C₁ * (f₁ t ^ e N * ((t - a) ^ c * (t - a) ^ N)) := h
      _ ≤ |C₁| * (MN * ((t - a) ^ c * (t - a) ^ N)) := by
          gcongr
          · exact le_abs_self _
      _ = _ := by ring
  have hdvd : X ^ N ∣ S0 := coeff_eq_zero_of_isBigO (tendsto_ofReal_sub_nhdsGT a)
    (hτ.mono fun t ht => Complex.ofReal_ne_zero.mpr ht.ne') (dexp_zero_iff.mp (hE0 0)) hO
  -- iterating `(1/p′) d/dt`
  set E : ℕ → ℝ → ℂ := fun k => (dopF p')^[k] E0 with hEdef
  have hEk : ∀ k J, ∃ S, X ^ N ∣ S ∧ DExp a J (E k) (c - k * μ) S := by
    intro k
    induction k with
    | zero => intro J; exact ⟨S0, hdvd, by simpa [hEdef] using hE0 J⟩
    | succ k ih =>
      intro J
      obtain ⟨S, hS, h⟩ := ih (J + 1)
      refine ⟨_, X_pow_dvd_lopPS_mul hS (c - k * μ) Dc⁻¹, ?_⟩
      have h2 := h.dop (hp'C J) hD0
      refine (h2.congr_exp (by push_cast; ring)).congr (Eventually.of_forall fun t => ?_)
      simp only [hEdef, Function.iterate_succ_apply']
  -- the explicit form of `E k`
  have hp'ne : ∀ᶠ t in 𝓝[>] a, (p' t : ℂ) ≠ 0 := (hp'C 0).ne_zero hD0
  set G : ℕ → ℝ → ℂ := fun k t => statP p' q k t - ∑ s ∈ Finset.range N, b s *
    (((descPochhammer ℝ k).eval (e s) : ℝ) : ℂ) * ((v t ^ (e s - k) : ℝ) : ℂ) with hGdef
  have hvd : ∀ r : ℝ, ∀ᶠ t in 𝓝[>] a, HasDerivAt (fun t => ((v t ^ r : ℝ) : ℂ))
      (((r * v t ^ (r - 1) * p' t : ℝ)) : ℂ) t := fun r => by
    filter_upwards [hIoo, hvpos] with t ht hv
    have h := (((hpd t ht).sub_const (p a)).rpow_const (p := r) (Or.inl hv.ne')).ofReal_comp
    convert h using 2
    simp only [hvdef]
    ring
  have hEG : ∀ k, E k =ᶠ[𝓝[>] a] G k := by
    intro k
    induction k with
    | zero =>
      exact Eventually.of_forall fun t => by simp [hEdef, hGdef, hE0def]
    | succ k ih =>
      obtain ⟨S, -, h⟩ := hEk k 1
      have hEd := (dexp_succ_iff.mp h).2.1
      have hderiv := eventually_deriv_eq_of_eventuallyEq ih
      have hall : ∀ᶠ t in 𝓝[>] a, ∀ s ∈ Finset.range N, HasDerivAt
          (fun t => ((v t ^ (e s - k) : ℝ) : ℂ))
          ((((e s - k) * v t ^ (e s - k - 1) * p' t : ℝ)) : ℂ) t :=
        (Filter.eventually_all_finset _).mpr fun s _ => hvd (e s - k)
      have hGd : ∀ᶠ t in 𝓝[>] a, DifferentiableAt ℝ (statP p' q k) t := by
        filter_upwards [eventually_eventually_nhds_of_nhdsGT ih,
          eventually_eventually_nhds_of_nhdsGT hEd,
          eventually_eventually_nhds_of_nhdsGT hall] with t h1 h2 h3
        have hsum : DifferentiableAt ℝ (fun t => ∑ s ∈ Finset.range N, b s *
            (((descPochhammer ℝ k).eval (e s) : ℝ) : ℂ) * ((v t ^ (e s - k) : ℝ) : ℂ)) t :=
          DifferentiableAt.fun_sum fun s hs =>
            ((h3.self_of_nhds s hs).differentiableAt.const_mul _)
        have hGk : DifferentiableAt ℝ (G k) t :=
          h2.self_of_nhds.congr_of_eventuallyEq (h1.mono fun u hu => hu.symm)
        have := hGk.add hsum
        refine this.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
        simp [hGdef]
      filter_upwards [hderiv, hGd, hall, hp'ne, hvpos] with t h1 h2 h3 h4 h5
      have hsumd : HasDerivAt (fun t => ∑ s ∈ Finset.range N, b s *
          (((descPochhammer ℝ k).eval (e s) : ℝ) : ℂ) * ((v t ^ (e s - k) : ℝ) : ℂ))
          (∑ s ∈ Finset.range N, b s * (((descPochhammer ℝ k).eval (e s) : ℝ) : ℂ) *
            ((((e s - k) * v t ^ (e s - k - 1) * p' t : ℝ)) : ℂ)) t :=
        HasDerivAt.fun_sum fun s hs => (h3 s hs).const_mul _
      have hd : deriv (G k) t = deriv (statP p' q k) t - ∑ s ∈ Finset.range N, b s *
          (((descPochhammer ℝ k).eval (e s) : ℝ) : ℂ) *
            ((((e s - k) * v t ^ (e s - k - 1) * p' t : ℝ)) : ℂ) :=
        (h2.hasDerivAt.sub hsumd).deriv
      simp only [hEdef, Function.iterate_succ_apply', dopF] at h1 ⊢
      rw [h1, hd, hGdef]
      simp only [statP, dopF]
      rw [sub_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [descPochhammer_succ_eval, show e s - ((k + 1 : ℕ) : ℝ) = e s - k - 1 by push_cast; ring]
      push_cast
      field_simp
  -- the final bound
  obtain ⟨S, hS, hk⟩ := hEk k 0
  obtain ⟨δ₁, C₂, hδ₁, hb⟩ := hk.bound_of_dvd hS
  set r := e N - k
  set mr := min ((ps 0 / 2) ^ r) ((2 * ps 0) ^ r)
  have hmr : 0 < mr := lt_min (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (((hEG k).and hfpos).and (hfr.and hτ))
  have hu' : a < u := hu
  refine ⟨min δ₁ (u - a), C₂ / mr, lt_min hδ₁ (by linarith), fun t ht => ?_⟩
  have ht1 : t < a + δ₁ := ht.2.trans_le (by linarith [min_le_left δ₁ (u - a)])
  have ht2 : t < u := by linarith [ht.2, min_le_right δ₁ (u - a)]
  obtain ⟨⟨hEGt, hft⟩, hfrt, hτt⟩ := hus ⟨ht.1, ht2⟩
  have hbt := hb t ⟨ht.1, ht1⟩
  rw [hEGt] at hbt
  have hC₂ : 0 ≤ C₂ := by
    have := (norm_nonneg _).trans hbt
    exact (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hτt _)).mp this
  have hμr : μ * r = c - k * μ + N := by
    simp only [r, hedef, spExp, hcdef]; field_simp; ring
  have hvr : v t ^ r = f₁ t ^ r * (t - a) ^ (c - k * μ + N) := by rw [hvpow t hτt hft, hμr]
  have hfm := (hrange r (f₁ t) hfrt.1 hfrt.2).1
  calc _ = ‖G k t‖ := rfl
    _ ≤ C₂ * (t - a) ^ (c - k * μ + N) := hbt
    _ ≤ C₂ * (v t ^ r / mr) := by
        rw [hvr]
        gcongr
        rw [le_div_iff₀ hmr]
        calc (t - a) ^ (c - k * μ + N) * mr ≤ (t - a) ^ (c - k * μ + N) * f₁ t ^ r := by
              gcongr
          _ = _ := by ring
    _ = _ := by ring

end Azurite.DLMF
