/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Interpolatory

/-!
# DLMF §3.5(v): Gauss quadrature, orthogonal polynomials and their zeros

* The setting (§18.2(i)): `IsGaussWeight` (a positive weight `w` on a finite or infinite open
  interval `I` with finite moments), `wInt` (`∫_I p w`), its linearity, `wInt_pos` and
  `wInt_mul_self_pos` (positivity on nonzero polynomials `≥ 0` on `I`).
* Monic orthogonal polynomials: `IsOrthMonic`, `exists_isOrthMonic` (the moment matrix is
  positive definite), `IsOrthMonic.unique`.
* Zeros: `IsOrthMonic.roots_spec` (`p_n` has `n` simple zeros, all in `I`; via
  `eval_nonneg_or_nonpos_of_even`: a polynomial whose zeros in `I` have even multiplicity does not
  change sign on `I`), `IsOrthMonic.eq_nodal`.
* 3.5.18: `christoffel` (the Christoffel numbers as printed), `christoffel_eq_wInt_basis`
  (`wₖ = ∫_I ℓₖ w`, so Gauss quadrature is 3.5.15 with the zeros of `p_n` as nodes),
  `christoffel_pos` (`wₖ = ∫_I ℓₖ² w > 0`).
* 3.5.20: `gaussGamma` (`γ_n = ∫_I p_n² w`), `gaussGamma_eq_div` (`γ_n = h_n/k_n²`).
* 3.5.20_1: `dlmf_3_5_20_1` (exact for degree `≤ 2n − 1`, by division by `p_n`).
* 3.5.20_2: `dlmf_3_5_20_2` (discrete orthogonality of `p₀, …, p_{n−1}` on the nodes).
* The remainder 3.5.19 is in `Section5GaussError`.
-/

open Polynomial Finset Set MeasureTheory

namespace Azurite.DLMF

/-- A positive weight function `w` on a (finite or infinite) open interval `I`, with all moments
`∫_I xᵏ w(x) dx` finite. -/
structure IsGaussWeight (I : Set ℝ) (w : ℝ → ℝ) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  nonempty : I.Nonempty
  pos : ∀ x ∈ I, 0 < w x
  integrableOn : ∀ k : ℕ, IntegrableOn (fun x => x ^ k * w x) I

/-- `∫_I p(x) w(x) dx` for a polynomial `p`. -/
noncomputable def wInt (I : Set ℝ) (w : ℝ → ℝ) (p : ℝ[X]) : ℝ := ∫ x in I, p.eval x * w x

variable {I : Set ℝ} {w : ℝ → ℝ}

theorem IsGaussWeight.integrableOn_eval (hw : IsGaussWeight I w) (p : ℝ[X]) :
    IntegrableOn (fun x => p.eval x * w x) I := by
  simp_rw [eval_eq_sum_range, sum_mul]
  exact integrable_finsetSum _ fun i _ => by
    simpa [mul_assoc] using (hw.integrableOn i).const_mul (p.coeff i)

theorem wInt_add (hw : IsGaussWeight I w) (p q : ℝ[X]) :
    wInt I w (p + q) = wInt I w p + wInt I w q := by
  simp only [wInt, eval_add, add_mul]
  exact integral_add (hw.integrableOn_eval p) (hw.integrableOn_eval q)

theorem wInt_C_mul (c : ℝ) (p : ℝ[X]) : wInt I w (C c * p) = c * wInt I w p := by
  simp only [wInt, eval_mul, eval_C, mul_assoc]
  exact integral_const_mul c _

theorem wInt_neg (p : ℝ[X]) : wInt I w (-p) = -wInt I w p := by
  simp only [wInt, eval_neg, neg_mul]
  exact integral_neg _

theorem wInt_sub (hw : IsGaussWeight I w) (p q : ℝ[X]) :
    wInt I w (p - q) = wInt I w p - wInt I w q := by
  rw [sub_eq_add_neg, wInt_add hw, wInt_neg, sub_eq_add_neg]

theorem wInt_sum (hw : IsGaussWeight I w) {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    wInt I w (∑ i ∈ s, f i) = ∑ i ∈ s, wInt I w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wInt]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, wInt_add hw, ih]

theorem wInt_zero : wInt I w 0 = 0 := by simp [wInt]

/-- `∫_I p w > 0` for a nonzero polynomial `p ≥ 0` on `I`. -/
theorem wInt_pos (hw : IsGaussWeight I w) {p : ℝ[X]} (hp0 : p ≠ 0)
    (hnn : ∀ x ∈ I, 0 ≤ p.eval x) : 0 < wInt I w p := by
  classical
  have hf : 0 ≤ᵐ[volume.restrict I] fun x => p.eval x * w x :=
    (ae_restrict_iff' hw.isOpen.measurableSet).mpr (Filter.Eventually.of_forall fun x hx =>
      mul_nonneg (hnn x hx) (hw.pos x hx).le)
  rw [wInt, setIntegral_pos_iff_support_of_nonneg_ae hf (hw.integrableOn_eval p)]
  have hZ : volume ((p.roots.toFinset : Set ℝ)) = 0 := (Finset.finite_toSet _).measure_zero _
  have hI : 0 < volume I := hw.isOpen.measure_pos volume hw.nonempty
  calc 0 < volume I := hI
    _ = volume (I \ (p.roots.toFinset : Set ℝ)) := (measure_sdiff_null hZ).symm
    _ ≤ volume (Function.support (fun x => p.eval x * w x) ∩ I) := by
        refine measure_mono fun x hx => ⟨?_, hx.1⟩
        have hroot : p.eval x ≠ 0 := fun h => hx.2 (by
          simp only [Finset.mem_coe, Multiset.mem_toFinset]; exact (mem_roots hp0).mpr h)
        exact mul_ne_zero hroot (hw.pos x hx.1).ne'

theorem wInt_mul_self_pos (hw : IsGaussWeight I w) {p : ℝ[X]} (hp0 : p ≠ 0) :
    0 < wInt I w (p * p) :=
  wInt_pos hw (mul_ne_zero hp0 hp0) fun x _ => by rw [eval_mul]; exact mul_self_nonneg _

/-- A nonzero polynomial whose zeros in an interval `I` all have even multiplicity does not
change sign on `I`. -/
theorem eval_nonneg_or_nonpos_of_even {r : ℝ[X]} (hI : I.OrdConnected) (hr : r ≠ 0)
    (heven : ∀ z ∈ I, Even (r.roots.count z)) :
    (∀ t ∈ I, 0 ≤ r.eval t) ∨ (∀ t ∈ I, r.eval t ≤ 0) := by
  classical
  set R := r.roots.filter (· ∈ I)
  set Q := (R.map fun a => X - C a).prod
  obtain ⟨s, hs⟩ : Q ∣ r := (Multiset.prod_dvd_prod_of_le
    (Multiset.map_le_map (Multiset.filter_le _ _))).trans (prod_multiset_X_sub_C_dvd r)
  have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact hr hs
  have hsroot : ∀ z ∈ I, s.eval z ≠ 0 := by
    intro z hz h0
    have hc := congrArg (Multiset.count z) (congrArg roots hs)
    rw [roots_mul (hs ▸ hr), roots_multiset_prod_X_sub_C, Multiset.count_add,
      Multiset.count_filter_of_pos hz] at hc
    have : 0 < s.roots.count z := Multiset.count_pos.mpr ((mem_roots hs0).mpr h0)
    omega
  have hQnn : ∀ t, 0 ≤ Q.eval t := by
    intro t
    rw [eval_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    refine Finset.prod_nonneg fun z hz => ?_
    have hzI : z ∈ I := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hz)).2
    rw [Multiset.count_filter_of_pos hzI]
    exact (heven z hzI).pow_nonneg _
  by_cases h : ∃ u ∈ I, 0 < s.eval u
  · left
    obtain ⟨u, hu, hpos⟩ := h
    intro t ht
    have : 0 < s.eval t := by
      by_contra hneg
      push Not at hneg
      obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (s.continuous.continuousOn (s := uIcc u t))
        (Set.mem_uIcc.mpr (Or.inr ⟨hneg, hpos.le⟩))
      exact hsroot c (hI.uIcc_subset hu ht hc) hc0
    rw [hs, eval_mul]
    exact mul_nonneg (hQnn t) this.le
  · right
    push Not at h
    intro t ht
    rw [hs, eval_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hQnn t) (h t ht)

/-! ### Monic orthogonal polynomials -/

/-- `p` is the monic polynomial of degree `n` orthogonal (with respect to `w` on `I`) to every
polynomial of lower degree. -/
def IsOrthMonic (I : Set ℝ) (w : ℝ → ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = n ∧ ∀ q : ℝ[X], q.degree < n → wInt I w (p * q) = 0

theorem IsOrthMonic.wInt_mul_eq_zero {n : ℕ} {p : ℝ[X]} (hp : IsOrthMonic I w n p) {q : ℝ[X]}
    (hq : q.degree < n) : wInt I w (p * q) = 0 := hp.2.2 q hq

/-- Uniqueness of the monic orthogonal polynomial of degree `n`. -/
theorem IsOrthMonic.unique (hw : IsGaussWeight I w) {n : ℕ} {p p' : ℝ[X]}
    (hp : IsOrthMonic I w n p) (hp' : IsOrthMonic I w n p') : p = p' := by
  by_contra hne
  have hd0 : p - p' ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p - p').degree < n := by
    have := degree_sub_lt_left (p := p) (q := p')
      (by rw [degree_eq_natDegree hp.1.ne_zero, degree_eq_natDegree hp'.1.ne_zero, hp.2.1,
        hp'.2.1]) hp.1.ne_zero (by rw [hp.1.leadingCoeff, hp'.1.leadingCoeff])
    rwa [degree_eq_natDegree hp.1.ne_zero, hp.2.1] at this
  have h := wInt_mul_self_pos hw hd0
  rw [show (p - p') * (p - p') = p * (p - p') - p' * (p - p') by ring, wInt_sub hw,
    hp.wInt_mul_eq_zero hdeg, hp'.wInt_mul_eq_zero hdeg, sub_zero] at h
  exact lt_irrefl _ h

/-- Existence of the monic orthogonal polynomial of degree `n` (the moment matrix is positive
definite, hence invertible). -/
theorem exists_isOrthMonic (hw : IsGaussWeight I w) (n : ℕ) : ∃ p, IsOrthMonic I w n p := by
  let rc : (Fin n → ℝ) → ℝ[X] := fun c => ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  let M : Matrix (Fin n) (Fin n) ℝ := fun j i => wInt I w (X ^ (i : ℕ) * X ^ (j : ℕ))
  have hrc : ∀ c (q : ℝ[X]), wInt I w (rc c * q) = ∑ i, c i * wInt I w (X ^ (i : ℕ) * q) := by
    intro c q
    simp only [rc, sum_mul, wInt_sum hw, mul_assoc, wInt_C_mul]
  have hMc : ∀ c j, (M.mulVecLin c) j = ∑ i, c i * wInt I w (X ^ (i : ℕ) * X ^ (j : ℕ)) :=
    fun c j => by
      change ∑ i, M j i * c i = _
      exact sum_congr rfl fun i _ => mul_comm (M j i) (c i)
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : wInt I w (rc c * rc c) = 0 := by
      rw [hrc]
      refine sum_eq_zero fun i _ => ?_
      rw [mul_comm (X ^ (i : ℕ)), hrc, ← hMc, hc]
      simp
    have hr0 : rc c = 0 := by
      by_contra h
      exact (wInt_mul_self_pos hw h).ne' h0
    funext i
    have := congrArg (fun q : ℝ[X] => q.coeff i) hr0
    simpa [rc, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using this
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.mp hinj
    (fun j => wInt I w (X ^ n * X ^ (j : ℕ)))
  have hdeg : (rc c).degree < n := degree_sum_fin_lt _
  have hdegp : (X ^ n - rc c).degree = (n : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  refine ⟨X ^ n - rc c, monic_X_pow_sub hdeg, natDegree_eq_of_degree_eq_some hdegp, ?_⟩
  have key : ∀ j < n, wInt I w ((X ^ n - rc c) * X ^ j) = 0 := fun j hj => by
    rw [sub_mul, wInt_sub hw, hrc]
    have := congrFun hc ⟨j, hj⟩
    rw [hMc] at this
    rw [this, sub_self]
  intro q hq
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, wInt_zero]
  rw [as_sum_range' q n ((natDegree_lt_iff_degree_lt hq0).mpr hq), mul_sum, wInt_sum hw]
  refine sum_eq_zero fun j hj => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, wInt_C_mul, key j (mem_range.mp hj), mul_zero]

/-! ### The zeros of `p_n` -/

/-- The zeros of the monic orthogonal polynomial `p_n` are real, simple and lie in `I`:
`p_n` has `n` distinct zeros, all in `I`. -/
theorem IsOrthMonic.roots_spec (hw : IsGaussWeight I w) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic I w n p) :
    p.roots.Nodup ∧ Multiset.card p.roots = n ∧ ∀ x ∈ p.roots, x ∈ I := by
  classical
  obtain ⟨hmon, hdeg, horth⟩ := hp
  set Z := p.roots.toFinset.filter (fun z => z ∈ I ∧ Odd (p.roots.count z))
  set q : ℝ[X] := ∏ z ∈ Z, (X - C z)
  have hq0 : q ≠ 0 := (monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z).ne_zero
  have hp0 := hmon.ne_zero
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  have heven : ∀ z ∈ I, Even ((p * q).roots.count z) := by
    intro z hz
    rw [roots_mul hpq0, Multiset.count_add, roots_prod_X_sub_C]
    rcases Nat.even_or_odd (p.roots.count z) with he | ho
    · have : z ∉ Z := fun h => Nat.not_odd_iff_even.mpr he (Finset.mem_filter.mp h).2.2
      rw [Multiset.count_eq_zero.mpr this, add_zero]
      exact he
    · have hmem : z ∈ Z := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
        (Multiset.count_pos.mp ho.pos), hz, ho⟩
      rw [Multiset.count_eq_one_of_mem Z.nodup hmem]
      exact ho.add_one
  have hne : wInt I w (p * q) ≠ 0 := by
    rcases eval_nonneg_or_nonpos_of_even hw.ordConnected hpq0 heven with h | h
    · exact (wInt_pos hw hpq0 h).ne'
    · have := wInt_pos hw (neg_ne_zero.mpr hpq0) fun x hx => by
        rw [eval_neg]; exact neg_nonneg.mpr (h x hx)
      rw [wInt_neg] at this
      linarith
  have hqdeg : q.natDegree = #Z := by
    rw [natDegree_prod_of_monic _ _ fun z _ => monic_X_sub_C z]
    simp
  have hZ : n ≤ #Z := by
    by_contra hlt
    push Not at hlt
    exact hne (horth q (by rw [degree_eq_natDegree hq0, hqdeg]; exact_mod_cast hlt))
  have h1 : #Z ≤ #p.roots.toFinset := card_le_card (filter_subset _ _)
  have h2 := Multiset.toFinset_card_le (m := p.roots)
  have h3 := card_roots' p
  have hcard : Multiset.card p.roots = n := by omega
  have hnodup : p.roots.Nodup := Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega)
  have hZeq : Z = p.roots.toFinset := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  refine ⟨hnodup, hcard, fun x hx => ?_⟩
  have : x ∈ Z := hZeq ▸ Multiset.mem_toFinset.mpr hx
  exact (Finset.mem_filter.mp this).2.1

/-- With `s` the set of zeros, `p_n = ∏_{x ∈ s} (x − xₖ)` (Mathlib's `Lagrange.nodal`). -/
theorem IsOrthMonic.eq_nodal (hw : IsGaussWeight I w) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic I w n p) : p = Lagrange.nodal p.roots.toFinset id := by
  classical
  obtain ⟨hnodup, hcard, -⟩ := hp.roots_spec hw
  rw [Lagrange.nodal_eq, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnodup]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp.1 (by rw [hcard, hp.2.1])).symm

/-! ### Gauss quadrature 3.5.18–3.5.20 -/

/-- **DLMF 3.5.18**: the Christoffel numbers
`wₖ = ∫_I p_n(x)/((x − xₖ) p_n′(xₖ)) w(x) dx`. -/
noncomputable def christoffel (I : Set ℝ) (w : ℝ → ℝ) (p : ℝ[X]) (xk : ℝ) : ℝ :=
  ∫ x in I, p.eval x / ((x - xk) * (derivative p).eval xk) * w x

/-- The Christoffel numbers are the interpolatory weights `∫_I ℓₖ w` (3.5.15 with the zeros of
`p_n` as nodes). -/
theorem christoffel_eq_wInt_basis (hw : IsGaussWeight I w) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic I w n p) {xk : ℝ} (hk : xk ∈ p.roots.toFinset) :
    christoffel I w p xk = wInt I w (Lagrange.basis p.roots.toFinset id xk) := by
  classical
  have hnod := hp.eq_nodal hw
  have hae : ∀ᵐ x ∂(volume.restrict I), x ≠ xk :=
    ae_restrict_of_ae ((Set.countable_singleton xk).ae_notMem volume)
  refine integral_congr_ae (hae.mono fun x hx => ?_)
  simp only
  rw [Lagrange.eval_basis_not_at_node hk hx, Lagrange.nodalWeight_eq_eval_derivative_nodal hk,
    ← hnod, id, div_eq_mul_inv, mul_inv]
  ring

/-- **DLMF 3.5.20_1**: the Gauss rule is exact for every polynomial of degree `≤ 2n − 1`. -/
theorem dlmf_3_5_20_1 (hw : IsGaussWeight I w) {n : ℕ} {p : ℝ[X]} (hp : IsOrthMonic I w n p)
    {f : ℝ[X]} (hf : f.degree < (2 * n : ℕ)) :
    wInt I w f = ∑ k ∈ p.roots.toFinset, christoffel I w p k * f.eval k := by
  classical
  have hmon := hp.1
  obtain ⟨hnodup, hcard, -⟩ := hp.roots_spec hw
  set q := f /ₘ p
  set r := f %ₘ p
  have hq : q.degree < n := by
    by_cases hq0 : q = 0
    · rw [hq0, degree_zero]; exact WithBot.bot_lt_coe _
    have hf0 : f ≠ 0 := by rintro rfl; exact hq0 (zero_divByMonic p)
    have hfn : f.natDegree < 2 * n := (natDegree_lt_iff_degree_lt hf0).mpr hf
    rw [degree_eq_natDegree hq0, natDegree_divByMonic f hmon, hp.2.1]
    exact_mod_cast (by omega : f.natDegree - n < n)
  have hr : r.degree < #p.roots.toFinset := by
    rw [Multiset.toFinset_card_of_nodup hnodup, hcard, ← hp.2.1,
      ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt f hmon
  have hsplit : f = r + p * q := (modByMonic_add_div f p).symm
  have hinj : Set.InjOn (id : ℝ → ℝ) (p.roots.toFinset : Set ℝ) := Function.injective_id.injOn
  have hrint : r = Lagrange.interpolate p.roots.toFinset id (fun k => r.eval k) :=
    Lagrange.eq_interpolate hinj hr
  have hval : ∀ k ∈ p.roots.toFinset, f.eval k = r.eval k := fun k hk => by
    have : p.eval k = 0 := (mem_roots hmon.ne_zero).mp (Multiset.mem_toFinset.mp hk)
    conv_lhs => rw [hsplit]
    rw [eval_add, eval_mul, this, zero_mul, add_zero]
  rw [sum_congr rfl fun k hk => by rw [hval k hk, christoffel_eq_wInt_basis hw hp hk]]
  conv_lhs => rw [hsplit]
  rw [wInt_add hw, hp.wInt_mul_eq_zero hq, add_zero]
  conv_lhs => rw [hrint]
  rw [Lagrange.interpolate_apply, wInt_sum hw]
  exact sum_congr rfl fun k _ => by rw [wInt_C_mul, mul_comm]

/-- The Christoffel numbers are positive: `wₖ = ∫_I ℓₖ² w > 0`. -/
theorem christoffel_pos (hw : IsGaussWeight I w) {n : ℕ} {p : ℝ[X]} (hp : IsOrthMonic I w n p)
    {xk : ℝ} (hk : xk ∈ p.roots.toFinset) : 0 < christoffel I w p xk := by
  classical
  obtain ⟨hnodup, hcard, -⟩ := hp.roots_spec hw
  set s := p.roots.toFinset
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Function.injective_id.injOn
  set ℓ := Lagrange.basis s id xk
  have hℓ0 : ℓ ≠ 0 := Lagrange.basis_ne_zero hinj hk
  have hs : #s = n := by rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
  have hdeg : (ℓ * ℓ).degree < (2 * n : ℕ) := by
    rw [degree_mul, Lagrange.degree_basis hinj hk, hs]
    have : 0 < n := hs ▸ card_pos.mpr ⟨xk, hk⟩
    norm_cast
    omega
  have h := dlmf_3_5_20_1 hw hp hdeg
  rw [sum_eq_single_of_mem xk hk fun j hj hjk => by
    rw [eval_mul, show ℓ.eval j = 0 from Lagrange.eval_basis_of_ne (v := id) hjk.symm hj, zero_mul,
      mul_zero]] at h
  rw [eval_mul, show ℓ.eval xk = 1 from Lagrange.eval_basis_self hinj hk, mul_one, mul_one] at h
  rw [← h]
  exact wInt_mul_self_pos hw hℓ0

/-- **DLMF 3.5.20**: `γ_n = ∫_I p_n² w`. -/
noncomputable def gaussGamma (I : Set ℝ) (w : ℝ → ℝ) (p : ℝ[X]) : ℝ := wInt I w (p * p)

/-- **DLMF 3.5.20_2**: `p₀, …, p_{n−1}` are orthogonal on the nodes `x₁, …, xₙ` (the zeros of
`p_n`) with respect to the Christoffel numbers: `∑ₖ p_ℓ(xₖ) p_m(xₖ) wₖ = h_m δ_{ℓ,m}`,
`h_m = ∫_I p_m² w`. -/
theorem dlmf_3_5_20_2 (hw : IsGaussWeight I w) {P : ℕ → ℝ[X]}
    (hP : ∀ m, IsOrthMonic I w m (P m)) (n : ℕ) {l m : ℕ} (hl : l < n) (hm : m < n) :
    ∑ k ∈ (P n).roots.toFinset, (P l).eval k * (P m).eval k * christoffel I w (P n) k =
      if l = m then wInt I w (P m * P m) else 0 := by
  have hdeg : (P l * P m).degree < (2 * n : ℕ) := by
    rw [degree_mul, degree_eq_natDegree (hP l).1.ne_zero, degree_eq_natDegree (hP m).1.ne_zero,
      (hP l).2.1, (hP m).2.1]
    norm_cast
    omega
  have h := dlmf_3_5_20_1 hw (hP n) hdeg
  rw [sum_congr rfl fun k _ => by rw [mul_comm, ← eval_mul], ← h]
  split_ifs with hlm
  · rw [hlm]
  · rcases lt_or_gt_of_ne hlm with hlt | hlt
    · rw [mul_comm]
      exact (hP m).wInt_mul_eq_zero (by
        rw [degree_eq_natDegree (hP l).1.ne_zero, (hP l).2.1]; exact_mod_cast hlt)
    · exact (hP l).wInt_mul_eq_zero (by
        rw [degree_eq_natDegree (hP m).1.ne_zero, (hP m).2.1]; exact_mod_cast hlt)

/-- `γ_n = h_n/k_n²` for an orthogonal polynomial `P = k_n p_n` with leading coefficient `k_n` and
`h_n = ∫_I P² w`. -/
theorem gaussGamma_eq_div {p : ℝ[X]} {k : ℝ} (hk : k ≠ 0) :
    gaussGamma I w p = wInt I w (C k * p * (C k * p)) / k ^ 2 := by
  rw [show C k * p * (C k * p) = C (k ^ 2) * (p * p) by rw [C_pow]; ring, wInt_C_mul,
    gaussGamma]
  field_simp

end Azurite.DLMF
