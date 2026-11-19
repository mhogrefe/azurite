/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Values
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Derivatives of polynomials in `z`, `℘`, `℘′`, `ζ`

Polynomials in six variables `Z, P, P′, T, Y, W` with integer coefficients stand for the
functions `Q(2z, ℘(z), ℘′(z), 2ζ(z), e, ϖ)` (`pt`); `e`, `ϖ` are constants.  When
`g₂ = 2 c e²` the derivation `dD c` — `Z ↦ 2`, `P ↦ P′`, `P′ ↦ 6P² − cY²`, `T ↦ −2P`,
`Y, W ↦ 0` — is differentiation (`hasDerivAt_aeval`, `iteratedDeriv_aeval`).

Sizes: with the `ℓ¹`-norm `ml1` of a multivariate integer polynomial (sub-multiplicative,
`ml1_mul_le`), a derivation whose values on the variables have degree `≤ 2` and norm `≤ K`
raises the total degree by at most `1` and multiplies the norm by at most `K · deg`
(`totalDegree_mkDerivation_le`, `ml1_mkDerivation_le`); iterated in
`totalDegree_iterate_le`, `ml1_iterate_le`.
-/

namespace Azurite.Chudnovsky

open MvPolynomial

/-! ### The `ℓ¹`-norm -/

section ml1

variable {σ : Type*}

/-- The sum of the absolute values of the coefficients. -/
noncomputable def ml1 (p : MvPolynomial σ ℤ) : ℝ := ∑ s ∈ p.support, |(p.coeff s : ℝ)|

theorem ml1_nonneg (p : MvPolynomial σ ℤ) : 0 ≤ ml1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem ml1_eq_sum_of_subset {p : MvPolynomial σ ℤ} {S : Finset (σ →₀ ℕ)} (h : p.support ⊆ S) :
    ml1 p = ∑ s ∈ S, |(p.coeff s : ℝ)| := by
  refine Finset.sum_subset h fun s _ hs => ?_
  rw [MvPolynomial.notMem_support_iff.mp hs]
  simp

@[simp] theorem ml1_zero : ml1 (0 : MvPolynomial σ ℤ) = 0 := by simp [ml1]

theorem ml1_add_le (p q : MvPolynomial σ ℤ) : ml1 (p + q) ≤ ml1 p + ml1 q := by
  classical
  rw [ml1_eq_sum_of_subset (MvPolynomial.support_add (p := p) (q := q)),
    ml1_eq_sum_of_subset (Finset.subset_union_left (s₂ := q.support)),
    ml1_eq_sum_of_subset (Finset.subset_union_right (s₁ := p.support)), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  push_cast
  exact abs_add_le _ _

theorem ml1_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    ml1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ml1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ml1_add_le _ _).trans (by gcongr)

theorem ml1_monomial_le (s : σ →₀ ℕ) (a : ℤ) : ml1 (monomial s a) ≤ |(a : ℝ)| := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · simp [ml1, support_monomial, ha]

theorem ml1_mul_le (p q : MvPolynomial σ ℤ) : ml1 (p * q) ≤ ml1 p * ml1 q := by
  classical
  calc ml1 (p * q)
      = ml1 (∑ s ∈ p.support, ∑ t ∈ q.support, monomial (s + t) (p.coeff s * q.coeff t)) := by
        conv_lhs => rw [p.as_sum, q.as_sum, Finset.sum_mul_sum]
        simp only [monomial_mul_monomial]
    _ ≤ ∑ s ∈ p.support, ∑ t ∈ q.support, |(p.coeff s : ℝ)| * |(q.coeff t : ℝ)| := by
        refine (ml1_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        refine (ml1_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
        refine (ml1_monomial_le _ _).trans (le_of_eq ?_)
        push_cast
        exact abs_mul _ _
    _ = ml1 p * ml1 q := by rw [ml1, ml1, Finset.sum_mul_sum]

theorem ml1_smul_le (a : ℤ) (p : MvPolynomial σ ℤ) : ml1 (a • p) ≤ |(a : ℝ)| * ml1 p := by
  rw [← C_mul']
  refine (ml1_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (ml1_nonneg p))
  exact ml1_monomial_le 0 a

/-- The degree of a monomial. -/
def mdeg (s : σ →₀ ℕ) : ℕ := s.sum fun _ e => e

theorem mdeg_le_totalDegree {p : MvPolynomial σ ℤ} {s : σ →₀ ℕ} (h : s ∈ p.support) :
    mdeg s ≤ p.totalDegree := le_totalDegree h

theorem mdeg_sub_single [DecidableEq σ] {s : σ →₀ ℕ} {i : σ} (hi : i ∈ s.support) :
    mdeg (s - Finsupp.single i 1) + 1 = mdeg s := by
  have h1 : Finsupp.single i 1 ≤ s := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have h2 : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := (tsub_add_cancel_of_le h1).symm
  conv_rhs => rw [h2]
  unfold mdeg
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

variable (f : σ → MvPolynomial σ ℤ)

/-- A derivation with values of degree `≤ 2` on the variables raises the degree by at most
one. -/
theorem totalDegree_mkDerivation_le (hf : ∀ i, (f i).totalDegree ≤ 2) (p : MvPolynomial σ ℤ) :
    (mkDerivation ℤ f p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [mkDerivation_monomial]
  refine (totalDegree_smul_le _ _).trans ?_
  rw [Finsupp.sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
  rw [smul_eq_mul]
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (monomial (s - Finsupp.single i 1) ((s i : ℕ) : ℤ)).totalDegree
      ≤ mdeg (s - Finsupp.single i 1) := totalDegree_monomial_le _ _
  have h2 := mdeg_sub_single hi
  have h3 := mdeg_le_totalDegree hs
  have h4 := hf i
  omega

/-- A derivation with values of norm `≤ K` on the variables multiplies the norm by at most
`K · deg`. -/
theorem ml1_mkDerivation_le {K : ℝ} (hK : 0 ≤ K) (hf : ∀ i, ml1 (f i) ≤ K)
    (p : MvPolynomial σ ℤ) : ml1 (mkDerivation ℤ f p) ≤ K * p.totalDegree * ml1 p := by
  classical
  have hmono : ∀ s ∈ p.support, ml1 (mkDerivation ℤ f (monomial s (p.coeff s)))
      ≤ K * p.totalDegree * |(p.coeff s : ℝ)| := by
    intro s hs
    rw [mkDerivation_monomial]
    refine (ml1_smul_le _ _).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [Finsupp.sum]
    refine (ml1_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ s.support,
        ml1 (monomial (s - Finsupp.single i 1) ((s i : ℕ) : ℤ) • f i) ≤ K * (s i : ℕ) := by
      intro i _
      rw [smul_eq_mul, mul_comm K]
      refine (ml1_mul_le _ _).trans (mul_le_mul ?_ (hf i) (ml1_nonneg _) (by positivity))
      refine (ml1_monomial_le _ _).trans (le_of_eq ?_)
      push_cast
      exact abs_of_nonneg (by positivity)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hK
    have := mdeg_le_totalDegree hs
    unfold mdeg at this
    rw [Finsupp.sum] at this
    exact_mod_cast this
  conv_lhs => rw [p.as_sum, map_sum]
  refine (ml1_sum_le _ _).trans ((Finset.sum_le_sum hmono).trans (le_of_eq ?_))
  rw [← Finset.mul_sum, ml1]

variable {f}

theorem totalDegree_iterate_le (hf : ∀ i, (f i).totalDegree ≤ 2) (p : MvPolynomial σ ℤ)
    (n : ℕ) : ((mkDerivation ℤ f)^[n] p).totalDegree ≤ p.totalDegree + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := totalDegree_mkDerivation_le f hf ((mkDerivation ℤ f)^[n] p)
    omega

theorem ml1_iterate_le {K : ℝ} (hK : 0 ≤ K) (hf : ∀ i, ml1 (f i) ≤ K)
    (hf2 : ∀ i, (f i).totalDegree ≤ 2) (p : MvPolynomial σ ℤ) (n : ℕ) :
    ml1 ((mkDerivation ℤ f)^[n] p) ≤ (K * (p.totalDegree + n : ℕ)) ^ n * ml1 p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine (ml1_mkDerivation_le f hK hf _).trans ?_
    have hdeg := totalDegree_iterate_le hf2 p n
    have h1 : K * (((mkDerivation ℤ f)^[n] p).totalDegree : ℝ)
        ≤ K * (p.totalDegree + (n + 1) : ℕ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg.trans (by omega)) hK
    have h2 : (K * (p.totalDegree + n : ℕ)) ^ n ≤ (K * (p.totalDegree + (n + 1) : ℕ)) ^ n :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : _ ≤ _)) hK) _
    calc K * ((mkDerivation ℤ f)^[n] p).totalDegree * ml1 ((mkDerivation ℤ f)^[n] p)
        ≤ K * (p.totalDegree + (n + 1) : ℕ) * ((K * (p.totalDegree + (n + 1) : ℕ)) ^ n * ml1 p) :=
          mul_le_mul h1 (ih.trans (mul_le_mul_of_nonneg_right h2 (ml1_nonneg p)))
            (ml1_nonneg _) (by positivity)
      _ = (K * (p.totalDegree + (n + 1) : ℕ)) ^ (n + 1) * ml1 p := by ring

end ml1

/-! ### The derivation of the Weierstrass functions -/

/-- The derivatives of the variables `Z, P, P′, T, Y, W`. -/
noncomputable def dGen (c : ℤ) : Fin 6 → MvPolynomial (Fin 6) ℤ :=
  ![C 2, X 2, monomial (Finsupp.single 1 2) 6 + monomial (Finsupp.single 4 2) (-c),
    monomial (Finsupp.single 1 1) (-2), 0, 0]

/-- The derivation `Z ↦ 2`, `P ↦ P′`, `P′ ↦ 6P² − cY²`, `T ↦ −2P`, `Y, W ↦ 0`. -/
noncomputable def dD (c : ℤ) :
    Derivation ℤ (MvPolynomial (Fin 6) ℤ) (MvPolynomial (Fin 6) ℤ) := mkDerivation ℤ (dGen c)

theorem totalDegree_dGen_le (c : ℤ) (i : Fin 6) : (dGen c i).totalDegree ≤ 2 := by
  have hm : ∀ (j : Fin 6) (k : ℕ) (a : ℤ), k ≤ 2 →
      (monomial (Finsupp.single j k) a).totalDegree ≤ 2 := fun j k a hk =>
    (totalDegree_monomial_le _ _).trans (by rw [Finsupp.sum_single_index rfl]; exact hk)
  fin_cases i
  · show (C 2 : MvPolynomial (Fin 6) ℤ).totalDegree ≤ 2
    rw [totalDegree_C]; omega
  · show (X 2 : MvPolynomial (Fin 6) ℤ).totalDegree ≤ 2
    rw [totalDegree_X]; omega
  · exact (totalDegree_add _ _).trans (max_le (hm _ _ _ le_rfl) (hm _ _ _ le_rfl))
  · exact hm _ _ _ (by omega)
  · show (0 : MvPolynomial (Fin 6) ℤ).totalDegree ≤ 2
    simp
  · show (0 : MvPolynomial (Fin 6) ℤ).totalDegree ≤ 2
    simp

theorem ml1_dGen_le {c : ℤ} (hc : |c| ≤ 2) (i : Fin 6) : ml1 (dGen c i) ≤ 8 := by
  have hc' : |(c : ℝ)| ≤ 2 := by exact_mod_cast hc
  fin_cases i
  · exact (ml1_monomial_le 0 2).trans (by norm_num)
  · exact (ml1_monomial_le (Finsupp.single 2 1) 1).trans (by norm_num)
  · refine (ml1_add_le _ _).trans ?_
    have h1 := ml1_monomial_le (Finsupp.single (1 : Fin 6) 2) 6
    have h2 := ml1_monomial_le (Finsupp.single (4 : Fin 6) 2) (-c)
    push_cast at h1 h2
    rw [abs_neg] at h2
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)] at h1
    linarith
  · refine (ml1_monomial_le _ _).trans ?_
    push_cast
    rw [abs_neg]
    norm_num
  · show ml1 (0 : MvPolynomial (Fin 6) ℤ) ≤ 8
    simp
  · show ml1 (0 : MvPolynomial (Fin 6) ℤ) ≤ 8
    simp

theorem totalDegree_dD_iterate_le (c : ℤ) (p : MvPolynomial (Fin 6) ℤ) (n : ℕ) :
    ((dD c)^[n] p).totalDegree ≤ p.totalDegree + n :=
  totalDegree_iterate_le (totalDegree_dGen_le c) p n

theorem ml1_dD_iterate_le {c : ℤ} (hc : |c| ≤ 2) (p : MvPolynomial (Fin 6) ℤ) (n : ℕ) :
    ml1 ((dD c)^[n] p) ≤ (8 * (p.totalDegree + n : ℕ)) ^ n * ml1 p :=
  ml1_iterate_le (by norm_num) (ml1_dGen_le hc) (totalDegree_dGen_le c) p n

variable (L : PeriodPair)

/-- The point `(2z, ℘(z), ℘′(z), 2ζ(z), e, ϖ)`. -/
noncomputable def pt (e ϖ z : ℂ) : Fin 6 → ℂ :=
  ![2 * z, L.weierstrassP z, L.derivWeierstrassP z, 2 * weierstrassZeta L z, e, ϖ]

variable {L} {e ϖ : ℂ} {c : ℤ}

theorem hasDerivAt_pt (hg : L.g₂ = 2 * c * e ^ 2) {z : ℂ} (hz : z ∉ L.lattice) (i : Fin 6) :
    HasDerivAt (fun w => pt L e ϖ w i) (aeval (pt L e ϖ z) (dGen c i)) z := by
  have hU := (isOpen_compl_lattice L).mem_nhds hz
  fin_cases i
  · show HasDerivAt (fun w => 2 * w) (aeval (pt L e ϖ z) (C 2)) z
    simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
  · show HasDerivAt L.weierstrassP (aeval (pt L e ϖ z) (X 2)) z
    have h := (L.differentiableOn_weierstrassP.differentiableAt hU).hasDerivAt
    rw [L.deriv_weierstrassP] at h
    simpa [pt] using h
  · show HasDerivAt L.derivWeierstrassP (aeval (pt L e ϖ z)
      (monomial (Finsupp.single 1 2) 6 + monomial (Finsupp.single 4 2) (-c))) z
    have h := (L.differentiableOn_derivWeierstrassP.differentiableAt hU).hasDerivAt
    rw [deriv_derivWeierstrassP L hz, hg] at h
    convert h using 1
    simp [pt, aeval_monomial]
    ring
  · show HasDerivAt (fun w => 2 * weierstrassZeta L w) (aeval (pt L e ϖ z)
      (monomial (Finsupp.single 1 1) (-2))) z
    convert (hasDerivAt_weierstrassZeta L hz).const_mul (2 : ℂ) using 1
    simp [pt, aeval_monomial]
  · show HasDerivAt (fun _ => e) (aeval (pt L e ϖ z) (0 : MvPolynomial (Fin 6) ℤ)) z
    simpa using hasDerivAt_const z e
  · show HasDerivAt (fun _ => ϖ) (aeval (pt L e ϖ z) (0 : MvPolynomial (Fin 6) ℤ)) z
    simpa using hasDerivAt_const z ϖ

/-- **`dD c` is differentiation** of `z ↦ Q(2z, ℘, ℘′, 2ζ, e, ϖ)` when `g₂ = 2ce²`. -/
theorem hasDerivAt_aeval (hg : L.g₂ = 2 * c * e ^ 2) {z : ℂ} (hz : z ∉ L.lattice)
    (Q : MvPolynomial (Fin 6) ℤ) :
    HasDerivAt (fun w => aeval (pt L e ϖ w) Q) (aeval (pt L e ϖ z) (dD c Q)) z := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have h0 : dD c (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]
      exact (dD c).map_algebraMap a
    rw [h0, map_zero]
    simpa using hasDerivAt_const z ((a : ℂ))
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have h := hp.mul (hasDerivAt_pt (ϖ := ϖ) hg hz i)
    have hD : dD c (X i) = dGen c i := mkDerivation_X _ _ _
    simp only [map_mul, aeval_X, Derivation.leibniz, map_add, smul_eq_mul, hD]
    convert h using 1
    ring

theorem iteratedDeriv_aeval (hg : L.g₂ = 2 * c * e ^ 2) (Q : MvPolynomial (Fin 6) ℤ) (n : ℕ)
    {z : ℂ} (hz : z ∉ L.lattice) :
    iteratedDeriv n (fun w => aeval (pt L e ϖ w) Q) z = aeval (pt L e ϖ z) ((dD c)^[n] Q) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, Function.iterate_succ_apply']
    have hev : iteratedDeriv n (fun w => aeval (pt L e ϖ w) Q)
        =ᶠ[nhds z] fun w => aeval (pt L e ϖ w) ((dD c)^[n] Q) := by
      filter_upwards [(isOpen_compl_lattice L).mem_nhds hz] with w hw
      exact ih hw
    rw [hev.deriv_eq]
    exact (hasDerivAt_aeval hg hz _).deriv

end Azurite.Chudnovsky
