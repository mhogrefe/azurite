/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Derivation
import Azurite.Chudnovsky.PairMeasure
import Azurite.Feldman.Auxiliary

/-!
# Numbers of the form `A(ϖ, e) + τ A′(ϖ, e)` with controlled size

`Rep ϖ e τ d B x`: `x = A(ϖ, e) + τ A′(ϖ, e)` with `A, A′ ∈ ℤ[X, Y]` of total degree `≤ d` and
`ℓ¹`-norm `≤ B/3` (the normalization makes the bound multiplicative, `Rep.mul`, when
`τ² = pτ − q`, `|p|, |q| ≤ 1`).  Values of integer polynomials at points with such
coordinates are of this form (`Rep_aeval`), and a pair measure gives the dichotomy
`x = 0 ∨ |x| ≥ 2^(−c T² (size T)³)` (`Rep.dichotomy`).
-/

namespace Azurite.Chudnovsky

open MvPolynomial Azurite.Feldman

/-- The point `(ϖ, e)`. -/
noncomputable def pt2 (ϖ e : ℂ) : Fin 2 → ℂ := ![ϖ, e]

/-- `x = A(ϖ, e) + τ A′(ϖ, e)` with `deg A, deg A′ ≤ d` and `‖A‖₁, ‖A′‖₁ ≤ B/3`. -/
def Rep (ϖ e τ : ℂ) (d : ℕ) (B : ℝ) (x : ℂ) : Prop :=
  ∃ A A' : MvPolynomial (Fin 2) ℤ, A.totalDegree ≤ d ∧ A'.totalDegree ≤ d ∧ ml1 A ≤ B / 3 ∧
    ml1 A' ≤ B / 3 ∧ x = aeval (pt2 ϖ e) A + τ * aeval (pt2 ϖ e) A'

variable {ϖ e τ : ℂ}

theorem Rep.nonneg {d : ℕ} {B : ℝ} {x : ℂ} (h : Rep ϖ e τ d B x) : 0 ≤ B := by
  obtain ⟨A, -, -, -, hA, -, -⟩ := h
  have := ml1_nonneg A
  linarith

theorem Rep.mono {d d' : ℕ} {B B' : ℝ} {x : ℂ} (h : Rep ϖ e τ d B x) (hd : d ≤ d')
    (hB : B ≤ B') : Rep ϖ e τ d' B' x := by
  obtain ⟨A, A', h1, h2, h3, h4, h5⟩ := h
  exact ⟨A, A', h1.trans hd, h2.trans hd, by linarith, by linarith, h5⟩

theorem Rep.zero (d : ℕ) {B : ℝ} (hB : 0 ≤ B) : Rep ϖ e τ d B 0 :=
  ⟨0, 0, by simp, by simp, by simpa using div_nonneg hB (by norm_num),
    by simpa using div_nonneg hB (by norm_num), by simp⟩

theorem Rep.add {d₁ d₂ : ℕ} {B₁ B₂ : ℝ} {x y : ℂ} (hx : Rep ϖ e τ d₁ B₁ x)
    (hy : Rep ϖ e τ d₂ B₂ y) : Rep ϖ e τ (max d₁ d₂) (B₁ + B₂) (x + y) := by
  obtain ⟨A, A', h1, h2, h3, h4, rfl⟩ := hx
  obtain ⟨C, C', k1, k2, k3, k4, rfl⟩ := hy
  refine ⟨A + C, A' + C', ?_, ?_, ?_, ?_, ?_⟩
  · exact (totalDegree_add _ _).trans (max_le_max h1 k1)
  · exact (totalDegree_add _ _).trans (max_le_max h2 k2)
  · have := ml1_add_le A C
    linarith
  · have := ml1_add_le A' C'
    linarith
  · simp only [map_add]
    ring

theorem Rep.sum {ι : Type*} (s : Finset ι) {d : ℕ} {B : ι → ℝ} {x : ι → ℂ}
    (h : ∀ i ∈ s, Rep ϖ e τ d (B i) (x i)) : Rep ϖ e τ d (∑ i ∈ s, B i) (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep.zero d le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).mono (by simp) le_rfl

theorem Rep.int_mul {d : ℕ} {B : ℝ} {x : ℂ} (hx : Rep ϖ e τ d B x) (n : ℤ) :
    Rep ϖ e τ d (|(n : ℝ)| * B) (n * x) := by
  obtain ⟨A, A', h1, h2, h3, h4, rfl⟩ := hx
  refine ⟨n • A, n • A', (totalDegree_smul_le _ _).trans h1, (totalDegree_smul_le _ _).trans h2,
    ?_, ?_, ?_⟩
  · refine (ml1_smul_le n A).trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  · refine (ml1_smul_le n A').trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  · rw [map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
    ring

/-- **The bound is multiplicative.** -/
theorem Rep.mul {p q : ℤ} (hsq : τ ^ 2 = p * τ - q) (hp : |p| ≤ 1) (hq : |q| ≤ 1) {d₁ d₂ : ℕ}
    {B₁ B₂ : ℝ} {x y : ℂ} (hx : Rep ϖ e τ d₁ B₁ x) (hy : Rep ϖ e τ d₂ B₂ y) :
    Rep ϖ e τ (d₁ + d₂) (B₁ * B₂) (x * y) := by
  obtain ⟨A, A', h1, h2, h3, h4, rfl⟩ := hx
  obtain ⟨C, C', k1, k2, k3, k4, rfl⟩ := hy
  have hpR : |(p : ℝ)| ≤ 1 := by exact_mod_cast hp
  have hqR : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have a0 := ml1_nonneg A
  have a0' := ml1_nonneg A'
  have c0 := ml1_nonneg C
  have c0' := ml1_nonneg C'
  have hd : ∀ {P R : MvPolynomial (Fin 2) ℤ}, P.totalDegree ≤ d₁ → R.totalDegree ≤ d₂ →
      (P * R).totalDegree ≤ d₁ + d₂ := fun hP hR =>
    (totalDegree_mul _ _).trans (add_le_add hP hR)
  have hm : ∀ {P R : MvPolynomial (Fin 2) ℤ}, ml1 P ≤ B₁ / 3 → ml1 R ≤ B₂ / 3 →
      ml1 (P * R) ≤ B₁ * B₂ / 9 := fun {P R} hP hR => by
    refine (ml1_mul_le P R).trans ?_
    have := mul_le_mul hP hR (ml1_nonneg R) (by linarith [ml1_nonneg P])
    linarith
  have hB : 0 ≤ B₁ * B₂ / 9 := (ml1_nonneg _).trans (hm h3 k3)
  refine ⟨A * C - q • (A' * C'), A * C' + A' * C + p • (A' * C'), ?_, ?_, ?_, ?_, ?_⟩
  · exact (totalDegree_sub _ _).trans
      (max_le (hd h1 k1) ((totalDegree_smul_le _ _).trans (hd h2 k2)))
  · exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (hd h1 k2) (hd h2 k1))) ((totalDegree_smul_le _ _).trans (hd h2 k2)))
  · have e1 : A * C - q • (A' * C') = A * C + (-q) • (A' * C') := by
      rw [neg_smul, sub_eq_add_neg]
    rw [e1]
    refine (ml1_add_le _ _).trans ?_
    have s1 := ml1_smul_le (-q) (A' * C')
    push_cast at s1
    rw [abs_neg] at s1
    have s2 := hm h4 k4
    have s3 := hm h3 k3
    nlinarith [ml1_nonneg (A' * C')]
  · refine (ml1_add_le _ _).trans ?_
    have s0 := ml1_add_le (A * C') (A' * C)
    have s1 := ml1_smul_le p (A' * C')
    have s2 := hm h4 k4
    have s3 := hm h3 k4
    have s4 := hm h4 k3
    nlinarith [ml1_nonneg (A' * C')]
  · simp only [map_sub, map_add, map_mul, map_zsmul]
    simp only [zsmul_eq_mul]
    linear_combination (aeval (pt2 ϖ e) A' * aeval (pt2 ϖ e) C') * hsq

/-- Direct representations. -/
theorem Rep.of_pair (A A' : MvPolynomial (Fin 2) ℤ) {d : ℕ} {B : ℝ} (h1 : A.totalDegree ≤ d)
    (h2 : A'.totalDegree ≤ d) (h3 : 3 * ml1 A ≤ B) (h4 : 3 * ml1 A' ≤ B) :
    Rep ϖ e τ d B (aeval (pt2 ϖ e) A + τ * aeval (pt2 ϖ e) A') :=
  ⟨A, A', h1, h2, by linarith, by linarith, rfl⟩

theorem Rep.one : Rep ϖ e τ 0 3 1 := by
  have h := Rep.of_pair (ϖ := ϖ) (e := e) (τ := τ) (C 1) 0 (d := 0) (B := 3) (by simp) (by simp)
    (by
      have h1 : ml1 (C 1 : MvPolynomial (Fin 2) ℤ) ≤ 1 := by
        simpa [C_apply] using ml1_monomial_le (σ := Fin 2) 0 1
      linarith) (by simp)
  simpa using h

theorem Rep.pow_mul {p q : ℤ} (hsq : τ ^ 2 = p * τ - q) (hp : |p| ≤ 1) (hq : |q| ≤ 1) {B : ℝ}
    {x : ℂ} (hx : Rep ϖ e τ 1 B x) {d n : ℕ} {P : ℂ} (hP : Rep ϖ e τ d (3 * B ^ n) P) (k : ℕ) :
    Rep ϖ e τ (d + k) (3 * B ^ (n + k)) (x ^ k * P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have := hx.mul hsq hp hq ih
    have e1 : x ^ (k + 1) * P = x * (x ^ k * P) := by ring
    rw [e1]
    refine this.mono (by omega : 1 + (d + k) ≤ d + (k + 1)) (le_of_eq ?_)
    rw [← add_assoc, pow_succ]
    ring

theorem Rep.prod_pow {p q : ℤ} (hsq : τ ^ 2 = p * τ - q) (hp : |p| ≤ 1) (hq : |q| ≤ 1) {B : ℝ}
    {ι : Type*} {x : ι → ℂ} (hx : ∀ i, Rep ϖ e τ 1 B (x i)) (s : ι → ℕ) (I : Finset ι) :
    Rep ϖ e τ (∑ i ∈ I, s i) (3 * B ^ (∑ i ∈ I, s i)) (∏ i ∈ I, x i ^ s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using Rep.one
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have := (hx a).pow_mul hsq hp hq ih (s a)
    rw [add_comm (s a)]
    exact this

/-- **Values of integer polynomials** at points with representable coordinates. -/
theorem Rep_aeval {p q : ℤ} (hsq : τ ^ 2 = p * τ - q) (hp : |p| ≤ 1) (hq : |q| ≤ 1) {B : ℝ}
    (hB : 1 ≤ B) {σ : Type*} [Fintype σ] {x : σ → ℂ} (hx : ∀ i, Rep ϖ e τ 1 B (x i))
    (Q : MvPolynomial σ ℤ) {d : ℕ} (hd : Q.totalDegree ≤ d) :
    Rep ϖ e τ d (3 * (ml1 Q * B ^ d)) (aeval x Q) := by
  rw [aeval_def, eval₂_eq']
  have hterm : ∀ s ∈ Q.support, Rep ϖ e τ d (|(Q.coeff s : ℝ)| * (3 * B ^ d))
      (algebraMap ℤ ℂ (Q.coeff s) * ∏ i, x i ^ s i) := by
    intro s hs
    have h1 := Rep.prod_pow hsq hp hq hx (fun i => s i) Finset.univ
    have hdeg : ∑ i, s i ≤ d := by
      have := (mdeg_le_totalDegree hs).trans hd
      unfold mdeg at this
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    have h2 := (h1.mono hdeg (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB hdeg) (by norm_num))).int_mul (Q.coeff s)
    simpa using h2
  have := Rep.sum Q.support hterm
  refine this.mono le_rfl (le_of_eq ?_)
  rw [← Finset.sum_mul, ml1]
  ring

/-! ### Conversion to `ℤ[X][Y]` and the dichotomy -/

theorem Sz.sum' {ι : Type*} (s : Finset ι) {f : ι → Polynomial ℤ} {g : ℕ} {B : ι → ℝ}
    (h : ∀ i ∈ s, Sz g (B i) (f i)) : Sz g (∑ i ∈ s, B i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sz.zero g le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mdeg_fin_two (s : Fin 2 →₀ ℕ) : mdeg s = s 0 + s 1 := by
  unfold mdeg
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

theorem l1_toC_C_mul_X_pow (a : ℤ) (i : ℕ) :
    l1 (toC (Polynomial.C a * Polynomial.X ^ i)) = |(a : ℝ)| := by
  have h : toC (Polynomial.C a * Polynomial.X ^ i)
      = Polynomial.C (a : ℂ) * Polynomial.X ^ i := by simp [toC]
  rw [h, l1_C_mul, l1_X_pow, mul_one, Complex.norm_intCast]

/-- A polynomial in two variables as an element of `ℤ[X][Y]`, with its sizes. -/
theorem exists_bivariate (ϖ e : ℂ) (A : MvPolynomial (Fin 2) ℤ) :
    ∃ M : Polynomial (Polynomial ℤ), ev2 ϖ e M = aeval (pt2 ϖ e) A ∧
      M.natDegree ≤ A.totalDegree ∧ ∀ k, Sz A.totalDegree (ml1 A) (M.coeff k) := by
  classical
  refine ⟨∑ s ∈ A.support,
    Polynomial.C (Polynomial.C (A.coeff s) * Polynomial.X ^ s 0) * Polynomial.X ^ s 1,
    ?_, ?_, ?_⟩
  · rw [map_sum, aeval_def, eval₂_eq']
    refine Finset.sum_congr rfl fun s _ => ?_
    have h1 : ev2 ϖ e (Polynomial.C (Polynomial.C (A.coeff s) * Polynomial.X ^ s 0)
        * Polynomial.X ^ s 1) = evX ϖ (Polynomial.C (A.coeff s) * Polynomial.X ^ s 0)
          * e ^ s 1 := by
      unfold ev2
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_pow, Polynomial.eval₂_X]
    have h2 : evX ϖ (Polynomial.C (A.coeff s) * Polynomial.X ^ s 0)
        = (A.coeff s : ℂ) * ϖ ^ s 0 := by
      rw [evX_apply]
      simp
    rw [h1, h2, Fin.prod_univ_two]
    simp [pt2]
    ring
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := mdeg_le_totalDegree hs
    rw [mdeg_fin_two] at this
    omega
  · intro k
    rw [Polynomial.finsetSum_coeff]
    refine Sz.sum' A.support (B := fun s => |(A.coeff s : ℝ)|) fun s hs => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    · refine ⟨(Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_, (l1_toC_C_mul_X_pow _ _).le⟩
      have := mdeg_le_totalDegree hs
      rw [mdeg_fin_two] at this
      omega
    · exact Sz.zero _ (abs_nonneg _)

/-- **The dichotomy**: a representable number is zero or not too small. -/
theorem Rep.dichotomy {cst : ℕ} (hm : PairMeasure ϖ e τ cst) {d T : ℕ} {B : ℝ} {x : ℂ}
    (h : Rep ϖ e τ d B x) (hT : 1 ≤ T) (hd : d ≤ T) (hB : B / 3 ≤ 2 ^ T) :
    x = 0 ∨ 1 ≤ ‖x‖ * (2 : ℝ) ^ (cst * T ^ 2 * Nat.size T ^ 3) := by
  obtain ⟨A, A', h1, h2, h3, h4, rfl⟩ := h
  obtain ⟨M, hM, hMd, hMc⟩ := exists_bivariate ϖ e A
  obtain ⟨M', hM', hMd', hMc'⟩ := exists_bivariate ϖ e A'
  by_cases h0 : aeval (pt2 ϖ e) A + τ * aeval (pt2 ϖ e) A' = 0
  · exact Or.inl h0
  · right
    have := hm T hT M M'
      ⟨hMd.trans (h1.trans hd), fun k => (hMc k).mono (h1.trans hd) (h3.trans hB)⟩
      ⟨hMd'.trans (h2.trans hd), fun k => (hMc' k).mono (h2.trans hd) (h4.trans hB)⟩
      (by rwa [hM, hM'])
    rwa [hM, hM'] at this

end Azurite.Chudnovsky
