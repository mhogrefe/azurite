/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveZeroSet
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# BPR §4.7, Lemma 4.102

An algebraic subset of `ℙ₁(C)` (one projective line, `m = 1`, `k = 1`) is either all of `ℙ₁(C)` or
finite. Equivalently, the zero set of a finite set of homogeneous polynomials in two variables over
`C = Ri R` is either everything or finite.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The vector `![0, 1]` is nonzero. -/
theorem vec01_ne_zero : (![0, 1] : Fin 2 → Ri R) ≠ 0 := by
  intro h; simpa using congrFun h 1

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The vector `![1, t]` is nonzero. -/
theorem vec1t_ne_zero (t : Ri R) : (![1, t] : Fin 2 → Ri R) ≠ 0 := by
  intro h; simpa using congrFun h 0

/-- Every point of `ℙ₁(C)` lies in one of the two standard charts: either it is `(0 : 1)` or it is
`(1 : t)` for some `t`. -/
theorem proj_line_chart (p : Projectivization (Ri R) (Fin 2 → Ri R)) :
    p = mkLine ![0, 1] vec01_ne_zero
    ∨ ∃ t : Ri R, p = mkLine ![1, t] (vec1t_ne_zero t) := by
  have hpr : mkLine p.rep p.rep_nonzero = p := Projectivization.mk_rep p
  by_cases h0 : p.rep 0 = 0
  · left
    conv_lhs => rw [← hpr]
    rw [mkLine_eq_mkLine_iff]
    refine ⟨p.rep 1, ?_, ?_⟩
    · intro hc
      apply p.rep_nonzero
      funext i; fin_cases i
      · exact h0
      · simpa using hc
    · funext i; fin_cases i
      · simp [h0]
      · simp
  · right
    refine ⟨p.rep 1 / p.rep 0, ?_⟩
    conv_lhs => rw [← hpr]
    rw [mkLine_eq_mkLine_iff]
    refine ⟨p.rep 0, h0, ?_⟩
    funext i; fin_cases i
    · simp
    · simp [smul_eq_mul, mul_div_cancel₀ _ h0]

/-- The variable index type for one block of two homogeneous coordinates `X₀, X₁`. -/
abbrev LineVar : Type := (i : Fin 1) × Fin ((fun _ => 1 : Fin 1 → ℕ) i + 1)

/-- The dehomogenization substitution `X₀ ↦ 1`, `X₁ ↦ T`, used to turn a homogeneous polynomial in
two variables into the univariate polynomial `P(1, T)`. -/
noncomputable def dehom (s : LineVar) : Polynomial (Ri R) :=
  if s.2 = 0 then (1 : Polynomial (Ri R)) else Polynomial.X

/-- The dehomogenization `P(1, T)` of a homogeneous polynomial `P` in the two homogeneous
coordinates of `ℙ₁(C)`. -/
noncomputable def dehomPoly (P : MvPolynomial LineVar (Ri R)) : Polynomial (Ri R) :=
  MvPolynomial.aeval dehom P

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Naturality.** Evaluating `P` at the affine chart point `(1 : t)` equals evaluating the
dehomogenization `P(1, T)` at `T = t`. -/
theorem evalCoords_eq_eval_dehomPoly
    (P : MvPolynomial LineVar (Ri R)) (t : Ri R) :
    evalCoords (m := 1) (k := fun _ => 1) P (fun _ => ![1, t])
      = Polynomial.eval t (dehomPoly P) := by
  rw [dehomPoly, evalCoords, ← Polynomial.coe_evalRingHom, MvPolynomial.map_aeval,
    show (eval fun s : LineVar => ![1, t] s.snd)
      = MvPolynomial.eval₂Hom (RingHom.id (Ri R)) (fun s : LineVar => ![1, t] s.snd) from rfl]
  refine MvPolynomial.eval₂Hom_congr ?_ ?_ rfl
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, Polynomial.algebraMap_eq, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, RingHom.id_apply]
  · funext i
    obtain ⟨i, j⟩ := i
    fin_cases j <;> simp [dehom]

/-- The monomial of multidegree `d` in the two homogeneous coordinates whose `X₁`-exponent is `j`
(and whose `X₀`-exponent is `d - j`). -/
noncomputable def lineMonom (d j : ℕ) : LineVar →₀ ℕ :=
  Finsupp.single ⟨0, 0⟩ (d - j) + Finsupp.single ⟨0, 1⟩ j

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The dehomogenization as an explicit sum over the support. -/
theorem dehomPoly_eq_sum (P : MvPolynomial LineVar (Ri R)) :
    dehomPoly P = ∑ u ∈ P.support, Polynomial.C (P.coeff u) * Polynomial.X ^ (u ⟨0, 1⟩) := by
  rw [dehomPoly, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Polynomial.algebraMap_eq]
  congr 1
  -- the product over `u.support` of `dehom i ^ u i` collapses to `X ^ u ⟨0,1⟩`
  rw [Finset.prod_subset (Finset.subset_univ u.support)
    (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, pow_zero])]
  rw [Fintype.prod_sigma]
  simp [dehom, Fin.prod_univ_two]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- A monomial `u` in the support of a homogeneous `P` of multidegree `d` is determined by its
`X₁`-exponent: it equals `lineMonom (d 0) (u ⟨0,1⟩)`. -/
theorem support_eq_lineMonom {P : MvPolynomial LineVar (Ri R)} {d : Fin 1 → ℕ}
    (hP : IsMultihomogeneous P d) {u : LineVar →₀ ℕ} (hu : u ∈ P.support) :
    u = lineMonom (d 0) (u ⟨0, 1⟩) := by
  have hsum : u ⟨0, 0⟩ + u ⟨0, 1⟩ = d 0 := by
    have := hP 0 u hu
    rwa [Fin.sum_univ_two] at this
  ext s
  obtain ⟨i, j⟩ := s
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [lineMonom, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  fin_cases j
  · simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Fin.zero_eta,
      one_ne_zero, ite_false, ite_true, add_zero]
    omega
  · simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Fin.mk_one,
      zero_ne_one, ite_false, ite_true, zero_add]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The `j`-th coefficient of the dehomogenization equals the coefficient of `P` at the unique
monomial of multidegree `d` with `X₁`-exponent `j`. -/
theorem dehomPoly_coeff {P : MvPolynomial LineVar (Ri R)} {d : Fin 1 → ℕ}
    (hP : IsMultihomogeneous P d) (j : ℕ) :
    (dehomPoly P).coeff j = P.coeff (lineMonom (d 0) j) := by
  rw [dehomPoly_eq_sum, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hj : lineMonom (d 0) j ∈ P.support
  · rw [Finset.sum_eq_single (lineMonom (d 0) j)]
    · have : (lineMonom (d 0) j) ⟨0, 1⟩ = j := by
        rw [lineMonom, Finsupp.add_apply, Finsupp.single_eq_of_ne (by decide),
          Finsupp.single_eq_same, zero_add]
      rw [this, ite_eq_left rfl]
    · intro u hu hne
      rw [ite_eq_right]
      intro heq
      exact hne (by rw [support_eq_lineMonom hP hu, heq])
    · intro h; exact absurd hj h
  · rw [Finset.sum_eq_zero, MvPolynomial.notMem_support_iff.mp hj]
    intro u hu
    rw [ite_eq_right]
    intro heq
    apply hj
    rw [heq, ← support_eq_lineMonom hP hu]
    exact hu

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The dehomogenization is nonzero when `P` is a nonzero homogeneous polynomial. -/
theorem dehomPoly_ne_zero {P : MvPolynomial LineVar (Ri R)} {d : Fin 1 → ℕ}
    (hP : IsMultihomogeneous P d) (hP0 : P ≠ 0) : dehomPoly P ≠ 0 := by
  intro h
  apply hP0
  ext v
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases hv : v ∈ P.support
  · have hcoeff := dehomPoly_coeff hP (v ⟨0, 1⟩)
    rw [h, Polynomial.coeff_zero, ← support_eq_lineMonom hP hv] at hcoeff
    exact hcoeff.symm
  · exact MvPolynomial.notMem_support_iff.mp hv

/-- **BPR Lemma 4.102.** An algebraic subset of `ℙ₁(C)` (here `m = 1`, `k = 1`) is either all of
`ℙ₁(C)` or finite. -/
theorem lemma_4_102
    (Ps : Finset (MvPolynomial ((i : Fin 1) × Fin ((fun _ => 1 : Fin 1 → ℕ) i + 1)) (Ri R)))
    (hPs : ∀ P ∈ Ps, ∃ d : Fin 1 → ℕ, IsMultihomogeneous P d) :
    projZerOfFinset (R := R) (k := fun _ => 1) Ps = Set.univ
      ∨ (projZerOfFinset (R := R) (k := fun _ => 1) Ps).Finite := by
  by_cases hall : ∀ P ∈ Ps, P = 0
  · -- Case 1: all polynomials are zero, so the zero set is everything.
    left
    rw [Set.eq_univ_iff_forall]
    intro x P hP
    rw [ProjVanishes, evalCoords, hall P hP, map_zero]
  · -- Case 2: some `P₀ ≠ 0`; the zero set is finite.
    right
    push Not at hall
    obtain ⟨P₀, hP₀mem, hP₀ne⟩ := hall
    obtain ⟨d, hd⟩ := hPs P₀ hP₀mem
    -- The affine root set.
    set A : Set (Ri R) := {t | ∀ P ∈ Ps, evalCoords (k := fun _ => 1) P (fun _ => ![1, t]) = 0}
      with hA
    have hAfin : A.Finite := by
      apply Set.Finite.subset (dehomPoly_ne_zero hd hP₀ne |> Polynomial.finite_setOfPred_isRoot)
      intro t ht
      have := ht P₀ hP₀mem
      rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, ← evalCoords_eq_eval_dehomPoly P₀ t]
      exact this
    -- The finite superset of the zero set.
    refine Set.Finite.subset
      (Set.Finite.union (Set.finite_singleton
        (fun _ : Fin 1 => mkLine ![0, 1] vec01_ne_zero))
        (hAfin.image (fun t => fun _ : Fin 1 => mkLine ![1, t] (vec1t_ne_zero t)))) ?_
    intro x hx
    -- `x` is determined by `x 0 : ℙ₁(C)`; apply the chart dichotomy.
    have hx0 : ∀ i : Fin 1, x i = x 0 := fun i => by rw [Subsingleton.elim i 0]
    rcases proj_line_chart (x 0) with h01 | ⟨t, h1t⟩
    · -- `x 0 = (0 : 1)`, so `x = pt₀`.
      left
      rw [Set.mem_singleton_iff]
      funext i; rw [hx0 i, h01]
    · -- `x 0 = (1 : t)`, so `t ∈ A` and `x` is its image.
      right
      have hreduce : ∀ P ∈ Ps, evalCoords (k := fun _ => 1) P (fun _ => ![1, t]) = 0 := by
        intro P hP
        obtain ⟨e, he⟩ := hPs P hP
        have hmk : ∀ i : Fin 1,
            mkLine ((x i).rep) (x i).rep_nonzero
              = mkLine (![1, t] : Fin 2 → Ri R) (vec1t_ne_zero t) := by
          intro i
          rw [hx0 i, show mkLine ((x 0).rep) (x 0).rep_nonzero = x 0 from
            Projectivization.mk_rep (x 0), h1t]
        rw [← evalCoords_eq_zero_iff_of_mkLine_eq (d := e) he
          (fun i => (x i).rep_nonzero) (fun _ => vec1t_ne_zero t) hmk]
        exact hx P hP
      exact ⟨t, hreduce, by funext i; rw [hx0 i, h1t]⟩

end Azurite.BPR.Chapter4
