/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.OpNorm

/-! # BPR §3.5, Proposition 3.23 — the mean value inequality

**Let `x` and `y` be two points of `R^k`, `U` an open semialgebraic set containing the
segment `[x, y]`, and `f ∈ 𝒮¹(U, R^ℓ)`. Then `‖f(x) − f(y)‖ ≤ M ‖x − y‖`, where
`M = sup {‖df(z)‖ | z ∈ [x, y]}` (well-defined by Theorem 3.20).**

The file proceeds in three layers.

1. *Norm toolkit*: on top of §3.1's triangle inequality (`euclideanNorm_add_le`),
   homogeneity (`euclideanNorm_smul`), symmetry of distances, and the unsquared operator
   bound `‖A·v‖ ≤ ‖A‖ ‖v‖` (`norm_mulVec_le`) — all derived through squared norms, with no
   `sqrt` arithmetic.

2. *Well-definedness of `M`* (`exists_isGreatest_opNorm_segment`): the supremum over the
   segment of `z ↦ ‖df(z)‖` is attained. Rather than proving continuity of the operator
   norm, we maximize the squared polynomial objective `‖df(z)·w‖²` over the *product* of
   the segment and the unit sphere (closed, bounded, semialgebraic — Theorem 3.20 and the
   general extreme-value lemma apply), and check that the value at a maximizing pair is the
   greatest operator norm.

3. *The inequality* (`proposition_3_23`): BPR's continuity-induction. With
   `g(t) = f((1−t)x + ty)` and `c > 0`, the set
   `A_c = {t ∈ [0,1] | ‖g(t) − g(0)‖ ≤ (M‖x−y‖ + c) t}` is a closed semialgebraic subset
   of `[0,1]` containing `0`; it has a largest element `t₀`; and if `t₀ ≠ 1` the
   first-order approximation at `γ(t₀)` (which controls `‖g(t) − g(t₀)‖` for `t` slightly
   beyond `t₀`) contradicts maximality. So `1 ∈ A_c` for every `c`, giving the result. -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Norm toolkit: triangle inequality, homogeneity, operator bound -/

omit [IsRealClosed R] in
theorem eq_of_sq_eq_sq {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  refine le_antisymm ?_ ?_
  · have := abs_le_of_sq_le_sq h.le hb
    rwa [abs_of_nonneg ha] at this
  · have := abs_le_of_sq_le_sq h.ge ha
    rwa [abs_of_nonneg hb] at this

/-- Homogeneity of the euclidean norm: `‖c • w‖ = |c| ‖w‖`. -/
theorem euclideanNorm_smul {k : ℕ} (c : R) (w : Fin k → R) :
    euclideanNorm (c • w) = |c| * euclideanNorm w := by
  refine (eq_of_sq_eq_sq (euclideanNorm_nonneg _)
    (mul_nonneg (abs_nonneg c) (euclideanNorm_nonneg w)) ?_)
  rw [euclideanNorm_sq, mul_pow, sq_abs, euclideanNorm_sq, euclideanNormSq_smul]

theorem euclideanNorm_sub_symm {k : ℕ} (u v : Fin k → R) :
    euclideanNorm (u - v) = euclideanNorm (v - u) := by
  rw [euclideanNorm, euclideanNorm]
  congr 1
  rw [euclideanNormSq, euclideanNormSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply, Pi.sub_apply]
  ring

/-- The triangle inequality in difference form: `‖a − c‖ ≤ ‖a − b‖ + ‖b − c‖`. -/
theorem euclideanNorm_sub_le {k : ℕ} (a b c : Fin k → R) :
    euclideanNorm (a - c) ≤ euclideanNorm (a - b) + euclideanNorm (b - c) := by
  have h : a - c = (a - b) + (b - c) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [h]
  exact euclideanNorm_add_le _ _

theorem euclideanNorm_le_iff_normSq_le {k : ℕ} {v : Fin k → R} {b : R} (hb : 0 ≤ b) :
    euclideanNorm v ≤ b ↔ euclideanNormSq v ≤ b ^ 2 := by
  constructor
  · intro h
    rw [← euclideanNorm_sq]
    nlinarith [euclideanNorm_nonneg v]
  · intro h
    have hsq : euclideanNorm v ^ 2 ≤ b ^ 2 := by rwa [euclideanNorm_sq]
    have := abs_le_of_sq_le_sq hsq hb
    rwa [abs_of_nonneg (euclideanNorm_nonneg v)] at this

/-- The unsquared operator-norm inequality: `‖A·v‖ ≤ ‖A‖ ‖v‖`. -/
theorem norm_mulVec_le {k p : ℕ} (hk : 0 < k) (A : Matrix (Fin p) (Fin k) R)
    (v : Fin k → R) :
    euclideanNorm (A.mulVec v) ≤ opNorm A * euclideanNorm v := by
  have hsq : euclideanNorm (A.mulVec v) ^ 2 ≤ (opNorm A * euclideanNorm v) ^ 2 := by
    rw [euclideanNorm_sq, mul_pow, euclideanNorm_sq]
    exact normSq_mulVec_le_opNorm hk A v
  have := abs_le_of_sq_le_sq hsq
    (mul_nonneg (opNorm_nonneg hk A) (euclideanNorm_nonneg v))
  rwa [abs_of_nonneg (euclideanNorm_nonneg _)] at this

/-! ### The segment path, and the well-definedness of `M` -/

/-- The affine path `γ(t) = (1 − t)x + ty` through the segment `[x, y]`. -/
def segPath {k : ℕ} (x y : Fin k → R) (t : R) : Fin k → R :=
  fun i => (1 - t) * x i + t * y i

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem segPath_zero {k : ℕ} [Field R] (x y : Fin k → R) : segPath x y 0 = x :=
  funext fun i => by simp [segPath]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem segPath_one {k : ℕ} [Field R] (x y : Fin k → R) : segPath x y 1 = y :=
  funext fun i => by simp [segPath]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem segPath_sub {k : ℕ} [Field R] (x y : Fin k → R) (t t' : R) :
    segPath x y t' - segPath x y t = (t' - t) • (y - x) :=
  funext fun i => by
    simp only [segPath, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- **`M = sup {‖df(z)‖ | z ∈ [x, y]}` is well-defined** (BPR, by Theorem 3.20): the
supremum of the operator norms of the derivative along the segment is attained. Proved by
maximizing the squared objective `‖df(γ(t))·w‖²` — semialgebraic and continuous in the
pair `(t, w)` — over the product of `[0, 1]` and the unit sphere. -/
theorem exists_isGreatest_opNorm_segment {k ℓ : ℕ} (hk : 0 < k) {U : Set (Fin k → R)}
    {g : Fin ℓ → Fin k → (Fin k → R) → R} {x y : Fin k → R}
    (hseg : ∀ t : R, 0 ≤ t → t ≤ 1 → segPath x y t ∈ U)
    (hg : ∀ l j, IsSemialgContinuousOn U (g l j)) :
    ∃ M, IsGreatest {r : R | ∃ t : R, 0 ≤ t ∧ t ≤ 1 ∧
      r = opNorm (jacobianMatrix g (segPath x y t))} M := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  -- the product domain `[0,1] × S^{k−1} ⊆ R^{1+k}`
  set P : Set (Fin (1 + k) → R) :=
    {w | w ∘ Fin.castAdd k ∈ Set.Icc (constPt 0) (constPt 1) ∧
      w ∘ Fin.natAdd 1 ∈ sphere (0 : Fin k → R) 1} with hPd
  have hPsa : IsSemialgebraicSet P :=
    (IsSemialgebraicSet.comap _ (isSemialgebraicSet_Icc 0 1)).inter
      (IsSemialgebraicSet.comap _ (isSemialgebraicSet_sphere 0 1))
  have hπ1 : (fun w : Fin (1 + k) → R => w ∘ Fin.castAdd k)
      = polynomialMap (fun j : Fin 1 =>
        (X (Fin.castAdd k j) : MvPolynomial (Fin (1 + k)) R)) :=
    funext fun w => funext fun j => by simp [polynomialMap]
  have hπ2 : (fun w : Fin (1 + k) → R => w ∘ Fin.natAdd 1)
      = polynomialMap (fun j : Fin k =>
        (X (Fin.natAdd 1 j) : MvPolynomial (Fin (1 + k)) R)) :=
    funext fun w => funext fun j => by simp [polynomialMap]
  have hPcl : IsClosed P := by
    have h1 : IsClosed ((fun w : Fin (1 + k) → R => w ∘ Fin.castAdd k) ⁻¹'
        Set.Icc (constPt 0) (constPt 1)) := by
      rw [hπ1]
      exact (isClosed_Icc_constPt 0 1).preimage (continuous_polynomialMap _)
    have h2 : IsClosed ((fun w : Fin (1 + k) → R => w ∘ Fin.natAdd 1) ⁻¹'
        sphere (0 : Fin k → R) 1) := by
      rw [hπ2]
      exact (isClosed_sphere 0 1).preimage (continuous_polynomialMap _)
    exact h1.inter h2
  have hPb : IsBoundedSet P := by
    refine ⟨2, two_pos, fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := hw
    rw [mem_closedBall, sub_zero]
    have hsplit : euclideanNormSq w
        = (w (Fin.castAdd k 0)) ^ 2 + euclideanNormSq (w ∘ Fin.natAdd 1) := by
      rw [euclideanNormSq, Fin.sum_univ_add, Fin.sum_univ_one]
      rfl
    have ht := mem_Icc_fin_one.mp hw1
    have hsph := mem_sphere.mp hw2
    rw [sub_zero, one_pow] at hsph
    rw [hsplit, hsph]
    have ht0 : (0 : R) ≤ (w ∘ Fin.castAdd k) 0 := ht.1
    have ht1 : (w ∘ Fin.castAdd k) 0 ≤ 1 := ht.2
    have hco : (w ∘ Fin.castAdd k) 0 = w (Fin.castAdd k 0) := rfl
    rw [hco] at ht0 ht1
    nlinarith
  have hPne : P.Nonempty := by
    obtain ⟨e, he⟩ := sphere_one_nonempty (R := R) hk
    refine ⟨Fin.append (constPt 0) e, ?_, ?_⟩
    · have heq : Fin.append (constPt 0) e ∘ Fin.castAdd k = constPt (0 : R) :=
        funext fun j => Fin.append_left _ _ _
      rw [heq, mem_Icc_fin_one]
      exact ⟨le_refl _, zero_le_one⟩
    · have heq : Fin.append (constPt 0) e ∘ Fin.natAdd 1 = e :=
        funext fun j => Fin.append_right _ _ _
      rw [heq]
      exact he
  -- the parametrization of the segment from the product space
  set Γ : (Fin (1 + k) → R) → (Fin k → R) :=
    fun w => segPath x y (w (Fin.castAdd k 0)) with hΓd
  set Pvec : Fin k → MvPolynomial (Fin (1 + k)) R := fun i =>
    (1 - X (Fin.castAdd k 0)) * C (x i) + X (Fin.castAdd k 0) * C (y i) with hPvecd
  have hΓpoly : Γ = polynomialMap Pvec := by
    funext w i
    simp [hΓd, hPvecd, segPath, polynomialMap]
  have hΓsa : IsSemialgebraicFunction P Γ := by
    rw [hΓpoly]
    refine isSemialgebraicFunction_of_coords fun i => ?_
    show IsSemialgebraicFunction P (polyFun (Pvec i))
    exact polyFun_isSemialgebraicFunction_on hPsa _
  have hΓmaps : Set.MapsTo Γ P U := by
    intro w hw
    have ht := mem_Icc_fin_one.mp hw.1
    exact hseg _ ht.1 ht.2
  have hΓcont : ContinuousOn Γ P := by
    rw [hΓpoly]
    exact (continuous_polynomialMap _).continuousOn
  -- the composed entries `t ↦ ∂f_l/∂X_j (γ(t))` are semialgebraic continuous on `P`
  have hgt : ∀ l j, IsSemialgContinuousOn P (fun w => g l j (Γ w)) := by
    intro l j
    refine ⟨?_, ?_⟩
    · show IsSemialgebraicFunction P (scalarFun (g l j) ∘ Γ)
      exact proposition_2_84 hΓsa (hg l j).1 hΓmaps
    · show ContinuousOn (scalarFun (g l j) ∘ Γ) P
      exact ContinuousOn.comp (hg l j).2 hΓcont hΓmaps
  -- the coordinates of the sphere block
  have hcoord : ∀ j : Fin k, IsSemialgContinuousOn P
      (fun w : Fin (1 + k) → R => w (Fin.natAdd 1 j)) := by
    intro j
    have hco : scalarFun (fun w : Fin (1 + k) → R => w (Fin.natAdd 1 j))
        = polyFun (X (Fin.natAdd 1 j)) :=
      funext fun w => funext fun m => by simp [scalarFun, polyFun, constPt]
    refine ⟨?_, ?_⟩
    · rw [hco]
      exact polyFun_isSemialgebraicFunction_on hPsa _
    · rw [hco]
      exact (continuous_iff_components.mpr fun _ =>
        continuousR_eval (X (Fin.natAdd 1 j))).continuousOn
  -- the squared objective `‖df(γ(t))·w‖²` is semialgebraic continuous on `P`
  set cobj : (Fin (1 + k) → R) → R :=
    fun w => ∑ l : Fin ℓ, (∑ j : Fin k, g l j (Γ w) * w (Fin.natAdd 1 j)) ^ 2 with hcobjd
  have hcobj : IsSemialgContinuousOn P cobj := by
    rw [isSemialgContinuousOn_iff_mem hPsa]
    have heq : scalarFun cobj = ∑ l : Fin ℓ,
        (∑ j : Fin k, scalarFun (fun w => g l j (Γ w))
          * scalarFun (fun w : Fin (1 + k) → R => w (Fin.natAdd 1 j))) ^ 2 := by
      funext w m
      simp only [hcobjd, scalarFun, constPt, Finset.sum_apply, Pi.pow_apply, Pi.mul_apply]
    rw [heq]
    refine Subring.sum_mem _ fun l _ => ?_
    refine pow_mem (Subring.sum_mem _ fun j _ => ?_) 2
    exact mul_mem ((isSemialgContinuousOn_iff_mem hPsa _).mp (hgt l j))
      ((isSemialgContinuousOn_iff_mem hPsa _).mp (hcoord j))
  -- the value of the objective is the squared norm of the matrix action
  have hval : ∀ w : Fin (1 + k) → R, cobj w
      = euclideanNormSq ((jacobianMatrix g (Γ w)).mulVec (w ∘ Fin.natAdd 1)) := by
    intro w
    rw [hcobjd, euclideanNormSq]
    exact Finset.sum_congr rfl fun l _ => rfl
  -- maximize over the product
  have : Nonempty (Fin (1 + k)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨w₀, hw₀P, hw₀max⟩ := exists_max_of_closed_bounded hPsa hPcl hPb hPne
    hcobj.1 hcobj.2
  set tstar : R := w₀ (Fin.castAdd k 0) with htstard
  have htstar01 : 0 ≤ tstar ∧ tstar ≤ 1 := mem_Icc_fin_one.mp hw₀P.1
  set vstar : Fin k → R := w₀ ∘ Fin.natAdd 1 with hvstard
  have hvstar1 : euclideanNormSq vstar = 1 := by
    have := mem_sphere.mp hw₀P.2
    rwa [sub_zero, one_pow] at this
  -- comparison of objectives at an arbitrary admissible pair
  have hcompare : ∀ (t : R) (v₀ : Fin k → R), 0 ≤ t → t ≤ 1 → euclideanNormSq v₀ = 1 →
      euclideanNorm ((jacobianMatrix g (segPath x y t)).mulVec v₀)
        ≤ euclideanNorm ((jacobianMatrix g (segPath x y tstar)).mulVec vstar) := by
    intro t v₀ ht0 ht1 hv₀
    have hpair : Fin.append (constPt t) v₀ ∈ P := by
      constructor
      · have heq : Fin.append (constPt t) v₀ ∘ Fin.castAdd k = constPt t :=
          funext fun j => Fin.append_left _ _ _
        rw [heq, mem_Icc_fin_one]
        exact ⟨ht0, ht1⟩
      · have heq : Fin.append (constPt t) v₀ ∘ Fin.natAdd 1 = v₀ :=
          funext fun j => Fin.append_right _ _ _
        rw [heq, mem_sphere, sub_zero, one_pow]
        exact hv₀
    have hcmp := hw₀max _ hpair
    have h1 : scalarFun cobj (Fin.append (constPt t) v₀) 0
        = euclideanNormSq ((jacobianMatrix g (segPath x y t)).mulVec v₀) := by
      show cobj _ = _
      rw [hval]
      have e1 : Fin.append (constPt t) v₀ ∘ Fin.natAdd 1 = v₀ :=
        funext fun j => Fin.append_right _ _ _
      have e2 : Γ (Fin.append (constPt t) v₀) = segPath x y t := by
        show segPath x y (Fin.append (constPt t) v₀ (Fin.castAdd k 0)) = _
        rw [Fin.append_left]
        rfl
      rw [e1, e2]
    have h2 : scalarFun cobj w₀ 0
        = euclideanNormSq ((jacobianMatrix g (segPath x y tstar)).mulVec vstar) := by
      show cobj _ = _
      rw [hval]
    rw [h1, h2] at hcmp
    exact euclideanNorm_le_of_normSq_le hcmp
  refine ⟨euclideanNorm ((jacobianMatrix g (segPath x y tstar)).mulVec vstar), ?_, ?_⟩
  · -- membership: the value equals `‖df(γ(t*))‖`
    refine ⟨tstar, htstar01.1, htstar01.2, ?_⟩
    refine (le_antisymm ?_ ?_).symm
    · obtain ⟨⟨v₀, hv₀, hv₀val⟩, -⟩ :=
        opNorm_isGreatest hk (jacobianMatrix g (segPath x y tstar))
      rw [hv₀val]
      exact hcompare tstar v₀ htstar01.1 htstar01.2 hv₀
    · exact norm_mulVec_le_opNorm hk _ hvstar1
  · -- upper bound: every `‖df(γ(t))‖` is `≤` the value
    rintro r ⟨t, ht0, ht1, rfl⟩
    obtain ⟨⟨v₀, hv₀, hv₀val⟩, -⟩ :=
      opNorm_isGreatest hk (jacobianMatrix g (segPath x y t))
    rw [hv₀val]
    exact hcompare t v₀ ht0 ht1 hv₀

/-! ### Proposition 3.23 -/

omit [IsRealClosed R] in
private theorem segPath_ne {k : ℕ} {x y : Fin k → R} (hxy : y ≠ x) {t t₀ : R}
    (htne : t ≠ t₀) : segPath x y t ≠ segPath x y t₀ := by
  intro hcon
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  have h := congrFun hcon j
  simp only [segPath] at h
  have : (t - t₀) * (y j - x j) = 0 := by ring_nf; linarith [h]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact htne (by linarith [sub_eq_zero.mp h1])
  · exact hj (by linarith [sub_eq_zero.mp h1])

/-- **BPR Proposition 3.23 (the mean value inequality).** Let `x` and `y` be two points of
`R^k`, `U` an open semialgebraic set containing the segment `[x, y]`, and `f ∈ 𝒮¹(U, R^ℓ)`
(coordinatewise: `f_l` semialgebraic continuous on `U`, with partial derivatives `g l j`
existing on `U` and semialgebraic continuous). Then `‖f(x) − f(y)‖ ≤ M ‖x − y‖` for any
`M ≥ 0` dominating the operator norms `‖df(z)‖` along the segment — in particular for
`M = sup {‖df(z)‖ | z ∈ [x, y]}`, which is well defined by Theorem 3.20
(`exists_isGreatest_opNorm_segment`). -/
theorem proposition_3_23 {k ℓ : ℕ} {U : Set (Fin k → R)}
    {f : (Fin k → R) → (Fin ℓ → R)} {g : Fin ℓ → Fin k → (Fin k → R) → R}
    {x y : Fin k → R} {M : R} (hUopen : IsOpen U)
    (hseg : ∀ t : R, 0 ≤ t → t ≤ 1 → segPath x y t ∈ U)
    (hf : ∀ l, IsSemialgContinuousOn U (fun z => f z l))
    (hdiff : ∀ l j, ∀ z ∈ U, HasPartialDerivAtIn (fun w => f w l) U j z (g l j z))
    (hgsc : ∀ l j, IsSemialgContinuousOn U (g l j))
    (hM : ∀ t : R, 0 ≤ t → t ≤ 1 → opNorm (jacobianMatrix g (segPath x y t)) ≤ M)
    (hM0 : 0 ≤ M) :
    euclideanNorm (f x - f y) ≤ M * euclideanNorm (x - y) := by
  classical
  -- degenerate dimension
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have hxy : x = y := funext fun i => i.elim0
    rw [hxy, sub_self, euclideanNorm_zero]
    exact mul_nonneg hM0 (euclideanNorm_nonneg _)
  -- coincident endpoints
  by_cases hxy : y = x
  · rw [hxy, sub_self, euclideanNorm_zero]
    exact mul_nonneg hM0 (euclideanNorm_nonneg _)
  have hnxy : 0 < euclideanNorm (x - y) := by
    have := euclideanNorm_pos_of_ne (u := x) (v := y) (Ne.symm hxy)
    exact this
  -- it suffices to beat `M‖x−y‖ + c` for every `c > 0`
  rw [euclideanNorm_sub_symm (f x) (f y)]
  refine le_of_forall_pos_le_add fun c hc => ?_
  set B : R := M * euclideanNorm (x - y) with hBd
  have hB0 : 0 ≤ B := mul_nonneg hM0 (euclideanNorm_nonneg _)
  have hBc : 0 < B + c := by linarith
  -- the step estimate from the first-order approximation
  have hstep : ∀ t₀ : R, 0 ≤ t₀ → t₀ < 1 → ∃ r, 0 < r ∧ ∀ t, t₀ < t → t < t₀ + r →
      t ≤ 1 → euclideanNorm (f (segPath x y t) - f (segPath x y t₀))
        ≤ (B + c) * (t - t₀) := by
    intro t₀ ht₀0 ht₀1
    have hz₀ : segPath x y t₀ ∈ U := hseg t₀ ht₀0 ht₀1.le
    have hlo := isLittleO_sub_totalDeriv hUopen (fun l => (hf l).1) hdiff
      (fun l j => (hgsc l j).2) hz₀
    set ε : R := c / (euclideanNorm (x - y) + 1) with hεd
    have hε : 0 < ε := by positivity
    obtain ⟨δ, hδ, hball⟩ := hlo ε hε
    refine ⟨δ / (euclideanNorm (x - y) + 1), by positivity, fun t ht0 htr ht1 => ?_⟩
    have htt₀ : 0 < t - t₀ := by linarith
    have hzt : segPath x y t ∈ U := hseg t (by linarith) ht1
    have hne : segPath x y t ≠ segPath x y t₀ := segPath_ne hxy (by intro h; linarith [h])
    -- the displacement and its norm
    have hdisp : segPath x y t - segPath x y t₀ = (t - t₀) • (y - x) := segPath_sub x y t₀ t
    have hN : euclideanNorm (segPath x y t - segPath x y t₀)
        = (t - t₀) * euclideanNorm (x - y) := by
      rw [hdisp, euclideanNorm_smul, abs_of_pos htt₀, euclideanNorm_sub_symm y x]
    have hNpos : 0 < euclideanNorm (segPath x y t - segPath x y t₀) := by
      rw [hN]
      positivity
    have hNδ : euclideanNorm (segPath x y t - segPath x y t₀) < δ := by
      rw [hN]
      calc (t - t₀) * euclideanNorm (x - y)
          < δ / (euclideanNorm (x - y) + 1) * euclideanNorm (x - y) := by
            exact mul_lt_mul_of_pos_right (by linarith) hnxy
        _ ≤ δ := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [euclideanNorm_nonneg (x - y)]
    -- the little-o bound, unsmul'd
    have hballt := hball (segPath x y t) hzt hne hNδ
    rw [sub_zero] at hballt
    have hsmul : euclideanNorm ((euclideanNorm (segPath x y t - segPath x y t₀))⁻¹ •
        (f (segPath x y t) - f (segPath x y t₀)
          - totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀)))
        = (euclideanNorm (segPath x y t - segPath x y t₀))⁻¹
          * euclideanNorm (f (segPath x y t) - f (segPath x y t₀)
            - totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀)) := by
      rw [euclideanNorm_smul, abs_of_pos (by positivity)]
    rw [hsmul] at hballt
    have hlittle : euclideanNorm (f (segPath x y t) - f (segPath x y t₀)
        - totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀))
        ≤ ε * euclideanNorm (segPath x y t - segPath x y t₀) := by
      have h1 := (inv_mul_lt_iff₀ hNpos).mp hballt
      calc euclideanNorm _ ≤ euclideanNorm (segPath x y t - segPath x y t₀) * ε := h1.le
        _ = ε * euclideanNorm (segPath x y t - segPath x y t₀) := by ring
    -- the derivative term
    have hderiv : euclideanNorm (totalDeriv g (segPath x y t₀)
        (segPath x y t - segPath x y t₀))
        ≤ M * ((t - t₀) * euclideanNorm (x - y)) := by
      rw [totalDeriv_eq_mulVec]
      calc euclideanNorm ((jacobianMatrix g (segPath x y t₀)).mulVec
            (segPath x y t - segPath x y t₀))
          ≤ opNorm (jacobianMatrix g (segPath x y t₀))
            * euclideanNorm (segPath x y t - segPath x y t₀) :=
            norm_mulVec_le hk _ _
        _ ≤ M * euclideanNorm (segPath x y t - segPath x y t₀) := by
            refine mul_le_mul_of_nonneg_right (hM t₀ ht₀0 ht₀1.le)
              (euclideanNorm_nonneg _)
        _ = M * ((t - t₀) * euclideanNorm (x - y)) := by rw [hN]
    -- assemble by the triangle inequality
    have htri : euclideanNorm (f (segPath x y t) - f (segPath x y t₀))
        ≤ euclideanNorm (f (segPath x y t) - f (segPath x y t₀)
            - totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀))
          + euclideanNorm (totalDeriv g (segPath x y t₀)
            (segPath x y t - segPath x y t₀)) := by
      have h := euclideanNorm_add_le
        (f (segPath x y t) - f (segPath x y t₀)
          - totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀))
        (totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀))
      have heq : (f (segPath x y t) - f (segPath x y t₀)
            - totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀))
          + totalDeriv g (segPath x y t₀) (segPath x y t - segPath x y t₀)
          = f (segPath x y t) - f (segPath x y t₀) := by
        funext i
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rwa [heq] at h
    have hεbound : ε * euclideanNorm (x - y) ≤ c := by
      rw [hεd, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [euclideanNorm_nonneg (x - y)]
    calc euclideanNorm (f (segPath x y t) - f (segPath x y t₀))
        ≤ ε * euclideanNorm (segPath x y t - segPath x y t₀)
          + M * ((t - t₀) * euclideanNorm (x - y)) := by
          refine le_trans htri (add_le_add hlittle hderiv)
      _ = (ε * euclideanNorm (x - y) + M * euclideanNorm (x - y)) * (t - t₀) := by
          rw [hN]
          ring
      _ ≤ (c + B) * (t - t₀) := by
          refine mul_le_mul_of_nonneg_right ?_ htt₀.le
          rw [hBd]
          linarith [hεbound]
      _ = (B + c) * (t - t₀) := by ring
  -- the set `A_c`, encoded on the line
  set fcomp : (Fin 1 → R) → (Fin ℓ → R) := fun w => f (segPath x y (w 0)) with hfcompd
  set D : (Fin 1 → R) → R := fun w =>
    euclideanNormSq (fcomp w - f x) - ((B + c) * w 0) ^ 2 with hDd
  set Ac : Set (Fin 1 → R) :=
    Set.Icc (constPt 0) (constPt 1) ∩ scalarFun D ⁻¹' {v : Fin 1 → R | v 0 ≤ 0}
    with hAcd
  -- membership in `A_c`, decoded
  have hmemAc : ∀ t : R, constPt t ∈ Ac ↔ (0 ≤ t ∧ t ≤ 1) ∧
      euclideanNorm (f (segPath x y t) - f x) ≤ (B + c) * t := by
    intro t
    rw [hAcd, Set.mem_inter_iff, mem_Icc_fin_one, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, h1⟩, hD⟩
      refine ⟨⟨h0, h1⟩, ?_⟩
      have hDval : euclideanNormSq (f (segPath x y t) - f x) - ((B + c) * t) ^ 2 ≤ 0 := hD
      rw [euclideanNorm_le_iff_normSq_le (by positivity)]
      linarith
    · rintro ⟨⟨h0, h1⟩, hle⟩
      refine ⟨⟨h0, h1⟩, ?_⟩
      show euclideanNormSq (f (segPath x y t) - f x) - ((B + c) * t) ^ 2 ≤ 0
      have := (euclideanNorm_le_iff_normSq_le
        (show (0:R) ≤ (B + c) * t by positivity)).mp hle
      linarith
  -- the affine parametrization of the segment from the line
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  set Λ : (Fin 1 → R) → (Fin k → R) := fun w => segPath x y (w 0) with hΛd
  set Qvec : Fin k → MvPolynomial (Fin 1) R := fun i =>
    (1 - X 0) * C (x i) + X 0 * C (y i) with hQvecd
  have hΛpoly : Λ = polynomialMap Qvec := by
    funext w i
    simp [hΛd, hQvecd, segPath, polynomialMap]
  have hΛsa : IsSemialgebraicFunction (Set.Icc (constPt 0) (constPt 1)) Λ := by
    rw [hΛpoly]
    refine isSemialgebraicFunction_of_coords fun i => ?_
    show IsSemialgebraicFunction _ (polyFun (Qvec i))
    exact polyFun_isSemialgebraicFunction_on (isSemialgebraicSet_Icc 0 1) _
  have hΛmaps : Set.MapsTo Λ (Set.Icc (constPt 0) (constPt 1)) U := by
    intro w hw
    have ht := mem_Icc_fin_one.mp hw
    exact hseg _ ht.1 ht.2
  have hΛcont : ContinuousOn Λ (Set.Icc (constPt 0) (constPt 1)) := by
    rw [hΛpoly]
    exact (continuous_polynomialMap _).continuousOn
  -- `D` is semialgebraic continuous on the interval
  have hfcl : ∀ l, IsSemialgContinuousOn (Set.Icc (constPt 0) (constPt 1))
      (fun w => fcomp w l) := by
    intro l
    refine ⟨?_, ?_⟩
    · show IsSemialgebraicFunction _ (scalarFun (fun z => f z l) ∘ Λ)
      exact proposition_2_84 hΛsa (hf l).1 hΛmaps
    · show ContinuousOn (scalarFun (fun z => f z l) ∘ Λ) _
      exact ContinuousOn.comp (hf l).2 hΛcont hΛmaps
  have hcoord0 : IsSemialgContinuousOn (Set.Icc (constPt 0) (constPt 1))
      (fun w : Fin 1 → R => w 0) := by
    have hco : scalarFun (fun w : Fin 1 → R => w 0) = polyFun (X 0) :=
      funext fun w => funext fun m => by simp [scalarFun, polyFun, constPt]
    refine ⟨?_, ?_⟩
    · rw [hco]
      exact polyFun_isSemialgebraicFunction_on (isSemialgebraicSet_Icc 0 1) _
    · rw [hco]
      exact (continuous_iff_components.mpr fun _ => continuousR_eval (X 0)).continuousOn
  have hD : IsSemialgContinuousOn (Set.Icc (constPt 0) (constPt 1)) D := by
    rw [isSemialgContinuousOn_iff_mem (isSemialgebraicSet_Icc 0 1)]
    have heq : scalarFun D = (∑ l : Fin ℓ,
        (scalarFun (fun w => fcomp w l)
          - scalarFun (fun _ : Fin 1 → R => f x l)) ^ 2)
        - (scalarFun (fun _ : Fin 1 → R => B + c)
            * scalarFun (fun w : Fin 1 → R => w 0)) ^ 2 := by
      funext w m
      simp only [hDd, scalarFun, constPt, euclideanNormSq, Finset.sum_apply,
        Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]
    rw [heq]
    refine sub_mem (Subring.sum_mem _ fun l _ => ?_) ?_
    · refine pow_mem (sub_mem ?_ ?_) 2
      · exact (isSemialgContinuousOn_iff_mem _ _).mp (hfcl l)
      · exact (isSemialgContinuousOn_iff_mem _ _).mp
          (isSemialgContinuousOn_constFun (isSemialgebraicSet_Icc 0 1) (f x l))
    · refine pow_mem (mul_mem ?_ ?_) 2
      · exact (isSemialgContinuousOn_iff_mem _ _).mp
          (isSemialgContinuousOn_constFun (isSemialgebraicSet_Icc 0 1) (B + c))
      · exact (isSemialgContinuousOn_iff_mem _ _).mp hcoord0
  -- `A_c` is semialgebraic, closed, bounded, nonempty
  have hVsa : IsSemialgebraicSet {v : Fin 1 → R | v 0 ≤ 0} := by
    have heq : {v : Fin 1 → R | v 0 ≤ 0} = {v | eval v (X 0 : MvPolynomial (Fin 1) R) ≤ 0} := by
      ext v
      simp [eval_X]
    rw [heq]
    exact IsSemialgebraicSet.leZero _
  have hVcl : IsClosed {v : Fin 1 → R | v 0 ≤ 0} := by
    rw [isClosed_iff, isOpen_iff]
    intro v hv
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hv
    refine ⟨v, v 0, hv, mem_openBall_self v hv, fun z hz => ?_⟩
    rw [mem_openBall, euclideanNormSq_fin_one, Pi.sub_apply] at hz
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    nlinarith
  have hAcsa : IsSemialgebraicSet Ac := (proposition_2_83 hD.1).2 hVsa
  have hAccl : IsClosed Ac :=
    ContinuousOn.preimage_isClosed_of_isClosed hD.2 (isClosed_Icc_constPt 0 1) hVcl
  have hAcb : IsBoundedSet Ac := by
    refine ⟨2, two_pos, fun w hw => ?_⟩
    have ht := mem_Icc_fin_one.mp hw.1
    rw [mem_closedBall, sub_zero, euclideanNormSq_fin_one]
    nlinarith [ht.1, ht.2]
  have hAcne : Ac.Nonempty := by
    refine ⟨constPt 0, (hmemAc 0).mpr ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩⟩
    rw [segPath_zero, sub_self, euclideanNorm_zero, mul_zero]
  -- the largest element of `A_c`
  obtain ⟨w₀, hw₀Ac, hw₀max⟩ := exists_max_of_closed_bounded hAcsa hAccl hAcb hAcne
    (polyFun_isSemialgebraicFunction_on hAcsa (X 0))
    ((continuous_iff_components.mpr fun _ => continuousR_eval (X 0)).continuousOn)
  set t₀ : R := w₀ 0 with ht₀d
  have hw₀eta : constPt t₀ = w₀ := constPt_eta w₀
  have ht₀Ac : constPt t₀ ∈ Ac := by rw [hw₀eta]; exact hw₀Ac
  have ht₀dec := (hmemAc t₀).mp ht₀Ac
  have ht₀max : ∀ t : R, constPt t ∈ Ac → t ≤ t₀ := by
    intro t ht
    have := hw₀max _ ht
    have h1 : polyFun (X (0 : Fin 1)) (constPt t) 0 = t := by
      simp [polyFun, constPt]
    have h2 : polyFun (X (0 : Fin 1)) w₀ 0 = t₀ := by
      simp [polyFun, ht₀d]
    rwa [h1, h2] at this
  -- the largest element is `1`
  have ht₀1 : t₀ = 1 := by
    by_contra hne1
    have ht₀lt1 : t₀ < 1 := lt_of_le_of_ne ht₀dec.1.2 hne1
    obtain ⟨r, hr, hstep'⟩ := hstep t₀ ht₀dec.1.1 ht₀lt1
    set t : R := min (t₀ + r / 2) ((t₀ + 1) / 2) with htd
    have htgt : t₀ < t := lt_min (by linarith) (by linarith)
    have htlt : t < t₀ + r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htle1 : t ≤ 1 := le_trans (min_le_right _ _) (by linarith)
    have hbound := hstep' t htgt htlt htle1
    have hsum : euclideanNorm (f (segPath x y t) - f x) ≤ (B + c) * t := by
      calc euclideanNorm (f (segPath x y t) - f x)
          ≤ euclideanNorm (f (segPath x y t) - f (segPath x y t₀))
            + euclideanNorm (f (segPath x y t₀) - f x) :=
            euclideanNorm_sub_le _ _ _
        _ ≤ (B + c) * (t - t₀) + (B + c) * t₀ := add_le_add hbound ht₀dec.2
        _ = (B + c) * t := by ring
    have htAc : constPt t ∈ Ac := (hmemAc t).mpr ⟨⟨by linarith [ht₀dec.1.1], htle1⟩, hsum⟩
    exact absurd (ht₀max t htAc) (not_le.mpr htgt)
  -- conclude
  have hfinal := ht₀dec.2
  rw [ht₀1, segPath_one, mul_one] at hfinal
  calc euclideanNorm (f y - f x) ≤ B + c := hfinal
    _ = M * euclideanNorm (x - y) + c := by rw [hBd]

end Azurite.BPR
