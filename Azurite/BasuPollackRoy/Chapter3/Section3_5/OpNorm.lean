import Azurite.BasuPollackRoy.Chapter3.Section3_5.SClass

/-! # BPR §3.5 — the norm of a linear mapping

Given a linear mapping `F : R^k → R^p`, **the norm of `F`** is
`‖F‖ = sup {‖F(x)‖ | ‖x‖ = 1}`. This is a well-defined element of `R` by Theorem 3.20,
since `x ↦ ‖F(x)‖` is a continuous semialgebraic function and `{x | ‖x‖ = 1}` is a closed
and bounded semialgebraic set.

Linear mappings `R^k → R^p` are carried by matrices (`Matrix.mulVec`; the derivative
`totalDeriv` is `mulVec` of the Jacobian matrix, `totalDeriv_eq_mulVec`). The supremum is
in fact attained: the general extreme-value lemma `exists_max_of_closed_bounded`
(Theorem 3.20 + the o-minimal least-upper-bound argument of `ExtremeValue.lean`, for an
arbitrary closed bounded nonempty semialgebraic domain) applied to the *squared* norm of
`F(x)` — a polynomial objective — on the unit sphere. `opNorm` is then the value at a
maximizing point, characterized choice-freely by `opNorm_isGreatest`, with the
IFT-ready squared bound `euclideanNormSq (A.mulVec y) ≤ ‖A‖² ‖y‖²`
(`normSq_mulVec_le_opNorm`). -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### The general extreme-value lemma -/

/-- **The maximum of a continuous semialgebraic function on a closed, bounded, nonempty
semialgebraic set is attained** (the unnumbered consequence of Theorem 3.20 opening §3.5,
for a general domain). -/
theorem exists_max_of_closed_bounded {k : ℕ} [Nonempty (Fin k)] {S : Set (Fin k → R)}
    (hS : IsSemialgebraicSet S) (hScl : IsClosed S) (hSb : IsBoundedSet S)
    (hne : S.Nonempty) {f : (Fin k → R) → (Fin 1 → R)}
    (hSf : IsSemialgebraicFunction S f) (hcont : ContinuousOn f S) :
    ∃ y ∈ S, ∀ z ∈ S, f z 0 ≤ f y 0 := by
  have hg : ∀ j : Fin 1, IsSemialgContinuousOn S (fun y => f y j) := by
    intro j
    rw [Fin.eq_zero j]
    have hfeq : scalarFun (fun y => f y 0) = f := funext fun y => constPt_eta (f y)
    rw [IsSemialgContinuousOn, hfeq]
    exact ⟨hSf, hcont⟩
  obtain ⟨hclosed, hbdd⟩ := theorem_3_20 S hS hScl hSb f hg
  have hTsa : IsSemialgebraicSet (f '' S) := (proposition_2_83 hSf).1 hS (subset_refl S)
  set T : Set R := constPt ⁻¹' (f '' S) with hTd
  have hCOG : ConstOnGaps T := isSemialgebraicSet_sect_constOnGaps hTsa
  have hval : ∀ y ∈ S, f y 0 ∈ T := fun y hy => by
    show constPt (f y 0) ∈ f '' S
    rw [constPt_eta (f y)]
    exact Set.mem_image_of_mem f hy
  obtain ⟨y₀, hy₀⟩ := hne
  have hneT : T.Nonempty := ⟨f y₀ 0, hval _ hy₀⟩
  have hbddAbove : BddAbove T := by
    obtain ⟨M, hM, hsub⟩ := hbdd
    refine ⟨M, fun t ht => ?_⟩
    have hball := hsub ht
    rw [mem_closedBall, sub_zero, euclideanNormSq_fin_one] at hball
    have hball' : t ^ 2 ≤ M ^ 2 := hball
    nlinarith [hball']
  obtain ⟨c, hc⟩ := hCOG.exists_isLUB hneT hbddAbove
  have hcT : c ∈ T := by
    by_contra hcT
    have hmem : (f '' S)ᶜ ∈ nhds (constPt c) := hclosed.isOpen_compl.mem_nhds hcT
    obtain ⟨r, hr, hsub⟩ := mem_nhds_iff_openBall.mp hmem
    obtain ⟨t, htT, htgt⟩ : ∃ t ∈ T, c - r < t := by
      by_contra hcon
      push Not at hcon
      have : c ≤ c - r := hc.2 (fun t ht => hcon t ht)
      linarith
    have htle : t ≤ c := hc.1 htT
    have hin : constPt t ∈ openBall (constPt c) r := by
      rw [mem_openBall, euclideanNormSq_fin_one, Pi.sub_apply]
      show (t - c) ^ 2 < r ^ 2
      nlinarith
    exact hsub hin htT
  obtain ⟨y, hyS, hyfc⟩ := hcT
  refine ⟨y, hyS, fun z hz => ?_⟩
  have hfz : f z 0 ≤ c := hc.1 (hval _ hz)
  have hfd : f y 0 = c := by
    have := congrFun hyfc 0
    exact this
  rw [hfd]
  exact hfz

/-! ### The unit sphere is semialgebraic, closed, bounded, nonempty -/

theorem isClosed_sphere {k : ℕ} (x : Fin k → R) (ρ : R) : IsClosed (sphere x ρ) := by
  have hpre : sphere x ρ
      = polynomialMap ![ballPoly x ρ] ⁻¹' {w : Fin 1 → R | w 0 = 0} := by
    ext y
    rw [mem_sphere, Set.mem_preimage, Set.mem_ofPred_eq]
    show euclideanNormSq (y - x) = ρ ^ 2 ↔ eval y (ballPoly x ρ) = 0
    rw [eval_ballPoly, sub_eq_zero]
  have hclosed : IsClosed {w : Fin 1 → R | w 0 = 0} := by
    rw [isClosed_iff, isOpen_iff]
    intro w hw
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq] at hw
    refine ⟨w, |w 0|, abs_pos.mpr hw, mem_openBall_self w (abs_pos.mpr hw),
      fun z hz => ?_⟩
    rw [mem_openBall, euclideanNormSq_fin_one, Pi.sub_apply, sq_abs] at hz
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq]
    intro hz0
    rw [hz0] at hz
    nlinarith
  rw [hpre]
  exact hclosed.preimage (continuous_polynomialMap _)

theorem isBoundedSet_sphere {k : ℕ} (ρ : R) :
    IsBoundedSet (sphere (0 : Fin k → R) ρ) := by
  refine ⟨|ρ| + 1, by positivity, fun y hy => ?_⟩
  rw [mem_sphere, sub_zero] at hy
  rw [mem_closedBall, sub_zero, hy]
  nlinarith [sq_abs ρ, abs_nonneg ρ]

theorem sphere_one_nonempty {k : ℕ} (hk : 0 < k) :
    (sphere (0 : Fin k → R) 1).Nonempty := by
  refine ⟨fun i => if i = ⟨0, hk⟩ then 1 else 0, ?_⟩
  rw [mem_sphere, sub_zero, one_pow, euclideanNormSq, Finset.sum_eq_single ⟨0, hk⟩]
  · rw [ite_eq_left rfl, one_pow]
  · intro j _ hj
    rw [ite_eq_right hj]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Norm comparison from squared comparison -/

theorem euclideanNorm_le_of_normSq_le {k p : ℕ} {u : Fin k → R} {v : Fin p → R}
    (h : euclideanNormSq u ≤ euclideanNormSq v) : euclideanNorm u ≤ euclideanNorm v := by
  have hsq : euclideanNorm u ^ 2 ≤ euclideanNorm v ^ 2 := by
    rw [euclideanNorm_sq, euclideanNorm_sq]
    exact h
  have := abs_le_of_sq_le_sq hsq (euclideanNorm_nonneg v)
  rwa [abs_of_nonneg (euclideanNorm_nonneg u)] at this

/-! ### The operator norm -/

/-- The squared norm of `A.mulVec x`, as a polynomial in `x`. -/
noncomputable def mulVecNormSqPoly {k p : ℕ} (A : Matrix (Fin p) (Fin k) R) :
    MvPolynomial (Fin k) R :=
  ∑ l : Fin p, (∑ j : Fin k, C (A l j) * X j) ^ 2

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem eval_mulVecNormSqPoly {k p : ℕ} (A : Matrix (Fin p) (Fin k) R) (x : Fin k → R) :
    eval x (mulVecNormSqPoly A) = euclideanNormSq (A.mulVec x) := by
  simp only [mulVecNormSqPoly, euclideanNormSq, Matrix.mulVec, dotProduct, map_sum,
    map_pow, map_mul, eval_C, eval_X]

open scoped Classical in
/-- **BPR's norm of a linear mapping** `F : R^k → R^p` (carried by a matrix):
`‖F‖ = sup {‖F(x)‖ | ‖x‖ = 1}`, packaged choice-freely through `IsGreatest` (the
supremum is attained; see `opNorm_isGreatest`). For `k = 0` the sphere is empty and the
norm is `0`. -/
noncomputable def opNorm {k p : ℕ} (A : Matrix (Fin p) (Fin k) R) : R :=
  if h : ∃ m, IsGreatest {r : R | ∃ x : Fin k → R,
      euclideanNormSq x = 1 ∧ r = euclideanNorm (A.mulVec x)} m
  then h.choose else 0

/-- **The norm of a linear mapping is a well-defined element of `R`** (BPR, via
Theorem 3.20): the supremum over the unit sphere is attained, and `opNorm` realizes it. -/
theorem opNorm_isGreatest {k p : ℕ} (hk : 0 < k) (A : Matrix (Fin p) (Fin k) R) :
    IsGreatest {r : R | ∃ x : Fin k → R,
      euclideanNormSq x = 1 ∧ r = euclideanNorm (A.mulVec x)} (opNorm A) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  -- maximize the squared norm of `A.mulVec x` on the unit sphere
  have hmax : ∃ y ∈ sphere (0 : Fin k → R) 1, ∀ z ∈ sphere (0 : Fin k → R) 1,
      polyFun (mulVecNormSqPoly A) z 0 ≤ polyFun (mulVecNormSqPoly A) y 0 := by
    refine exists_max_of_closed_bounded (isSemialgebraicSet_sphere 0 1)
      (isClosed_sphere 0 1) (isBoundedSet_sphere 1) (sphere_one_nonempty hk)
      (polyFun_isSemialgebraicFunction_on (isSemialgebraicSet_sphere 0 1) _) ?_
    exact (continuous_iff_components.mpr fun _ =>
      continuousR_eval (mulVecNormSqPoly A)).continuousOn
  obtain ⟨y, hyS, hymax⟩ := hmax
  have hyS' : euclideanNormSq y = 1 := by
    have := mem_sphere.mp hyS
    rwa [sub_zero, one_pow] at this
  have hgreat : IsGreatest {r : R | ∃ x : Fin k → R,
      euclideanNormSq x = 1 ∧ r = euclideanNorm (A.mulVec x)}
      (euclideanNorm (A.mulVec y)) := by
    constructor
    · exact ⟨y, hyS', rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      have hxS : x ∈ sphere (0 : Fin k → R) 1 := by
        rw [mem_sphere, sub_zero, one_pow]
        exact hx
      have h := hymax x hxS
      show euclideanNorm (A.mulVec x) ≤ euclideanNorm (A.mulVec y)
      refine euclideanNorm_le_of_normSq_le ?_
      have h1 : polyFun (mulVecNormSqPoly A) x 0 = euclideanNormSq (A.mulVec x) :=
        eval_mulVecNormSqPoly A x
      have h2 : polyFun (mulVecNormSqPoly A) y 0 = euclideanNormSq (A.mulVec y) :=
        eval_mulVecNormSqPoly A y
      rw [h1, h2] at h
      exact h
  classical
  rw [opNorm, dite_eq_left ⟨_, hgreat⟩]
  exact Exists.choose_spec _

theorem opNorm_nonneg {k p : ℕ} (hk : 0 < k) (A : Matrix (Fin p) (Fin k) R) :
    0 ≤ opNorm A := by
  obtain ⟨⟨x, -, hx⟩, -⟩ := opNorm_isGreatest hk A
  rw [hx]
  exact euclideanNorm_nonneg _

theorem norm_mulVec_le_opNorm {k p : ℕ} (hk : 0 < k) (A : Matrix (Fin p) (Fin k) R)
    {x : Fin k → R} (hx : euclideanNormSq x = 1) :
    euclideanNorm (A.mulVec x) ≤ opNorm A :=
  (opNorm_isGreatest hk A).2 ⟨x, hx, rfl⟩

/-- The IFT-ready squared bound: `‖A x‖² ≤ ‖A‖² ‖x‖²` for every `x` (the operator-norm
inequality, with squared norms to stay within polynomial arithmetic). -/
theorem normSq_mulVec_le_opNorm {k p : ℕ} (hk : 0 < k) (A : Matrix (Fin p) (Fin k) R)
    (y : Fin k → R) :
    euclideanNormSq (A.mulVec y) ≤ opNorm A ^ 2 * euclideanNormSq y := by
  rcases eq_or_ne y 0 with rfl | hne
  · rw [Matrix.mulVec_zero]
    simp [euclideanNormSq]
  · set Ny : R := euclideanNorm y with hNyd
    have hNy : 0 < Ny := by
      have := euclideanNorm_pos_of_ne (u := y) (v := 0) hne
      rwa [sub_zero] at this
    have hNy2 : Ny ^ 2 = euclideanNormSq y := euclideanNorm_sq y
    -- normalize to the unit sphere
    have hNyne : Ny ≠ 0 := ne_of_gt hNy
    have hx : euclideanNormSq (Ny⁻¹ • y) = 1 := by
      rw [euclideanNormSq_smul, inv_pow, ← hNy2]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hNyne)
    have hle := norm_mulVec_le_opNorm hk A hx
    have hsq : euclideanNormSq (A.mulVec (Ny⁻¹ • y)) ≤ opNorm A ^ 2 := by
      have h1 : euclideanNorm (A.mulVec (Ny⁻¹ • y)) ^ 2 ≤ opNorm A ^ 2 := by
        nlinarith [euclideanNorm_nonneg (A.mulVec (Ny⁻¹ • y)), hle, opNorm_nonneg hk A]
      rwa [euclideanNorm_sq] at h1
    rw [Matrix.mulVec_smul, euclideanNormSq_smul, inv_pow] at hsq
    have hNy2pos : (0 : R) < Ny ^ 2 := by positivity
    calc euclideanNormSq (A.mulVec y)
        = Ny ^ 2 * ((Ny ^ 2)⁻¹ * euclideanNormSq (A.mulVec y)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hNyne), one_mul]
      _ ≤ Ny ^ 2 * opNorm A ^ 2 := mul_le_mul_of_nonneg_left hsq hNy2pos.le
      _ = opNorm A ^ 2 * euclideanNormSq y := by rw [hNy2]; ring

/-! ### The derivative as a matrix action -/

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `df(x₀)` is the action of the Jacobian matrix: `totalDeriv g x₀ = (Jac f)(x₀) ⬝ ·`. -/
theorem totalDeriv_eq_mulVec {k p : ℕ} (g : Fin p → Fin k → (Fin k → R) → R)
    (x₀ h : Fin k → R) :
    totalDeriv g x₀ h = (jacobianMatrix g x₀).mulVec h := by
  funext l
  simp only [totalDeriv, jacobianMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]

end Azurite.BPR
