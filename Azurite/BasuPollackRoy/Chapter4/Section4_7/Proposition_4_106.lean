import Azurite.BasuPollackRoy.Chapter4.Section4_7.WeakBezoutWitness
import Azurite.BasuPollackRoy.Chapter3.Section3_3.Theorem_3_19

/-!
# BPR §4.7, Proposition 4.106: relative closedness of `Pm m` and the capstone

This file supplies the relative closedness of the parameter set `Pm P d γ m` in `(0,1]` (gap (c)) and
assembles the capstone `proposition_4_106` (the weak Bézout bound).

It provides:

* the trivial `m = 0` case (`pm_isClosedIn_zero`: `Pm … 0 = (0,1]`, relatively clopen);
* semialgebraic continuity of the moment-map components along a unit-normalized representative curve
  (`isSemialgContinuousOn_momentFn_repsFromY`), the hypothesis `projective_curve_limit` consumes for
  each representative branch of the curve selected on `Wb`;
* the limit line of each representative branch (`exists_branch_limit`) and that it is a common zero of
  `S₍γ t₀₎` (`branchLimit_isCommonZero`), via the eval-limit `eval_eq_zero_of_curve_limit` and the
  chart-coordinate convergence lemmas;
* relative closedness of `Pm m` for `m ≥ 1` (`pm_isClosedIn`), with distinctness of the `m` limit
  lines recovered from non-singular isolation (`homotopy_local_ift_chartV`);
* the capstone `proposition_4_106`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

open scoped Azurite.BPR

set_option linter.unusedSectionVars false

/-! ### `Pm m = intervalSet` when `m = 0` -/

/-- For `m = 0` the parameter set `Pm m` is all of `(0,1]` (`AtLeastZeros … 0` is vacuous), hence
trivially relatively closed in `(0,1]`. -/
theorem pm_isClosedIn_zero (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1) :
    IsClosedIn (intervalSet (R := R)) (Pm P d γ 0) := by
  have heq : Pm P d γ 0 = intervalSet (R := R) := by
    ext w
    simp only [Pm, intervalSet, Set.mem_setOf_eq, and_iff_left_iff_imp]
    exact fun _ => atLeastZeros_zero P d (γ w)
  rw [heq]
  exact isClosedIn_self _

/-! ### Step (iii) crux: semialgebraic continuity of the moment components along a curve -/

variable (m : ℕ)

/-- The `(reL ∘ repsFromY)` real coordinate `Ri.reL (repsFromY m (q ∘ natAdd 1) a j)` reads off the
coordinate `(q ·) (natAdd 1 (castAdd … (finProdFinEquiv (a,j))))` of the curve point. -/
theorem reL_repsFromY_eq (q : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) (a : Fin m)
    (j : Fin (k + 1)) :
    Ri.reL (repsFromY m (q ∘ Fin.natAdd 1) a j)
      = q (Fin.natAdd 1 (Fin.castAdd (m * (k + 1)) (finProdFinEquiv (a, j)))) := by
  rw [repsFromY, reL_symm_apply, Function.comp_apply]

/-- The `(imL ∘ repsFromY)` real coordinate reads off the imaginary-block coordinate of the curve. -/
theorem imL_repsFromY_eq (q : Fin (1 + (m * (k + 1) + m * (k + 1))) → R) (a : Fin m)
    (j : Fin (k + 1)) :
    Ri.imL (repsFromY m (q ∘ Fin.natAdd 1) a j)
      = q (Fin.natAdd 1 (Fin.natAdd (m * (k + 1)) (finProdFinEquiv (a, j)))) := by
  rw [repsFromY, imL_symm_apply, Function.comp_apply]

/-- Each coordinate `w ↦ Ri.reL (repsFromY m (q w ∘ natAdd 1) a j)` of a representative, viewed
through a curve `q : (Fin 1 → R) → Rᴾ` whose coordinates are all `IsSemialgContinuousOn S`, is
`IsSemialgContinuousOn S`. -/
theorem isSemialgContinuousOn_reL_repsFromY {S : Set (Fin 1 → R)} (_hS : IsSemialgebraicSet S)
    (q : (Fin 1 → R) → Fin (1 + (m * (k + 1) + m * (k + 1))) → R)
    (hq : ∀ c, IsSemialgContinuousOn S (fun w => q w c)) (a : Fin m) (j : Fin (k + 1)) :
    IsSemialgContinuousOn S (fun w => Ri.reL (repsFromY m (q w ∘ Fin.natAdd 1) a j)) := by
  have heq : (fun w => Ri.reL (repsFromY m (q w ∘ Fin.natAdd 1) a j))
      = fun w => q w (Fin.natAdd 1 (Fin.castAdd (m * (k + 1)) (finProdFinEquiv (a, j)))) := by
    funext w; rw [reL_repsFromY_eq]
  rw [heq]; exact hq _

theorem isSemialgContinuousOn_imL_repsFromY {S : Set (Fin 1 → R)} (_hS : IsSemialgebraicSet S)
    (q : (Fin 1 → R) → Fin (1 + (m * (k + 1) + m * (k + 1))) → R)
    (hq : ∀ c, IsSemialgContinuousOn S (fun w => q w c)) (a : Fin m) (j : Fin (k + 1)) :
    IsSemialgContinuousOn S (fun w => Ri.imL (repsFromY m (q w ∘ Fin.natAdd 1) a j)) := by
  have heq : (fun w => Ri.imL (repsFromY m (q w ∘ Fin.natAdd 1) a j))
      = fun w => q w (Fin.natAdd 1 (Fin.natAdd (m * (k + 1)) (finProdFinEquiv (a, j)))) := by
    funext w; rw [imL_repsFromY_eq]
  rw [heq]; exact hq _

/-- `IsSemialgContinuousOn` depends only on the values of the function on the domain. -/
theorem IsSemialgContinuousOn.congr {S : Set (Fin 1 → R)} {c d : (Fin 1 → R) → R}
    (hc : IsSemialgContinuousOn S c) (h : ∀ u ∈ S, c u = d u) :
    IsSemialgContinuousOn S d := by
  obtain ⟨hsa, hcont⟩ := hc
  have hscalar : ∀ u ∈ S, scalarFun c u = scalarFun d u := by
    intro u hu; simp only [scalarFun]; rw [h u hu]
  have hscalar' : Set.EqOn (scalarFun d) (scalarFun c) S := fun u hu => (hscalar u hu).symm
  refine ⟨?_, ?_⟩
  · show IsSemialgebraicSet (funGraph S (scalarFun d))
    rw [← funGraph_congr hscalar]; exact hsa
  · exact hcont.congr hscalar'

/-- **Step (iii) crux: moment components are semialgebraic-continuous along a unit-normalized
representative curve.** If every coordinate of the curve `q` is `IsSemialgContinuousOn S` and the
`a`-th representative is everywhere a unit vector on `S`, then each moment component
`w ↦ momentFn (repsFromY m (q w ∘ natAdd 1) a) idx` is `IsSemialgContinuousOn S`. With the unit norm
the projector denominator is `1`, so each entry is a polynomial in the real coordinates of `q`. -/
theorem isSemialgContinuousOn_momentFn_repsFromY {S : Set (Fin 1 → R)} (hS : IsSemialgebraicSet S)
    (q : (Fin 1 → R) → Fin (1 + (m * (k + 1) + m * (k + 1))) → R)
    (hq : ∀ c, IsSemialgContinuousOn S (fun w => q w c)) (a : Fin m)
    (hunit : ∀ w ∈ S, hermNormSq (repsFromY m (q w ∘ Fin.natAdd 1) a) = 1)
    (idx : MomentIndex k) :
    IsSemialgContinuousOn S (fun w => momentFn (repsFromY m (q w ∘ Fin.natAdd 1) a) idx) := by
  set re : Fin (k + 1) → (Fin 1 → R) → R :=
    fun j w => Ri.reL (repsFromY m (q w ∘ Fin.natAdd 1) a j) with hre
  set im : Fin (k + 1) → (Fin 1 → R) → R :=
    fun j w => Ri.imL (repsFromY m (q w ∘ Fin.natAdd 1) a j) with him
  have hrec : ∀ j, IsSemialgContinuousOn S (re j) := fun j =>
    isSemialgContinuousOn_reL_repsFromY m hS q hq a j
  have himc : ∀ j, IsSemialgContinuousOn S (im j) := fun j =>
    isSemialgContinuousOn_imL_repsFromY m hS q hq a j
  obtain ⟨p⟩ | ⟨p⟩ := idx
  · -- real-part entry, numerator `re p.1 · re p.2 + im p.1 · im p.2` (denom = 1 on `S`)
    have hnum : IsSemialgContinuousOn S
        ((re p.1 * re p.2 + im p.1 * im p.2 : (Fin 1 → R) → R)) :=
      IsSemialgContinuousOn.add hS
        (IsSemialgContinuousOn.mul hS (hrec p.1) (hrec p.2))
        (IsSemialgContinuousOn.mul hS (himc p.1) (himc p.2))
    refine IsSemialgContinuousOn.congr hnum (fun w hw => ?_)
    rw [momentFn_inl, projReV, hunit w hw, div_one]
    simp only [hre, him, Pi.add_apply, Pi.mul_apply]
  · -- imaginary-part entry, numerator `im p.1 · re p.2 - re p.1 · im p.2`
    have hnum : IsSemialgContinuousOn S
        ((im p.1 * re p.2 + (-(re p.1 * im p.2)) : (Fin 1 → R) → R)) :=
      IsSemialgContinuousOn.add hS
        (IsSemialgContinuousOn.mul hS (himc p.1) (hrec p.2))
        (IsSemialgContinuousOn.neg hS (IsSemialgContinuousOn.mul hS (hrec p.1) (himc p.2)))
    refine IsSemialgContinuousOn.congr hnum (fun w hw => ?_)
    rw [momentFn_inr, projImV, hunit w hw, div_one]
    simp only [hre, him, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]
    ring

set_option linter.unusedSectionVars false

/-! ### Part (A): per-coordinate semialgebraic continuity from a semialgebraic curve -/

/-- The scalar function of a coordinate equals the polynomial-projection composed with the curve. -/
theorem scalarFun_coord_eq {n : ℕ} (σ : (Fin 1 → R) → (Fin n → R)) (c : Fin n) :
    Azurite.BPR.scalarFun (fun w => σ w c) = Azurite.BPR.polyFun (X c) ∘ σ := by
  funext w j
  simp only [Azurite.BPR.scalarFun, Azurite.BPR.constPt, Azurite.BPR.polyFun, Function.comp_apply,
    eval_X]

/-- Each coordinate of a semialgebraic, continuous curve `σ : closedRightNbhd 1 → Rⁿ` is
`IsSemialgContinuousOn (rightNbhd 1)`. -/
theorem isSemialgContinuousOn_coord_of_isSemialgebraicFunction {n : ℕ}
    {σ : (Fin 1 → R) → (Fin n → R)}
    (hσsa : IsSemialgebraicFunction (Azurite.BPR.closedRightNbhd 1) σ)
    (hσcont : ContinuousOn σ (Azurite.BPR.closedRightNbhd 1)) (c : Fin n) :
    IsSemialgContinuousOn (Azurite.BPR.rightNbhd (1 : R)) (fun w => σ w c) := by
  have hrnsub : Azurite.BPR.rightNbhd (1 : R) ⊆ Azurite.BPR.closedRightNbhd 1 := by
    intro u hu; exact ⟨hu.1.le, hu.2⟩
  have hrnsa : IsSemialgebraicSet (Azurite.BPR.rightNbhd (1 : R)) :=
    Azurite.BPR.isSemialgebraicSet_rightNbhd 1
  have hpolycont : Continuous (Azurite.BPR.polyFun (X c) : (Fin n → R) → (Fin 1 → R)) :=
    Azurite.BPR.continuous_iff_components.mpr (fun _ => Azurite.BPR.continuousR_eval (X c))
  have hcoord_cl : IsSemialgContinuousOn (Azurite.BPR.closedRightNbhd (1 : R)) (fun w => σ w c) := by
    refine ⟨?_, ?_⟩
    · show IsSemialgebraicSet
        (Azurite.BPR.funGraph (Azurite.BPR.closedRightNbhd 1) (Azurite.BPR.scalarFun (fun w => σ w c)))
      rw [scalarFun_coord_eq]
      exact Azurite.BPR.proposition_2_84 hσsa (Azurite.BPR.polyFun_isSemialgebraicFunction (X c))
        (Set.mapsTo_univ _ _)
    · rw [scalarFun_coord_eq]
      exact hpolycont.comp_continuousOn hσcont
  exact hcoord_cl.mono hrnsa hrnsub

/-! ### The limit line `z a` of the `a`-th representative branch -/


/-- The `a`-th representative branch along the curve `σ`: the projective line spanned by the `a`-th
unit representative at parameter `s` (a junk default where the representative would be zero). -/
noncomputable def branchCurve
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R)) (a : Fin m) :
    R → complexProjectiveSpace R k :=
  fun s => if hne : repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a ≠ 0
    then mkLine (repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a) hne
    else Classical.arbitrary _

/-- Every line-set element `Fin 1 → R` equals the constant point of its single entry. -/
theorem eq_constPt_self (w : Fin 1 → R) : w = Azurite.BPR.constPt (w 0) := by
  funext s; rw [Subsingleton.elim s 0]; rfl

/-- On `rightNbhd 1`, the `a`-th representative of `σ` is unit-norm. -/
theorem unit_along_curve
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R))
    (hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ)
    (a : Fin m) :
    ∀ w ∈ Azurite.BPR.rightNbhd (1 : R),
      hermNormSq (repsFromY m (σ w ∘ Fin.natAdd 1) a) = 1 := by
  intro w hw
  have hmem := hσWb (w 0) hw.1 hw.2
  rw [← eq_constPt_self w] at hmem
  exact ((mem_Wb_iff m P d γ (σ w)).mp hmem).2 a

/-- **Steps (A)+(B): the limit line.** The representative branch `branchCurve σ a` has a projective
limit `z a` at `0⁺`. -/
theorem exists_branch_limit
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R))
    (hσsa : IsSemialgebraicFunction (Azurite.BPR.closedRightNbhd 1) σ)
    (hσcont : ContinuousOn σ (Azurite.BPR.closedRightNbhd 1))
    (hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ)
    (a : Fin m) :
    ∃ (z : complexProjectiveSpace R k) (i : Fin (k + 1)),
      z.rep i ≠ 0 ∧
      ∃ a' : R, 0 < a' ∧ (∀ s, 0 < s → s < a' → (branchCurve m σ a s).rep i ≠ 0) ∧
        (∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
          (∀ j, |Ri.reL (chartInv i (branchCurve m σ a s) j) - Ri.reL (chartInv i z j)| < r) ∧
          (∀ j, |Ri.imL (chartInv i (branchCurve m σ a s) j) - Ri.imL (chartInv i z j)| < r)) := by
  classical
  have hunit := unit_along_curve m P d γ σ hσWb a
  have hq : ∀ c, IsSemialgContinuousOn (Azurite.BPR.rightNbhd (1 : R)) (fun w => σ w c) :=
    fun c => isSemialgContinuousOn_coord_of_isSemialgebraicFunction hσsa hσcont c
  have hmom : ∀ idx : MomentIndex k, IsSemialgContinuousOn (Azurite.BPR.rightNbhd (1 : R))
      (fun w => momentFn (repsFromY m (σ w ∘ Fin.natAdd 1) a) idx) :=
    fun idx => isSemialgContinuousOn_momentFn_repsFromY m
      (Azurite.BPR.isSemialgebraicSet_rightNbhd 1) σ hq a hunit idx
  -- `momentMap (branchCurve s) idx = momentFn (repsFromY (σ (constPt s)) a) idx` (unit ⇒ nonzero)
  have hbranch_moment : ∀ (w : Fin 1 → R), w ∈ Azurite.BPR.rightNbhd (1 : R) → ∀ idx,
      momentMap (branchCurve m σ a (w 0)) idx
        = momentFn (repsFromY m (σ w ∘ Fin.natAdd 1) a) idx := by
    intro w hw idx
    have hcw : (Azurite.BPR.constPt (w 0) : Fin 1 → R) ∈ Azurite.BPR.rightNbhd (1 : R) := by
      refine ⟨hw.1, hw.2⟩
    have hunitc : hermNormSq (repsFromY m (σ (Azurite.BPR.constPt (w 0)) ∘ Fin.natAdd 1) a) = 1 := by
      have := hunit (Azurite.BPR.constPt (w 0)) hcw
      simpa using this
    have hne : repsFromY m (σ (Azurite.BPR.constPt (w 0)) ∘ Fin.natAdd 1) a ≠ 0 := by
      intro h0
      rw [h0, hermNormSq_eq_zero_iff.mpr rfl] at hunitc
      exact one_ne_zero hunitc.symm
    rw [branchCurve, dif_pos hne, momentMap_mkLine, ← eq_constPt_self w]
  -- discharge `projective_curve_limit`'s hypothesis
  have hcont : ∀ idx : MomentIndex k,
      IsSemialgContinuousOn (Azurite.BPR.rightNbhd (1 : R))
        (fun w : Fin 1 → R => momentMap (branchCurve m σ a (w 0)) idx) := by
    intro idx
    refine IsSemialgContinuousOn.congr (hmom idx) (fun w hw => ?_)
    exact (hbranch_moment w hw idx).symm
  exact projective_curve_limit 1 one_pos (branchCurve m σ a) hcont

/-! ### Step (C): passing a real-polynomial zero condition to the curve limit -/

/-- Coordinatewise smallness implies euclidean-norm smallness. -/
theorem euclideanNorm_lt_of_coords {N : ℕ} (a : Fin N → R) {δ : R} (hδ : 0 < δ)
    (h : ∀ j, |a j| < δ / (N + 1)) :
    Azurite.BPR.euclideanNorm a < δ := by
  classical
  have hbnd : Azurite.BPR.euclideanNormSq a ≤ ∑ _j : Fin N, (δ / (N + 1)) ^ 2 := by
    rw [Azurite.BPR.euclideanNormSq]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have := h j
    nlinarith [abs_nonneg (a j), sq_abs (a j), this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbnd
  have hpos : (0 : R) < (N + 1 : R) := by positivity
  have hsq : Azurite.BPR.euclideanNorm a ^ 2 ≤ (N : R) * (δ / (N + 1)) ^ 2 := by
    rw [Azurite.BPR.euclideanNorm_sq]; exact hbnd
  have hNlt : (N : R) * (δ / (N + 1)) ^ 2 < δ ^ 2 := by
    have heq : (N : R) * (δ / (N + 1)) ^ 2 = (N : R) * δ ^ 2 / (N + 1) ^ 2 := by
      rw [div_pow]; ring
    rw [heq, div_lt_iff₀ (by positivity)]
    have hδsq : 0 < δ ^ 2 := by positivity
    have hNn : (0 : R) ≤ (N : R) := Nat.cast_nonneg N
    have hNlt2 : (N : R) < (N + 1 : R) ^ 2 := by nlinarith [hNn]
    nlinarith [mul_lt_mul_of_pos_left hNlt2 hδsq]
  have hlt : Azurite.BPR.euclideanNorm a ^ 2 < δ ^ 2 := lt_of_le_of_lt hsq hNlt
  nlinarith [Azurite.BPR.euclideanNorm_nonneg a, hlt, hδ]

/-- **Eval-limit.** If a curve `f : R → Rᴺ` converges coordinatewise to `b` at `0⁺` (ε–δ) and a real
polynomial `Q` vanishes along `f` on a right-neighborhood `(0, c)` of `0`, then `eval b Q = 0`. -/
theorem eval_eq_zero_of_curve_limit {N : ℕ} (f : R → (Fin N → R)) (b : Fin N → R)
    (Q : MvPolynomial (Fin N) R) (c : R) (hc : 0 < c)
    (hconv : ∀ j, ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → |f s j - b j| < r)
    (hzero : ∀ s : R, 0 < s → s < c → eval (f s) Q = 0) :
    eval b Q = 0 := by
  classical
  by_contra hne
  -- `ε := |eval b Q| > 0`; use continuity of `eval _ Q` and the convergence to derive a contradiction.
  set ε : R := |eval b Q| with hε
  have hεpos : 0 < ε := abs_pos.mpr hne
  obtain ⟨δ0, hδ0, hδ0Q⟩ := Azurite.BPR.continuousR_eval Q b ε hεpos
  -- coordinatewise: pick a common `δ` so `|f s j - b j| < δ0/(N+1)` for all `j`, `s ∈ (0,δ)`.
  have hrm : 0 < δ0 / (N + 1) := by positivity
  obtain ⟨δ, hδpos, hδle, hδall⟩ :=
    exists_common_eventual_bound c hc (fun j s => |f s j - b j| < δ0 / (N + 1))
      (fun j => hconv j (δ0 / (N + 1)) hrm)
  -- evaluate at `s := min δ c / 2`
  set s : R := min δ c / 2 with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hsδ : s < δ := by
    rw [hs]; have : min δ c ≤ δ := min_le_left _ _; linarith [hδpos, min_le_right δ c, hc]
  have hsc : s < c := by
    rw [hs]; have : min δ c ≤ c := min_le_right _ _; linarith [hδpos, min_le_left δ c, hc]
  have hcoords : ∀ j, |f s j - b j| < δ0 / (N + 1) := fun j => hδall s hspos hsδ j
  have hnorm : Azurite.BPR.euclideanNorm (f s - b) < δ0 := by
    refine euclideanNorm_lt_of_coords (f s - b) hδ0 (fun j => ?_)
    rw [Pi.sub_apply]; exact hcoords j
  have hQ := hδ0Q (f s) hnorm
  simp only [hzero s hspos hsc, zero_sub, abs_neg] at hQ
  exact lt_irrefl _ hQ

/-- The pencil zero condition transfers between a nonzero vector and the line it spans. -/
theorem aeval_mkLine_homotopyPoly_zero
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (lam mu : Ri R)
    (v : Fin (k + 1) → Ri R) (hv : v ≠ 0) (i' : Fin k)
    (h : aeval v (homotopyPoly P d lam mu i') = 0) :
    aeval (mkLine v hv).rep (homotopyPoly P d lam mu i') = 0 := by
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul v hv
  rw [hrep, aeval_smul_isHomogeneous (homotopyPoly_isHomogeneous P d hP _ _ i') c v, h, mul_zero]

/-- `projW` is continuous (real topology): a coordinate selection. -/
theorem continuous_projW : Continuous (projW m : (Fin (1 + (m * (k + 1) + m * (k + 1))) → R) → (Fin 1 → R)) :=
  Azurite.BPR.continuous_iff_components.mpr
    (fun j => Azurite.BPR.continuousR_coord (Fin.castAdd (m * (k + 1) + m * (k + 1)) j))

/-- **Step (C) `γ`-block convergence.** The realified chart coordinates of `γ` along the curve
converge to those of `γ t₀`, in the ε–δ sense. -/
theorem gammaBlock_converges
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R))
    (hσcont : ContinuousOn σ (Azurite.BPR.closedRightNbhd 1))
    (hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ)
    {ζstar : Fin (1 + (m * (k + 1) + m * (k + 1))) → R} (hζeq : σ (Azurite.BPR.constPt 0) = ζstar)
    {t₀ : Fin 1 → R} (ht₀eq : projW m ζstar = t₀) (ht₀Icc : t₀ ∈ Set.Icc (0 : Fin 1 → R) 1)
    (i₀ : Fin 2) (hi₀ : γ t₀ ∈ chartSet i₀) :
    ∀ (c : Fin (1 + 1)), ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
      |realEquiv (chartInv i₀ (γ (projW m (σ (Azurite.BPR.constPt s))))) c
        - realEquiv (chartInv i₀ (γ t₀)) c| < r := by
  classical
  -- the composite `h u = realEquiv (chartInv i₀ (γ (projW (σ u))))`, continuous-within at `constPt 0`.
  set h : (Fin 1 → R) → (Fin (1 + 1) → R) :=
    fun u => realEquiv (chartInv i₀ (γ (projW m (σ u)))) with hh
  have hcl0 : (Azurite.BPR.constPt 0 : Fin 1 → R) ∈ Azurite.BPR.closedRightNbhd 1 :=
    ⟨le_refl 0, one_pos⟩
  -- `σ` continuous-within at `constPt 0`
  have hσcwa : ContinuousWithinAt σ (Azurite.BPR.closedRightNbhd 1) (Azurite.BPR.constPt 0) :=
    hσcont _ hcl0
  -- `projW ∘ σ` continuous-within at `constPt 0`
  have hpσcwa : ContinuousWithinAt (fun u => projW m (σ u)) (Azurite.BPR.closedRightNbhd 1)
      (Azurite.BPR.constPt 0) :=
    (continuous_projW m).continuousWithinAt.comp hσcwa (Set.mapsTo_univ _ _)
  -- MapsTo `projW ∘ σ : closedRightNbhd 1 → Icc 0 1`
  have hmapsIcc : Set.MapsTo (fun u => projW m (σ u)) (Azurite.BPR.closedRightNbhd 1)
      (Set.Icc (0 : Fin 1 → R) 1) := by
    intro u hu
    by_cases hu0 : u 0 = 0
    · have huc : u = Azurite.BPR.constPt 0 := by
        rw [eq_constPt_self u, hu0]
      show projW m (σ u) ∈ _
      rw [huc, hζeq, ht₀eq]; exact ht₀Icc
    · have hu0pos : 0 < u 0 := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have huc : u = Azurite.BPR.constPt (u 0) := eq_constPt_self u
      have hmem := hσWb (u 0) hu0pos hu.2
      rw [← huc] at hmem
      have := ((mem_Wb_iff m P d γ (σ u)).mp hmem).1.1
      show projW m (σ u) ∈ _
      rw [projW_eq_witW]; exact this
  -- `γ ∘ (projW ∘ σ)` continuous-within at `constPt 0` (value `γ t₀`)
  have hval0 : (fun u => projW m (σ u)) (Azurite.BPR.constPt 0) = t₀ := by
    show projW m (σ (Azurite.BPR.constPt 0)) = t₀; rw [hζeq, ht₀eq]
  have hγpt0 : γ (projW m (σ (Azurite.BPR.constPt 0))) = γ t₀ := by rw [hζeq, ht₀eq]
  have hγcwa : ContinuousWithinAt (fun u => γ (projW m (σ u))) (Azurite.BPR.closedRightNbhd 1)
      (Azurite.BPR.constPt 0) := by
    have hγt₀ : ContinuousWithinAt γ (Set.Icc (0 : Fin 1 → R) 1)
        ((fun u => projW m (σ u)) (Azurite.BPR.constPt 0)) := by
      rw [hval0]; exact hγcont t₀ ht₀Icc
    exact ContinuousWithinAt.comp (g := γ) (f := fun u => projW m (σ u)) hγt₀ hpσcwa hmapsIcc
  -- `realEquiv ∘ chartInv i₀ ∘ γ ∘ projW ∘ σ` continuous-within at `constPt 0` (value `realEquiv(chartInv i₀ (γ t₀))`)
  have hchart_cwa : ContinuousWithinAt
      (fun x : complexProjectiveSpace R 1 => realEquiv (chartInv i₀ x)) (chartSet i₀)
      ((fun u => γ (projW m (σ u))) (Azurite.BPR.constPt 0)) := by
    show ContinuousWithinAt _ _ (γ (projW m (σ (Azurite.BPR.constPt 0))))
    rw [hγpt0]
    exact (continuousOn_realEquiv_chartInv i₀).continuousWithinAt hi₀
  have hmapsChart : Set.MapsTo (fun u => γ (projW m (σ u)))
      (Azurite.BPR.closedRightNbhd 1 ∩ (fun u => γ (projW m (σ u))) ⁻¹' chartSet i₀)
      (chartSet i₀) := fun u hu => hu.2
  have hhcwa : ContinuousWithinAt h (Azurite.BPR.closedRightNbhd 1) (Azurite.BPR.constPt 0) := by
    rw [hh]
    have hcomp := ContinuousWithinAt.comp
      (g := fun x : complexProjectiveSpace R 1 => realEquiv (chartInv i₀ x))
      (f := fun u => γ (projW m (σ u))) hchart_cwa (hγcwa.mono Set.inter_subset_left) hmapsChart
    -- value: `(realEquiv ∘ chartInv i₀) (γ t₀)`
    have hpre : (fun u => γ (projW m (σ u))) ⁻¹' chartSet i₀
        ∈ nhdsWithin (Azurite.BPR.constPt 0 : Fin 1 → R) (Azurite.BPR.closedRightNbhd 1) := by
      have := hγcwa.preimage_mem_nhdsWithin
        ((isOpen_chartSet i₀).mem_nhds (by
          show γ (projW m (σ (Azurite.BPR.constPt 0))) ∈ chartSet i₀
          rw [hγpt0]; exact hi₀))
      exact this
    have hmem : Azurite.BPR.closedRightNbhd 1 ∩ (fun u => γ (projW m (σ u))) ⁻¹' chartSet i₀
        ∈ nhdsWithin (Azurite.BPR.constPt 0) (Azurite.BPR.closedRightNbhd 1) :=
      Filter.inter_mem self_mem_nhdsWithin hpre
    exact hcomp.mono_of_mem_nhdsWithin hmem
  -- convert `ContinuousWithinAt` at `constPt 0` to the ε–δ form in `s`.
  have hball_form : ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧
      ∀ u ∈ Azurite.BPR.closedRightNbhd 1,
        Azurite.BPR.euclideanNorm (u - Azurite.BPR.constPt 0) < δ →
        Azurite.BPR.euclideanNorm (h u - h (Azurite.BPR.constPt 0)) < r := by
    intro r hr
    have hb : (nhdsWithin (Azurite.BPR.constPt 0 : Fin 1 → R) (Azurite.BPR.closedRightNbhd 1)).HasBasis
        (fun δ : R => 0 < δ)
        (fun δ => Azurite.BPR.openBall (Azurite.BPR.constPt 0 : Fin 1 → R) δ
          ∩ Azurite.BPR.closedRightNbhd 1) :=
      (Azurite.BPR.nhds_hasBasis_openBall (Azurite.BPR.constPt 0 : Fin 1 → R)).inf_principal _
    rw [ContinuousWithinAt,
      hb.tendsto_iff (Azurite.BPR.nhds_hasBasis_openBall (h (Azurite.BPR.constPt 0)))] at hhcwa
    obtain ⟨δ, hδ, hδh⟩ := hhcwa r hr
    refine ⟨δ, hδ, fun u hu hund => ?_⟩
    have := hδh u ⟨(Azurite.BPR.mem_openBall_iff_norm hδ).mpr hund, hu⟩
    exact (Azurite.BPR.mem_openBall_iff_norm (by assumption)).mp this
  intro c r hr
  obtain ⟨δ, hδ, hδb⟩ := hball_form r hr
  refine ⟨min δ 1, lt_min hδ one_pos, fun s hs hsδ => ?_⟩
  have hsmem : (Azurite.BPR.constPt s : Fin 1 → R) ∈ Azurite.BPR.closedRightNbhd 1 :=
    ⟨hs.le, lt_of_lt_of_le hsδ (min_le_right _ _)⟩
  have hsnorm : Azurite.BPR.euclideanNorm
      ((Azurite.BPR.constPt s : Fin 1 → R) - Azurite.BPR.constPt 0) < δ := by
    rw [show (Azurite.BPR.constPt s : Fin 1 → R) - Azurite.BPR.constPt 0 = Azurite.BPR.constPt s from by
      funext j; simp [Azurite.BPR.constPt], Azurite.BPR.euclideanNorm_fin_one]
    show |s| < δ; rw [abs_of_pos hs]; exact lt_of_lt_of_le hsδ (min_le_left _ _)
  have hball := hδb (Azurite.BPR.constPt s) hsmem hsnorm
  -- `hball : euclideanNorm (h (constPt s) - h (constPt 0)) < r`; extract coordinate `c`.
  have hcoord : |h (Azurite.BPR.constPt s) c - h (Azurite.BPR.constPt 0) c| < r := by
    calc |h (Azurite.BPR.constPt s) c - h (Azurite.BPR.constPt 0) c|
        = |(h (Azurite.BPR.constPt s) - h (Azurite.BPR.constPt 0)) c| := by rw [Pi.sub_apply]
      _ ≤ Azurite.BPR.euclideanNorm (h (Azurite.BPR.constPt s) - h (Azurite.BPR.constPt 0)) :=
          Azurite.BPR.abs_coord_le_norm _ c
      _ < r := hball
  -- rewrite `h (constPt 0) = realEquiv (chartInv i₀ (γ t₀))`.
  have hh0 : h (Azurite.BPR.constPt 0) = realEquiv (chartInv i₀ (γ t₀)) := by
    rw [hh]; show realEquiv (chartInv i₀ (γ (projW m (σ (Azurite.BPR.constPt 0))))) = _
    rw [hζeq, ht₀eq]
  rw [hh0] at hcoord
  exact hcoord

/-- **Eventually in chart.** Near `0⁺`, the curve point `γ(projW(σ(constPt s)))` lies in `chartSet i₀`. -/
theorem gammaBlock_eventually_chart
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R))
    (hσcont : ContinuousOn σ (Azurite.BPR.closedRightNbhd 1))
    (hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ)
    {ζstar : Fin (1 + (m * (k + 1) + m * (k + 1))) → R} (hζeq : σ (Azurite.BPR.constPt 0) = ζstar)
    {t₀ : Fin 1 → R} (ht₀eq : projW m ζstar = t₀) (ht₀Icc : t₀ ∈ Set.Icc (0 : Fin 1 → R) 1)
    (i₀ : Fin 2) (hi₀ : γ t₀ ∈ chartSet i₀) :
    ∃ a' : R, 0 < a' ∧
      ∀ s : R, 0 < s → s < a' → γ (projW m (σ (Azurite.BPR.constPt s))) ∈ chartSet i₀ := by
  classical
  have hcl0 : (Azurite.BPR.constPt 0 : Fin 1 → R) ∈ Azurite.BPR.closedRightNbhd 1 :=
    ⟨le_refl 0, one_pos⟩
  have hσcwa : ContinuousWithinAt σ (Azurite.BPR.closedRightNbhd 1) (Azurite.BPR.constPt 0) :=
    hσcont _ hcl0
  have hpσcwa : ContinuousWithinAt (fun u => projW m (σ u)) (Azurite.BPR.closedRightNbhd 1)
      (Azurite.BPR.constPt 0) :=
    (continuous_projW m).continuousWithinAt.comp hσcwa (Set.mapsTo_univ _ _)
  have hmapsIcc : Set.MapsTo (fun u => projW m (σ u)) (Azurite.BPR.closedRightNbhd 1)
      (Set.Icc (0 : Fin 1 → R) 1) := by
    intro u hu
    by_cases hu0 : u 0 = 0
    · have huc : u = Azurite.BPR.constPt 0 := by rw [eq_constPt_self u, hu0]
      show projW m (σ u) ∈ _; rw [huc, hζeq, ht₀eq]; exact ht₀Icc
    · have hu0pos : 0 < u 0 := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have huc : u = Azurite.BPR.constPt (u 0) := eq_constPt_self u
      have hmem := hσWb (u 0) hu0pos hu.2
      rw [← huc] at hmem
      have := ((mem_Wb_iff m P d γ (σ u)).mp hmem).1.1
      show projW m (σ u) ∈ _; rw [projW_eq_witW]; exact this
  have hγpt0 : γ (projW m (σ (Azurite.BPR.constPt 0))) = γ t₀ := by rw [hζeq, ht₀eq]
  have hval0 : (fun u => projW m (σ u)) (Azurite.BPR.constPt 0) = t₀ := by
    show projW m (σ (Azurite.BPR.constPt 0)) = t₀; rw [hζeq, ht₀eq]
  have hγcwa : ContinuousWithinAt (fun u => γ (projW m (σ u))) (Azurite.BPR.closedRightNbhd 1)
      (Azurite.BPR.constPt 0) := by
    have hγt₀ : ContinuousWithinAt γ (Set.Icc (0 : Fin 1 → R) 1)
        ((fun u => projW m (σ u)) (Azurite.BPR.constPt 0)) := by
      rw [hval0]; exact hγcont t₀ ht₀Icc
    exact ContinuousWithinAt.comp (g := γ) (f := fun u => projW m (σ u)) hγt₀ hpσcwa hmapsIcc
  -- the preimage of the (open) chart is a right-neighborhood of `constPt 0`.
  have hpre : (fun u => γ (projW m (σ u))) ⁻¹' chartSet i₀
      ∈ nhdsWithin (Azurite.BPR.constPt 0 : Fin 1 → R) (Azurite.BPR.closedRightNbhd 1) :=
    hγcwa.preimage_mem_nhdsWithin ((isOpen_chartSet i₀).mem_nhds (by
      show γ (projW m (σ (Azurite.BPR.constPt 0))) ∈ chartSet i₀; rw [hγpt0]; exact hi₀))
  rw [mem_nhdsWithin] at hpre
  obtain ⟨O, hOopen, h0O, hOsub⟩ := hpre
  obtain ⟨ρ, hρ, hρsub⟩ := Azurite.BPR.mem_nhds_iff_openBall.mp (hOopen.mem_nhds h0O)
  refine ⟨min ρ 1, lt_min hρ one_pos, fun s hs hsδ => ?_⟩
  have hsmem : (Azurite.BPR.constPt s : Fin 1 → R) ∈ Azurite.BPR.closedRightNbhd 1 :=
    ⟨hs.le, lt_of_lt_of_le hsδ (min_le_right _ _)⟩
  have hsball : (Azurite.BPR.constPt s : Fin 1 → R)
      ∈ Azurite.BPR.openBall (Azurite.BPR.constPt 0) ρ := by
    rw [Azurite.BPR.mem_openBall_iff_norm hρ,
      show (Azurite.BPR.constPt s : Fin 1 → R) - Azurite.BPR.constPt 0 = Azurite.BPR.constPt s from by
        funext j; simp [Azurite.BPR.constPt], Azurite.BPR.euclideanNorm_fin_one]
    show |s| < ρ; rw [abs_of_pos hs]; exact lt_of_lt_of_le hsδ (min_le_left _ _)
  have := hOsub ⟨hρsub hsball, hsmem⟩
  exact this

/-- **Projective convergence of a branch.** Given the ε–δ chart-coordinate convergence of the branch
(from `exists_branch_limit`), the branch converges to `z` in the projective topology: it eventually
enters any neighborhood of `z`. -/
theorem branch_eventually_mem_nhd
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R)) (a : Fin m)
    {z : complexProjectiveSpace R k} {iₐ : Fin (k + 1)} (hzrep : z.rep iₐ ≠ 0)
    {a' : R} (ha' : 0 < a')
    (hbrep : ∀ s, 0 < s → s < a' → (branchCurve m σ a s).rep iₐ ≠ 0)
    (hbconv : ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
      (∀ j, |Ri.reL (chartInv iₐ (branchCurve m σ a s) j) - Ri.reL (chartInv iₐ z j)| < r) ∧
      (∀ j, |Ri.imL (chartInv iₐ (branchCurve m σ a s) j) - Ri.imL (chartInv iₐ z j)| < r))
    {V : Set (complexProjectiveSpace R k)} (hV : V ∈ nhds z) :
    ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ → branchCurve m σ a s ∈ V := by
  classical
  -- preimage of `V` under `chartMap iₐ ∘ realEquivₜ.symm` is a nhd of `realEquiv (chartInv iₐ z)`.
  set G : (Fin (k + k) → R) → complexProjectiveSpace R k :=
    fun w => chartMap iₐ ((realEquivₜ (R := R) (k := k)).symm w) with hG
  have hGcont : Continuous G :=
    (continuous_chartMap iₐ).comp (realEquivₜ (R := R) (k := k)).symm.continuous
  have hGz : G (realEquiv (chartInv iₐ z)) = z := by
    rw [hG]
    show chartMap iₐ ((realEquivₜ (R := R) (k := k)).symm (realEquiv (chartInv iₐ z))) = z
    rw [show ((realEquivₜ (R := R) (k := k)).symm (realEquiv (chartInv iₐ z)) : Fin k → Ri R)
        = realEquiv.symm (realEquiv (chartInv iₐ z)) from rfl, Equiv.symm_apply_apply]
    exact chartMap_chartInv iₐ z hzrep
  have hpre : G ⁻¹' V ∈ nhds (realEquiv (chartInv iₐ z)) := by
    have hca := hGcont.continuousAt (x := realEquiv (chartInv iₐ z))
    refine hca.preimage_mem_nhds ?_
    rw [hGz]; exact hV
  obtain ⟨ρ, hρ, hρsub⟩ := Azurite.BPR.mem_nhds_iff_openBall.mp hpre
  -- choose `δ` from the coordinatewise convergence so that the realified chart coords land in the ball.
  obtain ⟨δ, hδ, hδb⟩ := hbconv (ρ / ((k + k : ℕ) + 1)) (by positivity)
  refine ⟨min δ a', lt_min hδ ha', fun s hs hsδ => ?_⟩
  have hsδ' : s < δ := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsa' : s < a' := lt_of_lt_of_le hsδ (min_le_right _ _)
  -- norm of the difference of realified chart coords < ρ
  have hnorm : Azurite.BPR.euclideanNorm
      (realEquiv (chartInv iₐ (branchCurve m σ a s)) - realEquiv (chartInv iₐ z)) < ρ := by
    refine euclideanNorm_lt_of_coords _ hρ (fun c => ?_)
    rw [Pi.sub_apply]
    refine Fin.addCases (motive := fun c =>
        |realEquiv (chartInv iₐ (branchCurve m σ a s)) c - realEquiv (chartInv iₐ z) c|
          < ρ / ((k + k : ℕ) + 1)) (fun j => ?_) (fun j => ?_) c
    · rw [realEquiv_apply_castAdd, realEquiv_apply_castAdd]; exact (hδb s hs hsδ').1 j
    · rw [realEquiv_apply_natAdd, realEquiv_apply_natAdd]; exact (hδb s hs hsδ').2 j
  -- so `realEquiv (chartInv iₐ (branchCurve s)) ∈ openBall ... ρ ⊆ G ⁻¹' V`
  have hmem : realEquiv (chartInv iₐ (branchCurve m σ a s)) ∈ G ⁻¹' V :=
    hρsub ((Azurite.BPR.mem_openBall_iff_norm hρ).mpr hnorm)
  -- and `G (realEquiv (chartInv iₐ (branchCurve s))) = branchCurve s` (it lies in chartSet iₐ).
  have hbchart : (branchCurve m σ a s).rep iₐ ≠ 0 := hbrep s hs hsa'
  have hGb : G (realEquiv (chartInv iₐ (branchCurve m σ a s))) = branchCurve m σ a s := by
    rw [hG]
    show chartMap iₐ ((realEquivₜ (R := R) (k := k)).symm
        (realEquiv (chartInv iₐ (branchCurve m σ a s)))) = branchCurve m σ a s
    rw [show ((realEquivₜ (R := R) (k := k)).symm
          (realEquiv (chartInv iₐ (branchCurve m σ a s))) : Fin k → Ri R)
        = realEquiv.symm (realEquiv (chartInv iₐ (branchCurve m σ a s))) from rfl,
      Equiv.symm_apply_apply]
    exact chartMap_chartInv iₐ (branchCurve m σ a s) hbchart
  rw [Set.mem_preimage, hGb] at hmem
  exact hmem

/-- **Eventually in an open set.** If `U` is open and `γ t₀ ∈ U`, then near `0⁺` the curve point
`γ(projW(σ(constPt s)))` lies in `U`. -/
theorem eventually_gamma_mem_open
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R))
    (hσcont : ContinuousOn σ (Azurite.BPR.closedRightNbhd 1))
    (hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ)
    {ζstar : Fin (1 + (m * (k + 1) + m * (k + 1))) → R} (hζeq : σ (Azurite.BPR.constPt 0) = ζstar)
    {t₀ : Fin 1 → R} (ht₀eq : projW m ζstar = t₀) (ht₀Icc : t₀ ∈ Set.Icc (0 : Fin 1 → R) 1)
    {U : Set (complexProjectiveSpace R 1)} (hUopen : IsOpen U) (hUmem : γ t₀ ∈ U) :
    ∃ a' : R, 0 < a' ∧
      ∀ s : R, 0 < s → s < a' → γ (projW m (σ (Azurite.BPR.constPt s))) ∈ U := by
  classical
  have hcl0 : (Azurite.BPR.constPt 0 : Fin 1 → R) ∈ Azurite.BPR.closedRightNbhd 1 :=
    ⟨le_refl 0, one_pos⟩
  have hσcwa : ContinuousWithinAt σ (Azurite.BPR.closedRightNbhd 1) (Azurite.BPR.constPt 0) :=
    hσcont _ hcl0
  have hpσcwa : ContinuousWithinAt (fun u => projW m (σ u)) (Azurite.BPR.closedRightNbhd 1)
      (Azurite.BPR.constPt 0) :=
    (continuous_projW m).continuousWithinAt.comp hσcwa (Set.mapsTo_univ _ _)
  have hmapsIcc : Set.MapsTo (fun u => projW m (σ u)) (Azurite.BPR.closedRightNbhd 1)
      (Set.Icc (0 : Fin 1 → R) 1) := by
    intro u hu
    by_cases hu0 : u 0 = 0
    · have huc : u = Azurite.BPR.constPt 0 := by rw [eq_constPt_self u, hu0]
      show projW m (σ u) ∈ _; rw [huc, hζeq, ht₀eq]; exact ht₀Icc
    · have hu0pos : 0 < u 0 := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have huc : u = Azurite.BPR.constPt (u 0) := eq_constPt_self u
      have hmem := hσWb (u 0) hu0pos hu.2
      rw [← huc] at hmem
      have := ((mem_Wb_iff m P d γ (σ u)).mp hmem).1.1
      show projW m (σ u) ∈ _; rw [projW_eq_witW]; exact this
  have hγpt0 : γ (projW m (σ (Azurite.BPR.constPt 0))) = γ t₀ := by rw [hζeq, ht₀eq]
  have hval0 : (fun u => projW m (σ u)) (Azurite.BPR.constPt 0) = t₀ := by
    show projW m (σ (Azurite.BPR.constPt 0)) = t₀; rw [hζeq, ht₀eq]
  have hγcwa : ContinuousWithinAt (fun u => γ (projW m (σ u))) (Azurite.BPR.closedRightNbhd 1)
      (Azurite.BPR.constPt 0) := by
    have hγt₀ : ContinuousWithinAt γ (Set.Icc (0 : Fin 1 → R) 1)
        ((fun u => projW m (σ u)) (Azurite.BPR.constPt 0)) := by
      rw [hval0]; exact hγcont t₀ ht₀Icc
    exact ContinuousWithinAt.comp (g := γ) (f := fun u => projW m (σ u)) hγt₀ hpσcwa hmapsIcc
  have hpre : (fun u => γ (projW m (σ u))) ⁻¹' U
      ∈ nhdsWithin (Azurite.BPR.constPt 0 : Fin 1 → R) (Azurite.BPR.closedRightNbhd 1) :=
    hγcwa.preimage_mem_nhdsWithin (hUopen.mem_nhds (by
      show γ (projW m (σ (Azurite.BPR.constPt 0))) ∈ U; rw [hγpt0]; exact hUmem))
  rw [mem_nhdsWithin] at hpre
  obtain ⟨O, hOopen, h0O, hOsub⟩ := hpre
  obtain ⟨ρ, hρ, hρsub⟩ := Azurite.BPR.mem_nhds_iff_openBall.mp (hOopen.mem_nhds h0O)
  refine ⟨min ρ 1, lt_min hρ one_pos, fun s hs hsδ => ?_⟩
  have hsmem : (Azurite.BPR.constPt s : Fin 1 → R) ∈ Azurite.BPR.closedRightNbhd 1 :=
    ⟨hs.le, lt_of_lt_of_le hsδ (min_le_right _ _)⟩
  have hsball : (Azurite.BPR.constPt s : Fin 1 → R)
      ∈ Azurite.BPR.openBall (Azurite.BPR.constPt 0) ρ := by
    rw [Azurite.BPR.mem_openBall_iff_norm hρ,
      show (Azurite.BPR.constPt s : Fin 1 → R) - Azurite.BPR.constPt 0 = Azurite.BPR.constPt s from by
        funext j; simp [Azurite.BPR.constPt], Azurite.BPR.euclideanNorm_fin_one]
    show |s| < ρ; rw [abs_of_pos hs]; exact lt_of_lt_of_le hsδ (min_le_left _ _)
  exact hOsub ⟨hρsub hsball, hsmem⟩

/-- **Step (C): the limit line `z a` is a common zero of `S₍γ t₀₎`.** -/
theorem branchLimit_isCommonZero
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (σ : (Fin 1 → R) → (Fin (1 + (m * (k + 1) + m * (k + 1))) → R))
    (hσcont : ContinuousOn σ (Azurite.BPR.closedRightNbhd 1))
    (hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ)
    {ζstar : Fin (1 + (m * (k + 1) + m * (k + 1))) → R} (hζeq : σ (Azurite.BPR.constPt 0) = ζstar)
    {t₀ : Fin 1 → R} (ht₀eq : projW m ζstar = t₀) (ht₀Icc : t₀ ∈ Set.Icc (0 : Fin 1 → R) 1)
    (i₀ : Fin 2) (hi₀ : γ t₀ ∈ chartSet i₀) (a : Fin m)
    {z : complexProjectiveSpace R k} {iₐ : Fin (k + 1)} (hzrep : z.rep iₐ ≠ 0)
    {a' : R} (ha' : 0 < a')
    (hbrep : ∀ s, 0 < s → s < a' → (branchCurve m σ a s).rep iₐ ≠ 0)
    (hbconv : ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
      (∀ j, |Ri.reL (chartInv iₐ (branchCurve m σ a s) j) - Ri.reL (chartInv iₐ z j)| < r) ∧
      (∀ j, |Ri.imL (chartInv iₐ (branchCurve m σ a s) j) - Ri.imL (chartInv iₐ z j)| < r)) :
    ∀ i', aeval z.rep (homotopyPoly P d ((γ t₀).rep 0) ((γ t₀).rep 1) i') = 0 := by
  classical
  -- the two convergence inputs
  have hγconv := gammaBlock_converges m P d γ hγcont σ hσcont hσWb hζeq ht₀eq ht₀Icc i₀ hi₀
  obtain ⟨aγ, haγ, hγchart⟩ :=
    gammaBlock_eventually_chart m P d γ hγcont σ hσcont hσWb hζeq ht₀eq ht₀Icc i₀ hi₀
  -- the limit real point `z*`
  set zstar : Fin ((1 + 1) + (k + k)) → R :=
    Fin.append (realEquiv (chartInv i₀ (γ t₀))) (realEquiv (chartInv iₐ z)) with hzstar
  -- the curve real point `f s`
  set f : R → (Fin ((1 + 1) + (k + k)) → R) := fun s =>
    Fin.append (realEquiv (chartInv i₀ (γ (projW m (σ (Azurite.BPR.constPt s))))))
      (realEquiv (chartInv iₐ (branchCurve m σ a s))) with hf
  -- the common bound below which `branchCurve s` and the γ-chart are valid and `s < 1`
  set c0 : R := min (min a' aγ) 1 with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; exact lt_min (lt_min ha' haγ) one_pos
  -- per real-equation `l`, `eval (f s) Q_l = 0` on `(0, c0)`.
  have hkey : ∀ i', aeval z.rep (homotopyPoly P d ((γ t₀).rep 0) ((γ t₀).rep 1) i') = 0 := by
    -- it suffices to show all `homotopyF` vanish at `zstar`, then apply the bridge at `(γ t₀, z)`.
    have hFzstar : ∀ l, homotopyF P d i₀ iₐ l zstar = 0 := by
      intro l
      obtain ⟨Q, hQ⟩ := exists_homotopyF_eq_eval P d i₀ iₐ l
      -- `eval (f s) Q = 0` on `(0, c0)`
      have hzeroQ : ∀ s : R, 0 < s → s < c0 → eval (f s) Q = 0 := by
        intro s hs hsc0
        have hsa' : s < a' := lt_of_lt_of_le hsc0 (le_trans (min_le_left _ _) (min_le_left _ _))
        have hsaγ : s < aγ := lt_of_lt_of_le hsc0 (le_trans (min_le_left _ _) (min_le_right _ _))
        have hs1 : s < 1 := lt_of_lt_of_le hsc0 (min_le_right _ _)
        -- `γ(w(s)) ∈ chartSet i₀`, `branchCurve s ∈ chartSet iₐ`
        have hγs : γ (projW m (σ (Azurite.BPR.constPt s))) ∈ chartSet i₀ := hγchart s hs hsaγ
        have hbs : branchCurve m σ a s ∈ chartSet iₐ := by
          rw [chartSet_eq]; exact hbrep s hs hsa'
        -- the `a`-th representative validity at `w(s)`
        have hmem := hσWb s hs hs1
        have hvalid := ((mem_Wb_iff m P d γ (σ (Azurite.BPR.constPt s))).mp hmem).1.2
        -- `branchCurve s = mkLine (repsFromY ...)`
        have hrepne : repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a ≠ 0 := by
          intro h0
          have hunit := ((mem_Wb_iff m P d γ (σ (Azurite.BPR.constPt s))).mp hmem).2 a
          rw [h0, hermNormSq_eq_zero_iff.mpr rfl] at hunit
          exact one_ne_zero hunit.symm
        have hbranch_eq : branchCurve m σ a s
            = mkLine (repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a) hrepne := by
          rw [branchCurve, dif_pos hrepne]
        -- the projective parameter `p := γ(w(s))`; `aeval (repsFromY a) (homotopyPoly p) = 0`
        have hzeroP : ∀ i', aeval (branchCurve m σ a s).rep
            (homotopyPoly P d ((γ (projW m (σ (Azurite.BPR.constPt s)))).rep 0)
              ((γ (projW m (σ (Azurite.BPR.constPt s)))).rep 1) i') = 0 := by
          intro i'
          rw [hbranch_eq]
          refine aeval_mkLine_homotopyPoly_zero P d hP _ _ _ hrepne i' ?_
          have hwitW : witW m (σ (Azurite.BPR.constPt s)) = projW m (σ (Azurite.BPR.constPt s)) :=
            (projW_eq_witW m _).symm
          have := hvalid.2.2 a i'
          rw [hwitW] at this
          exact this
        -- the bridge: `homotopyF ... (f s) = 0`
        have hF0 := (homotopyF_eq_zero_iff P d hP i₀ iₐ
          (γ (projW m (σ (Azurite.BPR.constPt s)))) (branchCurve m σ a s) hγs hbs).mpr hzeroP
        rw [← hQ (f s)]
        exact hF0 l
      -- coordinatewise convergence of `f s` to `zstar`
      have hconv : ∀ cc : Fin ((1 + 1) + (k + k)), ∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧
          ∀ s : R, 0 < s → s < δ → |f s cc - zstar cc| < r := by
        intro cc r hr
        refine Fin.addCases (motive := fun cc => ∃ δ : R, 0 < δ ∧
            ∀ s : R, 0 < s → s < δ → |f s cc - zstar cc| < r) (fun b => ?_) (fun b => ?_) cc
        · -- γ-chart block
          obtain ⟨δ, hδ, hδb⟩ := hγconv b r hr
          refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
          have hfb : f s (Fin.castAdd (k + k) b)
              = realEquiv (chartInv i₀ (γ (projW m (σ (Azurite.BPR.constPt s))))) b := by
            rw [hf]; exact Fin.append_left _ _ b
          have hzb : zstar (Fin.castAdd (k + k) b) = realEquiv (chartInv i₀ (γ t₀)) b := by
            rw [hzstar]; exact Fin.append_left _ _ b
          rw [hfb, hzb]; exact hδb s hs hsδ
        · -- branch-chart block (real/imag of the chart coords)
          obtain ⟨δ, hδ, hδb⟩ := hbconv r hr
          refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
          have hfb : f s (Fin.natAdd (1 + 1) b)
              = realEquiv (chartInv iₐ (branchCurve m σ a s)) b := by
            rw [hf]; exact Fin.append_right _ _ b
          have hzb : zstar (Fin.natAdd (1 + 1) b) = realEquiv (chartInv iₐ z) b := by
            rw [hzstar]; exact Fin.append_right _ _ b
          rw [hfb, hzb]
          -- `b` decomposes into a real (castAdd) or imaginary (natAdd) chart coordinate
          refine Fin.addCases (motive := fun b =>
              |realEquiv (chartInv iₐ (branchCurve m σ a s)) b - realEquiv (chartInv iₐ z) b| < r)
            (fun j => ?_) (fun j => ?_) b
          · rw [realEquiv_apply_castAdd, realEquiv_apply_castAdd]
            exact (hδb s hs hsδ).1 j
          · rw [realEquiv_apply_natAdd, realEquiv_apply_natAdd]
            exact (hδb s hs hsδ).2 j
      -- apply the eval-limit
      rw [hQ zstar]
      exact eval_eq_zero_of_curve_limit f zstar Q c0 hc0pos hconv hzeroQ
    -- now `homotopyF ... zstar = 0`; apply the bridge at `(γ t₀, z)`
    have hzmem : z ∈ chartSet iₐ := by rw [chartSet_eq]; exact hzrep
    have hbridge := (homotopyF_eq_zero_iff P d hP i₀ iₐ (γ t₀) z hi₀ hzmem).mp
    -- `zstar = Fin.append (realEquiv (chartInv i₀ (γ t₀))) (realEquiv (chartInv iₐ z))`
    exact hbridge hFzstar
  exact hkey

/-! ### The capstone: relative closedness of `Pm m` and Proposition 4.106 -/

/-- **BPR Proposition 4.106, gap (c): `Pm m` is relatively closed in `(0,1]`.** -/
theorem pm_isClosedIn (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (γ : (Fin 1 → R) → complexProjectiveSpace R 1)
    (hγcont : ContinuousOn γ (Set.Icc (0 : Fin 1 → R) 1))
    (_hγ0 : γ (0 : Fin 1 → R) = pencilPt10 (R := R))
    (_hγ1 : γ (1 : Fin 1 → R) = pencilPt01 (R := R))
    (hγΔ : ∀ w ∈ intervalSet (R := R), γ w ∉ deltaSet P d)
    (hgraphRP : IsSemialgebraicSetRP
      {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
        tp.1 ∈ Set.Icc (0 : Fin 1 → R) 1 ∧ tp.2 = γ tp.1}) (m : ℕ) :
    IsClosedIn (intervalSet (R := R)) (Pm P d γ m) := by
  classical
  refine isClosedIn_of_closure_inter_subset P d γ m (fun t₀ ht₀ => ?_)
  obtain ⟨ht₀I, ht₀cl⟩ := ht₀
  -- `t₀ ∈ Icc 0 1`
  have ht₀Icc : t₀ ∈ Set.Icc (0 : Fin 1 → R) 1 := by
    rw [show (0 : Fin 1 → R) = Azurite.BPR.constPt 0 from rfl, one_eq_constPt,
      mem_Icc_fin_one_local]
    rw [mem_intervalSet] at ht₀I; exact ⟨ht₀I.1.le, ht₀I.2⟩
  -- `γ t₀ ∉ Δ`
  have hγΔ₀ : γ t₀ ∉ deltaSet P d := hγΔ t₀ ht₀I
  -- chart for `γ t₀`
  obtain ⟨i₀, hi₀⟩ := exists_mem_chartSet (γ t₀)
  -- closure point of `Wb`
  obtain ⟨ζstar, hζcl, hζeq⟩ := exists_closurePt_Wb m P d hP γ hgraphRP ht₀cl
  have hunitζ := unit_of_mem_closure_Wb m P d γ hζcl
  -- curve selection on `Wb`
  obtain ⟨σ, hσsa, hσcont, hσ0, hσWb1⟩ :=
    Azurite.BPR.theorem_3_19 (Wb m P d γ) (isSemialgebraicSet_Wb m P d γ hgraphRP) ζstar hζcl
  have hσWb : ∀ s : R, 0 < s → s < 1 → σ (Azurite.BPR.constPt s) ∈ Wb m P d γ := hσWb1
  have hζeq' : σ (Azurite.BPR.constPt 0) = ζstar := hσ0
  have ht₀eq : projW m ζstar = t₀ := hζeq
  -- per `a`: branch limit and common-zero membership.
  have hbranch : ∀ a : Fin m, ∃ (z : complexProjectiveSpace R k) (iₐ : Fin (k + 1)),
      z.rep iₐ ≠ 0 ∧ (∀ i', aeval z.rep (homotopyPoly P d ((γ t₀).rep 0) ((γ t₀).rep 1) i') = 0) ∧
      ∃ a' : R, 0 < a' ∧ (∀ s, 0 < s → s < a' → (branchCurve m σ a s).rep iₐ ≠ 0) ∧
        (∀ r : R, 0 < r → ∃ δ : R, 0 < δ ∧ ∀ s : R, 0 < s → s < δ →
          (∀ j, |Ri.reL (chartInv iₐ (branchCurve m σ a s) j) - Ri.reL (chartInv iₐ z j)| < r) ∧
          (∀ j, |Ri.imL (chartInv iₐ (branchCurve m σ a s) j) - Ri.imL (chartInv iₐ z j)| < r)) := by
    intro a
    obtain ⟨z, iₐ, hzrep, a', ha', hbrep, hbconv⟩ :=
      exists_branch_limit m P d γ σ hσsa hσcont hσWb a
    refine ⟨z, iₐ, hzrep, ?_, a', ha', hbrep, hbconv⟩
    exact branchLimit_isCommonZero m P d hP γ hγcont σ hσcont hσWb hζeq' ht₀eq ht₀Icc i₀ hi₀ a
      hzrep ha' hbrep hbconv
  choose zfn ifn hzrep hzero a' ha' hbrep hbconv using hbranch
  -- each `zfn a` is a non-singular projective zero of `S₍γ t₀₎`.
  have hns : ∀ a, IsNonsingularProjectiveZero
      (homotopyPoly P d ((γ t₀).rep 0) ((γ t₀).rep 1)) (zfn a) := fun a =>
    notMem_deltaSet_nonsingular P d (γ t₀) hγΔ₀ (zfn a) (hzero a)
  -- the branch line is `mkLine (repsFromY ...)` on `(0, small)`, with the `a`-th rep validity.
  have hbranch_eq : ∀ (a : Fin m) (s : R), 0 < s → s < 1 →
      ∃ hrepne : repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a ≠ 0,
        branchCurve m σ a s = mkLine (repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a) hrepne := by
    intro a s hs hs1
    have hmem := hσWb s hs hs1
    have hrepne : repsFromY m (σ (Azurite.BPR.constPt s) ∘ Fin.natAdd 1) a ≠ 0 := by
      intro h0
      have hunit := ((mem_Wb_iff m P d γ (σ (Azurite.BPR.constPt s))).mp hmem).2 a
      rw [h0, hermNormSq_eq_zero_iff.mpr rfl] at hunit; exact one_ne_zero hunit.symm
    exact ⟨hrepne, by rw [branchCurve, dif_pos hrepne]⟩
  -- **Step (D): injectivity of `a ↦ zfn a`.**
  have hinj : Function.Injective zfn := by
    intro a b hzab
    by_contra hab
    -- `zfn a` non-singular; local IFT at `(γ t₀, zfn a)` with chart `ifn a`.
    have hzachart : zfn a ∈ chartSet (ifn a) := by rw [chartSet_eq]; exact hzrep a
    obtain ⟨U, V, ϕ, hUopen, hpU, hVopen, hxV, hϕx₀, hϕclass, himpl, hVchart⟩ :=
      homotopy_local_ift_chartV m P d hP (γ t₀) (zfn a) i₀ (ifn a) hi₀ hzachart (hzero a) (hns a)
    -- both branches eventually in `V` (a nhd of `zfn a = zfn b`); `γ(w(s))` eventually in `U`.
    obtain ⟨δa, hδa, hδaV⟩ :=
      branch_eventually_mem_nhd m σ a (hzrep a) (ha' a) (hbrep a) (hbconv a) (hVopen.mem_nhds hxV)
    obtain ⟨δb, hδb, hδbV⟩ :=
      branch_eventually_mem_nhd m σ b (hzrep b) (ha' b) (hbrep b) (hbconv b)
        (hVopen.mem_nhds (by rw [← hzab]; exact hxV))
    -- `γ(w(s)) ∈ U` eventually: `U` open, `γ(w(s)) → γ t₀ ∈ U`.
    obtain ⟨δGU, hδGU, hδGUU⟩ :=
      eventually_gamma_mem_open m P d γ hγcont σ hσcont hσWb hζeq' ht₀eq ht₀Icc hUopen hpU
    -- `γ(w(s)) ∈ chartSet i₀` eventually.
    obtain ⟨δGC, hδGC, hδGCC⟩ :=
      eventually_gamma_mem_open m P d γ hγcont σ hσcont hσWb hζeq' ht₀eq ht₀Icc
        (isOpen_chartSet i₀) hi₀
    -- pick a small `s` below all thresholds and `< 1`.
    set s : R := min (min δa δb) (min (min δGU δGC) (min 1 (min (a' a) (a' b)))) / 2 with hsdef
    have hspos : 0 < s := by
      rw [hsdef]
      refine half_pos (lt_min (lt_min hδa hδb)
        (lt_min (lt_min hδGU hδGC) (lt_min one_pos (lt_min (ha' a) (ha' b)))))
    have hsle : ∀ x, min (min δa δb) (min (min δGU δGC) (min 1 (min (a' a) (a' b)))) ≤ x →
        s < x := by
      intro x hx; rw [hsdef]; linarith [hspos]
    have hsδa : s < δa := hsle δa (le_trans (min_le_left _ _) (min_le_left _ _))
    have hsδb : s < δb := hsle δb (le_trans (min_le_left _ _) (min_le_right _ _))
    have hsδGU : s < δGU :=
      hsle δGU (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hsδGC : s < δGC :=
      hsle δGC (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hs1 : s < 1 :=
      hsle 1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    -- the two branch lines at `s`
    have hbaV : branchCurve m σ a s ∈ V := hδaV s hspos hsδa
    have hbbV : branchCurve m σ b s ∈ V := hδbV s hspos hsδb
    have hγU : γ (projW m (σ (Azurite.BPR.constPt s))) ∈ U := hδGUU s hspos hsδGU
    have hγC : γ (projW m (σ (Azurite.BPR.constPt s))) ∈ chartSet i₀ := hδGCC s hspos hsδGC
    -- both branch lines are zeros of `S₍γ(w(s))₎`, in chart `ifn a` (since both ∈ V ⊆ chartSet (ifn a)).
    have hzeroAt : ∀ x : complexProjectiveSpace R k, x ∈ V →
        (∀ i', aeval x.rep (homotopyPoly P d
          ((γ (projW m (σ (Azurite.BPR.constPt s)))).rep 0)
          ((γ (projW m (σ (Azurite.BPR.constPt s)))).rep 1) i') = 0) →
        x = ϕ (γ (projW m (σ (Azurite.BPR.constPt s)))) := by
      intro x hxV hxzero
      have hxchart : x ∈ chartSet (ifn a) := hVchart x hxV
      have hcoord : ∀ l, homotopyF P d i₀ (ifn a) l
          (Fin.append (realEquiv (chartInv i₀ (γ (projW m (σ (Azurite.BPR.constPt s))))))
            (realEquiv (chartInv (ifn a) x))) = 0 :=
        (homotopyF_eq_zero_iff P d hP i₀ (ifn a) (γ (projW m (σ (Azurite.BPR.constPt s)))) x
          hγC hxchart).mpr hxzero
      exact (himpl (γ (projW m (σ (Azurite.BPR.constPt s)))) hγU x hxV).mp hcoord
    -- the common-zero condition along the curve for branch `c` (`c = a, b`)
    have hbzero : ∀ c : Fin m, ∀ i', aeval (branchCurve m σ c s).rep (homotopyPoly P d
        ((γ (projW m (σ (Azurite.BPR.constPt s)))).rep 0)
        ((γ (projW m (σ (Azurite.BPR.constPt s)))).rep 1) i') = 0 := by
      intro c i'
      obtain ⟨hrepne, hbeq⟩ := hbranch_eq c s hspos hs1
      rw [hbeq]
      refine aeval_mkLine_homotopyPoly_zero P d hP _ _ _ hrepne i' ?_
      have hmem := hσWb s hspos hs1
      have hvalid := ((mem_Wb_iff m P d γ (σ (Azurite.BPR.constPt s))).mp hmem).1.2
      have hwitW : witW m (σ (Azurite.BPR.constPt s)) = projW m (σ (Azurite.BPR.constPt s)) :=
        (projW_eq_witW m _).symm
      have := hvalid.2.2 c i'
      rw [hwitW] at this; exact this
    -- both branch lines equal `ϕ(γ(w(s)))`, hence equal each other.
    have heqa := hzeroAt (branchCurve m σ a s) hbaV (hbzero a)
    have heqb := hzeroAt (branchCurve m σ b s) hbbV (hbzero b)
    have hbranch_same : branchCurve m σ a s = branchCurve m σ b s := by rw [heqa, heqb]
    -- but the `m` branch lines are pairwise distinct (non-proportional reps).
    obtain ⟨hrepa, hbeqa⟩ := hbranch_eq a s hspos hs1
    obtain ⟨hrepb, hbeqb⟩ := hbranch_eq b s hspos hs1
    have hmem := hσWb s hspos hs1
    have hminor := ((mem_Wb_iff m P d γ (σ (Azurite.BPR.constPt s))).mp hmem).1.2.2.1 a b hab
    obtain ⟨j, l, hjl⟩ := hminor
    apply hjl
    rw [hbeqa, hbeqb] at hbranch_same
    exact (mkLine_eq_iff_minors_vanish _ _ hrepa hrepb).mp hbranch_same j l
  -- assemble `AtLeastZeros`.
  refine ⟨ht₀I, zfn, hinj, fun a i' => ?_⟩
  exact hzero a i'

set_option linter.unusedSectionVars false in
/-- **BPR Proposition 4.106 (weak Bézout).** The number of non-singular projective zeros of homogeneous
`P₁, …, P_k` of degrees `d₁, …, d_k ≥ 1` is at most `d₁ ⋯ d_k`. -/
theorem proposition_4_106 (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    {x : complexProjectiveSpace R k | IsNonsingularProjectiveZero P x}.ncard ≤ ∏ i, d i :=
  weakBezout_of_sa_of_closed P d hd hP (fun m => isSemialgebraicSetRP_atLeastZerosRP P d hP m)
    (fun γ hc h0 h1 hΔ hg m => pm_isClosedIn P d hP γ hc h0 h1 hΔ hg m)

set_option linter.unusedSectionVars false in
/-- **Finite-subset form of Proposition 4.106.** Every finite set `F` of non-singular projective
zeros of homogeneous `P₁, …, P_k` of degrees `d₁, …, d_k ≥ 1` has cardinality at most `d₁ ⋯ d_k`.
This refines `proposition_4_106` (which only bounds the `ncard`) so that finite collections of zeros
can be bounded directly, e.g. through an injection from affine non-singular zeros (Theorem 4.107). -/
theorem proposition_4_106_finsetCard (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (F : Finset (complexProjectiveSpace R k))
    (hF : (↑F : Set (complexProjectiveSpace R k)) ⊆ {x | IsNonsingularProjectiveZero P x}) :
    F.card ≤ ∏ i, d i :=
  weakBezout_finsetCard_of_sa_of_closed P d hd hP (fun m => isSemialgebraicSetRP_atLeastZerosRP P d hP m)
    (fun γ hc h0 h1 hΔ hg m => pm_isClosedIn P d hP γ hc h0 h1 hΔ hg m) F hF

end Azurite.BPR.Chapter4
