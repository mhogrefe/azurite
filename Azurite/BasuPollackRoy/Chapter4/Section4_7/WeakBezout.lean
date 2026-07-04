import Azurite.BasuPollackRoy.Chapter4.Section4_7.DiagonalCount
import Azurite.BasuPollackRoy.Chapter4.Section4_7.HomotopyIFTDet
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveComplete
import Azurite.BasuPollackRoy.Chapter4.Section4_7.Lemma_4_105
import Azurite.BasuPollackRoy.Chapter4.Section4_7.DeltaFinite

/-!
# BPR §4.7, Proposition 4.106: the homotopy-continuation pieces

This file assembles the pieces produced in `Section4_7/` towards the **weak Bézout bound**
`{x | IsNonsingularProjectiveZero P x}.ncard ≤ ∏ i, d i`. The counting step uses an injection `τ`
carrying non-singular zeros of `P = S₍₁:₀₎` to common zeros of the diagonal system `S₍₀:₁₎`.

BPR builds `τ` by **homotopy continuation**: deform `P` to the diagonal system along the pencil
`S₍λ:µ₎`, follow a semialgebraic path `γ : [0,1] → ℙ₁(C)` from `(1:0)` to `(0:1)` whose interior
avoids the finite singular-parameter set `Δ`, and continue each non-singular zero `x` of `P` along
`γ` (via the local implicit function theorem `homotopy_local_ift'` for openness and projective
completeness `projective_curve_limit` for the limit step) to a zero `σ_x(1)` of `S₍₀:₁₎`.

The pieces collected and proven here, all axiom-clean:

* `pencilPt01`, `pencilPt10` — the two pencil endpoints `(0:1)`, `(1:0)` of `ℙ₁(C)` and their
  parameter coordinates (`pencilPt01_rep_param`, `pencilPt10_rep_param`).
* `homotopyPoly_at_pencilPt01` — at `(0:1)` the pencil is `µ · Dᵢ` (a unit multiple of the diagonal
  factor), so a projective zero of `S₍₀:₁₎` is a common zero of the diagonal system
  (`zero_at_pencilPt01_iff_diagSystem`, the **diagonal-endpoint bridge**).
* `deltaFinset` — the singular-parameter set `Δ ⊆ ℙ₁(C)` packaged as a `Finset` (from `delta_finite`),
  with `pencilPt01_notMem_deltaFinset` recording `(0:1) ∉ Δ`.
* `gammaPath` — a semialgebraic path on `(↑Δ)ᶜ` joining `(1:0)`(if available) to `(0:1)`; more
  precisely, the path connecting any two points of `(↑Δ)ᶜ` from `lemma_4_105`.
* `mem_delta_iff_exists_singular` — membership of `Δ` is the existence of a singular projective zero
  of `S₍λ:µ₎`; its contrapositive `notMem_delta_all_nonsingular` says that off `Δ` every projective
  zero of the pencil is non-singular (the hypothesis the continuation needs at each `t ∈ (0,1]`).

The global clopen path-lift over `[0,1]` producing `σ_x` and the injection `τ` is developed in the
fiber-cardinality files (`WeakBezoutCount` and downstream).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### The two pencil endpoints of `ℙ₁(C)` -/

/-- The pencil endpoint `(0 : 1) ∈ ℙ₁(C)`, the parameter at which the pencil is the diagonal system
`S₍₀:₁₎`. -/
noncomputable def pencilPt01 : complexProjectiveSpace R 1 :=
  mkLine (![0, 1] : Fin 2 → Ri R) vec01_ne_zero

/-- The pencil endpoint `(1 : 0) ∈ ℙ₁(C)`, the parameter at which the pencil is the original system
`S₍₁:₀₎ = (P₁, …, P_k)`. -/
noncomputable def pencilPt10 : complexProjectiveSpace R 1 :=
  mkLine (![1, 0] : Fin 2 → Ri R) (vec1t_ne_zero 0)

set_option linter.unusedSectionVars false in
/-- The representative of `(0 : 1)` is a nonzero scalar multiple `c • ![0,1]`. -/
theorem pencilPt01_rep :
    ∃ c : Ri R, c ≠ 0 ∧ (pencilPt01 (R := R)).rep = c • (![0, 1] : Fin 2 → Ri R) := by
  apply (mkLine_eq_mkLine_iff (pencilPt01 (R := R)).rep _ (pencilPt01 (R := R)).rep_nonzero
    vec01_ne_zero).mp
  rw [show mkLine (pencilPt01 (R := R)).rep (pencilPt01 (R := R)).rep_nonzero = pencilPt01 from
    Projectivization.mk_rep _]
  rfl

set_option linter.unusedSectionVars false in
/-- The parameter coordinates of `(0 : 1)`: `λ = 0`, `µ = c ≠ 0`. -/
theorem pencilPt01_rep_param :
    ∃ c : Ri R, c ≠ 0 ∧ (pencilPt01 (R := R)).rep 0 = 0 ∧ (pencilPt01 (R := R)).rep 1 = c := by
  obtain ⟨c, hc, hrep⟩ := pencilPt01_rep (R := R)
  exact ⟨c, hc, by rw [hrep]; simp, by rw [hrep]; simp⟩

/-! ### The diagonal-endpoint bridge -/

set_option linter.unusedSectionVars false in
/-- At the parameter `(λ, µ) = (0, c)` the homotopy pencil is `c · Dᵢ`. -/
theorem homotopyPoly_zero_left (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (c : Ri R) (i : Fin k) :
    homotopyPoly P d 0 c i = C c * diagFactor (d i) i := by
  rw [homotopyPoly, map_zero, zero_mul, zero_add]

set_option linter.unusedSectionVars false in
/-- **Diagonal-endpoint bridge.** A point `x` is a common projective zero of the pencil at the
parameter `(0 : 1)` iff it is a common projective zero of the diagonal system `S₍₀:₁₎`. -/
theorem zero_at_pencilPt01_iff_diagSystem (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (x : complexProjectiveSpace R k) :
    (∀ i, aeval x.rep (homotopyPoly P d ((pencilPt01 (R := R)).rep 0)
        ((pencilPt01 (R := R)).rep 1) i) = 0)
      ↔ (∀ i, aeval x.rep (diagSystem (R := R) d i) = 0) := by
  obtain ⟨c, hc, hlam, hmu⟩ := pencilPt01_rep_param (R := R)
  rw [hlam, hmu]
  refine forall_congr' fun i => ?_
  rw [homotopyPoly_zero_left, map_mul, aeval_C, Algebra.algebraMap_self_apply, diagSystem]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hc
  · intro h; rw [h, mul_zero]

/-! ### The singular-parameter set `Δ` -/

/-- The singular-parameter set `Δ ⊆ ℙ₁(C)`: the projection on `ℙ₁(C)` of the locus of singular
projective zeros of the pencil `S₍λ:µ₎`, viewed as a subset of `ℙ₁(C)` (after the trivial reindexing
`Fin 1 → ℙ₁(C) ↦ ℙ₁(C)` evaluating at the single index `0`). -/
def deltaSet (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    Set (complexProjectiveSpace R 1) :=
  {p | ∃ x : complexProjectiveSpace R k,
      (∀ i, aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) i) = 0) ∧
      (projJacobian (homotopyPoly P d (p.rep 0) (p.rep 1)) x).rank < k}

set_option linter.unusedSectionVars false in
/-- `p ∈ Δ` iff the pencil `S₍p₎` has a singular projective zero (a common zero with rank-deficient
projective Jacobian). -/
theorem mem_deltaSet_iff (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (p : complexProjectiveSpace R 1) :
    p ∈ deltaSet P d ↔
      ∃ x : complexProjectiveSpace R k,
        (∀ i, aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) i) = 0) ∧
        (projJacobian (homotopyPoly P d (p.rep 0) (p.rep 1)) x).rank < k :=
  Iff.rfl

set_option linter.unusedSectionVars false in
/-- **Off `Δ` every projective zero of the pencil is non-singular.** If `p ∉ Δ` then any common
projective zero of `S₍p₎` has full-rank projective Jacobian, hence is a non-singular projective zero.
This is exactly the hypothesis the homotopy continuation needs at each path parameter `t ∈ (0,1]`. -/
theorem notMem_deltaSet_nonsingular (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (p : complexProjectiveSpace R 1) (hp : p ∉ deltaSet P d)
    (x : complexProjectiveSpace R k)
    (hx : ∀ i, aeval x.rep (homotopyPoly P d (p.rep 0) (p.rep 1) i) = 0) :
    IsNonsingularProjectiveZero (homotopyPoly P d (p.rep 0) (p.rep 1)) x := by
  refine ⟨hx, ?_⟩
  -- the projective Jacobian rank is `≤ k`; if it were `< k`, `p` would be in `Δ`.
  have hle : (projJacobian (homotopyPoly P d (p.rep 0) (p.rep 1)) x).rank ≤ k := by
    have := Matrix.rank_le_card_height (projJacobian (homotopyPoly P d (p.rep 0) (p.rep 1)) x)
    rwa [Fintype.card_fin] at this
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact absurd ⟨x, hx, hlt⟩ hp
  · exact heq

/-! ### `Δ` is finite -/

set_option linter.unusedSectionVars false in
/-- `Δ` is the image under `f ↦ f 0` of the projection of the singular locus used in `delta_finite`. -/
theorem deltaSet_eq_image (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ) :
    deltaSet P d
      = (fun g : Fin 1 → complexProjectiveSpace R 1 => g 0) ''
          ((fun xp : (i : Fin 2) → complexProjectiveSpace R ((![k, 1] : Fin 2 → ℕ) i) =>
              fun _ : Fin 1 => xp 1) '' singularLocus P d) := by
  ext p
  simp only [deltaSet, Set.mem_setOf_eq, Set.mem_image, singularLocus]
  constructor
  · rintro ⟨x, hzero, hrank⟩
    -- build a sigma point `xp` with `xp 0 = x`, `xp 1 = p`
    set xp : (i : Fin 2) → complexProjectiveSpace R (![k, 1] i) :=
      Fin.cons (α := fun i => complexProjectiveSpace R (![k, 1] i)) x
        (Fin.cases (motive := fun i : Fin 1 => complexProjectiveSpace R (![k, 1] i.succ)) p
          (fun i => i.elim0)) with hxp
    have hxp0 : xp 0 = x := rfl
    have hxp1 : xp 1 = p := rfl
    refine ⟨fun _ : Fin 1 => p, ⟨xp, ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · intro i; rw [hxp0, hxp1]; exact hzero i
    · rw [hxp0, hxp1]; exact hrank
    · funext j; fin_cases j; rw [hxp1]
  · rintro ⟨g, ⟨xp, ⟨hzero, hrank⟩, hg⟩, hp⟩
    refine ⟨xp 0, ?_, ?_⟩
    · intro i
      have hxp1 : xp 1 = p := by rw [← hp, ← hg]
      rw [hxp1] at hzero; exact hzero i
    · have hxp1 : xp 1 = p := by rw [← hp, ← hg]
      rw [hxp1] at hrank; exact hrank

set_option linter.unusedSectionVars false in
/-- **`Δ` is finite.** -/
theorem deltaSet_finite (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    (deltaSet P d).Finite := by
  rw [deltaSet_eq_image]
  exact (delta_finite P d hd hP).image _

/-- **`Δ` as a `Finset`.** -/
noncomputable def deltaFinset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    Finset (complexProjectiveSpace R 1) :=
  (deltaSet_finite P d hd hP).toFinset

set_option linter.unusedSectionVars false in
@[simp] theorem mem_deltaFinset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) (p : complexProjectiveSpace R 1) :
    p ∈ deltaFinset P d hd hP ↔ p ∈ deltaSet P d := by
  rw [deltaFinset, Set.Finite.mem_toFinset]

set_option linter.unusedSectionVars false in
theorem coe_deltaFinset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    (↑(deltaFinset P d hd hP) : Set (complexProjectiveSpace R 1)) = deltaSet P d := by
  rw [deltaFinset, Set.Finite.coe_toFinset]

/-! ### The diagonal endpoint `(0:1)` is not singular -/

set_option linter.unusedSectionVars false in
/-- **`(0 : 1) ∉ Δ`.** The diagonal endpoint is not a singular parameter: by Lemma B every common
projective zero of `S₍₀:₁₎` is non-singular (`diagSystem_common_zero_isNonsingular`), so the pencil at
`(0:1)` has no singular projective zero. -/
theorem pencilPt01_notMem_deltaSet (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) :
    pencilPt01 (R := R) ∉ deltaSet P d := by
  rintro ⟨x, hzero, hrank⟩
  obtain ⟨c, hc, hlam, hmu⟩ := pencilPt01_rep_param (R := R)
  rw [hlam, hmu] at hzero hrank
  exact not_singular_at_diag P d hd x c hc hzero hrank

set_option linter.unusedSectionVars false in
theorem pencilPt01_notMem_deltaFinset (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i)) :
    pencilPt01 (R := R) ∉ deltaFinset P d hd hP := by
  rw [mem_deltaFinset]; exact pencilPt01_notMem_deltaSet P d hd

/-! ### The semialgebraic path avoiding `Δ` -/

set_option linter.unusedSectionVars false in
/-- **The semialgebraic path on `ℙ₁(C) ∖ Δ` (from `lemma_4_105`).** Any two points off `Δ` are joined
by a continuous semialgebraic path `γ : [0,1] → ℙ₁(C)` lying entirely in the complement of `Δ`. In
particular, taking the second endpoint to be `(0:1)` (which is off `Δ`, `pencilPt01_notMem_deltaSet`),
this furnishes the BPR deformation path landing at the diagonal parameter; for a first endpoint off
`Δ` the whole path — including both endpoints — avoids `Δ`.

When `(1:0) ∈ Δ` (i.e. `P` itself has a singular zero), the continuation is started at `t = 0` from
the non-singular zero `x` of `P = S₍₁:₀₎` directly, and only the interior `γ((0,1])` need avoid `Δ`;
that half-open variant is the form consumed by the lift. -/
theorem exists_gammaPath_off_delta (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hd : ∀ i, 1 ≤ d i) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (x : complexProjectiveSpace R 1) (hx : x ∉ deltaSet P d) :
    ∃ γ : (Fin 1 → R) → complexProjectiveSpace R 1,
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.MapsTo γ (Set.Icc 0 1) ((↑(deltaFinset P d hd hP))ᶜ) ∧
      γ 0 = x ∧ γ 1 = pencilPt01 ∧
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R 1 |
          tp.1 ∈ Set.Icc 0 1 ∧ tp.2 = γ tp.1} := by
  have hxc : x ∈ ((↑(deltaFinset P d hd hP))ᶜ : Set (complexProjectiveSpace R 1)) := by
    rw [Set.mem_compl_iff, coe_deltaFinset]; exact hx
  have h01c : pencilPt01 (R := R)
      ∈ ((↑(deltaFinset P d hd hP))ᶜ : Set (complexProjectiveSpace R 1)) := by
    rw [Set.mem_compl_iff, coe_deltaFinset]; exact pencilPt01_notMem_deltaSet P d hd
  exact lemma_4_105 (deltaFinset P d hd hP) x hxc pencilPt01 h01c

/-! ### The local continuation step (openness ingredient of the clopen lift) -/

set_option linter.unusedSectionVars false in
/-- **Local continuation off `Δ`.** Let `p₀ ∉ Δ` lie in chart `i₀`, let `x₀ ∈ chart j₀` be a common
projective zero of the pencil `S₍p₀₎`. Since `p₀ ∉ Δ`, `x₀` is automatically a *non-singular*
projective zero (`notMem_deltaSet_nonsingular`), so the local implicit function theorem
`homotopy_local_ift'` applies: there are open neighborhoods `U ∋ p₀`, `V ∋ x₀` and an `𝒮^m` map
`ϕ : ℙ₁(C) → ℙ_k(C)` with `ϕ p₀ = x₀` such that, for `p ∈ U` and `x ∈ V`, `x` is a common projective
zero of `S₍p₎` iff `x = ϕ p`.  This is the openness ingredient of the path-lift: it extends a partial
lift from `p₀` to a neighborhood, with local uniqueness of the continued zero. -/
theorem local_continuation_off_delta (m : ℕ) (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (p₀ : complexProjectiveSpace R 1) (x₀ : complexProjectiveSpace R k)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (hp₀ : p₀ ∈ chartSet i₀) (hx₀ : x₀ ∈ chartSet j₀)
    (hp₀Δ : p₀ ∉ deltaSet P d)
    (hzero : ∀ i, aeval x₀.rep (homotopyPoly P d (p₀.rep 0) (p₀.rep 1) i) = 0) :
    ∃ (U : Set (complexProjectiveSpace R 1)) (V : Set (complexProjectiveSpace R k))
      (ϕ : complexProjectiveSpace R 1 → complexProjectiveSpace R k),
      IsOpen U ∧ p₀ ∈ U ∧ IsOpen V ∧ x₀ ∈ V ∧ ϕ p₀ = x₀ ∧
      IsSClassMapP m U V ϕ ∧
      (∀ p ∈ U, ∀ x ∈ V,
        ((∀ l, homotopyF P d i₀ j₀ l
            (Fin.append (realEquiv (chartInv i₀ p)) (realEquiv (chartInv j₀ x))) = 0)
          ↔ x = ϕ p)) := by
  have hns : IsNonsingularProjectiveZero (homotopyPoly P d (p₀.rep 0) (p₀.rep 1)) x₀ :=
    notMem_deltaSet_nonsingular P d p₀ hp₀Δ x₀ hzero
  exact homotopy_local_ift' m P d hP p₀ x₀ i₀ j₀ hp₀ hx₀ hzero hns

/-! ### The endpoint target: zeros of `S₍₀:₁₎` land in the diagonal-zero set -/

set_option linter.unusedSectionVars false in
/-- **Endpoint target.** A common projective zero of the pencil at `(0:1)` is a non-singular
projective zero of the diagonal system `S₍₀:₁₎` (via the diagonal-endpoint bridge
`zero_at_pencilPt01_iff_diagSystem` and Lemma B). This is the membership condition consumed by
`weakBezout_of_injection` for the endpoint of each continued zero. -/
theorem zero_at_pencilPt01_isNonsingular_diag (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R))
    (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) (x : complexProjectiveSpace R k)
    (hx : ∀ i, aeval x.rep (homotopyPoly P d ((pencilPt01 (R := R)).rep 0)
        ((pencilPt01 (R := R)).rep 1) i) = 0) :
    IsNonsingularProjectiveZero (diagSystem (R := R) d) x :=
  diagSystem_common_zero_isNonsingular d hd x
    ((zero_at_pencilPt01_iff_diagSystem P d x).mp hx)

end Azurite.BPR.Chapter4
