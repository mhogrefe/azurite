import Azurite.BasuPollackRoy.Chapter1.Section1_3.SplitLast
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula
import Azurite.BasuPollackRoy.Chapter2.Section2_3.SemialgebraicQF
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# BPR Theorem 2.62 — Projection of an Algebraic Set is Semialgebraic

BPR Theorem 2.62. The projection of an algebraic subset of `R^(k+1)`
defined over a subring `D ⊆ R` to `R^k` is a semialgebraic subset of
`R^k` defined over `D`.

The proof, following BPR and mirroring the structure of
`theorem_1_22` from `Azurite/BasuPollackRoy/Chapter1/Section1_3/Theorem1_22.lean`,
goes in three steps:

1. **Reduction to a single polynomial.** By sum-of-squares over a
   linearly ordered field, every algebraic-over-`D` set `V ⊆ R^k`
   equals `{x | aeval x P = 0}` for a single `P` (the sum of squares
   of the witness finset). See `IsAlgebraicSetOver.exists_singleton`.

2. **Image-of-projection rewrite.** The image of
   `{z ∈ R^(k+1) | aeval z P = 0}` under `Fin.init` (drop the last
   coordinate) equals the y-section
   `{y | ∃ x : R, aeval (Fin.snoc y x) P = 0}` -- the "fiber non-empty"
   predicate. See `Fin.init_image_eq_exists_aeval`.

3. **Sturm-Tarski content.** The "fiber non-empty" predicate is
   semialgebraic over `D`. This is the substantive content, going
   through the leaves of `TRems(P̃, ∂P̃/∂X)` (over the root truncations
   `P̃ ∈ Tru(splitLast P)`) and sign-condition realisations, following
   BPR's Theorem 2.62 proof outline.
   See `fiber_nonempty_isSemialgebraicSetOver`.

Step 3 dispatches on `(splitLast P).natDegree`:
* `natDegree = 0` -- `fiber_nonempty_isSemialgebraicSetOver_degx_zero`.
* `natDegree = 1` -- `fiber_nonempty_isSemialgebraicSetOver_degx_one`.
* `natDegree ≥ 2` -- the Sturm-Tarski content, reduced to
  `fiberFormula_high_realization` in
  `Azurite/BasuPollackRoy/Chapter2/Section2_3/FiberFormula.lean`
  via the QF formula `fiberFormula_high P`.

The Sturm-Tarski core lives in `FiberFormula.lean`: the bridge
`sturmCount_eq_actual_varAt_diff` matches the abstract sign-pattern
count to the actual `varAt(SRemS)` sign-change difference, proved by a
term-by-term positive-scalar correspondence (`PosAssoc`) between the
specialised TRems pseudo-remainder sequence and the true signed
remainder sequence. See `THEOREM_2_62_PLAN.md` for the development
record.
-/

namespace Azurite.BPR

open MvPolynomial

/-- A subset `V ⊆ R^k` is *algebraic and defined over* `D` if it is
the zero set of a finite collection of polynomials with coefficients
in `D`, evaluated in `R` via `aeval`. -/
def IsAlgebraicSetOver (D : Type*) [CommRing D] {k : ℕ}
    {R : Type*} [Field R] [Algebra D R]
    (V : Set (Fin k → R)) : Prop :=
  ∃ poly_set : Finset (MvPolynomial (Fin k) D),
    V = {x | ∀ P ∈ poly_set, aeval x P = 0}

variable {k : ℕ} {D : Type*} [CommRing D]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R]

omit [IsStrictOrderedRing R] in
/-- An algebraic set defined over `D` is in particular a semialgebraic
set defined over `D`: the `IsSemialgebraicSetOver` inductive's
`algebraic` constructor accepts the same witness. -/
theorem IsSemialgebraicSetOver.of_isAlgebraicSetOver
    {V : Set (Fin k → R)} (h : IsAlgebraicSetOver D V) :
    IsSemialgebraicSetOver D V :=
  .algebraic h

/-- **Sum-of-squares reduction.** Every algebraic-over-`D` set is the
zero set of a *single* polynomial in `D[X_1, …, X_k]`: take the sum of
squares of the witness finset. Over a linearly ordered field, a sum
of squares vanishes iff each square does, iff each summand does. -/
theorem IsAlgebraicSetOver.exists_singleton
    {V : Set (Fin k → R)} (h : IsAlgebraicSetOver D V) :
    ∃ P : MvPolynomial (Fin k) D, V = {x | aeval x P = 0} := by
  obtain ⟨poly_set, rfl⟩ := h
  refine ⟨∑ P ∈ poly_set, P ^ 2, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, map_sum, map_pow]
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro P hP; rw [h P hP]; ring
  · intro h P hP
    have hnn : ∀ Q ∈ poly_set, 0 ≤ (aeval x Q) ^ 2 := fun _ _ => sq_nonneg _
    have h_sq : (aeval x P) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h P hP
    exact sq_eq_zero_iff.mp h_sq

omit [IsStrictOrderedRing R] [LinearOrder R] in
/-- The image of `{z | aeval z P = 0}` under the projection
`Fin.init : R^(k+1) → R^k` equals the y-section "fiber non-empty"
predicate. -/
theorem Fin.init_image_eq_exists_aeval
    (P : MvPolynomial (Fin (k+1)) D) :
    (Fin.init '' ({z : Fin (k+1) → R | aeval z P = 0})) =
      {y : Fin k → R | ∃ x : R, aeval (Fin.snoc y x) P = 0} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z (Fin.last k), ?_⟩
    rwa [Fin.snoc_init_self z]
  · rintro ⟨x, hx⟩
    refine ⟨Fin.snoc y x, hx, ?_⟩
    simp

omit [IsStrictOrderedRing R] in
/-- Base case: the trivial polynomial `P = 0`. The fiber-non-empty
predicate becomes `R^k` (every `(y, x)` is a zero of `0`). -/
theorem fiber_nonempty_isSemialgebraicSetOver_zero :
    IsSemialgebraicSetOver D
      ({y : Fin k → R |
        ∃ x : R, aeval (Fin.snoc y x) (0 : MvPolynomial (Fin (k+1)) D) = 0}) := by
  have heq : ({y : Fin k → R |
      ∃ x : R, aeval (Fin.snoc y x) (0 : MvPolynomial (Fin (k+1)) D) = 0} : Set _) =
        Set.univ := by
    ext y
    simp only [Set.mem_setOf_eq, map_zero, Set.mem_univ, iff_true]
    exact ⟨(0 : R), trivial⟩
  rw [heq]
  exact IsSemialgebraicSetOver.algebraic ⟨∅, by ext y; simp⟩

omit [IsStrictOrderedRing R] in
/-- Base case: linear-in-X polynomials.
When `(splitLast P).natDegree = 1`, write
`splitLast P = C b + C a * X` for `a = (splitLast P).coeff 1`,
`b = (splitLast P).coeff 0`. Then
`∃ x : R, aeval (Fin.snoc y x) P = 0` iff `aeval y a ≠ 0 ∨ aeval y b = 0`
(over a field): if `a(y) ≠ 0` use `x = -b(y) / a(y)`; if `a(y) = 0` the
equation collapses to `b(y) = 0`. -/
theorem fiber_nonempty_isSemialgebraicSetOver_degx_one
    (P : MvPolynomial (Fin (k+1)) D)
    (hdeg : (splitLast P).natDegree = 1) :
    IsSemialgebraicSetOver D
      ({y : Fin k → R | ∃ x : R, aeval (Fin.snoc y x) P = 0}) := by
  set a := (splitLast P).coeff 1 with ha_def
  set b := (splitLast P).coeff 0 with hb_def
  have hp_eq : splitLast P = Polynomial.C b + Polynomial.C a * Polynomial.X := by
    have h_sum := Polynomial.as_sum_range_C_mul_X_pow' (splitLast P) (n := 2)
      (by rw [hdeg]; omega)
    rw [h_sum]
    simp [Finset.sum_range_succ, pow_succ, pow_zero, ← ha_def, ← hb_def]
  have heval : ∀ (y : Fin k → R) (x : R),
      aeval (Fin.snoc y x) P = aeval y b + aeval y a * x := by
    intros y x
    rw [aeval_snoc_eq_eval_splitLast y x P]
    conv_lhs => rw [hp_eq, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_C, Polynomial.eval_X]
    rfl
  have hset : ({y : Fin k → R | ∃ x : R, aeval (Fin.snoc y x) P = 0} : Set _) =
              {y | aeval y a ≠ 0} ∪ {y | aeval y b = 0} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨x, hx⟩
      rw [heval y x] at hx
      by_cases ha : aeval y a = 0
      · right
        rw [ha, zero_mul, add_zero] at hx
        exact hx
      · exact Or.inl ha
    · rintro (ha | hb)
      · refine ⟨-(aeval y b) / aeval y a, ?_⟩
        rw [heval]
        field_simp
        ring
      · refine ⟨0, ?_⟩
        rw [heval, hb, mul_zero, add_zero]
  rw [hset]
  exact (IsSemialgebraicSetOver.neZero (R := R) a).union
    (IsSemialgebraicSetOver.eqZero (R := R) b)

omit [IsStrictOrderedRing R] in
/-- Base case: when `P` is constant in the last variable
(`(splitLast P).natDegree = 0`), the fiber-non-empty predicate reduces
to a single equation on the (lifted) constant. Specifically,
`∃ x : R, P(y, x) = 0` iff `(splitLast P).coeff 0` vanishes at `y`,
since `P(y, x)` doesn't actually depend on `x`. -/
theorem fiber_nonempty_isSemialgebraicSetOver_degx_zero
    (P : MvPolynomial (Fin (k+1)) D)
    (hdeg : (splitLast P).natDegree = 0) :
    IsSemialgebraicSetOver D
      ({y : Fin k → R | ∃ x : R, aeval (Fin.snoc y x) P = 0}) := by
  have hC : splitLast P = Polynomial.C ((splitLast P).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have heval : ∀ (y : Fin k → R) (x : R),
      aeval (Fin.snoc y x) P = aeval y ((splitLast P).coeff 0) := by
    intros y x
    rw [aeval_snoc_eq_eval_splitLast y x P]
    have hC_map : (splitLast P).map (MvPolynomial.aeval y).toRingHom =
        Polynomial.C ((MvPolynomial.aeval y) ((splitLast P).coeff 0)) := by
      conv_lhs => rw [hC, Polynomial.map_C]
      rfl
    rw [hC_map, Polynomial.eval_C]
  have hset : ({y : Fin k → R |
      ∃ x : R, aeval (Fin.snoc y x) P = 0} : Set _) =
        {y | aeval y ((splitLast P).coeff 0) = 0} := by
    ext y
    constructor
    · rintro ⟨x, hx⟩; rw [heval y x] at hx; exact hx
    · intro hy; exact ⟨(0 : R), by rw [heval y (0 : R)]; exact hy⟩
  rw [hset]
  exact IsSemialgebraicSetOver.eqZero (R := R) ((splitLast P).coeff 0)

/-- **KEY TECHNICAL LEMMA.** The "fiber non-empty"
predicate `{y | ∃ x : R, P(y, x) = 0}` is semialgebraic over `D`.
Requires `[IsRealClosed R]`: this lemma is false over arbitrary
ordered fields (e.g., `R = ℚ` with `P(Y, X) = X² - Y` gives the set
of rational squares, which is not semialgebraic over `ℤ`).

Proof: the QF formula `fiberFormula_high P` (in `FiberFormula.lean`)
realises to the fibre-non-empty set
(`fiberFormula_high_realization`), so
`qfRealizable_isSemialgebraicSetOver` concludes. That formula is a
disjunction over the leaves of `TRems(P̃, ∂P̃/∂X)` (over root
truncations `P̃ ∈ Tru(splitLast P)`, the signed-remainder-sequence
tree from Chapter 1 §1.3 re-interpreted in the ordered setting), each
leaf contributing a `signCondFormula` over the leading coefficients
along the path. Sturm's Theorem~2.50 + Remark~2.51: on each cell of
the resulting sign-condition partition, either every fibre is
non-empty or every fibre is empty; the disjunction of the "non-empty"
leaves, together with the identically-vanishing locus, is the
predicate. -/
theorem fiber_nonempty_isSemialgebraicSetOver_degx_ge_two
    [IsRealClosed R] [IsDomain D]
    (P : MvPolynomial (Fin (k+1)) D)
    (hinj : Function.Injective (algebraMap D R))
    (_hdeg : (splitLast P).natDegree ≥ 2) :
    IsSemialgebraicSetOver D
      ({y : Fin k → R | ∃ x : R, aeval (Fin.snoc y x) P = 0}) := by
  rw [← fiberFormula_high_realization P hinj]
  exact qfRealizable_isSemialgebraicSetOver (fiberFormula_high_isQF P)

/-- **BPR Theorem 2.62 key lemma.** The "fiber non-empty" predicate
`{y | ∃ x : R, P(y, x) = 0}` is semialgebraic over `D`. Dispatches on
`(splitLast P).natDegree` to the three base/inductive lemmas:
* `degx 0` (`degx_zero`) — `P` is constant in the last variable.
* `degx 1` (`degx_one`) — linear in the last variable.
* `degx ≥ 2` (`degx_ge_two`) — the Sturm-Tarski machinery.
-/
theorem fiber_nonempty_isSemialgebraicSetOver
    [IsRealClosed R] [IsDomain D]
    (hinj : Function.Injective (algebraMap D R))
    (P : MvPolynomial (Fin (k+1)) D) :
    IsSemialgebraicSetOver D
      ({y : Fin k → R | ∃ x : R, aeval (Fin.snoc y x) P = 0}) := by
  by_cases h0 : (splitLast P).natDegree = 0
  · exact fiber_nonempty_isSemialgebraicSetOver_degx_zero P h0
  by_cases h1 : (splitLast P).natDegree = 1
  · exact fiber_nonempty_isSemialgebraicSetOver_degx_one P h1
  exact fiber_nonempty_isSemialgebraicSetOver_degx_ge_two P hinj (by omega)

/-- **BPR Theorem 2.62.** The projection (drop the last coordinate)
of an algebraic subset of `R^(k+1)` defined over `D` is a
semialgebraic subset of `R^k` defined over `D`.

The proof: sum-of-squares reduces to a single polynomial `P`; the
image-of-projection rewrites to the "fiber non-empty" predicate; that
predicate is semialgebraic over `D` by the Sturm-Tarski analysis. -/
theorem theorem_2_62 [IsRealClosed R] [IsDomain D]
    (hinj : Function.Injective (algebraMap D R))
    {Z : Set (Fin (k+1) → R)}
    (hZ : IsAlgebraicSetOver D Z) :
    IsSemialgebraicSetOver D (Fin.init '' Z) := by
  obtain ⟨P, rfl⟩ := IsAlgebraicSetOver.exists_singleton hZ
  rw [Fin.init_image_eq_exists_aeval]
  exact fiber_nonempty_isSemialgebraicSetOver hinj P

end Azurite.BPR
