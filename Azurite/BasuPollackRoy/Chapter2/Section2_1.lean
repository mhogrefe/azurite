import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_1
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_2
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_3
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Cones
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_14
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_15
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Example_2_10
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_4
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_6
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_7
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_8
import Azurite.BasuPollackRoy.Chapter2.Section2_1.GrlexProperties
import Azurite.BasuPollackRoy.Chapter2.Section2_1.HasNoNontrivialRealAlgebraicExtension
import Azurite.BasuPollackRoy.Chapter2.Section2_1.IsRealClosedOrder
import Azurite.BasuPollackRoy.Chapter2.Section2_1.InfinitesimalUnbounded
import Azurite.BasuPollackRoy.Chapter2.Section2_1.IntermediateValueProperty
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_12
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_2
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_9
import Azurite.BasuPollackRoy.Chapter2.Section2_1.LexProperties
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_1
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_4
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_6
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_8
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_13
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_16
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealClosedField
import Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SumOfSquares
import Azurite.BasuPollackRoy.Chapter2.Section2_1.SymmetricPolynomials
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_7
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Order.Ring.Ordering.Basic
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Sign.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Zorn
import Mathlib.Tactic.TFAE
import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 2: Real Closed Fields
## Section 2.1: Ordered, Real and Real Closed Fields

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

Let K be a field of characteristic 0 and P ∈ K[X].

The formal derivative and its iterates come directly from Mathlib's
`Polynomial.derivative` and `Polynomial.derivative^[i]`; the
exposition is in the blueprint
(`blueprint/src/chapter2/section2_1/derivative.tex`).
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-! Note: BPR Proposition 2.1 (Taylor's formula) and the
auxiliary `hasseDeriv_eval_eq` are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_1`. -/

/-! Note: `IsRootMultiplicity` (the multiplicity-of-a-root predicate)
and BPR Lemma 2.2 (`lemma_2_2`, the derivative characterization) are
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_2`. -/

/-! BPR's separable and square-free definitions defer to Mathlib's
`Polynomial.Separable` and `Squarefree`; exposition is in the
blueprint (`blueprint/src/chapter2/section2_1/separable_squarefree.tex`). -/



/-! Note: BPR Exercise 2.1 (parts (a) and (b): `exercise_2_1a`,
`exercise_2_1b`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_1`. -/

/-! BPR's unnumbered definitions of partially / totally ordered set,
ordered ring, and ordered field defer to Mathlib's `PartialOrder`,
`LinearOrder`, `IsStrictOrderedRing`, and `OrderRingHom`; exposition
is in the blueprint
(`blueprint/src/chapter2/section2_1/ordered_structures.tex`). -/

/-! Note: BPR Exercise 2.2 (`exercise_2_2_neg_one_lt_zero`,
`exercise_2_2_trichotomy`, plus an `example` for char-zero) is
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_2`. -/

/-! BPR Notation 2.3 (Sign) and the unnumbered absolute-value
definition defer to Mathlib's `SignType.sign` and `abs` / `|·|`;
exposition is in the blueprint
(`blueprint/src/chapter2/section2_1/sign_abs.tex`). -/

/-!
### Notation: Intervals

**Notation (BPR p.34).** Closed, open and semi-open intervals in an ordered
field `R` are denoted in the usual way:
- `(a, b) = {x ∈ R | a < x < b}`
- `[a, b] = {x ∈ R | a ≤ x ≤ b}`
- `(a, b] = {x ∈ R | a < x ≤ b}`
- `[a, b) = {x ∈ R | a ≤ x < b}`
- `(a, +∞) = {x ∈ R | a < x}`, `[a, +∞) = {x ∈ R | a ≤ x}`
- `(−∞, a) = {x ∈ R | x < a}`, `(−∞, a] = {x ∈ R | x ≤ a}`

In Mathlib (namespace `Set`, defined in `Mathlib.Order.Interval.Set.Defs`,
requiring only `[Preorder α]`):

| BPR | Mathlib | Membership |
|---|---|---|
| `(a, b)` | `Set.Ioo a b` | `a < x ∧ x < b` |
| `[a, b]` | `Set.Icc a b` | `a ≤ x ∧ x ≤ b` |
| `[a, b)` | `Set.Ico a b` | `a ≤ x ∧ x < b` |
| `(a, b]` | `Set.Ioc a b` | `a < x ∧ x ≤ b` |
| `(a, +∞)` | `Set.Ioi a` | `a < x` |
| `[a, +∞)` | `Set.Ici a` | `a ≤ x` |
| `(−∞, a)` | `Set.Iio a` | `x < a` |
| `(−∞, a]` | `Set.Iic a` | `x ≤ a` |

Naming mnemonic: `I{left}{right}` where `c` = closed, `o` = open,
`i` = infinite. Membership lemmas follow the pattern `Set.mem_Ioo` etc.
-/

example : ∀ a b : ℝ, Set.Ioo a b = {x | a < x ∧ x < b} := fun _ _ => rfl
example : ∀ a b : ℝ, Set.Icc a b = {x | a ≤ x ∧ x ≤ b} := fun _ _ => rfl
example : ∀ a b : ℝ, Set.Ioc a b = {x | a < x ∧ x ≤ b} := fun _ _ => rfl
example : ∀ a b : ℝ, Set.Ico a b = {x | a ≤ x ∧ x < b} := fun _ _ => rfl
example : ∀ a : ℝ, Set.Ioi a = {x | a < x} := fun _ => rfl
example : ∀ a : ℝ, Set.Ici a = {x | a ≤ x} := fun _ => rfl
example : ∀ a : ℝ, Set.Iio a = {x | x < a} := fun _ => rfl
example : ∀ a : ℝ, Set.Iic a = {x | x ≤ a} := fun _ => rfl

/-! Note: BPR Exercise 2.3 (`exercise_2_3`, ℂ cannot be ordered) is
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_3`. -/

/-! Note: BPR Proposition 2.4 (`prop_2_4`, sign of a polynomial for
large `|x|`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_4`. -/

/-! Note: BPR's unnumbered definitions of infinitesimal /
unbounded elements over an ordered field (`IsInfinitesimalOver`,
`IsUnboundedOver`) are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.InfinitesimalUnbounded`. -/

/-! Note: BPR Notation 2.5 (the 0₊ order on F[ε] and F(ε), with
infinitesimal `ε` and unbounded `1/ε`) is constructed in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.OrderZeroPlus`. Exposition is in
the blueprint (`blueprint/src/chapter2/section2_1/notation_2_5.tex`). -/

/-! Note: BPR Exercise 2.4 (`exercise_2_4`, uniqueness of the 0₊ order)
is defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_4`. -/

/-! Note: BPR's unnumbered definitions of cone (`IsCone`),
proper cone (`IsProperCone`), and the positive-cone lemmas
(`isCone_nonneg`, `isProperCone_nonneg`) — together with the
`RingPreordering`/`IsProperCone` bridges — are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Cones`. -/

section Cones

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! Note: BPR Proposition 2.6 (`prop_2_6_forward`,
`IsProperCone.toRingCone`, `IsProperCone.totalOrder`, plus the
`nonneg_hasMemOrNegMem` and `IsProperCone.eq_zero_of_mem_of_neg_mem'`
helpers) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_6`. -/

/-! Note: BPR's unnumbered notation for the set of squares
(`F^{(2)}` ↦ Mathlib's `IsSquare`) and the sum-of-squares
sub-semiring `ΣF^{(2)}` (`sumOfSquares` plus the
cone-containment lemmas `isCone_sumOfSquares` and
`sumOfSquares_le_cone`) are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.SumOfSquares`. -/

/-! Note: BPR's unnumbered definition of a real field
(`IsRealField`, equivalent to Mathlib's `IsSemireal`, plus the
`isRealField_iff*` reformulations and `isRealField_charZero`)
is defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.RealField`. -/

/-! Note: BPR Exercise 2.6 (`exercise_2_6_charZero`,
`exercise_2_6_complex_not_real`, `exercise_2_6_ordered_is_real`) is
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_6`. -/

/-! Note: BPR Lemma 2.9 (`coneExt`, `coneExt_isCone`,
`lemma_2_9`) and BPR Proposition 2.8 (`chain_ub_isProperCone`,
`le_coneExt`, `prop_2_8`) are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.{Lemma_2_9,Proposition_2_8}`. -/

end Cones

end Azurite.BPR

namespace Azurite.BPR

/-! Note: BPR Theorem 2.7 (`isSumSq_exists_vector`,
`theorem_2_7_a_of_b`, `theorem_2_7_b_of_c`, `theorem_2_7_c_of_d`,
`theorem_2_7_d_of_a`, and the bundled `theorem_2_7` TFAE) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Theorem_2_7`. -/

open Polynomial

/-! Note: BPR's unnumbered definition of a real closed field
(`IsRealClosedField`, the ordered-form characterisation
`isRealClosedField_iff`, the squares-as-nonneg lemma
`IsRealClosedField.nonneg_iff_isSquare`, and the implication
`IsRealClosedField.isRealField`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.RealClosedField`. -/

/-! Note: the order-side bridge for `IsRealClosed` (the noncomputable
`IsRealClosed.toLinearOrder` and `IsRealClosed.toIsOrderedRing` instances
extending the sum-of-squares cone via Prop. 2.8, plus uniqueness of the
ordering `isRealClosed_le_unique`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.IsRealClosedOrder`. -/

namespace Azurite.BPR

/-! Note: BPR Example 2.10 (`realAlgebraicNumbers` / `ℝ_alg` and the
trivial closure lemmas `zero_mem_realAlgebraicNumbers`,
`one_mem_realAlgebraicNumbers`, `intCast_mem_realAlgebraicNumbers`) is
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Example_2_10`.
The proof that `ℝ_alg` is real closed is Exercise 2.11
(`Azurite.BasuPollackRoy.Chapter2.Exercise_2_11`). -/

/-! Note: BPR's unnumbered definition of the intermediate value property
(`HasIntermediateValueProperty`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.IntermediateValueProperty`. -/

/-! Note: BPR's `HasNoNontrivialRealAlgebraicExtension` (condition (d) of
Theorem 2.11) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.HasNoNontrivialRealAlgebraicExtension`. -/

/-! Note: BPR's unnumbered definitions of symmetric polynomial
(`IsSymmetricPolynomial`, deferring to `MvPolynomial.IsSymmetric`) and
the elementary symmetric function (`elementarySymmetric`, deferring to
`MvPolynomial.esymm`) are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.SymmetricPolynomials`. -/

/-! Note: BPR Lemma 2.12 (`lemma_2_12`, the elementary-symmetric
expansion of `∏ (X − xⱼ)`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_12`. -/

/-! Note: BPR Exercise 2.7 (`monomialOrbitSum`, `exercise_2_7`) is
defined in `Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_7`. -/

/-! Note: BPR Definition 2.14 (`LexOrder`, the lexicographic ordering
on `Fin k → B`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_14`. -/

/-! Note: the supplementary lex properties (`lex_bot`, `lex_add_right`,
`lex_le_set_infinite`) are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.LexProperties`. -/

/-! Note: BPR Exercise 2.8 (`exercise_2_8`, well-foundedness of the lex
ordering on multi-indices) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_8`. -/

/-! Note: BPR Definition 2.15 (`GrlexOrder`, the graded lexicographic
ordering) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Definition_2_15`. -/

/-! Note: the supplementary grlex properties (`grlex_bot`, `grlex_add_right`,
`grlex_le_set_finite`) are defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.GrlexProperties`. -/

/-! Note: BPR Proposition 2.13 (`proposition_2_13`, the fundamental theorem
of symmetric polynomials) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_13`. -/

/-! Note: BPR Proposition 2.16 (`proposition_2_16`, symmetric polynomials in
the roots of a monic polynomial stay in `K`) is defined in
`Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_16`. -/

section Notation_2_18

/-!
### Notation 2.18: R[i], Conjugate, and Modulus

**Notation 2.18 (BPR).** If R is real closed, R[i] = R[T]/(T² + 1) can be identified
with R². For z = a + ib ∈ R[i], a, b ∈ R:
- The *conjugate* of z is z̄ = a − ib.
- The *modulus* of z is |z| = √(a² + b²).

**Mathlib.** There is no `StarRing` or `normSq` instance on `AdjoinRoot` in Mathlib.
The `RCLike` typeclass (which provides `conj`, `normSq`, and `‖·‖`) is designed for ℝ
and ℂ only, not for R[i] over an arbitrary real closed field. We therefore define the
conjugate, norm squared, and modulus directly on `Ri R := AdjoinRoot (X² + 1)`.
-/

open Polynomial

/-- R[i] := R[X]/(X² + 1), the "complex numbers" over R. -/
noncomputable abbrev Ri (R : Type*) [CommRing R] :=
  AdjoinRoot (X ^ 2 + 1 : R[X])

/-- The imaginary unit `i` in R[i], i.e., the image of X in R[X]/(X² + 1). -/
noncomputable def Ri.i (R : Type*) [CommRing R] : Ri R :=
  AdjoinRoot.root (X ^ 2 + 1 : R[X])

/-- **Conjugation** on R[i]: the R-algebra endomorphism sending i ↦ −i (BPR: z̄ = a − ib). -/
noncomputable def Ri.conj (R : Type*) [CommRing R] : Ri R →ₐ[R] Ri R :=
  { AdjoinRoot.lift (AdjoinRoot.of (X ^ 2 + 1 : R[X])) (-Ri.i R)
      (by
        simp only [Ri.i, eval₂_add, eval₂_pow, eval₂_one, eval₂_X, neg_sq]
        have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : R[X])
        simpa [eval₂_add, eval₂_pow, eval₂_one, eval₂_X] using h) with
    commutes' := fun r => by simp [AdjoinRoot.lift_of] }

/-- Conjugation sends i to −i. -/
theorem Ri.conj_i (R : Type*) [CommRing R] : (Ri.conj R) (Ri.i R) = -Ri.i R := by
  simp [Ri.conj, Ri.i, AdjoinRoot.lift_root]

/-- Conjugation is an involution: conj(conj(z)) = z. -/
theorem Ri.conj_conj (R : Type*) [CommRing R] (z : Ri R) :
    (Ri.conj R) ((Ri.conj R) z) = z := by
  have : (Ri.conj R).comp (Ri.conj R) = AlgHom.id R (Ri R) := by
    apply AdjoinRoot.algHom_ext
    simp only [Ri.conj, AlgHom.comp_apply, AlgHom.coe_mk, Ri.i,
      AdjoinRoot.lift_root, map_neg, neg_neg, AlgHom.id_apply]
  exact AlgHom.congr_fun this z

/-- Conjugation is injective. -/
theorem Ri.conj_injective (R : Type*) [CommRing R] :
    Function.Injective (Ri.conj R : Ri R →+* Ri R) :=
  Function.HasLeftInverse.injective ⟨Ri.conj R, Ri.conj_conj R⟩

/-- The defining relation: i² = −1 in R[i]. -/
theorem Ri.i_sq (R : Type*) [CommRing R] :
    (Ri.i R) ^ 2 = -(1 : Ri R) := by
  have h : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1 : R[X]) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  unfold Ri.i
  linear_combination h

/-- In a real closed field, −1 is not a square. -/
theorem not_isSquare_neg_one {R : Type*} [Field R] [IsRealClosed R] :
    ¬ IsSquare (-1 : R) := by
  intro h; exact IsSemireal.not_isSumSq_neg_one R h.isSumSq

/-- X² + 1 is irreducible over a real closed field R. -/
theorem irred_X_sq_add_one {R : Type*} [Field R] [IsRealClosed R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
    simp [this, Finset.mem_Icc]
  · intro x
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
    intro h
    have : (-1 : R) = x * x := by linear_combination -h
    exact not_isSquare_neg_one ⟨x, this⟩

/-- X² + 1 is irreducible (as a Fact, for `AdjoinRoot.instField`). -/
instance instFactIrred_X_sq_add_one (R : Type*) [Field R] [IsRealClosed R] :
    Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irred_X_sq_add_one⟩

/-- Every element of R[i] decomposes as ι(a) + ι(b) · i with a, b ∈ R. -/
theorem Ri.repr_exists {R : Type*} [CommRing R] [Nontrivial R] (z : Ri R) :
    ∃ a b : R, z = algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    set f := (X : R[X]) ^ 2 + 1
    have hfm : f.Monic := monic_X_pow_add_C 1 (by norm_num : (2 : ℕ) ≠ 0)
    set r := p %ₘ f
    have hmk : AdjoinRoot.mk f p = AdjoinRoot.mk f r := by
      rw [AdjoinRoot.mk_eq_mk]
      exact ⟨p /ₘ f, by have := modByMonic_eq_sub_mul_div p f; linear_combination -this⟩
    have hr_deg : r.natDegree ≤ 1 := by
      have hrd : r.degree < f.degree := degree_modByMonic_lt p hfm
      have hf_deg : f.degree = 2 := by
        have hnat : f.natDegree = 2 := by
          simp [f]; rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
        rw [Polynomial.degree_eq_natDegree hfm.ne_zero, hnat]; norm_num
      rw [hf_deg] at hrd
      by_cases hr : r = 0
      · simp [hr]
      · rw [Polynomial.degree_eq_natDegree hr] at hrd
        exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (by exact_mod_cast hrd))
    have hr_decomp := Polynomial.eq_X_add_C_of_natDegree_le_one hr_deg
    rw [hmk, show AdjoinRoot.mk f r = Polynomial.aeval (Ri.i R) r from
      (AdjoinRoot.aeval_eq r).symm, hr_decomp]
    simp [Polynomial.aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    exact ⟨r.coeff 0, r.coeff 1, by ring⟩

/-- The norm squared z · z̄ in R[i]. -/
noncomputable def Ri.normSq {R : Type*} [CommRing R] (z : Ri R) : Ri R :=
  z * Ri.conj R z

/-- normSq(a + bi) = ι(a² + b²). -/
theorem Ri.normSq_repr {R : Type*} [CommRing R] (a b : R) :
    Ri.normSq (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) =
    algebraMap R (Ri R) (a ^ 2 + b ^ 2) := by
  simp only [Ri.normSq]
  have hconj : (Ri.conj R) (algebraMap R (Ri R) a + algebraMap R (Ri R) b * Ri.i R) =
      algebraMap R (Ri R) a - algebraMap R (Ri R) b * Ri.i R := by
    simp only [map_add, map_mul, AlgHom.commutes, Ri.conj_i, mul_neg]
    ring
  rw [hconj, map_add, map_pow, map_pow]
  have hi_sq : (Ri.i R) ^ 2 = -(1 : Ri R) := Ri.i_sq R
  ring_nf
  rw [hi_sq]
  ring

/-- normSq z lies in the image of R. -/
theorem Ri.normSq_mem_range {R : Type*} [CommRing R] [Nontrivial R] (z : Ri R) :
    Ri.normSq z ∈ Set.range (algebraMap R (Ri R)) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists z
  rw [hab, Ri.normSq_repr]
  exact ⟨a ^ 2 + b ^ 2, rfl⟩

/-- The norm squared z · z̄, projected to R via algebraMap injectivity. -/
noncomputable def Ri.normSqR {R : Type*} [Field R] [IsRealClosed R] (z : Ri R) : R :=
  Classical.choose (Ri.normSq_mem_range z)

/-- algebraMap (normSqR z) = normSq z. -/
theorem Ri.normSqR_spec {R : Type*} [Field R] [IsRealClosed R] (z : Ri R) :
    algebraMap R (Ri R) (Ri.normSqR z) = Ri.normSq z :=
  Classical.choose_spec (Ri.normSq_mem_range z)

/-- normSqR z ≥ 0. -/
theorem Ri.normSqR_nonneg {R : Type*} [Field R] [IsRealClosed R] (z : Ri R) :
    @LE.le R IsRealClosed.toLinearOrder.toLE 0 (Ri.normSqR z) := by
  obtain ⟨a, b, hab⟩ := Ri.repr_exists z
  have hinj : Function.Injective (algebraMap R (Ri R)) := (algebraMap R (Ri R)).injective
  have heq : Ri.normSqR z = a ^ 2 + b ^ 2 := hinj (by
    rw [Ri.normSqR_spec, hab, Ri.normSq_repr])
  rw [heq]
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  exact add_nonneg (sq_nonneg a) (sq_nonneg b)

/-- **Modulus** |z| = √(a² + b²), the unique nonneg r ∈ R with r² = normSqR z. -/
noncomputable def Ri.modulus {R : Type*} [Field R] [IsRealClosed R]
    (z : Ri R) : R :=
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  |(IsRealClosed.exists_eq_pow_of_nonneg (Ri.normSqR_nonneg z) two_ne_zero).choose|

/-- The modulus is nonneg. -/
theorem Ri.modulus_nonneg {R : Type*} [Field R] [IsRealClosed R]
    (z : Ri R) : @LE.le R IsRealClosed.toLinearOrder.toLE 0 (Ri.modulus z) := by
  unfold Ri.modulus
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  exact abs_nonneg _

/-- The modulus squared equals the norm squared. -/
theorem Ri.modulus_sq {R : Type*} [Field R] [IsRealClosed R]
    (z : Ri R) : Ri.modulus z ^ 2 = Ri.normSqR z := by
  unfold Ri.modulus
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  rw [sq_abs]
  exact (IsRealClosed.exists_eq_pow_of_nonneg (Ri.normSqR_nonneg z) two_ne_zero).choose_spec.symm

end Notation_2_18

section Exercise_2_9

/-- **BPR Exercise 2.9.** In a real closed field `R`, a second-degree polynomial
    `P = aX² + bX + c` with `a ≠ 0` has constant non-zero sign (i.e. is everywhere
    positive or everywhere negative) if and only if its discriminant `b² − 4ac`
    is negative.

    **Proof.** Completing the square gives
    `4a · P(x) = (2ax + b)² − (b² − 4ac)`,
    the classical identity valid over any ring.

    **(⇐)** If `b² − 4ac < 0` then `4a · P(x) > 0` for all `x` since
    `(2ax + b)² ≥ 0`. Dividing by `4a` preserves the sign if `a > 0` and flips it
    if `a < 0`, so `P` has constant non-zero sign.

    **(⇒)** By contraposition: if `b² − 4ac ≥ 0` then in a real closed field we
    may write `b² − 4ac = s²` for some `s ∈ R` (by `IsRealClosed.exists_eq_pow_of_nonneg`),
    and `x₀ = (−b + s) / (2a)` is a root of `P` (a direct calculation using the
    completing-the-square identity). A root witnesses that `P` does not have
    constant non-zero sign. -/
theorem exercise_2_9 {R : Type*} [Field R] [IsRealClosed R]
    {a b c : R} (ha : a ≠ 0) :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    ((∀ x : R, 0 < a * x ^ 2 + b * x + c) ∨
     (∀ x : R, a * x ^ 2 + b * x + c < 0)) ↔
      b ^ 2 - 4 * a * c < 0 := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  -- Key completing-the-square identity.
  have key : ∀ x : R, 4 * a * (a * x ^ 2 + b * x + c) =
      (2 * a * x + b) ^ 2 - (b ^ 2 - 4 * a * c) := fun x => by ring
  constructor
  · -- Forward: constant non-zero sign ⇒ discriminant < 0 (by contraposition).
    intro hsign
    by_contra hdisc
    push Not at hdisc
    -- Extract a square root of the discriminant in the real closed field.
    obtain ⟨s, hs⟩ := IsRealClosed.exists_eq_pow_of_nonneg hdisc two_ne_zero
    -- Candidate root: x₀ = (-b + s) / (2a).
    have h2a : (2 * a : R) ≠ 0 := mul_ne_zero two_ne_zero ha
    have h4a : (4 * a : R) ≠ 0 := mul_ne_zero (by norm_num) ha
    set x₀ : R := (-b + s) / (2 * a) with hx₀_def
    -- Then 2a·x₀ + b = s, so 4a·P(x₀) = s² − (b² − 4ac) = 0.
    have h2ax₀b : 2 * a * x₀ + b = s := by
      rw [hx₀_def]; field_simp; ring
    have hPx₀ : a * x₀ ^ 2 + b * x₀ + c = 0 := by
      have h4aP : 4 * a * (a * x₀ ^ 2 + b * x₀ + c) = 0 := by
        rw [key, h2ax₀b, ← hs]; ring
      exact (mul_eq_zero.mp h4aP).resolve_left h4a
    -- A root contradicts constant non-zero sign at x₀.
    rcases hsign with hpos | hneg
    · exact absurd (hpos x₀) (by rw [hPx₀]; exact lt_irrefl 0)
    · exact absurd (hneg x₀) (by rw [hPx₀]; exact lt_irrefl 0)
  · -- Backward: discriminant < 0 ⇒ constant non-zero sign.
    intro hdisc
    -- In either sign of `a`, show 4a·P(x) has the same (strict) sign as `a`.
    have h4aP_pos_of_a_pos : 0 < a → ∀ x : R, 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
      intro hap x
      rw [key]
      have : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
      linarith
    have h4aP_pos_of_a_neg : a < 0 → ∀ x : R, 0 < 4 * a * (a * x ^ 2 + b * x + c) := by
      intro han x
      rw [key]
      have : 0 ≤ (2 * a * x + b) ^ 2 := sq_nonneg _
      linarith
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · -- a < 0 ⇒ 4a < 0, so P(x) < 0.
      right
      intro x
      have h4a_neg : 4 * a < 0 := by
        have : (0 : R) < 4 := by norm_num
        exact mul_neg_of_pos_of_neg this ha_neg
      have hP_pos := h4aP_pos_of_a_neg ha_neg x
      -- 4a · P(x) > 0 with 4a < 0 forces P(x) < 0.
      by_contra hPge
      push Not at hPge
      have : 4 * a * (a * x ^ 2 + b * x + c) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt h4a_neg) hPge
      linarith
    · -- a > 0 ⇒ 4a > 0, so P(x) > 0.
      left
      intro x
      have h4a_pos : 0 < 4 * a := by
        have : (0 : R) < 4 := by norm_num
        exact mul_pos this ha_pos
      have hP_pos := h4aP_pos_of_a_pos ha_pos x
      exact (mul_pos_iff_of_pos_left h4a_pos).mp hP_pos

end Exercise_2_9

/-!
### Theorem 2.11: Characterizations of Real Closed Fields

**Theorem 2.11 (BPR).** If R is an ordered field, the following are equivalent:
- (a) R is real closed.
- (b) R[i] = R[X]/(X² + 1) is algebraically closed.
- (c) R has the intermediate value property.
- (d) R is a real field with no non-trivial real algebraic extension.

The proof is split across five files in `Section2_1/`, one per implication:
- `Theorem_2_11_a_b.lean`: (a) ⇒ (b)
- `Theorem_2_11_b_c.lean`: (b) ⇒ (c)
- `Theorem_2_11_b_d.lean`: (b) ⇒ (d)
- `Theorem_2_11_c_a.lean`: (c) ⇒ (a)
- `Theorem_2_11_d_a.lean`: (d) ⇒ (a)

The combined TFAE statement is in `Section2_1/Theorem_2_11.lean`.
-/

/-!
### Proposition 2.19: Form of Irreducible Factors over a Real Closed Field

**Proposition 2.19 (BPR).** Let R be a real closed field, P ∈ R[X].
The irreducible factors of P are linear or have the form
(X − c)² + d² = (X − c − id)(X − c + id), d ≠ 0, with c, d ∈ R.

The proof uses Theorem 2.11 (a ⇒ b) — that R[i] is algebraically closed —
together with the fact that the conjugate of a root of P is a root of P.
See `Proposition_2_19.lean` (imports `Theorem_2_11_b_c.lean`).
-/

/-!
### Proposition 2.20: Constant Sign on a Non-Vanishing Interval

**Proposition 2.20 (BPR).** Let R be a real closed field, P ∈ R[X] such that
P does not vanish in `(a, b)`. Then P has constant sign in the interval `(a, b)`.

The proof uses Theorem 2.11 (b ⇒ c) — that R has the intermediate value
property — applied to a hypothetical pair of points where P takes values
of opposite sign.
See `Proposition_2_20.lean` (imports `Theorem_2_11_b_c.lean`).
-/

/-!
### Sign of a Polynomial to the Right / Left of a Point and at ±∞

Proposition 2.20 justifies speaking of the sign of `P ∈ R[X]`:
- **to the right of `a`** — the sign of `P` in any `(a, b)` on which `P`
  does not vanish;
- **to the left of `a`** — likewise on `(b, a)`;
- **at `+∞`** — the sign of `P(M)` for `M` sufficiently large (greater than
  any root of `P`);
- **at `−∞`** — the sign of `P(M)` for `M` sufficiently small.

The corresponding predicates `HasSignRight`, `HasSignLeft`,
`HasSignAtPosInfty`, `HasSignAtNegInfty` — along with their uniqueness
theorems and the `Classical.choose`-based functional forms `signRight`,
`signLeft`, `signAtPosInfty`, `signAtNegInfty` — live in `SignAtPoint.lean`
(imports `Proposition_2_20.lean`).

Also in `SignAtPoint.lean`: the sign-at-infinity identities via Proposition 2.4:
`signAtPosInfty P = sign(P.leadingCoeff)` and
`signAtNegInfty P = (−1)^{deg P} · sign(P.leadingCoeff)`.
-/

/-!
### Proposition 2.21: Sign of a Polynomial Near a Root

**Proposition 2.21 (BPR).** If `r` is a root of `P ∈ R[X]` of multiplicity `µ`
in a real closed field `R`, then
- the sign of `P` to the right of `r` is the sign of `P^{(µ)}(r)`,
- the sign of `P` to the left  of `r` is the sign of `(−1)^µ · P^{(µ)}(r)`.

*Proof sketch.* Write `P = (X − r)^µ · Q` with `Q(r) ≠ 0`. Taylor's formula
gives `P^{(µ)}(r) = µ! · Q(r)`, hence `sign(Q(r)) = sign(P^{(µ)}(r))`. On a
sufficiently small interval around `r` avoiding all other roots of `Q`,
Proposition 2.20 yields that `Q` has constant sign there (equal to
`sign(Q(r))`); for `x` to the right of `r`, `(x − r)^µ > 0` so
`sign(P(x)) = sign(Q(r))`; to the left, `sign((x − r)^µ) = (−1)^µ`.
See `Proposition_2_21.lean` (imports `SignAtPoint.lean`).
-/

/-!
### Archimedean ordered fields (BPR p.46)

**Definition (BPR p.46).** An ordered field `F` is *archimedean* if, whenever `a, b`
are positive elements of `F`, there exists a natural number `n ∈ ℕ` so that `n · a > b`.

**Mathlib correspondence.** This is `Archimedean` from
`Mathlib.Algebra.Order.Archimedean.Defs`, defined as
`∀ (x : R) {y : R}, 0 < y → ∃ n : ℕ, x ≤ n • y`.

`ℝ` is archimedean via `Real.instArchimedean`.
-/

/-- Any intermediate field of an archimedean ordered field is archimedean,
    via `Archimedean.comap` along the subtype inclusion. -/
theorem IntermediateField.archimedean {F E : Type*} [Field F] [Field E]
    [Algebra F E] [LinearOrder E] [IsStrictOrderedRing E] [Archimedean E]
    (S : IntermediateField F E) : Archimedean ↥S :=
  Archimedean.comap S.subtype.toAddMonoidHom (fun _ _ h => h)

end Azurite.BPR
