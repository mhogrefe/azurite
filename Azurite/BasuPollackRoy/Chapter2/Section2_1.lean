import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_1
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_2
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_3
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Cones
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_4
import Azurite.BasuPollackRoy.Chapter2.Section2_1.InfinitesimalUnbounded
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Lemma_2_2
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_1
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_4
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

/-!
### Proposition 2.6

**Proposition 2.6 (BPR).** Let (F, ≤) be an ordered field. The positive cone
C = { x ∈ F | x ≥ 0} is a proper cone satisfying C ∪ (−C) = F. Conversely,
if C is a proper cone of a field F with C ∪ (−C) = F, then F is ordered by
x ≤ y ⇔ y − x ∈ C.

**Mathlib link.** The condition `C ∪ (−C) = F` is exactly `HasMemOrNegMem C`
in Mathlib. A proper cone with this totality is a `RingCone`, since if both
`a ∈ C` and `−a ∈ C` with `a ≠ 0`, then `a⁻¹ = (a⁻¹)² · a ∈ C`, so
`−1 = (−a) · a⁻¹ ∈ C`, contradicting properness.
-/

/-- **Prop 2.6 (Forward, part 1).** The positive cone satisfies `C ∪ (−C) = F`. -/
lemma nonneg_hasMemOrNegMem : HasMemOrNegMem (Subsemiring.nonneg F) :=
  ⟨fun a => by
    simp only [Subsemiring.mem_nonneg]
    rcases le_total 0 a with h | h
    · left; exact h
    · right; linarith⟩

/-- **Prop 2.6 (Forward, full).** The positive cone of an ordered field is
    a proper cone with `C ∪ (−C) = F`. -/
theorem prop_2_6_forward :
    IsProperCone (Subsemiring.nonneg F) ∧ HasMemOrNegMem (Subsemiring.nonneg F) :=
  ⟨isProperCone_nonneg, nonneg_hasMemOrNegMem⟩

section Prop_2_6_Converse

variable {F : Type*} [Field F]

/-- In a field, a proper cone satisfies the `RingCone` antisymmetry:
    if `a ∈ C` and `−a ∈ C`, then `a = 0`. The key step uses `a⁻¹ = (a⁻¹)² · a ∈ C`,
    so `−1 = (−a) · a⁻¹ ∈ C`, contradicting properness. -/
lemma IsProperCone.eq_zero_of_mem_of_neg_mem' {C : Subsemiring F}
    (hC : IsProperCone C) {a : F} (ha : a ∈ C) (hna : -a ∈ C) : a = 0 := by
  by_contra h
  have hinv : a⁻¹ ∈ C := by
    have hsq : a⁻¹ ^ 2 ∈ C := hC.1 a⁻¹
    have := C.mul_mem hsq ha
    rwa [sq, mul_assoc, inv_mul_cancel₀ h, mul_one] at this
  have : (-1 : F) ∈ C := by
    have := C.mul_mem hna hinv
    rwa [neg_mul, mul_inv_cancel₀ h] at this
  exact hC.2 this

/-- **Prop 2.6 (Converse).** A proper cone with `C ∪ (−C) = F` gives a `RingCone`. -/
def IsProperCone.toRingCone {C : Subsemiring F} (hC : IsProperCone C) : RingCone F where
  toSubsemiring := C
  eq_zero_of_mem_of_neg_mem' := fun ha hna => hC.eq_zero_of_mem_of_neg_mem' ha hna

/-- The order induced by a proper cone: `x ≤ y ↔ y − x ∈ C`. -/
def IsProperCone.le {C : Subsemiring F} (_ : IsProperCone C) (x y : F) : Prop :=
  y - x ∈ C

/-- **Prop 2.6 (Converse, stated).** If `C` is a proper cone of a field `F`
    with `C ∪ (−C) = F`, then `x ≤ y ⇔ y − x ∈ C` defines a linear order
    making `F` an ordered field. The cone `C` becomes the positive cone
    `{x | 0 ≤ x}` of this order.

    We have already shown that such `C` produces a `RingCone`
    (via `IsProperCone.toRingCone`), and the totality condition
    `HasMemOrNegMem` ensures the order is linear. -/
theorem IsProperCone.totalOrder {C : Subsemiring F}
    (hC : IsProperCone C) (hT : ∀ a : F, a ∈ C ∨ -a ∈ C) :
    ∀ x y : F, hC.le x y ∨ hC.le y x := by
  intro x y
  rcases hT (y - x) with h | h
  · left; exact h
  · right; rwa [show -(y - x) = x - y from by ring] at h

end Prop_2_6_Converse

/-!
### Squares and Sums of Squares (BPR p.37)

**Notation (BPR p.37).** For a field `K`:
- `K^{(2)}` denotes the set of *squares* of elements of `K`,
  i.e., `{x² | x ∈ K}`.  In Mathlib this is `{x | IsSquare x}`.
- `ΣK^{(2)}` denotes the `Subsemiring` of *sums of squares* of elements
  of `K`.  In Mathlib this is `Subsemiring.sumSq K`, built from the
  inductive predicate `IsSumSq`.

The set `ΣK^{(2)}` is a cone: it is closed under addition and multiplication,
contains 0 = 0² and 1 = 1², and every element of `K^{(2)}` belongs to it.
Moreover it is the *smallest* cone: it is contained in every cone of `K`.

**Definition (BPR p.37).** A field `K` is a *real field* if `−1 ∉ ΣK^{(2)}`.
In Mathlib's terminology this is `IsSemireal K`.
-/

section SquaresAndSumOfSquares

variable (F : Type*) [CommRing F]

/-!
**BPR Notation.** `F^{(2)}` — the set of squares.  In Mathlib, a square
is expressed by the predicate `IsSquare x` (meaning `∃ y, x = y * y`).
Using `x ^ 2 = x * x` we can also write `{x | ∃ y, x = y ^ 2}`.
-/

/-- **BPR Notation.** `ΣF^{(2)}`: the `Subsemiring` of sums of squares in `F`.
    An element `s : F` belongs to `Subsemiring.sumSq F` iff `IsSumSq s`,
    i.e., `s` can be written as a finite sum `a₁·a₁ + a₂·a₂ + ⋯ + aₙ·aₙ`. -/
abbrev sumOfSquares : Subsemiring F := Subsemiring.sumSq F

/-- `ΣF^{(2)}` is a cone: every square `x²` is a sum of squares. -/
lemma isCone_sumOfSquares : IsCone (sumOfSquares F) :=
  fun x => Subsemiring.mem_sumSq.mpr (by rw [sq]; exact IsSumSq.mul_self x)

/-- `ΣF^{(2)}` is contained in every cone of `F` —
    it is the smallest cone. -/
lemma sumOfSquares_le_cone (C : Subsemiring F) (hC : IsCone C) :
    sumOfSquares F ≤ C := by
  intro x hx
  rw [Subsemiring.mem_sumSq] at hx
  induction hx with
  | zero => exact C.zero_mem
  | sq_add a _ ih => exact C.add_mem (by rw [← sq]; exact hC a) ih

end SquaresAndSumOfSquares

section RealField

variable (F : Type*) [Field F]

/-- **BPR Definition (p.37).** A field `F` is a *real field* if `−1 ∉ ΣF^{(2)}`,
    i.e., `−1` cannot be expressed as a sum of squares in `F`.

    In Mathlib this is `IsSemireal F` (from `Mathlib.Algebra.Ring.Semireal.Defs`),
    which is defined by the equivalent condition `∀ s, IsSumSq s → 1 + s ≠ 0`.
    Every ordered field is semireal. -/
abbrev IsRealField : Prop := IsSemireal F

/-- A field is real iff `−1 ∉ ΣF^{(2)}`. -/
lemma isRealField_iff : IsRealField F ↔ ¬ IsSumSq (-1 : F) :=
  isSemireal_iff_not_isSumSq_neg_one

/-- A field is real iff `−1 ∉ ΣF^{(2)}` (stated using `sumOfSquares`). -/
lemma isRealField_iff_neg_one_notMem :
    IsRealField F ↔ (-1 : F) ∉ sumOfSquares F := by
  rw [isRealField_iff, Subsemiring.mem_sumSq]

/-- A real field has characteristic zero
    (Mathlib synthesizes `CharZero F` from `IsSemireal F`). -/
theorem isRealField_charZero (h : IsRealField F) : CharZero F :=
  haveI : IsSemireal F := h; inferInstance

end RealField

/-!
### Exercise 2.6

**Exercise 2.6 (BPR p.37).**
1. A real field has characteristic 0.
2. The field ℂ of complex numbers is not a real field.
3. Every ordered field is a real field.

*Proofs.*
1. In a semireal ring, if `char R = p > 0` then `p = 0` in `R` and `p` is a sum
   of squares of `1`s, giving `0 = p ∈ ΣR^{(2)}` with `1 + p = 1 ≠ 0` — a
   contradiction. Mathlib derives `CharZero` from `IsSemireal` automatically.
2. In ℂ we have `i² = −1`, so `−1 = i·i + 0` is a sum of squares, hence
   `−1 ∈ Σℂ^{(2)}` and ℂ is not real.
3. In an ordered field, every sum of squares is non-negative, so `−1 < 0`
   cannot be a sum of squares. Mathlib provides a `IsSemireal` instance for
   any `[IsStrictOrderedRing]`.
-/

section Exercise_2_6

/-- **BPR Exercise 2.6(1).** A real field has characteristic 0.
    (This is a restatement of `isRealField_charZero`.) -/
theorem exercise_2_6_charZero {F : Type*} [Field F] (h : IsRealField F) : CharZero F :=
  haveI : IsSemireal F := h; inferInstance

/-- **BPR Exercise 2.6(2).** The field ℂ of complex numbers is not a real field.
    *Proof.* `i² = −1` in ℂ, so `−1 = i·i ∈ Σℂ^{(2)}`. -/
theorem exercise_2_6_complex_not_real : ¬ IsRealField ℂ := by
  rw [IsRealField, isSemireal_iff_not_isSumSq_neg_one]
  push Not
  have : (-1 : ℂ) = Complex.I * Complex.I := by simp
  rw [this]
  exact IsSumSq.mul_self _

/-- **BPR Exercise 2.6(3).** Every ordered field is a real field.
    *Proof.* Sums of squares are non-negative in an ordered ring, so `−1 < 0`
    cannot be a sum of squares. Mathlib provides the `IsSemireal` instance
    for `[IsStrictOrderedRing]`. -/
theorem exercise_2_6_ordered_is_real
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    IsRealField F :=
  haveI : IsSemireal F := inferInstance; this

end Exercise_2_6

/-!
### Lemma 2.9

**Lemma 2.9 (BPR).** Let `C` be a proper cone of `F`. If `−a ∉ C`, then
`C[a] = { x + a·y | x, y ∈ C}` is a proper cone of `F`.
-/

section Lemma_2_9

variable {F : Type*} [Field F]

/-- The extension `C[a]`: the set `{ x + a·y | x, y ∈ C}`. -/
def coneExt (C : Subsemiring F) (hCone : IsCone C) (a : F) : Subsemiring F where
  carrier := { z | ∃ x ∈ C, ∃ y ∈ C, z = x + a * y}
  zero_mem' := ⟨0, C.zero_mem, 0, C.zero_mem, by ring⟩
  one_mem' := ⟨1, C.one_mem, 0, C.zero_mem, by ring⟩
  add_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    exact ⟨x₁ + x₂, C.add_mem hx₁ hx₂, y₁ + y₂, C.add_mem hy₁ hy₂, by ring⟩
  mul_mem' := by
    rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
    exact ⟨x₁ * x₂ + a ^ 2 * (y₁ * y₂),
           C.add_mem (C.mul_mem hx₁ hx₂) (C.mul_mem (hCone a) (C.mul_mem hy₁ hy₂)),
           x₁ * y₂ + x₂ * y₁, C.add_mem (C.mul_mem hx₁ hy₂) (C.mul_mem hx₂ hy₁), by ring⟩

/-- `C[a]` is a cone (contains all squares). -/
lemma coneExt_isCone {C : Subsemiring F} (hCone : IsCone C) (a : F) :
    IsCone (coneExt C hCone a) :=
  fun x => ⟨x ^ 2, hCone x, 0, C.zero_mem, by ring⟩

/-- **BPR Lemma 2.9.** If `C` is a proper cone and `−a ∉ C`, then `C[a]` is proper. -/
theorem lemma_2_9 {C : Subsemiring F} (hC : IsProperCone C) (hna : -a ∉ C) :
    IsProperCone (coneExt C hC.1 a) := by
  refine ⟨coneExt_isCone hC.1 a, ?_⟩
  -- Need: -1 ∉ coneExt C a, i.e., ¬∃ x ∈ C, ∃ y ∈ C, -1 = x + a*y
  rintro ⟨x, hx, y, hy, heq⟩
  by_cases hy0 : y = 0
  · rw [hy0, mul_zero, add_zero] at heq; exact hC.2 (heq ▸ hx)
  · apply hna
    have hay : a * y = -1 - x := by linear_combination -heq
    have ha : a = (-1 - x) * y⁻¹ := by rw [← hay]; field_simp
    have : -a = y⁻¹ ^ 2 * (y * (1 + x)) := by rw [ha]; field_simp; ring
    rw [this]
    exact C.mul_mem (hC.1 y⁻¹) (C.mul_mem hy (C.add_mem C.one_mem hx))

end Lemma_2_9

/-!
### Proposition 2.8

**Proposition 2.8 (BPR).** Let `C` be a proper cone of `F`. Then `C` is
contained in the positive cone of some order on `F`.

Equivalently, there exists a `RingCone` (= proper cone with antisymmetry)
containing `C` that also satisfies totality (`HasMemOrNegMem`).

The proof uses Zorn's lemma to obtain a maximal proper cone `C̄ ⊇ C`,
then Lemma 2.9 to show `C̄ ∪ (−C̄) = F`.
-/

section Prop_2_8

variable {F : Type*} [Field F]

/-- The sSup of a chain of proper cones is a proper cone (when the chain is nonempty). -/
lemma chain_ub_isProperCone {c : Set (Subsemiring F)}
    (hc : IsChain (· ≤ ·) c) (hpc : ∀ T ∈ c, IsProperCone T)
    {T₀ : Subsemiring F} (hT₀ : T₀ ∈ c) :
    IsProperCone (sSup c) := by
  constructor
  · -- IsCone: x² ∈ sSup c because x² ∈ T₀ ≤ sSup c
    intro x
    exact le_sSup hT₀ ((hpc T₀ hT₀).1 x)
  · -- -1 ∉ sSup c: if -1 ∈ sSup c then -1 ∈ some T ∈ c
    intro hmem
    rw [Subsemiring.mem_sSup_of_directedOn ⟨T₀, hT₀⟩ hc.directedOn] at hmem
    obtain ⟨T, hT, hmT⟩ := hmem
    exact (hpc T hT).2 hmT

/-- `C[a]` contains `C`. -/
lemma le_coneExt (C : Subsemiring F) (hCone : IsCone C) (a : F) :
    C ≤ coneExt C hCone a :=
  fun x hx => ⟨x, hx, 0, C.zero_mem, by ring⟩

/-- **BPR Proposition 2.8.** Every proper cone is contained in a `RingCone`
    with totality (i.e., the positive cone of some order). -/
theorem prop_2_8 {C : Subsemiring F} (hC : IsProperCone C) :
    ∃ T : RingCone F, (C : Set F) ⊆ T ∧ HasMemOrNegMem T := by
  -- Apply Zorn's lemma to the set of proper cones containing C, ordered by ≤
  let S := {T : Subsemiring F | IsProperCone T ∧ C ≤ T}
  have hCS : C ∈ S := ⟨hC, le_refl C⟩
  -- Chain condition: every nonempty chain in S has an upper bound in S
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | ⟨T₀, hT₀⟩
    · exact ⟨C, hCS, fun z hz => hz.elim⟩
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun T hT => le_sSup hT⟩
      · exact chain_ub_isProperCone hc (fun T hT => (hcS hT).1) hT₀
      · exact le_trans (hcS hT₀).2 (le_sSup hT₀)
  -- Obtain a maximal element M ∈ S
  obtain ⟨M, hMS, hMax⟩ := zorn_le₀ S hchain
  -- M contains C
  have hCM : C ≤ M := hMS.2
  -- Show M gives a RingCone with totality
  refine ⟨hMS.1.toRingCone, fun x hx => hCM hx, ⟨fun a => ?_⟩⟩
  -- Need: a ∈ M ∨ -a ∈ M
  by_contra hboth
  push Not at hboth
  obtain ⟨ha, hna⟩ := hboth
  -- By Lemma 2.9, M[a] is a proper cone extending M
  have hMa : IsProperCone (coneExt M hMS.1.1 a) :=
    lemma_2_9 hMS.1 hna
  -- M[a] contains M and a ∈ M[a]
  have hMle : M ≤ coneExt M hMS.1.1 a := le_coneExt M hMS.1.1 a
  have hMaS : coneExt M hMS.1.1 a ∈ S :=
    ⟨hMa, le_trans hCM hMle⟩
  -- By maximality of M, M = M[a], so a ∈ M — contradiction
  have heq : coneExt M hMS.1.1 a ≤ M := hMax hMaS hMle
  -- a = a + M.0 * 0 ∈ coneExt M ... a
  have ha' : a ∈ coneExt M hMS.1.1 a :=
    ⟨0, M.zero_mem, 1, M.one_mem, by ring⟩
  exact ha (heq ha')

end Prop_2_8

end Cones

end Azurite.BPR

namespace Azurite.BPR

/-!
### Theorem 2.7: Equivalent characterizations of real fields

**Theorem 2.7 (BPR p.37).** Let F be a field. The following are equivalent:
- **(a)** F is a real field (`IsRealField F`).
- **(b)** F has a proper cone (`∃ C : Subsemiring F, IsProperCone C`).
- **(c)** F can be ordered (`∃ T : RingCone F, HasMemOrNegMem T`).
    A `RingCone` with totality is exactly the data of a linear field ordering
    (positive cone = elements of T; `IsCone` holds automatically since
    `HasMemOrNegMem` implies every square is in T).
- **(d)** For every finite family `x : Fin n → F`, `∑ i, x i ^ 2 = 0 → ∀ i, x i = 0`.

**Proof outline:**
- a) ⇒ b): `ΣF^{(2)}` is a proper cone when F is real.
- b) ⇒ c): Proposition 2.8 (Zorn's lemma) extends any proper cone to a total one.
- c) ⇒ d): If `∑ xᵢ² = 0` and xₖ ≠ 0, then `∑_{i≠k} xᵢ²` and its negative
  `xₖ²` are both in T, forcing `∑_{i≠k} xᵢ² = 0` (antisymmetry), then xₖ² = 0.
- d) ⇒ a): If −1 ∈ ΣF^{(2)}, then −1 = ∑ aᵢ², so 1² + ∑ aᵢ² = 0, giving 1 = 0.
-/

section Theorem_2_7

variable {F : Type*} [Field F]

/-- Extract a Fin-indexed vector from an `IsSumSq` witness. -/
lemma isSumSq_exists_vector {s : F} (h : IsSumSq s) :
    ∃ (n : ℕ) (x : Fin n → F), s = ∑ i, x i * x i := by
  induction h with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | sq_add a _ ih =>
    obtain ⟨n, x, rfl⟩ := ih
    exact ⟨n + 1, Fin.cons a x, by simp [Fin.sum_univ_succ]⟩

/-- **Theorem 2.7 a) ⇒ b).** A real field has a proper cone, namely `ΣF^{(2)}`. -/
theorem theorem_2_7_a_of_b (ha : IsRealField F) : ∃ C : Subsemiring F, IsProperCone C :=
  ⟨sumOfSquares F, isCone_sumOfSquares F, (isRealField_iff_neg_one_notMem F).mp ha⟩

/-- **Theorem 2.7 b) ⇒ c).** A proper cone extends to a `RingCone` with totality
    (Proposition 2.8). -/
theorem theorem_2_7_b_of_c (hb : ∃ C : Subsemiring F, IsProperCone C) :
    ∃ T : RingCone F, HasMemOrNegMem T := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨T, _, hT⟩ := prop_2_8 hC
  exact ⟨T, hT⟩

/-- **Theorem 2.7 c) ⇒ d).** If F has a total RingCone, then every
    finite sum of squares that equals 0 forces all summands to be 0. -/
theorem theorem_2_7_c_of_d (hc : ∃ T : RingCone F, HasMemOrNegMem T) :
    ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0 := by
  obtain ⟨T, hT⟩ := hc
  intro n x hsum k
  -- S := ∑_{i ≠ k} xᵢ²
  set S := ∑ i ∈ Finset.univ.erase k, x i ^ 2 with hS_def
  -- S + xk² = 0 (from hsum via Finset.sum_erase_add)
  have hSk : S + x k ^ 2 = 0 := by
    have hera : ∑ i ∈ Finset.univ.erase k, x i ^ 2 + x k ^ 2 = ∑ i : Fin n, x i ^ 2 :=
      Finset.sum_erase_add Finset.univ _ (Finset.mem_univ k)
    linear_combination hera.trans hsum
  -- Each xᵢ² is in T: by HasMemOrNegMem, xᵢ ∈ T or -xᵢ ∈ T; in either case xᵢ² = xᵢ·xᵢ ∈ T
  have hmem : ∀ i : Fin n, x i ^ 2 ∈ T.toSubsemiring := fun i => by
    rw [sq]
    rcases hT.mem_or_neg_mem (x i) with h | h
    · exact T.toSubsemiring.mul_mem h h
    · have := T.toSubsemiring.mul_mem h h
      rwa [neg_mul_neg] at this
  -- S ∈ T (sum of elements in a subsemiring)
  have hS_mem : S ∈ T.toSubsemiring :=
    T.toSubsemiring.sum_mem fun i _ => hmem i
  -- -S = xk² ∈ T
  have hneg_eq : -S = x k ^ 2 := by linear_combination -hSk
  have hneg_mem : -S ∈ T.toSubsemiring := hneg_eq ▸ hmem k
  -- By RingCone antisymmetry: S = 0
  have hS0 : S = 0 := T.eq_zero_of_mem_of_neg_mem' hS_mem hneg_mem
  -- xk² = 0 hence xk = 0
  have hk2 : x k ^ 2 = 0 := by rw [hS0, zero_add] at hSk; exact hSk
  exact pow_eq_zero_iff (by norm_num) |>.mp hk2

/-- **Theorem 2.7 d) ⇒ a).** If sums of squares vanish only trivially,
    then −1 is not a sum of squares. -/
theorem theorem_2_7_d_of_a
    (hd : ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0) :
    IsRealField F := by
  rw [isRealField_iff]
  intro h
  obtain ⟨n, x, hx⟩ := isSumSq_exists_vector h
  -- Let y = Fin.cons 1 x : Fin (n+1) → F (prepend 1)
  let y : Fin (n + 1) → F := Fin.cons 1 x
  have hkey : ∑ i : Fin (n + 1), y i ^ 2 = 0 := by
    simp only [y, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sq]
    -- goal: 1 * 1 + ∑ i, x i * x i = 0
    -- hx : -1 = ∑ i, x i * x i, so ∑ x i * x i = -1
    have : ∑ i : Fin n, x i * x i = -1 := hx.symm
    rw [this]; ring
  have h1 := hd (n + 1) y hkey ⟨0, Nat.zero_lt_succ n⟩
  simp [y, Fin.cons_zero] at h1

/-- **Theorem 2.7 (BPR p.37).** The four characterizations of real fields are equivalent.

The `List.TFAE` structure lets us extract any pairwise implication via `theorem_2_7.out`. -/
theorem theorem_2_7 {F : Type*} [Field F] : List.TFAE
    [ IsRealField F,
      ∃ C : Subsemiring F, IsProperCone C,
      ∃ T : RingCone F, HasMemOrNegMem T,
      ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0] := by
  tfae_have 1 → 2 := theorem_2_7_a_of_b
  tfae_have 2 → 3 := theorem_2_7_b_of_c
  tfae_have 3 → 4 := theorem_2_7_c_of_d
  tfae_have 4 → 1 := theorem_2_7_d_of_a
  tfae_finish

end Theorem_2_7

end Azurite.BPR

namespace Azurite.BPR

open Polynomial

/-!
### Definition: Real Closed Field (BPR Definition 2.8, p.38)

**Definition (BPR p.38).** A field R is *real closed* if:
1. R is an ordered field whose positive cone is the set of squares R^{(2)},
   i.e., `0 ≤ x ↔ IsSquare x`.
2. Every polynomial in R[X] of odd degree has a root in R.

**Mathlib correspondence.** Mathlib's `IsRealClosed R` (in
`Mathlib.FieldTheory.IsRealClosed.Basic`) uses an equivalent formulation
without requiring a linear order as data:
- `IsSemireal R`: `-1` is not a sum of squares.
- `IsSquare x ∨ IsSquare (-x)` for every `x`: every element or its negative is a square.
- Every odd-degree polynomial has a root.

The BPR ordered-field form is a special case:
`IsRealClosed.of_linearOrderedField` derives `IsRealClosed` from it.
Conversely, `IsRealClosed.nonneg_iff_isSquare` (for any linear order on an
`IsRealClosed` field) shows the positive cone equals the squares.
-/

section RealClosedField

variable (R : Type*) [Field R]

/-- **BPR Definition 2.8.** `R` is a *real closed field* if it is an ordered field
    whose positive cone equals the set of squares, and every odd-degree polynomial has a root.

    We define this as `IsRealClosed R` from Mathlib, which uses an equivalent
    algebraically intrinsic formulation not requiring a linear order as data. -/
def IsRealClosedField : Prop := IsRealClosed R

/-- A real closed field is a real field. -/
theorem IsRealClosedField.isRealField [IsRealClosed R] : IsRealField R :=
  (isRealField_iff R).mpr (IsSemireal.not_isSumSq_neg_one R)

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Definition 2.8 (ordered form).** Given an ordered field, `R` is real closed iff
    (1) the positive cone equals the squares, and (2) odd-degree polynomials have roots. -/
theorem isRealClosedField_iff :
    IsRealClosedField R ↔
    (∀ x : R, 0 ≤ x ↔ IsSquare x) ∧
    (∀ f : R[X], Odd f.natDegree → ∃ x, f.IsRoot x) := by
  constructor
  · intro h
    haveI : IsRealClosed R := h
    exact ⟨fun _ => IsRealClosed.nonneg_iff_isSquare,
           fun f hf => IsRealClosed.exists_isRoot_of_odd_natDegree hf⟩
  · intro ⟨hcone, hroots⟩
    exact IsRealClosed.of_linearOrderedField
      (fun hx => (hcone _).mp hx) (fun {f} hf => hroots f hf)

/-- In a real closed ordered field, `x ≥ 0 ↔ x` is a square. -/
theorem IsRealClosedField.nonneg_iff_isSquare [IsRealClosed R] {x : R} :
    0 ≤ x ↔ IsSquare x :=
  IsRealClosed.nonneg_iff_isSquare

end RealClosedField

/-!
### IsRealClosed implies a linear order

`IsRealClosed R` (algebraic, no order) implies `R` can be linearly ordered.
Construction: `sumOfSquares R` is a proper cone (by `IsSemireal`), extended to
a total cone `T` by `prop_2_8`. We then use `T` to define both `LinearOrder R`
and `IsOrderedRing R` from the same cone, ensuring compatibility.
-/

section IsRealClosedOrder

variable {R : Type*} [Field R] [IsRealClosed R]

private lemma isProperCone_sumOfSquares_realClosed :
    IsProperCone (sumOfSquares R) :=
  ⟨isCone_sumOfSquares (F := R),
   (isRealField_iff_neg_one_notMem R).mp (IsRealClosedField.isRealField R)⟩

-- The canonical total cone: the sum-of-squares cone extended to a total cone
-- via Prop. 2.8. Using `Classical.choose` ensures both instances share the
-- same cone and hence produce compatible orders.
private noncomputable def isRealClosed_totalCone : RingCone R :=
  Classical.choose (prop_2_8 isProperCone_sumOfSquares_realClosed)

private lemma isRealClosed_totalCone_total :
    HasMemOrNegMem (isRealClosed_totalCone (R := R)) :=
  (Classical.choose_spec (prop_2_8 isProperCone_sumOfSquares_realClosed)).2

/-- A real closed field carries a noncomputable linear order, with
    `a ≤ b ↔ b - a` lies in the total cone extending `ΣR^{(2)}`. -/
noncomputable instance IsRealClosed.toLinearOrder : LinearOrder R :=
  haveI : DecidablePred (· ∈ (isRealClosed_totalCone (R := R)).toAddGroupCone) :=
    Classical.decPred _
  haveI : HasMemOrNegMem (isRealClosed_totalCone (R := R)).toAddGroupCone :=
    ⟨fun a => (isRealClosed_totalCone_total (R := R)).mem_or_neg_mem a⟩
  LinearOrder.mkOfAddGroupCone (isRealClosed_totalCone (R := R)).toAddGroupCone

/-- The linear order on a real closed field is compatible with the ring structure. -/
noncomputable instance IsRealClosed.toIsOrderedRing :
    @IsOrderedRing R _ IsRealClosed.toLinearOrder.toPartialOrder :=
  IsOrderedRing.mkOfCone (isRealClosed_totalCone (R := R))

end IsRealClosedOrder

/-!
### Uniqueness of the ordering on a real closed field
-/

section UniqueOrder

/-- In a real closed field with a given compatible ordering, `a ≤ b` iff `b - a` is a square.
    This is the key lemma: since `IsSquare` is order-independent, any two orderings
    satisfying this must agree. -/
private lemma isRealClosed_characterize_le
    {R : Type*} [Field R] [IsRealClosed R]
    (lo : LinearOrder R) (hlo : @IsStrictOrderedRing R _ lo.toPartialOrder)
    {a b : R} :
    @LE.le R lo.toLE a b ↔ IsSquare (b - a) := by
  letI : LinearOrder R := lo
  letI : IsStrictOrderedRing R := hlo
  exact sub_nonneg.symm.trans IsRealClosed.nonneg_iff_isSquare

/-- **Uniqueness of the order on a real closed field.**

Any two linear orderings making `R` into a strictly ordered ring must agree on every
comparison `a ≤ b`.

**Proof.** In any ordered field, `a ≤ b ↔ 0 ≤ b - a`, and in a real closed field
`0 ≤ x ↔ IsSquare x`. Since `IsSquare` is purely algebraic (independent of the ordering),
both orderings satisfy `a ≤ b ↔ IsSquare (b - a)` and must agree.

Equivalently: the positive cone of any compatible ordering necessarily contains `R^{(2)}`
(squares are always nonneg in an ordered ring); the real closed condition forces the positive
cone to be *exactly* `R^{(2)}`, leaving no room for a second ordering. -/
theorem isRealClosed_le_unique
    {R : Type*} [Field R] [IsRealClosed R]
    (lo₁ lo₂ : LinearOrder R)
    (h₁ : @IsStrictOrderedRing R _ lo₁.toPartialOrder)
    (h₂ : @IsStrictOrderedRing R _ lo₂.toPartialOrder)
    {a b : R} :
    @LE.le R lo₁.toLE a b ↔ @LE.le R lo₂.toLE a b :=
  (isRealClosed_characterize_le lo₁ h₁).trans (isRealClosed_characterize_le lo₂ h₂).symm

end UniqueOrder

namespace Azurite.BPR

/-!
### Definition: Real Algebraic Numbers (BPR p.38)

**Definition (BPR p.38).** The *real algebraic numbers* `R_alg` are those real numbers
that satisfy a nonzero polynomial equation with integer coefficients:
$$R_{\mathrm{alg}} := \{x \in \mathbb{R} \mid \exists p \in \mathbb{Z}[X],\, p \neq 0,\, p(x) = 0\}.$$

Equivalently (clearing denominators), a real number is algebraic over `ℤ` iff it is algebraic
over `ℚ`. In Mathlib this is `IsAlgebraic ℤ x` (using the `Algebra ℤ ℝ` instance).

The real algebraic numbers form a subfield of `ℝ` (since algebraic elements over a subfield
of a field extension are closed under the field operations).
-/

section RealAlgebraicNumbers

/-- **BPR p.38.** The set of *real algebraic numbers* `R_alg`:
    those `x : ℝ` satisfying some nonzero polynomial with integer coefficients.

    Formally: `IsAlgebraic ℤ x`, i.e., `∃ p : ℤ[X], p ≠ 0 ∧ aeval x p = 0`. -/
def realAlgebraicNumbers : Set ℝ :=
  {x : ℝ | IsAlgebraic ℤ x}

scoped notation "ℝ_alg" => realAlgebraicNumbers

/-- The zero element 0 is real algebraic, witnessed by the polynomial `X`. -/
theorem zero_mem_realAlgebraicNumbers : (0 : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_zero

/-- The element 1 is real algebraic, witnessed by the polynomial `X - 1`. -/
theorem one_mem_realAlgebraicNumbers : (1 : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_one

/-- Every integer is a real algebraic number. -/
theorem intCast_mem_realAlgebraicNumbers (n : ℤ) : (n : ℝ) ∈ realAlgebraicNumbers :=
  isAlgebraic_algebraMap n

end RealAlgebraicNumbers

/-!
### Intermediate Value Property (BPR p.38)

**Definition (BPR p.38).** A field `R` has the *intermediate value property* if `R` is an
ordered field such that, for any `P ∈ R[X]`, if there exist `a, b ∈ R` with `a < b` and
`P(a) · P(b) < 0`, then there exists `x ∈ (a, b)` such that `P(x) = 0`.
-/

section IntermediateValueProperty

/-- **BPR Definition (p.38).** An ordered field `R` has the *intermediate value property*
    if, for every polynomial `P ∈ R[X]` and every pair `a < b` with `P(a) · P(b) < 0`,
    there exists `x ∈ (a, b)` such that `P(x) = 0`. -/
def HasIntermediateValueProperty (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Prop :=
  ∀ (P : Polynomial R) (a b : R), a < b →
    Polynomial.eval a P * Polynomial.eval b P < 0 →
    ∃ x : R, a < x ∧ x < b ∧ Polynomial.eval x P = 0

end IntermediateValueProperty

section NoNontrivialRealExtension

variable {u : _} (F : Type u) [Field F]

/-- **BPR Theorem 2.11 (d).** A field `F` has *no non-trivial real algebraic extension*
    if it is a real field and every algebraic extension of `F` that is also real must
    coincide with `F` (i.e., the algebra map is surjective). -/
def HasNoNontrivialRealAlgebraicExtension : Prop :=
  IsRealField F ∧
  ∀ (F₁ : Type u) [Field F₁] [Algebra F F₁],
    Algebra.IsAlgebraic F F₁ → IsRealField F₁ →
    Function.Surjective (algebraMap F F₁)

end NoNontrivialRealExtension

/-!
### Symmetric Polynomials (BPR p.38)

**Definition (BPR p.38).** Let `K` be a field. A polynomial `Q(X₁, …, Xₖ) ∈ K[X₁, …, Xₖ]`
is *symmetric* if for every permutation `σ` of `{1, …, k}`,
`Q(X_{σ(1)}, …, X_{σ(k)}) = Q(X₁, …, Xₖ)`.

**Mathlib correspondence.** This is exactly `MvPolynomial.IsSymmetric` from
`Mathlib.RingTheory.MvPolynomial.Symmetric.Defs`, defined as
`∀ e : Equiv.Perm σ, MvPolynomial.rename e φ = φ`.
-/

section SymmetricPolynomials

open MvPolynomial

variable {K : Type*} [Field K]

/-- **BPR Definition (p.38).** A polynomial `Q ∈ K[X₁, …, Xₖ]` is *symmetric* if it is
    invariant under every permutation of its variables.

    This is `MvPolynomial.IsSymmetric` in Mathlib: `∀ e : Perm (Fin k), rename e Q = Q`. -/
def IsSymmetricPolynomial (k : ℕ) (Q : MvPolynomial (Fin k) K) : Prop :=
  Q.IsSymmetric

/-- **BPR Definition (p.38).** The `i`-th *elementary symmetric function*
    `E_i = ∑_{1 ≤ j₁ < ⋯ < jᵢ ≤ k} X_{j₁} ⋯ X_{jᵢ}`,
    i.e., the sum of all squarefree degree-`i` monomials.

    This is `MvPolynomial.esymm` in Mathlib. -/
noncomputable def elementarySymmetric (k : ℕ) (i : ℕ) : MvPolynomial (Fin k) K :=
  esymm (Fin k) K i

end SymmetricPolynomials

section Lemma_2_12

open Polynomial

variable {K : Type*} [CommRing K]

/-- **BPR Lemma 2.12.** Let `x₁, …, xₖ ∈ K` and
    `P = (X − x₁)⋯(X − xₖ) = Xᵏ + C₁Xᵏ⁻¹ + ⋯ + Cₖ`.
    Then `Cᵢ = (−1)ⁱ Eᵢ(x₁, …, xₖ)`, i.e., the coefficient of `Xᵏ⁻ⁱ` in `P`
    equals `(−1)ⁱ` times the `i`-th elementary symmetric function evaluated at
    the roots.

    This is `Multiset.prod_X_sub_C_coeff` in Mathlib, specialized to `Fin k → K`. -/
theorem lemma_2_12 {k : ℕ} (x : Fin k → K) {i : ℕ} (hi : i ≤ k) :
    (∏ j : Fin k, (X - C (x j))).coeff (k - i) =
    (-1) ^ i * (Finset.univ.val.map x).esymm i := by
  have hcard : (Finset.univ.val.map x).card = k := by simp
  have hmap : (Finset.univ.val.map (fun j => X - C (x j))) =
      (Finset.univ.val.map x).map (fun t => X - C t) := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, hmap,
      Multiset.prod_X_sub_C_coeff _ (by omega)]
  simp only [hcard, Nat.sub_sub_self hi]

end Lemma_2_12

/-!
### Exercise 2.7: Orbit sums span symmetric polynomials

**Exercise 2.7 (BPR).** For a multi-index `α`, define
`M_α = ∑_{σ ∈ S_k} X_σ^α`. Prove that every symmetric polynomial can be written
as a finite sum `∑ c_α M_α`.

The proof uses averaging: since `rename σ Q = Q` for symmetric `Q`,
`k! • Q = ∑_σ rename σ Q`. Expanding `Q` as a sum of monomials and swapping
sums gives `k! • Q = ∑_α coeff_α(Q) • M_α`. Dividing by `k!` (nonzero in
characteristic 0) yields the result.

**Characteristic restriction.** BPR does not mention a characteristic restriction, but
the `CharZero K` hypothesis is necessary for this formulation. In characteristic `p`,
`M_α` sums over *all* permutations (including those that fix `α`), so the stabilizer
multiplicity `|Stab(α)|` appears as a factor. When `p ∣ |Stab(α)|`, `M_α` vanishes.
For example, `X₁X₂ ∈ F₂[X₁,X₂]` is symmetric but `M_{(1,1)} = 2X₁X₂ = 0`
in char 2, and no other `M_α` contains the monomial `X₁X₂`.

The statement *does* hold over arbitrary fields if one uses the proper monomial
symmetric polynomials `m_α = ∑_{β ∈ orbit(α)} X^β` (each distinct monomial counted
once), which is Mathlib's `MvPolynomial.msymm`. If a future application needs the
result in positive characteristic, this proof should be refactored to use `msymm`.
-/

section Exercise_2_7

open MvPolynomial Equiv

variable {K : Type*} [Field K]

/-- **BPR Notation.** `M_α = ∑_{σ ∈ S_k} X_σ^α`: the sum of the monomial `X^α` over
    all permutations of the variables. `X_σ^α = rename σ (monomial α 1)`. -/
noncomputable def monomialOrbitSum (k : ℕ) (α : Fin k →₀ ℕ) : MvPolynomial (Fin k) K :=
  ∑ σ : Perm (Fin k), rename (σ : Fin k → Fin k) (monomial α 1)

/-- **BPR Exercise 2.7.** Every symmetric polynomial can be written as a finite
    sum `∑ cα • M_α`. -/
theorem exercise_2_7 [CharZero K] {k : ℕ} {Q : MvPolynomial (Fin k) K}
    (hQ : Q.IsSymmetric) :
    ∃ (S : Finset (Fin k →₀ ℕ)) (c : (Fin k →₀ ℕ) → K),
      Q = ∑ α ∈ S, c α • monomialOrbitSum k α := by
  refine ⟨Q.support, fun α => Q.coeff α / (k.factorial : K), ?_⟩
  have hk_ne : (↑k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  -- Step 1: k! • Q = ∑ σ, rename σ Q
  have h1 : (↑k.factorial : K) • Q = ∑ σ : Perm (Fin k), rename ↑σ Q := by
    conv_rhs => arg 2; ext σ; rw [hQ σ]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    norm_cast
  -- Step 2: ∑ σ, rename σ Q = ∑ α ∈ support, coeff α Q • M_α
  have h2 : ∑ σ : Perm (Fin k), rename (↑σ) Q =
      ∑ α ∈ Q.support, Q.coeff α • (monomialOrbitSum k α : MvPolynomial (Fin k) K) := by
    calc ∑ σ : Perm (Fin k), rename (⇑σ) Q
        = ∑ σ : Perm (Fin k), ∑ α ∈ Q.support,
            MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α) (Q.coeff α) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          conv_lhs => rw [Q.as_sum, map_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          exact rename_monomial _ _ _
      _ = ∑ α ∈ Q.support, ∑ σ : Perm (Fin k),
            MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α) (Q.coeff α) :=
          Finset.sum_comm
      _ = ∑ α ∈ Q.support, Q.coeff α • monomialOrbitSum k α := by
          refine Finset.sum_congr rfl fun α _ => ?_
          unfold monomialOrbitSum; simp_rw [rename_monomial]
          have hfactor : ∀ σ : Perm (Fin k),
            (MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α)) (Q.coeff α) =
            Q.coeff α • (MvPolynomial.monomial (Finsupp.mapDomain (⇑σ) α)) (1 : K) :=
            fun σ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          simp_rw [hfactor, ← Finset.smul_sum]
  -- Combine: Q = (1/k!) • k! • Q = ∑ (coeff/k!) • M_α
  have hmain := h1.trans h2
  have hinv : Q = (↑k.factorial : K)⁻¹ • ((↑k.factorial : K) • Q) :=
    (inv_smul_smul₀ hk_ne Q).symm
  conv_lhs => rw [hinv, hmain, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [smul_comm (↑k.factorial : K)⁻¹, div_eq_mul_inv, mul_smul]

end Exercise_2_7

section Definition_2_14

/-- **BPR Definition 2.14.** The *lexicographic ordering* on `Fin k → B` for a
    linearly ordered type `B`: `a <ₗₑₓ b` iff there exists an index `i` such that
    `a j = b j` for all `j < i` and `a i < b i`.

    This is `Pi.Lex (· < ·) (· < ·)` in Mathlib (`Mathlib.Order.PiLex`). -/
def LexOrder (k : ℕ) (B : Type*) [LT B] (a b : Fin k → B) : Prop :=
  Pi.Lex (· < ·) (· < ·) a b

end Definition_2_14

/-!
### Properties of the lexicographic ordering on monomials

BPR notes three key properties of the lex ordering on monomials `Fin k →₀ ℕ`:
1. The smallest monomial is `1` (the zero exponent).
2. The ordering is compatible with multiplication (addition of exponents).
3. The set of monomials `≤ₗₑₓ` a given monomial can be infinite.
-/

section LexProperties

/-- The zero multi-index (monomial `1`) is the lex-smallest: for any nonzero `α`,
    `0 <ₗₑₓ α`. -/
theorem lex_bot {k : ℕ} {α : Fin k →₀ ℕ} (hα : α ≠ 0) :
    LexOrder k ℕ 0 α := by
  simp only [LexOrder, Pi.Lex, Pi.zero_apply]
  rw [Finsupp.ne_iff] at hα
  obtain ⟨i, hi⟩ := hα
  have hi' : 0 < α i := by simp [Finsupp.coe_zero] at hi; omega
  classical
  let S := Finset.univ.filter (fun j : Fin k => 0 < α j)
  have hS : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩⟩
  refine ⟨S.min' hS, fun m hm => ?_, ?_⟩
  · by_contra h; push Not at h
    have : 0 < α m := Nat.pos_of_ne_zero (by omega)
    exact absurd (Finset.min'_le S m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩))
      (not_le.mpr hm)
  · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2

/-- The lex ordering on monomials is compatible with multiplication:
    if `α <ₗₑₓ β` then `α + γ <ₗₑₓ β + γ`. -/
theorem lex_add_right {k : ℕ} {α β γ : Fin k →₀ ℕ}
    (h : LexOrder k ℕ α β) :
    LexOrder k ℕ (α + γ) (β + γ) := by
  simp only [LexOrder, Pi.Lex] at *
  obtain ⟨i, hi_eq, hi_lt⟩ := h
  refine ⟨i, fun m hm => ?_, ?_⟩
  · simp [Pi.add_apply, hi_eq m hm]
  · simp [Pi.add_apply]; omega

/-- The set of monomials lex-≤ a given monomial can be infinite.
    Concretely, for `k ≥ 2` and `α = X₁`, the set
    `{β | LexOrder k ℕ β α ∨ β = α}` is infinite. -/
theorem lex_le_set_infinite {k : ℕ} (hk : 2 ≤ k) :
    Set.Infinite {β : Fin k →₀ ℕ | LexOrder k ℕ β (Finsupp.single ⟨0, by omega⟩ 1) ∨
      β = Finsupp.single ⟨0, by omega⟩ 1} := by
  -- For any n, Finsupp.single ⟨1, _⟩ n is in the set (since its 0-th component is 0 < 1)
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => Finsupp.single ⟨1, by omega⟩ n)
  · intro a b hab
    simp [Finsupp.single_eq_single_iff] at hab
    omega
  · intro n
    left
    simp only [LexOrder, Pi.Lex]
    exact ⟨⟨0, by omega⟩, fun j hj => absurd hj (not_lt.mpr (Fin.mk_le_mk.mpr (Nat.zero_le _))),
      by simp [Fin.ext_iff]⟩

/-- **BPR Exercise 2.8.** A strictly decreasing sequence for the lexicographic
    ordering on `ℕᵏ` is necessarily finite. Equivalently, the lex ordering on
    multi-indices is well-founded.

    The classical proof is by induction on `k`: for `k = 0` every sequence is
    constant; for `k + 1`, the first component must eventually stabilize (by
    well-foundedness of `ℕ`), after which the problem reduces to `ℕᵏ`.

    In Mathlib this is `Pi.Lex.wellFounded` applied to `Fin k` (finite, linearly
    ordered) and `ℕ` (well-ordered). -/
theorem exercise_2_8 (k : ℕ) :
    WellFounded (fun α β : Fin k →₀ ℕ => LexOrder k ℕ α β) := by
  unfold LexOrder
  exact InvImage.wf (fun (x : Fin k →₀ ℕ) => (x : Fin k → ℕ))
    (Pi.Lex.wellFounded _ (fun _ => Nat.lt_wfRel.wf))

end LexProperties

section Definition_2_15

/-- **BPR Definition 2.15.** The *graded lexicographic ordering* on the set of
    monomials in `k` variables: `X^α <_grlex X^β` iff either `|α| < |β|`
    (total degree is smaller) or `|α| = |β|` and `α <_lex β`.

    In Mathlib this is the `<` on `DegLex (Fin k →₀ ℕ)`, accessed via
    `toDegLex` / `ofDegLex` from `Mathlib.Data.Finsupp.MonomialOrder.DegLex`. -/
def GrlexOrder (k : ℕ) (α β : Fin k →₀ ℕ) : Prop :=
  toDegLex α < toDegLex β

end Definition_2_15

section GrlexProperties

open Finsupp.DegLex in
/-- The zero multi-index (monomial `1`) is the grlex-smallest: for any nonzero `α`,
    `0 <_grlex α`. -/
theorem grlex_bot {k : ℕ} {α : Fin k →₀ ℕ} (hα : α ≠ 0) :
    GrlexOrder k 0 α := by
  exact bot_lt_iff_ne_bot.mpr (show toDegLex α ≠ ⊥ from fun h => hα (toDegLex_inj.mp h))

open Finsupp.DegLex in
/-- The grlex ordering on monomials is compatible with multiplication:
    if `α <_grlex β` then `α + γ <_grlex β + γ`. -/
theorem grlex_add_right {k : ℕ} {α β γ : Fin k →₀ ℕ}
    (h : GrlexOrder k α β) :
    GrlexOrder k (α + γ) (β + γ) := by
  simp only [GrlexOrder, lt_iff, ofDegLex_toDegLex] at *
  rcases h with hdeg | ⟨hdeq, hlex⟩
  · left; simp [map_add]; omega
  · right
    exact ⟨by simp [map_add, hdeq], by simpa [toLex_add] using add_lt_add_right hlex (toLex γ)⟩

open Finsupp.DegLex in
/-- The set of monomials grlex-≤ a given monomial is always finite.
    This is because grlex-≤ implies bounded total degree, and there
    are finitely many monomials of bounded total degree in `k` variables. -/
theorem grlex_le_set_finite {k : ℕ} (α : Fin k →₀ ℕ) :
    Set.Finite {β : Fin k →₀ ℕ | GrlexOrder k β α ∨ β = α} := by
  apply Set.Finite.subset (Finsupp.finite_of_degree_le α.degree)
  intro β hβ
  rcases hβ with hlt | heq
  · exact monotone_degree (le_of_lt hlt)
  · simp [heq]

end GrlexProperties

section Proposition_2_13

variable {K : Type*} [CommRing K]

open MvPolynomial in
/-- **BPR Proposition 2.13** (Fundamental Theorem of Symmetric Polynomials).
    Let `K` be a field. Every symmetric polynomial `Q(X₁,…,Xₖ) ∈ K[X₁,…,Xₖ]`
    can be written as `R(E₁,…,Eₖ)` for some polynomial `R(T₁,…,Tₖ) ∈ K[T₁,…,Tₖ]`,
    where `Eᵢ` is the `i`-th elementary symmetric function.

    **Proof sketch (BPR):** The leading monomial of a symmetric polynomial `Q`
    in the graded lexicographic ordering satisfies `α₁ ≥ α₂ ≥ ⋯ ≥ αₖ`.
    Subtracting the matching product `c_α E₁^{α₁−α₂} ⋯ Eₖ^{αₖ}` yields a symmetric
    polynomial `Q₁` with strictly smaller leading monomial. Iterating and using
    well-foundedness of the grlex ordering (no infinite descending sequences) gives
    the result.

    In Mathlib this is `MvPolynomial.esymmAlgHom_surjective`, which states that the
    `R`-algebra homomorphism sending `Tᵢ ↦ Eᵢ` is surjective onto the symmetric
    subalgebra. -/
theorem proposition_2_13 {k : ℕ} (Q : MvPolynomial (Fin k) K)
    (hQ : Q.IsSymmetric) :
    ∃ R : MvPolynomial (Fin k) K,
      MvPolynomial.aeval (fun i : Fin k => MvPolynomial.esymm (Fin k) K (↑i + 1)) R = Q := by
  have hsurj := MvPolynomial.esymmAlgHom_surjective K (show Fintype.card (Fin k) ≤ k by simp)
  obtain ⟨R, hR⟩ := hsurj ⟨Q, hQ⟩
  exact ⟨R, by rw [← MvPolynomial.esymmAlgHom_apply, hR]⟩

end Proposition_2_13

section Proposition_2_16

open MvPolynomial Polynomial in
/-- **BPR Proposition 2.16.** Let `P ∈ K[X]` be monic of degree `k`, and let
    `x₁,…,xₖ` be its roots (with multiplicities) in a field extension `C ⊇ K`.
    If `Q(X₁,…,Xₖ) ∈ K[X₁,…,Xₖ]` is symmetric, then `Q(x₁,…,xₖ) ∈ K`.

    **Proof (BPR):** Let `eᵢ = Eᵢ(x₁,…,xₖ)`. Since the `eᵢ` are (up to sign)
    coefficients of `P` by Lemma 2.12, we have `eᵢ ∈ K`. By Proposition 2.13,
    `Q = R(E₁,…,Eₖ)` for some `R ∈ K[T₁,…,Tₖ]`. Thus
    `Q(x₁,…,xₖ) = R(e₁,…,eₖ) ∈ K`. -/
theorem proposition_2_16 {K C : Type*} [Field K] [Field C] [Algebra K C]
    {k : ℕ} (P : Polynomial K)
    (x : Fin k → C)
    (hx : P.map (algebraMap K C) = ∏ j : Fin k, (Polynomial.X - Polynomial.C (x j)))
    (Q : MvPolynomial (Fin k) K) (hQ : Q.IsSymmetric) :
    MvPolynomial.aeval x Q ∈ Set.range (algebraMap K C) := by
  -- Step 1: By Prop 2.13, Q = R(E₁,...,Eₖ) for some R ∈ K[T₁,...,Tₖ]
  obtain ⟨R, hR⟩ := proposition_2_13 Q hQ
  -- Step 2: Rewrite Q and compose the evaluations:
  --   aeval x Q = aeval x (aeval(esymm) R) = aeval(aeval x ∘ esymm) R
  rw [← hR]
  show (MvPolynomial.aeval x).comp
    (MvPolynomial.bind₁ (fun i : Fin k => MvPolynomial.esymm (Fin k) K (↑i + 1))) R ∈ _
  rw [MvPolynomial.aeval_comp_bind₁]
  -- Step 3: Each eᵢ ∈ K by Vieta. Extract preimages:
  --   aeval x (esymm K (i+1)) = algebraMap K C (eᵢ) for some eᵢ : K
  suffices h : ∀ i : Fin k, ∃ e : K,
      algebraMap K C e = MvPolynomial.aeval x (MvPolynomial.esymm (Fin k) K (↑i + 1)) by
    -- Choose the K-valued preimages
    choose e he using h
    -- Step 4: aeval(algebraMap K C ∘ e) R = algebraMap K C (eval e R)
    refine ⟨MvPolynomial.eval e R, ?_⟩
    have heq : (fun i : Fin k => MvPolynomial.aeval x (MvPolynomial.esymm (Fin k) K (↑i + 1))) =
        fun i => algebraMap K C (e i) := funext (fun i => (he i).symm)
    rw [heq]
    simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp, Function.comp_def]
  -- Step 3 proof: use Vieta to show each esymm eval is a coefficient of P
  intro i
  -- aeval x (esymm K (i+1)) = (univ.val.map x).esymm (i+1)
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  -- By Vieta (lemma_2_12 over C): the RHS is (-1)^(i+1) * coeff of ∏(X-C(xⱼ))
  have h2_12 := @lemma_2_12 C _ k x (i.val + 1) (by omega)
  -- From hx, comparing coefficients: coeff of ∏(X-C(xⱼ)) = algebraMap K C (P.coeff _)
  have hcoeff : (∏ j : Fin k, (Polynomial.X - Polynomial.C (x j))).coeff (k - (i.val + 1)) =
      algebraMap K C (P.coeff (k - (i.val + 1))) := by
    rw [← hx, Polynomial.coeff_map]
  rw [hcoeff] at h2_12
  -- h2_12 : algebraMap(coeff) = (-1)^(i+1) * esymm
  -- So esymm = (-1)^(i+1) · algebraMap(coeff), since (-1)^n · (-1)^n = 1
  refine ⟨(-1) ^ (i.val + 1) * P.coeff (k - (i.val + 1)), ?_⟩
  rw [map_mul, map_pow, map_neg, map_one, h2_12, ← mul_assoc,
      ← pow_add, ← Nat.two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end Proposition_2_16

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

The proof is split across five files, one per implication:
- `Theorem_2_11_a_b.lean`: (a) ⇒ (b)
- `Theorem_2_11_b_c.lean`: (b) ⇒ (c)
- `Theorem_2_11_b_d.lean`: (b) ⇒ (d)
- `Theorem_2_11_c_a.lean`: (c) ⇒ (a)
- `Theorem_2_11_d_a.lean`: (d) ⇒ (a)

The combined TFAE statement is in `Theorem_2_11.lean`.
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
