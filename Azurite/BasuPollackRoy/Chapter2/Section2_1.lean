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

### Derivative

The **derivative** P' of a polynomial P is defined in Mathlib as a linear map:

```
/-- `derivative p` is the formal derivative of the polynomial `p` -/
def Polynomial.derivative : R[X] →ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)
```

See: `Mathlib.Algebra.Polynomial.Derivative`

The **i-th derivative** P⁽ⁱ⁾ is obtained by iterating `derivative` using Lean's
general `Function.iterate`:

```
Polynomial.derivative^[i] P
```

This is not a separate Mathlib definition; it uses `Function.iterate` (from `Init`):

```
def Function.iterate (f : α → α) : ℕ → α → α
  | 0,     a => a
  | n + 1, a => f (iterate f n a)
```

### Key properties

**(P + Q)' = P' + Q'** — the derivative is additive. In Mathlib:

```
@[simp]
theorem Polynomial.derivative_add {R : Type u} [Semiring R] {f g : R[X]} :
    Polynomial.derivative (f + g) = Polynomial.derivative f + Polynomial.derivative g
```

Note: since `Polynomial.derivative` is a linear map (`R[X] →ₗ[R] R[X]`),
additivity also follows from `LinearMap.map_add`.

**(P · Q)' = P' · Q + P · Q'** — the Leibniz (product) rule. In Mathlib:

```
@[simp]
theorem Polynomial.derivative_mul {R : Type u} [Semiring R] {f g : R[X]} :
    Polynomial.derivative (f * g) =
      Polynomial.derivative f * g + f * Polynomial.derivative g
```

Both properties hold over any `Semiring`; no characteristic-zero assumption
is needed.

### Azurite Implementation

The derivative is also implemented natively on `AzPolynomial` as
`Azurite.AzPolynomial.derivative` (see `Azurite.AzPolynomial.Derivative`).
Its equivalence to `Polynomial.derivative` is proved in
`Azurite.AzPolynomial.Equiv.Derivative`:

- `toPoly_derivative : toPoly (derivative p) = Polynomial.derivative (toPoly p)`
- `ofPoly_derivative : ofPoly (Polynomial.derivative p) = derivative (ofPoly p)`
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-!
### Derivative API

Key Mathlib declarations for derivatives:
- `Polynomial.derivative` — `K[X] →ₗ[K] K[X]`
- `Polynomial.derivative_add` — `(P + Q)' = P' + Q'`
- `Polynomial.derivative_mul` — `(P · Q)' = P' · Q + P · Q'`
- `Polynomial.iterate_derivative_sum` — iterated derivative of a sum
- `Polynomial.iterate_derivative_mul` — general Leibniz rule
-/

/-!
### Proposition 2.1: Taylor's Formula

The **Hasse derivative** `hasseDeriv k P` is defined in Mathlib as
`∑ (i.choose k) · aᵢ · X^{i−k}`. It satisfies:

```
k! • (hasseDeriv k P) = derivative^[k] P
```

See: `Mathlib.Algebra.Polynomial.HasseDeriv` (`factorial_smul_hasseDeriv`)

Over a field of characteristic zero, this means the k-th Taylor
coefficient at x equals `P⁽ᵏ⁾(x) / k!`.

Mathlib's `Polynomial.taylor r P` computes `P(X + r)`, and
`sum_taylor_eq` gives the expansion:

```
((taylor r P).sum fun i a => C a * (X - C r) ^ i) = P
```

See: `Mathlib.Algebra.Polynomial.Taylor`
-/

/-- In a field of characteristic zero, the k-th Hasse derivative evaluated at x
    equals the k-th iterated derivative evaluated at x, divided by k!. -/
theorem hasseDeriv_eval_eq (P : K[X]) (x : K) (k : ℕ) :
    (hasseDeriv k P).eval x = (derivative^[k] P).eval x / (↑(Nat.factorial k) : K) := by
  have hk : (↑(Nat.factorial k) : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [eq_div_iff hk, mul_comm]
  have h := congr_fun (factorial_smul_hasseDeriv k) P
  simp only [LinearMap.smul_apply] at h
  rw [← h]
  simp [nsmul_eq_mul]

/-- **BPR Proposition 2.1 (Taylor's Formula).**
    Let K be a field of characteristic 0, P ∈ K[X], and x ∈ K. Then
    P = ∑_{i=0}^{deg P} (P⁽ⁱ⁾(x) / i!) · (X − x)ⁱ. -/
theorem prop_2_1 (P : K[X]) (x : K) :
    P = ∑ i ∈ Finset.range (P.natDegree + 1),
      C ((derivative^[i] P).eval x / (↑(Nat.factorial i) : K)) * (X - C x) ^ i := by
  -- Each Taylor coefficient equals derivative^[i]/i!
  have key : ∀ i, (taylor x P).coeff i =
      (derivative^[i] P).eval x / ↑(Nat.factorial i) :=
    fun i => by rw [taylor_coeff]; exact hasseDeriv_eval_eq P x i
  -- Rewrite sum_taylor_eq with the derivative characterization
  have h := sum_taylor_eq P x
  simp only [Polynomial.sum, key] at h
  -- Extend from support to range (natDegree + 1)
  have hsub : (taylor x P).support ⊆ Finset.range (P.natDegree + 1) := by
    intro i hi
    rw [← natDegree_taylor P x]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_mem_supp i hi))
  have h2 : ∑ i ∈ (taylor x P).support,
      C ((derivative^[i] P).eval x / ↑(Nat.factorial i)) * (X - C x) ^ i =
    ∑ i ∈ Finset.range (P.natDegree + 1),
      C ((derivative^[i] P).eval x / ↑(Nat.factorial i)) * (X - C x) ^ i :=
    Finset.sum_subset hsub (fun i _ hi => by
      have : (taylor x P).coeff i = 0 := notMem_support_iff.mp hi
      rw [key i] at this
      simp [this])
  exact h.symm.trans h2

/-!
### Root Multiplicity

**Definition 2.2** (BPR p.33). Let x ∈ K and P ∈ K[X]. The **multiplicity** of x
as a root of P is the natural number µ such that there exists Q ∈ K[X] with
P = (X − x)^µ · Q(X) and Q(x) ≠ 0. Note that if x is not a root of P, the
multiplicity of x as a root of P is equal to 0.

Mathlib already provides:

```
def Polynomial.rootMultiplicity (a : R) (p : R[X]) : ℕ
```

defined via `multiplicity (X - C a) p` (see `Mathlib.Algebra.Polynomial.Div`).

Key Mathlib theorems matching the BPR characterization:
- `Polynomial.pow_rootMultiplicity_dvd` — `(X - C a)^µ ∣ P`
- `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd` —
    `∃ Q, P = (X - C a)^µ * Q ∧ ¬(X - C a) ∣ Q`
- `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` —
    `eval a (P /ₘ (X - C a)^µ) ≠ 0`
-/

/-- **BPR Definition 2.2 (Root Multiplicity).**
    `IsRootMultiplicity x P μ` holds when there exists Q ∈ K[X] such that
    P = (X − x)^μ · Q and Q(x) ≠ 0. -/
def IsRootMultiplicity (x : K) (P : K[X]) (μ : ℕ) : Prop :=
  ∃ Q : K[X], P = (X - C x) ^ μ * Q ∧ Q.eval x ≠ 0

/-!
### Lemma 2.2: Derivative characterization of root multiplicity

**Lemma 2.2** (BPR p.33). Let K be a field of characteristic zero. The element
x ∈ K is a root of P ∈ K[X] of multiplicity μ if and only if
P^{(μ)}(x) ≠ 0 and P^{(μ−1)}(x) = ⋯ = P′(x) = P(x) = 0.

This is proved using two Mathlib lemmas from `Mathlib.Algebra.Polynomial.FieldDivision`:

- `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative` —
    `n < rootMultiplicity t P ↔ ∀ m ≤ n, (derivative^[m] P).IsRoot t`
- `Polynomial.eval_iterate_derivative_rootMultiplicity` —
    `eval t (derivative^[μ] P) = μ! • eval t (P /ₘ (X − C t)^μ)`
-/

/-- **BPR Lemma 2.2.** x is a root of P of multiplicity μ iff
    P(x) = P'(x) = ⋯ = P^{(μ−1)}(x) = 0 and P^{(μ)}(x) ≠ 0. -/
theorem lemma_2_2 (P : K[X]) (t : K) (hP : P ≠ 0) (μ : ℕ) :
    μ = rootMultiplicity t P ↔
      (∀ i < μ, (derivative^[i] P).IsRoot t) ∧
      ¬(derivative^[μ] P).IsRoot t := by
  constructor
  · -- forward: μ = rootMultiplicity → derivatives vanish below, nonzero at μ
    rintro rfl
    exact ⟨
      fun i hi => (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).mp (by omega) i le_rfl,
      by rw [Polynomial.IsRoot, Polynomial.eval_iterate_derivative_rootMultiplicity]
         exact smul_ne_zero_iff.mpr
           ⟨Nat.cast_ne_zero.mpr (rootMultiplicity t P).factorial_ne_zero,
            eval_divByMonic_pow_rootMultiplicity_ne_zero t hP⟩⟩
  · -- backward: conditions → μ = rootMultiplicity
    rintro ⟨hvanish, hnonzero⟩
    apply le_antisymm
    · -- μ ≤ rootMultiplicity: if not, derivative^[rootMultiplicity] vanishes, contradiction
      by_contra h; push_neg at h
      have hne : ¬(derivative^[rootMultiplicity t P] P).IsRoot t := by
        rw [Polynomial.IsRoot, Polynomial.eval_iterate_derivative_rootMultiplicity]
        exact smul_ne_zero_iff.mpr
          ⟨Nat.cast_ne_zero.mpr (rootMultiplicity t P).factorial_ne_zero,
           eval_divByMonic_pow_rootMultiplicity_ne_zero t hP⟩
      exact hne (hvanish _ h)
    · -- rootMultiplicity ≤ μ: if not, derivative^[μ] vanishes, contradiction
      by_contra h; push_neg at h
      exact hnonzero
        ((Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).mp h μ le_rfl)

/-!
### Separable and Square-free Polynomials

**Definition (BPR p.33).** A polynomial P ∈ K[X] is **separable** if the greatest
common divisor of P and P' is an element of K \ {0}.

In Mathlib this is `Polynomial.Separable`, defined as `IsCoprime P (derivative P)`
(see `Mathlib.FieldTheory.Separable`). Over a field, gcd(P, P') ∈ K \ {0} is
equivalent to coprimality.

**Definition (BPR p.33).** A polynomial P is **square-free** if there is no
non-constant polynomial A ∈ K[X] such that A² divides P.

In Mathlib this is `Squarefree`, defined as `∀ x, x * x ∣ r → IsUnit x`
(see `Mathlib.Algebra.Squarefree.Basic`). In K[X], `IsUnit` means constant
and nonzero, which matches "no non-constant A".

Key Mathlib results:
- `Polynomial.Separable.squarefree` — separable → square-free
- `Polynomial.separable_def` — `P.Separable ↔ IsCoprime P (derivative P)`
-/



/-!
### Exercise 2.1(a): Separable iff no multiple roots

**Exercise 2.1(a)** (BPR p.34). Prove that P ∈ K[X] is separable if and only if
P has no multiple root in C, where C is an algebraically closed field
containing K.

In Mathlib, "no multiple root" is expressed as `(P.aroots C).Nodup`.
The proof is a direct application of `Polynomial.nodup_aroots_iff_of_splits`,
using `IsAlgClosed.splits` to show that the mapped polynomial splits in C.
-/

variable {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

omit [CharZero K] in
/-- **BPR Exercise 2.1(a).** P is separable iff P has no multiple root
    in an algebraically closed field C containing K. -/
theorem exercise_2_1a (P : K[X]) (hP : P ≠ 0) :
    P.Separable ↔ (P.aroots C).Nodup :=
  (nodup_aroots_iff_of_splits hP (IsAlgClosed.splits (P.map (algebraMap K C)))).symm

/-!
### Exercise 2.1(b): Separable iff square-free (in characteristic 0)

**Exercise 2.1(b)** (BPR p.34). If the characteristic of K is 0, prove that
P ∈ K[X] is separable if and only if P is square-free.

This follows from `PerfectField.separable_iff_squarefree`
(see `Mathlib.FieldTheory.Perfect`), since every field of characteristic 0
is a perfect field.
-/

/-- **BPR Exercise 2.1(b).** In characteristic 0, P is separable iff P is square-free. -/
theorem exercise_2_1b (P : K[X]) :
    P.Separable ↔ Squarefree P :=
  PerfectField.separable_iff_squarefree

/-!
### Partially Ordered Sets

**Definition (BPR p.34).** A **partially ordered set** (poset) is a set S
equipped with a binary relation ≤ that is reflexive, antisymmetric, and
transitive.

In Mathlib this is the typeclass `PartialOrder`:

```
class PartialOrder (α : Type*) extends Preorder α where
  le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b
```

See: `Mathlib.Order.Basic`

**Example (BPR p.34).** If A is a set, then 2^A = {B | B ⊆ A} is a poset
under the inclusion relation. In Mathlib, `Set α` already carries a
`PartialOrder` instance where `≤` is definitionally `⊆`.
-/

variable {α : Type*}

/-- The powerset of A, ordered by inclusion, is a partial order.
    This is automatic in Mathlib: `Set α` has a `PartialOrder` instance
    where `≤` is `⊆`, so `Set.powerset A = {B | B ⊆ A}` inherits the order. -/
example (A B : Set α) : A ≤ B ↔ A ⊆ B := Iff.rfl

/-!
### Totally Ordered Sets and Ordered Rings

**Definition (BPR p.34).** A **totally ordered set** is a partially ordered set
(A, ≤) where every two elements a, b ∈ A are comparable: a ≤ b or b ≤ a.
In a totally ordered set, a < b stands for a ≤ b, a ≠ b, and a ≥ b (resp.
a > b) for b ≤ a (resp. b < a).

In Mathlib this is `LinearOrder` (see `Mathlib.Order.Defs.LinearOrder`).

**Definition (BPR p.34).** An **ordered ring** (A, ≤) is a ring A together with
a total order ≤ satisfying:
- x ≤ y ⇒ x + z ≤ y + z
- 0 ≤ x, 0 ≤ y ⇒ 0 ≤ xy

In Mathlib: `[Ring A] [LinearOrder A] [IsStrictOrderedRing A]`.

**Definition (BPR p.34).** An **ordered field** (F, ≤) is a field F which is an
ordered ring.

In Mathlib: `[Field F] [LinearOrder F] [IsStrictOrderedRing F]`.

**Definition (BPR p.34).** An ordered ring (A, ≤) is **contained in** an
ordered field (F, ≤) if A ⊂ F and the inclusion is order preserving.

In Mathlib this is modeled by `OrderRingHom` (notation `A →+*o F`),
an order-preserving ring homomorphism (see `Mathlib.Algebra.Order.Hom.Ring`).
-/

section OrderedStructures
variable (A : Type*) [Ring A] [LinearOrder A] [IsStrictOrderedRing A]

example (x y : A) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := mul_nonneg hx hy

variable (F : Type*) [Field F] [inst : LinearOrder F] [IsStrictOrderedRing F]

/-- **BPR Proposition (p.34).** An ordered ring is necessarily an integral domain.
    In Mathlib, `IsDomain` is automatically synthesized from `IsStrictOrderedRing`. -/
example : IsDomain A := inferInstance

end OrderedStructures

/-!
### Exercise 2.2: Properties of ordered fields

**Exercise 2.2** (BPR p.35).
1. In an ordered field, −1 < 0.
2. An ordered field has characteristic zero.
3. Law of trichotomy: for every a in the field, exactly one of a < 0, a = 0,
   a > 0 holds.
-/

section Exercise_2_2
variable (F : Type*) [Field F] [inst : LinearOrder F] [IsStrictOrderedRing F]

/-- **BPR Exercise 2.2(1).** In an ordered field, −1 < 0. -/
theorem exercise_2_2_neg_one_lt_zero : (-1 : F) < 0 := neg_one_lt_zero

/-- **BPR Exercise 2.2(2).** An ordered field has characteristic zero. -/
example : CharZero F := inferInstance

omit [IsStrictOrderedRing F] in
/-- **BPR Exercise 2.2(3).** Trichotomy: for every a, exactly one of
    a < 0, a = 0, 0 < a holds. -/
theorem exercise_2_2_trichotomy (a : F) : a < 0 ∨ a = 0 ∨ 0 < a :=
  lt_trichotomy a 0

end Exercise_2_2

/-!
### Notation 2.3: Sign and Absolute Value

**Notation 2.3** (BPR p.35). The **sign** of an element a in an ordered field
is defined by:
- sign(a) = 0  if a = 0
- sign(a) = 1  if a > 0
- sign(a) = −1 if a < 0

When a > 0 we say a is **positive**, and when a < 0 we say a is **negative**.

In Mathlib, `SignType.sign : α →o SignType` returns a value in the type
`SignType` (which has elements `0`, `1`, `−1`).
See `Mathlib.Data.Sign.Defs`.

The **absolute value** |a| of a is `max a (−a)` and is non-negative.
In Mathlib this is `abs : α → α` (notation `|a|`).
See `Mathlib.Algebra.Order.Group.Abs`.
-/

section SignAndAbs
variable {F : Type*} [Field F] [inst : LinearOrder F] [IsStrictOrderedRing F]

example : ∀ a : F, |a| = max a (-a) := fun _ => abs_eq_max_neg
example : ∀ a : F, 0 ≤ |a| := abs_nonneg

end SignAndAbs

/-!
### Examples of Ordered Fields

**Example (BPR p.34).** The fields ℚ and ℝ with their natural order are
ordered fields.

In Mathlib, both `ℚ` and `ℝ` already carry instances for `Field`,
`LinearOrder`, and `IsStrictOrderedRing`.
-/

-- ℚ is an ordered field
example : Field ℚ := inferInstance
example : LinearOrder ℚ := inferInstance
example : IsStrictOrderedRing ℚ := inferInstance

-- ℝ is an ordered field
noncomputable example : Field ℝ := inferInstance
noncomputable example : LinearOrder ℝ := inferInstance
noncomputable example : IsStrictOrderedRing ℝ := inferInstance

/-!
### Exercise 2.3: ℂ cannot be ordered

**Exercise 2.3** (BPR p.35). Show that it is not possible to order the field
of complex numbers ℂ so that it becomes an ordered field.

*Proof.* In any ordered field, x² ≥ 0 for all x. But i² = −1, so we would
need 0 ≤ −1, contradicting −1 < 0.
-/

open Complex in
/-- **BPR Exercise 2.3.** ℂ cannot be made into an ordered field. -/
theorem exercise_2_3 :
    ¬ ∃ (_ : LinearOrder ℂ), IsStrictOrderedRing ℂ := by
  rintro ⟨ord, hord⟩
  letI := ord; letI := hord
  have hsq : 0 ≤ I * I := mul_self_nonneg I
  rw [I_mul_I] at hsq
  exact not_le.mpr neg_one_lt_zero hsq

/-!
### Proposition 2.4: Sign of polynomial for large |x|

**Proposition 2.4** (BPR p.35). Let P = aₚ X^p + … + a₀, aₚ ≠ 0, be a polynomial
with coefficients in an ordered field F. If

  |x| > 2 ∑ᵢ≤ₚ |aᵢ/aₚ|,

then P(x) and aₚ·x^p have the same sign.

*Proof sketch.* Write P(x) = L + R where L = aₚ·x^p is the leading term and
R = ∑ᵢ<ₚ aᵢ·x^i is the remainder. Show |R| < |L| using the hypothesis,
which implies sign(P(x)) = sign(L).
-/

section Prop_2_4

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- If |a − b| < |b| and b ≠ 0, then sign(a) = sign(b). -/
private lemma sign_eq_of_abs_sub_lt {a b : F} (hb : b ≠ 0) (h : |a - b| < |b|) :
    SignType.sign a = SignType.sign b := by
  rcases lt_or_gt_of_ne hb with hbn | hbp
  · have : a < 0 := by
      linarith [abs_of_neg hbn, (abs_sub_lt_iff.mp h).1, (abs_sub_lt_iff.mp h).2]
    rw [sign_neg hbn, sign_neg this]
  · have : 0 < a := by
      linarith [abs_of_pos hbp, (abs_sub_lt_iff.mp h).1, (abs_sub_lt_iff.mp h).2]
    rw [sign_pos hbp, sign_pos this]

/-- The tail of P (everything except the leading term) evaluated at x. -/
private lemma eval_sub_lead (P : F[X]) (x : F) :
    P.eval x - P.leadingCoeff * x ^ P.natDegree =
    ∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i := by
  have h : P.eval x = (∑ i ∈ Finset.range P.natDegree, P.coeff i * x ^ i)
      + P.coeff P.natDegree * x ^ P.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
  unfold leadingCoeff
  linarith

/-- **BPR Proposition 2.4.** If |x| > 2 ∑ᵢ≤ₚ |aᵢ/aₚ|, then P(x) and
    aₚ·x^p have the same sign. -/
theorem prop_2_4 (P : F[X]) (hP : P ≠ 0) (x : F)
    (hx : 2 * ∑ i ∈ Finset.range (P.natDegree + 1),
      |P.coeff i / P.leadingCoeff| < |x|) :
    SignType.sign (P.eval x) =
    SignType.sign (P.leadingCoeff * x ^ P.natDegree) := by
  set p := P.natDegree with hp_def
  set ap := P.leadingCoeff with hap_def
  set L := ap * x ^ p with hL_def
  have hap_ne : ap ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hx_pos : 0 < |x| := by
    have h1 : (0 : F) ≤ 2 * ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| := by positivity
    linarith
  have hx_ne : x ≠ 0 := fun h => by simp [h] at hx_pos
  have hL_ne : L ≠ 0 := mul_ne_zero hap_ne (pow_ne_zero _ hx_ne)
  -- Apply sign_eq_of_abs_sub_lt: suffices |P.eval x - L| < |L|
  apply sign_eq_of_abs_sub_lt hL_ne
  -- Rewrite the difference as the tail sum
  rw [eval_sub_lead]
  -- Split on p = 0 (trivial) vs p ≥ 1
  by_cases hp : p = 0
  · -- Constant polynomial: tail sum is empty, |0| < |L|
    rw [show P.natDegree = 0 from hp ▸ hp_def.symm]
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    exact abs_pos.mpr hL_ne
  · -- Degree p ≥ 1
    have hp_pos : 0 < p := Nat.pos_of_ne_zero hp
    have h1le : 1 ≤ |x| := by
      have h_ap_term : |P.coeff p / ap| = 1 := by
        rw [show P.coeff p = ap from rfl, div_self hap_ne, abs_one]
      have h_sum_ge : 1 ≤ ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| := by
        calc (1:F) = |P.coeff p / ap| := h_ap_term.symm
          _ ≤ ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| :=
              Finset.single_le_sum (fun i _ => abs_nonneg (P.coeff i / ap))
                (show p ∈ Finset.range (p + 1) by simp)
      linarith [mul_le_mul_of_nonneg_left h_sum_ge (by positivity : (0:F) ≤ 2)]
    have hsum_lt : ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap| < |x| / 2 := by
      rw [lt_div_iff₀ (two_pos (α := F))]; linarith
    -- Main inequality chain
    calc |∑ i ∈ Finset.range p, P.coeff i * x ^ i|
        ≤ ∑ i ∈ Finset.range p, |P.coeff i * x ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range p, |P.coeff i| * |x| ^ i := by
          congr 1; ext i; rw [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ Finset.range p, |P.coeff i| * |x| ^ (p - 1) := by
          apply Finset.sum_le_sum; intro i hi
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ h1le (Nat.le_pred_of_lt (Finset.mem_range.mp hi)))
            (abs_nonneg _)
      _ = (∑ i ∈ Finset.range p, |P.coeff i|) * |x| ^ (p - 1) :=
          (Finset.sum_mul ..).symm
      _ ≤ (∑ i ∈ Finset.range (p + 1), |P.coeff i|) * |x| ^ (p - 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (by omega)) (fun i _ _ => abs_nonneg _)
      _ = (|ap| * ∑ i ∈ Finset.range (p + 1), |P.coeff i / ap|) * |x| ^ (p - 1) := by
          congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
          rw [abs_div]; exact (mul_div_cancel₀ _ (abs_ne_zero.mpr hap_ne)).symm
      _ < (|ap| * (|x| / 2)) * |x| ^ (p - 1) := by
          apply mul_lt_mul_of_pos_right _ (pow_pos hx_pos _)
          exact mul_lt_mul_of_pos_left hsum_lt (abs_pos.mpr hap_ne)
      _ = |ap| * (|x| ^ (p - 1) * |x|) / 2 := by ring
      _ = |ap| * |x| ^ p / 2 := by
          congr 2; rw [← pow_succ]; congr 1; omega
      _ < |ap| * |x| ^ p := by
          linarith [mul_pos (abs_pos.mpr hap_ne) (pow_pos hx_pos p)]
      _ = |L| := by rw [abs_mul, abs_pow]

end Prop_2_4

/-!
### Infinitesimal and Unbounded Elements

**Definition (BPR p.35).** Let F ⊂ F′ be two ordered fields (with `Algebra F F'`
providing the canonical embedding `algebraMap F F'`).

- The element x ∈ F′ is *infinitesimal over F* if its absolute value is
  positive and smaller than any positive element of F.
- The element x ∈ F′ is *unbounded over F* if its absolute value is
  greater than any positive element of F.

Mathlib has specific versions of these for the hyperreals (`Hyperreal.Infinitesimal`
and `Hyperreal.Infinite` in `Mathlib.Analysis.Real.Hyperreal`). The definitions
below generalize to any ordered field extension.
-/

section InfinitesimalUnbounded

variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {F' : Type*} [Field F'] [LinearOrder F'] [IsStrictOrderedRing F']
variable [Algebra F F']

/-- **BPR Definition (Infinitesimal).** An element x ∈ F′ is *infinitesimal
    over F* if x ≠ 0 and |x| < ι(a) for every positive a ∈ F,
    where ι = algebraMap F F′. -/
def IsInfinitesimalOver (x : F') : Prop :=
  x ≠ 0 ∧ ∀ a : F, 0 < a → |x| < algebraMap F F' a

/-- **BPR Definition (Unbounded).** An element x ∈ F′ is *unbounded
    over F* if ι(a) < |x| for every positive a ∈ F,
    where ι = algebraMap F F′. -/
def IsUnboundedOver (x : F') : Prop :=
  ∀ a : F, 0 < a → algebraMap F F' a < |x|

end InfinitesimalUnbounded

/-!
### Notation 2.5: The 0₊ Order

The 0₊ order on F(ε) is constructed in
`Azurite.BasuPollackRoy.Chapter2.OrderZeroPlus`, which provides:

* A `LinearOrder` on `F[X]` where P > 0 iff the trailing coefficient
  (lowest nonzero term) is positive.
* An `IsStrictOrderedRing` instance making `F[X]` an ordered ring.
* Notation `ε` for the indeterminate `X`.
* A proof that `ε` is infinitesimal over `F` (i.e., `0 < ε < C a`
  for every positive `a ∈ F`).
* A `LinearOrder` on `RatFunc F` (= F(ε)) where `P/Q > 0 ↔ PQ > 0`,
  extending the polynomial order to the full rational function field.
* `rfPos_div`: bridge lemma connecting `rfPos` on canonical `num/denom`
  to `polyPos` on arbitrary representative pairs.
* `εR_inv_gt_ιR`: `1/ε` is greater than every element of `F` embedded
  in `RatFunc F`, i.e., `∀ a : F, ιR a < εR_inv`. This is stronger
  than BPR's statement and implies that `1/ε` is unbounded over `F`
  in the sense of `IsUnboundedOver` above.
-/

/-!
### Exercise 2.4: Uniqueness of the 0₊ order

**Exercise 2.4 (BPR).** Show that 0₊ is the only order on F[X] in which ε
is positive infinitesimal over F.

We formalize this as: any positivity predicate `pos` on `F[X]` satisfying
the ordered-ring axioms + "X is positive infinitesimal" must agree with
`polyPos` (the 0₊ positivity predicate).
-/

end Azurite.BPR

section Exercise_2_4

open Polynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Exercise 2.4.** The 0₊ order is the unique order on F[X] making ε
    positive infinitesimal: any positivity predicate satisfying the
    ordered-ring axioms with X infinitesimal agrees with `polyPos`. -/
theorem Azurite.BPR.exercise_2_4
    (pos : F[X] → Prop)
    (pos_add : ∀ {a b}, pos a → pos b → pos (a + b))
    (pos_mul : ∀ {a b}, pos a → pos b → pos (a * b))
    (pos_tri : ∀ a, pos a ∨ a = 0 ∨ pos (-a))
    (pos_antisymm : ∀ {a}, pos a → ¬ pos (-a))
    (hC : ∀ {a : F}, 0 < a → pos (C a))
    (hε_pos : pos X)
    (hε_inf : ∀ {a : F}, 0 < a → pos (C a - X))
    (P : F[X]) (hP : P ≠ 0) :
    pos P ↔ 0 < P.trailingCoeff := by
  -- Helper facts
  have not_pos_zero : ¬ pos 0 := fun h => pos_antisymm h (by rwa [neg_zero])
  have pos_C_iff : ∀ {a : F}, a ≠ 0 → (pos (C a) ↔ 0 < a) := by
    intro a ha
    exact ⟨fun h => by
      by_contra hle; push_neg at hle
      exact pos_antisymm h (by rw [← map_neg]; exact hC (neg_pos.mpr (lt_of_le_of_ne hle ha))),
      fun h => hC h⟩
  -- X^k > 0 for k ≥ 1
  have pos_X_pow : ∀ k, 1 ≤ k → pos (X ^ k : F[X]) := by
    intro k hk; induction k with
    | zero => omega
    | succ n ih => cases n with
      | zero => simpa
      | succ m => rw [pow_succ]; exact pos_mul (ih (by omega)) hε_pos
  -- X^k < C(a) for k ≥ 1 and a > 0
  have pos_C_sub_X_pow : ∀ k, 1 ≤ k → ∀ {a : F}, 0 < a → pos (C a - X ^ k : F[X]) := by
    intro k hk; induction k with
    | zero => omega
    | succ n ih => intro a ha; cases n with
      | zero => simpa using hε_inf ha
      | succ m =>
        rw [show C a - X ^ (m + 2) =
            (C a - X ^ (m + 1)) + (X ^ (m + 1) * (C (1 : F) - X)) from by
          rw [map_one]; ring]
        exact pos_add (ih (by omega) ha)
          (pos_mul (pos_X_pow _ (by omega)) (by rw [map_one]; exact hε_inf one_pos))
  -- pos(a) → pos(a*b) ↔ pos(b)
  have pos_cancel : ∀ {a b : F[X]}, pos a → (pos (a * b) ↔ pos b) := by
    intro a b ha
    constructor
    · intro hab
      rcases pos_tri b with hb | hb | hb
      · exact hb
      · exact absurd (by rw [hb, mul_zero] at hab; exact hab) not_pos_zero
      · have : pos (a * (-b)) := pos_mul ha hb
        rw [mul_neg] at this
        exact absurd this (pos_antisymm hab)
    · exact fun hb => pos_mul ha hb
  -- KEY LEMMA: X * Q is bounded by any positive constant
  have mul_X_bounded : ∀ Q : F[X], ∀ {a : F}, 0 < a → pos (C a - X * Q) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p q ihp ihq =>
      intro a ha
      have hsplit : C a - X * (p + q) = (C (a / 2) - X * p) + (C (a / 2) - X * q) := by
        have : C a = C (a / 2) + C (a / 2) := by rw [← map_add]; congr 1; field_simp; ring
        rw [this]; ring
      rw [hsplit]
      exact pos_add (ihp (half_pos ha)) (ihq (half_pos ha))
    | monomial n c =>
      intro a ha
      have hmon : X * monomial n c = C c * X ^ (n + 1) := by
        rw [← C_mul_X_pow_eq_monomial]; ring
      rw [hmon]
      by_cases hc : c = 0
      · simp [hc]; exact hC ha
      · rcases pos_tri (C c * X ^ (n + 1) : F[X]) with h | h | h
        · -- term > 0: show it's < C(a) via X^(n+1) < C(a/c)
          have hc_pos : (0 : F) < c := by
            rw [show C c * X ^ (n + 1) = X ^ (n + 1) * C c from mul_comm ..] at h
            rwa [pos_cancel (pos_X_pow _ (Nat.one_le_iff_ne_zero.mpr (by omega))),
                 pos_C_iff hc] at h
          rw [show C a - C c * X ^ (n + 1) = C c * (C (a / c) - X ^ (n + 1)) from by
            rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hc]]
          exact pos_mul (hC hc_pos) (pos_C_sub_X_pow _
            (Nat.one_le_iff_ne_zero.mpr (by omega)) (div_pos ha hc_pos))
        · -- term = 0: trivial
          rw [show C a - C c * X ^ (n + 1) = C a + -(C c * X ^ (n + 1)) from sub_eq_add_neg ..,
              h, neg_zero, add_zero]
          exact hC ha
        · -- term < 0: C(a) - term = C(a) + |term| > 0
          rw [show C a - C c * X ^ (n + 1) = C a + -(C c * X ^ (n + 1)) from sub_eq_add_neg ..]
          exact pos_add (hC ha) h
  -- MAIN PROOF
  -- Step 1: Factor P = X^m * Q where m = natTrailingDegree P
  have hdvd : X ^ P.natTrailingDegree ∣ P :=
    X_pow_dvd_iff.mpr (fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd)
  obtain ⟨Q, hQ⟩ := hdvd
  have hQne : Q ≠ 0 := right_ne_zero_of_mul (hQ ▸ hP)
  -- Q.coeff 0 = trailingCoeff P ≠ 0
  have hcm : (X ^ P.natTrailingDegree * Q).coeff P.natTrailingDegree = Q.coeff 0 := by
    have := coeff_X_pow_mul Q P.natTrailingDegree 0; simp at this; exact this
  have hQ0 : Q.coeff 0 = P.trailingCoeff := by
    rw [trailingCoeff]; rw [← hcm]
    congr 1; exact hQ.symm
  have hQ0ne : Q.coeff 0 ≠ 0 := hQ0 ▸ trailingCoeff_nonzero_iff_nonzero.mpr hP
  -- Step 2: pos P ↔ pos Q
  have hfactor : pos P ↔ pos Q := by
    rw [hQ]
    rcases Nat.eq_zero_or_pos P.natTrailingDegree with hm | hm
    · rw [hm]; simp
    · exact pos_cancel (pos_X_pow _ hm)
  -- Step 3: Q = C(Q.coeff 0) + X * Q.divX
  have hQeq : Q = C (Q.coeff 0) + X * Q.divX := by
    ext n; cases n with
    | zero => simp [coeff_divX]
    | succ k => simp [coeff_divX, coeff_X_mul]
  -- Helper for splitting C(a) = C(a/2) + C(a/2)
  have half_split : ∀ (a : F) (S : F[X]),
      C a - X * S = C (a / 2) + (C (a / 2) - X * S) := by
    intro a S
    have : C a = C (a / 2) + C (a / 2) := by rw [← map_add]; congr 1; field_simp; ring
    rw [show C a - X * S = C a + (-X * S) from by ring,
        this, show C (a / 2) + C (a / 2) + -X * S = C (a / 2) + (C (a / 2) - X * S) from by ring]
  -- Step 4: pos Q ↔ 0 < Q.coeff 0
  have hQ_iff : pos Q ↔ 0 < Q.coeff 0 := by
    constructor
    · intro hposQ
      rcases lt_trichotomy (Q.coeff 0) 0 with hlt | heq | hgt
      · exfalso
        have hneg : pos (-Q) := by
          rw [hQeq, show -(C (Q.coeff 0) + X * Q.divX) = C (-(Q.coeff 0)) - X * Q.divX
            from by rw [map_neg]; ring, half_split]
          exact pos_add (hC (by linarith)) (mul_X_bounded _ (by linarith))
        exact pos_antisymm hposQ hneg
      · exact absurd heq.symm (Ne.symm hQ0ne)
      · exact hgt
    · intro hbpos
      rw [hQeq, show C (Q.coeff 0) + X * Q.divX = C (Q.coeff 0) - X * (-Q.divX) from by ring,
          half_split]
      exact pos_add (hC (by linarith)) (mul_X_bounded _ (by linarith))
  rw [hfactor, hQ_iff, hQ0]

end Exercise_2_4

namespace Azurite.BPR

/-!
### Cones (BPR Definition 2.6)

**Definition.** A *cone* of a field `F` is a subset `C ⊆ F` satisfying:
1. `x ∈ C, y ∈ C ⇒ x + y ∈ C`
2. `x ∈ C, y ∈ C ⇒ x · y ∈ C`
3. `x ∈ F ⇒ x² ∈ C`

The cone `C` is *proper* if in addition `−1 ∉ C`.

**Mathlib correspondence.**
- BPR's "cone" is a `Subsemiring` that contains all squares.
  We define `IsCone` below as this predicate on a `Subsemiring`.
- BPR's "proper cone" is exactly Mathlib's `RingPreordering`
  (from `Mathlib.Algebra.Order.Ring.Ordering.Basic`):
  a `Subsemiring` containing all squares with `−1 ∉ C`.
- Mathlib's `RingCone` is *stronger* than a proper cone: it
  additionally requires `a ∈ C ∧ −a ∈ C → a = 0`, which
  corresponds to the cone inducing a *total* order.
- The *positive cone* `{x ∈ F | x ≥ 0}` of an ordered field is
  `RingCone.nonneg` from `Mathlib.Algebra.Order.Ring.Cone`.
-/

section Cones

variable {F : Type*} [CommRing F]

/-- **BPR Definition 2.6 (Cone).** A *cone* of a commutative ring `F` is a
    `Subsemiring` that contains all squares.
    This is weaker than Mathlib's `RingPreordering`, which additionally
    requires `−1 ∉ C`. -/
def IsCone (C : Subsemiring F) : Prop :=
  ∀ x : F, x ^ 2 ∈ C

/-- A cone is *proper* iff `−1 ∉ C`. A proper `IsCone` is exactly a
    `RingPreordering`. -/
def IsProperCone (C : Subsemiring F) : Prop :=
  IsCone C ∧ (-1 : F) ∉ C

/-- Every `RingPreordering` is a proper cone. -/
lemma RingPreordering.isProperCone (P : RingPreordering F) :
    IsProperCone P.toSubsemiring :=
  ⟨fun x => by
    have : IsSquare (x ^ 2) := ⟨x, sq x⟩
    exact P.mem_of_isSquare this,
   P.neg_one_notMem⟩

/-- A proper cone gives rise to a `RingPreordering`. -/
def IsProperCone.toRingPreordering {C : Subsemiring F} (hC : IsProperCone C) :
    RingPreordering F :=
  RingPreordering.mk' (↑C)
    (fun hx hy => C.add_mem hx hy)
    (fun hx hy => C.mul_mem hx hy)
    (fun x => by have := hC.1 x; rwa [sq] at this)
    hC.2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **BPR Remark.** The positive cone `{x ∈ F | x ≥ 0}` of an ordered field
    is a cone. This is `Subsemiring.nonneg` in Mathlib. -/
lemma isCone_nonneg : IsCone (Subsemiring.nonneg F) :=
  fun x => by simp [Subsemiring.mem_nonneg]; positivity

/-- The positive cone of an ordered field is proper. -/
lemma isProperCone_nonneg : IsProperCone (Subsemiring.nonneg F) :=
  ⟨isCone_nonneg, by simp [Subsemiring.mem_nonneg]⟩

/-!
### Proposition 2.6

**Proposition 2.6 (BPR).** Let (F, ≤) be an ordered field. The positive cone
C = { x ∈ F | x ≥ 0 } is a proper cone satisfying C ∪ (−C) = F. Conversely,
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
def IsRealField : Prop := IsSemireal F

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
  push_neg
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
`C[a] = { x + a·y | x, y ∈ C }` is a proper cone of `F`.
-/

section Lemma_2_9

variable {F : Type*} [Field F]

/-- The extension `C[a]`: the set `{ x + a·y | x, y ∈ C }`. -/
def coneExt (C : Subsemiring F) (hCone : IsCone C) (a : F) : Subsemiring F where
  carrier := { z | ∃ x ∈ C, ∃ y ∈ C, z = x + a * y }
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
  push_neg at hboth
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
private lemma isSumSq_exists_vector {s : F} (h : IsSumSq s) :
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
      ∀ (n : ℕ) (x : Fin n → F), (∑ i, x i ^ 2 = 0) → ∀ k, x k = 0 ] := by
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
  · by_contra h; push_neg at h
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

end Azurite.BPR
