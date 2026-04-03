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

end Cones

end Azurite.BPR
