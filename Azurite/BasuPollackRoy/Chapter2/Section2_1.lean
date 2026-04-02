import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Sign.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree

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
-/

end Azurite.BPR
