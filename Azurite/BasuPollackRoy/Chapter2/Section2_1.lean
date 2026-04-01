import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Perfect

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
### Derivative examples

We provide `#check` references to confirm that the Mathlib API is
available and demonstrate standard usage.
-/

-- P' — the derivative of P
#check @Polynomial.derivative K _
-- Type: K[X] →ₗ[K] K[X]

-- P⁽ⁱ⁾ — the i-th derivative of P
noncomputable example (P : K[X]) (i : ℕ) : K[X] := Polynomial.derivative^[i] P

-- (P + Q)' = P' + Q'
#check @Polynomial.derivative_add K _
-- derivative (f + g) = derivative f + derivative g

-- (P · Q)' = P' · Q + P · Q'
#check @Polynomial.derivative_mul K _
-- derivative (f * g) = derivative f * g + f * derivative g

-- Iterated derivative of a sum
#check @Polynomial.iterate_derivative_sum K _ _

-- General Leibniz rule for iterated derivatives
#check @Polynomial.iterate_derivative_mul K _

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

#check @rootMultiplicity K _
-- rootMultiplicity : K → K[X] → ℕ

#check @pow_rootMultiplicity_dvd K _
-- (X - C a) ^ rootMultiplicity a p ∣ p

#check @exists_eq_pow_rootMultiplicity_mul_and_not_dvd K _
-- ∃ q, p = (X - C a) ^ rootMultiplicity a p * q ∧ ¬(X - C a) ∣ q

#check @eval_divByMonic_pow_rootMultiplicity_ne_zero K _
-- eval a (p /ₘ (X - C a) ^ rootMultiplicity a p) ≠ 0

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

-- Separable: IsCoprime P (derivative P)
#check @Polynomial.Separable K _

-- Unfolded: P.Separable ↔ IsCoprime P (derivative P)
#check @Polynomial.separable_def K _

-- Square-free: ∀ A, A * A ∣ P → IsUnit A
#check @Squarefree K[X] _

-- Separable → square-free
#check @Polynomial.Separable.squarefree K _

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

end Azurite.BPR
