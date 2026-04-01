import Mathlib.Algebra.Polynomial.Derivative

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

end Azurite.BPR
