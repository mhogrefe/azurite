import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs

/-!
# BPR §8.1: Algebraic computation structures

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, pp. 281–284.

BPR defines a hierarchy of **algebraic computation structures** used to
state complexity results throughout the book. Each structure specifies
the set of **primitive operations** (unit-cost steps) available to
algorithms.

We do not formalize complexity measurements here, since Lean does not
currently provide a clean way to connect such measures to actual
algorithm implementations. Instead, we document and cross-reference the
seven algebraic structures defined in BPR §8.1 with their Lean 4 / Mathlib
counterparts.

### BPR Structure Hierarchy (§8.1)

1. **Ring structure (D₀)**: addition, subtraction, multiplication, and
   zero-testing in a commutative ring.
2. **Ordered ring structure**: D₀ operations plus total order comparison.
3. **Ring with integer division (D₁)**: D₀ operations plus exact division
   by nonzero integers, in a ring where `n · 1 ≠ 0` for all `n ∈ ℤ \ {0}`.
4. **Integral domain structure**: D₀ operations plus exact division by
   nonzero elements of the domain (when the result is known to belong to
   the domain).
5. **Field structure**: D₀ operations plus division by any nonzero element.
6. **Ordered integral domain structure**: integral domain + total order.
7. **Ordered field structure**: field + total order.
-/

namespace Azurite.BPR

/-!
## 1. Ring structure (D₀)

BPR's "ring structure" on a ring D provides the following unit-cost
operations:
- Addition:        `a + b`
- Subtraction:     `a - b`
- Multiplication:  `a * b`
- Zero testing:    decide whether `a = 0`

In Lean / Mathlib this corresponds to:

```
class CommRing (R : Type u) extends Ring R, CommMonoid R
```

See: `Mathlib.Algebra.Ring.Defs`

The zero-testing operation requires `DecidableEq R` (which gives us
`Decidable (a = 0)` for free).

Combined Lean typeclass bundle: `[CommRing R] [DecidableEq R]`
-/

-- BPR's "ring structure" is captured by:
-- [CommRing R] [DecidableEq R]
-- No new definition needed.

/-!
## 2. Ordered ring structure

BPR's "ordered ring structure" extends the ring structure with a total
order: given `a, b` in the ring, we can decide whether `a = b`,
`a > b`, or `a < b`.

In current Mathlib (post-deprecation of `LinearOrderedCommRing`), the
recommended formulation is:

```
[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
```

Where:
- `LinearOrder R` provides a decidable total order (`DecidableLE`,
  `DecidableLT`, `DecidableEq`).
- `IsStrictOrderedRing R` ties the ring and order structures together:
  multiplication by positive elements preserves strict inequalities,
  the order is compatible with addition, `0 ≤ 1`, etc.

See: `Mathlib.Algebra.Order.Ring.Defs`

Note: `LinearOrder` already provides `DecidableEq`, so the
`DecidableEq R` from the ring structure is subsumed.
-/

-- BPR's "ordered ring structure" is captured by:
-- [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
-- No new definition needed.

/-!
## 3. Ring with integer division (D₁)

BPR defines D₁ as a ring where, in addition to the D₀ operations:
- **Exact integer division**: for `n ∈ ℤ` and `a ∈ R`, if it is known
  that `a / n ∈ R` (i.e. `n` divides `a` in R), then performing the
  division is a unit-cost operation.
- **Characteristic zero**: `n · 1 ≠ 0` for all `n ∈ ℤ`, `n ≠ 0`.

The characteristic-zero condition is captured by Mathlib's `CharZero`:

```
class CharZero (R : Type u) [AddMonoidWithOne R] : Prop where
  cast_injective : Function.Injective (Nat.cast : ℕ → R)
```

See: `Mathlib.Algebra.CharZero.Defs`

For a `CommRing R` with `CharZero R`, the condition `n · 1 ≠ 0` for
nonzero `n ∈ ℤ` follows automatically.

The "exact division by an integer" operation itself has no standard
Mathlib typeclass, since it is a partial operation (only defined when
the integer divides the element). We define a class `HasIntDiv` to
capture this.
-/

/-- BPR's ring with integer division (D₁): a commutative ring of
    characteristic zero equipped with a partial division-by-integer
    operation.

    `intDiv a n h` computes `a / n` in `R`, given a proof `h` that
    `(n : R) * intDiv a n h = a`. -/
class HasIntDiv (R : Type*) [CommRing R] [CharZero R] where
  /-- Exact division of `a : R` by a nonzero integer `n : ℤ`, valid when
      the result is known to belong to `R`. -/
  intDiv : R → (n : ℤ) → n ≠ 0 → R
  /-- The division is exact: `n * intDiv a n h = a`. -/
  intDiv_spec : ∀ (a : R) (n : ℤ) (hn : n ≠ 0),
    (n : R) * intDiv a n hn = a

-- BPR's "ring with integer division" (D₁) is captured by:
-- [CommRing R] [CharZero R] [DecidableEq R] [HasIntDiv R]

/-!
## 4. Integral domain structure

BPR's "integral domain structure" extends the ring structure with exact
division by any nonzero element of the domain (when the result is known
to belong to the domain).

An integral domain in Mathlib is a `CommRing` satisfying `IsDomain`:

```
class IsDomain (α : Type u) [Semiring α] extends NoZeroDivisors α, Nontrivial α : Prop
```

See: `Mathlib.Algebra.Ring.Defs`

The "exact division" operation (dividing `a` by a nonzero `b` when `b ∣ a`
in the domain) has no standard Mathlib typeclass. We define `HasExactDiv`
to capture it.
-/

/-- BPR's exact-division operation for integral domains: given `a, b : R`
    with `b ≠ 0` and `b ∣ a`, compute the unique `q` such that `b * q = a`. -/
class HasExactDiv (R : Type*) [CommRing R] [IsDomain R] where
  /-- Exact division of `a` by a nonzero `b`, valid when `b ∣ a`. -/
  exactDiv : R → (b : R) → b ≠ 0 → R
  /-- The division is exact: `b * exactDiv a b hb = a` when `b ∣ a`. -/
  exactDiv_spec : ∀ (a b : R) (hb : b ≠ 0) (_ : b ∣ a),
    b * exactDiv a b hb = a

-- BPR's "integral domain structure" is captured by:
-- [CommRing R] [IsDomain R] [DecidableEq R] [HasExactDiv R]

/-!
## 5. Field structure

BPR's "field structure" extends the ring structure with division by any
nonzero element (not just when the result is known to lie in the ring,
since in a field it always does).

In Lean / Mathlib:

```
class Field (K : Type u) extends CommRing K, DivisionRing K
```

See: `Mathlib.Algebra.Field.Defs`

Fields already support `a / b` for any `b ≠ 0`, so no additional
division typeclass is needed.
-/

-- BPR's "field structure" is captured by:
-- [Field K] [DecidableEq K]
-- No new definition needed.

/-!
## 6. Ordered integral domain structure

BPR's "ordered integral domain structure" extends the integral domain
structure with a total order comparison (decide `a = b`, `a > b`, or
`a < b`).

In Lean / Mathlib this combines:
- `CommRing R` with `IsDomain R` (integral domain)
- `LinearOrder R` with `IsStrictOrderedRing R` (compatible total order)
-/

-- BPR's "ordered integral domain structure" is captured by:
-- [CommRing R] [IsDomain R] [LinearOrder R] [IsStrictOrderedRing R]
--   [HasExactDiv R]
-- No new definition needed.

/-!
## 7. Ordered field structure

BPR's "ordered field structure" extends the field structure with a
total order comparison.

In Lean / Mathlib this combines:
- `Field K` (field operations including division)
- `LinearOrder K` with `IsStrictOrderedRing K` (compatible total order)
-/

-- BPR's "ordered field structure" is captured by:
-- [Field K] [LinearOrder K] [IsStrictOrderedRing K]
-- No new definition needed.

/-!
## Summary table

| BPR name                   | Lean typeclasses                                                   |
|----------------------------|--------------------------------------------------------------------|
| Ring (D₀)                  | `[CommRing R] [DecidableEq R]`                                    |
| Ordered ring               | `[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]`            |
| Ring with int. div. (D₁)   | `[CommRing R] [CharZero R] [DecidableEq R] [HasIntDiv R]`         |
| Integral domain            | `[CommRing R] [IsDomain R] [DecidableEq R] [HasExactDiv R]`       |
| Field                      | `[Field K] [DecidableEq K]`                                       |
| Ordered integral domain    | `[CommRing R] [IsDomain R] [LinearOrder R] [IsStrictOrderedRing R]` `[HasExactDiv R]` |
| Ordered field              | `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`               |

### Key Mathlib references

- `CommRing`:            `Mathlib.Algebra.Ring.Defs`
- `IsDomain`:            `Mathlib.Algebra.Ring.Defs`
- `NoZeroDivisors`:      `Mathlib.Algebra.Ring.Defs`
- `Field`:               `Mathlib.Algebra.Field.Defs`
- `CharZero`:            `Mathlib.Algebra.CharZero.Defs`
- `LinearOrder`:         `Init.Order.LinearOrder`
- `IsStrictOrderedRing`: `Mathlib.Algebra.Order.Ring.Defs`
-/

end Azurite.BPR
