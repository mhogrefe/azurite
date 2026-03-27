import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 8: Complexity of Basic Algorithms
## Section 8.1: Definition of Complexity

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006, pp. 281–284.

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

/-!
## Algorithm 8.1. Addition of Univariate Polynomials

Given `P = a_p X^p + ⋯ + a_0` and `Q = b_q X^q + ⋯ + b_0`, compute
`P + Q` by adding corresponding coefficients and normalizing
(dropping trailing zeros).

**Complexity (BPR):** `max(p, q) + 1` additions in the ring.

**Azurite implementation:** `Azurite.AzPolynomial.add`

See: `Azurite.AzPolynomial.Add`

The equivalence with Mathlib's `Polynomial.add` is proved in
`Azurite.AzPolynomial.Equiv.Add`.
-/

/-!
## Algorithm 8.2. Multiplication of Univariate Polynomials

Given `P = a_p X^p + ⋯ + a_0` and `Q = b_q X^q + ⋯ + b_0`, compute
`P · Q` by the standard (schoolbook) convolution:

  `c_k = ∑_{i+j=k} a_i · b_j`

and normalizing.

**Complexity (BPR):** `(p + 1)(q + 1)` multiplications and `pq`
additions in the ring.

**Azurite implementation:** `Azurite.AzPolynomial.mulBasecase`

See: `Azurite.AzPolynomial.Mul`

The equivalence with Mathlib's `Polynomial.mul` is proved in
`Azurite.AzPolynomial.Equiv.Mul`.

Note: Azurite also provides `Azurite.AzPolynomial.karatsuba`, an
asymptotically-faster O(n^1.585) multiplication algorithm. Its
equivalence with basecase multiplication (and thus with Mathlib) is
proved in `Azurite.AzPolynomial.Equiv.Karatsuba`.
-/

/-!
## Algorithm 8.3. Euclidean Division

Given polynomials `P = a_p X^p + ⋯ + a_0` and `Q = b_q X^q + ⋯ + b_0`
over a field `K` with `Q ≠ 0`, compute the unique quotient `Quo(P, Q)`
and remainder `Rem(P, Q)` such that:

  `P = Quo(P, Q) · Q + Rem(P, Q)` and `deg Rem(P, Q) < deg Q`.

**Algorithm:**
- Initialize `C := 0`, `R := P`.
- For `j` from `p` down to `q`:
  - `C := C + (coeff_j(R) / b_q) · X^{j−q}`
  - `R := R − (coeff_j(R) / b_q) · X^{j−q} · Q`
- Output `(C, R)`.

**Complexity (BPR):** `(p − q + 1)(2q + 1)` operations in the field
(each of the `p − q + 1` steps performs a division, a monomial
multiplication by `Q` costing `q + 1` multiplications, and a
subtraction of `q + 1` terms).

**Structure required:** Field (D₅).

**Azurite implementation:** `Azurite.AzPolynomial.quoRem`

See: `Azurite.AzPolynomial.QuoRem`

The equivalence with Mathlib's `Polynomial` division (`/` and `%`) is
proved in `Azurite.AzPolynomial.Equiv.QuoRem`, including:
- `toPoly_quo`:  `toPoly (quo P Q) = toPoly P / toPoly Q`
- `toPoly_rem`:  `toPoly (rem P Q) = toPoly P % toPoly Q`
- `degree_toPoly_rem_lt`:  `deg(toPoly (rem P Q)) < deg(toPoly Q)`
-/

/-!
## Definition 8.4. Bitsize

The **bitsize** of a non-zero integer `N` is the number `bit(N)` of
bits in its binary representation, characterized by:

  `2^{bit(N)−1} ≤ |N| < 2^{bit(N)}`

**Mathlib note:** `Nat.size : ℕ → ℕ` (from `Mathlib.Data.Nat.Size`)
computes exactly this for natural numbers, with the key lemmas:
- `Nat.lt_size : m < n.size ↔ 2 ^ m ≤ n`
- `Nat.lt_size_self : n < 2 ^ n.size`

There is no `Int.size` in Mathlib, so we define `Int.bitsize` as
`N.natAbs.size`.
-/

/-- BPR Definition 8.4. The bitsize of an integer `N`, defined as the
    number of bits in the binary representation of `|N|`.
    Returns `0` for `N = 0`. -/
def Int.bitsize (N : ℤ) : ℕ := N.natAbs.size

/-- For `N ≠ 0`, `2^{bit(N)−1} ≤ |N|`. -/
theorem Int.two_pow_pred_le_natAbs (N : ℤ) (hN : N ≠ 0) :
    2 ^ (Int.bitsize N - 1) ≤ N.natAbs := by
  have hpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hsize : 0 < N.natAbs.size := Nat.size_pos.mpr hpos
  show 2 ^ (N.natAbs.size - 1) ≤ N.natAbs
  exact Nat.lt_size.mp (Nat.sub_one_lt_of_le hsize le_rfl)

/-- `|N| < 2^{bit(N)}` (holds for all integers, including `0`). -/
theorem Int.natAbs_lt_two_pow_bitsize (N : ℤ) :
    N.natAbs < 2 ^ (Int.bitsize N) :=
  Nat.lt_size_self N.natAbs

/-- The bitsize of a nonzero integer is positive. -/
theorem Int.bitsize_pos (N : ℤ) (hN : N ≠ 0) : 0 < Int.bitsize N :=
  Nat.size_pos.mpr (Int.natAbs_pos.mpr hN)

/-- Corollary of Definition 8.4: `bit(N) − 1 ≤ log₂(|N|)`. -/
theorem Int.bitsize_sub_one_le_logb (N : ℤ) (hN : N ≠ 0) :
    (Int.bitsize N : ℝ) - 1 ≤ Real.logb 2 (N.natAbs : ℝ) := by
  have hposR : (0 : ℝ) < ↑N.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hN
  have hbs := bitsize_pos N hN
  rw [show (Int.bitsize N : ℝ) - 1 = ((Int.bitsize N - 1 : ℕ) : ℝ) from by
        rw [Nat.cast_sub hbs]; norm_cast,
      Real.le_logb_iff_rpow_le (by norm_num) hposR, Real.rpow_natCast]
  exact_mod_cast two_pow_pred_le_natAbs N hN

/-- Corollary of Definition 8.4: `log₂(|N|) < bit(N)`. -/
theorem Int.logb_lt_bitsize (N : ℤ) (hN : N ≠ 0) :
    Real.logb 2 (N.natAbs : ℝ) < (Int.bitsize N : ℝ) := by
  have hposR : (0 : ℝ) < ↑N.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hN
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hposR, Real.rpow_natCast]
  exact_mod_cast natAbs_lt_two_pow_bitsize N

end Azurite.BPR
