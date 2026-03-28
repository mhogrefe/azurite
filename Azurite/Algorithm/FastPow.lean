import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Group.Defs

/-!
# Exponentiation by Squaring

This file implements **right-to-left binary exponentiation** (exponentiation by squaring)
for any type with `Mul` and `One`. It computes `a ^ n` in `O(log n)` multiplications by
iterating over the bits of `n` from least-significant to most-significant.

## Algorithm

The right-to-left method maintains two accumulators: `acc` (the partial result) and `base`
(the current power of `a`). At each step:
- If the current bit of `n` is 1, multiply `acc` by `base`.
- Square `base` for the next bit.
- Shift `n` right by one.

The loop invariant is: `acc * base ^ remaining_n = a ^ original_n`.

## Main Definitions

- `Azurite.fastPow a n`: computes `a ^ n` in `O(log n)` multiplications.
- `Azurite.fastPowAux acc base n`: tail-recursive helper with invariant `result = acc * base ^ n`.

## Main Theorems

- `Azurite.fastPowAux_eq`: the loop invariant `fastPowAux acc base n = acc * base ^ n`.
- `Azurite.fastPow_eq_pow`: correctness `fastPow a n = a ^ n` (where `^` is Mathlib's `HPow`).

## Design Notes

The computational definitions (`fastPowAux`, `fastPow`) only require `[Mul M]` and `[One M]`,
making them computable for types whose `Monoid` instance is noncomputable (e.g., `AzPolynomial`,
`AzMatrix`) but whose `Mul` and `One` are computable. The correctness proofs use the full
`[Monoid M]` structure.
-/

namespace Azurite

/-- Tail-recursive helper for binary exponentiation (right-to-left).
    Processes bits of `n` from LSB to MSB.
    Invariant: `fastPowAux acc base n = acc * base ^ n` (when `M` is a `Monoid`). -/
def fastPowAux [Mul M] (acc base : M) (n : ℕ) : M :=
  if h : n = 0 then acc
  else if n % 2 = 0 then
    fastPowAux acc (base * base) (n / 2)
  else
    fastPowAux (acc * base) (base * base) (n / 2)
termination_by n

/-- Exponentiation by squaring. Computes `a ^ n` in `O(log n)` multiplications.
    Only requires `Mul` and `One`; proven equivalent to `a ^ n` when `M` is a `Monoid`. -/
def fastPow [Mul M] [One M] (a : M) (n : ℕ) : M :=
  fastPowAux 1 a n

/-- The loop invariant: `fastPowAux acc base n = acc * base ^ n`. -/
theorem fastPowAux_eq [Monoid M] (acc base : M) (n : ℕ) :
    fastPowAux acc base n = acc * base ^ n := by
  induction n using Nat.strongRecOn generalizing acc base with
  | _ n ih =>
    unfold fastPowAux
    split
    · -- n = 0: acc = acc * base ^ 0 = acc * 1
      rename_i h; subst h; simp [pow_zero, mul_one]
    · rename_i h
      split
      · -- n even: go acc (base²) (n/2) = acc * (base²)^(n/2) = acc * base^n
        rename_i heven
        rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        congr 1
        rw [show base * base = base ^ 2 from (sq base).symm, ← pow_mul]
        congr 1; omega
      · -- n odd: go (acc * base) (base²) (n/2) = (acc * base) * (base²)^(n/2)
        --       = acc * base^(2*(n/2)+1) = acc * base^n
        rename_i hodd
        rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
        rw [mul_assoc]
        congr 1
        rw [show base * base = base ^ 2 from (sq base).symm, ← pow_mul, ← pow_succ']
        congr 1; omega

/-- Exponentiation by squaring agrees with Mathlib's `HPow.hPow`. -/
theorem fastPow_eq_pow [Monoid M] (a : M) (n : ℕ) : fastPow a n = a ^ n := by
  simp [fastPow, fastPowAux_eq, one_mul]

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard fastPow (2 : ℕ) 0 = 1
#guard fastPow (2 : ℕ) 1 = 2
#guard fastPow (2 : ℕ) 10 = 1024
#guard fastPow (3 : ℕ) 5 = 243
#guard fastPow (7 : ℕ) 0 = 1
#guard fastPow (1 : ℕ) 100 = 1
#guard fastPow (5 : ℕ) 3 = 125

end Tests

end Azurite
