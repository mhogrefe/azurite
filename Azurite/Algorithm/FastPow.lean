import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Group.Defs

/-!
# Exponentiation by Squaring

This file implements **right-to-left binary exponentiation** (exponentiation by squaring)
for any type with `Mul`, `One`, and a `Square` operation. It computes `a ^ n` in `O(log n)`
squarings and at most `O(log n)` multiplications.

## Algorithm

The right-to-left method maintains two accumulators: `acc` (the partial result) and `base`
(the current power of `a`). At each step:
- If the current bit of `n` is 1, multiply `acc` by `base`.
- Square `base` for the next bit (via `Square.square`).
- Shift `n` right by one.

The loop invariant is: `acc * base ^ remaining_n = a ^ original_n`.

## The `Square` typeclass

`Square M` packages an explicit `square : M → M` operation together with the proof that
it agrees with `x * x`. Types whose squaring is faster than a general multiplication
(e.g., a custom multiplication algorithm that exploits commutativity of the two operands)
override the default instance to plug in their faster version. Any type with `Mul` gets
the default `square x := x * x` instance automatically.

## Main Definitions

- `Azurite.Square M`: typeclass with `square : M → M` and `square_eq`.
- `Azurite.fastPow a n`: computes `a ^ n` in `O(log n)` squarings.
- `Azurite.fastPowAux acc base n`: tail-recursive helper with invariant `result = acc * base ^ n`.

## Main Theorems

- `Azurite.fastPowAux_eq`: the loop invariant `fastPowAux acc base n = acc * base ^ n`.
- `Azurite.fastPow_eq_pow`: correctness `fastPow a n = a ^ n` (where `^` is Mathlib's `HPow`).

## Design Notes

The computational definitions (`fastPowAux`, `fastPow`) only require `[Mul M]`, `[One M]`,
and `[Square M]`. The correctness proofs use the full `[Monoid M]` structure. This split
lets the algorithm be invoked in modules where only the multiplicative pieces are in scope
(useful when the full `Monoid` instance lives later in the import graph), and keeps the
runtime path through bare function calls rather than `Monoid`-bundle field projections.
-/

namespace Azurite

/-- A type with an explicit squaring operation that agrees with `x * x`. Override
    the default instance for types where squaring can be done faster than the
    general multiplication. -/
class Square (M : Type _) [Mul M] where
  /-- Square an element. -/
  square : M → M
  /-- The squaring operation agrees with multiplying the element by itself. -/
  square_eq : ∀ x : M, square x = x * x

/-- Default `Square` instance: square via `x * x`. Low priority so types
    with a faster squaring can override. -/
instance (priority := low) [Mul M] : Square M where
  square x := x * x
  square_eq _ := rfl

/-- Tail-recursive helper for binary exponentiation (right-to-left).
    Processes bits of `n` from LSB to MSB. Squares `base` via `Square.square`
    so types with a custom squaring path can plug in.

    Once the remaining bits `n / 2` are exhausted we return directly instead of
    squaring `base` one last time: that final square would be the single most
    expensive operation (squaring the largest intermediate `base`), and its
    result is never used.

    Invariant: `fastPowAux acc base n = acc * base ^ n` (when `M` is a `Monoid`). -/
def fastPowAux [Mul M] [Square M] (acc base : M) (n : ℕ) : M :=
  if n = 0 then acc
  else if n / 2 = 0 then
    -- last bit: `n = 1`, so the answer is `acc * base`; no more squaring.
    if n % 2 = 0 then acc else acc * base
  else if n % 2 = 0 then
    fastPowAux acc (Square.square base) (n / 2)
  else
    fastPowAux (acc * base) (Square.square base) (n / 2)
termination_by n

/-- Exponentiation by squaring. Computes `a ^ n` in `O(log n)` squarings.
    Only requires `Mul`, `One`, and `Square`; proven equivalent to `a ^ n` when
    `M` is a `Monoid`. -/
def fastPow [Mul M] [One M] [Square M] (a : M) (n : ℕ) : M :=
  fastPowAux 1 a n

/-- **The loop invariant, transported along any multiplicative map.** For a function `f : M → N`
into a monoid `N` that preserves multiplication, `f (fastPowAux acc base n) = f acc * (f base) ^ n`.

This is the single source of truth for `fastPow`'s correctness: it is proven once, by induction on the
algorithm. Two important consequences follow without re-doing the induction:
* `fastPowAux_eq` (take `f = id`, `N = M`): the plain invariant `fastPowAux acc base n = acc * base ^ n`;
* for a wrapper type `T` whose `HPow` is *defined* as `fastPow`, a map `f : T → MathlibType` (such as
  `toMat`/`toPoly`) gives `f (fastPow a n) = (f a) ^ n` directly — there the plain `fastPowAux_eq` would
  be circular, since `a ^ n` on `T` is itself `fastPow`. -/
theorem map_fastPowAux {M N : Type*} [Mul M] [Square M] [Monoid N]
    (f : M → N) (hmul : ∀ a b : M, f (a * b) = f a * f b) (acc base : M) (n : ℕ) :
    f (fastPowAux acc base n) = f acc * (f base) ^ n := by
  induction n using Nat.strongRecOn generalizing acc base with
  | _ n ih =>
    unfold fastPowAux
    split
    · -- n = 0: f acc = f acc * (f base) ^ 0
      rename_i h; subst h; simp
    · rename_i h
      split
      · -- n / 2 = 0, so n = 1: the answer is `acc * base`, mapping to `f acc * (f base) ^ 1`.
        rename_i hd
        have hn1 : n = 1 := by omega
        subst hn1
        rw [if_neg (show ¬ ((1 : ℕ) % 2 = 0) from by decide), hmul, pow_one]
      · rename_i hd
        split
        · -- n even
          rename_i heven
          rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
          congr 1
          rw [Square.square_eq, hmul, show f base * f base = (f base) ^ 2 from (sq _).symm, ← pow_mul]
          congr 1; omega
        · -- n odd
          rename_i hodd
          rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega))]
          rw [hmul, mul_assoc]
          congr 1
          rw [Square.square_eq, hmul, show f base * f base = (f base) ^ 2 from (sq _).symm,
              ← pow_mul, ← pow_succ']
          congr 1; omega

/-- The loop invariant: `fastPowAux acc base n = acc * base ^ n`. The `f = id` case of
`map_fastPowAux`. -/
theorem fastPowAux_eq [Monoid M] [Square M] (acc base : M) (n : ℕ) :
    fastPowAux acc base n = acc * base ^ n :=
  map_fastPowAux id (fun _ _ => rfl) acc base n

/-- Exponentiation by squaring agrees with Mathlib's `HPow.hPow`. -/
theorem fastPow_eq_pow [Monoid M] [Square M] (a : M) (n : ℕ) : fastPow a n = a ^ n := by
  simp [fastPow, fastPowAux_eq, one_mul]

/-- **`fastPow` transported along a multiplicative map.** For `f : M → N` preserving `1` and `*`,
`f (fastPow a n) = (f a) ^ n`. This is how a wrapper type relates its `fastPow`-based power to the
reference power on a Mathlib type, without re-proving the algorithm. -/
theorem map_fastPow {M N : Type*} [Mul M] [One M] [Square M] [Monoid N]
    (f : M → N) (hone : f 1 = 1) (hmul : ∀ a b : M, f (a * b) = f a * f b) (a : M) (n : ℕ) :
    f (fastPow a n) = (f a) ^ n := by
  rw [fastPow, map_fastPowAux f hmul, hone, one_mul]

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
