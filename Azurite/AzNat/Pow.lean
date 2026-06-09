import Azurite.Algorithm.SlidingWindowPow
import Azurite.AzNat.Equiv.Square.ToomCook3
import Azurite.AzNat.Instances

/-!
# Exponentiation for AzNat

Computable exponentiation `a ^ n` for multi-limb naturals, in `O(log n)` `AzNat`
multiplications. Two variants are provided so they can be benchmarked against each other:

- `AzNat.pow` — **sliding-window** exponentiation (`Azurite.slidingWindowPow`).
- `AzNat.powBinary` — **right-to-left binary** exponentiation (`Azurite.fastPow`), the older
  algorithm, kept as a benchmarking baseline.

Both route their squarings through AzNat's dedicated three-way `square` (schoolbook / Karatsuba /
Toom-Cook 3) via the `Square AzNat` instance below, so a squaring costs a single subquadratic
squaring rather than a general multiplication.

## Main definitions

- `Azurite.AzNat.pow a n`, `Azurite.AzNat.powBinary a n`.

## Main theorems

- `Azurite.AzNat.toNat_pow`, `Azurite.AzNat.toNat_powBinary`: both agree with `a.toNat ^ n`.
- `Azurite.AzNat.pow_eq_powBinary`: the two algorithms compute the same value.
-/

namespace Azurite.AzNat

/-- Route `Square.square` to AzNat's dedicated three-way `square` (schoolbook / Karatsuba /
Toom-Cook 3), so exponentiation squares in subquadratic time rather than via a general
multiplication. Overrides the low-priority default `Square` instance. -/
instance instSquareAzNat : Azurite.Square AzNat where
  square := AzNat.square
  square_eq a := toNat_injective (by rw [toNat_square, toNat_mul, pow_two])

/-- Exponentiation for `AzNat` via **sliding-window** exponentiation, in `O(log n)`
multiplications (with a small precomputed table of odd powers). -/
def pow (a : AzNat) (n : ℕ) : AzNat :=
  Azurite.slidingWindowPow a n

/-- Exponentiation for `AzNat` via **right-to-left binary** exponentiation (exponentiation by
squaring) — the older algorithm, kept for benchmarking against `pow`. -/
def powBinary (a : AzNat) (n : ℕ) : AzNat :=
  Azurite.fastPow a n

/-- `pow` agrees with `ℕ` exponentiation under `toNat`. -/
@[simp] theorem toNat_pow (a : AzNat) (n : ℕ) : (a.pow n).toNat = a.toNat ^ n :=
  Azurite.map_slidingWindowPow AzNat.toNat toNat_one toNat_mul a n

/-- `powBinary` agrees with `ℕ` exponentiation under `toNat`. -/
@[simp] theorem toNat_powBinary (a : AzNat) (n : ℕ) : (a.powBinary n).toNat = a.toNat ^ n :=
  Azurite.map_fastPow AzNat.toNat toNat_one toNat_mul a n

/-- The two exponentiation algorithms compute the same value. -/
theorem pow_eq_powBinary (a : AzNat) (n : ℕ) : a.pow n = a.powBinary n :=
  toNat_injective (by rw [toNat_pow, toNat_powBinary])

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard (AzNat.ofNat 3).pow 4 = AzNat.ofNat 81
#guard (AzNat.ofNat 2).pow 10 = AzNat.ofNat 1024
#guard (AzNat.ofNat 7).pow 0 = AzNat.ofNat 1
#guard (AzNat.ofNat 7).pow 1 = AzNat.ofNat 7
#guard (AzNat.ofNat 5).pow 3 = AzNat.ofNat 125
#guard (AzNat.ofNat 2).pow 64 = AzNat.ofNat (2 ^ 64)
#guard (AzNat.ofNat 3).pow 100 = AzNat.ofNat (3 ^ 100)
#guard (AzNat.ofNat 2).pow 1000 = AzNat.ofNat (2 ^ 1000)

-- The sliding-window and binary algorithms agree across a range of exponents.
#guard (List.range 60).all (fun n => (AzNat.ofNat 3).pow n = (AzNat.ofNat 3).powBinary n)
#guard (List.range 40).all (fun n => (AzNat.ofNat 12345).pow n = (AzNat.ofNat 12345).powBinary n)

end Tests

end Azurite.AzNat
