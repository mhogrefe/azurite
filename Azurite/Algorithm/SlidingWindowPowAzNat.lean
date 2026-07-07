import Azurite.Algorithm.SlidingWindowPow
import Azurite.AzNat.TestBit
import Azurite.AzNat.Size

/-!
# `AzNat`-exponent exponentiation (limb-level)

`slidingWindowPowAzNat a n` computes `a ^ n` where the exponent `n : AzNat` is read
**directly at the limb level** — never materialized as a `Nat` via `AzNat.toNat`.  This is what
lets factorization-style powers `x ^ (p^k)` (with `n` a 40+ digit number) run without pushing a huge
exponent through Lean's `Nat` (GMP) representation.

The algorithm is left-to-right binary exponentiation: scan the exponent's bits from the most
significant (`AzNat.size n` gives the bit length, a small `Nat`) down to bit `0`, squaring the
accumulator at every step and multiplying in `a` at each set bit.  The bits are obtained by
`AzNat.testBit`, which reads a single limb — so the whole computation is `O(bitLen n)` squarings
with no `Nat`-valued exponent ever constructed.

This is a leaner (binary) companion of the windowed ℕ-exponent `slidingWindowPow`; the existing
ℕ `slidingWindowPow` (the `npow` of `AzPolynomial`/`AzMatrix`/`AzMvPolynomial`) is left untouched.
-/

namespace Azurite

variable {M : Type _}

/-- Left-to-right binary exponentiation loop over the bits of `n`, from index `i-1` down to `0`.
`result` holds `a ^ (high bits already consumed)`; each step squares it and multiplies by `a` when
the next (limb-read) bit is set. -/
def slidingWindowPowAzNatAux [Mul M] [Square M] (a : M) (n : AzNat) : Nat → M → M
  | 0, result => result
  | i + 1, result =>
    let sq := Square.square result
    let next := if n.testBit i then sq * a else sq
    slidingWindowPowAzNatAux a n i next

/-- **`AzNat`-exponent exponentiation.**  Computes `a ^ n` reading the bits of `n : AzNat`
directly (limb-level, never via `AzNat.toNat`). -/
def slidingWindowPowAzNat [Mul M] [One M] [Square M] (a : M) (n : AzNat) : M :=
  slidingWindowPowAzNatAux a n n.size 1

end Azurite
