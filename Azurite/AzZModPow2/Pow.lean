import Azurite.AzZModPow2.Basic
import Azurite.AzNat.SquareModPow2.Dispatch
import Azurite.AzNat.Equiv.SquareModPow2.Dispatch
import Azurite.Algorithm.SlidingWindowPow

/-!
## Exponentiation for `AzZModPow2`

A dedicated squaring (`Square` instance) routed through the size-dispatched low
square `AzNat.squareDispatchModPow2`, and `pow` via the generic
**sliding-window** exponentiation `Azurite.slidingWindowPow`, so `a ^ n mod 2^k`
costs `O(log n)` modular multiplications, each squaring using the three-way low
square rather than a general multiply.
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- **Squaring** in `ℤ / 2^k`, via the size-dispatched low square
    `AzNat.squareDispatchModPow2` (exploiting symmetry and skipping the top half).
    Overrides the default `x * x` so the sliding-window power uses the fast
    square. -/
instance instSquare : Azurite.Square (AzZModPow2 k) where
  square a := ⟨AzNat.squareDispatchModPow2 a.val k, by
    rw [AzNat.toNat_squareDispatchModPow2]; exact Nat.mod_lt _ (by positivity)⟩
  square_eq a := by
    apply ext
    apply AzNat.toNat_injective
    show (AzNat.squareDispatchModPow2 a.val k).toNat = (AzNat.mulDispatchModPow2 a.val a.val k).toNat
    rw [AzNat.toNat_squareDispatchModPow2, AzNat.toNat_mulDispatchModPow2, pow_two]

/-- **Exponentiation** in `ℤ / 2^k`: `a ^ n mod 2^k`, by sliding-window
    exponentiation over the `AzZModPow2` ring operations. -/
def pow (a : AzZModPow2 k) (n : ℕ) : AzZModPow2 k :=
  Azurite.slidingWindowPow a n

end Azurite.AzZModPow2

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZModPow2

-- `3^4 = 81 ≡ 1 (mod 16)`, `2^10 = 1024 ≡ 0 (mod 256)`, `7^0 = 1`.
#guard ((AzZModPow2.ofNat 4 3).pow 4) == (AzZModPow2.ofNat 4 1)
#guard ((AzZModPow2.ofNat 8 2).pow 10) == (AzZModPow2.ofNat 8 0)
#guard ((AzZModPow2.ofNat 8 7).pow 0) == (AzZModPow2.ofNat 8 1)
#guard ((AzZModPow2.ofNat 32 3).pow 20) == (AzZModPow2.ofNat 32 (3 ^ 20 % 2 ^ 32))
-- Multi-limb modulus.
#guard ((AzZModPow2.ofNat 128 123456789).pow 50) ==
  (AzZModPow2.ofNat 128 (123456789 ^ 50 % 2 ^ 128))

end Tests
