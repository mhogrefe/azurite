import Azurite.AzZMod.Basic
import Azurite.AzZMod.ToString
import Azurite.Algorithm.SlidingWindowPow

/-!
## Exponentiation for `AzZMod`

`pow` via the generic **sliding-window** exponentiation `Azurite.slidingWindowPow`,
so `a ^ n mod m` costs `O(log n)` modular multiplications, each squaring using the
fast `Square` instance rather than a general multiply.  Mirrors `AzZModPow2.pow`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- **Exponentiation** in `ℤ / m`: `a ^ n mod m`, by sliding-window
exponentiation over the `AzZMod` ring operations. -/
def pow [NeZero m.toNat] (a : AzZMod m) (n : ℕ) : AzZMod m :=
  Azurite.slidingWindowPow a n

end Azurite.AzZMod

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

-- `3^4 = 81 ≡ 4 (mod 7)`, `2^10 = 1024 ≡ 24 (mod 1000)`, `7^0 = 1`.
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 7) 3).pow 4) == "4"
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 1000) 2).pow 10) == "24"
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 1000) 7).pow 0) == "1"
-- `123^5 mod 1000`: `123^5 = 28153056843`, `≡ 843`.
#guard Azurite.AzZMod.toString ((AzZMod.ofNat (AzNat.ofNat 1000) 123).pow 5) == "843"

end Tests
