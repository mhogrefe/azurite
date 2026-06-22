import Azurite.AzZMod.Conversion
import Azurite.AzInt.ExtendedGcd

/-!
## Modular inverse of a unit in `ℤ / m`

An element of `ℤ / m` is a unit exactly when its representative is coprime to `m`.
The inverse is read off the **extended GCD**: `AzInt.egcd a.val m` returns
`(g, s, t)` with `s · a.val + t · m = g = gcd(a.val, m)`.  When `a.val` is coprime
to `m` this gcd is `1`, so `s · a.val ≡ 1 (mod m)` and the inverse is the
reduction `ofAzInt m s` of the Bézout coefficient `s`.  Correctness lives in
`AzZMod/Equiv/Inv.lean`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- **Modular inverse** of a residue coprime to the modulus, via the extended GCD.
Requires a proof that `a.val` is coprime to `m` (the exact condition for `a` to be
a unit). -/
def inv [NeZero m.toNat] (a : AzZMod m) (_h : Nat.Coprime a.val.toNat m.toNat) : AzZMod m :=
  ofAzInt m (AzInt.egcd a.val m).2.1

end Azurite.AzZMod
