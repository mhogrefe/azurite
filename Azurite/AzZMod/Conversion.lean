import Azurite.AzZMod.Basic
import Azurite.AzInt.Add

namespace Azurite.AzZMod

/-- Convert an `AzInt` to `AzZMod m`: reduce the magnitude modulo `m`, then
negate via the limb-level `neg` when the sign is negative. -/
def ofAzInt (m : AzNat) [NeZero m.toNat] (z : AzInt) : AzZMod m :=
  if z.sign then ofAzNat m z.abs else -(ofAzNat m z.abs)

end Azurite.AzZMod

section Tests
open Azurite Azurite.AzZMod
-- `ℤ/7`: `+19 → 5`, `-1 → 6`, `-19 → 2`, `-0 → 0`; `ℤ/1000`: `-456 → 544`.
#guard ofAzInt (AzNat.ofNat 7) (AzInt.mkNorm true (AzNat.ofNat 19)) == AzZMod.ofNat (AzNat.ofNat 7) 5
#guard ofAzInt (AzNat.ofNat 7) (AzInt.mkNorm false (AzNat.ofNat 1)) == AzZMod.ofNat (AzNat.ofNat 7) 6
#guard ofAzInt (AzNat.ofNat 7) (AzInt.mkNorm false (AzNat.ofNat 19)) == AzZMod.ofNat (AzNat.ofNat 7) 2
#guard ofAzInt (AzNat.ofNat 7) (AzInt.mkNorm true (AzNat.ofNat 0)) == AzZMod.ofNat (AzNat.ofNat 7) 0
#guard ofAzInt (AzNat.ofNat 1000) (AzInt.mkNorm false (AzNat.ofNat 456)) ==
  AzZMod.ofNat (AzNat.ofNat 1000) 544
end Tests
