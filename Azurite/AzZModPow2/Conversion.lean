import Azurite.AzZModPow2.Basic
import Azurite.AzInt.Add

namespace Azurite.AzZModPow2

/-- Convert an `AzInt` to `AzZModPow2 k`: reduce the magnitude modulo `2^k`
(masking), then negate via the limb-level `neg` when the sign is negative. -/
def ofAzInt (k : Nat) (z : AzInt) : AzZModPow2 k :=
  if z.sign then ofAzNat k z.abs else -(ofAzNat k z.abs)

end Azurite.AzZModPow2

section Tests
open Azurite Azurite.AzZModPow2
-- `ℤ/16`: `+19 → 3`, `-1 → 15`, `-19 → 13`; `ℤ/256`: `-200 → 56`.
#guard (ofAzInt 4 (AzInt.mkNorm true (AzNat.ofNat 19))).val == (AzZModPow2.ofNat 4 3).val
#guard (ofAzInt 4 (AzInt.mkNorm false (AzNat.ofNat 1))).val == (AzZModPow2.ofNat 4 15).val
#guard (ofAzInt 4 (AzInt.mkNorm false (AzNat.ofNat 19))).val == (AzZModPow2.ofNat 4 13).val
#guard (ofAzInt 8 (AzInt.mkNorm false (AzNat.ofNat 200))).val == (AzZModPow2.ofNat 8 56).val
#guard (ofAzInt 4 (AzInt.mkNorm true (AzNat.ofNat 0))).val == (AzZModPow2.ofNat 4 0).val
end Tests
