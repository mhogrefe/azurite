import Azurite.AzZModPow2.ToString
import Azurite.AzZModPow2.Parse
import Azurite.AzNat.Equiv.ParseBase

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- **Round-trip:** parsing the rendering of a residue recovers it.  (Parsing is
not injective in general — `parse` reduces modulo `2^k` — but on the output of
`toString`, which already prints a canonical residue, it round-trips.) -/
theorem parse_toString (a : AzZModPow2 k) : parse (toString a) = some a := by
  show (AzNat.parse (AzNat.toString a.val)).map (ofAzNat k) = some a
  rw [AzNat.parse_toString]
  show some (ofAzNat k a.val) = some a
  rw [ofAzNat_val]

end Azurite.AzZModPow2
