import Azurite.AzZMod.ToString
import Azurite.AzZMod.Parse
import Azurite.AzNat.Equiv.ParseBase

namespace Azurite.AzZMod

variable {m : AzNat} [NeZero m.toNat]

/-- **Round-trip:** parsing the rendering of a residue recovers it.  (Parsing is
not injective in general — `parse` reduces modulo `m` — but on the output of
`toString`, which already prints a canonical residue, it round-trips.) -/
theorem parse_toString (a : AzZMod m) : parse (toString a) = some a := by
  show (AzNat.parse (AzNat.toString a.val)).map (ofAzNat m) = some a
  rw [AzNat.parse_toString]
  show some (ofAzNat m a.val) = some a
  rw [ofAzNat_val]

end Azurite.AzZMod
