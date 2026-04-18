import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.ClearBit

namespace Azurite.AzNat

/-- Clear the `i`-th bit of `n` (0-indexed, LSB first), setting it to `0`. Bit `i`
lives in limb `i / 64` at position `i % 64`; if that limb is beyond the array,
the bit is already `0` and `n` is returned unchanged. Otherwise the bit in the
corresponding limb is cleared, and trailing zero limbs are trimmed. -/
def clearBit (n : AzNat) (i : Nat) : AzNat :=
  let limbIdx := i / 64
  let bitIdx := i % 64
  if h : limbIdx < n.limbs.size then
    ofLimbs (n.limbs.set limbIdx ((n.limbs[limbIdx]).clearBit bitIdx))
  else
    n

end Azurite.AzNat
