import Azurite.AzNat.Basic

namespace Azurite

/-- The number of bits required to represent the natural number in binary.
Equivalent to `Nat.size`. -/
def AzNat.size (n : AzNat) : Nat :=
  if h : n.limbs.size > 0 then
    have hs : n.limbs.size - 1 < n.limbs.size := Nat.sub_lt h (by decide)
    let s := n.limbs.size - 1
    s * 64 + n.limbs[s].log2.toNat + 1
  else
    0

end Azurite
