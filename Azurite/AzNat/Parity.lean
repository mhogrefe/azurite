import Azurite.AzNat.Basic

namespace Azurite

/-- Efficient parity test: checks bit 0 of the lowest limb. -/
def AzNat.isEven (n : AzNat) : Bool :=
  if h : n.limbs.size > 0 then
    n.limbs[0] &&& 1 == 0
  else
    true

/-- Efficient parity test: checks bit 0 of the lowest limb. -/
def AzNat.isOdd (n : AzNat) : Bool :=
  !n.isEven

end Azurite
