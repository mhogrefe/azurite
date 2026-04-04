import Azurite.AzNat.Basic

namespace Azurite

structure AzInt where
  sign : Bool
  abs : AzNat
  zero_sign : abs = 0 → sign = true
  deriving DecidableEq

end Azurite
