import Azurite.AzInt.Add
import Azurite.AzNat.Karatsuba

namespace Azurite.AzInt

/-- Multiply an `AzInt` `z` by a `UInt64` `u`. -/
def mulUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  mkNorm z.sign (z.abs.mulUInt64 u)

/-- Multiply an `AzInt` `z` by an `Int64` `i`. -/
def mulInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then mkNorm z.sign (z.abs.mulUInt64 i.toUInt64)
  else mkNorm (!z.sign) (z.abs.mulUInt64 (-i).toUInt64)

/-- Multiply two `AzInt`s. -/
def mul (a b : AzInt) : AzInt :=
  mkNorm (a.sign == b.sign) (a.abs * b.abs)

instance : Mul AzInt := ⟨mul⟩

end Azurite.AzInt
