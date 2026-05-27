import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs

namespace Azurite.AzNat

/-- Count trailing zeros in a limb array starting from limb index `i`.
    Scans from `i` upward; when a nonzero limb is found, returns
    `i * 64 + ctz(limb)`.  Requires `i < a.size`. -/
def trailingZerosLimbsAux (a : Array UInt64) (i : Nat) (h_bound : i < a.size) : Nat :=
  if h : a[i] = 0 then
    if h2 : i + 1 < a.size then
      trailingZerosLimbsAux a (i + 1) h2
    else
      0
  else
    i * 64 + a[i].toBitVec.ctz.toNat
  termination_by a.size - i

/-- Count trailing zeros in a raw limb array.  Returns `0` for a zero or
    empty array (the caller should guard for those cases). -/
def trailingZerosLimbs (a : Array UInt64) : Nat :=
  if h : 0 < a.size then trailingZerosLimbsAux a 0 h else 0

/-- Count the number of trailing zeros in the binary representation.
    Returns `none` for zero (which has infinitely many trailing zeros). -/
def trailingZeros (n : AzNat) : Option Nat :=
  if n.limbs.size = 0 then none
  else some (trailingZerosLimbs n.limbs)

end Azurite.AzNat
