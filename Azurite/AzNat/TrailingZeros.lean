import Azurite.AzNat.Basic
import Azurite.AzNat.Parse

namespace Azurite.AzNat

/-- Count trailing zeros starting from limb index `i`. Requires a proof that
some limb at index `≥ i` is non-zero (guaranteed by the AzNat invariant). -/
def trailingZerosAux (a : AzNat) (i : Nat) (hi : i < a.limbs.size) : Nat :=
  if h : a.limbs[i] = 0 then
    have : a.limbs.size - (i + 1) < a.limbs.size - i := by omega
    have hi2 : i + 1 < a.limbs.size := by
      if hc : i + 1 < a.limbs.size then exact hc
      else
        have heq : a.limbs.size - 1 = i := by omega
        subst heq
        have hback : a.limbs.back? = some 0 := by
          show a.limbs[a.limbs.size - 1]? = some 0
          rw [Array.getElem?_eq_getElem hi]
          exact congrArg some h
        exact absurd hback a.last_ne_zero
    trailingZerosAux a (i + 1) hi2
  else
    i * 64 + a.limbs[i].toBitVec.ctz.toNat
termination_by a.limbs.size - i

/-- Count the number of trailing zeros in the binary representation.
Returns `none` for zero (which has infinitely many trailing zeros). -/
def trailingZeros (n : AzNat) : Option Nat :=
  if h : n.limbs.size = 0 then none
  else some (trailingZerosAux n 0 (by omega))

-- 0 has infinitely many trailing zeros
#guard (Azurite.AzNat.parse "0".toList).get!.trailingZeros == none
-- 1 = ...001₂, 0 trailing zeros
#guard (Azurite.AzNat.parse "1".toList).get!.trailingZeros == some 0
-- 8 = 1000₂, 3 trailing zeros
#guard (Azurite.AzNat.parse "8".toList).get!.trailingZeros == some 3
-- 12 = 1100₂, 2 trailing zeros
#guard (Azurite.AzNat.parse "12".toList).get!.trailingZeros == some 2
-- 2^64 = one zero limb then 1, so 64 trailing zeros
#guard (Azurite.AzNat.parse "18446744073709551616".toList).get!.trailingZeros == some 64
-- 3 * 2^128 = two zero limbs then 3, so 128 trailing zeros
#guard (Azurite.AzNat.parse "1020847100762815390390123822295304634368".toList).get!.trailingZeros == some 128

end Azurite.AzNat
