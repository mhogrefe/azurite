import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs

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

end Azurite.AzNat
