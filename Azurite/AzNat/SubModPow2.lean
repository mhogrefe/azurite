import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.ModPow2
import Azurite.UInt64.SubWithBorrow

/-!
## `AzNat.subModPow2` — fused subtract-then-reduce mod `2 ^ k`

The borrow analogue of `AzNat.addModPow2`.  Walks the low `L = (k + 63) / 64`
limbs of `a` and `b`, reading `0` past each array's length (no padding
allocation), subtracts with borrow, drops the final borrow-out (it corresponds
to the `+2^k` wrap when `a < b`), and masks the result to the low `k` bits via
`modPow2`.
-/

namespace Azurite.AzNat

/-- Build the low `L` limbs of `a - b` reading `0` past each array's length,
    pushing each borrow-propagated limb onto `acc`; the final borrow-out is
    dropped. -/
def lowDiffLimbs (a b : Array UInt64) (L i : Nat) (borrow : Bool)
    (acc : Array UInt64) : Array UInt64 :=
  if i < L then
    let swb := UInt64.subWithBorrow (a.getD i 0) (b.getD i 0) borrow
    lowDiffLimbs a b L (i + 1) swb.2 (acc.push swb.1)
  else acc
termination_by L - i

/-- **Fused subtract-and-mask.** `(a - b) mod 2 ^ k`, computed by walking only the
    low `L = (k + 63) / 64` limbs of `a` and `b` (no padding) and masking to the
    low `k` bits.  The final borrow-out is dropped (the `+2^k` wrap when
    `a < b`).  Reads with allocation-free `Array.getD` (no `Option` boxing) into a
    buffer pre-sized to `L` limbs (no reallocation during the borrow walk). -/
def subModPow2 (a b : AzNat) (k : Nat) : AzNat :=
  modPow2 (ofLimbs (lowDiffLimbs a.limbs b.limbs ((k + 63) / 64) 0 false
    (Array.emptyWithCapacity ((k + 63) / 64)))) k

end Azurite.AzNat
