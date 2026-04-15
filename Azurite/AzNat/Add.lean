import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.OfLimbs

namespace Azurite.AzNat

/-- Add a single limb `b` into the subrange `a[lo:hi)`, propagating carry
    upward.  Returns the modified array (mutated in place when possible)
    and a boolean carry out of the high end.  When the running carry
    becomes zero, the remaining limbs are left untouched. -/
def addLimb (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × Bool :=
  go a lo b hhi
where
  go (a : Array UInt64) (i : Nat) (carry : UInt64) (h_size : hi ≤ a.size) :
      Array UInt64 × Bool :=
    if carry = 0 then
      (a, false)
    else if h : i < hi then
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h h_size
      let x := a[i]
      let sum := x + carry
      let newCarry : UInt64 := if sum < carry then 1 else 0
      go (a.set i sum) (i + 1) newCarry
        (by rw [Array.size_set]; exact h_size)
    else
      (a, true)
  termination_by hi - i

/-- Add a `UInt64` `b` to an `AzNat` `a`.  Empty `a` is handled directly via
    `UInt64.toAzNat b`; otherwise `addLimb` runs over `a.limbs` and the carry
    bit (if any) is appended as a new high limb of value `1`. -/
def addUInt64 (a : AzNat) (b : UInt64) : AzNat :=
  if a.limbs.size = 0 then b.toAzNat
  else
    let r := addLimb a.limbs 0 a.limbs.size b (Nat.zero_le _) (Nat.le_refl _)
    if r.2 then ofLimbs (r.1.push 1)
    else ofLimbs r.1

end Azurite.AzNat
