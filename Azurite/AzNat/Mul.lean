import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.MulWithCarry

namespace Azurite.AzNat

/-- Multiply the subrange `a[lo:hi)` by a single limb `b`, threading a running
    carry.  Each limb `a[i]` is replaced by the low half of
    `a[i] * b + carry`; the high half becomes the new carry.  Returns the
    modified array and the final carry-out. -/
def mulLimb (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × UInt64 :=
  go b a lo 0 hhi
where
  go (b : UInt64) (a : Array UInt64) (i : Nat) (carry : UInt64)
      (h_size : hi ≤ a.size) : Array UInt64 × UInt64 :=
    if h : i < hi then
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h h_size
      let x := a[i]
      let (newCarry, lo') := UInt64.mulWithCarry x b carry
      go b (a.set i lo') (i + 1) newCarry
        (by rw [Array.size_set]; exact h_size)
    else
      (a, carry)
  termination_by hi - i

/-- Multiply an `AzNat` `a` by a `UInt64` `b`.  Zero operands short-circuit;
    otherwise `mulLimb` runs over `a.limbs` and the final carry (if nonzero)
    is appended as a new high limb. -/
def mulUInt64 (a : AzNat) (b : UInt64) : AzNat :=
  if a.limbs.size = 0 then 0
  else if b = 0 then 0
  else
    let r := mulLimb a.limbs 0 a.limbs.size b (Nat.zero_le _) (Nat.le_refl _)
    if r.2 = 0 then ofLimbs r.1
    else ofLimbs (r.1.push r.2)

end Azurite.AzNat
