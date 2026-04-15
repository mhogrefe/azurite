import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.SubWithBorrow

namespace Azurite.AzNat

/-- Subtract a single limb `b` from the subrange `a[lo:hi)`, propagating
    borrow upward.  Returns the modified array (mutated in place when
    possible) and a boolean borrow out of the high end.  When the running
    borrow becomes zero, the remaining limbs are left untouched. -/
def subLimb (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × Bool :=
  go a lo b hhi
where
  go (a : Array UInt64) (i : Nat) (borrow : UInt64) (h_size : hi ≤ a.size) :
      Array UInt64 × Bool :=
    if borrow = 0 then
      (a, false)
    else if h : i < hi then
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h h_size
      let x := a[i]
      let diff := x - borrow
      let newBorrow : UInt64 := if x < borrow then 1 else 0
      go (a.set i diff) (i + 1) newBorrow
        (by rw [Array.size_set]; exact h_size)
    else
      (a, true)
  termination_by hi - i

/-- Subtract a `UInt64` `b` from an `AzNat` `a`.  Empty `a` returns `0`
    (truncated `Nat` subtraction).  Otherwise `subLimb` runs over `a.limbs`;
    if a final borrow comes out, `a < b` so the result is `0`, else the
    trimmed limbs form the result. -/
def subUInt64 (a : AzNat) (b : UInt64) : AzNat :=
  if a.limbs.size = 0 then 0
  else
    let r := subLimb a.limbs 0 a.limbs.size b (Nat.zero_le _) (Nat.le_refl _)
    if r.2 then 0
    else ofLimbs r.1

end Azurite.AzNat
