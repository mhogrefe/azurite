import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.AddWithCarry

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

/-- Recursive helper for `addSameLengthLimbs`: processes positions
    `loA + k .. loA + len` and `loB + k .. loB + len` simultaneously. -/
def addSameLengthLimbs.go (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    Array UInt64 × Bool :=
  if h : k < len then
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    let awc := UInt64.addWithCarry a[loA + k] b[loB + k] carry
    addSameLengthLimbs.go b loA loB len (a.set (loA + k) awc.1) (k + 1) awc.2
      (by rw [Array.size_set]; exact hA) hB
  else
    (a, carry)
  termination_by len - k

/-- Add the slice `b[loB : loB + len)` into `a[loA : loA + len)` in place.
    Returns the modified array `a` and the final carry-out of the high end. -/
def addSameLengthLimbs (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    Array UInt64 × Bool :=
  addSameLengthLimbs.go b loA loB len a 0 false hA hB

/-- Size preservation of `addSameLengthLimbs.go`. -/
theorem addSameLengthLimbs.go_size (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (addSameLengthLimbs.go b loA loB len a k carry hA hB).1.size = a.size := by
  induction h_sub : len - k generalizing a k carry with
  | zero =>
    have h_ge : len ≤ k := by omega
    rw [addSameLengthLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    rw [addSameLengthLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega), Array.size_set]

/-- Size preservation of `addSameLengthLimbs`. -/
theorem addSameLengthLimbs_size (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (addSameLengthLimbs a b loA loB len hA hB).1.size = a.size :=
  addSameLengthLimbs.go_size b loA loB len a 0 false hA hB

/-- Add the slice `b[loB : loB + lenB)` into `a[loA : loA + lenA)` where
    `lenA ≥ lenB` and both slices are nonempty.  Low `lenB` limbs are summed
    via `addSameLengthLimbs`; any outgoing carry is propagated into the upper
    `lenA - lenB` limbs of `a` via `addLimb`.  Returns the modified array and
    the final high carry-out. -/
def addGeqLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (_h_posA : 0 < lenA) (_h_posB : 0 < lenB) :
    Array UInt64 × Bool :=
  let lo := addSameLengthLimbs a b loA loB lenB (by omega) hB
  if lo.2 then
    addLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
      (by rw [addSameLengthLimbs_size]; exact hA)
  else
    (lo.1, false)

/-- Add the slice `b[loB : loB + lenB)` to the slice `a[loA : loA + lenA)`,
    dispatching to `addGeqLimbs` based on which slice is longer.  The result
    is written into the longer slice (in `a` when `lenB ≤ lenA`, else `b`). -/
def addLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_posA : 0 < lenA) (h_posB : 0 < lenB) :
    Array UInt64 × Bool :=
  if h : lenB ≤ lenA then
    addGeqLimbs a b loA lenA loB lenB hA hB h h_posA h_posB
  else
    addGeqLimbs b a loB lenB loA lenA hB hA (by omega) h_posB h_posA

/-- Add a `UInt64` `b` to an `AzNat` `a`.  Empty `a` is handled directly via
    `UInt64.toAzNat b`; otherwise `addLimb` runs over `a.limbs` and the carry
    bit (if any) is appended as a new high limb of value `1`. -/
def addUInt64 (a : AzNat) (b : UInt64) : AzNat :=
  if a.limbs.size = 0 then b.toAzNat
  else
    let r := addLimb a.limbs 0 a.limbs.size b (Nat.zero_le _) (Nat.le_refl _)
    if r.2 then ofLimbs (r.1.push 1)
    else ofLimbs r.1

/-- Add two `AzNat`s.  Empty operands return the other directly; otherwise
    `addLimbs` runs over the limb arrays and the carry bit (if any) is
    appended as a new high limb of value `1`. -/
def add (a b : AzNat) : AzNat :=
  if ha : a.limbs.size = 0 then b
  else if hb : b.limbs.size = 0 then a
  else
    let r := addLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
              (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
              (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
    if r.2 then ofLimbs (r.1.push 1)
    else ofLimbs r.1

instance : Add AzNat := ⟨add⟩

end Azurite.AzNat
