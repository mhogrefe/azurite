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

/-- Recursive helper for `subSameLengthLimbs`: processes positions
    `loA + k .. loA + len` and `loB + k .. loB + len` simultaneously. -/
def subSameLengthLimbs.go (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    Array UInt64 × Bool :=
  if h : k < len then
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    let swb := UInt64.subWithBorrow a[loA + k] b[loB + k] borrow
    subSameLengthLimbs.go b loA loB len (a.set (loA + k) swb.1) (k + 1) swb.2
      (by rw [Array.size_set]; exact hA) hB
  else
    (a, borrow)
  termination_by len - k

/-- Subtract the slice `b[loB : loB + len)` from `a[loA : loA + len)` in place.
    Returns the modified array `a` and the final borrow-out of the high end. -/
def subSameLengthLimbs (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    Array UInt64 × Bool :=
  subSameLengthLimbs.go b loA loB len a 0 false hA hB

/-- Size preservation of `subSameLengthLimbs.go`. -/
theorem subSameLengthLimbs.go_size (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (subSameLengthLimbs.go b loA loB len a k borrow hA hB).1.size = a.size := by
  induction h_sub : len - k generalizing a k borrow with
  | zero =>
    have h_ge : len ≤ k := by omega
    rw [subSameLengthLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    rw [subSameLengthLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega), Array.size_set]

/-- Size preservation of `subSameLengthLimbs`. -/
theorem subSameLengthLimbs_size (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    (subSameLengthLimbs a b loA loB len hA hB).1.size = a.size :=
  subSameLengthLimbs.go_size b loA loB len a 0 false hA hB

/-- Subtract the slice `b[loB : loB + lenB)` from `a[loA : loA + lenA)` where
    `lenB ≤ lenA` and both slices are nonempty.  Low `lenB` limbs are subtracted
    via `subSameLengthLimbs`; any outgoing borrow is propagated into the upper
    `lenA - lenB` limbs of `a` via `subLimb`.  Returns the modified array and
    the final high borrow-out. -/
def subGeqLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (_h_posA : 0 < lenA) (_h_posB : 0 < lenB) :
    Array UInt64 × Bool :=
  let lo := subSameLengthLimbs a b loA loB lenB (by omega) hB
  if lo.2 then
    subLimb lo.1 (loA + lenB) (loA + lenA) 1 (by omega)
      (by rw [subSameLengthLimbs_size]; exact hA)
  else
    (lo.1, false)

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

/-- Subtract `b` from `a` in `AzNat` (truncated: returns `0` if `b > a`).
    Empty `a` returns `0`; empty `b` returns `a`; if `b` has strictly more
    limbs than `a` then `b > a` (since `AzNat` has no trailing zeros), so the
    result is `0`.  Otherwise `subGeqLimbs` runs over the limb arrays and a
    final borrow indicates `a < b`, so the result is `0`; else the trimmed
    limbs form the result. -/
def sub (a b : AzNat) : AzNat :=
  if ha : a.limbs.size = 0 then 0
  else if hb : b.limbs.size = 0 then a
  else if hgt : b.limbs.size > a.limbs.size then 0
  else
    let r := subGeqLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
              (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _)
              (Nat.not_lt.mp hgt)
              (Nat.pos_of_ne_zero ha)
              (Nat.pos_of_ne_zero hb)
    if r.2 then 0
    else ofLimbs r.1

instance : Sub AzNat := ⟨sub⟩

end Azurite.AzNat
