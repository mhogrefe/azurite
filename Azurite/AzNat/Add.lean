import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.AddWithCarry

namespace Azurite.AzNat

/-- Recursive helper for `addLimb`: processes positions `i .. hi` propagating
    the running `carry`. -/
def addLimb.go (hi : Nat) (a : Array UInt64) (i : Nat) (carry : UInt64)
    (h_size : hi ≤ a.size) : Array UInt64 × Bool :=
  if carry = 0 then
    (a, false)
  else if h : i < hi then
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h h_size
    let x := a[i]
    let sum := x + carry
    let newCarry : UInt64 := if sum < carry then 1 else 0
    addLimb.go hi (a.set i sum) (i + 1) newCarry
      (by rw [Array.size_set]; exact h_size)
  else
    (a, true)
  termination_by hi - i

/-- Add a single limb `b` into the subrange `a[lo:hi)`, propagating carry
    upward.  Returns the modified array (mutated in place when possible)
    and a boolean carry out of the high end.  When the running carry
    becomes zero, the remaining limbs are left untouched. -/
def addLimb (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × Bool :=
  addLimb.go hi a lo b hhi

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

/-- Size preservation of `addLimb.go`. -/
theorem addLimb.go_size (hi : Nat) (a : Array UInt64) (i : Nat) (carry : UInt64)
    (h_size : hi ≤ a.size) :
    (addLimb.go hi a i carry h_size).1.size = a.size := by
  induction h_sub : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [addLimb.go]
    by_cases h_carry : carry = 0
    · simp [h_carry]
    · simp [h_carry, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    rw [addLimb.go]
    by_cases h_carry : carry = 0
    · simp [h_carry]
    · have h_new : hi - (i + 1) = n := by omega
      simp only [h_carry, ↓reduceIte, h_lt, ↓reduceDIte]
      rw [ih _ _ _ _ h_new, Array.size_set]

/-- Size preservation of `addLimb`. -/
theorem addLimb_size (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (addLimb a lo hi b hlo hhi).1.size = a.size :=
  addLimb.go_size hi a lo b hhi

/-- Positions below the recursion's current index `i` are unchanged by
    `addLimb.go`.  Used to show `addLimb` leaves low limbs intact. -/
theorem addLimb.go_get_below (hi : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) (j : Nat) (h_j : j < i)
    (h_j_size : j < a.size) :
    (addLimb.go hi a i carry h_size).1[j]'(by
      rw [addLimb.go_size]; exact h_j_size) = a[j] := by
  induction h_sub : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    unfold addLimb.go
    by_cases h_carry : carry = 0
    · simp [h_carry]
    · simp [h_carry, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    unfold addLimb.go
    by_cases h_carry : carry = 0
    · simp [h_carry]
    · have h_new : hi - (i + 1) = n := by omega
      have h_j' : j < i + 1 := by omega
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
      simp only [h_carry, ↓reduceIte, h_lt, ↓reduceDIte]
      rw [ih (a.set i (a[i] + carry)) (i + 1)
        (if a[i] + carry < carry then 1 else 0)
        (by rw [Array.size_set]; exact h_size) h_j'
        (by rw [Array.size_set]; exact h_j_size) h_new]
      rw [Array.getElem_set]
      have h_ne : i ≠ j := by omega
      simp [h_ne]

/-- Positions strictly below `lo` are unchanged by `addLimb`. -/
theorem addLimb_get_below (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (j : Nat) (h_j : j < lo)
    (h_j_size : j < a.size) :
    (addLimb a lo hi b hlo hhi).1[j]'(by
      rw [addLimb_size]; exact h_j_size) = a[j] :=
  addLimb.go_get_below hi a lo b hhi j h_j h_j_size

/-- Positions at or above `hi` are unchanged by `addLimb.go`. -/
theorem addLimb.go_get_above (hi : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) (j : Nat) (h_j : hi ≤ j)
    (h_j_size : j < a.size) :
    (addLimb.go hi a i carry h_size).1[j]'(by
      rw [addLimb.go_size]; exact h_j_size) = a[j] := by
  induction h_sub : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    unfold addLimb.go
    by_cases h_carry : carry = 0
    · simp [h_carry]
    · simp [h_carry, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    unfold addLimb.go
    by_cases h_carry : carry = 0
    · simp [h_carry]
    · have h_new : hi - (i + 1) = n := by omega
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
      simp only [h_carry, ↓reduceIte, h_lt, ↓reduceDIte]
      rw [ih (a.set i (a[i] + carry)) (i + 1)
        (if a[i] + carry < carry then 1 else 0)
        (by rw [Array.size_set]; exact h_size)
        (by rw [Array.size_set]; exact h_j_size) h_new]
      rw [Array.getElem_set]
      have h_ne : i ≠ j := by omega
      simp [h_ne]

/-- Positions at or above `hi` are unchanged by `addLimb`. -/
theorem addLimb_get_above (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (j : Nat) (h_j : hi ≤ j)
    (h_j_size : j < a.size) :
    (addLimb a lo hi b hlo hhi).1[j]'(by
      rw [addLimb_size]; exact h_j_size) = a[j] :=
  addLimb.go_get_above hi a lo b hhi j h_j h_j_size

/-- `addSameLengthLimbs.go` preserves positions outside `[loA + k, loA + len)`. -/
theorem addSameLengthLimbs.go_get_outside (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (carry : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) (j : Nat)
    (h_j : j < loA + k ∨ loA + len ≤ j) (h_j_size : j < a.size) :
    (addSameLengthLimbs.go b loA loB len a k carry hA hB).1[j]'(by
      rw [addSameLengthLimbs.go_size]; exact h_j_size) = a[j] := by
  induction h_sub : len - k generalizing a k carry with
  | zero =>
    have h_ge : len ≤ k := by omega
    unfold addSameLengthLimbs.go
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    unfold addSameLengthLimbs.go
    simp only [h_lt, ↓reduceDIte]
    have h_iA : loA + k < a.size := by omega
    have h_iB : loB + k < b.size := by omega
    have h_j' : j < loA + (k + 1) ∨ loA + len ≤ j := by
      rcases h_j with h | h
      · left; omega
      · right; exact h
    rw [ih _ (k + 1) _
      (by rw [Array.size_set]; exact hA) h_j'
      (by rw [Array.size_set]; exact h_j_size) (by omega)]
    rw [Array.getElem_set]
    have h_ne : loA + k ≠ j := by
      rcases h_j with h | h
      · omega
      · omega
    simp [h_ne]

/-- `addSameLengthLimbs` preserves positions outside `[loA, loA + len)`. -/
theorem addSameLengthLimbs_get_outside (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) (j : Nat)
    (h_j : j < loA ∨ loA + len ≤ j) (h_j_size : j < a.size) :
    (addSameLengthLimbs a b loA loB len hA hB).1[j]'(by
      rw [addSameLengthLimbs_size]; exact h_j_size) = a[j] := by
  have h_j' : j < loA + 0 ∨ loA + len ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; exact h
  exact addSameLengthLimbs.go_get_outside b loA loB len a 0 false hA hB j h_j' h_j_size

/-- Size preservation of `addGeqLimbs`. -/
theorem addGeqLimbs_size (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB) :
    (addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1.size = a.size := by
  unfold addGeqLimbs
  by_cases h : (addSameLengthLimbs a b loA loB lenB (by omega) hB).2 = true
  · rw [if_pos h, addLimb_size, addSameLengthLimbs_size]
  · rw [if_neg h, addSameLengthLimbs_size]

/-- `addGeqLimbs` preserves positions outside `[loA, loA + lenA)`. -/
theorem addGeqLimbs_get_outside (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB) (j : Nat)
    (h_j : j < loA ∨ loA + lenA ≤ j) (h_j_size : j < a.size) :
    (addGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1[j]'(by
      rw [addGeqLimbs_size]; exact h_j_size) = a[j] := by
  have h_j_inner : j < loA ∨ loA + lenB ≤ j := by
    rcases h_j with h | h
    · left; exact h
    · right; omega
  unfold addGeqLimbs
  simp only
  by_cases h_car : (addSameLengthLimbs a b loA loB lenB (by omega) hB).2 = true
  · simp only [h_car, ↓reduceIte]
    have h_sub_j : j < loA + lenB ∨ loA + lenA ≤ j := by
      rcases h_j with h | h
      · left; omega
      · right; exact h
    rcases h_sub_j with h_below | h_above
    · rw [addLimb_get_below _ _ _ _ _ _ j h_below
        (by rw [addSameLengthLimbs_size]; exact h_j_size)]
      exact addSameLengthLimbs_get_outside a b loA loB lenB (by omega) hB j
        h_j_inner h_j_size
    · rw [addLimb_get_above _ _ _ _ _ _ j h_above
        (by rw [addSameLengthLimbs_size]; exact h_j_size)]
      exact addSameLengthLimbs_get_outside a b loA loB lenB (by omega) hB j
        h_j_inner h_j_size
  · set_option linter.unusedSimpArgs false in
    simp only [h_car, ↓reduceIte]
    exact addSameLengthLimbs_get_outside a b loA loB lenB (by omega) hB j
      h_j_inner h_j_size

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
