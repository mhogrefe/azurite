import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.SubWithBorrow

namespace Azurite.AzNat

/-- Recursive helper for `subLimb`: processes positions `i .. hi` propagating
    the running `borrow`. -/
def subLimb.go (hi : Nat) (a : Array UInt64) (i : Nat) (borrow : UInt64)
    (h_size : hi ≤ a.size) : Array UInt64 × Bool :=
  if borrow = 0 then
    (a, false)
  else if h : i < hi then
    have h_i_size : i < a.size := Nat.lt_of_lt_of_le h h_size
    let x := a[i]
    let diff := x - borrow
    let newBorrow : UInt64 := if x < borrow then 1 else 0
    subLimb.go hi (a.set i diff) (i + 1) newBorrow
      (by rw [Array.size_set]; exact h_size)
  else
    (a, true)
  termination_by hi - i

/-- Subtract a single limb `b` from the subrange `a[lo:hi)`, propagating
    borrow upward.  Returns the modified array (mutated in place when
    possible) and a boolean borrow out of the high end.  When the running
    borrow becomes zero, the remaining limbs are left untouched. -/
def subLimb (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size) : Array UInt64 × Bool :=
  subLimb.go hi a lo b hhi

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

/-- Size preservation of `subLimb.go`. -/
theorem subLimb.go_size (hi : Nat) (a : Array UInt64) (i : Nat) (borrow : UInt64)
    (h_size : hi ≤ a.size) :
    (subLimb.go hi a i borrow h_size).1.size = a.size := by
  induction h_sub : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [subLimb.go]
    by_cases h_borrow : borrow = 0
    · simp [h_borrow]
    · simp [h_borrow, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    rw [subLimb.go]
    by_cases h_borrow : borrow = 0
    · simp [h_borrow]
    · have h_new : hi - (i + 1) = n := by omega
      simp only [h_borrow, ↓reduceIte, h_lt, ↓reduceDIte]
      rw [ih _ _ _ _ h_new, Array.size_set]

/-- Size preservation of `subLimb`. -/
theorem subLimb_size (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) :
    (subLimb a lo hi b hlo hhi).1.size = a.size :=
  subLimb.go_size hi a lo b hhi

/-- Positions below the recursion's current index `i` are unchanged by
    `subLimb.go`. -/
theorem subLimb.go_get_below (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size) (j : Nat) (h_j : j < i)
    (h_j_size : j < a.size) :
    (subLimb.go hi a i borrow h_size).1[j]'(by
      rw [subLimb.go_size]; exact h_j_size) = a[j] := by
  induction h_sub : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    unfold subLimb.go
    by_cases h_borrow : borrow = 0
    · simp [h_borrow]
    · simp [h_borrow, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    unfold subLimb.go
    by_cases h_borrow : borrow = 0
    · simp [h_borrow]
    · have h_new : hi - (i + 1) = n := by omega
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
      simp only [h_borrow, ↓reduceIte, h_lt, ↓reduceDIte]
      rw [ih (a.set i (a[i] - borrow)) (i + 1)
        (if a[i] < borrow then 1 else 0)
        (by rw [Array.size_set]; exact h_size) (by omega)
        (by rw [Array.size_set]; exact h_j_size) h_new]
      rw [Array.getElem_set]
      have h_ne : i ≠ j := by omega
      simp [h_ne]

/-- Positions at or above `hi` are unchanged by `subLimb.go`. -/
theorem subLimb.go_get_above (hi : Nat) (a : Array UInt64) (i : Nat)
    (borrow : UInt64) (h_size : hi ≤ a.size) (j : Nat) (h_j : hi ≤ j)
    (h_j_size : j < a.size) :
    (subLimb.go hi a i borrow h_size).1[j]'(by
      rw [subLimb.go_size]; exact h_j_size) = a[j] := by
  induction h_sub : hi - i generalizing a i borrow with
  | zero =>
    have h_ge : hi ≤ i := by omega
    unfold subLimb.go
    by_cases h_borrow : borrow = 0
    · simp [h_borrow]
    · simp [h_borrow, Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    unfold subLimb.go
    by_cases h_borrow : borrow = 0
    · simp [h_borrow]
    · have h_new : hi - (i + 1) = n := by omega
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h_lt h_size
      simp only [h_borrow, ↓reduceIte, h_lt, ↓reduceDIte]
      rw [ih (a.set i (a[i] - borrow)) (i + 1)
        (if a[i] < borrow then 1 else 0)
        (by rw [Array.size_set]; exact h_size)
        (by rw [Array.size_set]; exact h_j_size) h_new]
      rw [Array.getElem_set]
      have h_ne : i ≠ j := by omega
      simp [h_ne]

/-- Positions strictly below `lo` are unchanged by `subLimb`. -/
theorem subLimb_get_below (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (j : Nat) (h_j : j < lo)
    (h_j_size : j < a.size) :
    (subLimb a lo hi b hlo hhi).1[j]'(by
      rw [subLimb_size]; exact h_j_size) = a[j] :=
  subLimb.go_get_below hi a lo b hhi j h_j h_j_size

/-- Positions at or above `hi` are unchanged by `subLimb`. -/
theorem subLimb_get_above (a : Array UInt64) (lo hi : Nat) (b : UInt64)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size) (j : Nat) (h_j : hi ≤ j)
    (h_j_size : j < a.size) :
    (subLimb a lo hi b hlo hhi).1[j]'(by
      rw [subLimb_size]; exact h_j_size) = a[j] :=
  subLimb.go_get_above hi a lo b hhi j h_j h_j_size

/-- `subSameLengthLimbs.go` preserves positions outside `[loA + k, loA + len)`. -/
theorem subSameLengthLimbs.go_get_outside (b : Array UInt64) (loA loB len : Nat)
    (a : Array UInt64) (k : Nat) (borrow : Bool)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) (j : Nat)
    (h_j : j < loA + k ∨ loA + len ≤ j) (h_j_size : j < a.size) :
    (subSameLengthLimbs.go b loA loB len a k borrow hA hB).1[j]'(by
      rw [subSameLengthLimbs.go_size]; exact h_j_size) = a[j] := by
  induction h_sub : len - k generalizing a k borrow with
  | zero =>
    have h_ge : len ≤ k := by omega
    unfold subSameLengthLimbs.go
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < len := by omega
    unfold subSameLengthLimbs.go
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

/-- `subSameLengthLimbs` preserves positions outside `[loA, loA + len)`. -/
theorem subSameLengthLimbs_get_outside (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) (j : Nat)
    (h_j : j < loA ∨ loA + len ≤ j) (h_j_size : j < a.size) :
    (subSameLengthLimbs a b loA loB len hA hB).1[j]'(by
      rw [subSameLengthLimbs_size]; exact h_j_size) = a[j] := by
  have h_j' : j < loA + 0 ∨ loA + len ≤ j := by
    rcases h_j with h | h
    · left; omega
    · right; exact h
  exact subSameLengthLimbs.go_get_outside b loA loB len a 0 false hA hB j h_j' h_j_size

/-- Size preservation of `subGeqLimbs`. -/
theorem subGeqLimbs_size (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB) :
    (subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1.size = a.size := by
  unfold subGeqLimbs
  by_cases h : (subSameLengthLimbs a b loA loB lenB (by omega) hB).2 = true
  · rw [if_pos h, subLimb_size, subSameLengthLimbs_size]
  · rw [if_neg h, subSameLengthLimbs_size]

/-- `subGeqLimbs` preserves positions outside `[loA, loA + lenA)`. -/
theorem subGeqLimbs_get_outside (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (h_ge : lenB ≤ lenA) (h_posA : 0 < lenA) (h_posB : 0 < lenB) (j : Nat)
    (h_j : j < loA ∨ loA + lenA ≤ j) (h_j_size : j < a.size) :
    (subGeqLimbs a b loA lenA loB lenB hA hB h_ge h_posA h_posB).1[j]'(by
      rw [subGeqLimbs_size]; exact h_j_size) = a[j] := by
  -- Both `subSameLengthLimbs` (modifies [loA, loA+lenB)) and `subLimb`
  -- (modifies [loA+lenB, loA+lenA)) leave positions outside [loA, loA+lenA)
  -- untouched.  Pre-derive the weaker hypothesis for subSameLengthLimbs.
  have h_j_inner : j < loA ∨ loA + lenB ≤ j := by
    rcases h_j with h | h
    · left; exact h
    · right; omega
  unfold subGeqLimbs
  simp only
  by_cases h_bor : (subSameLengthLimbs a b loA loB lenB (by omega) hB).2 = true
  · simp only [h_bor, ↓reduceIte]
    have h_sub_j : j < loA + lenB ∨ loA + lenA ≤ j := by
      rcases h_j with h | h
      · left; omega
      · right; exact h
    rcases h_sub_j with h_below | h_above
    · rw [subLimb_get_below _ _ _ _ _ _ j h_below
        (by rw [subSameLengthLimbs_size]; exact h_j_size)]
      exact subSameLengthLimbs_get_outside a b loA loB lenB (by omega) hB j
        h_j_inner h_j_size
    · rw [subLimb_get_above _ _ _ _ _ _ j h_above
        (by rw [subSameLengthLimbs_size]; exact h_j_size)]
      exact subSameLengthLimbs_get_outside a b loA loB lenB (by omega) hB j
        h_j_inner h_j_size
  · set_option linter.unusedSimpArgs false in
    simp only [h_bor, ↓reduceIte]
    exact subSameLengthLimbs_get_outside a b loA loB lenB (by omega) hB j
      h_j_inner h_j_size

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
