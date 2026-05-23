import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.MulWithCarry
import Azurite.UInt64.MulAddWithCarry

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

/-- Fused multiply-accumulate loop: adds `a[offA : offA + lenA] * b` into
    `acc[offAcc : offAcc + lenA]` in place, using `mulAddWithCarry` to combine
    one limb of the product with one limb of the accumulator and a running
    carry.  Returns the updated accumulator and the final carry-out. -/
def mulAddLimbs.go (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64) (k : Nat) (carry : UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    Array UInt64 × UInt64 :=
  if h : k < lenA then
    have h_iA : offA + k < a.size := by omega
    have h_iAcc : offAcc + k < acc.size := by omega
    let mac := UInt64.mulAddWithCarry a[offA + k] b acc[offAcc + k] carry
    mulAddLimbs.go a offA lenA offAcc b (acc.set (offAcc + k) mac.2) (k + 1) mac.1
      hA (by rw [Array.size_set]; exact hAcc)
  else
    (acc, carry)
  termination_by lenA - k

/-- Entry point for `mulAddLimbs.go`: starts with `k = 0`, `carry = 0`. -/
def mulAddLimbs (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    Array UInt64 × UInt64 :=
  mulAddLimbs.go a offA lenA offAcc b acc 0 0 hA hAcc

/-- Size preservation of `mulAddLimbs.go`. -/
theorem mulAddLimbs.go_size (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64) (k : Nat) (carry : UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    (mulAddLimbs.go a offA lenA offAcc b acc k carry hA hAcc).1.size = acc.size := by
  induction h_sub : lenA - k generalizing acc k carry with
  | zero =>
    have h_ge : lenA ≤ k := by omega
    rw [mulAddLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < lenA := by omega
    rw [mulAddLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ (by omega), Array.size_set]

/-- Size preservation of `mulAddLimbs`. -/
theorem mulAddLimbs_size (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size) :
    (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.size = acc.size :=
  mulAddLimbs.go_size a offA lenA offAcc b acc 0 0 hA hAcc

/-- Outer loop of naive schoolbook multiplication over slices.  For each
    `j ∈ [0, lenB)`, runs `mulAddLimbs` to add `a[loA : loA + lenA] * b[loB + j]`
    into `acc[j : j + lenA]`, then stores the final carry into `acc[j + lenA]`.
    The accumulator `acc` is written at offset `0..lenA + lenB` (caller supplies
    a fresh buffer). -/
def schoolbookMulLimbs.go (a : Array UInt64) (loA lenA : Nat) (b : Array UInt64)
    (loB lenB : Nat) (acc : Array UInt64) (j : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (hAcc : lenA + lenB ≤ acc.size) : Array UInt64 :=
  if h : j < lenB then
    have hBj : loB + j < b.size := by omega
    have hAcc_row : j + lenA ≤ acc.size := by omega
    let r := mulAddLimbs a loA lenA j b[loB + j] acc hA hAcc_row
    have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
    have hCarryIdx : j + lenA < r.1.size := by rw [h_r_size]; omega
    schoolbookMulLimbs.go a loA lenA b loB lenB (r.1.set (j + lenA) r.2) (j + 1) hA hB
      (by rw [Array.size_set, h_r_size]; exact hAcc)
  else
    acc
  termination_by lenB - j

/-- Naive `O(lenA · lenB)` schoolbook multiplication of two slices, producing
    a fresh array of size `lenA + lenB`. -/
def schoolbookMulLimbs (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  schoolbookMulLimbs.go a loA lenA b loB lenB
    (Array.replicate (lenA + lenB) 0) 0 hA hB
    (by rw [Array.size_replicate])

/-- Size preservation of `schoolbookMulLimbs.go`: the accumulator's size is
    unchanged by the outer loop. -/
theorem schoolbookMulLimbs.go_size (a : Array UInt64) (loA lenA : Nat) (b : Array UInt64)
    (loB lenB : Nat) (acc : Array UInt64) (j : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (hAcc : lenA + lenB ≤ acc.size) :
    (schoolbookMulLimbs.go a loA lenA b loB lenB acc j hA hB hAcc).size = acc.size := by
  induction h_sub : lenB - j generalizing acc j with
  | zero =>
    have h_ge : lenB ≤ j := by omega
    rw [schoolbookMulLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : j < lenB := by omega
    have h_new : lenB - (j + 1) = n := by omega
    rw [schoolbookMulLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ h_new, Array.size_set, mulAddLimbs_size]

/-- Schoolbook multiplication produces a `lenA + lenB` limb result. -/
theorem schoolbookMulLimbs_size (a b : Array UInt64) (loA lenA loB lenB : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) :
    (schoolbookMulLimbs a b loA lenA loB lenB hA hB).size = lenA + lenB := by
  unfold schoolbookMulLimbs
  rw [schoolbookMulLimbs.go_size, Array.size_replicate]

end Azurite.AzNat
