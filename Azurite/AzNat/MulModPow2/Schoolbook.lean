import Azurite.AzNat.Mul.Schoolbook
import Azurite.AzNat.ModPow2
import Azurite.AzNat.ParseBase

/-!
## `AzNat.mulSchoolbookModPow2` — low (mod `2 ^ k`) schoolbook multiplication

To compute `(a * b) mod 2 ^ k` we only need the low `L = (k + 63) / 64` limbs of
the product, so the upper half of the schoolbook rectangle is never formed.

The outer loop runs the same multiply-accumulate rows as `schoolbookMulLimbs`,
but each row `j` is **clamped** to `min lenA (L - j)` limbs so it never writes at
or past position `L`; its carry-out is stored only when it lands strictly below
`L`, and dropped otherwise (it would contribute a multiple of `2 ^ (64 * L)`,
hence `0` modulo `2 ^ (64 * L) ⊇ 2 ^ k`).  Rows with `j ≥ L` are no-ops.  When
operands fill the window this is roughly half the limb multiplications of the
full product.
-/

namespace Azurite.AzNat

/-- One row of the low schoolbook multiplication.  Clamps the row to
    `rowLen = min lenA (L - j)` limbs, multiply-accumulates
    `a[loA : loA + rowLen] * bj` into `acc[j : j + rowLen]`, and stores the
    carry-out just past the row at position `j + rowLen` — unless that position
    is `≥ L` (the carry then lies at or above `2 ^ (64 * L)` and is dropped). -/
def schoolbookMulLowRow (a : Array UInt64) (loA lenA : Nat) (bj : UInt64)
    (L j : Nat) (acc : Array UInt64)
    (hA : loA + lenA ≤ a.size) (hAcc : L ≤ acc.size) (hjL : j ≤ L) : Array UInt64 :=
  let rowLen := min lenA (L - j)
  let r := mulAddLimbs a loA rowLen j bj acc
    (by have := Nat.min_le_left lenA (L - j); omega)
    (by have := Nat.min_le_right lenA (L - j); omega)
  if h2 : j + rowLen < L then
    r.1.set (j + rowLen) r.2 (by rw [mulAddLimbs_size]; omega)
  else r.1

/-- Size preservation of `schoolbookMulLowRow`. -/
theorem schoolbookMulLowRow_size (a : Array UInt64) (loA lenA : Nat) (bj : UInt64)
    (L j : Nat) (acc : Array UInt64)
    (hA : loA + lenA ≤ a.size) (hAcc : L ≤ acc.size) (hjL : j ≤ L) :
    (schoolbookMulLowRow a loA lenA bj L j acc hA hAcc hjL).size = acc.size := by
  unfold schoolbookMulLowRow
  dsimp only
  split
  · rw [Array.size_set, mulAddLimbs_size]
  · rw [mulAddLimbs_size]

/-- Outer loop of the low schoolbook multiplication: process rows `[j, lenB)`,
    each clamped to the low `L` limbs of the accumulator. -/
def schoolbookMulLowLimbs.go (a : Array UInt64) (loA lenA : Nat) (b : Array UInt64)
    (loB lenB L : Nat) (acc : Array UInt64) (j : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size)
    (hAcc : L ≤ acc.size) : Array UInt64 :=
  if h : j < lenB ∧ j < L then
    have hBj : loB + j < b.size := by omega
    let acc' := schoolbookMulLowRow a loA lenA b[loB + j] L j acc hA hAcc (by omega)
    have hAcc' : L ≤ acc'.size := by rw [schoolbookMulLowRow_size]; exact hAcc
    schoolbookMulLowLimbs.go a loA lenA b loB lenB L acc' (j + 1) hA hB hAcc'
  else acc
  termination_by lenB - j

/-- Low `L` limbs of `a[loA : loA + lenA] * b[loB : loB + lenB]`, i.e. the
    product truncated to `2 ^ (64 * L)`.  Allocates a fresh `L`-limb buffer. -/
def schoolbookMulLowLimbs (a b : Array UInt64) (loA lenA loB lenB L : Nat)
    (hA : loA + lenA ≤ a.size) (hB : loB + lenB ≤ b.size) : Array UInt64 :=
  schoolbookMulLowLimbs.go a loA lenA b loB lenB L
    (Array.replicate L 0) 0 hA hB (by rw [Array.size_replicate])

/-- **Low (mod `2 ^ k`) schoolbook multiplication.** `(a * b) mod 2 ^ k`,
    computing only the low `L = (k + 63) / 64` limbs of the product and masking
    to the low `k` bits. -/
def mulSchoolbookModPow2 (a b : AzNat) (k : Nat) : AzNat :=
  modPow2 (ofLimbs (schoolbookMulLowLimbs a.limbs b.limbs
    0 a.limbs.size 0 b.limbs.size ((k + 63) / 64)
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))) k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def parse (s : String) : AzNat := (AzNat.parse s).get!

-- Small single-limb cases (compare to the full product reduced by hand).
-- `7 * 9 = 63`; mod 2^4 = 16 → 15.
#guard (mulSchoolbookModPow2 (parse "7") (parse "9") 4).toNat == 15
-- `13 * 11 = 143`; mod 2^4 → 15, mod 2^8 → 143.
#guard (mulSchoolbookModPow2 (parse "13") (parse "11") 4).toNat == 143 % 16
#guard (mulSchoolbookModPow2 (parse "13") (parse "11") 8).toNat == 143
-- `255 * 255 = 65025`; mod 2^8 → 1, mod 2^16 → 65025.
#guard (mulSchoolbookModPow2 (parse "255") (parse "255") 8).toNat == 65025 % 256
#guard (mulSchoolbookModPow2 (parse "255") (parse "255") 16).toNat == 65025
-- Zero / one.
#guard (mulSchoolbookModPow2 (parse "0") (parse "12345") 32).toNat == 0
#guard (mulSchoolbookModPow2 (parse "1") (parse "12345") 32).toNat == 12345

-- Multi-limb operands crossing the 64-bit boundary.
-- `(2^64 + 1) * (2^64 + 1) = 2^128 + 2^65 + 1`; mod 2^64 → 1.
#guard (mulSchoolbookModPow2 (parse "18446744073709551617")
  (parse "18446744073709551617") 64).toNat == 1
-- mod 2^128 → 2^128 + 2^65 + 1 reduced = 2^65 + 1 = 36893488147419103233.
#guard (mulSchoolbookModPow2 (parse "18446744073709551617")
  (parse "18446744073709551617") 128).toNat == 36893488147419103233
-- Full multi-limb agreement: low 200 bits of a large product.
#guard (mulSchoolbookModPow2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 200).toNat ==
  (123456789012345678901234567890 * 987654321098765432109876543210) % (2 ^ 200)
-- `k` not a multiple of 64: low 100 bits.
#guard (mulSchoolbookModPow2 (parse "123456789012345678901234567890")
  (parse "987654321098765432109876543210") 100).toNat ==
  (123456789012345678901234567890 * 987654321098765432109876543210) % (2 ^ 100)
-- `k = 0`: everything collapses to 0.
#guard (mulSchoolbookModPow2 (parse "123456789") (parse "987654321") 0).toNat == 0

end Tests
