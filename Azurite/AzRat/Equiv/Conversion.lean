import Azurite.AzRat.Conversion
import Azurite.AzRat.Equiv.Basic
import Azurite.AzInt.Equiv.Conversion

/-!
# Equivalence: conversions into `AzRat`

Correctness of the conversions into `AzRat`: the rational represented by `n.toAzRat` is
`(n.toNat : ℚ)`, the one for `z.toAzRat` is `(z.toInt : ℚ)`, and each primitive fixed-width
conversion agrees with the corresponding cast (`toNat`/`toInt`) into `ℚ`.
Mirrors `Azurite.AzNat.toInt_toAzInt` and the primitive `*.toInt_toAzInt` lemmas.
-/

namespace Azurite.AzRat

/-- The rational represented by `n.toAzRat` is `(n.toNat : ℚ)`. -/
theorem toRat_toAzRat (n : AzNat) : toRat n.toAzRat = (n.toNat : ℚ) := by
  apply Rat.ext
  · show (if (true : Bool) then (n.toNat : ℤ) else -(n.toNat : ℤ)) = ((n.toNat : ℚ)).num
    simp
  · show ((1 : AzNat).toNat : ℕ) = ((n.toNat : ℚ)).den
    rw [AzNat.toNat_one]; simp

/-- The rational represented by `z.toAzRat` is `(z.toInt : ℚ)`. -/
theorem toRat_toAzRat_int (z : AzInt) : toRat z.toAzRat = (z.toInt : ℚ) := by
  apply Rat.ext
  · show (if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ)) = ((z.toInt : ℚ)).num
    rw [Rat.num_intCast]; rfl
  · show ((1 : AzNat).toNat : ℕ) = ((z.toInt : ℚ)).den
    rw [AzNat.toNat_one]; simp

end Azurite.AzRat

/-! ### Primitive fixed-width types -/

-- Unsigned: the represented rational is the `toNat` cast.
theorem UInt64.toRat_toAzRat (u : UInt64) : Azurite.AzRat.toRat u.toAzRat = (u.toNat : ℚ) := by
  rw [UInt64.toAzRat, Azurite.AzRat.toRat_toAzRat_int, UInt64.toInt_toAzInt]; norm_cast

theorem UInt32.toRat_toAzRat (u : UInt32) : Azurite.AzRat.toRat u.toAzRat = (u.toNat : ℚ) := by
  rw [UInt32.toAzRat, Azurite.AzRat.toRat_toAzRat_int, UInt32.toInt_toAzInt]; norm_cast

theorem UInt16.toRat_toAzRat (u : UInt16) : Azurite.AzRat.toRat u.toAzRat = (u.toNat : ℚ) := by
  rw [UInt16.toAzRat, Azurite.AzRat.toRat_toAzRat_int, UInt16.toInt_toAzInt]; norm_cast

theorem UInt8.toRat_toAzRat (u : UInt8) : Azurite.AzRat.toRat u.toAzRat = (u.toNat : ℚ) := by
  rw [UInt8.toAzRat, Azurite.AzRat.toRat_toAzRat_int, UInt8.toInt_toAzInt]; norm_cast

theorem USize.toRat_toAzRat (u : USize) : Azurite.AzRat.toRat u.toAzRat = (u.toNat : ℚ) := by
  rw [USize.toAzRat, Azurite.AzRat.toRat_toAzRat_int, USize.toInt_toAzInt]; norm_cast

-- Signed: the represented rational is the `toInt` cast.
theorem Int64.toRat_toAzRat (i : Int64) : Azurite.AzRat.toRat i.toAzRat = (i.toInt : ℚ) := by
  rw [Int64.toAzRat, Azurite.AzRat.toRat_toAzRat_int, Int64.toInt_toAzInt]

theorem Int32.toRat_toAzRat (i : Int32) : Azurite.AzRat.toRat i.toAzRat = (i.toInt : ℚ) := by
  rw [Int32.toAzRat, Azurite.AzRat.toRat_toAzRat_int, Int32.toInt_toAzInt]

theorem Int16.toRat_toAzRat (i : Int16) : Azurite.AzRat.toRat i.toAzRat = (i.toInt : ℚ) := by
  rw [Int16.toAzRat, Azurite.AzRat.toRat_toAzRat_int, Int16.toInt_toAzInt]

theorem Int8.toRat_toAzRat (i : Int8) : Azurite.AzRat.toRat i.toAzRat = (i.toInt : ℚ) := by
  rw [Int8.toAzRat, Azurite.AzRat.toRat_toAzRat_int, Int8.toInt_toAzInt]

theorem ISize.toRat_toAzRat (i : ISize) : Azurite.AzRat.toRat i.toAzRat = (i.toInt : ℚ) := by
  rw [ISize.toAzRat, Azurite.AzRat.toRat_toAzRat_int, ISize.toInt_toAzInt]

-- The conversions compute.
#guard Azurite.AzRat.toRat (Azurite.AzNat.ofNat 7).toAzRat == (7 : ℚ)
#guard Azurite.AzRat.toRat (Azurite.AzInt.ofInt (-5)).toAzRat == (-5 : ℚ)
#guard Azurite.AzRat.toRat (200 : UInt8).toAzRat == (200 : ℚ)
#guard Azurite.AzRat.toRat (-13 : Int64).toAzRat == (-13 : ℚ)
