import Azurite.AzNat.Conversion
import Azurite.AzNat.Equiv.Basic

theorem UInt64.toNat_toAzNat (u : UInt64) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt64.toAzNat
  by_cases h : u = 0
  · simp [h, Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]
  · simp [h, Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]

theorem UInt32.toNat_toAzNat (u : UInt32) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt32.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem UInt16.toNat_toAzNat (u : UInt16) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt16.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem UInt8.toNat_toAzNat (u : UInt8) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt8.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem USize.toNat_toAzNat (u : USize) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold USize.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

theorem Int64.toNat_toAzNatClampNeg (i : Int64) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int64.toAzNatClampNeg
  split
  · rename_i h
    have h1 : i.toBitVec.slt 0 = true := h
    have h2 : decide (i.toBitVec.toInt < 0) = true := h1
    have h3 : i.toInt < 0 := of_decide_eq_true h2
    simp [Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]
    change 0 = i.toInt.toNat
    omega
  · rename_i h
    rw [UInt64.toNat_toAzNat]
    have h1 : ¬(i.toBitVec.slt 0 = true) := h
    have h2 : ¬(decide (i.toBitVec.toInt < 0) = true) := h1
    have h3 : ¬(i.toInt < 0) := fun hc => h2 (decide_eq_true hc)
    have h4 : 0 ≤ i.toInt := by exact Int.not_lt.mp h3
    change i.toBitVec.toNat = i.toInt.toNat
    have h_toInt : i.toInt = if 2 * i.toBitVec.toNat < 2 ^ 64 then (i.toBitVec.toNat : ℤ) else (i.toBitVec.toNat : ℤ) - (2 ^ 64 : ℤ) := rfl
    have isLt := i.toBitVec.isLt
    omega

theorem Int32.toNat_toAzNatClampNeg (i : Int32) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int32.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int32.toInt_toInt64]

theorem Int16.toNat_toAzNatClampNeg (i : Int16) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int16.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int16.toInt_toInt64]

theorem Int8.toNat_toAzNatClampNeg (i : Int8) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int8.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int8.toInt_toInt64]

theorem ISize.toNat_toAzNatClampNeg (i : ISize) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold ISize.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [ISize.toInt_toInt64]

theorem UInt64.ofNat_toNat_eq_toAzNat (u : UInt64) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt64.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem UInt32.ofNat_toNat_eq_toAzNat (u : UInt32) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt32.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem UInt16.ofNat_toNat_eq_toAzNat (u : UInt16) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt16.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem UInt8.ofNat_toNat_eq_toAzNat (u : UInt8) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt8.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem USize.ofNat_toNat_eq_toAzNat (u : USize) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← USize.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

theorem Int64.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int64) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int64.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem Int32.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int32) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int32.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem Int16.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int16) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int16.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem Int8.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int8) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int8.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

theorem ISize.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : ISize) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← ISize.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]
