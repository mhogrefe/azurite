import Azurite.AzInt.Add

namespace Azurite.AzInt

/-- Subtract a `UInt64` `u` from an `AzInt` `z`. -/
def subUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  if hs : z.sign then
    match h_cmp : z.abs.compareUInt64 u with
    | .lt =>
      have h_lt : z.abs.toNat < u.toNat := by
        have h := AzNat.compareUInt64_eq z.abs u
        rw [h_cmp] at h; exact Nat.compare_eq_lt.mp h.symm
      mkNonzero false (u.toAzNat - z.abs) (by
        intro hc
        have hc' : (u.toAzNat - z.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_sub, UInt64.toNat_toAzNat] at hc'; omega)
    | .eq => 0
    | .gt => (z.abs.subUInt64 u).toAzInt
  else
    have h_abs_ne : z.abs ≠ 0 := fun h0 => by
      rw [z.zero_sign h0] at hs; contradiction
    have h_abs_pos : 0 < z.abs.toNat := by
      rcases Nat.eq_zero_or_pos z.abs.toNat with h | h
      · exact absurd
          (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero])) h_abs_ne
      · exact h
    mkNonzero false (z.abs.addUInt64 u) (by
      intro hc
      have hc' : (z.abs.addUInt64 u).toNat = 0 := by rw [hc]; rfl
      rw [AzNat.toNat_addUInt64] at hc'; omega)

/-- Add an `Int64` `i` to an `AzInt` `z`. -/
def addInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then z.addUInt64 i.toUInt64 else z.subUInt64 (-i).toUInt64

/-- Subtract an `Int64` `i` from an `AzInt` `z`. -/
def subInt64 (z : AzInt) (i : Int64) : AzInt :=
  if i ≥ 0 then z.subUInt64 i.toUInt64 else z.addUInt64 (-i).toUInt64

/-- Subtract `b` from `a` in `AzInt`. -/
def sub (a b : AzInt) : AzInt :=
  if hsa : a.sign then
    if hsb : b.sign then
      match h_cmp : AzNat.compare a.abs b.abs with
      | .lt =>
        have h_lt : a.abs.toNat < b.abs.toNat := by
          have := AzNat.compare_eq_compare_toNat a.abs b.abs
          rw [h_cmp] at this; exact Nat.compare_eq_lt.mp this.symm
        mkNonzero false (b.abs - a.abs) (by
          intro hc
          have : (b.abs - a.abs).toNat = 0 := by rw [hc]; rfl
          rw [AzNat.toNat_sub] at this; omega)
      | .eq => 0
      | .gt => (a.abs - b.abs).toAzInt
    else (a.abs + b.abs).toAzInt
  else
    have hanz : a.abs ≠ 0 := fun h0 => by
      rw [a.zero_sign h0] at hsa; contradiction
    if hsb : b.sign then
      mkNonzero false (a.abs + b.abs) (by
        intro hc
        have : (a.abs + b.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_add] at this
        have h_az : a.abs.toNat = 0 := by omega
        exact hanz (AzNat.toNat_injective (by rw [h_az, AzNat.toNat_zero])))
    else
      match h_cmp : AzNat.compare a.abs b.abs with
      | .lt => (b.abs - a.abs).toAzInt
      | .eq => 0
      | .gt =>
        have h_gt : b.abs.toNat < a.abs.toNat := by
          have := AzNat.compare_eq_compare_toNat a.abs b.abs
          rw [h_cmp] at this; exact Nat.compare_eq_gt.mp this.symm
        mkNonzero false (a.abs - b.abs) (by
          intro hc
          have : (a.abs - b.abs).toNat = 0 := by rw [hc]; rfl
          rw [AzNat.toNat_sub] at this; omega)

instance : Sub AzInt := ⟨sub⟩

end Azurite.AzInt
