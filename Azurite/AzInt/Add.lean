import Azurite.AzInt.Basic
import Azurite.AzInt.Conversion
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Compare

namespace Azurite.AzInt

/-- Smart constructor: normalizes the zero case so the `zero_sign` invariant
    holds for any input sign.  Use only when both `s` may be `false` and
    `a` may be zero — otherwise prefer `AzNat.toAzInt` (true sign) or
    `mkNonzero` (nonzero magnitude). -/
def mkNorm (s : Bool) (a : AzNat) : AzInt :=
  if h : a = 0 then ⟨true, 0, fun _ => rfl⟩
  else ⟨s, a, fun h' => absurd h' h⟩

/-- Construct an `AzInt` with explicit sign, given a proof that the magnitude
    is nonzero (so the `zero_sign` invariant holds vacuously). -/
def mkNonzero (s : Bool) (a : AzNat) (h : a ≠ 0) : AzInt :=
  ⟨s, a, fun h' => absurd h' h⟩

/-- Add a `UInt64` `u` to an `AzInt` `z`. -/
def addUInt64 (z : AzInt) (u : UInt64) : AzInt :=
  if z.sign then
    (z.abs.addUInt64 u).toAzInt
  else
    match h_cmp : z.abs.compareUInt64 u with
    | .lt => (u.toAzNat - z.abs).toAzInt
    | .eq => 0
    | .gt =>
      have h_gt : u.toNat < z.abs.toNat := by
        have h := AzNat.compareUInt64_eq z.abs u
        rw [h_cmp] at h; exact Nat.compare_eq_gt.mp h.symm
      mkNonzero false (z.abs.subUInt64 u) (by
        intro hc
        have hc' : (z.abs.subUInt64 u).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_subUInt64] at hc'; omega)

/-- Add two `AzInt`s. -/
def add (a b : AzInt) : AzInt :=
  if hsa : a.sign then
    if hsb : b.sign then (a.abs + b.abs).toAzInt
    else
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
  else
    have hanz : a.abs ≠ 0 := fun h0 => by
      rw [a.zero_sign h0] at hsa; contradiction
    if hsb : b.sign then
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
    else
      mkNonzero false (a.abs + b.abs) (by
        intro hc
        have : (a.abs + b.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_add] at this
        have h_az : a.abs.toNat = 0 := by omega
        exact hanz (AzNat.toNat_injective (by rw [h_az, AzNat.toNat_zero])))

instance : Add AzInt := ⟨add⟩

/-- Negation of an `AzInt`: flip the sign, preserving the `zero_sign`
    invariant via `mkNorm`. -/
def neg (z : AzInt) : AzInt := mkNorm (!z.sign) z.abs

instance : Neg AzInt := ⟨neg⟩

end Azurite.AzInt
