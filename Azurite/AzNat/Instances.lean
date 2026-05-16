import Azurite.AzNat.Equiv.Mul.Karatsuba

namespace Azurite.AzNat

instance : CommSemiring AzNat where
  add_assoc a b c := toNat_injective (by simp [toNat_add, Nat.add_assoc])
  zero_add a := toNat_injective (by simp [toNat_add])
  add_zero a := toNat_injective (by simp [toNat_add])
  add_comm a b := toNat_injective (by simp [toNat_add, Nat.add_comm])
  mul_assoc a b c := toNat_injective (by simp [toNat_mul, Nat.mul_assoc])
  one_mul a := toNat_injective (by simp [toNat_mul])
  mul_one a := toNat_injective (by simp [toNat_mul])
  left_distrib a b c := toNat_injective (by simp [toNat_add, toNat_mul, Nat.mul_add])
  right_distrib a b c := toNat_injective (by simp [toNat_add, toNat_mul, Nat.add_mul])
  zero_mul a := toNat_injective (by simp [toNat_mul])
  mul_zero a := toNat_injective (by simp [toNat_mul])
  mul_comm a b := toNat_injective (by simp [toNat_mul, Nat.mul_comm])
  nsmul := nsmulRec

instance : Nontrivial AzNat := ⟨0, 1, fun h => by
  have : (0 : Nat) = 1 := by rw [← toNat_zero, ← toNat_one, h]
  exact absurd this (by decide)⟩

end Azurite.AzNat
