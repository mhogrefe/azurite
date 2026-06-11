import Azurite.AzNat.Equiv.Square.ToomCook3
import Azurite.Algorithm.SlidingWindowPow

namespace Azurite.AzNat

/-- Route `Square.square` to AzNat's dedicated three-way `square` (schoolbook / Karatsuba /
Toom-Cook 3), so exponentiation squares in subquadratic time rather than via a general
multiplication. Overrides the low-priority default `Square` instance. -/
instance instSquareAzNat : Azurite.Square AzNat where
  square := AzNat.square
  square_eq a := toNat_injective (by rw [toNat_square, toNat_mul, pow_two])

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
  -- The cast `(n : ℕ) : AzNat` is the limb-level `AzNat.ofNat` (the default
  -- `Nat.unaryCast` would be `n` additions of `1`), and `n • a` is one cast
  -- plus one multiplication (the default `nsmulRec` would be `n` additions).
  natCast n := AzNat.ofNat n
  natCast_zero := toNat_injective (by rw [toNat_ofNat, toNat_zero])
  natCast_succ n := toNat_injective (by
    rw [toNat_add, toNat_ofNat, toNat_ofNat, toNat_one])
  nsmul n a := AzNat.ofNat n * a
  nsmul_zero a := toNat_injective (by
    rw [toNat_mul, toNat_ofNat, toNat_zero, Nat.zero_mul])
  nsmul_succ n a := toNat_injective (by
    rw [toNat_add, toNat_mul, toNat_mul, toNat_ofNat, toNat_ofNat, Nat.succ_mul])
  -- Exponentiation `a ^ n` runs the generic sliding-window algorithm (the same one behind
  -- `AzNat.pow`), so it is `O(log n)` multiplications rather than the default `O(n)`, and
  -- `a.pow n = a ^ n` definitionally. The `npow_succ` obligation is discharged by the generic
  -- transport `map_slidingWindowPow` under `toNat`, which needs only `Mul`/`One`/`Square`
  -- (all in scope here), so it goes through while the `Monoid` is still being built.
  npow n a := Azurite.slidingWindowPow a n
  npow_zero _ := rfl
  npow_succ n a := toNat_injective (by
    rw [toNat_mul, map_slidingWindowPow AzNat.toNat toNat_one toNat_mul a (n + 1),
        map_slidingWindowPow AzNat.toNat toNat_one toNat_mul a n, pow_succ])

instance : Nontrivial AzNat := ⟨0, 1, fun h => by
  have : (0 : Nat) = 1 := by rw [← toNat_zero, ← toNat_one, h]
  exact absurd this (by decide)⟩

end Azurite.AzNat
