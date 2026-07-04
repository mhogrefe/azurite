import Azurite.AzZModPow2.Equiv.Basic
import Azurite.AzZModPow2.Equiv.Conversion
import Azurite.AzZModPow2.Equiv.Pow

/-!
## `CommRing (AzZModPow2 k)`

The ring structure pinned by the projection `toZMod : AzZModPow2 k → ZMod (2^k)`:
every axiom is the corresponding `ZMod` axiom pulled back through the injective,
operation-preserving `toZMod` (mirroring `AzInt`'s `CommRing`).  The arithmetic
that runs is the computable masking arithmetic: `+`/`-`/`*` are the fused/low
limb operations, `npow` is the sliding-window `pow`, and `nsmul`/`zsmul` are one
cast plus one multiplication (not the default `n`-fold sums).
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- Computable `NatCast`: reduce the literal modulo `2^k` (the default
    `Nat.unaryCast` would be `n` additions of `1`). -/
instance : NatCast (AzZModPow2 k) := ⟨fun n => ofNat k n⟩

@[simp] theorem toZMod_natCast (n : ℕ) : toZMod (n : AzZModPow2 k) = (n : ZMod (2 ^ k)) := by
  show toZMod (ofAzNat k (AzNat.ofNat n)) = (n : ZMod (2 ^ k))
  rw [toZMod_ofAzNat, AzNat.toNat_ofNat]

/-- Computable `IntCast`: convert through `AzInt.ofInt` and reduce modulo `2^k`. -/
instance : IntCast (AzZModPow2 k) := ⟨fun i => ofAzInt k (AzInt.ofInt i)⟩

@[simp] theorem toZMod_intCast (i : ℤ) : toZMod (i : AzZModPow2 k) = (i : ZMod (2 ^ k)) := by
  show toZMod (ofAzInt k (AzInt.ofInt i)) = (i : ZMod (2 ^ k))
  rw [toZMod_ofAzInt, AzInt.toInt_ofInt]

instance instCommRing : CommRing (AzZModPow2 k) where
  add_assoc a b c := toZMod_injective (by simp only [toZMod_add]; ring)
  zero_add a := toZMod_injective (by simp)
  add_zero a := toZMod_injective (by simp)
  add_comm a b := toZMod_injective (by simp only [toZMod_add]; ring)
  mul_assoc a b c := toZMod_injective (by simp only [toZMod_mul]; ring)
  one_mul a := toZMod_injective (by simp)
  mul_one a := toZMod_injective (by simp)
  left_distrib a b c := toZMod_injective (by simp only [toZMod_add, toZMod_mul]; ring)
  right_distrib a b c := toZMod_injective (by simp only [toZMod_add, toZMod_mul]; ring)
  zero_mul a := toZMod_injective (by simp)
  mul_zero a := toZMod_injective (by simp)
  mul_comm a b := toZMod_injective (by simp only [toZMod_mul]; ring)
  neg_add_cancel a := toZMod_injective (by simp)
  sub_eq_add_neg a b := toZMod_injective (by simp only [toZMod_sub, toZMod_add, toZMod_neg]; ring)
  natCast_zero := toZMod_injective (by simp)
  natCast_succ n := toZMod_injective (by simp [toZMod_add])
  intCast_ofNat n := toZMod_injective (by simp)
  intCast_negSucc n := toZMod_injective (by simp [toZMod_neg, Int.negSucc_eq])
  -- `n • a` / `i • a` are one cast plus one multiplication.
  nsmul n a := (n : AzZModPow2 k) * a
  nsmul_zero a := toZMod_injective (by
    show (((0 : ℕ) : AzZModPow2 k) * a).toZMod = _
    simp)
  nsmul_succ n a := toZMod_injective (by
    show ((((n + 1 : ℕ)) : AzZModPow2 k) * a).toZMod = ((((n : ℕ)) : AzZModPow2 k) * a + a).toZMod
    simp [toZMod_add, toZMod_mul]
    ring)
  zsmul i a := (i : AzZModPow2 k) * a
  zsmul_zero' a := toZMod_injective (by
    show (((0 : ℤ) : AzZModPow2 k) * a).toZMod = _
    simp)
  zsmul_succ' n a := toZMod_injective (by
    show ((((n + 1 : ℕ) : ℤ) : AzZModPow2 k) * a).toZMod
      = ((((n : ℕ) : ℤ) : AzZModPow2 k) * a + a).toZMod
    simp [toZMod_add, toZMod_mul]
    ring)
  zsmul_neg' n a := toZMod_injective (by
    show (((Int.negSucc n) : AzZModPow2 k) * a).toZMod
      = (-((((n + 1 : ℕ) : ℤ) : AzZModPow2 k) * a)).toZMod
    simp [toZMod_mul, toZMod_neg, Int.negSucc_eq]
    ring)
  -- Exponentiation runs the sliding-window `pow` (`O(log n)` multiplications).
  npow n a := a.pow n
  npow_zero a := toZMod_injective (by
    show (a.pow 0).toZMod = _
    rw [toZMod_pow, pow_zero, toZMod_one])
  npow_succ n a := toZMod_injective (by
    show (a.pow (n + 1)).toZMod = (a.pow n * a).toZMod
    rw [toZMod_mul, toZMod_pow, toZMod_pow, pow_succ])

-- Sanity: the `CommRing` is fully usable — `ring` discharges polynomial identities,
-- and `pow` is the monoid power.
example (a b c : AzZModPow2 k) : (a + b) * c = a * c + b * c := by ring
example (a : AzZModPow2 k) (n : ℕ) : a ^ n = a.pow n := rfl

end Azurite.AzZModPow2
