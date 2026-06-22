import Azurite.AzZMod.Equiv.Basic
import Azurite.AzZMod.Equiv.Conversion

/-!
## `CommRing (AzZMod m)`

The ring structure pinned by the projection `toZMod : AzZMod m → ZMod m.toNat`:
every axiom is the corresponding `ZMod` axiom pulled back through the injective,
operation-preserving `toZMod` (mirroring `AzZModPow2`'s `CommRing`).  The
arithmetic that runs is the computable residue arithmetic: `+`/`-`/`*` are the
add-then-subtract / borrow / reduce-the-product operations, and `nsmul`/`zsmul`
are one cast plus one multiplication (not the default `n`-fold sums).  A nonzero
modulus (`NeZero m.toNat`) is required throughout, as for the underlying residue
operations and the `ZMod` bridge.

`npow` is left as the default `npowRec` for now (an `O(log n)` sliding-window
`pow` would mirror `AzZModPow2.pow`, but is deferred along with the rest of the
multiplicative tower).
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- Computable `NatCast`: reduce the literal modulo `m` (the default
    `Nat.unaryCast` would be `n` additions of `1`). -/
instance [NeZero m.toNat] : NatCast (AzZMod m) := ⟨fun n => ofNat m n⟩

@[simp] theorem toZMod_natCast [NeZero m.toNat] (n : ℕ) :
    toZMod (n : AzZMod m) = (n : ZMod m.toNat) := by
  show toZMod (ofAzNat m (AzNat.ofNat n)) = (n : ZMod m.toNat)
  rw [toZMod_ofAzNat, AzNat.toNat_ofNat]

/-- Computable `IntCast`: convert through `AzInt.ofInt` and reduce modulo `m`. -/
instance [NeZero m.toNat] : IntCast (AzZMod m) := ⟨fun i => ofAzInt m (AzInt.ofInt i)⟩

@[simp] theorem toZMod_intCast [NeZero m.toNat] (i : ℤ) :
    toZMod (i : AzZMod m) = (i : ZMod m.toNat) := by
  show toZMod (ofAzInt m (AzInt.ofInt i)) = (i : ZMod m.toNat)
  rw [toZMod_ofAzInt, AzInt.toInt_ofInt]

instance instCommRing [NeZero m.toNat] : CommRing (AzZMod m) where
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
  nsmul n a := (n : AzZMod m) * a
  nsmul_zero a := toZMod_injective (by simp)
  nsmul_succ n a := toZMod_injective (by simp [toZMod_add, toZMod_mul]; ring)
  zsmul i a := (i : AzZMod m) * a
  zsmul_zero' a := toZMod_injective (by simp)
  zsmul_succ' n a := toZMod_injective (by simp [toZMod_add, toZMod_mul]; ring)
  zsmul_neg' n a := toZMod_injective (by simp [toZMod_mul, toZMod_neg, Int.negSucc_eq]; ring)

-- Sanity: the `CommRing` is fully usable — `ring` discharges polynomial identities.
example [NeZero m.toNat] (a b c : AzZMod m) : (a + b) * c = a * c + b * c := by ring

end Azurite.AzZMod
