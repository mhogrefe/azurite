import Azurite.AzZMod.Inv
import Azurite.AzZMod.Equiv.Conversion
import Azurite.AzZMod.Instances
import Azurite.AzZMod.ToString
import Azurite.AzInt.Equiv.ExtendedGcd

/-!
## Correctness of the modular inverse `AzZMod.inv`

`inv` is a two-sided inverse of any residue coprime to the modulus (and hence
such a residue is a unit).  The proof casts the Bézout identity
`s · a.val + t · m = 1` into `ZMod m.toNat`, where the `t · m` term vanishes
(`m ≡ 0`), leaving `s · a.val = 1`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- **Correctness:** `inv` is a right inverse. -/
@[simp] theorem mul_inv [NeZero m.toNat] (a : AzZMod m) (h : Nat.Coprime a.val.toNat m.toNat) :
    a * a.inv h = 1 := by
  apply toZMod_injective
  rw [toZMod_mul, toZMod_one]
  show toZMod a * toZMod (ofAzInt m (AzInt.egcd a.val m).2.1) = 1
  rw [toZMod_ofAzInt]
  -- Bézout `s · a.val + t · m = gcd = 1`, cast into `ZMod m.toNat`.
  have hg1 : (AzInt.egcd a.val m).1.toNat = 1 := (AzInt.egcd_gcd a.val m).trans h
  have hb := AzInt.egcd_bezout a.val m
  rw [hg1, Nat.cast_one] at hb
  have hbz := congrArg (fun z : ℤ => (z : ZMod m.toNat)) hb
  push_cast at hbz
  rw [ZMod.natCast_self, mul_zero, add_zero] at hbz
  -- hbz : ↑s.toInt * ↑a.val.toNat = 1; goal is the same product commuted.
  rw [mul_comm]
  exact hbz

/-- **Correctness:** `inv` is a left inverse. -/
@[simp] theorem inv_mul [NeZero m.toNat] (a : AzZMod m) (h : Nat.Coprime a.val.toNat m.toNat) :
    a.inv h * a = 1 := by
  rw [mul_comm]; exact mul_inv a h

/-- A residue coprime to the modulus is a unit of `ℤ / m`. -/
theorem isUnit_of_coprime [NeZero m.toNat] (a : AzZMod m) (h : Nat.Coprime a.val.toNat m.toNat) :
    IsUnit a :=
  ⟨⟨a, a.inv h, mul_inv a h, inv_mul a h⟩, rfl⟩

/-- `(ofNat m a).val` is the reduced literal — convenient for discharging
coprimality of concrete residues. -/
@[simp] theorem val_toNat_ofNat [NeZero m.toNat] (a : Nat) :
    (ofNat m a).val.toNat = a % m.toNat := by
  show ((AzNat.ofNat a % m).toNat) = a % m.toNat
  rw [AzNat.toNat_mod, AzNat.toNat_ofNat]

end Azurite.AzZMod

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

-- Coprimality of a literal residue: reduce to `Nat.Coprime (a % k) k` (decidable on ℕ).
private theorem coprimeLit {k a : Nat} [NeZero (AzNat.ofNat k).toNat]
    (h : Nat.Coprime (a % k) k) :
    Nat.Coprime (AzZMod.ofNat (AzNat.ofNat k) a).val.toNat (AzNat.ofNat k).toNat := by
  rw [val_toNat_ofNat, AzNat.toNat_ofNat]; exact h

-- `3⁻¹ = 5` in `ℤ/7` (`3·5 = 15 ≡ 1`), `= 7` in `ℤ/10` (`3·7 = 21 ≡ 1`),
-- `= 667` in `ℤ/1000` (`3·667 = 2001 ≡ 1`).
#guard Azurite.AzZMod.toString
  ((AzZMod.ofNat (AzNat.ofNat 7) 3).inv (coprimeLit (by decide))) == "5"
#guard Azurite.AzZMod.toString
  ((AzZMod.ofNat (AzNat.ofNat 10) 3).inv (coprimeLit (by decide))) == "7"
#guard Azurite.AzZMod.toString
  ((AzZMod.ofNat (AzNat.ofNat 1000) 3).inv (coprimeLit (by decide))) == "667"
-- The inverse really inverts.
#guard Azurite.AzZMod.toString (AzZMod.ofNat (AzNat.ofNat 1000) 3 *
  (AzZMod.ofNat (AzNat.ofNat 1000) 3).inv (coprimeLit (by decide))) == "1"
#guard Azurite.AzZMod.toString (AzZMod.ofNat (AzNat.ofNat 1000) 999 *
  (AzZMod.ofNat (AzNat.ofNat 1000) 999).inv (coprimeLit (by decide))) == "1"

end Tests
