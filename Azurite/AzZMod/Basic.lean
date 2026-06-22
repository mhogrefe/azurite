import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Basic
import Mathlib.Data.Nat.Cast.Defs

namespace Azurite

/-!
## `AzZMod m` — integers modulo a general `AzNat`

The general companion of [`AzZModPow2`](../AzZModPow2/Basic.lean): residues modulo
an arbitrary `AzNat` modulus `m`, with `AzZModPow2 k` the power-of-two
specialization where reduction is masking rather than division.

The modulus is an **`AzNat` value index** (not a `Nat`).  This is the deliberate
choice that keeps computation limb-level: reduction is `AzNat.mod` against `m`,
which is already an `AzNat` and so never has to be reconstructed from a `Nat`
literal (that would route a possibly huge modulus through `Nat` arithmetic).
`AzZModPow2 k` can index by the small `Nat` `k` only because its modulus `2^k`
is never materialized — masking needs just the bit-count.

`val` is the canonical residue in `[0, m)` (so equality is the real
`DecidableEq`).  A nonzero modulus (`NeZero m.toNat`) is required for the type to
be inhabited and for the `ZMod m.toNat` bridge; it is taken as an instance
argument wherever needed, mirroring `ZMod`'s `[NeZero n]`.
-/

/-- Integers modulo `m`, as a canonical `AzNat` residue in `[0, m)`. -/
structure AzZMod (m : AzNat) where
  /-- The canonical residue, in `[0, m)`. -/
  val : AzNat
  /-- Canonicity: `val` is reduced modulo `m`. -/
  isLt : val.toNat < m.toNat
  deriving DecidableEq

namespace AzZMod

variable {m : AzNat}

@[ext] theorem ext {a b : AzZMod m} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- `NeZero` of the value of an `AzNat` literal, so a literal modulus such as
`AzNat.ofNat 7` automatically supplies the `NeZero m.toNat` the residue
operations need. -/
instance instNeZeroToNatOfNat (n : Nat) [NeZero n] : NeZero (AzNat.ofNat n).toNat :=
  ⟨by rw [AzNat.toNat_ofNat]; exact NeZero.ne n⟩

/-- Reduce an `AzNat` modulo `m` (limb-level `AzNat.mod`). -/
def ofAzNat (m : AzNat) [NeZero m.toNat] (n : AzNat) : AzZMod m :=
  ⟨n % m, by rw [AzNat.toNat_mod]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩

/-- The canonical residue as an `AzNat`. -/
def toAzNat (a : AzZMod m) : AzNat := a.val

@[simp] theorem toAzNat_eq_val (a : AzZMod m) : a.toAzNat = a.val := rfl

/-- Reducing an already-canonical residue is the identity. -/
@[simp] theorem ofAzNat_val [NeZero m.toNat] (a : AzZMod m) : ofAzNat m a.val = a := by
  apply ext
  show a.val % m = a.val
  apply AzNat.toNat_injective
  rw [AzNat.toNat_mod, Nat.mod_eq_of_lt a.isLt]

instance [NeZero m.toNat] : Zero (AzZMod m) :=
  ⟨⟨0, by rw [AzNat.toNat_zero]; exact Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
instance [NeZero m.toNat] : One (AzZMod m) := ⟨ofAzNat m 1⟩
instance [NeZero m.toNat] : Inhabited (AzZMod m) := ⟨0⟩

@[simp] theorem val_zero [NeZero m.toNat] : (0 : AzZMod m).val = 0 := rfl

/-- Construct from a `Nat` literal (reduced modulo `m`). -/
def ofNat (m : AzNat) [NeZero m.toNat] (a : Nat) : AzZMod m := ofAzNat m (AzNat.ofNat a)

/-- Numeric literals `≥ 2` reduce modulo `m`. -/
instance instOfNat [NeZero m.toNat] {a : Nat} [a.AtLeastTwo] : OfNat (AzZMod m) a :=
  ⟨ofNat m a⟩

end AzZMod

end Azurite

/-! ### Tests -/

section Tests

open Azurite Azurite.AzZMod

-- In `ℤ/7`: `19 ≡ 5`, `7 ≡ 0`, `6` is canonical.
#guard AzZMod.ofNat (AzNat.ofNat 7) 19 == AzZMod.ofNat (AzNat.ofNat 7) 5
#guard AzZMod.ofNat (AzNat.ofNat 7) 7 == AzZMod.ofNat (AzNat.ofNat 7) 0
#guard AzZMod.ofNat (AzNat.ofNat 7) 6 == AzZMod.ofNat (AzNat.ofNat 7) 6
-- A non-power-of-two, multi-digit modulus `ℤ/1000`: `123456 ≡ 456`.
#guard AzZMod.ofNat (AzNat.ofNat 1000) 123456 == AzZMod.ofNat (AzNat.ofNat 1000) 456
-- Reduction is genuine division, not masking: `ℤ/100`, `250 ≡ 50`.
#guard AzZMod.ofNat (AzNat.ofNat 100) 250 == AzZMod.ofNat (AzNat.ofNat 100) 50

end Tests
