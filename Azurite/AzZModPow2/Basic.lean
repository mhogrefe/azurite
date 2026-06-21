import Azurite.AzNat.ModPow2
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Tactic.Positivity

namespace Azurite

/-!
## `AzZModPow2 k` — integers modulo `2^k`

The `Pow2` specialization of the planned general `AzZMod`, backed by `AzNat`.
Reduction modulo `2^k` is masking the low `k` bits (`AzNat.modPow2`) — never
division — which is the reason to special-case powers of two.  `val` is the
canonical residue in `[0, 2^k)` (so equality is the real `DecidableEq`).  For
`k = 0` the only residue is `0` (`AzZModPow2 0` is trivial, matching `ZMod 1`).
-/

/-- Integers modulo `2^k`, as a canonical `AzNat` residue in `[0, 2^k)`. -/
structure AzZModPow2 (k : Nat) where
  /-- The canonical residue, in `[0, 2^k)`. -/
  val : AzNat
  /-- Canonicity: `val` is reduced modulo `2^k`. -/
  isLt : val.toNat < 2 ^ k
  deriving DecidableEq

namespace AzZModPow2

variable {k : Nat}

@[ext] theorem ext {a b : AzZModPow2 k} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

/-- Reduce an `AzNat` modulo `2^k` (low-`k`-bit mask). -/
def ofAzNat (k : Nat) (n : AzNat) : AzZModPow2 k :=
  ⟨n.modPow2 k, by rw [AzNat.toNat_modPow2]; exact Nat.mod_lt _ (by positivity)⟩

/-- The canonical residue as an `AzNat`. -/
def toAzNat (a : AzZModPow2 k) : AzNat := a.val

@[simp] theorem toAzNat_eq_val (a : AzZModPow2 k) : a.toAzNat = a.val := rfl

instance : Zero (AzZModPow2 k) := ⟨⟨0, by rw [AzNat.toNat_zero]; positivity⟩⟩
instance : One (AzZModPow2 k) := ⟨ofAzNat k 1⟩
instance : Inhabited (AzZModPow2 k) := ⟨0⟩

@[simp] theorem val_zero : (0 : AzZModPow2 k).val = 0 := rfl

/-- Construct from a `Nat` literal (reduced modulo `2^k`). -/
def ofNat (k m : Nat) : AzZModPow2 k := ofAzNat k (AzNat.ofNat m)

/-- Numeric literals `≥ 2` reduce modulo `2^k`. -/
instance instOfNat {m : Nat} [m.AtLeastTwo] : OfNat (AzZModPow2 k) m :=
  ⟨ofNat k m⟩

end AzZModPow2

end Azurite
